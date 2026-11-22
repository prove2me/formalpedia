-- Prove2me | solution 1 for RandomOracleUnitarySynthesis.synthesis_query_bound
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:35:28.590173+00:00
-- url     : https://prove2.me/submissions/b2bf52e5-529e-4cf4-9054-257037188d67

import Mathlib
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit
import Definitions.Def_SpaceReset_Hardness_Quantum
import Definitions.Def_DirectFidelity_State_Setting
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_resampling
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_family
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Theorems.Thm_HaarPhaseInvariantUnitary_logMeanBound


/- Module RandomOracleInfluence -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate

section Frobenius
variable {α β : Type} [Fintype α] [Fintype β]
open scoped Matrix.Norms.Frobenius in
lemma frob_sq_entries (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=∑i,∑j,‖A i j‖^2 := by
  change ‖A‖^2=_
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (sum_nonneg (fun i _=>sum_nonneg (fun j _=>sq_nonneg _)))

lemma frob_sq_gram [DecidableEq β] (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=(Aᴴ*A).trace.re := by
  rw [frob_sq_entries]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.star_def]

lemma frob_sq_leftGram [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=(A*Aᴴ).trace.re := by rw [frob_sq_gram,Matrix.trace_mul_comm]
end Frobenius

variable {n m m₀ k : ℕ}

lemma prefix_join (h:n ≤ m) (x : synthesis_Bits n) (a : synthesis_Bits (m-n)) :
    synthesis_prefix h (synthesis_join h x a)=x := by
  funext i
  simp [synthesis_prefix,synthesis_join,i.isLt]

lemma join_left_injective (h:n ≤ m) (a : synthesis_Bits (m-n)) :
    Function.Injective (fun x=>synthesis_join h x a) := by
  intro x y hh
  have hpre:=congrArg (synthesis_prefix h) hh
  simpa only [prefix_join] using hpre

lemma J_isometry (C : synthesis_Circuit n m m₀ k) : (synthesis_J C)ᴴ*synthesis_J C=1 := by
  have hinj:=join_left_injective C.system_le (fun _=>0)
  ext x y
  simp [synthesis_J,Matrix.mul_apply,Matrix.conjTranspose_apply,ite_mul,mul_ite,hinj.eq_iff,eq_comm,Matrix.one_apply]

lemma gate_unitary (C : synthesis_Circuit n m m₀ k) (i : ℕ) :
    synthesis_gate C i∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  unfold synthesis_gate
  split_ifs with hi
  · exact (C.gates ⟨i,hi⟩).property
  · exact one_mem _

lemma oracle_unitary (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_oracle C f∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  apply Unitary.mem_iff.mpr
  constructor <;> ext x y <;> by_cases h:x=y
  all_goals simp [synthesis_oracle,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal,Matrix.one_apply,Matrix.diagonal_apply,h]
  all_goals split_ifs <;> norm_num

lemma segment_unitary (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a b : ℕ) :
    synthesis_segment C f a b∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  have hfold:∀(L:List ℕ) (W:synthesis_Mat m),W∈Matrix.unitaryGroup (synthesis_Bits m) ℂ→
      L.foldl (fun W t=>synthesis_gate C (a+t+1)*synthesis_oracle C f*W) W∈
        Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
    intro L
    induction L with
    | nil => intro W hW;exact hW
    | cons t L ih =>
      intro W hW
      exact ih _ (mul_mem (mul_mem (gate_unitary C _) (oracle_unitary C f)) hW)
  exact hfold _ _ (gate_unitary C a)

lemma projector_columns (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀)
    {α : Type} [Fintype α] (A : Matrix α (synthesis_Bits m) ℂ) (i : α) (j : synthesis_Bits m) :
    (A*synthesis_projector C x) i j=if synthesis_prefix C.oracle_le j=x then A i j else 0 := by
  simp [Matrix.mul_apply,synthesis_projector,ite_and,mul_ite]

lemma projector_rows (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀)
    {α : Type} [Fintype α] (A : Matrix (synthesis_Bits m) α ℂ) (i : synthesis_Bits m) (j : α) :
    (synthesis_projector C x*A) i j=if synthesis_prefix C.oracle_le i=x then A i j else 0 := by
  simp [Matrix.mul_apply,synthesis_projector,ite_and,ite_mul]

lemma sum_projector_right_frob (C : synthesis_Circuit n m m₀ k)
    {α : Type} [Fintype α] (A : Matrix α (synthesis_Bits m) ℂ) :
    (∑x,QAlgorithms.frobNorm (A*synthesis_projector C x)^2)=QAlgorithms.frobNorm A^2 := by
  simp only [frob_sq_entries,projector_columns]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (synthesis_prefix C.oracle_le j)]
  · simp
  · intro x hx hne
    simp [Ne.symm hne]
  · simp

lemma sum_projector_left_frob (C : synthesis_Circuit n m m₀ k)
    {α : Type} [Fintype α] (A : Matrix (synthesis_Bits m) α ℂ) :
    (∑x,QAlgorithms.frobNorm (synthesis_projector C x*A)^2)=QAlgorithms.frobNorm A^2 := by
  simp only [frob_sq_entries,projector_rows]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (synthesis_prefix C.oracle_le i)]
  · simp
  · intro x hx hne
    simp [Ne.symm hne]
  · simp

lemma left_gram (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (j : Fin k) :
    synthesis_left C f j*(synthesis_left C f j)ᴴ=1 := by
  have hU:=segment_unitary C f (j.val+1) k
  have hh:(synthesis_segment C f (j.val+1) k)*(synthesis_segment C f (j.val+1) k)ᴴ=1 :=
    (Unitary.mem_iff.mp hU).2
  simp only [synthesis_left,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ (synthesis_J C),hh,Matrix.one_mul,J_isometry]

lemma right_gram (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (j : Fin k) :
    (synthesis_right C f j)ᴴ*synthesis_right C f j=1 := by
  have hU:=segment_unitary C f 0 j.val
  have hh:(synthesis_segment C f 0 j.val)ᴴ*(synthesis_segment C f 0 j.val)=1 :=
    (Unitary.mem_iff.mp hU).1
  simp only [synthesis_right,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ (synthesis_J C),hh,Matrix.one_mul,J_isometry]

lemma trace_one_bits (n : ℕ) : ((1:synthesis_Mat n).trace).re=(2:ℝ)^n := by
  rw [Matrix.trace_one]
  simp only [Complex.natCast_re,Fintype.card_fun,Fintype.card_fin]
  norm_cast

/-- Exact public Lemma4.7, retaining the full computational basis and the
published circuit fold products and ancilla embedding. -/
theorem synthesis_total_influence (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    (∑x,synthesis_influence C f x)=2*(k:ℝ)*(2:ℝ)^n := by
  unfold synthesis_influence
  rw [sum_comm]
  simp only [sum_add_distrib,sum_projector_right_frob,sum_projector_left_frob]
  have he:∀j:Fin k,QAlgorithms.frobNorm (synthesis_left C f j)^2+
      QAlgorithms.frobNorm (synthesis_right C f j)^2=2*(2:ℝ)^n := by
    intro j
    rw [frob_sq_leftGram,frob_sq_gram,left_gram,right_gram,trace_one_bits]
    ring
  rw [← sum_add_distrib]
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOracleChannelKraus -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open scoped ComplexOrder ComplexConjugate Kronecker
variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι]
  [DecidableEq α] [DecidableEq β]

def krausMap (M : ι→Matrix α β ℂ) (ρ : Matrix β β ℂ) : Matrix α α ℂ :=
  ∑i,M i*ρ*(M i)ᴴ

lemma krausMap_pos (M : ι→Matrix α β ℂ) (ρ : Matrix β β ℂ) (hρ:ρ.PosSemidef) :
    (krausMap M ρ).PosSemidef :=
  Matrix.posSemidef_sum univ (fun i _=>hρ.mul_mul_conjTranspose_same (M i))

lemma krausMap_trace (M : ι→Matrix α β ℂ) (ρ : Matrix β β ℂ)
    (hM:(∑i,(M i)ᴴ*M i)=1) : (krausMap M ρ).trace=ρ.trace := by
  unfold krausMap
  have he:∀i:ι,(M i*ρ*(M i)ᴴ).trace=(((M i)ᴴ*M i)*ρ).trace :=
    fun i=>Matrix.trace_mul_cycle _ _ _
  rw [Matrix.trace_sum]
  simp only [he]
  rw [←Matrix.trace_sum,←Finset.sum_mul,hM,Matrix.one_mul]

lemma krausMap_density (M : ι→Matrix α β ℂ) (ρ : Matrix β β ℂ)
    (hM:(∑i,(M i)ᴴ*M i)=1) (hρ:WildeQIT.IsDensityOperator ρ) :
    WildeQIT.IsDensityOperator (krausMap M ρ) :=
  ⟨krausMap_pos M ρ hρ.1,(krausMap_trace M ρ hM).trans hρ.2⟩

def krausLinear (M : ι→Matrix α β ℂ) : Matrix β β ℂ→ₗ[ℂ]Matrix α α ℂ where
  toFun:=krausMap M
  map_add' A B:=by simp [krausMap,Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
  map_smul' c A:=by simp [krausMap,Matrix.mul_smul,Matrix.smul_mul,Finset.smul_sum]

lemma coordinates_linear {n : ℕ} (L : synthesis_Mat n→ₗ[ℂ]synthesis_Mat n) (ρ : synthesis_Mat n) :
    synthesis_apply (synthesis_coordinates L) ρ=L ρ := by
  calc
    _ = ∑a:synthesis_Bits n,∑b:synthesis_Bits n,ρ a b • L (Matrix.single a b 1) := by
      ext x y
      simp only [synthesis_apply,synthesis_coordinates,Fintype.sum_prod_type,Matrix.sum_apply,
        Matrix.smul_apply,smul_eq_mul]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      exact mul_comm _ _
    _ = L (∑a:synthesis_Bits n,∑b:synthesis_Bits n,ρ a b • Matrix.single a b 1) := by
      simp only [map_sum,map_smul]
    _ = L ρ := by
      congr 1
      simp only [Matrix.smul_single,smul_eq_mul,mul_one]
      exact (Matrix.matrix_eq_sum_single ρ).symm

lemma amplify_kraus {n : ℕ} (M : ι→synthesis_Mat n) (b : ℕ)
    (ρ : Matrix (synthesis_Bits n×Fin b) (synthesis_Bits n×Fin b) ℂ) :
    synthesis_amplify (synthesis_coordinates (krausLinear M)) b ρ=
      krausMap (fun i=>(M i) ⊗ₖ (1:Matrix (Fin b) (Fin b) ℂ)) ρ := by
  ext x y
  rcases x with ⟨x,s⟩
  rcases y with ⟨y,t⟩
  let R:synthesis_Mat n:=fun a c=>ρ (a,s) (c,t)
  simp only [synthesis_amplify,Matrix.of_apply]
  rw [coordinates_linear]
  change krausMap M R x y=_
  simp only [krausMap,Matrix.sum_apply,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply,Matrix.conjTranspose_apply,Matrix.one_apply]
  simp only [apply_ite,map_zero,mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  dsimp only [R]
  simp only [star_zero,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]

lemma kraus_tensor_identity_complete {n : ℕ} (M : ι→synthesis_Mat n)
    (hM:(∑i,(M i)ᴴ*M i)=1) (b : ℕ) :
    (∑i,((M i) ⊗ₖ (1:Matrix (Fin b) (Fin b) ℂ))ᴴ*((M i) ⊗ₖ (1:Matrix (Fin b) (Fin b) ℂ)))=1 := by
  simp_rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,←Matrix.mul_kronecker_mul,
    Matrix.one_mul]
  ext x y
  simp only [Matrix.sum_apply,Matrix.kroneckerMap_apply]
  rw [←Finset.sum_mul,←Matrix.sum_apply,hM]
  simp only [Matrix.one_apply,Prod.ext_iff,ite_and]
  by_cases h1:x.1=y.1 <;> by_cases h2:x.2=y.2 <;> simp [h1,h2]

lemma amplify_kraus_density {n : ℕ} (M : ι→synthesis_Mat n)
    (hM:(∑i,(M i)ᴴ*M i)=1) (b : ℕ)
    (ρ : Matrix (synthesis_Bits n×Fin b) (synthesis_Bits n×Fin b) ℂ)
    (hρ:WildeQIT.IsDensityOperator ρ) :
    WildeQIT.IsDensityOperator (synthesis_amplify (synthesis_coordinates (krausLinear M)) b ρ) := by
  rw [amplify_kraus]
  exact krausMap_density _ _ (kraus_tensor_identity_complete M hM b) hρ

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleDirtyKraus -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open scoped ComplexConjugate Kronecker
variable {n m m₀ k : ℕ}

lemma suffix_join (h:n ≤ m) (x : synthesis_Bits n) (a : synthesis_Bits (m-n)) :
    synthesis_suffix h (synthesis_join h x a)=a := by
  funext i
  have hi:¬n+i.val<n := by omega
  simp [synthesis_suffix,synthesis_join,hi]

lemma join_prefix_suffix (h:n ≤ m) (y : synthesis_Bits m) :
    synthesis_join h (synthesis_prefix h y) (synthesis_suffix h y)=y := by
  funext i
  by_cases hi:i.val<n
  · simp [synthesis_join,synthesis_prefix,hi]
  · simp only [synthesis_join,dif_neg hi,synthesis_suffix]
    congr 1
    apply Fin.ext
    dsimp
    omega

def joinEquiv (h:n ≤ m) : synthesis_Bits n×synthesis_Bits (m-n) ≃ synthesis_Bits m where
  toFun p:=synthesis_join h p.1 p.2
  invFun y:=(synthesis_prefix h y,synthesis_suffix h y)
  left_inv p:=by simp only [InfluenceProof.prefix_join,suffix_join]
  right_inv y:=join_prefix_suffix h y

def slice (h:n ≤ m) (V : Matrix (synthesis_Bits m) (synthesis_Bits n) ℂ)
    (a : synthesis_Bits (m-n)) : synthesis_Mat n :=
  fun x y=>V (synthesis_join h x a) y

lemma slice_complete (h:n ≤ m) (V : Matrix (synthesis_Bits m) (synthesis_Bits n) ℂ)
    (hV:Vᴴ*V=1) : (∑a:synthesis_Bits (m-n),(slice h V a)ᴴ*slice h V a)=1 := by
  ext x y
  have hreindex:(∑p:synthesis_Bits n×synthesis_Bits (m-n),
      star (V (synthesis_join h p.1 p.2) x)*V (synthesis_join h p.1 p.2) y)=
      ∑z:synthesis_Bits m,star (V z x)*V z y := by
    have hh:=(joinEquiv h).sum_comp (fun z:synthesis_Bits m=>star (V z x)*V z y)
    exact hh
  have he:=congrFun (congrFun hV x) y
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply] at he
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,slice]
  rw [sum_comm]
  simpa only [Fintype.sum_prod_type] using hreindex.trans he

lemma partialTrace_slice (h:n ≤ m) (V : Matrix (synthesis_Bits m) (synthesis_Bits n) ℂ)
    (ρ : synthesis_Mat n) :
    WildeQIT.partialTraceRight (Matrix.of fun a b:synthesis_Bits n×synthesis_Bits (m-n)=>
      (V*ρ*Vᴴ) (synthesis_join h a.1 a.2) (synthesis_join h b.1 b.2))=
      krausMap (slice h V) ρ := by
  ext x y
  simp only [WildeQIT.partialTraceRight,Matrix.of_apply,krausMap,Matrix.sum_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,slice]

lemma WJ_isometry (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    (synthesis_W C f*synthesis_J C)ᴴ*(synthesis_W C f*synthesis_J C)=1 := by
  have hW:(synthesis_W C f)ᴴ*synthesis_W C f=1 :=
    Unitary.star_mul_self_of_mem (InfluenceProof.segment_unitary C f 0 k)
  calc
    _ = (synthesis_J C)ᴴ*((synthesis_W C f)ᴴ*synthesis_W C f)*synthesis_J C := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = 1 := by rw [hW,Matrix.mul_one,InfluenceProof.J_isometry]

lemma actualChannel_kraus (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_actualChannel C f=synthesis_coordinates
      (krausLinear (slice C.system_le (synthesis_W C f*synthesis_J C))) := by
  unfold synthesis_actualChannel
  apply congrArg synthesis_coordinates
  funext ρ
  have he:synthesis_W C f*synthesis_J C*ρ*(synthesis_J C)ᴴ*(synthesis_W C f)ᴴ=
      (synthesis_W C f*synthesis_J C)*ρ*(synthesis_W C f*synthesis_J C)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he,partialTrace_slice]
  rfl

/-- Every finite-reference amplification of the actual dirty circuit preserves
all mixed density operators, derived from its literal partial-trace definition. -/
theorem actualChannel_amplify_density (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (b : ℕ) (ρ : Matrix (synthesis_Bits n×Fin b) (synthesis_Bits n×Fin b) ℂ)
    (hρ:WildeQIT.IsDensityOperator ρ) :
    WildeQIT.IsDensityOperator (synthesis_amplify (synthesis_actualChannel C f) b ρ) := by
  rw [actualChannel_kraus]
  exact amplify_kraus_density _ (slice_complete C.system_le _ (WJ_isometry C f)) b ρ hρ

lemma unitaryChannel_kraus {n : ℕ} (U : synthesis_Unitary n) :
    synthesis_unitaryChannel U=synthesis_coordinates (krausLinear (fun _:Unit=>(U:synthesis_Mat n))) := by
  unfold synthesis_unitaryChannel
  apply congrArg synthesis_coordinates
  funext ρ
  change (U:synthesis_Mat n)*ρ*(U:synthesis_Mat n)ᴴ=
    krausMap (fun _:Unit=>(U:synthesis_Mat n)) ρ
  simp only [krausMap,Fintype.sum_unique]

 theorem unitaryChannel_amplify_density {n : ℕ} (U : synthesis_Unitary n)
    (b : ℕ) (ρ : Matrix (synthesis_Bits n×Fin b) (synthesis_Bits n×Fin b) ℂ)
    (hρ:WildeQIT.IsDensityOperator ρ) :
    WildeQIT.IsDensityOperator (synthesis_amplify (synthesis_unitaryChannel U) b ρ) := by
  rw [unitaryChannel_kraus]
  have hc:(∑_:Unit,(U:synthesis_Mat n)ᴴ*(U:synthesis_Mat n))=1 := by
    simp only [Fintype.sum_unique]
    exact Unitary.star_mul_self_of_mem U.property
  exact amplify_kraus_density _ hc b ρ hρ

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleObservableKraus -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open scoped ComplexConjugate Kronecker
variable {n m m₀ k : ℕ}

def liftOperator (h:n ≤ m) (P : synthesis_Mat n) : synthesis_Mat m :=
  fun y z=>if synthesis_suffix h y=synthesis_suffix h z then
    P (synthesis_prefix h y) (synthesis_prefix h z) else 0

lemma liftOperator_join (h:n ≤ m) (P : synthesis_Mat n)
    (x y : synthesis_Bits n) (a b : synthesis_Bits (m-n)) :
    liftOperator h P (synthesis_join h x a) (synthesis_join h y b)=if a=b then P x y else 0 := by
  simp only [liftOperator,suffix_join,InfluenceProof.prefix_join]

lemma liftOperator_reindex (h:n ≤ m) (P : synthesis_Mat n) :
    (liftOperator h P).submatrix (joinEquiv h) (joinEquiv h)=
      P ⊗ₖ (1:Matrix (synthesis_Bits (m-n)) (synthesis_Bits (m-n)) ℂ) := by
  ext x y
  change liftOperator h P (synthesis_join h x.1 x.2) (synthesis_join h y.1 y.2)=_
  rw [liftOperator_join]
  simp [Matrix.kroneckerMap_apply,Matrix.one_apply,mul_ite]

lemma conjugate_reindex {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (V : Matrix α β ℂ) (L : Matrix α α ℂ) (e : γ≃α) :
    (V.submatrix e id)ᴴ*(L.submatrix e e)*(V.submatrix e id)=Vᴴ*L*V := by
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]

def blockSlice {α β γ : Type} (S : Matrix (α×γ) β ℂ) (a : γ) : Matrix α β ℂ :=
  fun x y=>S (x,a) y

lemma block_conjugate {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (S : Matrix (α×γ) β ℂ) (P : Matrix α α ℂ) :
    Sᴴ*(P ⊗ₖ (1:Matrix γ γ ℂ))*S=
      ∑a:γ,(blockSlice S a)ᴴ*P*blockSlice S a := by
  ext x y
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.sum_apply,Finset.sum_mul,blockSlice]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,mul_one,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_univ,if_true]
  rw [sum_comm]

lemma slice_conjugate (h:n ≤ m) (V : Matrix (synthesis_Bits m) (synthesis_Bits n) ℂ)
    (P : synthesis_Mat n) :
    Vᴴ*liftOperator h P*V=∑a:synthesis_Bits (m-n),(slice h V a)ᴴ*P*slice h V a := by
  rw [←conjugate_reindex V (liftOperator h P) (joinEquiv h),liftOperator_reindex,block_conjugate]
  rfl

lemma observable_kraus (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (P : synthesis_Pauli n) :
    synthesis_observable C f P=
      ∑a:synthesis_Bits (m-n),(slice C.system_le (synthesis_W C f*synthesis_J C) a)ᴴ*
        DirectFidelity.State.W P*slice C.system_le (synthesis_W C f*synthesis_J C) a := by
  have he:synthesis_observable C f P=
      (synthesis_W C f*synthesis_J C)ᴴ*liftOperator C.system_le (DirectFidelity.State.W P)*
        (synthesis_W C f*synthesis_J C) := by
    simp only [synthesis_observable,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rfl
  rw [he,slice_conjugate]

end RandomOracleUnitarySynthesis.ChannelProof

/- Module SpaceResetFidelityCore -/

/-! Finite matrix foundations, extracted from the accepted Prove2Me proof
of Uhlmann (submission e7f79aee-b42a-40df-9b8b-becca22296a9,
theorem c84df38e-32fb-41ea-8ea7-c4b571ce7f65, Apache-2.0).
Only the Mathlib-only matrix proofs are retained; the unrelated relative
entropy sections and paper-specific definition imports are omitted. -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace CFCBasics
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cs (X Y : Matrix I I ℂ) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ (Xᴴ * X).trace.re + (Yᴴ * Y).trace.re := by
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self (X - Y))
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h0
  linarith

/-- `Re Tr Z ≤ Tr √(Z Z†)` -/
theorem re_tr_le (Z : Matrix I I ℂ) : Z.trace.re ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set M := Z * Zᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Z
  have hMs : IsSelfAdjoint M := hM.1.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hM.nonneg hx
  have key : ∀ ε : ℝ, 0 < ε → Z.trace.re ≤ (cfc Real.sqrt M).trace.re + ε * Fintype.card I / 2 := by
    intro ε hε
    set L := cfc (fun x => Real.sqrt (Real.sqrt x + ε)) M
    set K := cfc (fun x => (Real.sqrt (Real.sqrt x + ε))⁻¹) M
    have hpos : ∀ x : ℝ, 0 < Real.sqrt (Real.sqrt x + ε) :=
      fun x => Real.sqrt_pos.2 (by positivity)
    have hLK : L * K = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => mul_inv_cancel₀ (hpos x).ne'
    have hKL : K * L = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => inv_mul_cancel₀ (hpos x).ne'
    have hLh : Lᴴ = L := (cfc_predicate _ M : IsSelfAdjoint L)
    have hKh : Kᴴ = K := (cfc_predicate _ M : IsSelfAdjoint K)
    have h := cs L (K * Z)
    have e1 : Lᴴ * (K * Z) = Z := by rw [hLh, ← Matrix.mul_assoc, hLK, Matrix.one_mul]
    have e2 : (K * Z)ᴴ * L = Zᴴ := by
      rw [conjTranspose_mul, hKh, Matrix.mul_assoc, hKL, Matrix.mul_one]
    have e3 : (Lᴴ * L).trace.re = (cfc Real.sqrt M).trace.re + ε * Fintype.card I := by
      have : Lᴴ * L = cfc Real.sqrt M + (ε : ℂ) • 1 := by
        rw [hLh, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        rw [show (ε : ℂ) • (1 : Matrix I I ℂ) = cfc (fun _ : ℝ => ε) M by
          rw [cfc_const ε M hMs]; simp [Algebra.algebraMap_eq_smul_one]]
        rw [← cfc_add _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        exact Real.mul_self_sqrt (by have := Real.sqrt_nonneg x; linarith)
      rw [this, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Matrix.trace_one]
      simp
    have e4 : ((K * Z)ᴴ * (K * Z)).trace.re ≤ (cfc Real.sqrt M).trace.re := by
      have t1 : ((K * Z)ᴴ * (K * Z)).trace = (K * K * M).trace := by
        rw [conjTranspose_mul, hKh]
        rw [show Zᴴ * K * (K * Z) = Zᴴ * (K * K * Z) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [M, Matrix.mul_assoc]
      have t2 : K * K * M = cfc (fun x => x / (Real.sqrt x + ε)) M := by
        rw [show K * K * M = K * K * cfc (fun x : ℝ => x) M by rw [cfc_id' ℝ M hMs],
          ← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [← mul_inv, Real.mul_self_sqrt h1.le, div_eq_inv_mul]
      have t3 : (cfc Real.sqrt M - K * K * M).PosSemidef := by
        rw [t2, ← cfc_sub _ _ _ (fin _ _) (fin _ _)]
        refine (cfc_nonneg (fun x hx => ?_) :
          0 ≤ cfc (fun x => Real.sqrt x - x / (Real.sqrt x + ε)) M).posSemidef
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [sub_nonneg, div_le_iff₀ h1]
        have := Real.mul_self_sqrt h0
        nlinarith [Real.sqrt_nonneg x]
      have := psd_re t3
      rw [Matrix.trace_sub, Complex.sub_re] at this
      rw [t1]; linarith
    rw [e1, e2, e3, Matrix.trace_conjTranspose] at h
    simp only [RCLike.star_def, Complex.conj_re] at h
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have := key (2 * δ / (Fintype.card I + 1)) (by positivity)
  refine this.trans ?_
  have : 2 * δ / (Fintype.card I + 1) * Fintype.card I / 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix I I ℂ} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  refine cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

end CFCBasics
namespace Nuclear
open Polynomial
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]

section Polar
variable {R : Type*} [Fintype R] [DecidableEq R]
lemma dot_self (Y : Matrix R R ℂ) (v : R → ℂ) :
    star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma norm_sq_eq (x : EuclideanSpace ℂ R) : ((‖x‖ ^ 2 : ℝ) : ℂ) = star (x.ofLp) ⬝ᵥ x.ofLp := by
  rw [Complex.ofReal_pow, show ((‖x‖ : ℂ)) ^ 2 = inner ℂ x x from
    (inner_self_eq_norm_sq_to_K x).symm, PiLp.inner_apply]
  simp [dotProduct, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

/-- Polar decomposition: `Y = W |Y|` with `W` unitary. -/
theorem polar (Y : Matrix R R ℂ) :
    ∃ W : Matrix.unitaryGroup R ℂ, (W : Matrix R R ℂ) * cfc Real.sqrt (Yᴴ * Y) = Y := by
  set G := Yᴴ * Y
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  set A := cfc Real.sqrt G
  set Ap := cfc (fun x => (Real.sqrt x)⁻¹) G
  set P := cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) G
  have hAh : Aᴴ = A := CFCBasics.sqrt_herm G
  have hAA : A * A = G := CFCBasics.sqrt_sq hG
  have hApA : Ap * A = P := by
    rw [← cfc_mul _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hA1P : A * (1 - P) = 0 := by
    rw [← cfc_one ℝ G, ← cfc_sub _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _),
      ← cfc_mul _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _)]
    rw [show (0 : Matrix R R ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) G by simp]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  have hY1P : Y * (1 - P) = 0 := by
    have : (Y * (1 - P))ᴴ * (Y * (1 - P)) = 0 := by
      have e : (Y * (1 - P))ᴴ * (Y * (1 - P)) = (A * (1 - P))ᴴ * (A * (1 - P)) := by
        simp only [conjTranspose_mul, hAh]
        rw [show (1 - P)ᴴ * Yᴴ * (Y * (1 - P)) = (1 - P)ᴴ * G * (1 - P) by
            simp only [G, Matrix.mul_assoc],
          ← hAA]
        simp only [Matrix.mul_assoc]
      rw [e, hA1P, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  set M := Y * Ap
  have hMA : M * A = Y := by
    rw [Matrix.mul_assoc, hApA]
    have := hY1P
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  -- isometry on the range of A
  have hnorm : ∀ v : R → ℂ, ‖(WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)‖ := by
    intro v
    have h1 := norm_sq_eq (WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)
    have h2 := norm_sq_eq (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)
    simp only [WithLp.ofLp_toLp] at h1 h2
    rw [dot_self] at h1
    rw [dot_self, hAh, hAA] at h2
    rw [← h2] at h1
    have := Complex.ofReal_injective h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  set TA := Matrix.toEuclideanLin A
  set S := LinearMap.range TA
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
    { toLinearMap := (Matrix.toEuclideanLin M).domRestrict S
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simp only [LinearMap.domRestrict_apply, TA, Matrix.toEuclideanLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hMA, Submodule.coe_norm]
        exact hnorm _ }
  set W := L.extend
  set Wm := Matrix.toEuclideanLin.symm W.toLinearMap
  have hW : ∀ x, Matrix.toEuclideanLin Wm x = W x := by
    intro x; simp [Wm]
  have hWv : ∀ u : R → ℂ, Wm *ᵥ u = (W (WithLp.toLp 2 u)).ofLp := by
    intro u; rw [← hW]; simp
  have hWA : Wm * A = Y := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [← Matrix.mulVec_mulVec, hWv]
    have hx : (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R) ∈ S := ⟨WithLp.toLp 2 v, by simp [TA]⟩
    have := L.extend_apply ⟨_, hx⟩
    simp only at this
    rw [this]
    simp [L, Matrix.mulVec_mulVec, hMA]
  have hU : Wm ∈ Matrix.unitaryGroup R ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := W.inner_map_map (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j 1)
    have hc : ∀ j : R, (W (EuclideanSpace.single j (1 : ℂ))).ofLp = Wm.col j := by
      intro j; rw [← Matrix.mulVec_single_one, hWv]; rfl
    rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at this
    simp only [hc] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    convert this using 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.col_apply, RCLike.inner_apply]
      exact mul_comm _ _
    · simp [EuclideanSpace.single_apply, eq_comm]
  exact ⟨⟨Wm, hU⟩, hWA⟩
lemma psd_tr {X : Matrix R R ℂ} (h : X.PosSemidef) : X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have := h.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact Complex.ext (by simp) (by simp [← this.2])

/-- `|Tr (Z V)| ≤ Tr √(Z Z†)` for unitary `V`. -/
lemma abs_tr_le (Z V : Matrix R R ℂ) (hV : V * Vᴴ = 1) :
    ‖(Z * V).trace‖ ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set t := (Z * V).trace
  by_cases ht : t = 0
  · rw [ht, norm_zero]
    exact CFCBasics.psd_re (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) :
      0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  set c : ℂ := star t / (‖t‖ : ℂ)
  have hn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ht
  have hc : c * star c = 1 := by
    simp only [c, star_div₀, star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    rw [div_mul_div_comm, Complex.conj_mul', ← pow_two]
    exact div_self (pow_ne_zero 2 hn)
  have h := CFCBasics.re_tr_le (c • (Z * V))
  have e1 : (c • (Z * V)) * (c • (Z * V))ᴴ = Z * Zᴴ := by
    rw [conjTranspose_smul, smul_mul_smul_comm, hc, one_smul, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul]
  have e2 : (c • (Z * V)).trace.re = ‖t‖ := by
    rw [Matrix.trace_smul, smul_eq_mul]
    simp only [c, Complex.star_def]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [pow_two, mul_div_assoc, div_self hn, mul_one]
    simp only [Complex.ofReal_re]; rfl
  rw [e1, e2] at h
  exact h

lemma tr_attain (Z : Matrix R R ℂ) :
    ∃ V : Matrix.unitaryGroup R ℂ, ‖(Z * (V : Matrix R R ℂ)).trace‖ =
      (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  obtain ⟨W, hW⟩ := polar Zᴴ
  rw [conjTranspose_conjTranspose] at hW
  have hZ : Z = cfc Real.sqrt (Z * Zᴴ) * (W : Matrix R R ℂ)ᴴ := by
    have := congrArg conjTranspose hW
    rw [conjTranspose_conjTranspose, conjTranspose_mul, CFCBasics.sqrt_herm] at this
    exact this.symm
  refine ⟨W, ?_⟩
  have hWW : (W : Matrix R R ℂ)ᴴ * W = 1 := by
    have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  nth_rewrite 1 [hZ]
  rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hp : (cfc Real.sqrt (Z * Zᴴ)).PosSemidef :=
    (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  rw [psd_tr hp, Complex.norm_real, Real.norm_of_nonneg (CFCBasics.psd_re hp), Complex.ofReal_re]

end Polar
end Nuclear
end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearNorm -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma sqrt_eq_cfc (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg,cfcₙ_eq_cfc]

/-- The public trace norm agrees with either rectangular Gram expression. -/
lemma traceNorm_eq_left (A : Matrix α β ℂ) :
    WildeQIT.traceNorm A=(cfc Real.sqrt (A*Aᴴ)).trace.re := by
  rw [WildeQIT.traceNorm,sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self A),
    Nuclear.tr_cfc_swap A _ Real.sqrt_zero]

lemma traceNorm_nonneg (A : Matrix α β ℂ) : 0 ≤ WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact CFCBasics.psd_re (cfc_nonneg (fun _ _=>Real.sqrt_nonneg _) :
    0 ≤ cfc Real.sqrt (A*Aᴴ)).posSemidef

lemma traceNorm_zero : WildeQIT.traceNorm (0:Matrix α β ℂ)=0 := by
  simp [WildeQIT.traceNorm]

lemma traceNorm_dual (A : Matrix α α ℂ) (U : Matrix.unitaryGroup α ℂ) :
    ‖(A*(U:Matrix α α ℂ)).trace‖ ≤ WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact Nuclear.abs_tr_le A U (by exact Unitary.coe_mul_star_self U)

lemma traceNorm_attain (A : Matrix α α ℂ) :
    ∃ U : Matrix.unitaryGroup α ℂ,‖(A*(U:Matrix α α ℂ)).trace‖=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact Nuclear.tr_attain A

lemma traceNorm_add_le_square (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A+B) ≤ WildeQIT.traceNorm A+WildeQIT.traceNorm B := by
  obtain ⟨U,hU⟩:=traceNorm_attain (A+B)
  rw [← hU,add_mul,Matrix.trace_add]
  exact (norm_add_le _ _).trans (add_le_add (traceNorm_dual A U) (traceNorm_dual B U))

lemma traceNorm_smul_square (c : ℂ) (A : Matrix α α ℂ) :
    WildeQIT.traceNorm (c • A)=‖c‖*WildeQIT.traceNorm A := by
  apply le_antisymm
  · obtain ⟨U,hU⟩:=traceNorm_attain (c • A)
    rw [← hU,Matrix.smul_mul,Matrix.trace_smul,norm_smul]
    exact mul_le_mul_of_nonneg_left (traceNorm_dual A U) (norm_nonneg _)
  · obtain ⟨U,hU⟩:=traceNorm_attain A
    have hh:=traceNorm_dual (c • A) U
    rwa [Matrix.smul_mul,Matrix.trace_smul,norm_smul,hU] at hh

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearOrder -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma sqrt_smul_sq (r : ℝ) (hr:0 ≤ r) (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    CFC.sqrt ((r^2:ℝ) • A)=r • CFC.sqrt A := by
  apply (CFC.sqrt_eq_iff _ _ (hA.smul (sq_nonneg r)).nonneg
    ((CFC.sqrt_nonneg A).posSemidef.smul hr).nonneg).mpr
  rw [smul_mul_smul_comm,CFC.sqrt_mul_sqrt_self A hA.nonneg,pow_two]

lemma traceNorm_of_posSemidef (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    WildeQIT.traceNorm A=A.trace.re := by
  rw [WildeQIT.traceNorm,hA.isHermitian.eq,CFC.sqrt_mul_self A hA.nonneg]

lemma traceNorm_conjTranspose (A : Matrix α β ℂ) : WildeQIT.traceNorm Aᴴ=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left,Matrix.conjTranspose_conjTranspose,WildeQIT.traceNorm,
    sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self A)]

lemma traceNorm_mul_coisometry (A : Matrix α β ℂ) (U : Matrix β γ ℂ) (hU:U*Uᴴ=1) :
    WildeQIT.traceNorm (A*U)=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left,traceNorm_eq_left,Matrix.conjTranspose_mul]
  rw [show A*U*(Uᴴ*Aᴴ)=A*(U*Uᴴ)*Aᴴ by simp only [Matrix.mul_assoc],hU,Matrix.mul_one]

open scoped Matrix.Norms.L2Operator in
/-- Multiplication by an operator bounded by r contracts nuclear norm by r;
the hypothesis is expressed by the actual finite positive-semidefinite order. -/
theorem traceNorm_mul_left_le (A : Matrix α β ℂ) (B : Matrix β γ ℂ) (r : ℝ) (hr:0 ≤ r)
    (hA:((r^2:ℝ) • (1:Matrix β β ℂ)-Aᴴ*A).PosSemidef) :
    WildeQIT.traceNorm (A*B) ≤ r*WildeQIT.traceNorm B := by
  have hconj:=hA.mul_mul_conjTranspose_same Bᴴ
  rw [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one] at hconj
  have he:(A*B)ᴴ*(A*B)=Bᴴ*(Aᴴ*A)*B := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hord:(A*B)ᴴ*(A*B) ≤ (r^2:ℝ) • (Bᴴ*B) := by
    rw [Matrix.le_iff,he]
    exact hconj
  have hs:=CFC.sqrt_le_sqrt _ _ hord
  have ht:=CFCBasics.psd_re (Matrix.le_iff.mp hs)
  rw [Matrix.trace_sub,Complex.sub_re] at ht
  rw [sqrt_smul_sq r hr _ (Matrix.posSemidef_conjTranspose_mul_self B),Matrix.trace_smul,
    Complex.real_smul] at ht
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at ht
  change 0 ≤ r*WildeQIT.traceNorm B-WildeQIT.traceNorm (A*B) at ht
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTraceDistance -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped MatrixOrder ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

lemma trace_mul_posSemidef_nonneg (A B : Matrix α α ℂ) (ha:A.PosSemidef) (hb:B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let S := CFC.sqrt A
  have hs:Sᴴ=S := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have ht:=hb.mul_mul_conjTranspose_same S
  have htr:0 ≤ (S*B*Sᴴ).trace.re := (Complex.nonneg_iff.mp ht.trace_nonneg).1
  rw [hs,Matrix.trace_mul_cycle] at htr
  change 0 ≤ ((CFC.sqrt A*CFC.sqrt A)*B).trace.re at htr
  rw [CFC.sqrt_mul_sqrt_self A ha.nonneg] at htr
  exact htr

lemma trace_mul_effect_le (P A : Matrix α α ℂ) (ha:A.PosSemidef)
    (hp:(1-P).PosSemidef) : (P*A).trace.re ≤ A.trace.re := by
  have ht:=trace_mul_posSemidef_nonneg (1-P) A hp ha
  simp only [sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re] at ht
  linarith

/-- The sharp half-trace-norm variational bound for a traceless Hermitian
matrix, with an arbitrary matrix effect. -/
theorem trace_effect_le_half_traceNorm (H P : Matrix α α ℂ)
    (hH:H.IsHermitian) (htr:H.trace=0) (hp:P.PosSemidef) (hpc:(1-P).PosSemidef) :
    (P*H).trace.re ≤ WildeQIT.traceNorm H/2 := by
  have hpos:(H⁺).PosSemidef := (CFC.posPart_nonneg H).posSemidef
  have hneg:(H⁻).PosSemidef := (CFC.negPart_nonneg H).posSemidef
  have habs:CFC.abs H=H⁺+H⁻ := (CFC.posPart_add_negPart H hH.isSelfAdjoint).symm
  have hsplit:H=H⁺-H⁻ := (CFC.posPart_sub_negPart H hH.isSelfAdjoint).symm
  have heq:(H⁺).trace.re=(H⁻).trace.re := by
    have hh:=congrArg (fun M : Matrix α α ℂ=>M.trace.re) hsplit
    rw [htr,Matrix.trace_sub] at hh
    simp only [Complex.zero_re,Complex.sub_re] at hh
    linarith
  have hnorm:WildeQIT.traceNorm H=(H⁺).trace.re+(H⁻).trace.re := by
    change (CFC.abs H).trace.re= _
    rw [habs,Matrix.trace_add,Complex.add_re]
  have h1:=trace_mul_effect_le P H⁺ hpos hpc
  have h2:=trace_mul_posSemidef_nonneg P H⁻ hp hneg
  have h3:(P*H).trace.re=(P*H⁺).trace.re-(P*H⁻).trace.re := by
    conv_lhs => rw [hsplit]
    rw [mul_sub,Matrix.trace_sub,Complex.sub_re]
  linarith

/-- Outcome probabilities of an arbitrary effect differ by at most the
public trace distance of two equal-trace Hermitian matrices. -/
theorem trace_effect_sub_le_tdist (A B P : Matrix α α ℂ)
    (ha:A.IsHermitian) (hb:B.IsHermitian) (ht:A.trace=B.trace)
    (hp:P.PosSemidef) (hpc:(1-P).PosSemidef) :
    (P*(A-B)).trace.re ≤ tdist A B := by
  exact trace_effect_le_half_traceNorm (A-B) P (ha.sub hb) (by simp [ht]) hp hpc

end SpaceReset.Hardness.QuantumRankProof

/- Module RandomOracleDiamondWitness -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open SpaceReset.Hardness.FidelityProof
open scoped ComplexOrder ComplexConjugate MatrixOrder

lemma density_traceNorm_one {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℂ) (hA:WildeQIT.IsDensityOperator A) : WildeQIT.traceNorm A=1 := by
  rw [traceNorm_of_posSemidef A hA.1,hA.2,Complex.one_re]

lemma density_sub_traceNorm_le_two {α : Type} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℂ) (hA:WildeQIT.IsDensityOperator A) (hB:WildeQIT.IsDensityOperator B) :
    WildeQIT.traceNorm (A-B) ≤ 2 := by
  have hn:WildeQIT.traceNorm (-B)=WildeQIT.traceNorm B := by
    simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using traceNorm_smul_square (-1:ℂ) B
  rw [sub_eq_add_neg]
  exact (traceNorm_add_le_square A (-B)).trans_eq (by
    rw [hn,density_traceNorm_one A hA,density_traceNorm_one B hB]; norm_num)

variable {n m m₀ k : ℕ}

/-- The actual public diamond optimization is bounded over every finite
reference and every mixed density; no fixed-reference convention is substituted. -/
lemma diamond_values_bdd (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (U : synthesis_Unitary n) :
    BddAbove {z:ℝ | ∃(b:ℕ)
      (ρ:Matrix (synthesis_Bits n×Fin b) (synthesis_Bits n×Fin b) ℂ),
      WildeQIT.IsDensityOperator ρ ∧ z=WildeQIT.traceNorm
        (synthesis_amplify (synthesis_actualChannel C f) b ρ-
          synthesis_amplify (synthesis_unitaryChannel U) b ρ)/2} := by
  refine ⟨1,?_⟩
  rintro z ⟨b,ρ,hρ,rfl⟩
  have hh:=density_sub_traceNorm_le_two _ _ (actualChannel_amplify_density C f b ρ hρ)
    (unitaryChannel_amplify_density U b ρ hρ)
  linarith

/-- Any genuine mixed-state finite-reference experiment is a valid lower
bound on the public supremum, with its boundedness proved above. -/
theorem diamond_ge_input (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (U : synthesis_Unitary n) (b : ℕ)
    (ρ : Matrix (synthesis_Bits n×Fin b) (synthesis_Bits n×Fin b) ℂ)
    (hρ:WildeQIT.IsDensityOperator ρ) :
    WildeQIT.traceNorm (synthesis_amplify (synthesis_actualChannel C f) b ρ-
      synthesis_amplify (synthesis_unitaryChannel U) b ρ)/2 ≤
        synthesis_diamond (synthesis_actualChannel C f) (synthesis_unitaryChannel U) :=
  le_csSup (diamond_values_bdd C f U) ⟨b,ρ,hρ,rfl⟩

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleChoiVectors -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open scoped ComplexOrder ComplexConjugate Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

def pure (v : α→ℂ) : Matrix α α ℂ:=Matrix.vecMulVec v (star v)

lemma pure_pos (v : α→ℂ) : (pure v).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
lemma pure_hermitian (v : α→ℂ) : (pure v).IsHermitian := (pure_pos v).isHermitian

lemma pure_trace (v : α→ℂ) : (pure v).trace=star v ⬝ᵥ v := by
  simp [pure,Matrix.vecMulVec_apply,Pi.star_apply,Matrix.trace,Matrix.diag,dotProduct,mul_comm]

lemma pure_density (v : α→ℂ) (hv:star v ⬝ᵥ v=1) : WildeQIT.IsDensityOperator (pure v) :=
  ⟨pure_pos v,(pure_trace v).trans hv⟩

lemma pure_idempotent (v : α→ℂ) (hv:star v ⬝ᵥ v=1) : pure v*pure v=pure v := by
  unfold pure
  rw [Matrix.vecMulVec_mul_vecMulVec,hv,one_smul]

lemma pure_complement_pos (v : α→ℂ) (hv:star v ⬝ᵥ v=1) : (1-pure v).PosSemidef := by
  have he:(1-pure v)ᴴ*(1-pure v)=1-pure v := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,(pure_hermitian v).eq,
      sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,pure_idempotent v hv]
    abel
  rw [←he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def vectorized (M : Matrix α α ℂ) : α×Fin (Fintype.card α)→ℂ :=
  fun p=>M p.1 ((Fintype.equivFin α).symm p.2)/(Real.sqrt (Fintype.card α:ℝ):ℂ)

lemma vectorized_inner (A B : Matrix α α ℂ) :
    star (vectorized A) ⬝ᵥ vectorized B=(Aᴴ*B).trace/(Fintype.card α:ℂ) := by
  have hd:(Real.sqrt (Fintype.card α:ℝ):ℂ)*(Real.sqrt (Fintype.card α:ℝ):ℂ)=
      (Fintype.card α:ℂ) := by
    rw [←Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _)]
    norm_cast
  have ht:∀x:α,(∑i:Fin (Fintype.card α),star (A x ((Fintype.equivFin α).symm i))*
      B x ((Fintype.equivFin α).symm i))=∑y:α,star (A x y)*B x y := by
    intro x
    exact (Fintype.equivFin α).symm.sum_comp (fun y:α=>star (A x y)*B x y)
  simp only [dotProduct,Fintype.sum_prod_type,Pi.star_apply,vectorized,star_div₀,
    Complex.star_def,Complex.conj_ofReal,div_mul_div_comm,hd]
  calc
    _ = (∑x:α,∑i:Fin (Fintype.card α),star (A x ((Fintype.equivFin α).symm i))*
        B x ((Fintype.equivFin α).symm i))/(Fintype.card α:ℂ) := by
      simp only [sum_div,Complex.star_def]
    _ = _ := by
      congr 1
      simp only [ht]
      simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
      exact sum_comm

lemma vectorized_unit_norm [Nonempty α] (U : Matrix.unitaryGroup α ℂ) :
    star (vectorized (U:Matrix α α ℂ)) ⬝ᵥ vectorized (U:Matrix α α ℂ)=1 := by
  rw [vectorized_inner]
  have hU:(U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 := Unitary.star_mul_self_of_mem U.property
  rw [hU,Matrix.trace_one]
  have hc:(Fintype.card α:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  exact div_self hc

lemma vectorized_one_norm [Nonempty α] :
    star (vectorized (1:Matrix α α ℂ)) ⬝ᵥ vectorized (1:Matrix α α ℂ)=1 :=
  vectorized_unit_norm (1:Matrix.unitaryGroup α ℂ)

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleChoiSemantics -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open scoped ComplexConjugate Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

lemma pure_conjugate (M : Matrix α α ℂ) (v : α→ℂ) : M*pure v*Mᴴ=pure (M*ᵥv) := by
  unfold pure
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,←star_mulVec]

lemma pure_overlap (u v : α→ℂ) :
    (pure u*pure v).trace=(star u ⬝ᵥv)*(star v ⬝ᵥu) := by
  unfold pure
  rw [Matrix.vecMulVec_mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_smul]
  simp only [smul_eq_mul,dotProduct_comm]

lemma vectorized_left (M A : Matrix α α ℂ) :
    (M ⊗ₖ (1:Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℂ))*ᵥvectorized A=
      vectorized (M*A) := by
  ext p
  rcases p with ⟨x,i⟩
  simp [Matrix.mulVec,dotProduct,vectorized,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,
    Matrix.one_apply,mul_ite,ite_mul,mul_div_assoc,Matrix.mul_apply,Finset.sum_div]

variable {n : ℕ} {ι : Type} [Fintype ι]

lemma amplify_bell (M : ι→synthesis_Mat n) :
    synthesis_amplify (synthesis_coordinates (krausLinear M)) (Fintype.card (synthesis_Bits n))
      (pure (vectorized (1:synthesis_Mat n)))=
      ∑i,pure (vectorized (M i)) := by
  rw [amplify_kraus]
  unfold krausMap
  simp_rw [pure_conjugate,vectorized_left,Matrix.mul_one]

lemma unitaryChannel_bell (U : synthesis_Unitary n) :
    synthesis_amplify (synthesis_unitaryChannel U) (Fintype.card (synthesis_Bits n))
      (pure (vectorized (1:synthesis_Mat n)))=pure (vectorized (U:synthesis_Mat n)) := by
  rw [unitaryChannel_kraus,amplify_bell]
  exact Fintype.sum_unique _

lemma actualChannel_bell {m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_amplify (synthesis_actualChannel C f) (Fintype.card (synthesis_Bits n))
      (pure (vectorized (1:synthesis_Mat n)))=
      ∑a:synthesis_Bits (m-n),pure (vectorized (slice C.system_le (synthesis_W C f*synthesis_J C) a)) := by
  rw [actualChannel_kraus,amplify_bell]

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleChannelCorrelation -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n : ℕ}

/-- Heisenberg dual in the public matrix-unit channel coordinates. -/
def channelDual (F : synthesis_Channel n) (P : synthesis_Mat n) : synthesis_Mat n :=
  fun x y=>∑a:synthesis_Bits n,∑b:synthesis_Bits n,P a b*F (b,a) (y,x)

/-- Correlation depends only on the target channel, so the published
channel-coordinate coupling can be used without any unproved disintegration. -/
def channelCorrelation (A : synthesis_Mat n) (P : synthesis_Pauli n)
    (G : synthesis_Channel n) : ℝ :=
  (DirectFidelity.State.W P*synthesis_apply G A).trace.re/(2:ℝ)^n

lemma coordinates_kraus_apply {ι : Type} [Fintype ι] (M : ι→synthesis_Mat n)
    (a b x y : synthesis_Bits n) :
    synthesis_coordinates (krausLinear M) (b,a) (y,x)=∑i,M i b y*star (M i a x) := by
  change krausMap M (Matrix.single y x 1) b a=_
  simp [krausMap,Matrix.sum_apply,Matrix.mul_apply,Matrix.single_apply,Matrix.conjTranspose_apply,mul_ite,ite_mul]
  simp [ite_and,Finset.sum_ite_eq,Finset.sum_ite_eq']

lemma channelDual_kraus {ι : Type} [Fintype ι] (M : ι→synthesis_Mat n) (P : synthesis_Mat n) :
    channelDual (synthesis_coordinates (krausLinear M)) P=∑i,(M i)ᴴ*P*M i := by
  ext x y
  simp only [channelDual,coordinates_kraus_apply,Finset.mul_sum,Matrix.sum_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
  calc
    _ = ∑b:synthesis_Bits n,∑i:ι,∑a:synthesis_Bits n,P a b*(M i b y*star (M i a x)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      rw [sum_comm]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro a ha
      ring

lemma actualChannel_dual {m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) (P : synthesis_Pauli n) :
    channelDual (synthesis_actualChannel C f) (DirectFidelity.State.W P)=synthesis_observable C f P := by
  rw [actualChannel_kraus,channelDual_kraus,observable_kraus]

lemma unitaryChannel_apply (U : synthesis_Unitary n) (A : synthesis_Mat n) :
    synthesis_apply (synthesis_unitaryChannel U) A=(U:synthesis_Mat n)*A*(U:synthesis_Mat n)ᴴ := by
  rw [unitaryChannel_kraus,coordinates_linear]
  change krausMap (fun _:Unit=>(U:synthesis_Mat n)) A=_
  simp only [krausMap,Fintype.sum_unique]

lemma unitaryChannel_correlation (A : synthesis_Mat n) (P : synthesis_Pauli n)
    (U : synthesis_Unitary n) :
    channelCorrelation A P (synthesis_unitaryChannel U)=synthesis_correlation A P U := by
  have ht:(DirectFidelity.State.W P*((U:synthesis_Mat n)*A*(U:synthesis_Mat n)ᴴ)).trace=
      (A*((U:synthesis_Mat n)ᴴ*DirectFidelity.State.W P*(U:synthesis_Mat n))).trace := by
    calc
      _ = ((DirectFidelity.State.W P*((U:synthesis_Mat n)*A))*(U:synthesis_Mat n)ᴴ).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((U:synthesis_Mat n)ᴴ*DirectFidelity.State.W P*((U:synthesis_Mat n)*A)).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [←Matrix.mul_assoc,Matrix.trace_mul_comm]
  unfold channelCorrelation synthesis_correlation
  rw [unitaryChannel_apply,ht]

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOraclePauliCompleteness -/

namespace RandomOracleUnitarySynthesis.PauliProof
open DirectFidelity.State

theorem pauli_orth1 (a b c d : Fin 2) :
    ∑ j : Fin 4, pauli1 j a b * star (pauli1 j c d) = if a = c ∧ b = d then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pauli1, Fin.sum_univ_four] <;> norm_num

theorem pauli_orth {n : ℕ} (y x y' x' : Q n) :
    ∑ k : P n, W k y x * star (W k y' x') = if y = y' ∧ x = x' then (2 : ℂ) ^ n else 0 := by
  have e1 : ∀ k : P n, W k y x * star (W k y' x') =
      ∏ i, (pauli1 (k i) (y i) (x i) * star (pauli1 (k i) (y' i) (x' i))) := by
    intro k
    unfold W
    rw [star_prod, ← Finset.prod_mul_distrib]
  simp only [e1]
  rw [← Fintype.prod_sum (fun i j => pauli1 j (y i) (x i) * star (pauli1 j (y' i) (x' i)))]
  simp only [pauli_orth1]
  by_cases h : y = y' ∧ x = x'
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc
      push_neg at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem trace_mul_W {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ) (k : P n) :
    (σ * W k).trace = ∑ z : Q n × Q n, σ z.1 z.2 * W k z.2 z.1 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]

theorem polar {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) :
    ∑ k : P n, (ρ * W k).trace * star ((σ * W k).trace) =
      (2 : ℂ) ^ n * ∑ z : Q n × Q n, ρ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [trace_mul_W, star_sum, Finset.sum_mul_sum, star_mul']
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  have : ∀ z' : Q n × Q n, ∑ k : P n, ρ z.1 z.2 * W k z.2 z.1 * (star (σ z'.1 z'.2) *
      star (W k z'.2 z'.1)) = ρ z.1 z.2 * star (σ z'.1 z'.2) *
      (if z.2 = z'.2 ∧ z.1 = z'.1 then (2 : ℂ) ^ n else 0) := by
    intro z'
    rw [← pauli_orth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [this]
  rw [Finset.sum_eq_single z]
  · simp; ring
  · intro z' _ hz'
    have : ¬ (z.2 = z'.2 ∧ z.1 = z'.1) := by
      rintro ⟨h1, h2⟩; exact hz' (Prod.ext h2 h1).symm
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ z) h

theorem pauli_herm1 (j : Fin 4) (a b : Fin 2) : star (pauli1 j a b) = pauli1 j b a := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [pauli1]

theorem W_herm {n : ℕ} (k : P n) : Matrix.conjTranspose (W k) = W k := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold W
  rw [star_prod]
  exact Finset.prod_congr rfl fun i _ => pauli_herm1 _ _ _

theorem trace_im {n : ℕ} (τ : Matrix (Q n) (Q n) ℂ) (hτ : τ.IsHermitian) (k : P n) :
    ((τ * W k).trace).im = 0 := by
  have h : star ((τ * W k).trace) = (τ * W k).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, W_herm, hτ.eq,
      Matrix.trace_mul_comm]
  rw [Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h

theorem trace_mul_herm {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) (hσ : σ.IsHermitian) :
    (ρ * σ).trace = ∑ z : Q n × Q n, ρ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have := congrFun (congrFun hσ.eq y) x
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]

theorem eq2 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ((ρ * σ).trace).re = ∑ k : P n, chi ρ k * chi σ k := by
  have hd : (0 : ℝ) < dim n := by unfold dim; positivity
  have hpol := congrArg Complex.re (polar ρ σ)
  rw [← trace_mul_herm ρ σ hσ] at hpol
  rw [show (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.re_sum] at hpol
  have hterm : ∀ k : P n, ((ρ * W k).trace * star ((σ * W k).trace)).re =
      ((ρ * W k).trace).re * ((σ * W k).trace).re := by
    intro k
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, trace_im σ hσ k]
    ring
  simp only [hterm] at hpol
  have hchi : ∀ k : P n, chi ρ k * chi σ k =
      ((ρ * W k).trace).re * ((σ * W k).trace).re / dim n := by
    intro k
    unfold chi
    rw [div_mul_div_comm, Real.mul_self_sqrt hd.le]
  simp only [hchi]
  rw [← Finset.sum_div, hpol]
  unfold dim
  field_simp

end RandomOracleUnitarySynthesis.PauliProof

namespace RandomOracleUnitarySynthesis.PauliProof
open DirectFidelity.State
lemma pauli_complete {n : ℕ} (a b c d : Q n) :
    (∑P:P n,W P a b*W P c d)=if a=d ∧ b=c then (2:ℂ)^n else 0 := by
  have he:∀P:P n,star (W P d c)=W P c d := by
    intro P
    exact congrFun (congrFun (W_herm P) c) d
  simpa only [he] using pauli_orth a b d c
end RandomOracleUnitarySynthesis.PauliProof

/- Module RandomOraclePauliTwirl -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.PauliProof
open Matrix Finset Classical DirectFidelity.State
open scoped ComplexConjugate

lemma pauli_twirl {n : ℕ} (X : Matrix (Q n) (Q n) ℂ) :
    (∑P:P n,W P*X*W P)=((2:ℂ)^n*X.trace) • (1:Matrix (Q n) (Q n) ℂ) := by
  ext a d
  simp only [Matrix.sum_apply,Matrix.mul_apply,Finset.sum_mul]
  calc
    _ = ∑b:Q n,∑c:Q n,∑P:P n,W P a c*X c b*W P b d := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      rw [sum_comm]
    _ = ∑b:Q n,∑c:Q n,X c b*(if a=d ∧ c=b then (2:ℂ)^n else 0) := by
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro c hc
      rw [←pauli_complete a c b d,Finset.mul_sum]
      apply sum_congr rfl
      intro P hP
      ring
    _ = _ := by
      by_cases had:a=d
      · subst d
        simp [Matrix.smul_apply,Matrix.one_apply,Matrix.trace,Matrix.diag,mul_comm]
        rw [←Finset.sum_mul]
        ring
      · simp [had,Matrix.smul_apply,Matrix.one_apply]

lemma pauli_trace_bilinear {n : ℕ} (A B : Matrix (Q n) (Q n) ℂ) :
    (∑P:P n,(A*W P*B*W P).trace)=(2:ℂ)^n*A.trace*B.trace := by
  rw [←Matrix.trace_sum]
  have he:(∑P:P n,A*W P*B*W P)=A*(∑P:P n,W P*B*W P) := by
    simp only [Matrix.mul_sum,Matrix.mul_assoc]
  rw [he,pauli_twirl,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

lemma pauli_kraus_overlap {n : ℕ} (M U : Matrix (Q n) (Q n) ℂ) :
    (∑P:P n,(Mᴴ*W P*M*Uᴴ*W P*U).trace)=
      (2:ℂ)^n*star ((M*Uᴴ).trace)*(M*Uᴴ).trace := by
  have he:∀P:P n,(Mᴴ*W P*M*Uᴴ*W P*U).trace=
      ((U*Mᴴ)*W P*(M*Uᴴ)*W P).trace := by
    intro P
    rw [Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  simp only [he]
  rw [pauli_trace_bilinear]
  have ht:(U*Mᴴ).trace=star ((M*Uᴴ).trace) := by
    rw [←Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [ht]

end RandomOracleUnitarySynthesis.PauliProof

/- Module RandomOraclePauliUnitary -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.PauliProof
open Matrix Finset Classical DirectFidelity.State
open scoped ComplexConjugate

lemma pauli1_square (p : Fin 4) (a b : Fin 2) :
    (∑c:Fin 2,pauli1 p a c*pauli1 p c b)=if a=b then (1:ℂ) else 0 := by
  fin_cases p <;> fin_cases a <;> fin_cases b <;> norm_num [pauli1,Fin.sum_univ_two]

lemma pauli1_trace (p : Fin 4) :
    (∑a:Fin 2,pauli1 p a a)=if p=0 then (2:ℂ) else 0 := by
  fin_cases p <;> norm_num [pauli1,Fin.sum_univ_two]

lemma W_square {n : ℕ} (P : P n) : W P*W P=1 := by
  ext x y
  simp only [Matrix.mul_apply,W]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i a=>pauli1 (P i) (x i) a*pauli1 (P i) a (y i))]
  simp only [pauli1_square,Matrix.one_apply]
  by_cases h:x=y
  · subst y
    simp
  · rw [if_neg h]
    have he:∃i:Fin n,x i≠y i := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩:=he
    exact prod_eq_zero (mem_univ i) (if_neg hi)

lemma W_unitary {n : ℕ} (P : P n) : W P∈Matrix.unitaryGroup (Q n) ℂ := by
  apply Unitary.mem_iff.mpr
  constructor
  · change (W P)ᴴ*W P=1
    rw [W_herm,W_square]
  · change W P*(W P)ᴴ=1
    rw [W_herm,W_square]

def pauliUnitary {n : ℕ} (P : P n) : Matrix.unitaryGroup (Q n) ℂ := ⟨W P,W_unitary P⟩

lemma trace_W {n : ℕ} (P : P n) :
    (W P).trace=if P=(fun _=>0) then (2:ℂ)^n else 0 := by
  simp only [Matrix.trace,Matrix.diag,W]
  rw [←Fintype.prod_sum (fun i a=>pauli1 (P i) a a)]
  simp only [pauli1_trace]
  by_cases h:P=(fun _=>0)
  · rw [if_pos h]
    subst P
    simp
  · rw [if_neg h]
    have he:∃i:Fin n,P i≠0 := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩:=he
    exact prod_eq_zero (mem_univ i) (if_neg hi)

lemma W_zero (n : ℕ) : W (fun _:Fin n=>0)=1 := by
  have h0:∀a b:Fin 2,pauli1 0 a b=if a=b then (1:ℂ) else 0 := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num [pauli1]
  ext x y
  simp only [W,h0,Matrix.one_apply]
  by_cases h:x=y
  · subst y
    simp
  · rw [if_neg h]
    have he:∃i:Fin n,x i≠y i := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩:=he
    exact prod_eq_zero (mem_univ i) (if_neg hi)

end RandomOracleUnitarySynthesis.PauliProof

/- Module RandomOracleSegments -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma segment_self (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a : ℕ) :
    synthesis_segment C f a a=synthesis_gate C a := by simp [synthesis_segment]

lemma segment_succ (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a b : ℕ)
    (hab:a ≤ b) : synthesis_segment C f a (b+1)=
      synthesis_gate C (b+1)*synthesis_oracle C f*synthesis_segment C f a b := by
  unfold synthesis_segment
  have hd:b+1-a=(b-a)+1 := by omega
  rw [hd,List.range_succ,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  have hi:a+(b-a)+1=b+1 := by omega
  rw [hi]

/-- Literal circuit-fold product difference; each summand uses the left
segment from f and the right segment from g, with no unproved hybrid rule. -/
theorem segment_difference (C : synthesis_Circuit n m m₀ k) (f g : synthesis_Oracle m₀)
    (b : ℕ) :
    synthesis_segment C g 0 b-synthesis_segment C f 0 b=
      ∑j∈Finset.range b,synthesis_segment C f (j+1) b*
        (synthesis_oracle C g-synthesis_oracle C f)*synthesis_segment C g 0 j := by
  induction b with
  | zero => simp [synthesis_segment]
  | succ b ih =>
    rw [segment_succ C g 0 b (Nat.zero_le b),segment_succ C f 0 b (Nat.zero_le b),sum_range_succ]
    have he:synthesis_gate C (b+1)*synthesis_oracle C g*synthesis_segment C g 0 b-
        synthesis_gate C (b+1)*synthesis_oracle C f*synthesis_segment C f 0 b=
        synthesis_gate C (b+1)*synthesis_oracle C f*
          (synthesis_segment C g 0 b-synthesis_segment C f 0 b)+
        synthesis_gate C (b+1)*(synthesis_oracle C g-synthesis_oracle C f)*synthesis_segment C g 0 b := by
      noncomm_ring
    rw [he,ih,Matrix.mul_sum,segment_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [segment_succ C f (j+1) b (by have hh:=Finset.mem_range.mp hj;omega)]
    simp only [Matrix.mul_assoc]

theorem A_difference (C : synthesis_Circuit n m m₀ k) (f g : synthesis_Oracle m₀) :
    synthesis_A C g-synthesis_A C f=
      ∑j:Fin k,synthesis_left C f j*(synthesis_oracle C g-synthesis_oracle C f)*synthesis_right C g j := by
  unfold synthesis_A synthesis_W
  rw [← Matrix.sub_mul,← Matrix.mul_sub,segment_difference,Matrix.mul_sum,Matrix.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [synthesis_left,synthesis_right,Matrix.mul_assoc]

lemma projector_idempotent (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀) :
    synthesis_projector C x*synthesis_projector C x=synthesis_projector C x := by
  ext y z
  rw [projector_rows]
  by_cases h:synthesis_prefix C.oracle_le y=x <;> simp [synthesis_projector,h]

lemma oracle_flip_difference (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_oracle C (synthesis_flip f x)-synthesis_oracle C f=
      (if f x then (2:ℂ) else -2) • synthesis_projector C x := by
  ext y z
  by_cases hyz:y=z
  · subst z
    by_cases hx:synthesis_prefix C.oracle_le y=x
    · simp [synthesis_oracle,synthesis_flip,synthesis_projector,hx]
      cases f x <;> norm_num
    · simp [synthesis_oracle,synthesis_flip,synthesis_projector,hx,Ne.symm hx]
  · simp [synthesis_oracle,synthesis_projector,Matrix.diagonal_apply,hyz]

theorem A_flip_difference (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_A C (synthesis_flip f x)-synthesis_A C f=
      (if f x then (2:ℂ) else -2) •
        ∑j:Fin k,(synthesis_left C f j*synthesis_projector C x)*
          (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j) := by
  rw [A_difference,oracle_flip_difference,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc (synthesis_projector C x) (synthesis_projector C x),
    projector_idempotent]

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOracleObservableCircuit -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open InfluenceProof PauliProof
open scoped ComplexConjugate Kronecker
variable {n m m₀ k : ℕ}

lemma liftPauli_unitary (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n) :
    synthesis_liftPauli C P∈synthesis_Unitary m := by
  have he:(synthesis_liftPauli C P).submatrix (joinEquiv C.system_le)
      (joinEquiv C.system_le)=DirectFidelity.State.W P ⊗ₖ
        (1:Matrix (synthesis_Bits (m-n)) (synthesis_Bits (m-n)) ℂ) :=
    liftOperator_reindex C.system_le (DirectFidelity.State.W P)
  apply Unitary.mem_iff.mpr
  constructor
  all_goals
    apply (Matrix.reindex (joinEquiv C.system_le).symm (joinEquiv C.system_le).symm).injective
    change _ = (1:synthesis_Mat m).submatrix (joinEquiv C.system_le) (joinEquiv C.system_le)
    simp only [Matrix.reindex_apply,Equiv.symm_symm,Matrix.star_eq_conjTranspose]
    rw [←Matrix.submatrix_mul_equiv _ _ (joinEquiv C.system_le)
      (joinEquiv C.system_le) (joinEquiv C.system_le)]
    simp only [←Matrix.conjTranspose_submatrix,he,Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one,←Matrix.mul_kronecker_mul,W_herm,W_square,
      Matrix.one_mul,Matrix.submatrix_one_equiv,Matrix.one_kronecker_one]


lemma liftPauli_hermitian (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n) :
    (synthesis_liftPauli C P).IsHermitian := by
  have he:=W_herm P
  ext x y
  change star (if synthesis_suffix C.system_le y=synthesis_suffix C.system_le x then
      DirectFidelity.State.W P (synthesis_prefix C.system_le y) (synthesis_prefix C.system_le x)
      else 0)=(if synthesis_suffix C.system_le x=synthesis_suffix C.system_le y then
      DirectFidelity.State.W P (synthesis_prefix C.system_le x) (synthesis_prefix C.system_le y)
      else 0)
  by_cases h:synthesis_suffix C.system_le x=synthesis_suffix C.system_le y
  · simp only [if_pos h,if_pos h.symm]
    exact congrFun (congrFun he (synthesis_prefix C.system_le x)) (synthesis_prefix C.system_le y)
  · simp [h,Ne.symm h]

/-- Actual oracle-independent gate list for W†(P⊗I)W. The middle gate absorbs
V_k†(P⊗I)V_k, so there are exactly 2k calls, including k=0. -/
def observableCircuit (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n) :
    synthesis_Circuit n m m₀ (2*k) where
  system_le:=C.system_le
  oracle_le:=C.oracle_le
  gates i:=if h:i.val<k then C.gates ⟨i.val,by omega⟩ else
    if he:i.val=k then
      star (C.gates ⟨k,by omega⟩)*⟨synthesis_liftPauli C P,liftPauli_unitary C P⟩*
        C.gates ⟨k,by omega⟩
    else star (C.gates ⟨2*k-i.val,by omega⟩)

lemma observableCircuit_oracle (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) : synthesis_oracle (observableCircuit C P) f=synthesis_oracle C f := rfl

lemma observableCircuit_gate_lt (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (i:ℕ) (hi:i<k) : synthesis_gate (observableCircuit C P) i=synthesis_gate C i := by
  simp [synthesis_gate,observableCircuit,hi,show i<2*k+1 by omega,show i<k+1 by omega]

lemma observableCircuit_gate_mid (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n) :
    synthesis_gate (observableCircuit C P) k=
      (synthesis_gate C k)ᴴ*synthesis_liftPauli C P*synthesis_gate C k := by
  simp [synthesis_gate,observableCircuit,show k<2*k+1 by omega]
  rfl

lemma observableCircuit_gate_gt (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (i:ℕ) (hi : k < i) (hik : i ≤ 2*k) :
    synthesis_gate (observableCircuit C P) i=(synthesis_gate C (2*k-i))ᴴ := by
  simp [synthesis_gate,observableCircuit,show ¬i<k by omega,show i≠k by omega,
    show i<2*k+1 by omega,show 2*k-i<k+1 by omega]
  rfl

lemma oracle_hermitian (C:synthesis_Circuit n m m₀ k) (f:synthesis_Oracle m₀) :
    (synthesis_oracle C f)ᴴ=synthesis_oracle C f := by
  simp only [synthesis_oracle,Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  cases h:f (synthesis_prefix C.oracle_le x) <;> simp [h]

lemma segment_left_step (C:synthesis_Circuit n m m₀ k) (f:synthesis_Oracle m₀)
    (a b:ℕ) (hab:a<b) : synthesis_segment C f a b=
      synthesis_segment C f (a+1) b*synthesis_oracle C f*synthesis_gate C a := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases he:a=b
    · subst a
      rw [segment_succ C f b b (le_refl _),segment_self,segment_self]
    · have hh:a<b := by omega
      rw [segment_succ C f a b hh.le,ih hh,
        segment_succ C f (a+1) b (by omega)]
      simp only [Matrix.mul_assoc]

lemma observableCircuit_prefix (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) (b:ℕ) (hb:b<k) :
    synthesis_segment (observableCircuit C P) f 0 b=synthesis_segment C f 0 b := by
  induction b with
  | zero => simp only [segment_self,observableCircuit_gate_lt C P 0 hb]
  | succ b ih =>
    rw [segment_succ _ _ 0 b (Nat.zero_le _),segment_succ _ _ 0 b (Nat.zero_le _),
      observableCircuit_gate_lt C P (b+1) hb,observableCircuit_oracle,ih (by omega)]

lemma observableCircuit_middle (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) : synthesis_segment (observableCircuit C P) f 0 k=
      (synthesis_gate C k)ᴴ*synthesis_liftPauli C P*synthesis_W C f := by
  cases k with
  | zero => simp only [synthesis_W,segment_self,observableCircuit_gate_mid]
  | succ k =>
    rw [segment_succ _ _ 0 k (Nat.zero_le _),observableCircuit_gate_mid,
      observableCircuit_oracle,observableCircuit_prefix C P f k (by omega)]
    unfold synthesis_W
    rw [segment_succ C f 0 k (Nat.zero_le _)]
    simp only [Matrix.mul_assoc]

lemma observableCircuit_tail (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) (j:ℕ) (hj:j≤k) :
    synthesis_segment (observableCircuit C P) f 0 (k+j)=
      (synthesis_segment C f (k-j) k)ᴴ*synthesis_liftPauli C P*synthesis_W C f := by
  induction j with
  | zero => simpa only [Nat.add_zero,Nat.sub_zero,segment_self] using observableCircuit_middle C P f
  | succ j ih =>
    have he:k+(j+1)=(k+j)+1 := by omega
    rw [he,segment_succ _ _ 0 (k+j) (Nat.zero_le _),
      observableCircuit_gate_gt C P (k+j+1) (by omega) (by omega),
      observableCircuit_oracle,ih (by omega)]
    have hleft:=segment_left_step C f (k-(j+1)) k (by omega)
    have hn:k-(j+1)+1=k-j := by omega
    rw [hn] at hleft
    rw [hleft,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,oracle_hermitian]
    have hind:2*k-(k+j+1)=k-(j+1) := by omega
    rw [hind]
    simp only [Matrix.mul_assoc]

lemma observableCircuit_W (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) : synthesis_W (observableCircuit C P) f=
      (synthesis_W C f)ᴴ*synthesis_liftPauli C P*synthesis_W C f := by
  simpa only [synthesis_W,Nat.sub_self,show k+k=2*k by omega] using
    observableCircuit_tail C P f k (le_refl _)

lemma observableCircuit_A (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) : synthesis_A (observableCircuit C P) f=synthesis_observable C f P := by
  unfold synthesis_A
  rw [observableCircuit_W]
  change (synthesis_J C)ᴴ*((synthesis_W C f)ᴴ*synthesis_liftPauli C P*synthesis_W C f)*synthesis_J C=_
  simp only [synthesis_observable,Matrix.mul_assoc]

lemma observable_hermitian (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (f:synthesis_Oracle m₀) : (synthesis_observable C f P).IsHermitian := by
  simpa only [synthesis_observable,Matrix.conjTranspose_mul,Matrix.mul_assoc] using
    Matrix.isHermitian_conjTranspose_mul_mul (synthesis_W C f*synthesis_J C)
      (liftPauli_hermitian C P)

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleChoiTester -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical
open SpaceReset.Hardness.FidelityProof SpaceReset.Hardness.QuantumRankProof
open scoped ComplexConjugate ComplexOrder MatrixOrder

lemma traceNorm_sub_comm {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A-B)=WildeQIT.traceNorm (B-A) := by
  have hn:WildeQIT.traceNorm (-(A-B))=WildeQIT.traceNorm (A-B) := by
    simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using traceNorm_smul_square (-1:ℂ) (A-B)
  simpa only [neg_sub] using hn.symm

/-- The pure Choi projector is an actual admissible finite-reference test
against the all-reference/all-mixed-state public diamond distance. -/
theorem choi_accept_ge_one_sub_diamond {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (U : synthesis_Unitary n) :
    1-synthesis_diamond (synthesis_actualChannel C f) (synthesis_unitaryChannel U) ≤
      (pure (vectorized (U:synthesis_Mat n))*
        synthesis_amplify (synthesis_actualChannel C f) (Fintype.card (synthesis_Bits n))
          (pure (vectorized (1:synthesis_Mat n)))).trace.re := by
  let bell:=pure (vectorized (1:synthesis_Mat n))
  let P:=pure (vectorized (U:synthesis_Mat n))
  let ρ:=synthesis_amplify (synthesis_actualChannel C f) (Fintype.card (synthesis_Bits n)) bell
  have hbell:WildeQIT.IsDensityOperator bell := pure_density _ vectorized_one_norm
  have hP:WildeQIT.IsDensityOperator P := pure_density _ (vectorized_unit_norm U)
  have hρ:WildeQIT.IsDensityOperator ρ := actualChannel_amplify_density C f _ bell hbell
  have htest: (P*(P-ρ)).trace.re ≤ WildeQIT.traceNorm (P-ρ)/2 :=
    trace_effect_le_half_traceNorm (P-ρ) P (hP.1.isHermitian.sub hρ.1.isHermitian)
      (by rw [Matrix.trace_sub,hP.2,hρ.2]; simp) hP.1
      (pure_complement_pos _ (vectorized_unit_norm U))
  have ht:(P*(P-ρ)).trace.re=1-(P*ρ).trace.re := by
    rw [mul_sub,pure_idempotent _ (vectorized_unit_norm U),Matrix.trace_sub,hP.2]
    simp only [Complex.sub_re,Complex.one_re]
  rw [ht,traceNorm_sub_comm] at htest
  have hd:=diamond_ge_input C f U (Fintype.card (synthesis_Bits n)) bell hbell
  have hUP:synthesis_amplify (synthesis_unitaryChannel U) (Fintype.card (synthesis_Bits n)) bell=P :=
    unitaryChannel_bell U
  rw [hUP] at hd
  change WildeQIT.traceNorm (ρ-P)/2 ≤ _ at hd
  change 1-synthesis_diamond (synthesis_actualChannel C f) (synthesis_unitaryChannel U) ≤ (P*ρ).trace.re
  linarith

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleProjectionEnergy -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_orthogonal (P : E→E)
    (hsym:∀x y,inner ℝ (P x) y=inner ℝ x (P y)) (hid:∀x,P (P x)=P x) (x y : E) :
    inner ℝ (P x) (y-P y)=0 := by
  rw [inner_sub_right,hsym,hsym,hid,sub_self]

lemma projection_loss (P : E→E)
    (hsym:∀x y,inner ℝ (P x) y=inner ℝ x (P y)) (hid:∀x,P (P x)=P x) (x : E) :
    ‖x-P x‖^2=‖x‖^2-‖P x‖^2 := by
  have hh:=hsym x (P x)
  rw [hid,real_inner_self_eq_norm_sq] at hh
  rw [norm_sub_sq_real]
  linarith

def projectionPath (P : ℕ→E→E) (a : E) : ℕ→E
  | 0=>a
  | i+1=>P i (projectionPath P a i)

lemma projectionPath_telescope (P : ℕ→E→E) (a : E) (T : ℕ) :
    (∑i∈range T,(projectionPath P a i-projectionPath P a (i+1)))=a-projectionPath P a T := by
  induction T with
  | zero => simp [projectionPath]
  | succ T ih => rw [sum_range_succ,ih];abel

lemma real_sum_telescope (D : ℕ→ℝ) (T : ℕ) :
    (∑i∈range T,(D i-D (i+1)))=D 0-D T := by
  induction T with
  | zero=>simp
  | succ T ih=>rw [sum_range_succ,ih];ring

/-- Finite noncommuting orthogonal-projection energy inequality. This is
the Hilbert-space core of the reversible resampling estimate; concrete
resampling-to-operator identities are established separately. -/
theorem projection_product_energy (P : ℕ→E→E) (a : E) (T : ℕ)
    (hsym:∀i<T,∀x y,inner ℝ (P i x) y=inner ℝ x (P i y))
    (hid:∀i<T,∀x,P i (P i x)=P i x) :
    inner ℝ a (a-projectionPath P a T)  ≤  2*(∑i∈range T,‖a-P i a‖^2) := by
  let v:=projectionPath P a
  let S:=∑i∈range T,‖a-P i a‖^2
  let Q:=∑i∈range T,‖v i-P i (v i)‖^2
  let D:=inner ℝ a (a-v T)
  have hS:0 ≤ S := sum_nonneg (fun i _=>sq_nonneg _)
  have hQ:0 ≤ Q := sum_nonneg (fun i _=>sq_nonneg _)
  have hsum:D=∑i∈range T,inner ℝ (a-P i a) (v i-P i (v i)) := by
    dsimp only [D]
    rw [← projectionPath_telescope P a T,inner_sum]
    apply sum_congr rfl
    intro i hi
    have horth:=projection_orthogonal (P i) (hsym i (mem_range.mp hi)) (hid i (mem_range.mp hi)) a (v i)
    rw [inner_sub_left,horth,sub_zero]
    rfl
  have hbound:D ≤ Real.sqrt S*Real.sqrt Q := by
    rw [hsum]
    have hc:=Real.sum_mul_le_sqrt_mul_sqrt (range T) (fun i=>‖a-P i a‖) (fun i=>‖v i-P i (v i)‖)
    exact (sum_le_sum (fun i _=>real_inner_le_norm _ _)).trans hc
  have hQloss:Q=‖a‖^2-‖v T‖^2 := by
    have he:Q=∑i∈range T,(‖v i‖^2-‖v (i+1)‖^2) := by
      apply sum_congr rfl
      intro i hi
      exact projection_loss (P i) (hsym i (mem_range.mp hi)) (hid i (mem_range.mp hi)) (v i)
    rw [he,real_sum_telescope]
    rfl
  have hDQ:Q ≤ 2*D := by
    rw [hQloss]
    dsimp only [D]
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖a-v T‖,norm_sub_sq_real a (v T)]
  have hD:0 ≤ D := by linarith
  have hsquare:=pow_le_pow_left₀ hD hbound 2
  rw [mul_pow,Real.sq_sqrt hS,Real.sq_sqrt hQ] at hsquare
  have hm:=mul_le_mul_of_nonneg_left hDQ hS
  change D ≤ 2*S
  by_cases hd:D=0
  · rw [hd];positivity
  · have hpos:0<D := lt_of_le_of_ne hD (Ne.symm hd)
    nlinarith

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingBasics -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma allowed_update (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) (b : Bool) :
    synthesis_resampleAllowed C r (Function.update f x b) x ↔ synthesis_resampleAllowed C r f x := by
  simp only [synthesis_resampleAllowed,Function.update_idem]

lemma flip_involutive (x : synthesis_Bits m₀) : Function.Involutive (fun f:synthesis_Oracle m₀=>synthesis_flip f x) := by
  intro f
  funext y
  by_cases h:y=x <;> simp [synthesis_flip,h]

lemma allowed_flip (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_resampleAllowed C r (synthesis_flip f x) x ↔ synthesis_resampleAllowed C r f x :=
  allowed_update C r f x (!f x)

def step (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (f : synthesis_Oracle m₀) (b : Bool) : synthesis_Oracle m₀ :=
  if synthesis_resampleAllowed C r f x then Function.update f x b else f

/-- Store the spent initial bit in its seed position. The map is an exact
involution on a pair of complete truth tables. It is the concrete
reversibility underlying the resampling proof. -/
def swapStep (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (z : synthesis_Oracle m₀×synthesis_Oracle m₀) : synthesis_Oracle m₀×synthesis_Oracle m₀ :=
  if synthesis_resampleAllowed C r z.1 x then
    (Function.update z.1 x (z.2 x),Function.update z.2 x (z.1 x)) else z

lemma swapStep_involutive (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    Function.Involutive (swapStep C r x) := by
  intro z
  rcases z with ⟨f,c⟩
  by_cases ha:synthesis_resampleAllowed C r f x
  · have ha':synthesis_resampleAllowed C r (Function.update f x (c x)) x := (allowed_update C r f x _).mpr ha
    simp [swapStep,ha,ha',Function.update_idem]
  · simp [swapStep,ha]

def swapEquiv (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    (synthesis_Oracle m₀×synthesis_Oracle m₀) ≃ (synthesis_Oracle m₀×synthesis_Oracle m₀) :=
  (swapStep_involutive C r x).toPerm

lemma swapStep_fst (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (z : synthesis_Oracle m₀×synthesis_Oracle m₀) :
    (swapStep C r x z).1=step C r x z.1 (z.2 x) := by
  unfold swapStep step
  split_ifs <;> rfl

lemma swapStep_future (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x y : synthesis_Bits m₀)
    (hxy:y≠x) (z : synthesis_Oracle m₀×synthesis_Oracle m₀) :
    (swapStep C r x z).2 y=z.2 y := by
  unfold swapStep
  split_ifs <;> simp [hxy]

def swapPath (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    ℕ→(synthesis_Oracle m₀×synthesis_Oracle m₀)→(synthesis_Oracle m₀×synthesis_Oracle m₀)
  | 0,z=>z
  | i+1,z=>if hi:i<Fintype.card (synthesis_Bits m₀) then
      swapStep C r (synthesis_order m₀ ⟨i,hi⟩) (swapPath C r i z) else swapPath C r i z

lemma swapPath_bijective (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ) :
    Function.Bijective (swapPath C r i) := by
  induction i with
  | zero => exact Function.bijective_id
  | succ i ih =>
    by_cases hi:i<Fintype.card (synthesis_Bits m₀)
    · simp only [swapPath,dif_pos hi]
      exact (swapStep_involutive C r (synthesis_order m₀ ⟨i,hi⟩)).bijective.comp ih
    · simpa only [swapPath,dif_neg hi] using ih

lemma swapPath_fresh (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) : (swapPath C r i (f,coins)).2 (synthesis_order m₀ j)=coins (synthesis_order m₀ j) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi:i<Fintype.card (synthesis_Bits m₀) := by omega
    rw [swapPath,dif_pos hi,swapStep_future]
    · exact ih (by omega)
    · intro hh
      have he:= (synthesis_order m₀).injective hh
      have hv:j.val=i := congrArg Fin.val he
      omega

/-- The reversible path has exactly the same current function as the
published procedure using fresh independent bits. The selected set is
retained by the public procedure, and is not replaced or weakened. -/
lemma swapPath_current (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) :
    (swapPath C r i (f,coins)).1=(synthesis_resamplePath C r f coins i).1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases hi:i<Fintype.card (synthesis_Bits m₀)
    · rw [swapPath,dif_pos hi,swapStep_fst]
      rw [swapPath_fresh C r f coins i ⟨i,hi⟩ (le_refl _),ih]
      simp only [synthesis_resamplePath,dif_pos hi,step]
      split_ifs <;> rfl
    · simpa only [swapPath,dif_neg hi,synthesis_resamplePath] using ih

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingStationarity -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma average_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    synthesis_average (fun _:α=>c)=c := by
  have hc:(Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [synthesis_average,sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc

lemma average_add {α : Type} [Fintype α] (f g : α→ℝ) :
    synthesis_average (fun a=>f a+g a)=synthesis_average f+synthesis_average g := by
  simp only [synthesis_average,sum_add_distrib,add_div]

lemma average_comp {α : Type} [Fintype α] (e : α≃α) (f : α→ℝ) :
    synthesis_average (fun a=>f (e a))=synthesis_average f := by
  unfold synthesis_average
  rw [e.sum_comp]

lemma average_bit (x : synthesis_Bits m₀) (F : Bool→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>F (coins x))=(F false+F true)/2 := by
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive x).toPerm
  have hs:∀coins:synthesis_Oracle m₀,F (coins x)+F ((e coins) x)=F false+F true := by
    intro coins
    change F (coins x)+F ((synthesis_flip coins x) x)=_
    simp only [synthesis_flip,Function.update_self]
    cases coins x <;> simp [add_comm]
  have hh:=average_add (fun coins:synthesis_Oracle m₀=>F (coins x)) (fun coins=>F ((e coins) x))
  rw [average_comp e (fun coins:synthesis_Oracle m₀=>F (coins x))] at hh
  have he:synthesis_average (fun coins:synthesis_Oracle m₀=>F (coins x)+F ((e coins) x))=F false+F true := by
    simp only [hs,average_const]
  rw [he] at hh
  linarith

lemma sum_swapPath {α : Type} [AddCommMonoid α] (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (i : ℕ) (h : synthesis_Oracle m₀×synthesis_Oracle m₀→α) :
    (∑f,∑coins,h (swapPath C r i (f,coins)))=(∑f,∑coins,h (f,coins)) := by
  simpa only [Fintype.sum_prod_type,Equiv.ofBijective_apply] using
    (Equiv.ofBijective (swapPath C r i) (swapPath_bijective C r i)).sum_comp h

lemma double_average_swapPath (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (i : ℕ) (h : synthesis_Oracle m₀×synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun f=>synthesis_average (fun coins=>h (swapPath C r i (f,coins))))=
      synthesis_average (fun f=>synthesis_average (fun coins=>h (f,coins))) := by
  unfold synthesis_average
  rw [← sum_div,← sum_div,sum_swapPath]

/-- Uniform truth-table marginal preservation for every actual intermediate
function, derived from the concrete reversible state-and-spent-seed map. -/
theorem average_path_current (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (h : synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun f=>synthesis_average (fun coins=>h (synthesis_resamplePath C r f coins i).1))=
      synthesis_average h := by
  have hs:∀f coins,h (synthesis_resamplePath C r f coins i).1=h (swapPath C r i (f,coins)).1 :=
    fun f coins=>congrArg h (swapPath_current C r f coins i).symm
  simp_rw [hs]
  rw [double_average_swapPath C r i (fun z=>h z.1)]
  simp only [average_const]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingFresh -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma average_div {α : Type} [Fintype α] (f : α→ℝ) (d : ℝ) :
    synthesis_average (fun a=>f a/d)=synthesis_average f/d := by
  unfold synthesis_average
  rw [← sum_div]
  ring

/-- Every unvisited fair bit is independent of the complete actual path
prefix, including its selected-coordinate set. -/
lemma path_coins_update (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) (b : Bool) :
    synthesis_resamplePath C r f (Function.update coins (synthesis_order m₀ j) b) i=
      synthesis_resamplePath C r f coins i := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    have hi:i<Fintype.card (synthesis_Bits m₀) := by omega
    have hne:synthesis_order m₀ ⟨i,hi⟩≠synthesis_order m₀ j := by
      intro hh
      have hv:i=j.val := congrArg Fin.val ((synthesis_order m₀).injective hh)
      omega
    simp only [synthesis_resamplePath,dif_pos hi,ih (by omega),Function.update_of_ne hne]

lemma path_coins_flip (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) :
    synthesis_resamplePath C r f (synthesis_flip coins (synthesis_order m₀ j)) i=
      synthesis_resamplePath C r f coins i := path_coins_update C r f coins i j hij _

lemma average_fresh_bit (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀))
    (H : (synthesis_Oracle m₀×Finset (synthesis_Bits m₀))→Bool→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>
      H (synthesis_resamplePath C r f coins i) (coins (synthesis_order m₀ ⟨i,hi⟩)))=
    synthesis_average (fun coins:synthesis_Oracle m₀=>
      (H (synthesis_resamplePath C r f coins i) false+H (synthesis_resamplePath C r f coins i) true)/2) := by
  let x:=synthesis_order m₀ ⟨i,hi⟩
  let F:=fun coins:synthesis_Oracle m₀=>H (synthesis_resamplePath C r f coins i) (coins x)
  let G:=fun coins:synthesis_Oracle m₀=>
    H (synthesis_resamplePath C r f coins i) false+H (synthesis_resamplePath C r f coins i) true
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive x).toPerm
  have he:synthesis_average (fun coins=>F (e coins))=synthesis_average F := average_comp e F
  have hs:∀coins:synthesis_Oracle m₀,F coins+F (e coins)=G coins := by
    intro coins
    dsimp only [F,G]
    change H (synthesis_resamplePath C r f coins i) (coins x)+
      H (synthesis_resamplePath C r f (synthesis_flip coins x) i) ((synthesis_flip coins x) x)=_
    rw [path_coins_flip C r f coins i ⟨i,hi⟩ (le_refl _)]
    simp only [synthesis_flip,Function.update_self]
    cases coins x <;> simp [add_comm]
  have hh:=average_add F (fun coins=>F (e coins))
  rw [he] at hh
  have hG:synthesis_average (fun coins=>F coins+F (e coins))=synthesis_average G := by simp only [hs]
  rw [hG] at hh
  change synthesis_average F=synthesis_average (fun coins=>G coins/2)
  rw [average_div]
  linarith

/-- Scalar conditional averaging for the genuine finite path. -/
def oneStepOp (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (h : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) : ℝ :=
  (h (step C r x f false)+h (step C r x f true))/2

lemma average_next (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀))
    (h : synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>h (synthesis_resamplePath C r f coins (i+1)).1)=
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        oneStepOp C r (synthesis_order m₀ ⟨i,hi⟩) h (synthesis_resamplePath C r f coins i).1) := by
  have hp:∀coins:synthesis_Oracle m₀,(synthesis_resamplePath C r f coins (i+1)).1=
      step C r (synthesis_order m₀ ⟨i,hi⟩) (synthesis_resamplePath C r f coins i).1
        (coins (synthesis_order m₀ ⟨i,hi⟩)) := by
    intro coins
    simp only [synthesis_resamplePath,dif_pos hi,step]
    split_ifs <;> rfl
  simp_rw [hp]
  exact average_fresh_bit C r f i hi (fun prev b=>h (step C r (synthesis_order m₀ ⟨i,hi⟩) prev.1 b))

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleFiniteProjections -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
variable {ι : Type} [Fintype ι]

def permutationAction (e : Equiv.Perm ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

lemma permutationAction_apply (e : Equiv.Perm ι) (v : EuclideanSpace ℝ ι) (i : ι) :
    permutationAction e v i=v (e i) := rfl

lemma permutationAction_involutive (e : Equiv.Perm ι) (he:Function.Involutive e) :
    Function.Involutive (permutationAction e) := by
  intro v
  apply PiLp.ext
  intro i
  change v (e (e i))=v i
  rw [he i]

def pairProjection (e : Equiv.Perm ι) (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (1/2:ℝ) • (v+permutationAction e v)

lemma pairProjection_apply (e : Equiv.Perm ι) (v : EuclideanSpace ℝ ι) (i : ι) :
    pairProjection e v i=(v i+v (e i))/2 := by
  change (1/2:ℝ)*(v i+permutationAction e v i)=_
  rw [permutationAction_apply]
  ring

lemma pairProjection_idempotent (e : Equiv.Perm ι) (he:Function.Involutive e) (v : EuclideanSpace ℝ ι) :
    pairProjection e (pairProjection e v)=pairProjection e v := by
  apply PiLp.ext
  intro i
  simp only [pairProjection_apply,he i]
  ring

lemma pairProjection_symmetric (e : Equiv.Perm ι) (he:Function.Involutive e) (u v : EuclideanSpace ℝ ι) :
    inner ℝ (pairProjection e u) v=inner ℝ u (pairProjection e v) := by
  have hh:inner ℝ (permutationAction e u) v=inner ℝ u (permutationAction e v) := by
    have ht:=(permutationAction e).inner_map_map u (permutationAction e v)
    rwa [permutationAction_involutive e he v] at ht
  simp only [pairProjection,inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,
    conj_trivial]
  rw [hh]

variable {n m m₀ k : ℕ}

def lazyFlip (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (f : synthesis_Oracle m₀) : synthesis_Oracle m₀ :=
  if synthesis_resampleAllowed C r f x then synthesis_flip f x else f

lemma lazyFlip_involutive (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    Function.Involutive (lazyFlip C r x) := by
  intro f
  by_cases ha:synthesis_resampleAllowed C r f x
  · have hb:= (allowed_flip C r f x).mpr ha
    simp [lazyFlip,ha,hb,flip_involutive x f]
  · simp [lazyFlip,ha]

def lazyFlipEquiv (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    Equiv.Perm (synthesis_Oracle m₀) := (lazyFlip_involutive C r x).toPerm

lemma forced_pair_sum (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (h : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) :
    oneStepOp C r x h f=(h f+h (lazyFlip C r x f))/2 := by
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [oneStepOp,step,if_pos ha,lazyFlip]
    have hf:Function.update f x (f x)=f := Function.update_eq_self x f
    cases hfx:f x
    · have h0:Function.update f x false=f := by simpa only [hfx] using hf
      simp only [synthesis_flip,hfx,Bool.not_false,h0]
    · have h1:Function.update f x true=f := by simpa only [hfx] using hf
      simp only [synthesis_flip,hfx,Bool.not_true,h1]
      ring
  · simp only [oneStepOp,step,lazyFlip,if_neg ha]

/-- Scalar form of the exact L2 projection at a resampling coordinate. -/
lemma oneStepOp_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) (f : synthesis_Oracle m₀) :
    pairProjection (lazyFlipEquiv C r x) v f=oneStepOp C r x v f := by
  rw [pairProjection_apply,forced_pair_sum]
  rfl

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingDP -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical

lemma average_sub {α : Type} [Fintype α] (f g : α→ℝ) :
    synthesis_average (fun a=>f a-g a)=synthesis_average f-synthesis_average g := by
  simp only [synthesis_average,sum_sub_distrib,sub_div]

lemma average_smul {α : Type} [Fintype α] (c : ℝ) (f : α→ℝ) :
    synthesis_average (fun a=>c*f a)=c*synthesis_average f := by
  unfold synthesis_average
  rw [← mul_sum]
  ring

lemma average_mul_const {α : Type} [Fintype α] (f : α→ℝ) (c : ℝ) :
    synthesis_average (fun a=>f a*c)=synthesis_average f*c := by
  simpa only [mul_comm] using average_smul c f

lemma average_sum {α β : Type} [Fintype α] [Fintype β] (F : β→α→ℝ) :
    synthesis_average (fun a=>∑b,F b a)=∑b,synthesis_average (F b) := by
  unfold synthesis_average
  rw [sum_comm,sum_div]

lemma average_mono {α : Type} [Fintype α] (f g : α→ℝ) (h:∀a,f a ≤ g a) :
    synthesis_average f ≤ synthesis_average g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun a _=>h a)) (Nat.cast_nonneg _)

variable {n m m₀ k : ℕ}

def visit (i : ℕ) : synthesis_Bits m₀ :=
  if hi:i<Fintype.card (synthesis_Bits m₀) then synthesis_order m₀ ⟨i,hi⟩ else fun _=>0

def backwardApply (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    ℕ→(synthesis_Oracle m₀→ℝ)→synthesis_Oracle m₀→ℝ
  | 0,h=>h
  | i+1,h=>backwardApply C r i (oneStepOp C r (visit i) h)

/-- Exact finite dynamic-programming semantics of the public adaptive path,
using its genuinely fresh fair seed bit at every visit. -/
theorem path_average_value (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (hi:i ≤ Fintype.card (synthesis_Bits m₀)) (h : synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>h (synthesis_resamplePath C r f coins i).1)=
      backwardApply C r i h f := by
  induction i generalizing h with
  | zero=>simp only [synthesis_resamplePath,backwardApply,average_const]
  | succ i ih=>
    have hi':i<Fintype.card (synthesis_Bits m₀) := by omega
    rw [average_next C r f i hi',ih (by omega)]
    simp only [backwardApply,visit,dif_pos hi']

/-- Averaging a real-valued observable after one update is the exact
orthogonal projection associated with the conditional bit flip. -/
def coordinateProjection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ) :
    EuclideanSpace ℝ (synthesis_Oracle m₀)→EuclideanSpace ℝ (synthesis_Oracle m₀) :=
  pairProjection (lazyFlipEquiv C r (visit i))

lemma coordinateProjection_symm (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (u v : EuclideanSpace ℝ (synthesis_Oracle m₀)) :
    inner ℝ (coordinateProjection C r i u) v=inner ℝ u (coordinateProjection C r i v) :=
  pairProjection_symmetric _ (lazyFlip_involutive C r (visit i)) u v

lemma coordinateProjection_idempotent (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) :
    coordinateProjection C r i (coordinateProjection C r i v)=coordinateProjection C r i v :=
  pairProjection_idempotent _ (lazyFlip_involutive C r (visit i)) v

lemma coordinateProjection_apply (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) (f : synthesis_Oracle m₀) :
    coordinateProjection C r i v f=oneStepOp C r (visit i) v f := oneStepOp_projection C r _ v f

def backwardVector (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    ℕ→EuclideanSpace ℝ (synthesis_Oracle m₀)→EuclideanSpace ℝ (synthesis_Oracle m₀)
  | 0,v=>v
  | i+1,v=>backwardVector C r i (coordinateProjection C r i v)

lemma backwardVector_apply (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) (f : synthesis_Oracle m₀) :
    backwardVector C r i v f=backwardApply C r i v f := by
  induction i generalizing v with
  | zero=>rfl
  | succ i ih=>
    rw [backwardVector,ih,backwardApply]
    congr 2
    funext g
    exact coordinateProjection_apply C r i v g

lemma backwardVector_inner_dual (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (u v : EuclideanSpace ℝ (synthesis_Oracle m₀)) :
    inner ℝ u (backwardVector C r i v)=inner ℝ (projectionPath (coordinateProjection C r) u i) v := by
  induction i generalizing v with
  | zero=>rfl
  | succ i ih=>
    rw [backwardVector,ih,← coordinateProjection_symm]
    rfl

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleFiniteMeans -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset Classical
open scoped ENNReal

lemma mean_map {α β : Type} [Fintype α] [Fintype β] (p : PMF α) (f : α→β) (h : β→ℝ) :
    synthesis_mean (p.map f) h=synthesis_mean p (fun a=>h (f a)) := by
  have he:∀b:β,((p.map f) b).toReal=∑a:α,if b=f a then (p a).toReal else 0 := by
    intro b
    rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum]
    · apply sum_congr rfl
      intro a ha
      split_ifs <;> simp
    · intro a ha
      split_ifs <;> simp [p.apply_ne_top]
  unfold synthesis_mean
  simp_rw [he,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  simp

lemma mean_uniform {α : Type} [Fintype α] [Nonempty α] (h : α→ℝ) :
    synthesis_mean (PMF.uniformOfFintype α) h=synthesis_average h := by
  unfold synthesis_mean synthesis_average
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← mul_sum]
  ring

lemma energy_eq_path {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_energy C (synthesis_resample C r)=
      synthesis_average (fun f=>synthesis_average (fun coins:synthesis_Oracle m₀=>
        QAlgorithms.frobNorm (synthesis_A C f-
          synthesis_A C (synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))).1)^2)) := by
  unfold synthesis_energy synthesis_resample
  simp only [mean_map,mean_uniform]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleChoiPauliOverlap -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical DirectFidelity.State PauliProof ResamplingProof
open scoped ComplexConjugate

lemma pauli_pure_overlap {n : ℕ} (M U : synthesis_Mat n) :
    synthesis_average (fun P:synthesis_Pauli n=>
      (Mᴴ*W P*M*(Uᴴ*W P*U)).trace.re/(2:ℝ)^n)=
      (pure (vectorized U)*pure (vectorized M)).trace.re := by
  have hc:(Fintype.card (Q n):ℂ)=(2:ℂ)^n := by simp [Q]
  have hp:(Fintype.card (P n):ℂ)=((2:ℂ)^n)^2 := by
    simp only [P,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    symm
    rw [pow_two,←mul_pow]
    norm_num
  have hN:(2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  have ht:(Mᴴ*U).trace=star ((Uᴴ*M).trace) := by
    rw [←Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have he:∀P:P n,(Mᴴ*W P*M*(Uᴴ*W P*U)).trace=(Mᴴ*W P*M*Uᴴ*W P*U).trace := by
    intro P
    simp only [Matrix.mul_assoc]
  have hcomplex:(∑P:P n,(Mᴴ*W P*M*(Uᴴ*W P*U)).trace)=
      (((2:ℝ)^n*(Fintype.card (P n):ℝ):ℝ):ℂ)*
        (pure (vectorized U)*pure (vectorized M)).trace := by
    simp only [he,pauli_kraus_overlap,pure_overlap,vectorized_inner,hc,ht,
      Matrix.trace_mul_comm M Uᴴ]
    push_cast
    rw [hp]
    field_simp
    <;> ring
  have hreal:=congrArg Complex.re hcomplex
  simp only [Complex.re_sum,Complex.re_ofReal_mul] at hreal
  unfold synthesis_average
  rw [←sum_div,hreal]
  have hnR:(2:ℝ)^n≠0 := ne_of_gt (pow_pos (by norm_num) n)
  have hpR:(Fintype.card (P n):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma kraus_pauli_pure_overlap {n : ℕ} {ι : Type} [Fintype ι]
    (M : ι→synthesis_Mat n) (U : synthesis_Mat n) :
    synthesis_average (fun P:synthesis_Pauli n=>
      ((∑i,(M i)ᴴ*W P*M i)*(Uᴴ*W P*U)).trace.re/(2:ℝ)^n)=
      (pure (vectorized U)*(∑i,pure (vectorized (M i)))).trace.re := by
  simp only [Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum,sum_div]
  rw [average_sum]
  simp only [pauli_pure_overlap,Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]

lemma actual_choi_pauli_overlap {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (U : synthesis_Unitary n) :
    synthesis_average (fun P:synthesis_Pauli n=>
      synthesis_correlation (synthesis_observable C f P) P U)=
      (pure (vectorized (U:synthesis_Mat n))*
        synthesis_amplify (synthesis_actualChannel C f) (Fintype.card (synthesis_Bits n))
          (pure (vectorized (1:synthesis_Mat n)))).trace.re := by
  simp only [synthesis_correlation,observable_kraus,actualChannel_bell]
  exact kraus_pauli_pure_overlap _ _

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleDirtyOverlapMain -/

set_option autoImplicit false
noncomputable section
namespace RandomOracleUnitarySynthesis

/-- Exact public Lemma4.11, retaining arbitrary workspace, dirty output,
all finite reference systems and all mixed states in the diamond distance. -/
theorem synthesis_dirty_pauli_overlap {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (U : synthesis_Unitary n) :
    1 - synthesis_diamond (synthesis_actualChannel C f) (synthesis_unitaryChannel U) ≤
      synthesis_average (fun P : synthesis_Pauli n =>
        synthesis_correlation (synthesis_observable C f P) P U) := by
  rw [ChannelProof.actual_choi_pauli_overlap]
  exact ChannelProof.choi_accept_ge_one_sub_diamond C f U

end RandomOracleUnitarySynthesis

/- Module RandomOraclePerturbation -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate

section Frobenius
variable {ι α β γ : Type} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
open scoped Matrix.Norms.Frobenius in
lemma frob_nonneg (A : Matrix α β ℂ) : 0 ≤ QAlgorithms.frobNorm A := norm_nonneg _

open scoped Matrix.Norms.Frobenius in
lemma frob_smul (c : ℂ) (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm (c • A)=‖c‖*QAlgorithms.frobNorm A := norm_smul _ _

open scoped Matrix.Norms.Frobenius in
/-- Finite Schatten--Cauchy--Schwarz, equivalently the horizontal/vertical
block-factor argument in the original proof. There is no extra k factor. -/
theorem frob_sum_mul_sq_le (A : ι→Matrix α β ℂ) (B : ι→Matrix β γ ℂ) :
    QAlgorithms.frobNorm (∑j,A j*B j)^2  ≤ 
      (∑j,QAlgorithms.frobNorm (A j)^2)*(∑j,QAlgorithms.frobNorm (B j)^2) := by
  have htriangle:QAlgorithms.frobNorm (∑j,A j*B j)  ≤  ∑j,QAlgorithms.frobNorm (A j*B j) :=
    norm_sum_le _ _
  have hmul:∀j,QAlgorithms.frobNorm (A j*B j)  ≤  QAlgorithms.frobNorm (A j)*QAlgorithms.frobNorm (B j) :=
    fun j=>Matrix.frobenius_norm_mul _ _
  have hcs:=Real.sum_mul_le_sqrt_mul_sqrt (univ:Finset ι)
    (fun j=>QAlgorithms.frobNorm (A j)) (fun j=>QAlgorithms.frobNorm (B j))
  have hh:=htriangle.trans ((sum_le_sum (fun j _=>hmul j)).trans hcs)
  have hA:0 ≤ ∑j,QAlgorithms.frobNorm (A j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hB:0 ≤ ∑j,QAlgorithms.frobNorm (B j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hs:=pow_le_pow_left₀ (frob_nonneg _) hh 2
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB] at hs
  exact hs
end Frobenius

variable {n m m₀ k : ℕ}

lemma influence_nonneg (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    0 ≤ synthesis_influence C f x := by
  exact sum_nonneg (fun j _=>add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Exact public Lemma4.8 for the full oracle and the compressed block. -/
theorem synthesis_one_bit_perturbation (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f x)-synthesis_A C f)^2  ≤ 
      4*synthesis_influence C f x*synthesis_influence C (synthesis_flip f x) x := by
  have hA:(∑j:Fin k,QAlgorithms.frobNorm (synthesis_left C f j*synthesis_projector C x)^2)  ≤ 
      synthesis_influence C f x := sum_le_sum (fun j _=>le_add_of_nonneg_right (sq_nonneg _))
  have hB:(∑j:Fin k,QAlgorithms.frobNorm (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)^2)  ≤ 
      synthesis_influence C (synthesis_flip f x) x := sum_le_sum (fun j _=>
        le_add_of_nonneg_left (sq_nonneg _))
  have hh:=frob_sum_mul_sq_le
    (fun j:Fin k=>synthesis_left C f j*synthesis_projector C x)
    (fun j:Fin k=>synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)
  have hb0:0 ≤ ∑j:Fin k,QAlgorithms.frobNorm
      (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hp:=mul_le_mul hA hB hb0 (influence_nonneg C f x)
  rw [A_flip_difference,frob_smul,mul_pow]
  have hc:‖(if f x then (2:ℂ) else -2)‖^2=4 := by cases f x <;> norm_num
  rw [hc]
  nlinarith [hh.trans hp]

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOracleContraction -/

set_option autoImplicit false
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Matrix Finset Classical
open scoped Matrix.Norms.L2Operator ComplexConjugate
variable {n m m₀ k : ℕ}

lemma J_specNorm (C : synthesis_Circuit n m m₀ k) : QAlgorithms.specNorm (synthesis_J C)=1 := by
  change ‖synthesis_J C‖=1
  have he:=Matrix.l2_opNorm_conjTranspose_mul_self (synthesis_J C)
  rw [InfluenceProof.J_isometry C,norm_one] at he
  nlinarith [norm_nonneg (synthesis_J C)]

/-- Every original center is a contraction; no clean-ancilla assumption is used. -/
theorem A_contraction (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_IsContraction (synthesis_A C f) := by
  have hJ:‖synthesis_J C‖=1 := J_specNorm C
  have hW:‖synthesis_W C f‖=1 :=
    CStarRing.norm_of_mem_unitary (InfluenceProof.segment_unitary C f 0 k)
  change ‖(synthesis_J C)ᴴ*synthesis_W C f*synthesis_J C‖ ≤ 1
  calc
    _ ≤ ‖(synthesis_J C)ᴴ*synthesis_W C f‖*‖synthesis_J C‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(synthesis_J C)ᴴ‖*‖synthesis_W C f‖)*‖synthesis_J C‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = 1 := by rw [Matrix.l2_opNorm_conjTranspose,hJ,hW]; norm_num

end RandomOracleUnitarySynthesis.NetProof

/- Module SpaceResetHilbertSchmidt -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

def entryVector (A : Matrix α β ℂ) : EuclideanSpace ℂ (α×β) :=
  WithLp.toLp 2 (fun p=>A p.1 p.2)

def hsNorm (A : Matrix α β ℂ) : ℝ := Real.sqrt (Aᴴ*A).trace.re

lemma trace_gram_eq_inner (A B : Matrix α β ℂ) :
    (Aᴴ*B).trace=inner ℂ (entryVector A) (entryVector B) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    entryVector,PiLp.inner_apply,WithLp.ofLp_toLp,RCLike.inner_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact mul_comm _ _

lemma hsNorm_eq_norm (A : Matrix α β ℂ) : hsNorm A=‖entryVector A‖ := by
  rw [hsNorm,trace_gram_eq_inner,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re]
  exact Real.sqrt_sq (norm_nonneg _)

lemma hsNorm_nonneg (A : Matrix α β ℂ) : 0 ≤ hsNorm A := Real.sqrt_nonneg _

lemma hs_trace_cauchy (A B : Matrix α β ℂ) :
    ‖(Aᴴ*B).trace‖ ≤ hsNorm A*hsNorm B := by
  rw [trace_gram_eq_inner,hsNorm_eq_norm,hsNorm_eq_norm]
  exact norm_inner_le_norm _ _

lemma hsNorm_conjTranspose (A : Matrix α β ℂ) : hsNorm Aᴴ=hsNorm A := by
  rw [hsNorm,hsNorm,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_comm]

lemma hsNorm_mul_unitary (A : Matrix α β ℂ) (U : Matrix.unitaryGroup β ℂ) :
    hsNorm (A*(U:Matrix β β ℂ))=hsNorm A := by
  unfold hsNorm
  congr 1
  have he:((A*(U:Matrix β β ℂ))ᴴ*(A*(U:Matrix β β ℂ))).trace=(Aᴴ*A).trace := by
    rw [Matrix.conjTranspose_mul]
    rw [show (U:Matrix β β ℂ)ᴴ*Aᴴ*(A*(U:Matrix β β ℂ))=
      (U:Matrix β β ℂ)ᴴ*(Aᴴ*A)*(U:Matrix β β ℂ) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_cycle]
    have hu:(U:Matrix β β ℂ)*(U:Matrix β β ℂ)ᴴ=1 := Unitary.coe_mul_star_self U
    rw [hu,Matrix.one_mul]
  rw [he]

lemma traceNorm_mul_le_hs_square (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A*B) ≤ hsNorm A*hsNorm B := by
  obtain ⟨U,hU⟩:=traceNorm_attain (A*B)
  have hh:=hs_trace_cauchy Aᴴ (B*(U:Matrix α α ℂ))
  rw [Matrix.conjTranspose_conjTranspose,← Matrix.mul_assoc,hU,
    hsNorm_conjTranspose,hsNorm_mul_unitary] at hh
  exact hh

/-- Schatten 2–2→1 Hölder, with arbitrary finite rectangular dimensions. -/
theorem traceNorm_mul_le_hs (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    WildeQIT.traceNorm (A*B) ≤ hsNorm A*hsNorm B := by
  let S : Matrix β β ℂ := CFC.sqrt (Aᴴ*A)
  let T : Matrix β β ℂ := CFC.sqrt (B*Bᴴ)
  have hS:Sᴴ=S := (CFC.sqrt_nonneg (Aᴴ*A)).isSelfAdjoint.star_eq
  have hT:Tᴴ=T := (CFC.sqrt_nonneg (B*Bᴴ)).isSelfAdjoint.star_eq
  have hSS:S*S=Aᴴ*A := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hTT:T*T=B*Bᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose B).nonneg
  have he1:WildeQIT.traceNorm (A*B)=WildeQIT.traceNorm (S*B) := by
    have hg:(A*B)ᴴ*(A*B)=(S*B)ᴴ*(S*B) := by
      simp only [Matrix.conjTranspose_mul,hS]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc S S,hSS]
    simp only [WildeQIT.traceNorm,hg]
  have he2:WildeQIT.traceNorm (S*B)=WildeQIT.traceNorm (S*T) := by
    have hg:(S*B)*(S*B)ᴴ=(S*T)*(S*T)ᴴ := by
      simp only [Matrix.conjTranspose_mul,hS,hT]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc T T,hTT]
    rw [traceNorm_eq_left,traceNorm_eq_left,hg]
  have hnS:hsNorm S=hsNorm A := by rw [hsNorm,hS,hSS];rfl
  have hnT:hsNorm T=hsNorm B := by
    rw [hsNorm,hT,hTT,Matrix.trace_mul_comm]
    rfl
  rw [he1,he2]
  exact (traceNorm_mul_le_hs_square S T).trans_eq (by rw [hnS,hnT])

end SpaceReset.Hardness.FidelityProof

/- Module RandomOracleCorrelationGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.GeometryProof
open Matrix Finset Classical
open SpaceReset.Hardness.FidelityProof
open scoped ComplexConjugate Matrix.Norms.L2Operator
variable {α : Type} [Fintype α] [DecidableEq α]

lemma hsNorm_eq_frob (A : Matrix α α ℂ) : hsNorm A=QAlgorithms.frobNorm A := by
  unfold hsNorm
  rw [←InfluenceProof.frob_sq_gram]
  exact Real.sqrt_sq (InfluenceProof.frob_nonneg _)

lemma norm_trace_mul_le_frob (A B : Matrix α α ℂ) :
    ‖(A*B).trace‖ ≤ QAlgorithms.frobNorm A*QAlgorithms.frobNorm B := by
  have hh:=hs_trace_cauchy Aᴴ B
  rw [Matrix.conjTranspose_conjTranspose,hsNorm_conjTranspose,hsNorm_eq_frob,hsNorm_eq_frob] at hh
  exact hh

lemma frob_conjTranspose (A : Matrix α α ℂ) : QAlgorithms.frobNorm Aᴴ=QAlgorithms.frobNorm A := by
  rw [←hsNorm_eq_frob,hsNorm_conjTranspose,hsNorm_eq_frob]

lemma frob_mul_unitary (A : Matrix α α ℂ) (U : Matrix.unitaryGroup α ℂ) :
    QAlgorithms.frobNorm (A*(U:Matrix α α ℂ))=QAlgorithms.frobNorm A := by
  rw [←hsNorm_eq_frob,hsNorm_mul_unitary,hsNorm_eq_frob]

lemma frob_unitary_mul (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    QAlgorithms.frobNorm ((U:Matrix α α ℂ)*A)=QAlgorithms.frobNorm A := by
  rw [←frob_conjTranspose,Matrix.conjTranspose_mul]
  have hh:=frob_mul_unitary Aᴴ (star U)
  simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,frob_conjTranspose] using hh

lemma unitary_frob [Nonempty α] (U : Matrix.unitaryGroup α ℂ) :
    QAlgorithms.frobNorm (U:Matrix α α ℂ)=Real.sqrt (Fintype.card α:ℝ) := by
  have hs:=InfluenceProof.frob_sq_gram (U:Matrix α α ℂ)
  rw [show (U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 from Unitary.star_mul_self_of_mem U.property,
    Matrix.trace_one] at hs
  have he:(Fintype.card α:ℂ).re=(Fintype.card α:ℝ) := by simp
  rw [he] at hs
  calc
    _ = Real.sqrt (QAlgorithms.frobNorm (U:Matrix α α ℂ)^2) :=
      (Real.sqrt_sq (InfluenceProof.frob_nonneg _)).symm
    _ = _ := congrArg Real.sqrt hs

lemma column_norm_le_specNorm (A : Matrix α α ℂ) (j : α) :
    ‖(WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)‖ ≤ QAlgorithms.specNorm A := by
  have hh:=Matrix.l2_opNorm_mulVec A (PiLp.single 2 j (1:ℂ))
  change ‖(WithLp.toLp 2 (A*ᵥPi.single j (1:ℂ)):EuclideanSpace ℂ α)‖ ≤
    QAlgorithms.specNorm A*‖(PiLp.single 2 j (1:ℂ):EuclideanSpace ℂ α)‖ at hh
  rwa [Matrix.mulVec_single_one,PiLp.norm_single,norm_one,mul_one] at hh

lemma contraction_frob_le (A : Matrix α α ℂ) (hA:QAlgorithms.specNorm A ≤ 1) :
    QAlgorithms.frobNorm A ≤ Real.sqrt (Fintype.card α:ℝ) := by
  have hc:∀j:α,(∑i:α,‖A i j‖^2) ≤ 1 := by
    intro j
    have hh:‖(WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)‖ ≤ 1 :=
      (column_norm_le_specNorm A j).trans hA
    have hs:‖(WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)‖^2 ≤ 1 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (A.col j):EuclideanSpace ℂ α)]
    simpa only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp,Matrix.col_apply] using hs
  have hs:=sum_le_sum (fun j (_:j∈(univ:Finset α))=>hc j)
  rw [sum_comm,←InfluenceProof.frob_sq_entries] at hs
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hs
  exact (sq_le_sq₀ (InfluenceProof.frob_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt (Nat.cast_nonneg _)])

lemma frob_eq_sqrt_entries (A : Matrix α α ℂ) :
    QAlgorithms.frobNorm A=Real.sqrt (∑i:α,∑j:α,‖A i j‖^2) := by
  rw [←InfluenceProof.frob_sq_entries,Real.sqrt_sq (InfluenceProof.frob_nonneg _)]

end RandomOracleUnitarySynthesis.GeometryProof

/- Module RandomOracleMatrixCorrelation -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.GeometryProof
open Matrix Finset Classical
open scoped ComplexConjugate Matrix.Norms.L2Operator
variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

def matrixCorrelation (A : Matrix α α ℂ) (Q U : Matrix.unitaryGroup α ℂ) : ℝ :=
  (A*(↑(star U*Q*U):Matrix α α ℂ)).trace.re/(Fintype.card α:ℝ)

lemma matrixCorrelation_continuous (A : Matrix α α ℂ) (Q : Matrix.unitaryGroup α ℂ) :
    Continuous (matrixCorrelation A Q) := by
  unfold matrixCorrelation
  fun_prop

lemma matrixCorrelation_bound (A : Matrix α α ℂ) (hA:QAlgorithms.specNorm A ≤ 1)
    (Q U : Matrix.unitaryGroup α ℂ) : |matrixCorrelation A Q U| ≤ 1 := by
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hh:|(A*(↑(star U*Q*U):Matrix α α ℂ)).trace.re| ≤ (Fintype.card α:ℝ) := by
    calc
      _ ≤ ‖(A*(↑(star U*Q*U):Matrix α α ℂ)).trace‖ := Complex.abs_re_le_norm _
      _ ≤ QAlgorithms.frobNorm A*QAlgorithms.frobNorm (↑(star U*Q*U):Matrix α α ℂ) := norm_trace_mul_le_frob _ _
      _ ≤ Real.sqrt (Fintype.card α:ℝ)*Real.sqrt (Fintype.card α:ℝ) := by
        rw [unitary_frob]
        exact mul_le_mul_of_nonneg_right (contraction_frob_le A hA) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hN.le
  unfold matrixCorrelation
  rw [abs_div,abs_of_pos hN]
  exact (div_le_one hN).mpr hh

lemma matrixCorrelation_change (A B : Matrix α α ℂ) (Q U : Matrix.unitaryGroup α ℂ) :
    |matrixCorrelation A Q U-matrixCorrelation B Q U| ≤
      QAlgorithms.frobNorm (A-B)/Real.sqrt (Fintype.card α:ℝ) := by
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs:0<Real.sqrt (Fintype.card α:ℝ) := Real.sqrt_pos.mpr hN
  have ht:(A*(↑(star U*Q*U):Matrix α α ℂ)).trace.re-
      (B*(↑(star U*Q*U):Matrix α α ℂ)).trace.re=
      ((A-B)*(↑(star U*Q*U):Matrix α α ℂ)).trace.re := by
    rw [sub_mul,Matrix.trace_sub,Complex.sub_re]
  have hh:|((A-B)*(↑(star U*Q*U):Matrix α α ℂ)).trace.re| ≤
      QAlgorithms.frobNorm (A-B)*Real.sqrt (Fintype.card α:ℝ) := by
    calc
      _ ≤ ‖((A-B)*(↑(star U*Q*U):Matrix α α ℂ)).trace‖ := Complex.abs_re_le_norm _
      _ ≤ QAlgorithms.frobNorm (A-B)*QAlgorithms.frobNorm (↑(star U*Q*U):Matrix α α ℂ) := norm_trace_mul_le_frob _ _
      _ = _ := by rw [unitary_frob]
  unfold matrixCorrelation
  rw [←sub_div,ht,abs_div,abs_of_pos hN]
  have hd:=div_le_div_of_nonneg_right hh hN.le
  have he:QAlgorithms.frobNorm (A-B)*Real.sqrt (Fintype.card α:ℝ)/(Fintype.card α:ℝ)=
      QAlgorithms.frobNorm (A-B)/Real.sqrt (Fintype.card α:ℝ) := by
    field_simp [hN.ne',hs.ne']
    nlinarith [congrArg (fun z:ℝ=>QAlgorithms.frobNorm (A-B)*z) (Real.sq_sqrt hN.le)]
  exact hd.trans_eq he

lemma matrixCorrelation_lipschitz (A : Matrix α α ℂ) (hA:QAlgorithms.specNorm A ≤ 1)
    (Q U V : Matrix.unitaryGroup α ℂ) :
    |matrixCorrelation A Q U-matrixCorrelation A Q V| ≤
      (2/Real.sqrt (Fintype.card α:ℝ))*QAlgorithms.frobNorm ((U:Matrix α α ℂ)-(V:Matrix α α ℂ)) := by
  let u:Matrix α α ℂ:=U
  let v:Matrix α α ℂ:=V
  let q:Matrix α α ℂ:=Q
  have hT:(A*(uᴴ*q*u)).trace-(A*(vᴴ*q*v)).trace=
      ((u-v)*(A*uᴴ*q)).trace+((uᴴ-vᴴ)*(q*v*A)).trace := by
    have hr:∀z:Matrix α α ℂ,(A*(zᴴ*q*z)).trace=(z*A*zᴴ*q).trace := by
      intro z
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A*zᴴ*q) z
    rw [hr,hr,←Matrix.trace_sub]
    have he:u*A*uᴴ*q-v*A*vᴴ*q=(u-v)*(A*uᴴ*q)+v*A*(uᴴ-vᴴ)*q := by noncomm_ring
    rw [he,Matrix.trace_add]
    congr 1
    rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  have h1:QAlgorithms.frobNorm (A*uᴴ*q)=QAlgorithms.frobNorm A := by
    simpa only [u,q,Submonoid.coe_mul,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.mul_assoc] using
      frob_mul_unitary A (star U*Q)
  have h2:QAlgorithms.frobNorm (q*v*A)=QAlgorithms.frobNorm A := by
    simpa only [q,v,Submonoid.coe_mul] using frob_unitary_mul (Q*V) A
  have h3:QAlgorithms.frobNorm (uᴴ-vᴴ)=QAlgorithms.frobNorm (u-v) := by
    rw [←Matrix.conjTranspose_sub,frob_conjTranspose]
  have hn:‖(A*(uᴴ*q*u)).trace-(A*(vᴴ*q*v)).trace‖ ≤
      2*QAlgorithms.frobNorm (u-v)*Real.sqrt (Fintype.card α:ℝ) := by
    rw [hT]
    calc
      _ ≤ ‖((u-v)*(A*uᴴ*q)).trace‖+‖((uᴴ-vᴴ)*(q*v*A)).trace‖ := norm_add_le _ _
      _ ≤ QAlgorithms.frobNorm (u-v)*QAlgorithms.frobNorm (A*uᴴ*q)+
          QAlgorithms.frobNorm (uᴴ-vᴴ)*QAlgorithms.frobNorm (q*v*A) :=
        add_le_add (norm_trace_mul_le_frob _ _) (norm_trace_mul_le_frob _ _)
      _ ≤ _ := by
        rw [h1,h2,h3]
        have hh:=mul_le_mul_of_nonneg_left (contraction_frob_le A hA) (InfluenceProof.frob_nonneg (u-v))
        nlinarith
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs:0<Real.sqrt (Fintype.card α:ℝ) := Real.sqrt_pos.mpr hN
  have hreal:=Complex.abs_re_le_norm ((A*(uᴴ*q*u)).trace-(A*(vᴴ*q*v)).trace)
  have ha:=hreal.trans hn
  simp only [Complex.sub_re] at ha
  change |(A*(uᴴ*q*u)).trace.re/(Fintype.card α:ℝ)-
      (A*(vᴴ*q*v)).trace.re/(Fintype.card α:ℝ)| ≤ _
  rw [←sub_div,abs_div,abs_of_pos hN]
  have hd:=div_le_div_of_nonneg_right ha hN.le
  have he:2*QAlgorithms.frobNorm (u-v)*Real.sqrt (Fintype.card α:ℝ)/(Fintype.card α:ℝ)=
      (2/Real.sqrt (Fintype.card α:ℝ))*QAlgorithms.frobNorm (u-v) := by
    field_simp [hN.ne',hs.ne']
    nlinarith [congrArg (fun z:ℝ=>2*QAlgorithms.frobNorm (u-v)*z) (Real.sq_sqrt hN.le)]
  exact hd.trans_eq he

lemma matrixCorrelation_phase (A : Matrix α α ℂ) (Q U V : Matrix.unitaryGroup α ℂ)
    (z : Circle) (hUV:(U:Matrix α α ℂ)=(z:ℂ) • (V:Matrix α α ℂ)) :
    matrixCorrelation A Q U=matrixCorrelation A Q V := by
  have hz:(z:ℂ)*star (z:ℂ)=1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,Circle.norm_coe]
    norm_num
  have hz':star (z:ℂ)*(z:ℂ)=1 := by rw [mul_comm,hz]
  change (A*((U:Matrix α α ℂ)ᴴ*(Q:Matrix α α ℂ)*(U:Matrix α α ℂ))).trace.re/(Fintype.card α:ℝ)=
    (A*((V:Matrix α α ℂ)ᴴ*(Q:Matrix α α ℂ)*(V:Matrix α α ℂ))).trace.re/(Fintype.card α:ℝ)
  rw [hUV,Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hz,hz',one_smul]

end RandomOracleUnitarySynthesis.GeometryProof

/- Module RandomOracleCoupling -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open InfluenceProof PauliProof GeometryProof ResamplingProof
open scoped ComplexConjugate ENNReal
variable {n m m₀ k : ℕ}

instance channel_secondCountable (n:ℕ) : SecondCountableTopology (synthesis_Channel n) := by
  change SecondCountableTopology ((synthesis_Bits n×synthesis_Bits n)→
    (synthesis_Bits n×synthesis_Bits n)→ℂ)
  infer_instance

lemma channelDual_continuous (P:synthesis_Mat n) : Continuous (fun F:synthesis_Channel n=>channelDual F P) := by
  unfold channelDual
  fun_prop

lemma channelCorrelation_continuous (P:synthesis_Pauli n) :
    Continuous (fun z:synthesis_Mat n×synthesis_Channel n=>channelCorrelation z.1 P z.2) := by
  unfold channelCorrelation synthesis_apply Matrix.trace Matrix.diag
  fun_prop

lemma unitaryChannel_continuous : Continuous (@synthesis_unitaryChannel n) := by
  unfold synthesis_unitaryChannel synthesis_coordinates
  fun_prop

lemma coupling_ae_ranges (C:synthesis_Circuit n m m₀ k)
    (γ:Measure (synthesis_Channel n×synthesis_Channel n))
    (hfst:γ.map Prod.fst=(PMF.uniformOfFintype (synthesis_Oracle m₀)).toMeasure.map (synthesis_actualChannel C))
    (hsnd:γ.map Prod.snd=(synthesis_haar n).map synthesis_unitaryChannel) :
    ∀ᵐp∂γ,p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n) := by
  have h1:MeasurableSet (Set.range (synthesis_actualChannel C)) := (Set.finite_range _).measurableSet
  have h2:MeasurableSet (Set.range (@synthesis_unitaryChannel n)) :=
    (isCompact_range unitaryChannel_continuous).isClosed.measurableSet
  have ha:∀ᵐF∂γ.map Prod.fst,F∈Set.range (synthesis_actualChannel C) := by
    rw [hfst]
    exact ae_map_mem_range _ h1 _
  have hb:∀ᵐG∂γ.map Prod.snd,G∈Set.range (@synthesis_unitaryChannel n) := by
    rw [hsnd]
    exact ae_map_mem_range _ h2 _
  exact ((ae_map_iff measurable_fst.aemeasurable h1).mp ha).and
    ((ae_map_iff measurable_snd.aemeasurable h2).mp hb)

/-- Observable overlap on the public channel-coordinate coupling. -/
def pairCorrelation (P:synthesis_Pauli n) (p:synthesis_Channel n×synthesis_Channel n) : ℝ :=
  channelCorrelation (channelDual p.1 (DirectFidelity.State.W P)) P p.2

lemma pairCorrelation_continuous (P:synthesis_Pauli n) : Continuous (pairCorrelation P) := by
  unfold pairCorrelation channelCorrelation channelDual synthesis_apply Matrix.trace Matrix.diag
  fun_prop

lemma pairCorrelation_actual (C:synthesis_Circuit n m m₀ k) (f:synthesis_Oracle m₀)
    (P:synthesis_Pauli n) (U:synthesis_Unitary n) :
    pairCorrelation P (synthesis_actualChannel C f,synthesis_unitaryChannel U)=
      synthesis_correlation (synthesis_observable C f P) P U := by
  simp only [pairCorrelation,actualChannel_dual,unitaryChannel_correlation]

lemma correlation_abs_le (A:synthesis_Mat n) (hA:synthesis_IsContraction A)
    (P:synthesis_Pauli n) (U:synthesis_Unitary n) :
    |synthesis_correlation A P U| ≤ 1 := by
  have hh:=matrixCorrelation_bound A hA (pauliUnitary P) U
  have hc:(Fintype.card (synthesis_Bits n):ℝ)=(2:ℝ)^n := by
    simp [synthesis_Bits,DirectFidelity.State.Q]
  simpa only [matrixCorrelation,synthesis_correlation,Submonoid.coe_mul,Unitary.coe_star,
    Matrix.star_eq_conjTranspose,pauliUnitary,hc] using hh

lemma pairCorrelation_abs_le (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (p:synthesis_Channel n×synthesis_Channel n)
    (hp:p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n)) :
    |pairCorrelation P p| ≤ 1 := by
  obtain ⟨⟨f,hf⟩,⟨U,hU⟩⟩:=hp
  have he:p=(synthesis_actualChannel C f,synthesis_unitaryChannel U) := Prod.ext hf.symm hU.symm
  rw [he,pairCorrelation_actual]
  apply correlation_abs_le
  rw [←observableCircuit_A C P f]
  exact NetProof.A_contraction _ _

lemma pairCorrelation_integrable (C:synthesis_Circuit n m m₀ k) (P:synthesis_Pauli n)
    (γ:Measure (synthesis_Channel n×synthesis_Channel n)) [IsProbabilityMeasure γ]
    (hp:∀ᵐp∂γ,p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n)) :
    Integrable (pairCorrelation P) γ :=
  (integrable_const (1:ℝ)).mono' (pairCorrelation_continuous P).aestronglyMeasurable
    (hp.mono (fun p hh=>by simpa only [Real.norm_eq_abs] using pairCorrelation_abs_le C P p hh))

lemma pairCorrelation_zero (C:synthesis_Circuit n m m₀ k)
    (p:synthesis_Channel n×synthesis_Channel n)
    (hp:p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n)) :
    pairCorrelation (fun _:Fin n=>0) p=1 := by
  obtain ⟨⟨f,hf⟩,⟨U,hU⟩⟩:=hp
  have he:p=(synthesis_actualChannel C f,synthesis_unitaryChannel U) := Prod.ext hf.symm hU.symm
  rw [he,pairCorrelation_actual]
  have hl:synthesis_liftPauli C (fun _:Fin n=>0)=1 := by
    have hd:(DirectFidelity.State.W (fun _:Fin n=>0))=1 := W_zero n
    apply (Matrix.reindex (joinEquiv C.system_le).symm (joinEquiv C.system_le).symm).injective
    change _ = (1:synthesis_Mat m).submatrix (joinEquiv C.system_le) (joinEquiv C.system_le)
    have he:=liftOperator_reindex C.system_le (DirectFidelity.State.W (fun _:Fin n=>0))
    change (synthesis_liftPauli C (fun _:Fin n=>0)).submatrix (joinEquiv C.system_le) (joinEquiv C.system_le)=_ at he
    simp only [Matrix.reindex_apply,Equiv.symm_symm,he,hd,
      Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
  have ho:synthesis_observable C f (fun _:Fin n=>0)=1 := by
    simp only [synthesis_observable,hl,Matrix.mul_one,Matrix.mul_assoc]
    have hW:(synthesis_W C f)ᴴ*synthesis_W C f=1 := (Unitary.mem_iff.mp (segment_unitary C f 0 k)).1
    rw [←Matrix.mul_assoc (synthesis_W C f)ᴴ,hW]
    simp only [Matrix.one_mul,J_isometry]
  simp only [ho,synthesis_correlation,W_zero,Matrix.mul_one,Matrix.one_mul]
  rw [show (U:synthesis_Mat n)ᴴ*(U:synthesis_Mat n)=1 from (Unitary.mem_iff.mp U.property).1]
  have hr:((2:ℂ)^n).re=(2:ℝ)^n := by norm_cast
  simp only [Matrix.trace_one,synthesis_Bits,DirectFidelity.State.Q,Fintype.card_fun,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,hr]
  exact div_self (by positivity)

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleCouplingMean -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open InfluenceProof PauliProof GeometryProof ResamplingProof
open scoped ComplexConjugate ENNReal
variable {n m m₀ k : ℕ}

lemma average_integrable {α β:Type} [Fintype α] [MeasurableSpace β]
    (μ:Measure β) (F:α→β→ℝ) (hF:∀a,Integrable (F a) μ) :
    Integrable (fun b=>synthesis_average (fun a=>F a b)) μ :=
  (integrable_finsetSum univ (fun a _=>hF a)).div_const _

lemma integral_average {α β:Type} [Fintype α] [MeasurableSpace β]
    (μ:Measure β) (F:α→β→ℝ) (hF:∀a,Integrable (F a) μ) :
    (∫b,synthesis_average (fun a=>F a b) ∂μ)=synthesis_average (fun a=>∫b,F a b ∂μ) := by
  unfold synthesis_average
  rw [integral_div,integral_finsetSum univ (fun a _=>hF a)]

def averagePairCorrelation (p:synthesis_Channel n×synthesis_Channel n) : ℝ :=
  synthesis_average (fun P:synthesis_Pauli n=>pairCorrelation P p)

lemma averagePairCorrelation_bounds (C:synthesis_Circuit n m m₀ k)
    (p:synthesis_Channel n×synthesis_Channel n)
    (hp:p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n)) :
    -1 ≤ averagePairCorrelation p∧averagePairCorrelation p ≤ 1 := by
  have hh:∀P:synthesis_Pauli n,-1 ≤ pairCorrelation P p∧pairCorrelation P p ≤ 1 :=
    fun P=>abs_le.mp (pairCorrelation_abs_le C P p hp)
  constructor
  · have h:=average_mono (fun _:synthesis_Pauli n=>(-1:ℝ)) (fun P=>pairCorrelation P p) (fun P=>(hh P).1)
    simpa only [ResamplingProof.average_const,averagePairCorrelation] using h
  · have h:=average_mono (fun P=>pairCorrelation P p) (fun _:synthesis_Pauli n=>(1:ℝ)) (fun P=>(hh P).2)
    simpa only [ResamplingProof.average_const,averagePairCorrelation] using h

lemma coupling_average_lower (C:synthesis_Circuit n m m₀ k) (ε:ℝ) (hε:0 ≤ ε)
    (γ:Measure (synthesis_Channel n×synthesis_Channel n)) [IsProbabilityMeasure γ]
    (hp:∀ᵐp∂γ,p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n))
    (herr:(∫⁻p,ENNReal.ofReal (synthesis_diamond p.1 p.2) ∂γ) ≤ ENNReal.ofReal ε) :
    1-ε ≤ synthesis_average (fun P:synthesis_Pauli n=>∫p,pairCorrelation P p ∂γ) := by
  have hi:Integrable (@averagePairCorrelation n) γ := average_integrable γ (fun P:synthesis_Pauli n=>pairCorrelation P)
    (fun P=>pairCorrelation_integrable C P γ hp)
  have hdi:Integrable (fun p=>1-averagePairCorrelation p) γ := (integrable_const (1:ℝ)).sub hi
  have hnonneg:∀ᵐp∂γ,0 ≤ 1-averagePairCorrelation p :=
    hp.mono (fun p hh=>sub_nonneg.mpr (averagePairCorrelation_bounds C p hh).2)
  have hle:(∫⁻p,ENNReal.ofReal (1-averagePairCorrelation p) ∂γ) ≤ ENNReal.ofReal ε := by
    apply le_trans (lintegral_mono_ae (hp.mono (fun p hh=>?_))) herr
    obtain ⟨⟨f,hf⟩,⟨U,hU⟩⟩:=hh
    have he:p=(synthesis_actualChannel C f,synthesis_unitaryChannel U) := Prod.ext hf.symm hU.symm
    subst p
    apply ENNReal.ofReal_le_ofReal
    have h:=synthesis_dirty_pauli_overlap C f U
    have heq:averagePairCorrelation (synthesis_actualChannel C f,synthesis_unitaryChannel U)=
        synthesis_average (fun P:synthesis_Pauli n=>synthesis_correlation (synthesis_observable C f P) P U) := by
      simp only [averagePairCorrelation,pairCorrelation_actual]
    rw [←heq] at h
    linarith
  rw [←ofReal_integral_eq_lintegral_ofReal hdi hnonneg] at hle
  have hh: (∫p,1-averagePairCorrelation p ∂γ) ≤ ε := (ENNReal.ofReal_le_ofReal_iff hε).mp hle
  rw [integral_sub (integrable_const (1:ℝ)) hi,integral_const] at hh
  simp only [probReal_univ,one_smul] at hh
  have hav:=integral_average γ (fun P:synthesis_Pauli n=>pairCorrelation P)
    (fun P=>pairCorrelation_integrable C P γ hp)
  change (∫p,averagePairCorrelation p ∂γ)=_ at hav
  rw [hav] at hh
  linarith

lemma nonidentity_coupling_overlap (C:synthesis_Circuit n m m₀ k) (ε:ℝ)
    (hε:0 ≤ ε) (hε1:ε<1) (hgap:4 ≤ ((2:ℝ)^n)^2*(1-ε))
    (γ:Measure (synthesis_Channel n×synthesis_Channel n)) [IsProbabilityMeasure γ]
    (hp:∀ᵐp∂γ,p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n))
    (herr:(∫⁻p,ENNReal.ofReal (synthesis_diamond p.1 p.2) ∂γ) ≤ ENNReal.ofReal ε) :
    ∃Q:synthesis_Pauli n,Q≠(fun _=>0)∧(1-ε)/2 ≤ ∫p,pairCorrelation Q p ∂γ := by
  let H:synthesis_Pauli n→ℝ:=fun P=>∫p,pairCorrelation P p ∂γ
  have hlow:=coupling_average_lower C ε hε γ hp herr
  change 1-ε ≤ synthesis_average H at hlow
  have hzero:H (fun _=>0)=1 := by
    have he:pairCorrelation (fun _:Fin n=>0)=ᵐ[γ] fun _=>1 := hp.mono (fun p hh=>pairCorrelation_zero C p hh)
    dsimp only [H]
    rw [integral_congr_ae he]
    simp
  have hc:(Fintype.card (synthesis_Pauli n):ℝ)=((2:ℝ)^n)^2 := by
    simp only [synthesis_Pauli,DirectFidelity.State.P,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    simp only [pow_two,←mul_pow]
    norm_num
  have hN:0<((2:ℝ)^n)^2 := by positivity
  by_contra hn
  push_neg at hn
  have hb:∀P:synthesis_Pauli n,H P ≤ (1-ε)/2+(if P=(fun _=>0) then 1 else 0) := by
    intro P
    by_cases he:P=(fun _=>0)
    · rw [he,hzero,if_pos rfl]
      linarith
    · rw [if_neg he]
      simpa only [H,add_zero] using (hn P he).le
  have hsum:=average_mono H (fun P:synthesis_Pauli n=>(1-ε)/2+(if P=(fun _=>0) then 1 else 0)) hb
  rw [average_add,ResamplingProof.average_const] at hsum
  have hind:synthesis_average (fun P:synthesis_Pauli n=>if P=(fun _=>0) then (1:ℝ) else 0)=1/((2:ℝ)^n)^2 := by
    simp only [synthesis_average,Finset.sum_ite_eq',Finset.mem_univ,if_true,hc]
  rw [hind] at hsum
  have hh:(1-ε)/2+1/((2:ℝ)^n)^2 < 1-ε := by
    have hi:1/((2:ℝ)^n)^2 ≤ (1-ε)/4 := (div_le_iff₀ hN).mpr (by nlinarith)
    linarith
  exact (not_lt_of_ge hlow) (lt_of_le_of_lt hsum hh)

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleNetMeasure -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open InfluenceProof PauliProof GeometryProof ResamplingProof
open scoped ComplexConjugate ENNReal
variable {n m m₀ k : ℕ}

lemma integral_uniform_average {α:Type} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] (f:α→ℝ) :
    (∫x,f x ∂(PMF.uniformOfFintype α).toMeasure)=synthesis_average f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [←mul_sum]
  unfold synthesis_average
  ring

lemma frob_continuous {α:Type} [Fintype α] [DecidableEq α] [Nonempty α] :
    Continuous (QAlgorithms.frobNorm:Matrix α α ℂ→ℝ) := by
  have he:∀A:Matrix α α ℂ,QAlgorithms.frobNorm A=Real.sqrt (∑x,∑y,‖A x y‖^2) :=
    fun A=>frob_eq_sqrt_entries A
  simp only [show (QAlgorithms.frobNorm:Matrix α α ℂ→ℝ)=fun A=>Real.sqrt (∑x,∑y,‖A x y‖^2) from funext he]
  fun_prop

def badNet (T:Finset (synthesis_Mat n)) (P:synthesis_Pauli n) (d:ℝ) (F:synthesis_Channel n) : Prop :=
  ∀A∈T,d*Real.sqrt ((2:ℝ)^n)<QAlgorithms.frobNorm (A-channelDual F (DirectFidelity.State.W P))

lemma badNet_measurable (T:Finset (synthesis_Mat n)) (P:synthesis_Pauli n) (d:ℝ) :
    MeasurableSet {F:synthesis_Channel n|badNet T P d F} := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [badNet]
  | @insert A T hA ih =>
    have he:{F:synthesis_Channel n|badNet (insert A T) P d F}=
        {F|d*Real.sqrt ((2:ℝ)^n)<QAlgorithms.frobNorm (A-channelDual F (DirectFidelity.State.W P))}∩
        {F|badNet T P d F} := by ext F;simp [badNet]
    rw [he]
    exact (measurableSet_lt measurable_const
      (frob_continuous.comp (continuous_const.sub (channelDual_continuous _))).measurable).inter ih

lemma badNet_indicator_measurable (T:Finset (synthesis_Mat n)) (P:synthesis_Pauli n) (d:ℝ) :
    Measurable (fun F:synthesis_Channel n=>if badNet T P d F then (1:ℝ) else 0) := by
  exact measurable_const.ite (badNet_measurable T P d) measurable_const

lemma badNet_actual (C:synthesis_Circuit n m m₀ k) (T:Finset (synthesis_Mat n))
    (P:synthesis_Pauli n) (d:ℝ) (f:synthesis_Oracle m₀) :
    badNet T P d (synthesis_actualChannel C f) ↔
      ∀A∈T,d*Real.sqrt ((2:ℝ)^n)<QAlgorithms.frobNorm (A-synthesis_observable C f P) := by
  simp only [badNet,actualChannel_dual]

lemma coupling_badNet_integral (C:synthesis_Circuit n m m₀ k)
    (γ:Measure (synthesis_Channel n×synthesis_Channel n))
    (hfst:γ.map Prod.fst=(PMF.uniformOfFintype (synthesis_Oracle m₀)).toMeasure.map (synthesis_actualChannel C))
    (T:Finset (synthesis_Mat n)) (P:synthesis_Pauli n) (d:ℝ) :
    (∫p,(if badNet T P d p.1 then (1:ℝ) else 0) ∂γ)=
      synthesis_average (fun f:synthesis_Oracle m₀=>if badNet T P d (synthesis_actualChannel C f) then 1 else 0) := by
  let b:synthesis_Channel n→ℝ:=fun F=>if badNet T P d F then 1 else 0
  have hb:Measurable b:=badNet_indicator_measurable T P d
  change (∫p,b p.1 ∂γ)=_
  rw [←integral_map measurable_fst.aemeasurable hb.aestronglyMeasurable,hfst,
    integral_map (measurable_of_finite (synthesis_actualChannel C)).aemeasurable hb.aestronglyMeasurable]
  exact integral_uniform_average _

def netMaximum (T:Finset (synthesis_Mat n)) (hT:T.Nonempty)
    (P:synthesis_Pauli n) (G:synthesis_Channel n) : ℝ :=
  T.sup' hT (fun A=>channelCorrelation A P G)

lemma netMaximum_continuous (T:Finset (synthesis_Mat n)) (hT:T.Nonempty)
    (P:synthesis_Pauli n) : Continuous (netMaximum T hT P) := by
  unfold netMaximum
  apply Continuous.finset_sup'_apply hT
  intro A hA
  unfold channelCorrelation synthesis_apply Matrix.trace Matrix.diag
  fun_prop

lemma netMaximum_bounds (T:Finset (synthesis_Mat n)) (hT:T.Nonempty)
    (hcontract:∀A∈T,synthesis_IsContraction A) (P:synthesis_Pauli n)
    (G:synthesis_Channel n) (hG:G∈Set.range (@synthesis_unitaryChannel n)) :
    -1 ≤ netMaximum T hT P G∧netMaximum T hT P G ≤ 1 := by
  obtain ⟨U,rfl⟩:=hG
  have hh:∀A∈T,-1 ≤ channelCorrelation A P (synthesis_unitaryChannel U)∧
      channelCorrelation A P (synthesis_unitaryChannel U) ≤ 1 := by
    intro A hA
    rw [unitaryChannel_correlation]
    exact abs_le.mp (correlation_abs_le A (hcontract A hA) P U)
  unfold netMaximum
  constructor
  · obtain ⟨A,hA⟩:=hT
    exact (hh A hA).1.trans (Finset.le_sup' (fun B=>channelCorrelation B P (synthesis_unitaryChannel U)) hA)
  · exact Finset.sup'_le hT _ (fun A hA=>(hh A hA).2)

lemma integral_lower_probability {α:Type} [MeasurableSpace α]
    (μ:Measure α) [IsProbabilityMeasure μ] (F:α→ℝ) (hFi:Integrable F μ)
    (a:ℝ) (ha:0 ≤ a) (hmean:2*a ≤ ∫x,F x ∂μ)
    (hbound:∀ᵐx∂μ,F x ≤ 1) (hs:MeasurableSet {x|a ≤ F x}) :
    ENNReal.ofReal a ≤ μ {x|a ≤ F x} := by
  let s:Set α:={x|a ≤ F x}
  have hI:Integrable (s.indicator (fun _=>(1:ℝ))) μ := (integrable_const (1:ℝ)).indicator hs
  have hpt:∀ᵐx∂μ,F x ≤ a+s.indicator (fun _=>(1:ℝ)) x := by
    filter_upwards [hbound] with x hx
    by_cases he:x∈s
    · simp only [Set.indicator_of_mem he]
      linarith
    · simp only [Set.indicator_of_notMem he,add_zero]
      exact (lt_of_not_ge he).le
  have hh:=integral_mono_ae hFi ((integrable_const a).add hI) hpt
  change (∫x,F x ∂μ) ≤ ∫x,a+s.indicator (fun _=>(1:ℝ)) x ∂μ at hh
  rw [integral_add (integrable_const a) hI,integral_const] at hh
  simp only [probReal_univ,one_smul] at hh
  have hval:(∫x,s.indicator (fun _=>(1:ℝ)) x ∂μ)=μ.real s := by
    exact integral_indicator_one hs
  rw [hval] at hh
  have hl:a ≤ μ.real s := by linarith
  calc
    ENNReal.ofReal a ≤ ENNReal.ofReal (μ.real s) := ENNReal.ofReal_le_ofReal hl
    _ = μ s := ENNReal.ofReal_toReal (measure_ne_top μ s)

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleNetApproximation -/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace RandomOracleUnitarySynthesis.ChannelProof
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open InfluenceProof PauliProof GeometryProof ResamplingProof
open scoped ComplexConjugate ENNReal
variable {n m m₀ k : ℕ}

lemma correlation_change (A B:synthesis_Mat n) (P:synthesis_Pauli n) (U:synthesis_Unitary n) :
    |synthesis_correlation A P U-synthesis_correlation B P U| ≤
      QAlgorithms.frobNorm (A-B)/Real.sqrt ((2:ℝ)^n) := by
  have hh:=matrixCorrelation_change A B (pauliUnitary P) U
  have hc:(Fintype.card (synthesis_Bits n):ℝ)=(2:ℝ)^n := by
    simp [synthesis_Bits,DirectFidelity.State.Q]
  simpa only [matrixCorrelation,synthesis_correlation,Submonoid.coe_mul,Unitary.coe_star,
    Matrix.star_eq_conjTranspose,pauliUnitary,hc] using hh

lemma pairCorrelation_net_bound (C:synthesis_Circuit n m m₀ k)
    (T:Finset (synthesis_Mat n)) (hT:T.Nonempty) (hcontract:∀A∈T,synthesis_IsContraction A)
    (P:synthesis_Pauli n) (d:ℝ) (hd:0 ≤ d)
    (p:synthesis_Channel n×synthesis_Channel n)
    (hp:p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n)) :
    pairCorrelation P p ≤ netMaximum T hT P p.2+d+
      2*(if badNet T P d p.1 then (1:ℝ) else 0) := by
  by_cases hb:badNet T P d p.1
  · rw [if_pos hb]
    have h1:pairCorrelation P p ≤ 1 := (abs_le.mp (pairCorrelation_abs_le C P p hp)).2
    have h2: -1 ≤ netMaximum T hT P p.2 := (netMaximum_bounds T hT hcontract P p.2 hp.2).1
    linarith
  · rw [if_neg hb,mul_zero,add_zero]
    obtain ⟨⟨f,hf⟩,⟨U,hU⟩⟩:=hp
    have he:p=(synthesis_actualChannel C f,synthesis_unitaryChannel U) := Prod.ext hf.symm hU.symm
    subst p
    rw [badNet_actual] at hb
    push_neg at hb
    obtain ⟨A,hA,hnear⟩:=hb
    have hdiff:=correlation_change A (synthesis_observable C f P) P U
    have hs:0<Real.sqrt ((2:ℝ)^n) := Real.sqrt_pos.mpr (pow_pos (by norm_num) _)
    have herr:QAlgorithms.frobNorm (A-synthesis_observable C f P)/Real.sqrt ((2:ℝ)^n) ≤ d :=
      (div_le_iff₀ hs).mpr hnear
    have hle:channelCorrelation A P (synthesis_unitaryChannel U) ≤
        netMaximum T hT P (synthesis_unitaryChannel U) :=
      Finset.le_sup' (fun B=>channelCorrelation B P (synthesis_unitaryChannel U)) hA
    rw [unitaryChannel_correlation] at hle
    rw [pairCorrelation_actual]
    have hdiff': -d ≤ synthesis_correlation A P U-synthesis_correlation (synthesis_observable C f P) P U :=
      (abs_le.mp (hdiff.trans herr)).1
    linarith

lemma coupling_netMaximum_integrable (C:synthesis_Circuit n m m₀ k)
    (γ:Measure (synthesis_Channel n×synthesis_Channel n)) [IsProbabilityMeasure γ]
    (hp:∀ᵐp∂γ,p.1∈Set.range (synthesis_actualChannel C)∧p.2∈Set.range (@synthesis_unitaryChannel n))
    (T:Finset (synthesis_Mat n)) (hT:T.Nonempty) (hcontract:∀A∈T,synthesis_IsContraction A)
    (P:synthesis_Pauli n) : Integrable (fun p=>netMaximum T hT P p.2) γ := by
  apply (integrable_const (1:ℝ)).mono'
    ((netMaximum_continuous T hT P).comp continuous_snd).aestronglyMeasurable
  filter_upwards [hp] with p hh
  simpa only [Real.norm_eq_abs,abs_le,Function.comp_def] using netMaximum_bounds T hT hcontract P p.2 hh.2

lemma coupling_netMaximum_integral
    (γ:Measure (synthesis_Channel n×synthesis_Channel n))
    (hsnd:γ.map Prod.snd=(synthesis_haar n).map synthesis_unitaryChannel)
    (T:Finset (synthesis_Mat n)) (hT:T.Nonempty) (P:synthesis_Pauli n) :
    (∫p,netMaximum T hT P p.2 ∂γ)=
      ∫U,netMaximum T hT P (synthesis_unitaryChannel U) ∂synthesis_haar n := by
  have hm:Measurable (netMaximum T hT P):=(netMaximum_continuous T hT P).measurable
  rw [←integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable,hsnd,
    integral_map unitaryChannel_continuous.measurable.aemeasurable hm.aestronglyMeasurable]

lemma integral_mono_add_const_mul {α:Type} [MeasurableSpace α]
    (μ:Measure α) [IsProbabilityMeasure μ] (f g h:α→ℝ)
    (hfi:Integrable f μ) (hgi:Integrable g μ) (hhi:Integrable h μ) (d c:ℝ)
    (hineq:∀ᵐx∂μ,f x ≤ g x+d+c*h x) :
    (∫x,f x ∂μ) ≤ (∫x,g x ∂μ)+d+c*(∫x,h x ∂μ) := by
  have hh := integral_mono_ae hfi ((hgi.add (integrable_const d)).add (hhi.const_mul c)) hineq
  change (∫x,f x ∂μ) ≤ ∫x,g x+d+c*h x ∂μ at hh
  rw [integral_add (f:=fun x=>g x+d) (g:=fun x=>c*h x)
      (hgi.add (integrable_const d)) (hhi.const_mul c),
    integral_add hgi (integrable_const d),integral_const_mul,integral_const] at hh
  simpa only [probReal_univ,one_smul] using hh

lemma coupling_net_mean_lower (C:synthesis_Circuit n m m₀ k)
    (γ:Measure (synthesis_Channel n×synthesis_Channel n)) [IsProbabilityMeasure γ]
    (hfst:γ.map Prod.fst=(PMF.uniformOfFintype (synthesis_Oracle m₀)).toMeasure.map (synthesis_actualChannel C))
    (hsnd:γ.map Prod.snd=(synthesis_haar n).map synthesis_unitaryChannel)
    (T:Finset (synthesis_Mat n)) (hT:T.Nonempty) (hcontract:∀A∈T,synthesis_IsContraction A)
    (P:synthesis_Pauli n) (d ζ b:ℝ) (hd:0 ≤ d)
    (hbad:synthesis_average (fun f:synthesis_Oracle m₀=>
      if badNet T P d (synthesis_actualChannel C f) then 1 else 0) ≤ ζ)
    (hmean:b ≤ ∫p,pairCorrelation P p ∂γ) :
    b-d-2*ζ ≤ ∫U,netMaximum T hT P (synthesis_unitaryChannel U) ∂synthesis_haar n := by
  have hp:=coupling_ae_ranges C γ hfst hsnd
  have hPi:=pairCorrelation_integrable C P γ hp
  have hMi:=coupling_netMaximum_integrable C γ hp T hT hcontract P
  let bad:synthesis_Channel n×synthesis_Channel n→ℝ:=fun p=>if badNet T P d p.1 then 1 else 0
  have hbi:Integrable bad γ := by
    apply (integrable_const (1:ℝ)).mono'
      ((badNet_indicator_measurable T P d).comp measurable_fst).aestronglyMeasurable
    filter_upwards with p
    change ‖(if badNet T P d p.1 then (1:ℝ) else 0)‖ ≤ 1
    split_ifs <;> norm_num
  have hcomp:=integral_mono_add_const_mul γ (pairCorrelation P)
    (fun p=>netMaximum T hT P p.2) bad hPi hMi hbi d 2
    (hp.mono (fun p hh=>pairCorrelation_net_bound C T hT hcontract P d hd p hh))
  have hb:(∫p,bad p ∂γ) ≤ ζ := by
    change (∫p,(if badNet T P d p.1 then (1:ℝ) else 0) ∂γ) ≤ ζ
    rw [coupling_badNet_integral C γ hfst T P d]
    exact hbad
  rw [coupling_netMaximum_integral γ hsnd T hT P] at hcomp
  linarith only [hcomp,hmean,hb]

end RandomOracleUnitarySynthesis.ChannelProof

/- Module RandomOracleResamplingEntropy -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
variable {n m m₀ k : ℕ}

/-- Actual finite conditional law of the path, written as a normalized sum. -/
def pathMass (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (g : synthesis_Oracle m₀) : ℝ :=
  synthesis_average (fun coins:synthesis_Oracle m₀=>
    if (synthesis_resamplePath C r f coins i).1=g then 1 else 0)

lemma path_current_unvisited (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) :
    (synthesis_resamplePath C r f coins i).1 (synthesis_order m₀ j)=f (synthesis_order m₀ j) := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    have hi:i<Fintype.card (synthesis_Bits m₀) := by omega
    have hne:synthesis_order m₀ j≠synthesis_order m₀ ⟨i,hi⟩ := by
      intro hh
      have hv:j.val=i := congrArg Fin.val ((synthesis_order m₀).injective hh)
      omega
    simp only [synthesis_resamplePath,dif_pos hi]
    split_ifs <;> simp only [Function.update_of_ne hne,ih (by omega)]

lemma pathMass_zero (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f g : synthesis_Oracle m₀)
    (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀))) (hij:i ≤ j.val)
    (hg:g (synthesis_order m₀ j)≠f (synthesis_order m₀ j)) : pathMass C r f i g=0 := by
  have hne:∀coins:synthesis_Oracle m₀,(synthesis_resamplePath C r f coins i).1≠g := by
    intro coins he
    have hh:=path_current_unvisited C r f coins i j hij
    rw [he] at hh
    exact hg hh
  simp only [pathMass,hne,if_false,average_const]

lemma pathMass_succ (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀)) (g : synthesis_Oracle m₀) :
    pathMass C r f (i+1) g=oneStepOp C r (visit i) (pathMass C r f i) g := by
  have hv:visit i=synthesis_order m₀ ⟨i,hi⟩ := by simp only [visit,dif_pos hi]
  unfold pathMass
  rw [average_next C r f i hi (fun h:synthesis_Oracle m₀=>if h=g then 1 else 0),←hv]
  simp_rw [forced_pair_sum]
  have he:∀h:synthesis_Oracle m₀,lazyFlip C r (visit i) h=g ↔ h=lazyFlip C r (visit i) g := by
    intro h
    constructor
    · intro hh
      rw [←hh,lazyFlip_involutive C r (visit i) h]
    · intro hh
      rw [hh,lazyFlip_involutive C r (visit i) g]
  simp only [he,average_div,average_add]

lemma sum_oneStepOp (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) : (∑f,oneStepOp C r x a f)=∑f,a f := by
  simp only [forced_pair_sum]
  rw [← sum_div,sum_add_distrib]
  have he:(∑f,a (lazyFlip C r x f))=∑f,a f := Equiv.sum_comp (lazyFlipEquiv C r x) a
  rw [he]
  ring

/-- A single Shannon summand, with the published zero-mass convention. -/
def entropyTerm (p : ℝ) : ℝ := -p*Real.logb 2 p

lemma entropyTerm_zero : entropyTerm 0=0 := by simp [entropyTerm]
lemma entropyTerm_one : entropyTerm 1=0 := by simp [entropyTerm]

lemma entropyTerm_half (p : ℝ) : entropyTerm (p/2)=entropyTerm p/2+p/2 := by
  by_cases hp:p=0
  · simp [hp,entropyTerm_zero]
  · unfold entropyTerm
    rw [Real.logb_div hp (by norm_num),Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    ring

lemma entropyTerm_half_pair (p q : ℝ) (h:p=0∨q=0) :
    entropyTerm ((p+q)/2)=(entropyTerm p+entropyTerm q)/2+(p+q)/2 := by
  rcases h with h|h
  · simp only [h,zero_add,entropyTerm_zero,entropyTerm_half]
  · simp only [h,add_zero,entropyTerm_zero,entropyTerm_half]

lemma entropy_oneStep (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (p : synthesis_Oracle m₀→ℝ)
    (hp:∀f,p f=0∨p (synthesis_flip f x)=0) :
    FuchsVdGraaf.entropy (oneStepOp C r x p)=FuchsVdGraaf.entropy p+
      ∑f,if synthesis_resampleAllowed C r f x then p f else 0 := by
  have hpoint:∀f:synthesis_Oracle m₀,entropyTerm (oneStepOp C r x p f)=
      oneStepOp C r x (fun g=>entropyTerm (p g)) f+
      oneStepOp C r x (fun g=>if synthesis_resampleAllowed C r g x then p g else 0) f := by
    intro f
    simp only [forced_pair_sum]
    by_cases ha:synthesis_resampleAllowed C r f x
    · have hb:synthesis_resampleAllowed C r (synthesis_flip f x) x := (allowed_flip C r f x).mpr ha
      simp only [lazyFlip,if_pos ha,if_pos hb]
      exact entropyTerm_half_pair _ _ (hp f)
    · simp only [lazyFlip,if_neg ha,add_zero,zero_div]
      have he:(p f+p f)/2=p f := by ring
      rw [he]
      ring
  have hs:∀a:synthesis_Oracle m₀→ℝ,FuchsVdGraaf.entropy a=∑f,entropyTerm (a f) := by
    intro a
    unfold FuchsVdGraaf.entropy entropyTerm
    rw [← sum_neg_distrib]
    simp only [neg_mul]
  rw [hs,hs]
  simp_rw [hpoint]
  rw [sum_add_distrib,sum_oneStepOp,sum_oneStepOp]

lemma path_entropy_succ (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀)) :
    FuchsVdGraaf.entropy (pathMass C r f (i+1))=FuchsVdGraaf.entropy (pathMass C r f i)+
      ∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0 := by
  have hp:∀g:synthesis_Oracle m₀,pathMass C r f i g=0∨
      pathMass C r f i (synthesis_flip g (visit i))=0 := by
    intro g
    have hv:visit i=synthesis_order m₀ ⟨i,hi⟩ := by simp only [visit,dif_pos hi]
    by_cases hg:g (visit i)=f (visit i)
    · right
      apply pathMass_zero C r f _ i ⟨i,hi⟩ (le_refl _)
      rw [←hv]
      simp only [synthesis_flip,Function.update_self]
      rw [←hg]
      cases g (visit i) <;> decide
    · left
      exact pathMass_zero C r f g i ⟨i,hi⟩ (le_refl _) (by simpa only [hv] using hg)
  have hs: pathMass C r f (i+1)=oneStepOp C r (visit i) (pathMass C r f i) :=
    funext (pathMass_succ C r f i hi)
  rw [hs]
  exact entropy_oneStep C r (visit i) _ hp

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEntropyLaw -/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset Classical
variable {n m m₀ k : ℕ}

lemma uniform_map_real {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (F : α→β) (b : β) : ((PMF.uniformOfFintype α).map F b).toReal=
      synthesis_average (fun a:α=>if F a=b then 1 else 0) := by
  calc
    _ = synthesis_mean ((PMF.uniformOfFintype α).map F) (fun c:β=>if c=b then 1 else 0) := by
      simp only [synthesis_mean,mul_ite,mul_one,mul_zero]
      simp
    _ = _ := by rw [mean_map,mean_uniform]

lemma pathMass_mean (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (a : synthesis_Oracle m₀→ℝ) :
    (∑g,pathMass C r f i g*a g)=synthesis_average (fun coins:synthesis_Oracle m₀=>
      a (synthesis_resamplePath C r f coins i).1) := by
  unfold pathMass synthesis_average
  simp only [div_mul_eq_mul_div,Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [←sum_div,sum_comm]
  congr 1
  apply sum_congr rfl
  intro coins hc
  simp

lemma pathMass_initial_entropy (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) : FuchsVdGraaf.entropy (pathMass C r f 0)=0 := by
  have he:∀g:synthesis_Oracle m₀,pathMass C r f 0 g=if f=g then 1 else 0 := by
    intro g
    unfold pathMass
    simp only [synthesis_resamplePath]
    exact average_const (α:=synthesis_Oracle m₀) (if f=g then 1 else 0)
  unfold FuchsVdGraaf.entropy
  simp only [he]
  have hz:∀g:synthesis_Oracle m₀,(if f=g then (1:ℝ) else 0)*Real.logb 2 (if f=g then 1 else 0)=0 := by
    intro g
    split_ifs <;> simp
  simp only [hz,sum_const_zero,neg_zero]

lemma average_path_entropy_succ (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀)) :
    synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f (i+1)))=
      synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f i))+
      synthesis_average (fun f:synthesis_Oracle m₀=>if synthesis_resampleAllowed C r f (visit i) then 1 else 0) := by
  have he:∀f:synthesis_Oracle m₀,
      (∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0)=
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        if synthesis_resampleAllowed C r (synthesis_resamplePath C r f coins i).1 (visit i) then 1 else 0) := by
    intro f
    calc
      _ = ∑g,pathMass C r f i g*(if synthesis_resampleAllowed C r g (visit i) then 1 else 0) := by
        apply sum_congr rfl
        intro g hg
        split_ifs <;> simp only [mul_one,mul_zero]
      _ = _ := pathMass_mean C r f i (fun g=>if synthesis_resampleAllowed C r g (visit i) then 1 else 0)
  calc
    _ = synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f i)+
        ∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0) :=
      congrArg synthesis_average (funext (fun f=>path_entropy_succ C r f i hi))
    _ = synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f i))+
        synthesis_average (fun f:synthesis_Oracle m₀=>
          ∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0) := average_add _ _
    _ = _ := by
      congr 1
      calc
        _ = synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_average (fun coins:synthesis_Oracle m₀=>
            if synthesis_resampleAllowed C r (synthesis_resamplePath C r f coins i).1 (visit i) then 1 else 0)) :=
          congrArg synthesis_average (funext he)
        _ = _ := average_path_current C r i (fun f:synthesis_Oracle m₀=>
          if synthesis_resampleAllowed C r f (visit i) then 1 else 0)

lemma average_path_entropy (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (T : ℕ) (hT:T ≤ Fintype.card (synthesis_Bits m₀)) :
    synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f T))=
      ∑i∈range T,synthesis_average (fun f:synthesis_Oracle m₀=>
        if synthesis_resampleAllowed C r f (visit i) then 1 else 0) := by
  induction T with
  | zero=>simp only [pathMass_initial_entropy,average_const,range_zero,sum_empty]
  | succ T ih=>
    rw [average_path_entropy_succ C r T (by omega),ih (by omega),sum_range_succ]

lemma resample_entropy_path (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_conditionalEntropy (synthesis_resample C r)=
      synthesis_average (fun f:synthesis_Oracle m₀=>
        FuchsVdGraaf.entropy (pathMass C r f (Fintype.card (synthesis_Bits m₀)))) := by
  unfold synthesis_conditionalEntropy
  congr 1
  funext f
  congr 1
  funext g
  unfold synthesis_resample
  rw [PMF.map_comp]
  convert uniform_map_real (fun coins:synthesis_Oracle m₀=>
    (synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))).1) g using 1 <;> first | rfl | simp only [pathMass]
  apply congrArg synthesis_average
  funext coins
  split_ifs <;> rfl

/-- Exact entropy of the same actual finite resampler used in the energy proof. -/
theorem resample_entropy_eq (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_conditionalEntropy (synthesis_resample C r)=
      ∑x:synthesis_Bits m₀,synthesis_average (fun f:synthesis_Oracle m₀=>
        if synthesis_resampleAllowed C r f x then 1 else 0) := by
  rw [resample_entropy_path,average_path_entropy C r _ (le_refl _),←Fin.sum_univ_eq_sum_range]
  have hv:∀i:Fin (Fintype.card (synthesis_Bits m₀)),visit i.val=synthesis_order m₀ i := by
    intro i
    simp only [visit,dif_pos i.isLt]
  simp_rw [hv]
  exact (synthesis_order m₀).sum_comp (fun x:synthesis_Bits m₀=>
    synthesis_average (fun f:synthesis_Oracle m₀=>if synthesis_resampleAllowed C r f x then 1 else 0))

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleScalarEnergy -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
variable {n m m₀ k : ℕ}

def scalarEnergy (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (a : synthesis_Oracle m₀→ℝ) : ℝ :=
  synthesis_average (fun f=>synthesis_average (fun coins:synthesis_Oracle m₀=>
    (a (synthesis_resamplePath C r f coins T).1-a f)^2))

def scalarStepEnergy (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (a : synthesis_Oracle m₀→ℝ) : ℝ :=
  synthesis_average (fun f=>synthesis_average (fun coins:synthesis_Oracle m₀=>
    (a (synthesis_resamplePath C r f coins (i+1)).1-a (synthesis_resamplePath C r f coins i).1)^2))

lemma euclidean_inner {α : Type} [Fintype α] (u v : EuclideanSpace ℝ α) :
    inner ℝ u v=∑x,u x*v x := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]
  apply sum_congr rfl
  intro x hx
  ring

lemma euclidean_norm_sq {α : Type} [Fintype α] (u : EuclideanSpace ℝ α) :
    ‖u‖^2=∑x,(u x)^2 := by rw [← real_inner_self_eq_norm_sq,euclidean_inner];simp only [pow_two]

lemma scalarEnergy_correlation (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (hT:T ≤ Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarEnergy C r T a=2*(synthesis_average (fun f=>a f^2)-
      synthesis_average (fun f=>a f*backwardApply C r T a f)) := by
  have he:∀f coins:synthesis_Oracle m₀,
      (a (synthesis_resamplePath C r f coins T).1-a f)^2=
      (a (synthesis_resamplePath C r f coins T).1)^2+(a f)^2-
        2*(a f*a (synthesis_resamplePath C r f coins T).1) := by intro f coins;ring
  unfold scalarEnergy
  simp_rw [he,average_sub,average_add,average_smul,average_const]
  rw [average_path_current C r T (fun f=>a f^2)]
  simp_rw [path_average_value C r _ T hT a]
  ring

lemma scalarEnergy_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (hT:T ≤ Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarEnergy C r T a=
      2/(Fintype.card (synthesis_Oracle m₀):ℝ)*
        inner ℝ (WithLp.toLp 2 a) (WithLp.toLp 2 a-projectionPath (coordinateProjection C r) (WithLp.toLp 2 a) T) := by
  let v:EuclideanSpace ℝ (synthesis_Oracle m₀):=WithLp.toLp 2 a
  have hd:inner ℝ v (projectionPath (coordinateProjection C r) v T)=inner ℝ v (backwardVector C r T v) := by
    rw [backwardVector_inner_dual,real_inner_comm]
  have hi:inner ℝ v (v-projectionPath (coordinateProjection C r) v T)=
      (∑f,a f^2)-(∑f,a f*backwardApply C r T a f) := by
    rw [inner_sub_right,hd,euclidean_inner,euclidean_inner]
    simp only [v,PiLp.toLp_apply,backwardVector_apply,pow_two]
  rw [scalarEnergy_correlation C r T hT a]
  change _=2/(Fintype.card (synthesis_Oracle m₀):ℝ)*inner ℝ v (v-projectionPath (coordinateProjection C r) v T)
  rw [hi]
  unfold synthesis_average
  ring

def oneStepCost (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) : ℝ :=
  ((a (step C r x f false)-a f)^2+(a (step C r x f true)-a f)^2)/2

lemma oneStepCost_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) :
    oneStepCost C r x a f=2*(a f-oneStepOp C r x a f)^2 := by
  unfold oneStepCost oneStepOp
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [step,if_pos ha]
    have hf:Function.update f x (f x)=f := Function.update_eq_self x f
    cases hfx:f x
    · have h0:Function.update f x false=f := by simpa only [hfx] using hf
      rw [h0]
      ring
    · have h1:Function.update f x true=f := by simpa only [hfx] using hf
      rw [h1]
      ring
  · simp only [step,if_neg ha]
    ring

lemma scalarStepEnergy_cost (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarStepEnergy C r i a=synthesis_average (oneStepCost C r (visit i) a) := by
  have hpoint:∀f coins:synthesis_Oracle m₀,
      (synthesis_resamplePath C r f coins (i+1)).1=
      step C r (synthesis_order m₀ ⟨i,hi⟩) (synthesis_resamplePath C r f coins i).1
        (coins (synthesis_order m₀ ⟨i,hi⟩)) := by
    intro f coins
    simp only [synthesis_resamplePath,dif_pos hi,step]
    split_ifs <;> rfl
  unfold scalarStepEnergy
  simp_rw [hpoint]
  have he:∀f:synthesis_Oracle m₀,
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        (a (step C r (synthesis_order m₀ ⟨i,hi⟩) (synthesis_resamplePath C r f coins i).1
          (coins (synthesis_order m₀ ⟨i,hi⟩)))-a (synthesis_resamplePath C r f coins i).1)^2)=
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        oneStepCost C r (visit i) a (synthesis_resamplePath C r f coins i).1) := by
    intro f
    exact (average_fresh_bit C r f i hi (fun prev b=>
      (a (step C r (synthesis_order m₀ ⟨i,hi⟩) prev.1 b)-a prev.1)^2)).trans
      (by simp only [oneStepCost,visit,dif_pos hi])
  simp_rw [he]
  exact average_path_current C r i (oneStepCost C r (visit i) a)

lemma scalarStepEnergy_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarStepEnergy C r i a=2/(Fintype.card (synthesis_Oracle m₀):ℝ)*
      ‖WithLp.toLp 2 a-coordinateProjection C r i (WithLp.toLp 2 a)‖^2 := by
  rw [scalarStepEnergy_cost C r i hi a]
  unfold synthesis_average
  simp_rw [oneStepCost_projection]
  rw [euclidean_norm_sq]
  simp only [PiLp.sub_apply,PiLp.toLp_apply,coordinateProjection_apply]
  rw [← mul_sum]
  ring

/-- The complete scalar version for the actual adaptive procedure.
The only normalization is uniform finite expectation. -/
theorem scalar_resampling_energy (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (hT:T ≤ Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarEnergy C r T a  ≤  2*(∑i∈range T,scalarStepEnergy C r i a) := by
  let v:EuclideanSpace ℝ (synthesis_Oracle m₀):=WithLp.toLp 2 a
  have hh:=projection_product_energy (coordinateProjection C r) v T
    (fun i hi=>coordinateProjection_symm C r i) (fun i hi=>coordinateProjection_idempotent C r i)
  have hfactor:0 ≤ 2/(Fintype.card (synthesis_Oracle m₀):ℝ) := by positivity
  have hm:=mul_le_mul_of_nonneg_left hh hfactor
  have he:(∑i∈range T,scalarStepEnergy C r i a)=
      2/(Fintype.card (synthesis_Oracle m₀):ℝ)*(∑i∈range T,‖v-coordinateProjection C r i v‖^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    exact scalarStepEnergy_projection C r i (by have h:=mem_range.mp hi;omega) a
  rw [he,scalarEnergy_projection C r T hT a]
  dsimp only [v] at hm
  nlinarith

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEnergy -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate

lemma frob_sq_sub_components {α β : Type} [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    QAlgorithms.frobNorm (A-B)^2=
      ∑i,∑j,(((A i j).re-(B i j).re)^2+((A i j).im-(B i j).im)^2) := by
  rw [InfluenceProof.frob_sq_entries]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Matrix.sub_apply,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

lemma frob_sq_sub_comm {α β : Type} [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    QAlgorithms.frobNorm (A-B)^2=QAlgorithms.frobNorm (B-A)^2 := by
  rw [frob_sq_sub_components,frob_sq_sub_components]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

variable {n m m₀ k : ℕ}

lemma energy_components (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_energy C (synthesis_resample C r)=
      ∑i,∑j,(scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).re)+
        scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).im)) := by
  rw [energy_eq_path]
  have he:∀f coins:synthesis_Oracle m₀,QAlgorithms.frobNorm (synthesis_A C f-
      synthesis_A C (synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))).1)^2=
      QAlgorithms.frobNorm (synthesis_A C (synthesis_resamplePath C r f coins
        (Fintype.card (synthesis_Bits m₀))).1-synthesis_A C f)^2 :=
    fun f coins=>frob_sq_sub_comm _ _
  simp_rw [he,frob_sq_sub_components,average_sum,average_add]
  rfl

lemma stepEnergy_components (C : synthesis_Circuit n m m₀ k) (r : ℝ) (t : ℕ) :
    synthesis_stepEnergy C r t=
      ∑i,∑j,(scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).re)+
        scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).im)) := by
  unfold synthesis_stepEnergy
  simp_rw [frob_sq_sub_components,average_sum,average_add]
  rfl

lemma triple_sum_comm {α β : Type} [Fintype α] [Fintype β] (T : ℕ) (F : α→β→ℕ→ℝ) :
    (∑i,∑j,∑t∈range T,F i j t)=∑t∈range T,∑i,∑j,F i j t := by
  calc
    _ = ∑i,∑t∈range T,∑j,F i j t := by
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ = _ := sum_comm

/-- Exact public Lemma4.9. The scalar argument derives all conditional
averages, reversibility and stationarity for the published finite path. -/
theorem synthesis_resampling_energy (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (hr:0<r) (hr1:r ≤ 1) :
    synthesis_energy C (synthesis_resample C r)  ≤ 
      2*∑i:Fin (Fintype.card (synthesis_Bits m₀)),synthesis_stepEnergy C r i.val := by
  rw [energy_components,Fin.sum_univ_eq_sum_range]
  have he:∀i j,
      scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).re)+
        scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).im)  ≤ 
      2*∑t∈range (Fintype.card (synthesis_Bits m₀)),
        (scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).re)+
          scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).im)) := by
    intro i j
    have hRe:=scalar_resampling_energy C r (Fintype.card (synthesis_Bits m₀)) (le_refl _)
      (fun f=>(synthesis_A C f i j).re)
    have hIm:=scalar_resampling_energy C r (Fintype.card (synthesis_Bits m₀)) (le_refl _)
      (fun f=>(synthesis_A C f i j).im)
    rw [sum_add_distrib,mul_add]
    exact add_le_add hRe hIm
  have hs:=sum_le_sum (fun i (_:i∈(univ:Finset (synthesis_Bits n)))=>
    sum_le_sum (fun j (_:j∈(univ:Finset (synthesis_Bits n)))=>he i j))
  calc
    _  ≤  ∑i,∑j,2*∑t∈range (Fintype.card (synthesis_Bits m₀)),
      (scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).re)+
        scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).im)) := hs
    _ = 2*∑t∈range (Fintype.card (synthesis_Bits m₀)),synthesis_stepEnergy C r t := by
      simp_rw [← mul_sum]
      congr 1
      rw [triple_sum_comm]
      simp only [stepEnergy_components]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEnergyBound -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma threshold_nonneg (k : ℕ) (r : ℝ) : 0 ≤ synthesis_threshold k r := by
  unfold synthesis_threshold
  split_ifs <;> positivity

lemma oneStepCost_flip (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) :
    oneStepCost C r x a f=if synthesis_resampleAllowed C r f x then
      (a (synthesis_flip f x)-a f)^2/2 else 0 := by
  rw [oneStepCost_projection,forced_pair_sum]
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [lazyFlip,if_pos ha]
    ring
  · simp only [lazyFlip,if_neg ha]
    ring

lemma stepEnergy_allowed (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) :
    synthesis_stepEnergy C r i=synthesis_average (fun f:synthesis_Oracle m₀=>
      if synthesis_resampleAllowed C r f (visit i) then
        QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f (visit i))-synthesis_A C f)^2/2 else 0) := by
  have hp : ∀ f : synthesis_Oracle m₀,
      (∑a,∑b,(oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).re) f+
        oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).im) f))=
      if synthesis_resampleAllowed C r f (visit i) then
        QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f (visit i))-synthesis_A C f)^2/2 else 0 := by
    intro f
    simp_rw [oneStepCost_flip]
    by_cases ha:synthesis_resampleAllowed C r f (visit i)
    · simp only [if_pos ha]
      rw [frob_sq_sub_components]
      simp only [sum_div,add_div]
    · simp only [if_neg ha,zero_add,sum_const_zero]
  rw [stepEnergy_components]
  simp_rw [scalarStepEnergy_cost C r i hi]
  calc
    _ = synthesis_average (fun f:synthesis_Oracle m₀=>
        ∑a,∑b,(oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).re) f+
          oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).im) f)) := by
      simp only [average_sum,average_add]
    _ = _ := congrArg synthesis_average (funext hp)

lemma allowed_influences (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) (ha:synthesis_resampleAllowed C r f x) :
    synthesis_influence C f x ≤ synthesis_threshold k r ∧
      synthesis_influence C (synthesis_flip f x) x ≤ synthesis_threshold k r := by
  have hf:Function.update f x (f x)=f := Function.update_eq_self x f
  cases hfx:f x
  · have h0:Function.update f x false=f := by simpa only [hfx] using hf
    exact ⟨by simpa only [h0] using ha.1,by simpa only [synthesis_flip,hfx,Bool.not_false] using ha.2⟩
  · have h1:Function.update f x true=f := by simpa only [hfx] using hf
    exact ⟨by simpa only [h1] using ha.2,by simpa only [synthesis_flip,hfx,Bool.not_true] using ha.1⟩

lemma stepEnergy_influence (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) :
    synthesis_stepEnergy C r i ≤ 2*synthesis_threshold k r*
      synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f (visit i)) := by
  rw [stepEnergy_allowed C r i hi]
  have hp:∀f:synthesis_Oracle m₀,
      (if synthesis_resampleAllowed C r f (visit i) then
        QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f (visit i))-synthesis_A C f)^2/2 else 0) ≤ 
      2*synthesis_threshold k r*synthesis_influence C (synthesis_flip f (visit i)) (visit i) := by
    intro f
    have hw:=InfluenceProof.influence_nonneg C (synthesis_flip f (visit i)) (visit i)
    by_cases ha:synthesis_resampleAllowed C r f (visit i)
    · rw [if_pos ha]
      have hh:=InfluenceProof.synthesis_one_bit_perturbation C f (visit i)
      have hf:=(allowed_influences C r f (visit i) ha).1
      nlinarith [mul_le_mul_of_nonneg_right hf hw]
    · rw [if_neg ha]
      exact mul_nonneg (mul_nonneg (by norm_num) (threshold_nonneg k r)) hw
  have hh:=average_mono _ _ hp
  rw [average_smul] at hh
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive (visit i)).toPerm
  have he:synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C (synthesis_flip f (visit i)) (visit i))=
      synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f (visit i)) := by
    have he':=average_comp e (fun f=>synthesis_influence C f (visit i))
    change synthesis_average (fun f:synthesis_Oracle m₀=>
      synthesis_influence C (synthesis_flip f (visit i)) (visit i))=_ at he'
    exact he' 
  rwa [he] at hh

theorem sum_stepEnergy_bound (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    (∑i:Fin (Fintype.card (synthesis_Bits m₀)),synthesis_stepEnergy C r i.val)  ≤ 
      4*synthesis_threshold k r*(k:ℝ)*(2:ℝ)^n := by
  have hh:=sum_le_sum (fun i (_:i∈(univ:Finset (Fin (Fintype.card (synthesis_Bits m₀)))))=>
    stepEnergy_influence C r i.val i.isLt)
  have hv:∀i:Fin (Fintype.card (synthesis_Bits m₀)),visit i.val=synthesis_order m₀ i := by
    intro i
    simp only [visit,dif_pos i.isLt]
  simp_rw [hv] at hh
  rw [← mul_sum,← average_sum] at hh
  have htot:∀f:synthesis_Oracle m₀,(∑i:Fin (Fintype.card (synthesis_Bits m₀)),
      synthesis_influence C f (synthesis_order m₀ i))=2*(k:ℝ)*(2:ℝ)^n := by
    intro f
    rw [(synthesis_order m₀).sum_comp,InfluenceProof.synthesis_total_influence]
  simp only [htot,average_const] at hh
  convert hh using 1 <;> first | rfl | ring

/-- Energy half of Theorem4.5, for the same actual resampler to be used
in the entropy half. The k=0 threshold is handled without division by zero. -/
theorem resample_energy_bound (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr:0<r) (hr1:r ≤ 1) :
    synthesis_energy C (synthesis_resample C r)  ≤  2*(2:ℝ)^n*r^2 := by
  have hE:=synthesis_resampling_energy C r hr hr1
  have hS:=sum_stepEnergy_bound C r
  have hτ:8*synthesis_threshold k r*(k:ℝ) ≤ r^2 := by
    by_cases hk:k=0
    · simp only [hk,Nat.cast_zero,mul_zero]
      exact sq_nonneg r
    · have hkR:(k:ℝ)≠0 := by exact_mod_cast hk
      unfold synthesis_threshold
      rw [if_neg hk]
      field_simp
      ring_nf
      exact le_rfl
  have hN:0 ≤ (2:ℝ)^n := pow_nonneg (by norm_num) n
  have hmul:=mul_le_mul_of_nonneg_right hτ hN
  nlinarith [mul_nonneg hN (sq_nonneg r)]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEntropyBound -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset Classical
variable {n m m₀ k : ℕ}

lemma allowed_iff_influences (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    synthesis_resampleAllowed C r f x ↔ synthesis_influence C f x ≤ synthesis_threshold k r ∧
      synthesis_influence C (synthesis_flip f x) x ≤ synthesis_threshold k r := by
  constructor
  · exact allowed_influences C r f x
  · intro ha
    have hf:Function.update f x (f x)=f := Function.update_eq_self x f
    cases hfx:f x
    · have h0:Function.update f x false=f := by simpa only [hfx] using hf
      refine ⟨?_,?_⟩
      · simpa only [h0] using ha.1
      · simpa only [synthesis_flip,hfx,Bool.not_false] using ha.2
    · have h1:Function.update f x true=f := by simpa only [hfx] using hf
      refine ⟨?_,?_⟩
      · simpa only [synthesis_flip,hfx,Bool.not_true] using ha.2
      · simpa only [h1] using ha.1

lemma rejection_influence (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    synthesis_threshold k r*(1-(if synthesis_resampleAllowed C r f x then 1 else 0)) ≤
      synthesis_influence C f x+synthesis_influence C (synthesis_flip f x) x := by
  have h0:=InfluenceProof.influence_nonneg C f x
  have h1:=InfluenceProof.influence_nonneg C (synthesis_flip f x) x
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [if_pos ha,sub_self,mul_zero]
    exact add_nonneg h0 h1
  · simp only [if_neg ha,sub_zero,mul_one]
    rw [allowed_iff_influences] at ha
    by_cases hf:synthesis_influence C f x ≤ synthesis_threshold k r
    · have hg:¬synthesis_influence C (synthesis_flip f x) x ≤ synthesis_threshold k r := fun hh=>ha ⟨hf,hh⟩
      linarith
    · linarith

lemma average_flip_influence (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀) :
    synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C (synthesis_flip f x) x)=
      synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f x) := by
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive x).toPerm
  have he:=average_comp e (fun f:synthesis_Oracle m₀=>synthesis_influence C f x)
  change synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C (synthesis_flip f x) x)=_ at he
  exact he

lemma threshold_entropy_deficit (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_threshold k r*((2:ℝ)^m₀-synthesis_conditionalEntropy (synthesis_resample C r)) ≤
      4*(k:ℝ)*(2:ℝ)^n := by
  have hx:∀x:synthesis_Bits m₀,synthesis_threshold k r*
      (1-synthesis_average (fun f:synthesis_Oracle m₀=>if synthesis_resampleAllowed C r f x then 1 else 0)) ≤
      2*synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f x) := by
    intro x
    have hh:=average_mono _ _ (fun f:synthesis_Oracle m₀=>rejection_influence C r f x)
    rw [average_smul,average_sub,average_const,average_add,average_flip_influence] at hh
    linarith
  have hh:=sum_le_sum (fun x (_:x∈(univ:Finset (synthesis_Bits m₀)))=>hx x)
  rw [←mul_sum,sum_sub_distrib,←mul_sum] at hh
  have htot:∀f:synthesis_Oracle m₀,(∑x:synthesis_Bits m₀,synthesis_influence C f x)=2*(k:ℝ)*(2:ℝ)^n :=
    fun f=>InfluenceProof.synthesis_total_influence C f
  have hw:(∑x:synthesis_Bits m₀,synthesis_average (fun f:synthesis_Oracle m₀=>
      synthesis_influence C f x))=2*(k:ℝ)*(2:ℝ)^n := by
    rw [←average_sum]
    simp only [htot,average_const]
  rw [hw] at hh
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hh
  have hc:(Fintype.card (synthesis_Bits m₀):ℝ)=(2:ℝ)^m₀ := by
    simp [synthesis_Bits,DirectFidelity.State.Q,Fintype.card_fun]
  rw [hc,←resample_entropy_eq] at hh
  convert hh using 1 <;> first | rfl | ring

theorem resample_entropy_bound (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr:0<r) :
    (2:ℝ)^m₀-32*(k:ℝ)^2*(2:ℝ)^n/r^2 ≤
      synthesis_conditionalEntropy (synthesis_resample C r) := by
  by_cases hk:k=0
  · subst k
    have ha:∀x:synthesis_Bits m₀,∀f:synthesis_Oracle m₀,synthesis_resampleAllowed C r f x := by
      intro x f
      simp [synthesis_resampleAllowed,synthesis_influence,synthesis_threshold]
    rw [resample_entropy_eq]
    simp [ha,average_const,synthesis_Bits,DirectFidelity.State.Q]
  · have hkR:0<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hτ:0<synthesis_threshold k r := by
      simp only [synthesis_threshold,if_neg hk]
      positivity
    have hd: (2:ℝ)^m₀-synthesis_conditionalEntropy (synthesis_resample C r) ≤
        4*(k:ℝ)*(2:ℝ)^n/synthesis_threshold k r := by
      apply (le_div_iff₀ hτ).mpr
      simpa only [mul_comm] using threshold_entropy_deficit C r
    have he:4*(k:ℝ)*(2:ℝ)^n/synthesis_threshold k r=32*(k:ℝ)^2*(2:ℝ)^n/r^2 := by
      simp only [synthesis_threshold,if_neg hk]
      field_simp [ne_of_gt hr,ne_of_gt hkR]
      <;> ring
    rw [he] at hd
    linarith

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleEntropyResamplingMain -/

set_option autoImplicit false
noncomputable section
namespace RandomOracleUnitarySynthesis

/-- The exact public Theorem 4.5: both conclusions use the concrete
published path and the same finite PMF kernel, including zero queries. -/
theorem synthesis_entropy_resampling {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ K : synthesis_Resampler m₀,
      (2 : ℝ)^m₀ - 32 * (k : ℝ)^2 * (2 : ℝ)^n / r^2 ≤ synthesis_conditionalEntropy K ∧
      synthesis_energy C K ≤ 2 * (2 : ℝ)^n * r^2 := by
  exact ⟨synthesis_resample C r,ResamplingProof.resample_entropy_bound C r hr,
    ResamplingProof.resample_energy_bound C r hr hr1⟩

end RandomOracleUnitarySynthesis

/- Module RandomOracleFiniteGibbs -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Finset Classical
open scoped ENNReal

lemma pmf_real_sum {α : Type} [Fintype α] (p : PMF α) : (∑a,(p a).toReal)=1 := by
  rw [← ENNReal.toReal_sum (fun a _=>p.apply_ne_top a)]
  have hs:(∑a,p a)=(1:ℝ≥0∞) := by simpa only [tsum_fintype] using p.tsum_coe
  rw [hs,ENNReal.toReal_one]

lemma weighted_log_ratio_le (p q : ℝ) (hp:0 ≤ p) (hq:0<q) :
    p*(Real.log q-Real.log p) ≤ q-p := by
  by_cases hz:p=0
  · simp only [hz,zero_mul,sub_zero]
    exact hq.le
  · have hp':0<p := lt_of_le_of_ne hp (Ne.symm hz)
    have he:=mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq hp')) hp
    rw [Real.log_div hq.ne' hz] at he
    have hv:p*(q/p-1)=q-p := by field_simp
    rwa [hv] at he

/-- Finite Gibbs inequality against a positive subprobability reference. -/
theorem finite_gibbs {α : Type} [Fintype α] (p q : α→ℝ)
    (hp:∀a,0 ≤ p a) (hs:(∑a,p a)=1) (hq:∀a,0<q a) (ht:(∑a,q a) ≤ 1) :
    FuchsVdGraaf.entropy p ≤ -(∑a,p a*Real.logb 2 (q a)) := by
  have hh:=sum_le_sum (fun a (_:a∈(univ:Finset α))=>weighted_log_ratio_le (p a) (q a) (hp a) (hq a))
  simp only [mul_sub,sum_sub_distrib,hs] at hh
  have hl:(∑a,p a*Real.log (q a)) ≤ ∑a,p a*Real.log (p a) := by linarith
  have hd:=div_le_div_of_nonneg_right hl (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  unfold FuchsVdGraaf.entropy
  simp only [Real.logb,←mul_div_assoc,←sum_div]
  linarith

lemma entropy_le_log_card {α : Type} [Fintype α] [Nonempty α]
    (p : α→ℝ) (hp:∀a,0 ≤ p a) (hs:(∑a,p a)=1) :
    FuchsVdGraaf.entropy p ≤ Real.logb 2 (Fintype.card α:ℝ) := by
  have hc:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hh:=finite_gibbs p (fun _=>1/(Fintype.card α:ℝ)) hp hs
    (fun _=>div_pos zero_lt_one hc) (by simp [mul_div_cancel₀ _ hc.ne'])
  have hl:Real.logb 2 (1/(Fintype.card α:ℝ))= -Real.logb 2 (Fintype.card α:ℝ) := by
    rw [Real.logb_div one_ne_zero hc.ne',Real.logb_one]
    ring
  simpa only [hl,←sum_mul,hs,one_mul,neg_neg] using hh

/-- Small-set entropy bound, without assuming a chain rule or importing an
unproved entropy theorem. The set may be empty and zero masses are allowed. -/
theorem small_set_entropy {α : Type} [Fintype α] [Nonempty α]
    (p : α→ℝ) (hp:∀a,0 ≤ p a) (hs:(∑a,p a)=1) (S : Finset α) (L : ℝ)
    (hS:(S.card:ℝ)*Real.exp (L*Real.log 2) ≤ (Fintype.card α:ℝ)) :
    FuchsVdGraaf.entropy p+L*(∑a∈S,p a) ≤ Real.logb 2 (Fintype.card α:ℝ)+1 := by
  let N:ℝ:=Fintype.card α
  have hN:0<N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let e:ℝ:=Real.exp (L*Real.log 2)
  let q:α→ℝ:=fun a=>(if a∈S then e else 1)/(2*N)
  have hq:∀a,0<q a := by
    intro a
    dsimp [q]
    split_ifs <;> positivity
  have hqsum:(∑a,q a) ≤ 1 := by
    have hh:(∑a:α,if a∈S then e else 1) ≤ (S.card:ℝ)*e+N := by
      calc
        _ ≤ ∑a:α,((if a∈S then e else 0)+1) := by
          apply sum_le_sum
          intro a ha
          split_ifs <;> linarith
        _ = _ := by simp [sum_add_distrib,N]
    have he:(S.card:ℝ)*e ≤ N := hS
    dsimp only [q]
    rw [←sum_div]
    apply (div_le_one (by positivity : (0:ℝ)<2*N)).mpr
    linarith
  have hg:=finite_gibbs p q hp hs hq hqsum
  have hlog:∀a:α,Real.logb 2 (q a)=
      (if a∈S then L else 0)-(1+Real.logb 2 N) := by
    intro a
    dsimp only [q]
    rw [Real.logb_div (by split_ifs <;> positivity) (by positivity)]
    rw [Real.logb_mul (by norm_num : (2:ℝ)≠0) hN.ne',Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    split_ifs
    · dsimp only [e]
      rw [Real.logb,Real.log_exp]
      field_simp
    · rw [Real.logb_one]
  have hsum:(∑a,p a*Real.logb 2 (q a))=L*(∑a∈S,p a)-(1+Real.logb 2 N) := by
    simp_rw [hlog,mul_sub,mul_ite,mul_zero]
    rw [sum_sub_distrib,←sum_mul,hs,one_mul]
    congr 1
    simp [mul_comm,←mul_sum]
  rw [hsum] at hg
  change FuchsVdGraaf.entropy p+L*(∑a∈S,p a) ≤ Real.logb 2 N+1
  linarith

end RandomOracleUnitarySynthesis.NetProof

/- Module RandomOracleEntropyNeighborhoods -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Finset Classical ResamplingProof

def neighborhood {α : Type} [Fintype α] (R : α→α→Prop) (f : α) : Finset α :=
  univ.filter (R f)

def smallNeighborhood {α : Type} [Fintype α] (R : α→α→Prop) (L : ℝ) (f : α) : Prop :=
  ((neighborhood R f).card:ℝ)*Real.exp (L*Real.log 2) ≤ (Fintype.card α:ℝ)

/-- Entropy deficit and mean cost control the uniform mass of small
neighborhoods. All expectations and all probability laws are finite sums. -/
theorem small_neighborhood_mass {α : Type} [Fintype α] [Nonempty α]
    (p : α→α→ℝ) (hp:∀f g,0 ≤ p f g) (hs:∀f,(∑g,p f g)=1)
    (R : α→α→Prop) (D : α→α→ℝ) (hD:∀f g,0 ≤ D f g)
    (a : ℝ) (ha:0<a) (hfar:∀f g,¬R f g→a ≤ D f g)
    (b E L : ℝ) (hL:0<L)
    (hH:Real.logb 2 (Fintype.card α:ℝ)-b ≤ synthesis_average (fun f=>FuchsVdGraaf.entropy (p f)))
    (hE:synthesis_average (fun f=>∑g,p f g*D f g) ≤ E) :
    synthesis_average (fun f:α=>if smallNeighborhood R L f then 1 else 0) ≤ (b+1)/L+E/a := by
  let S:α→Finset α:=fun f=>if smallNeighborhood R L f then neighborhood R f else ∅
  let mass:α→ℝ:=fun f=>∑g∈S f,p f g
  have hScard:∀f,((S f).card:ℝ)*Real.exp (L*Real.log 2) ≤ (Fintype.card α:ℝ) := by
    intro f
    dsimp only [S]
    split_ifs with hf
    · exact hf
    · simp
  have hpoint:∀f:α,FuchsVdGraaf.entropy (p f)+L*mass f ≤
      Real.logb 2 (Fintype.card α:ℝ)+1 := by
    intro f
    exact small_set_entropy (p f) (hp f) (hs f) (S f) L (hScard f)
  have hmass:synthesis_average mass ≤ (b+1)/L := by
    have hh:=average_mono _ _ hpoint
    rw [average_add,average_smul,average_const] at hh
    apply (le_div_iff₀ hL).mpr
    nlinarith
  have hprob:∀f:α,(if smallNeighborhood R L f then (1:ℝ) else 0) ≤
      mass f+(∑g,p f g*D f g)/a := by
    intro f
    by_cases hf:smallNeighborhood R L f
    · rw [if_pos hf]
      have hm:mass f=∑g:α,if R f g then p f g else 0 := by
        simp only [mass,S,if_pos hf,neighborhood,sum_filter]
      rw [hm]
      have hg:∀g:α,p f g ≤ (if R f g then p f g else 0)+p f g*D f g/a := by
        intro g
        by_cases hr:R f g
        · rw [if_pos hr]
          exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (hp f g) (hD f g)) ha.le)
        · rw [if_neg hr,zero_add]
          apply (le_div_iff₀ ha).mpr
          exact mul_le_mul_of_nonneg_left (hfar f g hr) (hp f g)
      have hh:=sum_le_sum (fun g (_:g∈(univ:Finset α))=>hg g)
      rwa [hs f,sum_add_distrib,←sum_div] at hh
    · rw [if_neg hf]
      have hm:mass f=0 := by simp only [mass,S,if_neg hf,sum_empty]
      rw [hm,zero_add]
      exact div_nonneg (sum_nonneg (fun g _=>mul_nonneg (hp f g) (hD f g))) ha.le
  have hh:=average_mono _ _ hprob
  rw [average_add,average_div] at hh
  have he:=div_le_div_of_nonneg_right hE ha.le
  linarith

lemma neighborhood_density {α : Type} [Fintype α] [Nonempty α]
    (R : α→α→Prop) (L : ℝ) (f : α) (hf:¬smallNeighborhood R L f) :
    Real.exp (-L*Real.log 2) ≤ synthesis_average (fun g:α=>if R f g then 1 else 0) := by
  have hN:0<(Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard:(Fintype.card α:ℝ)<((neighborhood R f).card:ℝ)*Real.exp (L*Real.log 2) :=
    lt_of_not_ge hf
  have he:0<Real.exp (L*Real.log 2) := Real.exp_pos _
  have hexp:Real.exp (-L*Real.log 2)=1/Real.exp (L*Real.log 2) := by
    rw [neg_mul,Real.exp_neg,one_div]
  rw [hexp]
  have hd:(1:ℝ)/Real.exp (L*Real.log 2) ≤ ((neighborhood R f).card:ℝ)/(Fintype.card α:ℝ) := by
    apply (div_le_div_iff₀ he hN).mpr
    simpa only [one_mul] using hcard.le
  have hc:(∑g:α,if R f g then (1:ℝ) else 0)=((neighborhood R f).card:ℝ) := by
    simp [neighborhood]
  simpa only [synthesis_average,hc] using hd

end RandomOracleUnitarySynthesis.NetProof

/- Module RandomOracleNetProbability -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Matrix Finset Classical ResamplingProof
variable {n m m₀ k : ℕ}

lemma oracle_log_card (m₀ : ℕ) : Real.logb 2 (Fintype.card (synthesis_Oracle m₀):ℝ)=(2:ℝ)^m₀ := by
  have hc:(Fintype.card (synthesis_Oracle m₀):ℝ)=(2:ℝ)^(Fintype.card (synthesis_Bits m₀)) := by
    simp [synthesis_Oracle]
  rw [hc,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one]
  simp [synthesis_Bits,DirectFidelity.State.Q]

lemma marginal_energy (C : synthesis_Circuit n m m₀ k) (K : synthesis_Resampler m₀) :
    synthesis_energy C K=synthesis_average (fun f:synthesis_Oracle m₀=>
      ∑g:synthesis_Oracle m₀,(((K f).map Prod.snd) g).toReal*
        QAlgorithms.frobNorm (synthesis_A C f-synthesis_A C g)^2) := by
  unfold synthesis_energy
  apply congrArg synthesis_average
  funext f
  exact (mean_map (K f) Prod.snd (fun g:synthesis_Oracle m₀=>
    QAlgorithms.frobNorm (synthesis_A C f-synthesis_A C g)^2)).symm

/-- The exact metric ball, with centers among the original compressed circuits. -/
def near (C : synthesis_Circuit n m m₀ k) (d : ℝ)
    (f g : synthesis_Oracle m₀) : Prop :=
  QAlgorithms.frobNorm (synthesis_A C g-synthesis_A C f) ≤ d*Real.sqrt ((2:ℝ)^n)

lemma oracle_small_neighborhood (C : synthesis_Circuit n m m₀ k)
    (d : ℝ) (hd:0<d) (r : ℝ) (hr:0<r) (hr1:r ≤ 1) (L : ℝ) (hL:0<L) :
    synthesis_average (fun f:synthesis_Oracle m₀=>if smallNeighborhood (near C d) L f then 1 else 0) ≤
      (32*(k:ℝ)^2*(2:ℝ)^n/r^2+1)/L+(2*(2:ℝ)^n*r^2)/(d^2*(2:ℝ)^n) := by
  obtain ⟨K,hH,hE⟩:=synthesis_entropy_resampling C r hr hr1
  let p:synthesis_Oracle m₀→synthesis_Oracle m₀→ℝ:=fun f g=>(((K f).map Prod.snd) g).toReal
  let D:synthesis_Oracle m₀→synthesis_Oracle m₀→ℝ:=fun f g=>
    QAlgorithms.frobNorm (synthesis_A C f-synthesis_A C g)^2
  have hp:∀f g,0 ≤ p f g := fun f g=>ENNReal.toReal_nonneg
  have hs:∀f,(∑g,p f g)=1 := fun f=>pmf_real_sum ((K f).map Prod.snd)
  have hN:0<(2:ℝ)^n := pow_pos (by norm_num) _
  have hfar:∀f g,¬near C d f g→d^2*(2:ℝ)^n ≤ D f g := by
    intro f g hfg
    have hf:d*Real.sqrt ((2:ℝ)^n) ≤ QAlgorithms.frobNorm (synthesis_A C g-synthesis_A C f) :=
      (lt_of_not_ge hfg).le
    have hpos:0 ≤ d*Real.sqrt ((2:ℝ)^n) := mul_nonneg hd.le (Real.sqrt_nonneg _)
    have hh:= (sq_le_sq₀ hpos (InfluenceProof.frob_nonneg _)).mpr hf
    rw [mul_pow,Real.sq_sqrt hN.le] at hh
    dsimp only [D]
    rwa [frob_sq_sub_comm] 
  have he:synthesis_average (fun f:synthesis_Oracle m₀=>∑g,p f g*D f g) ≤ 2*(2:ℝ)^n*r^2 := by
    rw [marginal_energy] at hE
    exact hE
  have hh:Real.logb 2 (Fintype.card (synthesis_Oracle m₀):ℝ)-32*(k:ℝ)^2*(2:ℝ)^n/r^2 ≤
      synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (p f)) := by
    rw [oracle_log_card]
    exact hH
  exact small_neighborhood_mass p hp hs (near C d) D (fun _ _=>sq_nonneg _) (d^2*(2:ℝ)^n)
    (by positivity) hfar (32*(k:ℝ)^2*(2:ℝ)^n/r^2) (2*(2:ℝ)^n*r^2) L hL hh he

end RandomOracleUnitarySynthesis.NetProof

/- Module RandomOracleFiniteCover -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Finset Classical
open ResamplingProof

lemma average_comm {α β : Type} [Fintype α] [Fintype β] (F : α→β→ℝ) :
    synthesis_average (fun a=>synthesis_average (F a))=
      synthesis_average (fun b=>synthesis_average (fun a=>F a b)) := by
  unfold synthesis_average
  simp_rw [←sum_div]
  rw [sum_comm]
  ring

lemma exists_le_average {α : Type} [Fintype α] [Nonempty α] (f : α→ℝ) :
    ∃a,f a ≤ synthesis_average f := by
  have hc:(Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have he:(∑a,f a)=(∑_:α,synthesis_average f) := by
    simp only [synthesis_average,sum_const,card_univ,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hc]
  obtain ⟨a,ha,hv⟩:=exists_le_of_sum_le (univ_nonempty (α:=α)) he.le
  exact ⟨a,hv⟩

def uncovered {α : Type} (R : α→α→Prop) (G : α→Prop) (T : Finset α) (a : α) : ℝ :=
  if G a ∧ ∀b∈T,¬R a b then 1 else 0

lemma uncovered_insert {α : Type} (R : α→α→Prop) (G : α→Prop)
    (T : Finset α) (b a : α) : uncovered R G (insert b T) a=
      uncovered R G T a*(if R a b then 0 else 1) := by
  simp only [uncovered,forall_mem_insert]
  by_cases hg:G a <;> by_cases ht:∀c∈T,¬R a c <;> by_cases hr:R a b <;>
    simp [hg,ht,hr]

lemma uncovered_step_average {α : Type} [Fintype α] [Nonempty α]
    (R : α→α→Prop) (G : α→Prop) (T : Finset α) :
    synthesis_average (fun b:α=>synthesis_average (uncovered R G (insert b T)))=
      synthesis_average (fun a:α=>uncovered R G T a*
        (1-synthesis_average (fun b:α=>if R a b then 1 else 0))) := by
  rw [average_comm]
  congr 1
  funext a
  simp only [uncovered_insert,average_smul]
  congr 1
  have he:(fun b:α=>(if R a b then (0:ℝ) else 1))=
      (fun b:α=>1-(if R a b then 1 else 0)) := by
    funext b
    split_ifs <;> norm_num
  rw [he,average_sub,average_const]

/-- A finite greedy covering proof; every chosen center belongs to the original
finite domain, so additional properties of the centers can be retained. -/
theorem finite_greedy_cover {α : Type} [Fintype α] [Nonempty α]
    (R : α→α→Prop) (G : α→Prop) (q : ℝ) (hq0:0 ≤ q) (hq1:q ≤ 1)
    (hdeg:∀a,G a→q ≤ synthesis_average (fun b:α=>if R a b then 1 else 0)) (K : ℕ) :
    ∃T:Finset α,T.card ≤ K ∧ (0<K→T.Nonempty) ∧
      synthesis_average (uncovered R G T) ≤ (1-q)^K := by
  induction K with
  | zero=>
    refine ⟨∅,by simp,by simp,?_⟩
    rw [pow_zero]
    calc
      _ ≤ synthesis_average (fun _:α=>(1:ℝ)) := average_mono _ _ (by
        intro a
        unfold uncovered
        split_ifs <;> norm_num)
      _ = 1 := average_const _
  | succ K ih=>
    obtain ⟨T,hcard,hne,hcover⟩:=ih
    have hstep:synthesis_average (fun b:α=>synthesis_average (uncovered R G (insert b T))) ≤
        (1-q)*synthesis_average (uncovered R G T) := by
      rw [uncovered_step_average]
      calc
        _ ≤ synthesis_average (fun a:α=>(1-q)*uncovered R G T a) := by
          apply average_mono
          intro a
          by_cases hg:G a ∧ ∀b∈T,¬R a b
          · have hd:=hdeg a hg.1
            simp only [uncovered,if_pos hg,mul_one,one_mul]
            linarith
          · simp only [uncovered,if_neg hg,mul_zero,zero_mul,le_refl]
        _ = _ := average_smul _ _
    obtain ⟨b,hb⟩:=exists_le_average (fun b:α=>synthesis_average (uncovered R G (insert b T)))
    refine ⟨insert b T,le_trans (card_insert_le b T) (Nat.succ_le_succ hcard),?_,?_⟩
    · intro h
      exact ⟨b,mem_insert_self b T⟩
    · calc
        _ ≤ (1-q)*synthesis_average (uncovered R G T) := hb.trans hstep
        _ ≤ (1-q)*(1-q)^K := mul_le_mul_of_nonneg_left hcover (sub_nonneg.mpr hq1)
        _ = (1-q)^(K+1) := by rw [pow_succ]; ring

end RandomOracleUnitarySynthesis.NetProof

/- Module RandomOracleCoverParameters -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof
open Finset Classical

/-- A concrete finite sample budget; the natural ceiling is kept explicitly. -/
def coverSize (L ζ : ℝ) : ℕ := ⌈Real.exp (L*Real.log 2)*(3/ζ)⌉₊

lemma coverSize_pos (L ζ : ℝ) (hζ:0<ζ) : 0<coverSize L ζ := by
  apply Nat.ceil_pos.mpr
  positivity

lemma exp_pair (L : ℝ) : Real.exp (-L*Real.log 2)*Real.exp (L*Real.log 2)=1 := by
  rw [←Real.exp_add]
  have he:-L*Real.log 2+L*Real.log 2=0 := by ring
  rw [he,Real.exp_zero]

lemma coverSize_failure (L ζ : ℝ) (hL:0 ≤ L) (hζ:0<ζ) :
    (1-Real.exp (-L*Real.log 2))^(coverSize L ζ) ≤ ζ/3 := by
  let q:=Real.exp (-L*Real.log 2)
  let X:=Real.exp (L*Real.log 2)*(3/ζ)
  let K:=coverSize L ζ
  have hq:0<q := Real.exp_pos _
  have hq1:q ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hl:0<Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hK:X ≤ (K:ℝ) := Nat.le_ceil X
  have he:q*X=3/ζ := by
    dsimp only [q,X]
    rw [←mul_assoc,exp_pair,one_mul]
  have hk:3/ζ ≤ (K:ℝ)*q := by
    have hh:=mul_le_mul_of_nonneg_left hK hq.le
    rw [he] at hh
    simpa only [mul_comm] using hh
  have hp:(1-q)^K ≤ Real.exp (-(K:ℝ)*q) := by
    have hh:1-q ≤ Real.exp (-q) := by have hx:=Real.add_one_le_exp (-q); linarith
    calc
      _ ≤ (Real.exp (-q))^K := pow_le_pow_left₀ (sub_nonneg.mpr hq1) hh _
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring
  have he:Real.exp (-(3/ζ)) ≤ ζ/3 := by
    rw [Real.exp_neg,←one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hh:3/ζ ≤ Real.exp (3/ζ) := by have hx:=Real.add_one_le_exp (3/ζ); linarith
    have hm:=mul_le_mul_of_nonneg_left hh (show 0 ≤ ζ/3 by positivity)
    have hz:(ζ/3)*(3/ζ)=1 := by field_simp
    rw [hz] at hm
    simpa only [mul_comm] using hm
  exact hp.trans ((Real.exp_le_exp.mpr (by linarith)).trans he)

lemma coverSize_log (L ζ : ℝ) (hL:0 ≤ L) (hζ:0<ζ) (hζ1:ζ<1) :
    Real.logb 2 (coverSize L ζ:ℝ) ≤ L+1+6/ζ := by
  let e:=Real.exp (L*Real.log 2)
  let X:=e*(3/ζ)
  have he:1 ≤ e := Real.one_le_exp_iff.mpr (mul_nonneg hL (Real.log_pos (by norm_num : (1:ℝ)<2)).le)
  have hx:1 ≤ X := by
    have hz:1 ≤ 3/ζ := (le_div_iff₀ hζ).mpr (by linarith)
    have hh:=mul_le_mul_of_nonneg_right he (show 0 ≤ 3/ζ by positivity)
    dsimp only [X]
    linarith
  have hK:0<(coverSize L ζ:ℝ) := by exact_mod_cast coverSize_pos L ζ hζ
  have hk:(coverSize L ζ:ℝ) ≤ 2*X := by
    have hh:=Nat.ceil_lt_add_one (show 0 ≤ X by linarith)
    change (coverSize L ζ:ℝ)<X+1 at hh
    linarith
  have hlog:Real.logb 2 (coverSize L ζ:ℝ) ≤ Real.logb 2 (2*X) :=
    (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hK (by positivity)).mpr hk
  have heq:Real.logb 2 (2*X)=1+L+Real.log (3/ζ)/Real.log 2 := by
    dsimp only [X,e]
    rw [Real.logb_mul (by norm_num : (2:ℝ)≠0) (by positivity),
      Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
      Real.logb_mul (Real.exp_ne_zero _) (by positivity)]
    simp only [Real.logb,Real.log_exp]
    have hl:Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2))
    field_simp <;> ring
  have hl2:(1:ℝ)/2 ≤ Real.log 2 := by
    have hh:=Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    linarith
  have hfrac:Real.log (3/ζ)/Real.log 2 ≤ 6/ζ := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    have hh:Real.log (3/ζ) ≤ 3/ζ := Real.log_le_self (by positivity)
    have hm:=mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 6/ζ by positivity)
    have he:(6/ζ)*(1/2)=3/ζ := by ring
    rw [he] at hm
    linarith
  rw [heq] at hlog
  linarith

end RandomOracleUnitarySynthesis.NetProof

/- Module RandomOracleNetNumerics -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.NetProof

lemma net_radius (d ζ : ℝ) (hd:0<d) (hd2:d<2) (hζ:0<ζ) (hζ1:ζ<1) :
    0<d*Real.sqrt (ζ/6) ∧ d*Real.sqrt (ζ/6) ≤ 1 ∧
      (d*Real.sqrt (ζ/6))^2=d^2*ζ/6 := by
  have hr:0<d*Real.sqrt (ζ/6) := mul_pos hd (Real.sqrt_pos.mpr (by positivity))
  have he:(d*Real.sqrt (ζ/6))^2=d^2*ζ/6 := by rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
  have hs:d^2 ≤ 4 := by nlinarith
  have ht:d^2*ζ ≤ 4 := by nlinarith [sq_nonneg d]
  refine ⟨hr,?_,he⟩
  nlinarith

/-- A fixed numerical bound sufficient for the universal constant in Cor4.10. -/
lemma net_log_budget (N K d ζ r : ℝ) (hN:1 ≤ N) (hK:1 ≤ K)
    (hd:0<d) (hd2:d<2) (hζ:0<ζ) (hζ1:ζ<1) (hrs:r^2=d^2*ζ/6) :
    3*(32*K^2*N/r^2+1)/ζ+1+6/ζ ≤ 1024*N*K^2/(ζ^2*d^2) := by
  let Q:=N*K^2/(ζ^2*d^2)
  have hD:0<ζ^2*d^2 := by positivity
  have hQ:0 ≤ Q := by dsimp only [Q]; positivity
  have hK2:1 ≤ K^2 := by nlinarith [sq_nonneg (K-1)]
  have hNK:1 ≤ N*K^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hK2)]
  have hd':d^2 ≤ 4 := by nlinarith
  have hζ':ζ^2 ≤ 1 := by nlinarith
  have hden:ζ^2*d^2 ≤ 4 := by
    have hh:=mul_le_mul_of_nonneg_right hζ' (sq_nonneg d)
    linarith
  have hden':ζ*d^2 ≤ 4 := by
    have hh:=mul_le_mul_of_nonneg_right hζ1.le (sq_nonneg d)
    linarith
  have h1:1 ≤ 4*Q := by
    change 1 ≤ 4*(N*K^2/(ζ^2*d^2))
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    linarith
  have h2:1/ζ ≤ 4*Q := by
    change 1/ζ ≤ 4*(N*K^2/(ζ^2*d^2))
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hζ hD).mpr
    have hh:=mul_le_mul_of_nonneg_left (show ζ*d^2 ≤ 4*(N*K^2) by linarith) hζ.le
    nlinarith
  have he:3*(32*K^2*N/r^2+1)/ζ+1+6/ζ=576*Q+1+9/ζ := by
    rw [hrs]
    dsimp only [Q]
    field_simp [hd.ne',hζ.ne'] <;> ring
  have hv:9/ζ=9*(1/ζ) := by ring
  rw [he,hv]
  have hh:576*Q+1+9*(1/ζ) ≤ 1024*Q := by linarith
  convert hh using 1 <;> first | rfl | dsimp only [Q]; ring

end RandomOracleUnitarySynthesis.NetProof

/- Module RandomOracleContractionNetMain -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis
open Matrix Finset Classical ResamplingProof NetProof

/-- Exact Corollary 4.10, with one universal constant and the full
Hermitian refinement. All selected centers are original circuit blocks. -/
theorem synthesis_contraction_net :
    ∃ B : ℝ, 0 < B ∧ ∀ (n m m₀ k : ℕ) (C : synthesis_Circuit n m m₀ k),
      1 ≤ k → ∀ d : ℝ, 0 < d → d < 2 → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ T : Finset (synthesis_Mat n), T.Nonempty ∧
        (∀ A ∈ T, synthesis_IsContraction A) ∧
        Real.logb 2 (T.card : ℝ) ≤ B * (2 : ℝ)^n * (k : ℝ)^2 / (ζ^2 * d^2) ∧
        synthesis_average (fun f : synthesis_Oracle m₀ =>
          if ∀ A ∈ T, d * Real.sqrt ((2 : ℝ)^n) < QAlgorithms.frobNorm (A - synthesis_A C f)
          then (1 : ℝ) else 0) ≤ ζ ∧
        ((∀ f, (synthesis_A C f).IsHermitian) → ∀ A ∈ T, A.IsHermitian) := by
  refine ⟨1024,by norm_num,?_⟩
  intro n m m₀ k C hk d hd hd2 ζ hζ hζ1
  let r:=d*Real.sqrt (ζ/6)
  have hr:=net_radius d ζ hd hd2 hζ hζ1
  have hr0:0<r := hr.1
  have hr1:r ≤ 1 := hr.2.1
  have hrs:r^2=d^2*ζ/6 := hr.2.2
  let b:=32*(k:ℝ)^2*(2:ℝ)^n/r^2
  let L:=3*(b+1)/ζ
  have hb:0 ≤ b := by dsimp only [b]; positivity
  have hb1:0<b+1 := by linarith
  have hL:0<L := by dsimp only [L]; positivity
  have hN:0<(2:ℝ)^n := pow_pos (by norm_num) _
  have hN1:(1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hbad:synthesis_average (fun f:synthesis_Oracle m₀=>
      if smallNeighborhood (near C d) L f then 1 else 0) ≤ 2*ζ/3 := by
    have hh:=oracle_small_neighborhood C d hd r hr0 hr1 L hL
    have hratio:(b+1)/L=ζ/3 := by
      dsimp only [L]
      field_simp [hζ.ne',hb1.ne'] <;> ring
    have henergy:(2*(2:ℝ)^n*r^2)/(d^2*(2:ℝ)^n)=ζ/3 := by
      rw [hrs]
      field_simp [hd.ne',hN.ne'] <;> ring
    change _ ≤ (b+1)/L+(2*(2:ℝ)^n*r^2)/(d^2*(2:ℝ)^n) at hh
    rw [hratio,henergy] at hh
    linarith
  let q:=Real.exp (-L*Real.log 2)
  let K:=coverSize L ζ
  have hq:0<q := Real.exp_pos _
  have hq1:q ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_pos hL (Real.log_pos (by norm_num : (1:ℝ)<2))]
  obtain ⟨U,hcard,hUne,hcover⟩:=finite_greedy_cover (near C d)
    (fun f:synthesis_Oracle m₀=>¬smallNeighborhood (near C d) L f) q hq.le hq1
    (fun f hf=>neighborhood_density (near C d) L f hf) K
  have hU:U.Nonempty := hUne (coverSize_pos L ζ hζ)
  have hcov:synthesis_average (uncovered (near C d)
      (fun f:synthesis_Oracle m₀=>¬smallNeighborhood (near C d) L f) U) ≤ ζ/3 :=
    hcover.trans (coverSize_failure L ζ hL.le hζ)
  let T:=U.image (fun f:synthesis_Oracle m₀=>synthesis_A C f)
  have hT:T.Nonempty := hU.image _
  refine ⟨T,hT,?_,?_,?_,?_⟩
  · intro A hA
    obtain ⟨f,hf,hAf⟩:=mem_image.mp hA
    rw [←hAf]
    exact A_contraction C f
  · have hTK:(T.card:ℝ) ≤ (K:ℝ) := by
      exact_mod_cast (card_image_le.trans hcard)
    have hTc:0<(T.card:ℝ) := by exact_mod_cast hT.card_pos
    have hKc:0<(K:ℝ) := by exact_mod_cast coverSize_pos L ζ hζ
    have hh:Real.logb 2 (T.card:ℝ) ≤ Real.logb 2 (K:ℝ) :=
      (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hTc hKc).mpr hTK
    have hnum:=net_log_budget ((2:ℝ)^n) (k:ℝ) d ζ r hN1 (by exact_mod_cast hk)
      hd hd2 hζ hζ1 hrs
    exact hh.trans ((coverSize_log L ζ hL.le hζ hζ1).trans hnum)
  · have he:∀f:synthesis_Oracle m₀,
        (if ∀A∈T,d*Real.sqrt ((2:ℝ)^n)<QAlgorithms.frobNorm (A-synthesis_A C f) then (1:ℝ) else 0)=
        if ∀g∈U,¬near C d f g then 1 else 0 := by
      intro f
      simp only [T,forall_mem_image,near,not_le]
    simp only [he]
    have hp:∀f:synthesis_Oracle m₀,(if ∀g∈U,¬near C d f g then (1:ℝ) else 0) ≤
        (if smallNeighborhood (near C d) L f then 1 else 0)+
        uncovered (near C d) (fun g:synthesis_Oracle m₀=>¬smallNeighborhood (near C d) L g) U f := by
      intro f
      by_cases hb:smallNeighborhood (near C d) L f <;>
        by_cases ht:∀g∈U,¬near C d f g <;> simp [uncovered,hb,ht] <;> split_ifs <;> norm_num
    have hh:=average_mono _ _ hp
    rw [average_add] at hh
    linarith
  · intro hHerm A hA
    obtain ⟨f,hf,hAf⟩:=mem_image.mp hA
    rw [←hAf]
    exact hHerm f

end RandomOracleUnitarySynthesis

/- Module RandomOracleCorrelationNetMain -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace RandomOracleUnitarySynthesis
open Matrix Finset Classical MeasureTheory ProbabilityTheory Filter
open ChannelProof
open scoped ComplexConjugate ENNReal

/-- Exact published Lemma4.12, using the original channel-coordinate coupling
and the actual oracle-independent 2k-query Heisenberg circuit. -/
theorem synthesis_haar_correlation_net :
    ∃ B : ℝ, 0 < B ∧ ∀ (m m₀ k : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n)) (ε : ℕ → ℝ),
      synthesis_Admissible m m₀ k C ε → synthesis_GapRegime ε →
      ∀ᶠ n in atTop,
        ∃ T : Finset (synthesis_Mat n), T.Nonempty ∧
          (∀ A ∈ T, A.IsHermitian ∧ synthesis_IsContraction A) ∧
          Real.logb 2 (T.card : ℝ) ≤ B * (2 : ℝ)^n * (k n : ℝ)^2 / (1-ε n)^4 ∧
          ∃ Q : synthesis_Pauli n, Q ≠ (fun _ => 0) ∧
            ENNReal.ofReal ((1-ε n)/8) ≤
              (synthesis_haar n) {U | ∃ A ∈ T, (1-ε n)/8 ≤ synthesis_correlation A Q U} := by
  obtain ⟨B,hB,hNet⟩:=synthesis_contraction_net
  refine ⟨B*65536,mul_pos hB (by norm_num),?_⟩
  intro m m₀ k C ε hAdm hGap
  have hg:∀ᶠn in atTop,4 ≤ ((2:ℝ)^n)^2*(1-ε n) :=
    hGap.eventually (eventually_ge_atTop 4)
  filter_upwards [hAdm,hg] with n hn hgap
  obtain ⟨hk,hε1,hε0,γ,hγ,hfst,hsnd,herr⟩:=hn
  letI : IsProbabilityMeasure γ:=hγ
  have hp:=coupling_ae_ranges (C n) γ hfst hsnd
  obtain ⟨Q,hQ,hmean⟩:=nonidentity_coupling_overlap (C n) (ε n) hε0 hε1 hgap γ hp herr
  let δ:ℝ:=1-ε n
  have hδ:0<δ := sub_pos.mpr hε1
  have hδ1:δ ≤ 1 := by dsimp only [δ];linarith
  let C₂:=observableCircuit (C n) Q
  obtain ⟨T,hT,hTC,hcard,hbad,hTH⟩:=hNet n (m n) (m₀ n) (2*k n) C₂ (by omega)
    (δ/8) (by positivity) (by linarith) (δ/16) (by positivity) (by linarith)
  have hHerm:∀f,(synthesis_A C₂ f).IsHermitian := by
    intro f
    rw [show synthesis_A C₂ f=synthesis_observable (C n) f Q from observableCircuit_A (C n) Q f]
    exact observable_hermitian (C n) Q f
  refine ⟨T,hT,(fun A hA=>⟨hTH hHerm A hA,hTC A hA⟩),?_,Q,hQ,?_⟩
  · have hnum:B*(2:ℝ)^n*((2*k n:ℕ):ℝ)^2/((δ/16)^2*(δ/8)^2)=
        (B*65536)*(2:ℝ)^n*(k n:ℝ)^2/δ^4 := by
      push_cast
      field_simp
      <;> ring
    rw [hnum] at hcard
    exact hcard
  · have hbad':synthesis_average (fun f:synthesis_Oracle (m₀ n)=>
        if badNet T Q (δ/8) (synthesis_actualChannel (C n) f) then 1 else 0) ≤ δ/16 := by
      have he:∀f:synthesis_Oracle (m₀ n),
          badNet T Q (δ/8) (synthesis_actualChannel (C n) f) ↔
          ∀A∈T,(δ/8)*Real.sqrt ((2:ℝ)^n)<QAlgorithms.frobNorm (A-synthesis_A C₂ f) := by
        intro f
        rw [badNet_actual,show synthesis_A C₂ f=synthesis_observable (C n) f Q from observableCircuit_A (C n) Q f]
      simpa only [he] using hbad
    have hm:=coupling_net_mean_lower (C n) γ hfst hsnd T hT hTC Q (δ/8) (δ/16) (δ/2)
      (by positivity) hbad' hmean
    let F:synthesis_Unitary n→ℝ:=fun U=>netMaximum T hT Q (synthesis_unitaryChannel U)
    have hF:Continuous F := (netMaximum_continuous T hT Q).comp unitaryChannel_continuous
    have hFi:Integrable F (synthesis_haar n) :=
      hF.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
    have hi:2*(δ/8) ≤ ∫U,F U ∂synthesis_haar n := by
      change _ ≤ ∫U,netMaximum T hT Q (synthesis_unitaryChannel U) ∂synthesis_haar n
      linarith
    have hprob:=integral_lower_probability (synthesis_haar n) F hFi (δ/8) (by positivity) hi
      (Filter.Eventually.of_forall (fun U=>(netMaximum_bounds T hT hTC Q _ ⟨U,rfl⟩).2))
      (measurableSet_le measurable_const hF.measurable)
    have hset:{U:synthesis_Unitary n|δ/8 ≤ F U}=
        {U|∃A∈T,δ/8 ≤ synthesis_correlation A Q U} := by
      ext U
      change δ/8 ≤ T.sup' hT (fun A=>channelCorrelation A Q (synthesis_unitaryChannel U)) ↔ _
      rw [Finset.le_sup'_iff]
      simp only [unitaryChannel_correlation,Set.mem_setOf_eq]
    rw [hset] at hprob
    exact hprob

end RandomOracleUnitarySynthesis

/- Module RandomOraclePublicUnitaryReindex -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.PublicHaarProof
open Matrix Finset Classical MeasureTheory
open GeometryProof
open scoped ComplexConjugate
instance public_unitaryHaar_isHaar (d:ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar
  infer_instance

instance public_unitaryHaar_probability (d:ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def reindexUnitary (e : β≃α) (U : Matrix.unitaryGroup α ℂ) : Matrix.unitaryGroup β ℂ := by
  refine ⟨(U:Matrix α α ℂ).submatrix e e,?_⟩
  apply Unitary.mem_iff.mpr
  constructor
  · change ((U:Matrix α α ℂ).submatrix e e)ᴴ*((U:Matrix α α ℂ).submatrix e e)=1
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
      show (U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 from Unitary.star_mul_self_of_mem U.property,
      Matrix.submatrix_one_equiv]
  · change ((U:Matrix α α ℂ).submatrix e e)*((U:Matrix α α ℂ).submatrix e e)ᴴ=1
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
      show (U:Matrix α α ℂ)*(U:Matrix α α ℂ)ᴴ=1 from Unitary.mul_star_self_of_mem U.property,
      Matrix.submatrix_one_equiv]

@[simp] lemma reindexUnitary_val (e : β≃α) (U : Matrix.unitaryGroup α ℂ) :
    (reindexUnitary e U:Matrix β β ℂ)=(U:Matrix α α ℂ).submatrix e e := rfl

def unitaryReindexEquiv (e : β≃α) : Matrix.unitaryGroup α ℂ≃*Matrix.unitaryGroup β ℂ where
  toFun:=reindexUnitary e
  invFun:=reindexUnitary e.symm
  left_inv U:=by apply Subtype.ext;ext x y;simp [Matrix.submatrix_apply]
  right_inv U:=by apply Subtype.ext;ext x y;simp [Matrix.submatrix_apply]
  map_mul' U V:=by
    apply Subtype.ext
    change ((U:Matrix α α ℂ)*(V:Matrix α α ℂ)).submatrix e e=
      (U:Matrix α α ℂ).submatrix e e*(V:Matrix α α ℂ).submatrix e e
    exact (Matrix.submatrix_mul_equiv _ _ e e e).symm

lemma continuous_unitaryReindexEquiv (e : β≃α) : Continuous (unitaryReindexEquiv e) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i=>continuous_pi (fun j=>
    (continuous_apply (e j)).comp ((continuous_apply (e i)).comp continuous_subtype_val)))

lemma frob_reindex (e : β≃α) (A : Matrix α α ℂ) :
    QAlgorithms.frobNorm (A.submatrix e e)=QAlgorithms.frobNorm A := by
  rw [frob_eq_sqrt_entries,frob_eq_sqrt_entries]
  congr 1
  have hi:∀i:α,(∑j:β,‖A i (e j)‖^2)=∑j:α,‖A i j‖^2 :=
    fun i=>e.sum_comp (fun j:α=>‖A i j‖^2)
  simp only [Matrix.submatrix_apply,hi]
  exact e.sum_comp (fun i:α=>∑j:α,‖A i j‖^2)

/-- Change only the finite basis labels; the full normalized Haar law is
transported by a continuous group isomorphism. -/
theorem qubit_unitary_reindex_measurePreserving (n : ℕ) :
    MeasurePreserving (unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm)
      (synthesis_haar n) (QAlgorithms.Schur.unitaryHaar (Fintype.card (synthesis_Bits n))) := by
  letI : Measure.IsHaarMeasure (synthesis_haar n) := by
    unfold synthesis_haar
    infer_instance
  exact MonoidHom.measurePreserving
    (f:=(unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm).toMonoidHom)
    (continuous_unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm)
    (unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm).surjective (by simp)

end RandomOracleUnitarySynthesis.PublicHaarProof

/- Module RandomOraclePublicHaarSubgaussian -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.PublicHaarProof
open MeasureTheory ProbabilityTheory Finset Classical

/-- Centered sub-Gaussian MGF for the actual full Haar measure, using the
proved SU kernel and genuine phase invariance. -/
theorem phase_invariant_subgaussian (d : ℕ) (hd:1 ≤ d)
    (F : Matrix.unitaryGroup (Fin d) ℂ→ℝ) (hF:Continuous F) (L : ℝ) (hL:0 ≤ L)
    (hLip:∀U V:Matrix.unitaryGroup (Fin d) ℂ,|F U-F V| ≤ L*Real.sqrt
      (∑x:Fin d,∑y:Fin d,‖(U:Matrix (Fin d) (Fin d) ℂ) x y-(V:Matrix (Fin d) (Fin d) ℂ) x y‖^2))
    (hphase:∀z:Circle,∀U V:Matrix.unitaryGroup (Fin d) ℂ,
      (U:Matrix (Fin d) (Fin d) ℂ)=(z:ℂ) • (V:Matrix (Fin d) (Fin d) ℂ)→F U=F V) :
    HasSubgaussianMGF (fun U=>F U-∫V,F V ∂QAlgorithms.Schur.unitaryHaar d)
      ⟨2*L^2/d,by positivity⟩ (QAlgorithms.Schur.unitaryHaar d) := by
  let μ:=QAlgorithms.Schur.unitaryHaar d
  let m:=∫U,F U ∂μ
  have hFi:Integrable F μ := hF.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  have hc:∀t:ℝ,Continuous (fun U=>t*(F U-m)) := fun t=>(hF.sub continuous_const).const_mul t
  have he:∀t:ℝ,Integrable (fun U=>Real.exp (t*(F U-m))) μ :=
    fun t=>(hc t).rexp.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  refine ⟨he,?_⟩
  intro t
  have hh:=HaarPhaseInvariantUnitary.logMeanBound d hd (fun U=>t*(F U-m)) (hc t) (|t| *L)
    (mul_nonneg (abs_nonneg t) hL) (by
      intro U V
      rw [←mul_sub,sub_sub_sub_cancel_right,abs_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hLip U V) (abs_nonneg t))
    (by intro z U V he;rw [hphase z U V he])
  have hi:(∫U,t*(F U-m) ∂μ)=0 := by
    rw [integral_const_mul,integral_sub hFi (integrable_const m)]
    simp [m]
  change Real.log (∫U,Real.exp (t*(F U-m)) ∂μ) ≤ (∫U,t*(F U-m) ∂μ)+(|t| *L)^2/d at hh
  rw [hi,zero_add] at hh
  have hcoef:(|t| *L)^2/d=(2*L^2/d)*t^2/2 := by rw [mul_pow,sq_abs];ring
  rw [hcoef] at hh
  exact (Real.log_le_iff_le_exp (integral_exp_pos (he t))).mp hh

end RandomOracleUnitarySynthesis.PublicHaarProof

/- Module RandomOraclePublicQubitSubgaussian -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.PublicHaarProof
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open GeometryProof
open scoped ComplexConjugate

/-- The proved phase-invariant concentration uses only finite basis labels;
transporting back to the public binary register preserves its Haar law. -/
theorem qubit_phase_subgaussian (n : ℕ) (F : synthesis_Unitary n→ℝ) (hF:Continuous F)
    (L : ℝ) (hL:0 ≤ L)
    (hLip:∀U V:synthesis_Unitary n,|F U-F V| ≤ L*QAlgorithms.frobNorm
      ((U:synthesis_Mat n)-(V:synthesis_Mat n)))
    (hphase:∀z:Circle,∀U V:synthesis_Unitary n,
      (U:synthesis_Mat n)=(z:ℂ) • (V:synthesis_Mat n)→F U=F V) :
    HasSubgaussianMGF (fun U=>F U-∫V,F V ∂synthesis_haar n)
      ⟨2*L^2/(Fintype.card (synthesis_Bits n):ℝ),by positivity⟩ (synthesis_haar n) := by
  let d:=Fintype.card (synthesis_Bits n)
  let e:Fin d≃synthesis_Bits n:=(Fintype.equivFin (synthesis_Bits n)).symm
  let E:=unitaryReindexEquiv e
  let G:Matrix.unitaryGroup (Fin d) ℂ→ℝ:=fun V=>F (E.symm V)
  have hd:1 ≤ d := Fintype.card_pos
  have hEi:Continuous (fun V:Matrix.unitaryGroup (Fin d) ℂ=>E.symm V) :=
    continuous_unitaryReindexEquiv e.symm
  have hG:Continuous G := hF.comp hEi
  have hmetric:∀U V:Matrix.unitaryGroup (Fin d) ℂ,
      QAlgorithms.frobNorm ((E.symm U:synthesis_Mat n)-(E.symm V:synthesis_Mat n))=
        Real.sqrt (∑x:Fin d,∑y:Fin d,‖(U:Matrix (Fin d) (Fin d) ℂ) x y-
          (V:Matrix (Fin d) (Fin d) ℂ) x y‖^2) := by
    intro U V
    have he:((E.symm U:synthesis_Mat n)-(E.symm V:synthesis_Mat n))=
        ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)).submatrix e.symm e.symm := rfl
    rw [he,frob_reindex,frob_eq_sqrt_entries]
    simp only [Matrix.sub_apply]
  have hsg:=phase_invariant_subgaussian d hd G hG L hL (by
    intro U V
    have hh:=hLip (E.symm U) (E.symm V)
    rwa [hmetric] at hh) (by
      intro z U V he
      apply hphase z
      ext x y
      exact congrFun (congrFun he (e.symm x)) (e.symm y))
  have hMP:=qubit_unitary_reindex_measurePreserving n
  have hI:(∫V,G V ∂QAlgorithms.Schur.unitaryHaar d)=∫U,F U ∂synthesis_haar n := by
    rw [←hMP.map_eq,integral_map hMP.measurable.aemeasurable hG.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun U=>by dsimp only [G];rw [E.symm_apply_apply])
  have hsg':HasSubgaussianMGF (fun V:Matrix.unitaryGroup (Fin d) ℂ=>G V-∫W,G W ∂QAlgorithms.Schur.unitaryHaar d)
      ⟨2*L^2/d,by positivity⟩ ((synthesis_haar n).map E) := by
    rw [hMP.map_eq]
    exact hsg
  have hh:=HasSubgaussianMGF.of_map hMP.measurable.aemeasurable hsg'
  have hEE:∀U:synthesis_Unitary n,
      E.symm ((unitaryReindexEquiv (Fintype.equivFin (synthesis_Bits n)).symm) U)=U :=
    fun U=>E.symm_apply_apply U
  simpa only [Function.comp_def,G,hEE,hI] using hh

end RandomOracleUnitarySynthesis.PublicHaarProof

/- Module RandomOraclePauliHaarMean -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis.HaarProof
open Matrix Finset Classical MeasureTheory
open GeometryProof PauliProof DirectFidelity.State
open scoped ComplexConjugate

@[simp] lemma pauliUnitary_val {n : ℕ} (P : synthesis_Pauli n) :
    (pauliUnitary P:synthesis_Mat n)=W P := rfl

lemma pauli_conjugate_correlation_sum {n : ℕ} (A : synthesis_Mat n)
    (Q : synthesis_Pauli n) (hQ:Q≠(fun _=>0)) (U : synthesis_Unitary n) :
    (∑P:synthesis_Pauli n,matrixCorrelation A (pauliUnitary Q) (pauliUnitary P*U))=0 := by
  have he:∀P:synthesis_Pauli n,matrixCorrelation A (pauliUnitary Q) (pauliUnitary P*U)=
      (A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n)).trace.re/
        (Fintype.card (synthesis_Bits n):ℝ) := by
    intro P
    unfold matrixCorrelation
    simp only [Submonoid.coe_mul,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      pauliUnitary_val,Matrix.conjTranspose_mul,W_herm]
    congr 2
    simp only [Matrix.mul_assoc]
  have hM:(∑P:synthesis_Pauli n,A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n))=0 := by
    have hh:(∑P:synthesis_Pauli n,A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n))=
        (A*(U:synthesis_Mat n)ᴴ)*(∑P:synthesis_Pauli n,W P*W Q*W P)*(U:synthesis_Mat n) := by
      simp only [Matrix.mul_sum,Matrix.sum_mul]
    rw [hh,pauli_twirl,trace_W,if_neg hQ,mul_zero,zero_smul,Matrix.mul_zero,Matrix.zero_mul]
  calc
    _ = ((∑P:synthesis_Pauli n,A*(U:synthesis_Mat n)ᴴ*(W P*W Q*W P)*(U:synthesis_Mat n)).trace).re/
        (Fintype.card (synthesis_Bits n):ℝ) := by
      simp only [he,Matrix.trace_sum,Complex.re_sum,sum_div]
    _ = 0 := by rw [hM];simp

/-- Mean zero is proved from the actual Haar left invariance and finite Pauli
twirl, using no assumed centeredness of the correlation observable. -/
theorem pauli_haar_mean_zero {n : ℕ} (A : synthesis_Mat n)
    (Q : synthesis_Pauli n) (hQ:Q≠(fun _=>0)) :
    (∫U,matrixCorrelation A (pauliUnitary Q) U ∂synthesis_haar n)=0 := by
  letI : Measure.IsHaarMeasure (synthesis_haar n) := by unfold synthesis_haar;infer_instance
  let F:synthesis_Unitary n→ℝ:=matrixCorrelation A (pauliUnitary Q)
  have hc:Continuous F := matrixCorrelation_continuous A (pauliUnitary Q)
  have hi:∀P:synthesis_Pauli n,Integrable (fun U:synthesis_Unitary n=>F (pauliUnitary P*U)) (synthesis_haar n) := by
    intro P
    exact (hc.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))
  have hz:(fun U:synthesis_Unitary n=>∑P:synthesis_Pauli n,F (pauliUnitary P*U))=(fun _=>0) :=
    funext (fun U=>pauli_conjugate_correlation_sum A Q hQ U)
  have hh:=congrArg (fun g:synthesis_Unitary n→ℝ=>∫U,g U ∂synthesis_haar n) hz
  rw [integral_finset_sum _ (fun P _=>hi P)] at hh
  simp only [integral_zero,integral_mul_left_eq_self,sum_const,card_univ,nsmul_eq_mul] at hh
  have hcard:(Fintype.card (synthesis_Pauli n):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hh).resolve_left hcard

end RandomOracleUnitarySynthesis.HaarProof

/- Module RandomOracleHaarTailPublic -/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace RandomOracleUnitarySynthesis
open Matrix Finset Classical MeasureTheory ProbabilityTheory
open GeometryProof HaarProof PublicHaarProof PauliProof
open scoped ComplexConjugate ENNReal

/-- Exact public Lemma4.13. The proof derives the stronger exponent 1/16
from the actual phase-invariant SU log-Sobolev kernel and then relaxes to 1/48. -/
theorem synthesis_haar_trace_tail (n : ℕ) (A : synthesis_Mat n)
    (hA : A.IsHermitian) (hcontract : synthesis_IsContraction A)
    (Q : synthesis_Pauli n) (hQ : Q ≠ (fun _ => 0)) (t : ℝ) (ht : 0 ≤ t) :
    (synthesis_haar n) {U | t ≤ synthesis_correlation A Q U} ≤
      ENNReal.ofReal (Real.exp (-((2 : ℝ)^n)^2 * t^2 / 48)) := by
  let F:synthesis_Unitary n→ℝ:=matrixCorrelation A (pauliUnitary Q)
  have hcard:(Fintype.card (synthesis_Bits n):ℝ)=(2:ℝ)^n := by
    simp [synthesis_Bits,DirectFidelity.State.Q]
  have hN:0<(2:ℝ)^n := pow_pos (by norm_num) _
  have hs:0<Real.sqrt ((2:ℝ)^n) := Real.sqrt_pos.mpr hN
  have hF:∀U:synthesis_Unitary n,F U=synthesis_correlation A Q U := by
    intro U
    change (A*((U:synthesis_Mat n)ᴴ*DirectFidelity.State.W Q*(U:synthesis_Mat n))).trace.re/
        (Fintype.card (synthesis_Bits n):ℝ)=_
    rw [hcard]
    rfl
  have hL:0 ≤ 2/Real.sqrt (Fintype.card (synthesis_Bits n):ℝ) := by positivity
  have hsg:=qubit_phase_subgaussian n F (matrixCorrelation_continuous A (pauliUnitary Q))
    (2/Real.sqrt (Fintype.card (synthesis_Bits n):ℝ)) hL
    (fun U V=>matrixCorrelation_lipschitz A hcontract (pauliUnitary Q) U V)
    (fun z U V he=>matrixCorrelation_phase A (pauliUnitary Q) U V z he)
  have hmean:(∫U,F U ∂synthesis_haar n)=0 := pauli_haar_mean_zero A Q hQ
  rw [hmean] at hsg
  simp only [sub_zero] at hsg
  have hh:=hsg.measure_ge_le ht
  change (synthesis_haar n).real {U|t ≤ F U} ≤
    Real.exp (-t^2/(2*(2*(2/Real.sqrt (Fintype.card (synthesis_Bits n):ℝ))^2/
      (Fintype.card (synthesis_Bits n):ℝ)))) at hh
  rw [hcard] at hh
  have hc:2*(2/Real.sqrt ((2:ℝ)^n))^2/((2:ℝ)^n)=8/((2:ℝ)^n)^2 := by
    rw [div_pow,Real.sq_sqrt hN.le]
    field_simp
    <;> ring
  rw [hc] at hh
  have he:-t^2/(2*(8/((2:ℝ)^n)^2))=-((2:ℝ)^n)^2*t^2/16 := by
    field_simp
    <;> ring
  rw [he] at hh
  have hweak:Real.exp (-((2:ℝ)^n)^2*t^2/16) ≤ Real.exp (-((2:ℝ)^n)^2*t^2/48) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg ((2:ℝ)^n)) (sq_nonneg t)]
  have hset:{U:synthesis_Unitary n|t ≤ F U}={U|t ≤ synthesis_correlation A Q U} := by
    ext U
    change t ≤ F U ↔ t ≤ synthesis_correlation A Q U
    rw [hF]
  rw [←hset]
  calc
    _ = ENNReal.ofReal ((synthesis_haar n).real {U|t ≤ F U}) :=
      (ENNReal.ofReal_toReal (measure_ne_top (synthesis_haar n) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hh.trans hweak)

end RandomOracleUnitarySynthesis

/- Module RandomOracleQueryNumerics -/

namespace RandomOracleUnitarySynthesis.QueryNumerics

lemma scaled_log_le_eight (delta : ℝ) (h0 : 0 < delta) (h1 : delta ≤ 1) :
    delta ^ 4 * Real.log (8 / delta) ≤ 8 := by
  have hh : Real.log (8 / delta) ≤ 8 / delta :=
    (Real.log_le_sub_one_of_pos (div_pos (by norm_num) h0)).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg h0.le 4)
  have he : delta ^ 4 * (8 / delta) = 8 * delta ^ 3 := by field_simp
  rw [he] at hm
  exact hm.trans (by nlinarith [show delta ^ 3 ≤ 1 from pow_le_one₀ h0.le h1])

theorem query_bound (B N k delta : ℝ) (hB : 0 ≤ B) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    (h : N ^ 2 * delta ^ 2 / 3072 ≤ Real.log (8 / delta) +
      B * Real.log 2 * N * k ^ 2 / delta ^ 4) :
    (1 / (3072 * (8 + B * Real.log 2))) * N ≤ k ^ 2 / delta ^ 6 := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hC : 0 < 3072 * (8 + B * Real.log 2) := by positivity
  have ht := mul_le_mul_of_nonneg_left h (pow_nonneg hd0.le 4)
  have he : delta ^ 4 * (N ^ 2 * delta ^ 2 / 3072) = N ^ 2 * delta ^ 6 / 3072 := by ring
  have he2 : delta ^ 4 * (B * Real.log 2 * N * k ^ 2 / delta ^ 4) =
      B * Real.log 2 * N * k ^ 2 := by field_simp
  rw [mul_add, he, he2] at ht
  have hsmall := scaled_log_le_eight delta hd0 hd1
  have hNk : 1 ≤ N * k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
  have hscaled : N ^ 2 * delta ^ 6 ≤ 3072 * (8 + B * Real.log 2) * N * k ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3072 by norm_num) (show 0 ≤ 8 * (N * k ^ 2 - 1) by nlinarith)]
  have hcancel : N * delta ^ 6 ≤ 3072 * (8 + B * Real.log 2) * k ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hN0.le)
    field_simp at hh
    nlinarith
  apply (le_div_iff₀ (pow_pos hd0 6)).mpr
  have hx : (N * delta ^ 6) / (3072 * (8 + B * Real.log 2)) ≤ k ^ 2 :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hcancel)
  calc
    _ = (N * delta ^ 6) / (3072 * (8 + B * Real.log 2)) := by ring
    _ ≤ k ^ 2 := hx

end RandomOracleUnitarySynthesis.QueryNumerics

/- Module RandomOracleTailUnion -/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace RandomOracleUnitarySynthesis.QueryNumerics
open Matrix Finset Classical MeasureTheory
open scoped ENNReal

lemma haar_net_union_bound (n:ℕ) (T:Finset (synthesis_Mat n))
    (hT:∀A∈T,A.IsHermitian∧synthesis_IsContraction A)
    (Q:synthesis_Pauli n) (hQ:Q≠(fun _=>0)) (t:ℝ) (ht:0 ≤ t) :
    (synthesis_haar n) {U|∃A∈T,t ≤ synthesis_correlation A Q U} ≤
      ENNReal.ofReal ((T.card:ℝ)*Real.exp (-((2:ℝ)^n)^2*t^2/48)) := by
  have he:{U:synthesis_Unitary n|∃A∈T,t ≤ synthesis_correlation A Q U}=
      ⋃A∈T,{U|t ≤ synthesis_correlation A Q U} := by ext U;simp
  rw [he]
  calc
    _ ≤ ∑A∈T,(synthesis_haar n) {U|t ≤ synthesis_correlation A Q U} :=
      measure_biUnion_finset_le T _
    _ ≤ ∑A∈T,ENNReal.ofReal (Real.exp (-((2:ℝ)^n)^2*t^2/48)) :=
      Finset.sum_le_sum (fun A hA=>synthesis_haar_trace_tail n A (hT A hA).1 (hT A hA).2 Q hQ t ht)
    _ = _ := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun A (_:A∈T)=>(Real.exp_pos _).le)]
      simp

lemma log_inequality_of_net (B:ℝ) (n k:ℕ) (δ:ℝ) (hδ:0<δ)
    (T:Finset (synthesis_Mat n)) (hT:T.Nonempty)
    (hTC:∀A∈T,A.IsHermitian∧synthesis_IsContraction A)
    (Q:synthesis_Pauli n) (hQ:Q≠(fun _=>0))
    (hcard:Real.logb 2 (T.card:ℝ) ≤ B*(2:ℝ)^n*(k:ℝ)^2/δ^4)
    (hprob:ENNReal.ofReal (δ/8) ≤ (synthesis_haar n) {U|∃A∈T,δ/8 ≤ synthesis_correlation A Q U}) :
    ((2:ℝ)^n)^2*δ^2/3072 ≤ Real.log (8/δ)+B*Real.log 2*(2:ℝ)^n*(k:ℝ)^2/δ^4 := by
  have hu:=haar_net_union_bound n T hTC Q hQ (δ/8) (by positivity)
  have hr:δ/8 ≤ (T.card:ℝ)*Real.exp (-((2:ℝ)^n)^2*(δ/8)^2/48) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hprob.trans hu)
  have hTc:0<(T.card:ℝ) := by exact_mod_cast hT.card_pos
  have hlog:=Real.log_le_log (show 0<δ/8 by positivity) hr
  rw [Real.log_mul hTc.ne' (Real.exp_pos _).ne',Real.log_exp] at hlog
  have hinv:Real.log (δ/8) = -Real.log (8/δ) := by
    rw [←Real.log_inv]
    congr 1
    field_simp
  rw [hinv] at hlog
  have h2:0<Real.log 2 := Real.log_pos (by norm_num)
  have hlogcard:Real.log (T.card:ℝ) ≤ B*(2:ℝ)^n*(k:ℝ)^2/δ^4*Real.log 2 :=
    (div_le_iff₀ h2).mp hcard
  have hexp:-((2:ℝ)^n)^2*(δ/8)^2/48 = -(((2:ℝ)^n)^2*δ^2/3072) := by ring
  rw [hexp] at hlog
  have halg:B*(2:ℝ)^n*(k:ℝ)^2/δ^4*Real.log 2=
      B*Real.log 2*(2:ℝ)^n*(k:ℝ)^2/δ^4 := by ring
  rw [halg] at hlogcard
  linarith only [hlog,hlogcard]

lemma query_bound_from_net (B:ℝ) (hB:0 ≤ B) (n k:ℕ) (hk:1 ≤ k)
    (δ:ℝ) (hδ:0<δ) (hδ1:δ ≤ 1)
    (T:Finset (synthesis_Mat n)) (hT:T.Nonempty)
    (hTC:∀A∈T,A.IsHermitian∧synthesis_IsContraction A)
    (Q:synthesis_Pauli n) (hQ:Q≠(fun _=>0))
    (hcard:Real.logb 2 (T.card:ℝ) ≤ B*(2:ℝ)^n*(k:ℝ)^2/δ^4)
    (hprob:ENNReal.ofReal (δ/8) ≤ (synthesis_haar n) {U|∃A∈T,δ/8 ≤ synthesis_correlation A Q U}) :
    (1/(3072*(8+B*Real.log 2)))*(2:ℝ)^n ≤ (k:ℝ)^2/δ^6 :=
  query_bound B ((2:ℝ)^n) (k:ℝ) δ hB (one_le_pow₀ (by norm_num)) (by exact_mod_cast hk) hδ hδ1
    (log_inequality_of_net B n k δ hδ T hT hTC Q hQ hcard hprob)

end RandomOracleUnitarySynthesis.QueryNumerics

/- Module RandomOracleMainCore -/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace RandomOracleUnitarySynthesis
open Matrix Finset Classical MeasureTheory Filter
open scoped ENNReal

/-- The complete first asymptotic conclusion, with one positive universal
constant for every admissible family and the original gap regime. -/
theorem synthesis_query_bound_core :
    ∃c:ℝ,0<c∧∀(m m₀ k:ℕ→ℕ)
      (C:(n:ℕ)→synthesis_Circuit n (m n) (m₀ n) (k n)) (ε:ℕ→ℝ),
      synthesis_Admissible m m₀ k C ε→synthesis_GapRegime ε→
      ∀ᶠn:ℕ in atTop,c*(2:ℝ)^n ≤ (k n:ℝ)^2*((1-ε n)⁻¹)^6 := by
  obtain ⟨B,hB,hNet⟩:=synthesis_haar_correlation_net
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  refine ⟨1/(3072*(8+B*Real.log 2)),by positivity,?_⟩
  intro m m₀ k C ε hAdm hGap
  have hn:=hNet m m₀ k C ε hAdm hGap
  filter_upwards [hAdm,hn] with n hA hN
  obtain ⟨hk,hε1,hSyn⟩:=hA
  obtain ⟨T,hT,hTC,hcard,Q,hQ,hprob⟩:=hN
  have hδ:0<1-ε n:=sub_pos.mpr hε1
  have hδ1:1-ε n ≤ 1:=by linarith [hSyn.1]
  have hh:=QueryNumerics.query_bound_from_net B hB.le n (k n) hk (1-ε n) hδ hδ1
    T hT hTC Q hQ hcard hprob
  simpa only [inv_pow,div_eq_mul_inv] using hh

end RandomOracleUnitarySynthesis

/- Module RandomOracleInverseNumerics -/

namespace RandomOracleUnitarySynthesis.QueryNumerics

 theorem inverse_bound (c N k delta A : ℝ)
    (hc : 0 < c) (hN : 0 ≤ N) (hk : 0 ≤ k) (hd : 0 < delta) (hA : 0 < A)
    (hquery : c * N ≤ k ^ 2 / delta ^ 6) (hinv : delta⁻¹ ≤ A) :
    Real.sqrt N / (A ^ 3 / Real.sqrt c) ≤ k := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hp : delta⁻¹ ^ 6 ≤ A ^ 6 := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 6
  have hr : k ^ 2 / delta ^ 6 ≤ k ^ 2 * A ^ 6 := by
    calc
      _ = k ^ 2 * (delta⁻¹ ^ 6) := by simp only [inv_pow, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (sq_nonneg k)
  have hsq : (Real.sqrt c * Real.sqrt N) ^ 2 ≤ (k * A ^ 3) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hN]
    nlinarith [hquery.trans hr]
  have hroot : Real.sqrt c * Real.sqrt N ≤ k * A ^ 3 := by
    nlinarith [mul_nonneg hk (pow_nonneg hA.le 3),
      mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg N)]
  apply (div_le_iff₀ (div_pos (pow_pos hA 3) hs)).2
  have hdiv : Real.sqrt N ≤ k * A ^ 3 / Real.sqrt c :=
    (le_div_iff₀ hs).2 (by simpa only [mul_comm] using hroot)
  simpa only [mul_div_assoc] using hdiv

 theorem inverse_polynomial_bound (c N k delta B x : ℝ) (d : ℕ)
    (hc : 0 < c) (hN : 0 ≤ N) (hk : 0 ≤ k) (hd : 0 < delta)
    (hB : 0 < B) (hx : 0 < x)
    (hquery : c * N ≤ k ^ 2 / delta ^ 6) (hinv : delta⁻¹ ≤ B * x ^ d) :
    Real.sqrt N / (B ^ 3 / Real.sqrt c * x ^ (3 * d)) ≤ k := by
  have hh := inverse_bound c N k delta (B * x ^ d) hc hN hk hd
    (mul_pos hB (pow_pos hx d)) hquery hinv
  have he : (B * x ^ d) ^ 3 / Real.sqrt c =
      B ^ 3 / Real.sqrt c * x ^ (3 * d) := by
    rw [mul_pow, ← pow_mul]
    simp only [Nat.mul_comm d 3]
    ring
  simpa only [he] using hh

end RandomOracleUnitarySynthesis.QueryNumerics

/- Module RandomOracleMain -/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace RandomOracleUnitarySynthesis
open Matrix Finset Classical MeasureTheory Filter
open scoped ENNReal

/-- Exact original Theorem4.1, including arbitrary real nonnegative
inverse-polynomial degree and all eventually admissible circuit families. -/
theorem synthesis_query_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (m m₀ k : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n)) (ε : ℕ → ℝ),
      synthesis_Admissible m m₀ k C ε → synthesis_GapRegime ε →
      (∀ᶠ n : ℕ in atTop, c * (2 : ℝ)^n ≤ (k n : ℝ)^2 * ((1-ε n)⁻¹)^6) ∧
      (∀ B d : ℝ, 0 < B → 0 ≤ d → synthesis_PolynomialGap ε B d →
        ∃ B' d' : ℝ, 0 < B' ∧ 0 ≤ d' ∧
          ∀ᶠ n : ℕ in atTop, Real.sqrt ((2 : ℝ)^n) /
            (B' * Real.rpow ((n : ℝ)+1) d') ≤ (k n : ℝ)) := by
  obtain ⟨c,hc,hcore⟩:=synthesis_query_bound_core
  refine ⟨c,hc,?_⟩
  intro m m₀ k C ε hAdm hGap
  have hfirst:=hcore m m₀ k C ε hAdm hGap
  refine ⟨hfirst,?_⟩
  intro B d hB hd hpoly
  have hs:0<Real.sqrt c:=Real.sqrt_pos.mpr hc
  refine ⟨B^3/Real.sqrt c,3*d,by positivity,mul_nonneg (by norm_num) hd,?_⟩
  filter_upwards [hAdm,hfirst,hpoly] with n hA hquery hinv
  have hδ:0<1-ε n:=sub_pos.mpr hA.2.1
  have hx:0<(n:ℝ)+1:=by positivity
  have hr:0<Real.rpow ((n:ℝ)+1) d:=Real.rpow_pos_of_pos hx d
  have hq:c*(2:ℝ)^n ≤ (k n:ℝ)^2/(1-ε n)^6 := by
    simpa only [inv_pow,div_eq_mul_inv] using hquery
  have hh:=QueryNumerics.inverse_bound c ((2:ℝ)^n) (k n:ℝ) (1-ε n)
    (B*Real.rpow ((n:ℝ)+1) d) hc (by positivity) (by positivity) hδ (mul_pos hB hr) hq hinv
  have hp:(Real.rpow ((n:ℝ)+1) d)^3=Real.rpow ((n:ℝ)+1) (3*d) := by
    simp only [Real.rpow_eq_pow]
    rw [←Real.rpow_mul_natCast hx.le d 3]
    congr 1
    norm_num
    ring
  have he:(B*Real.rpow ((n:ℝ)+1) d)^3/Real.sqrt c=
      (B^3/Real.sqrt c)*Real.rpow ((n:ℝ)+1) (3*d) := by
    rw [mul_pow,hp]
    ring
  simpa only [he] using hh

end RandomOracleUnitarySynthesis

open RandomOracleUnitarySynthesis Filter

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (m m₀ k : ℕ → ℕ)
      (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n)) (ε : ℕ → ℝ),
      synthesis_Admissible m m₀ k C ε → synthesis_GapRegime ε →
      (∀ᶠ n : ℕ in atTop, c * (2 : ℝ)^n ≤ (k n : ℝ)^2 * ((1-ε n)⁻¹)^6) ∧
      (∀ B d : ℝ, 0 < B → 0 ≤ d → synthesis_PolynomialGap ε B d →
        ∃ B' d' : ℝ, 0 < B' ∧ 0 ≤ d' ∧
          ∀ᶠ n : ℕ in atTop, Real.sqrt ((2 : ℝ)^n) /
            (B' * Real.rpow ((n : ℝ)+1) d') ≤ (k n : ℝ)) :=
  RandomOracleUnitarySynthesis.synthesis_query_bound 
