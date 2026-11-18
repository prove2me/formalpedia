-- Prove2me | solution 1 for RandomOracleUnitarySynthesis.synthesis_dirty_pauli_overlap
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T19:51:23.102749+00:00
-- url     : https://prove2.me/submissions/4c0a471d-284f-462f-9ee6-d593603749e1

import Mathlib
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit
import Definitions.Def_SpaceReset_Hardness_Quantum
import Definitions.Def_DirectFidelity_State_Setting
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_resampling


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

open RandomOracleUnitarySynthesis

theorem solution {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (U : synthesis_Unitary n) :
    1 - synthesis_diamond (synthesis_actualChannel C f) (synthesis_unitaryChannel U) ≤
      synthesis_average (fun P : synthesis_Pauli n =>
        synthesis_correlation (synthesis_observable C f P) P U) :=
  RandomOracleUnitarySynthesis.synthesis_dirty_pauli_overlap C f U
