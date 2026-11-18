-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T20:16:25.156514+00:00
-- url     : https://prove2.me/submissions/4d5bc7f1-6383-43c8-95fd-0f1b62e3d678

import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_Model
import Definitions.Def_SYKFastMix_FastMixing_Operators
import Mathlib
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector
import Theorems.Thm_HighDimProb_RandomProcesses_sudakov_fernique
import Theorems.Thm_SYKFastMix_FastMixing_traceMoment_opNorm_bounds

-- Solutions.CubicTrees
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace SYKFastMix.FastMixing

inductive CubicTree where
  | leaf
  | node (a b c : CubicTree)

def CubicTree.nodes : CubicTree → ℕ
  | .leaf => 0
  | .node a b c => a.nodes+b.nodes+c.nodes+1

def CubicTree.leaves : CubicTree → ℕ
  | .leaf => 1
  | .node a b c => a.leaves+b.leaves+c.leaves

lemma CubicTree.leaves_eq (t : CubicTree) : t.leaves=2*t.nodes+1 := by
  induction t with
  | leaf => rfl
  | node a b c ha hb hc => simp only [leaves,nodes,ha,hb,hc]; omega

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (V : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ E) E)

def CubicTree.eval : CubicTree → E → E
  | .leaf, x => x
  | .node a b c, x => V ![a.eval x,b.eval x,c.eval x]

def CubicTree.differential : CubicTree → E → (E →L[ℝ] E)
  | .leaf, _ => ContinuousLinearMap.id ℝ E
  | .node a b c, x =>
    (V.linearDeriv ![a.eval V x,b.eval V x,c.eval V x]).comp
      (ContinuousLinearMap.pi ![a.differential x,b.differential x,c.differential x])

lemma CubicTree.hasFDerivAt (t : CubicTree) (x : E) :
    HasFDerivAt (t.eval V) (t.differential V x) x := by
  induction t with
  | leaf => exact hasFDerivAt_id x
  | node a b c ha hb hc =>
    have hh : HasFDerivAt (fun y ↦ ![a.eval V y,b.eval V y,c.eval V y])
        (ContinuousLinearMap.pi ![a.differential V x,b.differential V x,c.differential V x]) x := by
      apply hasFDerivAt_pi.2
      intro i
      fin_cases i
      · simpa using! ha
      · simpa using! hb
      · simpa using! hc
    exact (V.hasFDerivAt ![a.eval V x,b.eval V x,c.eval V x]).comp x hh

lemma norm_cubic_apply (a b c : E) : ‖V ![a,b,c]‖≤‖V‖*‖a‖*‖b‖*‖c‖ := by
  have hh := V.le_opNorm ![a,b,c]
  simpa only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons,Fin.prod_univ_zero,mul_one,mul_assoc] using hh

lemma cubic_differential_apply (a b c u v z : E) :
    V.linearDeriv ![a,b,c] ![u,v,z]=V ![u,b,c]+V ![a,v,c]+V ![a,b,z] := by
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  have h0 : Function.update ![a,b,c] (0 : Fin 3) (![u,v,z] 0)=![u,b,c] := by
    ext i; fin_cases i <;> simp [Function.update,Fin.ext_iff]
  have h1 : Function.update ![a,b,c] (1 : Fin 3) (![u,v,z] 1)=![a,v,c] := by
    ext i; fin_cases i <;> simp [Function.update,Fin.ext_iff]
  have h2 : Function.update ![a,b,c] (2 : Fin 3) (![u,v,z] 2)=![a,b,z] := by
    ext i; fin_cases i <;> simp [Function.update,Fin.ext_iff]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,h0,add_zero]
  change V ![u,b,c]+(V (Function.update ![a,b,c] (1 : Fin 3) (![u,v,z] 1))+
    V (Function.update ![a,b,c] (2 : Fin 3) (![u,v,z] 2)))=_
  rw [h1,h2]
  abel

lemma norm_cubic_comp_differential (a b c : E) (A B C : E →L[ℝ] E) :
    ‖(V.linearDeriv ![a,b,c]).comp (ContinuousLinearMap.pi ![A,B,C])‖≤
      ‖V‖*(‖A‖*‖b‖*‖c‖+‖a‖*‖B‖*‖c‖+‖a‖*‖b‖*‖C‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖V.linearDeriv ![a,b,c] ![A x,B x,C x]‖≤_
  rw [cubic_differential_apply]
  calc
    _ ≤ ‖V ![A x,b,c]‖+‖V ![a,B x,c]‖+‖V ![a,b,C x]‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖V‖*‖A x‖*‖b‖*‖c‖+‖V‖*‖a‖*‖B x‖*‖c‖+‖V‖*‖a‖*‖b‖*‖C x‖ := by
      exact add_le_add (add_le_add (norm_cubic_apply V _ _ _) (norm_cubic_apply V _ _ _))
        (norm_cubic_apply V _ _ _)
    _ ≤ ‖V‖*(‖A‖*‖x‖)*‖b‖*‖c‖+‖V‖*‖a‖*(‖B‖*‖x‖)*‖c‖+‖V‖*‖a‖*‖b‖*(‖C‖*‖x‖) := by
      gcongr
      · exact A.le_opNorm x
      · exact B.le_opNorm x
      · exact C.le_opNorm x
    _ = _ := by ring

lemma CubicTree.norm_eval_le (t : CubicTree) (x : E) :
    ‖t.eval V x‖≤‖V‖^t.nodes*‖x‖^t.leaves := by
  induction t with
  | leaf => simp [eval,nodes,leaves]
  | node a b c ha hb hc =>
    calc
      _ ≤ ‖V‖*‖a.eval V x‖*‖b.eval V x‖*‖c.eval V x‖ := norm_cubic_apply V _ _ _
      _ ≤ ‖V‖*(‖V‖^a.nodes*‖x‖^a.leaves)*(‖V‖^b.nodes*‖x‖^b.leaves)*
          (‖V‖^c.nodes*‖x‖^c.leaves) := by gcongr
      _ = _ := by simp only [nodes,leaves,pow_add,pow_succ]; ring

lemma CubicTree.norm_differential_le (t : CubicTree) (x : E) :
    ‖t.differential V x‖≤(t.leaves : ℝ)*‖V‖^t.nodes*‖x‖^(t.leaves-1) := by
  induction t with
  | leaf => simp [differential,nodes,leaves,ContinuousLinearMap.norm_id_le]
  | node a b c ha hb hc =>
    have hal : 1≤a.leaves := by rw [a.leaves_eq]; omega
    have hbl : 1≤b.leaves := by rw [b.leaves_eq]; omega
    have hcl : 1≤c.leaves := by rw [c.leaves_eq]; omega
    calc
      _ ≤ ‖V‖*(‖a.differential V x‖*‖b.eval V x‖*‖c.eval V x‖+
          ‖a.eval V x‖*‖b.differential V x‖*‖c.eval V x‖+
          ‖a.eval V x‖*‖b.eval V x‖*‖c.differential V x‖) :=
        norm_cubic_comp_differential V _ _ _ _ _ _
      _ ≤ ‖V‖*((((a.leaves : ℝ)*‖V‖^a.nodes*‖x‖^(a.leaves-1))*
          (‖V‖^b.nodes*‖x‖^b.leaves)*(‖V‖^c.nodes*‖x‖^c.leaves))+
          ((‖V‖^a.nodes*‖x‖^a.leaves)*((b.leaves : ℝ)*‖V‖^b.nodes*‖x‖^(b.leaves-1))*
            (‖V‖^c.nodes*‖x‖^c.leaves))+
          ((‖V‖^a.nodes*‖x‖^a.leaves)*(‖V‖^b.nodes*‖x‖^b.leaves)*
            ((c.leaves : ℝ)*‖V‖^c.nodes*‖x‖^(c.leaves-1)))) := by
        gcongr <;> apply CubicTree.norm_eval_le
      _ = _ := by
        have ha' : a.leaves=(a.leaves-1)+1 := by omega
        have hb' : b.leaves=(b.leaves-1)+1 := by omega
        have hc' : c.leaves=(c.leaves-1)+1 := by omega
        have htot : a.leaves+b.leaves+c.leaves-1=(a.leaves-1)+(b.leaves-1)+(c.leaves-1)+2 := by omega
        have hpa : ‖x‖^a.leaves=‖x‖^(a.leaves-1)*‖x‖ := by
          calc
            _=‖x‖^((a.leaves-1)+1) := congrArg (fun n ↦ ‖x‖^n) ha'
            _=_ := pow_succ _ _
        have hpb : ‖x‖^b.leaves=‖x‖^(b.leaves-1)*‖x‖ := by
          calc
            _=‖x‖^((b.leaves-1)+1) := congrArg (fun n ↦ ‖x‖^n) hb'
            _=_ := pow_succ _ _
        have hpc : ‖x‖^c.leaves=‖x‖^(c.leaves-1)*‖x‖ := by
          calc
            _=‖x‖^((c.leaves-1)+1) := congrArg (fun n ↦ ‖x‖^n) hc'
            _=_ := pow_succ _ _
        simp only [nodes,leaves,Nat.cast_add]
        rw [htot,hpa,hpb,hpc]
        simp only [pow_add,pow_succ]
        ring

end
end SYKFastMix.FastMixing

end
end


-- Solutions.NormMoments
section

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hermitian_norm_eq_eigenvalues_norm (B : Mat ι) (hB : B.IsHermitian) :
    ‖B‖ = ‖fun i ↦ (hB.eigenvalues i : ℂ)‖ := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [StarAlgEquiv.norm_map, Matrix.l2_opNorm_diagonal]
  rfl

lemma traceMoment_eq_sum_eigenvalues_pow (p : ℕ) (A : Mat ι) :
    traceMoment p A = ∑ i, ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) ^ p := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  unfold traceMoment
  conv_lhs => rw [hB.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Pi.pow_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (((hB.eigenvalues i : ℝ) : ℂ) ^ p).re = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma traceMoment_nonneg (p : ℕ) (A : Mat ι) : 0 ≤ traceMoment p A := by
  rw [traceMoment_eq_sum_eigenvalues_pow]
  exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) _

lemma opNorm_pow_le_traceMoment [Nonempty ι] (p : ℕ) (A : Mat ι) :
    SYKEdge.opNorm A ^ (2*p) ≤ traceMoment p A := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ hB.eigenvalues Finset.univ_nonempty
  have hn (j : ι) : 0 ≤ hB.eigenvalues j := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have he : ‖Aᴴ * A‖ = hB.eigenvalues i := by
    rw [hermitian_norm_eq_eigenvalues_norm _ hB]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (hn i)).mpr
      intro j
      change ‖(hB.eigenvalues j : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_of_nonneg (hn j)]
      exact hmax j (Finset.mem_univ j)
    · have h := norm_le_pi_norm (fun j ↦ (hB.eigenvalues j : ℂ)) i
      simpa only [Complex.norm_real, Real.norm_of_nonneg (hn i)] using h
  rw [traceMoment_eq_sum_eigenvalues_pow]
  calc
    SYKEdge.opNorm A ^ (2*p) = ‖Aᴴ * A‖ ^ p := by
      change ‖A‖ ^ (2*p) = _
      rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, pow_mul]
    _ = hB.eigenvalues i ^ p := by rw [he]
    _ ≤ ∑ j, hB.eigenvalues j ^ p :=
      Finset.single_le_sum (fun j _ ↦ pow_nonneg (hn j) p) (Finset.mem_univ i)

lemma traceMoment_le_card_mul_opNorm_pow (p : ℕ) (A : Mat ι) :
    traceMoment p A ≤ (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  have hn (j : ι) : 0 ≤ hB.eigenvalues j := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have he (j : ι) : hB.eigenvalues j ≤ ‖Aᴴ * A‖ := by
    rw [hermitian_norm_eq_eigenvalues_norm _ hB]
    have h := norm_le_pi_norm (fun j ↦ (hB.eigenvalues j : ℂ)) j
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hn j)] using h
  rw [traceMoment_eq_sum_eigenvalues_pow]
  calc
    ∑ j, hB.eigenvalues j ^ p ≤ ∑ _ : ι, ‖Aᴴ * A‖ ^ p :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ (hn j) (he j) p)
    _ = (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      change ‖Aᴴ * A‖ ^ p = ‖A‖ ^ (2*p)
      rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, pow_mul]

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing


end
end


-- Solutions.MatrixScratch
section

noncomputable section
open scoped Matrix.Norms.L2Operator
open scoped ComplexConjugate
open Matrix
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def opVec (X : Mat ι) : ι × ι → ℂ := fun p => X p.1 p.2

lemma opVec_eq_zero_iff (X : Mat ι) : opVec X = 0 ↔ X = 0 := by
  constructor
  · intro h
    ext a b
    have hab := congrFun h (a, b)
    exact hab
  · rintro rfl
    rfl

lemma hsInner_eq_dotProduct (X Y : Mat ι) :
    hsInner X Y = star (opVec X) ⬝ᵥ opVec Y := by
  simp only [hsInner, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diag, dotProduct, opVec, Fintype.sum_prod_type]
  change (∑ i, ∑ j, star (X j i) * Y j i) =
    ∑ i, ∑ j, star (X i j) * Y i j
  rw [Finset.sum_comm]

lemma opVec_applySuper (T : Super ι) (X : Mat ι) :
    opVec (applySuper T X) = T *ᵥ opVec X := rfl

lemma hsInner_adj_mul (T : Super ι) (X : Mat ι) :
    hsInner X (applySuper (Tᴴ * T) X) = hsInner (applySuper T X) (applySuper T X) := by
  rw [hsInner_eq_dotProduct, hsInner_eq_dotProduct]
  rw [opVec_applySuper, opVec_applySuper]
  change star (opVec X) ⬝ᵥ ((Tᴴ * T) *ᵥ opVec X) =
    star (T *ᵥ opVec X) ⬝ᵥ (T *ᵥ opVec X)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  rw [star_star]

lemma qform_adj_mul (T : Super ι) (X : Mat ι) :
    qform (Tᴴ * T) X = hsSq (applySuper T X) := by
  exact congrArg Complex.re (hsInner_adj_mul T X)

lemma qform_sum_adj_mul {I : Type} [Fintype I] (T : I → Super ι) (X : Mat ι) :
    qform (∑ i, (T i)ᴴ * T i) X = ∑ i, hsSq (applySuper (T i) X) := by
  rw [qform, hsInner_eq_dotProduct, opVec_applySuper]
  rw [show (∑ i, (T i)ᴴ * T i) *ᵥ opVec X =
      ∑ i, ((T i)ᴴ * T i) *ᵥ opVec X by
    simpa using Matrix.sum_mulVec Finset.univ (fun i ↦ (T i)ᴴ * T i) (opVec X)]
  rw [dotProduct_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsSq, ← hsInner_adj_mul]
  rw [hsInner_eq_dotProduct, opVec_applySuper]

lemma hsSq_eq_sum_norm_sq (X : Mat ι) :
    hsSq X = ∑ p : ι × ι, ‖opVec X p‖ ^ 2 := by
  rw [hsSq, hsInner_eq_dotProduct]
  simp only [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Complex.sq_norm]
  change (conj (opVec X p) * opVec X p).re = Complex.normSq (opVec X p)
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

lemma hsSq_nonneg (X : Mat ι) : 0 ≤ hsSq X := by
  rw [hsSq_eq_sum_norm_sq]
  positivity

lemma hsSq_eq_zero_iff (X : Mat ι) : hsSq X = 0 ↔ X = 0 := by
  rw [hsSq_eq_sum_norm_sq]
  constructor
  · intro h
    have hzfun : (fun p : ι × ι ↦ ‖opVec X p‖ ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)).mp h
    have hz : ∀ p : ι × ι, ‖opVec X p‖ ^ 2 = 0 := fun p ↦ congrFun hzfun p
    ext a b
    have hab := hz (a, b)
    simp only [sq_eq_zero_iff, norm_eq_zero] at hab
    exact hab
  · rintro rfl
    simp [opVec]

lemma applySuper_sum_adj_mul_eq_zero_iff {I : Type} [Fintype I]
    (T : I → Super ι) (X : Mat ι) :
    applySuper (∑ i, (T i)ᴴ * T i) X = 0 ↔ ∀ i, applySuper (T i) X = 0 := by
  constructor
  · intro h i
    have hq : qform (∑ i, (T i)ᴴ * T i) X = 0 := by
      simp [qform, h, hsInner, applySuper]
    rw [qform_sum_adj_mul] at hq
    have hifun : (fun j ↦ hsSq (applySuper (T j) X)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun j ↦ hsSq_nonneg _)).mp hq
    have hi : hsSq (applySuper (T i) X) = 0 := congrFun hifun i
    exact (hsSq_eq_zero_iff _).mp hi
  · intro h
    apply (opVec_eq_zero_iff _).mp
    rw [opVec_applySuper]
    rw [show (∑ i, (T i)ᴴ * T i) *ᵥ opVec X =
        ∑ i, ((T i)ᴴ * T i) *ᵥ opVec X by
      simpa using Matrix.sum_mulVec Finset.univ (fun i ↦ (T i)ᴴ * T i) (opVec X)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Matrix.mulVec_mulVec, ← opVec_applySuper, h i]
    change (T i)ᴴ *ᵥ (0 : ι × ι → ℂ) = 0
    exact Matrix.mulVec_zero _

def familyVec {I : Type} (F : I → Mat ι) : EuclideanSpace ℂ (I × (ι × ι)) :=
  WithLp.toLp 2 (fun p ↦ opVec (F p.1) p.2)

lemma familyVec_sub {I : Type} (F G : I → Mat ι) :
    familyVec (fun i ↦ F i - G i) = familyVec F - familyVec G := by
  apply PiLp.ext
  intro p
  rfl

lemma familyVec_add {I : Type} (F G : I → Mat ι) :
    familyVec (fun i ↦ F i + G i) = familyVec F + familyVec G := by
  apply PiLp.ext
  intro p
  rfl

lemma familyVec_eq_zero_iff {I : Type} (F : I → Mat ι) :
    familyVec F = 0 ↔ ∀ i, F i = 0 := by
  constructor
  · intro h i
    ext a b
    have hp := congrArg (fun v : EuclideanSpace ℂ (I × (ι × ι)) ↦ v (i, (a, b))) h
    exact hp
  · intro h
    apply PiLp.ext
    intro p
    change opVec (F p.1) p.2 = 0
    rw [h p.1]
    rfl

lemma familyVec_norm_sq {I : Type} [Fintype I] (F : I → Mat ι) :
    ‖familyVec F‖ ^ 2 = ∑ i, hsSq (F i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [familyVec, hsSq_eq_sum_norm_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product]

lemma familyVec_norm {I : Type} [Fintype I] (F : I → Mat ι) :
    ‖familyVec F‖ = Real.sqrt (∑ i, hsSq (F i)) := by
  rw [← familyVec_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

end SYKFastMix.FastMixing

end
end


-- Solutions.TraceNormBounds
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hsSq_eq_traceMoment_one (X : Mat ι) : hsSq X = traceMoment 1 X := by
  simp [hsSq, hsInner, traceMoment]

lemma traceNorm_nonneg (X : Mat ι) : 0 ≤ traceNorm X := by
  unfold traceNorm
  positivity

lemma traceNorm_le_sqrt_card_mul_hs (X : Mat ι) :
    traceNorm X ≤ Real.sqrt (Fintype.card ι : ℝ) * hs X := by
  let ev := (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues
  have hev (i : ι) : 0 ≤ ev i := Matrix.eigenvalues_conjTranspose_mul_self_nonneg X i
  have hsum : hsSq X = ∑ i, ev i := by
    rw [hsSq_eq_traceMoment_one, traceMoment_eq_sum_eigenvalues_pow]
    simp [ev]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : ι ↦ Real.sqrt (ev i))
  simp only [Finset.card_univ, Real.sq_sqrt (hev _)] at h
  have he : (Real.sqrt (Fintype.card ι : ℝ) * hs X)^2 = (Fintype.card ι : ℝ) * hsSq X := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hs, Real.sq_sqrt (hsSq_nonneg X)]
  apply (sq_le_sq₀ (traceNorm_nonneg X) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  change (traceNorm X)^2 ≤ (Real.sqrt (Fintype.card ι : ℝ) * hs X)^2
  rw [he, hsum]
  exact h

lemma hsSq_hermitian_eq_sum_eigenvalues_sq (X : Mat ι) (hX : X.IsHermitian) :
    hsSq X = ∑ i, (hX.eigenvalues i)^2 := by
  unfold hsSq hsInner
  rw [hX.eq]
  conv_lhs => rw [hX.spectral_theorem, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Function.comp_apply, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change ((hX.eigenvalues i : ℂ) * (hX.eigenvalues i : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

lemma density_hsSq_le_one (X : Mat ι) (hX : IsDensity X) : hsSq X ≤ 1 := by
  have hpos := hX.1
  have hherm := hpos.isHermitian
  have hsum : (∑ i, hherm.eigenvalues i) = (1 : ℝ) := by
    have h := hherm.trace_eq_sum_eigenvalues
    rw [hX.2] at h
    have hre := congrArg Complex.re h
    simpa using hre.symm
  rw [hsSq_hermitian_eq_sum_eigenvalues_sq X hherm]
  calc
    _ ≤ (∑ i, hherm.eigenvalues i)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i hi ↦ hpos.eigenvalues_nonneg i)
    _ = 1 := by rw [hsum]; norm_num

lemma hsSq_eq_sum_columns (X : Mat ι) : hsSq X = ∑ j, ∑ i, ‖X i j‖^2 := by
  rw [hsSq_eq_sum_norm_sq]
  simp only [opVec, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma hsSq_mul_left_le (A X : Mat ι) : hsSq (A*X) ≤ ‖A‖^2 * hsSq X := by
  have hcol (j : ι) : (∑ i, ‖(A*X) i j‖^2) ≤ ‖A‖^2 * ∑ i, ‖X i j‖^2 := by
    let x : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i ↦ X i j)
    have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm x
    have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow] at h'
    change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x‖^2 ≤ ‖A‖^2 * ‖x‖^2 at h'
    convert! h' using 1
    · simp only [EuclideanSpace.norm_sq_eq, x, Matrix.toEuclideanCLM_toLp,
        WithLp.ofLp_toLp, Matrix.mulVec, Matrix.mul_apply, dotProduct]
    · simp only [EuclideanSpace.norm_sq_eq, x, WithLp.ofLp_toLp]
  rw [hsSq_eq_sum_columns, hsSq_eq_sum_columns, Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj ↦ hcol j

lemma hsSq_conjTranspose (X : Mat ι) : hsSq Xᴴ = hsSq X := by
  rw [hsSq_eq_sum_columns, hsSq_eq_sum_columns]
  simp only [Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

lemma hsSq_mul_right_le (X A : Mat ι) : hsSq (X*A) ≤ ‖A‖^2 * hsSq X := by
  have h := hsSq_mul_left_le Aᴴ Xᴴ
  simpa only [← Matrix.conjTranspose_mul, hsSq_conjTranspose, Matrix.l2_opNorm_conjTranspose] using h

lemma hs_mul_left_le (A X : Mat ι) : hs (A*X) ≤ ‖A‖ * hs X := by
  have h := hsSq_mul_left_le A X
  have he (Y : Mat ι) : (hs Y)^2 = hsSq Y := Real.sq_sqrt (hsSq_nonneg Y)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  change (hs (A*X))^2 ≤ (‖A‖ * hs X)^2
  rw [mul_pow, he, he]
  exact h

lemma hs_mul_right_le (X A : Mat ι) : hs (X*A) ≤ hs X * ‖A‖ := by
  have h := hs_mul_left_le Aᴴ Xᴴ
  have he (Y : Mat ι) : hs Yᴴ = hs Y := by rw [hs, hsSq_conjTranspose]; rfl
  simpa only [← Matrix.conjTranspose_mul, he, Matrix.l2_opNorm_conjTranspose, mul_comm] using h

lemma hsInner_sub_left (X Y Z : Mat ι) : hsInner (X-Y) Z = hsInner X Z - hsInner Y Z := by
  simp [hsInner, Matrix.conjTranspose_sub, sub_mul]

lemma hsInner_sub_right (X Y Z : Mat ι) : hsInner X (Y-Z) = hsInner X Y - hsInner X Z := by
  simp [hsInner, mul_sub]

lemma hsInner_smul_left (z : ℂ) (X Y : Mat ι) : hsInner (z • X) Y = conj z * hsInner X Y := by
  simp [hsInner, Matrix.conjTranspose_smul, smul_mul_assoc]

lemma hsInner_smul_right (z : ℂ) (X Y : Mat ι) : hsInner X (z • Y) = z * hsInner X Y := by
  simp [hsInner, mul_smul_comm]

lemma hsInner_conj_symm (X Y : Mat ι) : hsInner X Y = conj (hsInner Y X) := by
  unfold hsInner
  change (Xᴴ * Y).trace = star ((Yᴴ * X).trace)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma hsInner_self_real (X : Mat ι) : hsInner X X = (hsSq X : ℂ) := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (hsInner_conj_symm X X)
    simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

lemma hs_projection_bound (R W : Mat ι) (Z : ℝ) (hZ : 0 < Z)
    (hRR : hsSq R = Z) (hRW : hsInner R W = 1) :
    hsInner R (W - (Z⁻¹ : ℂ) • R) = 0 ∧ hsSq (W - (Z⁻¹ : ℂ) • R) ≤ hsSq W := by
  have hR : hsInner R R = (Z : ℂ) := by rw [hsInner_self_real, hRR]
  have hWR : hsInner W R = 1 := by rw [hsInner_conj_symm, hRW]; simp
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  constructor
  · rw [hsInner_sub_right, hsInner_smul_right, hRW, hR]
    simp [hZc]
  · have he : hsInner (W - (Z⁻¹ : ℂ) • R) (W - (Z⁻¹ : ℂ) • R) =
        hsInner W W - (Z⁻¹ : ℂ) := by
      simp only [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left, hsInner_smul_right,
        hRW, hWR, hR, Complex.conj_ofReal, Complex.ofReal_inv]
      field_simp
      <;> ring
    unfold hsSq
    rw [he, Complex.sub_re, ← Complex.ofReal_inv, Complex.ofReal_re]
    exact sub_le_self _ (inv_nonneg.mpr hZ.le)

end SYKFastMix.FastMixing

end
end


-- Solutions.OperatorCalculus
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def act (T : Super ι) : Mat ι →L[ℂ] Mat ι where
  toFun := applySuper T
  map_add' X Y := by ext a b; simp [applySuper, mul_add, Finset.sum_add_distrib]
  map_smul' z X := by ext a b; simp [applySuper, Finset.mul_sum, mul_left_comm]
  cont := by unfold applySuper; fun_prop

@[simp] lemma act_apply (T : Super ι) (X : Mat ι) : act T X = applySuper T X := rfl

lemma applySuper_mul (T U : Super ι) (X : Mat ι) :
    applySuper (T * U) X = applySuper T (applySuper U X) := by
  ext a b
  simp only [applySuper, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

def actAlgHom : Super ι →ₐ[ℂ] (Mat ι →L[ℂ] Mat ι) where
  toFun := act
  map_one' := by ext X a b; simp [act, applySuper, Matrix.one_apply]
  map_mul' T U := by ext1 X; exact applySuper_mul T U X
  map_zero' := by ext X a b; simp [act, applySuper]
  map_add' T U := by ext X a b; simp [act, applySuper, add_mul, Finset.sum_add_distrib]
  commutes' z := by
    ext X a b
    simp [act, applySuper, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

lemma act_exp (T : Super ι) : act (mexp T) = NormedSpace.exp (act T) := by
  letI : NormedAlgebra ℚ (Super ι) := .restrictScalars ℚ ℂ (Super ι)
  exact NormedSpace.map_exp (actAlgHom (ι := ι))
    (actAlgHom (ι := ι)).toLinearMap.continuous_of_finiteDimensional T

lemma applySuper_super (f : Mat ι →ₗ[ℂ] Mat ι) (X : Mat ι) :
    applySuper (super f) X = f X := by
  ext a b
  change (∑ p : ι × ι, f (Matrix.single p.1 p.2 1) a b * X p.1 p.2) = f X a b
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by simp]
  rw [map_smul]
  change _ = X i j * f (Matrix.single i j 1) a b
  exact mul_comm _ _

def evalSuper (X : Mat ι) : Super ι →L[ℂ] Mat ι where
  toFun := fun T ↦ applySuper T X
  map_add' T U := by ext a b; simp [applySuper, add_mul, Finset.sum_add_distrib]
  map_smul' z T := by ext a b; simp [applySuper, Finset.mul_sum, mul_assoc]
  cont := by unfold applySuper; fun_prop

@[simp] lemma evalSuper_apply (X : Mat ι) (T : Super ι) : evalSuper X T = applySuper T X := rfl

lemma applySuper_smul (z : ℂ) (T : Super ι) (X : Mat ι) :
    applySuper (z • T) X = z • applySuper T X := (evalSuper X).map_smul z T

def leftAct (H : Mat ι) : Mat ι →L[ℂ] Mat ι := ContinuousLinearMap.mul ℂ (Mat ι) H
def rightAct (H : Mat ι) : Mat ι →L[ℂ] Mat ι := (ContinuousLinearMap.mul ℂ (Mat ι)).flip H

@[simp] lemma leftAct_apply (H X : Mat ι) : leftAct H X = H * X := rfl
@[simp] lemma rightAct_apply (H X : Mat ι) : rightAct H X = X * H := rfl

lemma act_ad (H : Mat ι) : act (ad H) = leftAct H - rightAct H := by
  ext1 X
  exact applySuper_super (leftAct H - rightAct H).toLinearMap X

lemma act_smul (s : ℂ) (T : Super ι) : act (s • T) = s • act T :=
  (actAlgHom (ι := ι)).toLinearMap.map_smul s T

lemma leftAct_smul (s : ℂ) (H : Mat ι) : leftAct (s • H) = s • leftAct H := by
  ext1 X
  simp only [leftAct_apply, _root_.smul_apply, smul_mul_assoc]

lemma rightAct_smul (s : ℂ) (H : Mat ι) : rightAct (s • H) = s • rightAct H := by
  ext1 X
  simp only [rightAct_apply, _root_.smul_apply, mul_smul_comm]

lemma leftAct_pow_apply (H X : Mat ι) (n : ℕ) : (leftAct H ^ n) X = H^n * X := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ']; simp [ih, mul_assoc]

lemma rightAct_pow_apply (H X : Mat ι) (n : ℕ) : (rightAct H ^ n) X = X * H^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ]; simp [ih, mul_assoc]

lemma exp_leftAct_apply (H X : Mat ι) : NormedSpace.exp (leftAct H) X = mexp H * X := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (leftAct H)).mapL
    (ContinuousLinearMap.apply ℂ (Mat ι) X)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL (rightAct X)
  apply HasSum.unique h1
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    leftAct_pow_apply, rightAct_apply, smul_mul_assoc, mexp] using h2

lemma exp_rightAct_apply (H X : Mat ι) : NormedSpace.exp (rightAct H) X = X * mexp H := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (rightAct H)).mapL
    (ContinuousLinearMap.apply ℂ (Mat ι) X)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL (leftAct X)
  apply HasSum.unique h1
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    rightAct_pow_apply, leftAct_apply, mul_smul_comm, mexp] using h2

lemma exp_ad_apply (H X : Mat ι) (s : ℂ) :
    applySuper (mexp (s • ad H)) X = mexp (s • H) * X * mexp ((-s) • H) := by
  letI : NormedAlgebra ℚ (Mat ι →L[ℂ] Mat ι) :=
    .restrictScalars ℚ ℂ (Mat ι →L[ℂ] Mat ι)
  have he : act (s • ad H) = leftAct (s • H) + rightAct ((-s) • H) := by
    rw [act_smul, act_ad, leftAct_smul, rightAct_smul]
    module
  have hcomm : Commute (leftAct (s • H)) (rightAct ((-s) • H)) := by
    apply ContinuousLinearMap.ext
    intro X
    change (s • H) * (X * ((-s) • H)) = ((s • H) * X) * ((-s) • H)
    exact (mul_assoc _ _ _).symm
  rw [← act_apply, act_exp, he]
  have hexp := NormedSpace.exp_add_of_commute (𝔸 := Mat ι →L[ℂ] Mat ι) hcomm
  have happ := congrArg (fun f : Mat ι →L[ℂ] Mat ι ↦ f X) hexp
  calc
    (NormedSpace.exp (leftAct (s • H) + rightAct ((-s) • H))) X =
        (NormedSpace.exp (leftAct (s • H)) * NormedSpace.exp (rightAct ((-s) • H))) X := happ
    _ = _ := by
      change NormedSpace.exp (leftAct (s • H)) (NormedSpace.exp (rightAct ((-s) • H)) X) = _
      rw [exp_leftAct_apply, exp_rightAct_apply]
      exact (mul_assoc _ _ _).symm

end SYKFastMix.FastMixing

end
end


-- Solutions.CliffordWords
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma gamma_mul_word {N : ℕ} (Q : Model N) (j : Fin N) (l : List (Fin N)) :
    Q.γ j * (l.map Q.γ).prod =
      (-1 : ℂ)^((l.filter (· != j)).length) • ((l.map Q.γ).prod * Q.γ j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    let c : ℂ := if i=j then 1 else -1
    have hs : Q.γ j * Q.γ i = c • (Q.γ i * Q.γ j) := by
      by_cases hij : i=j
      · simp [c, hij]
      · simpa [c, hij] using Q.car.anticomm j i (Ne.symm hij)
    have hcount : (-1 : ℂ)^(((i::l).filter (· != j)).length) = c * (-1 : ℂ)^((l.filter (· != j)).length) := by
      by_cases hij : i=j <;> simp [c, hij, pow_succ, mul_comm]
    simp only [List.map_cons, List.prod_cons]
    calc
      Q.γ j * (Q.γ i * (l.map Q.γ).prod) = (Q.γ j * Q.γ i) * (l.map Q.γ).prod := by rw [mul_assoc]
      _ = c • (Q.γ i * (Q.γ j * (l.map Q.γ).prod)) := by rw [hs, smul_mul_assoc, mul_assoc]
      _ = c • (Q.γ i * ((-1 : ℂ)^((l.filter (· != j)).length) • ((l.map Q.γ).prod * Q.γ j))) := by rw [ih]
      _ = (-1 : ℂ)^(((i::l).filter (· != j)).length) • ((Q.γ i * (l.map Q.γ).prod) * Q.γ j) := by
        rw [mul_smul_comm, smul_smul, ← hcount, mul_assoc]

lemma rawString_character {N : ℕ} (Q : Model N) (S : Finset (Fin N)) (j : Fin N) :
    Q.γ j * rawString Q S * Q.γ j = (-1 : ℂ)^((S.erase j).card) • rawString Q S := by
  have hlen : ((S.sort (· ≤ ·)).filter (· != j)).length = (S.erase j).card := by
    have hn := (S.sort_nodup (· ≤ ·)).filter (· != j)
    have he : ((S.sort (· ≤ ·)).filter (· != j)).toFinset = S.erase j := by
      ext k
      simp [and_comm]
    rw [← he]
    exact (List.toFinset_card_of_nodup hn).symm
  unfold rawString
  rw [gamma_mul_word, smul_mul_assoc, mul_assoc, Q.car.sq, mul_one, hlen]

lemma rawString_unitary_word {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    rawString Q S ∈ unitary (Mat (SiteHilbert N)) := by
  unfold rawString
  apply Submonoid.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  apply Unitary.mem_iff.mpr
  change (Q.γ i)ᴴ * Q.γ i = 1 ∧ Q.γ i * (Q.γ i)ᴴ = 1
  rw [(Q.car.herm i).eq]
  exact ⟨Q.car.sq i, Q.car.sq i⟩

lemma neg_one_pow_mod_two_injective (a b : ℕ) (h : (-1 : ℂ)^a=(-1 : ℂ)^b) :
    a%2=b%2 := by
  have he : Even a ↔ Even b := by
    by_cases ha : Even a <;> by_cases hb : Even b
    · exact iff_of_true ha hb
    · norm_num [neg_one_pow_eq_ite, ha, hb] at h
    · norm_num [neg_one_pow_eq_ite, ha, hb] at h
    · exact iff_of_false ha hb
  simp only [Nat.even_iff] at he
  omega

lemma rawString_characters_injective {N : ℕ} (hN : Even N) (S T : Finset (Fin N))
    (hchar : ∀ j, (-1 : ℂ)^((S.erase j).card)=(-1 : ℂ)^((T.erase j).card)) : S=T := by
  have hm (j : Fin N) : ((S.erase j).card)%2=((T.erase j).card)%2 :=
    neg_one_pow_mod_two_injective _ _ (hchar j)
  have hpar : S.card%2=T.card%2 := by
    by_contra hp
    have hcomp (j : Fin N) : j ∈ T ↔ j ∉ S := by
      have he := hm j
      rw [Finset.card_erase_eq_ite, Finset.card_erase_eq_ite] at he
      by_cases hs : j ∈ S <;> by_cases ht : j ∈ T
      · have hsp : 1 ≤ S.card := Finset.one_le_card.mpr ⟨j, hs⟩
        have htp : 1 ≤ T.card := Finset.one_le_card.mpr ⟨j, ht⟩
        simp only [if_pos hs, if_pos ht] at he
        omega
      · simp [hs, ht]
      · simp [hs, ht]
      · simp only [if_neg hs, if_neg ht] at he
        omega
    have hd : Disjoint S T := Finset.disjoint_left.mpr fun j hs ht ↦ (hcomp j).mp ht hs
    have hu : S ∪ T=Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hs : j ∈ S
      · exact Or.inl hs
      · exact Or.inr ((hcomp j).mpr hs)
    have hsum : S.card+T.card=N := by
      rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ, Fintype.card_fin]
    have heven := Nat.even_iff.mp hN
    omega
  ext j
  have he := hm j
  rw [Finset.card_erase_eq_ite, Finset.card_erase_eq_ite] at he
  by_cases hs : j ∈ S <;> by_cases ht : j ∈ T
  · simp [hs, ht]
  · have hsp : 1 ≤ S.card := Finset.one_le_card.mpr ⟨j, hs⟩
    simp only [if_pos hs, if_neg ht] at he
    omega
  · have htp : 1 ≤ T.card := Finset.one_le_card.mpr ⟨j, ht⟩
    simp only [if_neg hs, if_pos ht] at he
    omega
  · simp [hs, ht]

lemma rawString_orthogonal {N : ℕ} (Q : Model N) (S T : Finset (Fin N)) (hST : S ≠ T) :
    hsInner (rawString Q S) (rawString Q T)=0 := by
  obtain ⟨j, hj⟩ : ∃ j, (-1 : ℂ)^((S.erase j).card) ≠ (-1 : ℂ)^((T.erase j).card) := by
    by_contra h
    push_neg at h
    exact hST (rawString_characters_injective Q.even S T h)
  have hsign : (-1 : ℂ)^((S.erase j).card) * (-1 : ℂ)^((T.erase j).card) = -1 := by
    rcases neg_one_pow_eq_or ℂ ((S.erase j).card) with hS | hS <;>
      rcases neg_one_pow_eq_or ℂ ((T.erase j).card) with hT | hT <;> simp_all
  have hSc : Q.γ j * (rawString Q S)ᴴ * Q.γ j =
      (-1 : ℂ)^((S.erase j).card) • (rawString Q S)ᴴ := by
    have h := congrArg Matrix.conjTranspose (rawString_character Q S j)
    simpa only [Matrix.conjTranspose_mul, (Q.car.herm j).eq, Matrix.conjTranspose_smul,
      star_pow, star_neg, star_one, mul_assoc] using h
  have hconj : Q.γ j * ((rawString Q S)ᴴ * rawString Q T) * Q.γ j =
      ((-1 : ℂ)^((S.erase j).card) * (-1 : ℂ)^((T.erase j).card)) •
        ((rawString Q S)ᴴ * rawString Q T) := by
    calc
      _ = (Q.γ j * (rawString Q S)ᴴ * Q.γ j) * (Q.γ j * rawString Q T * Q.γ j) := by
        symm
        calc
          _ = (Q.γ j * (rawString Q S)ᴴ) * (Q.γ j * Q.γ j) * (rawString Q T * Q.γ j) := by noncomm_ring
          _ = _ := by rw [Q.car.sq]; noncomm_ring
      _ = _ := by rw [hSc, rawString_character, smul_mul_assoc, mul_smul_comm, smul_smul]
  have htrace := congrArg Matrix.trace hconj
  rw [Matrix.trace_mul_cycle, Q.car.sq, one_mul, Matrix.trace_smul, hsign] at htrace
  rw [neg_one_smul] at htrace
  unfold hsInner
  linear_combination (1/2 : ℂ) * htrace

lemma rawString_hsInner_self {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    hsInner (rawString Q S) (rawString Q S) = (2^(N/2) : ℂ) := by
  have h := Unitary.star_mul_self_of_mem (rawString_unitary_word Q S)
  change (rawString Q S)ᴴ * rawString Q S=1 at h
  rw [hsInner, h]
  simp [SiteHilbert]

def hsInnerLinear {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι →ₗ[ℂ] ℂ where
  toFun := hsInner X
  map_add' Y Z := by simp [hsInner, mul_add]
  map_smul' z Y := by rw [hsInner_smul_right]; rfl

lemma rawString_linearIndependent {N : ℕ} (Q : Model N) :
    LinearIndependent ℂ (rawString Q) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc T
  have h := congrArg (hsInnerLinear (rawString Q T)) hc
  simp only [map_sum, map_smul, map_zero, hsInnerLinear, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul] at h
  have he : (∑ S : Finset (Fin N), c S * hsInner (rawString Q T) (rawString Q S)) =
      c T * (2^(N/2) : ℂ) := by
    rw [Finset.sum_eq_single T]
    · rw [rawString_hsInner_self]
    · intro S hS hST
      rw [rawString_orthogonal Q T S (Ne.symm hST), mul_zero]
    · simp
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (by norm_num))

lemma clifford_dimension {N : ℕ} (Q : Model N) :
    Fintype.card (Finset (Fin N)) = Module.finrank ℂ (Mat (SiteHilbert N)) := by
  simp only [Fintype.card_finset, Fintype.card_fin, Module.finrank_matrix, Module.finrank_self,
    mul_one, SiteHilbert, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  have he := Nat.even_iff.mp Q.even
  omega

lemma rawString_span {N : ℕ} (Q : Model N) :
    Submodule.span ℂ (Set.range (rawString Q)) = ⊤ :=
  (rawString_linearIndependent Q).span_eq_top_of_card_eq_finrank' (clifford_dimension Q)

lemma majorana_commutant_scalar {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N))
    (hX : ∀ i, Commute X (Q.γ i)) : ∃ z : ℂ, X=z • (1 : Mat (SiteHilbert N)) := by
  have hraw (S : Finset (Fin N)) : Commute X (rawString Q S) := by
    apply Commute.list_prod_right
    intro Y hY
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hY
    exact hX i
  let F : Mat (SiteHilbert N) →ₗ[ℂ] Mat (SiteHilbert N) := (leftAct X-rightAct X).toLinearMap
  have hker : Submodule.span ℂ (Set.range (rawString Q)) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro Y ⟨S, rfl⟩
    change X * rawString Q S - rawString Q S * X=0
    exact sub_eq_zero.mpr (hraw S).eq
  rw [rawString_span] at hker
  have hall (Y : Mat (SiteHilbert N)) : Commute X Y := by
    have hY : Y ∈ F.ker := hker (by trivial)
    change X*Y-Y*X=0 at hY
    exact sub_eq_zero.mp hY
  obtain ⟨z, hz⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr (fun i j ↦ (hall (Matrix.single i j 1)).symm)
  refine ⟨z, ?_⟩
  rw [← hz]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

lemma word_conjTranspose {N : ℕ} (Q : Model N) (l : List (Fin N)) (hl : l.Nodup) :
    ((l.map Q.γ).prod)ᴴ = (-1 : ℂ)^(l.length.choose 2) • (l.map Q.γ).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hin : i ∉ l := (List.nodup_cons.mp hl).1
    have hnodup : l.Nodup := (List.nodup_cons.mp hl).2
    have hfilter : l.filter (· != i)=l := by
      apply List.filter_eq_self.mpr
      intro j hj
      simp only [bne_iff_ne]
      exact fun h ↦ hin (h ▸ hj)
    have hm := gamma_mul_word Q i l
    rw [hfilter] at hm
    have hs : (-1 : ℂ)^l.length * (-1 : ℂ)^l.length=1 := by
      rcases neg_one_pow_eq_or ℂ l.length with h | h <;> simp [h]
    have hmove : (l.map Q.γ).prod * Q.γ i = (-1 : ℂ)^l.length • (Q.γ i * (l.map Q.γ).prod) := by
      rw [hm, smul_smul, hs, one_smul]
    simp only [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, (Q.car.herm i).eq,
      List.length_cons]
    rw [ih hnodup, smul_mul_assoc, hmove, smul_smul, ← pow_add]
    congr 1
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

lemma rawString_conjTranspose {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    (rawString Q S)ᴴ = (-1 : ℂ)^(S.card.choose 2) • rawString Q S := by
  have h := word_conjTranspose Q (S.sort (· ≤ ·)) (S.sort_nodup (· ≤ ·))
  simpa [rawString] using h

lemma rawString_mul_self {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    rawString Q S * rawString Q S = (-1 : ℂ)^(S.card.choose 2) • (1 : Mat (SiteHilbert N)) := by
  have h := Unitary.star_mul_self_of_mem (rawString_unitary_word Q S)
  change (rawString Q S)ᴴ * rawString Q S=1 at h
  have hs : (-1 : ℂ)^(S.card.choose 2) * (-1 : ℂ)^(S.card.choose 2)=1 := by
    rcases neg_one_pow_eq_or ℂ (S.card.choose 2) with h | h <;> simp [h]
  have he := congrArg (fun A : Mat (SiteHilbert N) ↦ (-1 : ℂ)^(S.card.choose 2) • A) h
  rwa [rawString_conjTranspose, smul_mul_assoc, smul_smul, hs, one_smul] at he

lemma half_add_choose_two_even {N : ℕ} (hN : Even N) : Even (N/2 + N.choose 2) := by
  rcases hN with ⟨k, rfl⟩
  have hhalf : (k+k)/2=k := by omega
  rw [hhalf, Nat.choose_two_right]
  have hc : (k+k)*(k+k-1)/2 = k*(k+k-1) := by
    rw [show (k+k)*(k+k-1)=k*(k+k-1)*2 by ring, Nat.mul_div_left]
    norm_num
  rw [hc]
  by_cases hk : k=0
  · simp [hk]
  · have hpos : 1 ≤ k+k := by omega
    have hsub := Nat.sub_add_cancel hpos
    refine ⟨k*k, ?_⟩
    nlinarith

lemma parityMatrix_sq {N : ℕ} (Q : Model N) : parityMatrix Q * parityMatrix Q=1 := by
  unfold parityMatrix
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, rawString_mul_self, smul_smul]
  simp only [Finset.card_univ, Fintype.card_fin]
  have hi : Complex.I^(N/2) * Complex.I^(N/2) = (-1 : ℂ)^(N/2) := by
    rw [← mul_pow, Complex.I_mul_I]
  rw [hi, ← pow_add, (half_add_choose_two_even Q.even).neg_one_pow, one_smul]

lemma parityMatrix_anticomm {N : ℕ} (Q : Model N) (i : Fin N) :
    Q.γ i * parityMatrix Q = -(parityMatrix Q * Q.γ i) := by
  have hodd : Odd (N-1) := by
    apply Nat.odd_iff.mpr
    have he := Nat.even_iff.mp Q.even
    have hs := Q.size
    omega
  have h := rawString_character Q Finset.univ i
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    hodd.neg_one_pow, neg_one_smul] at h
  have hm := congrArg (fun A : Mat (SiteHilbert N) ↦ A * Q.γ i) h
  have hr : Q.γ i * rawString Q Finset.univ = -(rawString Q Finset.univ * Q.γ i) := by
    simpa only [mul_assoc, Q.car.sq, mul_one, neg_mul] using hm
  unfold parityMatrix
  rw [mul_smul_comm, hr, smul_neg, smul_mul_assoc]

lemma parity_mul {N : ℕ} (Q : Model N) (X Y : Mat (SiteHilbert N)) :
    parity Q (X*Y)=parity Q X * parity Q Y := by
  unfold parity
  symm
  calc
    _ = (parityMatrix Q * X) * (parityMatrix Q * parityMatrix Q) * (Y * parityMatrix Q) := by noncomm_ring
    _ = _ := by rw [parityMatrix_sq]; noncomm_ring

lemma parity_involution {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N)) :
    parity Q (parity Q X)=X := by
  unfold parity
  calc
    _ = (parityMatrix Q * parityMatrix Q) * X * (parityMatrix Q * parityMatrix Q) := by noncomm_ring
    _ = _ := by rw [parityMatrix_sq, one_mul, mul_one]

lemma parity_gamma {N : ℕ} (Q : Model N) (i : Fin N) : parity Q (Q.γ i) = -Q.γ i := by
  unfold parity
  have h := parityMatrix_anticomm Q i
  calc
    _ = -(Q.γ i * parityMatrix Q) * parityMatrix Q := by rw [h, neg_neg]
    _ = _ := by rw [neg_mul, mul_assoc, parityMatrix_sq, mul_one]

lemma parityMatrix_hermitian {N : ℕ} (Q : Model N) : (parityMatrix Q).IsHermitian := by
  have hu := Unitary.star_mul_self_of_mem (rawString_unitary_word Q Finset.univ)
  change (rawString Q Finset.univ)ᴴ * rawString Q Finset.univ=1 at hu
  have hunit : (parityMatrix Q)ᴴ * parityMatrix Q=1 := by
    unfold parityMatrix
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hu]
    simp only [star_pow, ← mul_pow]
    have hi : star Complex.I * Complex.I=1 := by simp [Complex.conj_I, Complex.I_mul_I]
    rw [hi, one_pow, one_smul]
  have h := congrArg (fun A : Mat (SiteHilbert N) ↦ A * parityMatrix Q) hunit
  rw [mul_assoc, parityMatrix_sq, mul_one, one_mul] at h
  exact h

end SYKFastMix.FastMixing

end
end


-- Solutions.WordDifferentiation
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def realWord (l : List (Fin N)) (x : Fin N → ℝ) : ℝ := (l.map x).prod
def cliffordWord (Q : Model N) (l : List (Fin N)) : Mat (SiteHilbert N) := (l.map Q.γ).prod

def wordDifferential : List (Fin N) → (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] ℝ)
  | [], _ => 0
  | a::l, x => x a • wordDifferential l x+realWord l x • ContinuousLinearMap.proj a

lemma realWord_hasFDerivAt (l : List (Fin N)) (x : Fin N → ℝ) :
    HasFDerivAt (realWord l) (wordDifferential l x) x := by
  induction l with
  | nil =>
    change HasFDerivAt (fun _ : Fin N → ℝ ↦ (1 : ℝ)) 0 x
    exact hasFDerivAt_const (c := (1 : ℝ)) x
  | cons a l ih =>
    change HasFDerivAt (fun y : Fin N → ℝ ↦ y a*realWord l y)
      (x a • wordDifferential l x+realWord l x • ContinuousLinearMap.proj a) x
    convert! (hasFDerivAt_apply a x).mul ih using 1

lemma coordinateDerivative_realWord (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    coordinateDerivative (realWord l) i x=wordDifferential l x (Pi.single i 1) := by
  rw [coordinateDerivative,(realWord_hasFDerivAt l x).fderiv]

def realWordPartial (i : Fin N) : List (Fin N) → (Fin N → ℝ) → ℝ
  | [], _ => 0
  | a::l, x => (if a=i then realWord l x else 0)+x a*realWordPartial i l x

lemma wordDifferential_partial (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    wordDifferential l x (Pi.single i 1)=realWordPartial i l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [wordDifferential,realWordPartial,_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.proj_apply,smul_eq_mul,ih]
    by_cases h : a=i
    · subst a; simp [add_comm]
    · simp [Pi.single_apply,h,Ne.symm h]

structure WordDeletion (N : ℕ) where
  letter : Fin N
  position : ℕ
  remainder : List (Fin N)

def wordDeletions : List (Fin N) → List (WordDeletion N)
  | [] => []
  | a::l => ⟨a,0,l⟩::(wordDeletions l).map (fun d ↦ ⟨d.letter,d.position+1,a::d.remainder⟩)

lemma realWordPartial_deletions (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    realWordPartial i l x=((wordDeletions l).map
      (fun d ↦ if d.letter=i then realWord d.remainder x else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [realWordPartial,wordDeletions,List.map_cons,List.sum_cons,List.map_map,Function.comp_apply,realWord,List.map_cons,List.prod_cons]
    rw [ih]
    congr 1
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    by_cases h : d.letter=i <;> simp [h,realWord]

def cliffordWordPartial (Q : Model N) (i : Fin N) : List (Fin N) → Mat (SiteHilbert N)
  | [] => 0
  | a::l => (if a=i then cliffordWord Q l else 0)-Q.γ a*cliffordWordPartial Q i l

lemma cliffordWord_graded_derivative (Q : Model N) (i : Fin N) (l : List (Fin N)) :
    Q.γ i*cliffordWord Q l-(-1 : ℂ)^l.length • (cliffordWord Q l*Q.γ i)=
      (2 : ℂ) • cliffordWordPartial Q i l := by
  induction l with
  | nil => simp [cliffordWord,cliffordWordPartial]
  | cons a l ih =>
    have hcar : Q.γ i*Q.γ a+Q.γ a*Q.γ i=(if a=i then (2 : ℂ) • (1 : Mat (SiteHilbert N)) else 0) := by
      by_cases ha : a=i
      · subst a; rw [Q.car.sq]; simp; module
      · rw [Q.car.anticomm i a (Ne.symm ha)]; simp [ha]
    change Q.γ i*(Q.γ a*cliffordWord Q l)-(-1 : ℂ)^(l.length+1) •
      ((Q.γ a*cliffordWord Q l)*Q.γ i)=
        (2 : ℂ) • ((if a=i then cliffordWord Q l else 0)-Q.γ a*cliffordWordPartial Q i l)
    calc
      _=(Q.γ i*Q.γ a+Q.γ a*Q.γ i)*cliffordWord Q l-
          Q.γ a*(Q.γ i*cliffordWord Q l-(-1 : ℂ)^l.length • (cliffordWord Q l*Q.γ i)) := by
        rw [pow_succ]
        simp only [mul_neg_one,neg_smul,add_mul,mul_sub,mul_smul_comm,mul_assoc]
        module
      _=_ := by
        rw [hcar,ih]
        by_cases ha : a=i <;>
          simp only [ha,ite_true,ite_false,smul_mul_assoc,one_mul,zero_mul,mul_smul_comm,smul_sub] <;> module

lemma cliffordWordPartial_deletions (Q : Model N) (l : List (Fin N)) (i : Fin N) :
    cliffordWordPartial Q i l=((wordDeletions l).map
      (fun d ↦ if d.letter=i then (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum := by
  have htail (a : Fin N) (ds : List (WordDeletion N)) :
      (ds.map (fun d ↦ if d.letter=i then (-1 : ℂ)^(d.position+1) •
        (Q.γ a*cliffordWord Q d.remainder) else 0)).sum=
      -Q.γ a*(ds.map (fun d ↦ if d.letter=i then (-1 : ℂ)^d.position • cliffordWord Q d.remainder else 0)).sum := by
    induction ds with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons,List.sum_cons,ih,mul_add]
      by_cases h : d.letter=i <;>
        simp only [h,ite_true,ite_false,pow_succ,mul_neg_one,neg_smul,mul_smul_comm,mul_zero,zero_add] <;>
        noncomm_ring <;> module
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [cliffordWordPartial,wordDeletions,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_apply,pow_zero,one_smul]
    rw [ih]
    have ht := htail a (wordDeletions l)
    change (if a=i then cliffordWord Q l else 0)-_=
      (if a=i then cliffordWord Q l else 0)+
        ((wordDeletions l).map (fun d ↦ if d.letter=i then (-1 : ℂ)^(d.position+1) •
          (Q.γ a*cliffordWord Q d.remainder) else 0)).sum
    rw [ht]
    simp only [neg_mul,sub_eq_add_neg]

lemma wordDeletion_length (l : List (Fin N)) (d : WordDeletion N) (hd : d∈wordDeletions l) :
    d.remainder.length+1=l.length := by
  induction l generalizing d with
  | nil => simp [wordDeletions] at hd
  | cons a l ih =>
    simp only [wordDeletions,List.mem_cons,List.mem_map] at hd
    rcases hd with rfl|⟨e,he,rfl⟩
    · rfl
    · have hh := ih e he
      simp only [List.length_cons]
      omega

lemma cliffordWord_norm (Q : Model N) (l : List (Fin N)) : ‖cliffordWord Q l‖=1 := by
  have hu : cliffordWord Q l∈unitary (Mat (SiteHilbert N)) := by
    unfold cliffordWord
    apply Submonoid.list_prod_mem
    intro X hX
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hX
    apply Unitary.mem_iff.mpr
    change (Q.γ i)ᴴ*Q.γ i=1 ∧ Q.γ i*(Q.γ i)ᴴ=1
    rw [(Q.car.herm i).eq]
    exact ⟨Q.car.sq i,Q.car.sq i⟩
  letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
  exact CStarRing.norm_coe_unitary ⟨cliffordWord Q l,hu⟩

lemma cliffordWord_odd_anticomm (Q : Model N) (i : Fin N) (l : List (Fin N)) (hl : Odd l.length) :
    (1/2 : ℂ) • anticomm (Q.γ i) (cliffordWord Q l)=cliffordWordPartial Q i l := by
  have he := cliffordWord_graded_derivative Q i l
  rw [hl.neg_one_pow] at he
  simp only [neg_one_smul,sub_neg_eq_add] at he
  unfold anticomm
  rw [he,smul_smul]
  norm_num

end SYKFastMix.FastMixing

end
end


-- Solutions.WordSubstitution
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

structure WordSlot (N : ℕ) where
  letter : Fin N
  before : List (Fin N)
  after : List (Fin N)

def wordSlots : List (Fin N) → List (WordSlot N)
  | [] => []
  | a::l => ⟨a,[],l⟩::(wordSlots l).map (fun s ↦ ⟨s.letter,a::s.before,s.after⟩)

def WordSlot.replace (s : WordSlot N) (l : List (Fin N)) := s.before++l++s.after

lemma realWord_append (a b : List (Fin N)) (x : Fin N → ℝ) :
    realWord (a++b) x=realWord a x*realWord b x := by
  simp [realWord]
lemma cliffordWord_append (Q : Model N) (a b : List (Fin N)) :
    cliffordWord Q (a++b)=cliffordWord Q a*cliffordWord Q b := by
  simp [cliffordWord]

lemma wordSlot_length (l : List (Fin N)) (s : WordSlot N) (hs : s∈wordSlots l) :
    s.before.length+1+s.after.length=l.length := by
  induction l generalizing s with
  | nil => simp [wordSlots] at hs
  | cons a l ih =>
    simp only [wordSlots,List.mem_cons,List.mem_map] at hs
    rcases hs with rfl|⟨t,ht,rfl⟩
    · simp [Nat.add_comm]
    · have he := ih t ht
      simp only [List.length_cons]
      omega

lemma realWordPartial_slots (l : List (Fin N)) (i : Fin N) (x : Fin N → ℝ) :
    realWordPartial i l x=((wordSlots l).map
      (fun s ↦ if s.letter=i then realWord (s.replace []) x else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [realWordPartial,wordSlots,List.map_cons,List.sum_cons,List.map_map,
      Function.comp_def,WordSlot.replace,List.nil_append,List.cons_append]
    rw [ih]
    congr 1
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    by_cases he : s.letter=i <;> simp [he,realWord,WordSlot.replace,mul_assoc]

lemma commutator_word_slots (Q : Model N) (H : Mat (SiteHilbert N)) (l : List (Fin N)) :
    cliffordWord Q l*H-H*cliffordWord Q l=
      ((wordSlots l).map (fun s ↦ cliffordWord Q s.before*
        (Q.γ s.letter*H-H*Q.γ s.letter)*cliffordWord Q s.after)).sum := by
  have hsum (a : Fin N) (ss : List (WordSlot N)) :
      (ss.map (fun s ↦ cliffordWord Q (a::s.before)*
        (Q.γ s.letter*H-H*Q.γ s.letter)*cliffordWord Q s.after)).sum=
      Q.γ a*(ss.map (fun s ↦ cliffordWord Q s.before*
        (Q.γ s.letter*H-H*Q.γ s.letter)*cliffordWord Q s.after)).sum := by
    induction ss with
    | nil => simp
    | cons s ss ih =>
      simp only [List.map_cons,List.sum_cons,ih,mul_add]
      congr 1
      change (Q.γ a*cliffordWord Q s.before)*_*_=Q.γ a*(cliffordWord Q s.before*_*_)
      simp only [mul_assoc]
  induction l with
  | nil => simp [cliffordWord,wordSlots]
  | cons a l ih =>
    simp only [wordSlots,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    rw [hsum,← ih]
    simp only [cliffordWord,List.map_nil,List.prod_nil,List.map_cons,List.prod_cons,one_mul]
    noncomm_ring

lemma realWord_generator_slots (w : Disorder N) (l : List (Fin N)) (x : Fin N → ℝ) :
    classicalGenerator w (realWord l) x=
      2*((wordSlots l).map (fun s ↦ coordinateDerivative (classicalG w) s.letter x*
        realWord (s.replace []) x)).sum := by
  unfold classicalGenerator
  simp_rw [coordinateDerivative_realWord,wordDifferential_partial,realWordPartial_slots]
  have hswap : (∑ i : Fin N, coordinateDerivative (classicalG w) i x*
      ((wordSlots l).map (fun s ↦ if s.letter=i then realWord (s.replace []) x else 0)).sum)=
      ((wordSlots l).map (fun s ↦ coordinateDerivative (classicalG w) s.letter x*
        realWord (s.replace []) x)).sum := by
    induction wordSlots l with
    | nil => simp
    | cons s ss ih =>
      simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib,ih]
      congr 1
      simp [mul_ite]
  rw [hswap]

lemma quarticWord_even (A : SYKEdge.KSet N 4) : Even (A.1.sort (· ≤ ·)).length := by
  simpa only [Finset.length_sort,A.2] using (show Even 4 by decide)

lemma majorana_hamiltonian_word_derivative (Q : Model N) (w : Disorder N) (i : Fin N) :
    Q.γ i*hamiltonian Q w-hamiltonian Q w*Q.γ i=
      (2 : ℂ) • ∑ A : SYKEdge.KSet N 4, (w A : ℂ) •
        cliffordWordPartial Q i (A.1.sort (· ≤ ·)) := by
  simp only [hamiltonian,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,
    smul_mul_assoc,← Finset.sum_sub_distrib,← smul_sub]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have he := cliffordWord_graded_derivative Q i (A.1.sort (· ≤ ·))
  rw [(quarticWord_even A).neg_one_pow] at he
  simp only [one_smul] at he
  change (w A : ℂ) • (Q.γ i*cliffordWord Q (A.1.sort (· ≤ ·))-
    cliffordWord Q (A.1.sort (· ≤ ·))*Q.γ i)=_
  rw [he,smul_comm]

end SYKFastMix.FastMixing

end
end


-- Solutions.ClassicalWords
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma realWord_sort (A : Finset (Fin N)) (x : Fin N → ℝ) :
    realWord (A.sort (· ≤ ·)) x=∏ i∈A,x i := by
  unfold realWord
  rw [← List.prod_toFinset x (Finset.sort_nodup _ _)]
  simp

lemma classicalG_hasFDerivAt (w : Disorder N) (x : Fin N → ℝ) :
    HasFDerivAt (classicalG w)
      (∑ A : SYKEdge.KSet N 4, w A • wordDifferential (A.1.sort (· ≤ ·)) x) x := by
  have he : classicalG w=∑ A : SYKEdge.KSet N 4,
      fun y ↦ w A*realWord (A.1.sort (· ≤ ·)) y := by
    funext y
    simp [classicalG,realWord_sort]
  rw [he]
  apply HasFDerivAt.sum
  intro A hA
  exact (realWord_hasFDerivAt _ x).const_mul (w A)

lemma classicalG_derivative_words (w : Disorder N) (i : Fin N) (x : Fin N → ℝ) :
    coordinateDerivative (classicalG w) i x=
      ∑ A : SYKEdge.KSet N 4, w A*realWordPartial i (A.1.sort (· ≤ ·)) x := by
  rw [coordinateDerivative,(classicalG_hasFDerivAt w x).fderiv]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    wordDifferential_partial]

lemma hasFDerivAt_list_words {α : Type} (l : List α) (c : α → ℝ) (word : α → List (Fin N))
    (x : Fin N → ℝ) :
    HasFDerivAt (fun y ↦ (l.map (fun a ↦ c a*realWord (word a) y)).sum)
      (l.map (fun a ↦ c a • wordDifferential (word a) x)).sum x := by
  induction l with
  | nil => simpa using hasFDerivAt_const (c := (0 : ℝ)) x
  | cons a l ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      ((realWord_hasFDerivAt (word a) x).const_mul (c a)).add ih

lemma derivative_list_words {α : Type} (l : List α) (c : α → ℝ) (word : α → List (Fin N))
    (i : Fin N) (x : Fin N → ℝ) :
    coordinateDerivative (fun y ↦ (l.map (fun a ↦ c a*realWord (word a) y)).sum) i x=
      (l.map (fun a ↦ c a*realWordPartial i (word a) x)).sum := by
  rw [coordinateDerivative,(hasFDerivAt_list_words l c word x).fderiv]
  have hh : ∀ k : List α,
      (k.map (fun a ↦ c a • wordDifferential (word a) x)).sum (Pi.single i 1)=
      (k.map (fun a ↦ c a*realWordPartial i (word a) x)).sum := by
    intro k
    induction k with
    | nil => simp
    | cons a k ih =>
      simp only [List.map_cons,List.sum_cons,_root_.add_apply,_root_.smul_apply,
        smul_eq_mul,wordDifferential_partial,ih]
  exact hh l

lemma generator_list_words {α : Type} (w : Disorder N) (l : List α)
    (c : α → ℝ) (word : α → List (Fin N)) (x : Fin N → ℝ) :
    classicalGenerator w (fun y ↦ (l.map (fun a ↦ c a*realWord (word a) y)).sum) x=
      (l.map (fun a ↦ c a*classicalGenerator w (realWord (word a)) x)).sum := by
  simp only [classicalGenerator,derivative_list_words]
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib] at *
    rw [← ih]
    congr 1
    simp only [coordinateDerivative_realWord,wordDifferential_partial]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

end SYKFastMix.FastMixing

end
end


-- Solutions.GaussianMonomials
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SYKFastMix.FastMixing

lemma integrable_gaussian_power (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x^n) (gaussianReal 0 v) := by
  simpa only [id_eq] using integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 v) (by simp [integrableExpSet_id_gaussianReal]) n

lemma gaussian_power_integral_nonneg (v : ℝ≥0) (n : ℕ) :
    0 ≤ ∫ x : ℝ, x^n ∂gaussianReal 0 v := by
  rcases Nat.even_or_odd n with he|ho
  · exact integral_nonneg (fun x ↦ he.pow_nonneg x)
  · have hh := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ ↦ -x)
      (f := fun x : ℝ ↦ x^n) (by fun_prop) (by fun_prop)
    rw [gaussianReal_map_neg,neg_zero] at hh
    simp_rw [ho.neg_pow] at hh
    rw [integral_neg] at hh
    linarith

variable {N : ℕ}

def couplingMonomial (l : List (SYKEdge.KSet N 4)) (w : Disorder N) : ℝ :=
  ∏ A, (w A)^(l.count A)

lemma couplingMonomial_eq_list_prod (l : List (SYKEdge.KSet N 4)) (w : Disorder N) :
    couplingMonomial l w=(l.map w).prod := by
  induction l with
  | nil => simp [couplingMonomial]
  | cons A l ih =>
    rw [List.map_cons,List.prod_cons,← ih]
    unfold couplingMonomial
    have he (B : SYKEdge.KSet N 4) : w B^(List.count B (A::l))=
        (if A=B then w A else 1)*w B^(l.count B) := by
      by_cases h : A=B
      · subst B; simp [List.count_cons,pow_succ,mul_comm]
      · simp [List.count_cons,h,Ne.symm h]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp

lemma integrable_couplingMonomial (Q : Model N) (l : List (SYKEdge.KSet N 4)) :
    Integrable (couplingMonomial l) (disorderLaw Q) := by
  exact Integrable.fintype_prod (fun A ↦ integrable_gaussian_power
    (Real.toNNReal (6*Q.J^2/(N : ℝ)^3)) (l.count A))

lemma couplingMonomial_integral_nonneg (Q : Model N) (l : List (SYKEdge.KSet N 4)) :
    0 ≤ ∫ w, couplingMonomial l w ∂disorderLaw Q := by
  unfold couplingMonomial disorderLaw
  rw [integral_fintype_prod_eq_prod (fun (A : SYKEdge.KSet N 4) (x : ℝ) ↦ x^(l.count A))]
  exact Finset.prod_nonneg (fun A hA ↦ gaussian_power_integral_nonneg _ _)

lemma couplingMonomial_nil (w : Disorder N) : couplingMonomial [] w=1 := by simp [couplingMonomial]

lemma couplingMonomial_cons (A : SYKEdge.KSet N 4) (l : List (SYKEdge.KSet N 4)) (w : Disorder N) :
    couplingMonomial (A::l) w=w A*couplingMonomial l w := by
  simp only [couplingMonomial_eq_list_prod,List.map_cons,List.prod_cons]

lemma couplingMonomial_append (l k : List (SYKEdge.KSet N 4)) (w : Disorder N) :
    couplingMonomial (l++k) w=couplingMonomial l w*couplingMonomial k w := by
  simp only [couplingMonomial_eq_list_prod,List.map_append,List.prod_append]

end SYKFastMix.FastMixing

end
end


-- Solutions.InteractionPaths
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma list_sum_flatMap {α β M : Type} [AddMonoid M] (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum=(l.map (fun a ↦ ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

lemma all_list_sum {α M : Type} [Fintype α] [DecidableEq α] [AddCommMonoid M] (f : α → M) :
    ((Finset.univ.toList).map f).sum=∑ a,f a := by
  rw [← List.sum_toFinset f (Finset.nodup_toList _)]
  simp

structure InteractionPath (N : ℕ) where
  couplings : List (SYKEdge.KSet N 4)
  word : List (Fin N)
  sign : ℝ

def InteractionPath.step (t : InteractionPath N) : List (InteractionPath N) :=
  (wordSlots t.word).flatMap (fun s ↦ (Finset.univ.toList : List (SYKEdge.KSet N 4)).flatMap
    (fun A ↦ ((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
      (fun d ↦ ⟨A::t.couplings,s.replace d.remainder,t.sign*(-1)^d.position⟩)))

def interactionPaths (j : Fin N) : ℕ → List (InteractionPath N)
  | 0 => [⟨[],[j],1⟩]
  | m+1 => (interactionPaths j m).flatMap InteractionPath.step

lemma interactionPath_lengths (j : Fin N) (m : ℕ) (t : InteractionPath N)
    (ht : t∈interactionPaths j m) : t.couplings.length=m ∧ t.word.length=2*m+1 ∧ |t.sign|=1 := by
  induction m generalizing t with
  | zero =>
    simp only [interactionPaths,List.mem_singleton] at ht
    subst t
    simp
  | succ m ih =>
    simp only [interactionPaths,List.mem_flatMap] at ht
    obtain ⟨u,hu,ht⟩ := ht
    rcases ih u hu with ⟨huc,huw,hus⟩
    simp only [InteractionPath.step,List.mem_flatMap,List.mem_map,List.mem_filter] at ht
    obtain ⟨s,hs,A,hA,d,⟨hd,hdi⟩,rfl⟩ := ht
    have hslot := wordSlot_length u.word s hs
    have hdel := wordDeletion_length (A.1.sort (· ≤ ·)) d hd
    rw [Finset.length_sort,A.2] at hdel
    simp only [List.length_cons,huc,WordSlot.replace,List.length_append,abs_mul,abs_pow,abs_neg,abs_one,
      one_pow,hus,mul_one]
    constructor
    · trivial
    constructor
    · omega
    · trivial

lemma wordDeletions_filter_sum {M : Type} [AddCommMonoid M] (l : List (Fin N))
    (i : Fin N) (f : WordDeletion N → M) :
    (((wordDeletions l).filter (fun d ↦ d.letter=i)).map f).sum=
      ((wordDeletions l).map (fun d ↦ if d.letter=i then f d else 0)).sum := by
  have hh : ∀ ds : List (WordDeletion N),
      ((ds.filter (fun d ↦ d.letter=i)).map f).sum=
      (ds.map (fun d ↦ if d.letter=i then f d else 0)).sum := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih => by_cases he : d.letter=i <;> simp [he,ih]
  exact hh _

end SYKFastMix.FastMixing

end
end


-- Solutions.CubicTreeGrowth
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace SYKFastMix.FastMixing

def CubicTree.sprouts : CubicTree → List CubicTree
  | .leaf => [.node .leaf .leaf .leaf]
  | .node a b c => (a.sprouts.map (fun t ↦ .node t b c))++
    (b.sprouts.map (fun t ↦ .node a t c))++(c.sprouts.map (fun t ↦ .node a b t))

lemma CubicTree.sprouts_length (t : CubicTree) : t.sprouts.length=t.leaves := by
  induction t with
  | leaf => rfl
  | node a b c ha hb hc => simp [sprouts,leaves,ha,hb,hc,Nat.add_assoc]
lemma CubicTree.sprouts_nodes (t u : CubicTree) (hu : u∈t.sprouts) : u.nodes=t.nodes+1 := by
  induction t generalizing u with
  | leaf => simp only [sprouts,List.mem_singleton] at hu; subst u; rfl
  | node a b c ha hb hc =>
    simp only [sprouts,List.mem_append,List.mem_map] at hu
    rcases hu with (⟨v,hv,rfl⟩|⟨v,hv,rfl⟩)|⟨v,hv,rfl⟩
    · simp only [nodes,ha v hv]; omega
    · simp only [nodes,hb v hv]; omega
    · simp only [nodes,hc v hv]; omega

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (V : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ E) E)

lemma cubic_slot0 (a b c z : E) : V.toContinuousLinearMap ![a,b,c] 0 z=V ![z,b,c] := by
  change V (Function.update ![a,b,c] (0 : Fin 3) z)=_
  congr 1
  ext i
  fin_cases i <;> simp [Function.update,Fin.ext_iff]
lemma cubic_slot1 (a b c z : E) : V.toContinuousLinearMap ![a,b,c] 1 z=V ![a,z,c] := by
  change V (Function.update ![a,b,c] (1 : Fin 3) z)=_
  congr 1
  ext i
  fin_cases i <;> simp [Function.update,Fin.ext_iff]
lemma cubic_slot2 (a b c z : E) : V.toContinuousLinearMap ![a,b,c] 2 z=V ![a,b,z] := by
  change V (Function.update ![a,b,c] (2 : Fin 3) z)=_
  congr 1
  ext i
  fin_cases i <;> simp [Function.update,Fin.ext_iff]

lemma cubic_slot0_sum {α : Type} (l : List α) (f : α → E) (b c : E) :
    V ![(l.map f).sum,b,c]=(l.map (fun a ↦ V ![f a,b,c])).sum := by
  have h := map_list_sum (V.toContinuousLinearMap ![0,b,c] 0) (l.map f)
  simpa only [List.map_map,Function.comp_def,cubic_slot0] using h
lemma cubic_slot1_sum {α : Type} (l : List α) (f : α → E) (a c : E) :
    V ![a,(l.map f).sum,c]=(l.map (fun b ↦ V ![a,f b,c])).sum := by
  have h := map_list_sum (V.toContinuousLinearMap ![a,0,c] 1) (l.map f)
  simpa only [List.map_map,Function.comp_def,cubic_slot1] using h
lemma cubic_slot2_sum {α : Type} (l : List α) (f : α → E) (a b : E) :
    V ![a,b,(l.map f).sum]=(l.map (fun c ↦ V ![a,b,f c])).sum := by
  have h := map_list_sum (V.toContinuousLinearMap ![a,b,0] 2) (l.map f)
  simpa only [List.map_map,Function.comp_def,cubic_slot2] using h

lemma CubicTree.differential_sprouts (t : CubicTree) (x : E) :
    t.differential V x (V ![x,x,x])=(t.sprouts.map (fun u ↦ u.eval V x)).sum := by
  induction t with
  | leaf => simp [differential,sprouts,eval]
  | node a b c ha hb hc =>
    change V.linearDeriv ![a.eval V x,b.eval V x,c.eval V x]
      ![a.differential V x (V ![x,x,x]),b.differential V x (V ![x,x,x]),
        c.differential V x (V ![x,x,x])]=_
    rw [cubic_differential_apply,ha,hb,hc,cubic_slot0_sum,cubic_slot1_sum,cubic_slot2_sum]
    simp only [sprouts,List.map_append,List.sum_append,List.map_map,Function.comp_def,eval]

end
end SYKFastMix.FastMixing

end
end


-- Solutions.CubicForest
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace SYKFastMix.FastMixing

def cubicForest : ℕ → List CubicTree
  | 0 => [.leaf]
  | m+1 => (cubicForest m).flatMap CubicTree.sprouts

lemma cubicForest_nodes (m : ℕ) (t : CubicTree) (ht : t∈cubicForest m) : t.nodes=m := by
  induction m generalizing t with
  | zero => simp only [cubicForest,List.mem_singleton] at ht; subst t; rfl
  | succ m ih =>
    simp only [cubicForest,List.mem_flatMap] at ht
    obtain ⟨u,hu,ht⟩ := ht
    rw [CubicTree.sprouts_nodes u t ht,ih u hu]

lemma cubicForest_length (m : ℕ) : (cubicForest (m+1)).length=(2*m+1)*(cubicForest m).length := by
  rw [cubicForest,List.length_flatMap]
  have he : ((cubicForest m).map (fun t ↦ t.sprouts.length))=
      (cubicForest m).map (fun _ ↦ 2*m+1) := by
    apply List.map_congr_left
    intro t ht
    rw [CubicTree.sprouts_length,CubicTree.leaves_eq,cubicForest_nodes m t ht]
  rw [he]
  simp [List.map_const,Nat.mul_comm]

lemma cubicForest_coefficient_bound (m : ℕ) :
    ((2*m+1 : ℕ) : ℝ)*(cubicForest m).length≤(3 : ℝ)^m*(m.factorial : ℝ) := by
  induction m with
  | zero => simp [cubicForest]
  | succ m ih =>
    rw [cubicForest_length,Nat.cast_mul]
    have hle : ((2*(m+1)+1 : ℕ) : ℝ)≤3*(m+1 : ℝ) := by push_cast; nlinarith
    calc
      _=((2*(m+1)+1 : ℕ) : ℝ)*(((2*m+1 : ℕ) : ℝ)*(cubicForest m).length) := by ring
      _ ≤ (3*(m+1 : ℝ))*((3 : ℝ)^m*(m.factorial : ℝ)) := by gcongr
      _ = _ := by rw [pow_succ,Nat.factorial_succ]; push_cast; ring

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (V : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ E) E)

def forestEval (m : ℕ) (x : E) : E := ((cubicForest m).map (fun t ↦ t.eval V x)).sum
def forestDifferential (m : ℕ) (x : E) : E →L[ℝ] E :=
  ((cubicForest m).map (fun t ↦ t.differential V x)).sum

lemma forest_hasFDerivAt (m : ℕ) (x : E) :
    HasFDerivAt (forestEval V m) (forestDifferential V m x) x := by
  have hh : ∀ l : List CubicTree,
      HasFDerivAt (fun y ↦ (l.map (fun t ↦ t.eval V y)).sum)
        (l.map (fun t ↦ t.differential V x)).sum x := by
    intro l
    induction l with
    | nil => simpa using! hasFDerivAt_const (c := (0 : E)) x
    | cons t l ih =>
      simpa only [List.map_cons,List.sum_cons] using! (t.hasFDerivAt V x).add ih
  exact hh _

lemma norm_list_sum_le_const {α F : Type} [NormedAddCommGroup F] (l : List α) (f : α → F) (C : ℝ)
    (hf : ∀ a∈l, ‖f a‖≤C) : ‖(l.map f).sum‖≤(l.length : ℝ)*C := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ‖f a‖+‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ C+(l.length : ℝ)*C := add_le_add (hf a (by simp)) (ih (fun b hb ↦ hf b (by simp [hb])))
      _ = _ := by ring

lemma forest_differential_norm (m : ℕ) (x : E) :
    ‖forestDifferential V m x‖≤
      (((2*m+1 : ℕ) : ℝ)*(cubicForest m).length)*‖V‖^m*‖x‖^(2*m) := by
  have hh := norm_list_sum_le_const (cubicForest m) (fun t ↦ t.differential V x)
    (((2*m+1 : ℕ) : ℝ)*‖V‖^m*‖x‖^(2*m)) (by
      intro t ht
      have hn := cubicForest_nodes m t ht
      have hl := t.leaves_eq
      have hd := t.norm_differential_le V x
      rw [hl,hn] at hd
      simpa using hd)
  exact hh.trans (le_of_eq (by ring))

lemma forest_normalized_differential_norm (m : ℕ) (x : E) :
    ‖(m.factorial : ℝ)⁻¹ • forestDifferential V m x‖≤(3*‖V‖*‖x‖^2)^m := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (m.factorial : ℝ)⁻¹*
        ((((2*m+1 : ℕ) : ℝ)*(cubicForest m).length)*‖V‖^m*‖x‖^(2*m)) := by
      gcongr
      exact forest_differential_norm V m x
    _ ≤ (m.factorial : ℝ)⁻¹*((3 : ℝ)^m*(m.factorial : ℝ)*‖V‖^m*‖x‖^(2*m)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (cubicForest_coefficient_bound m) (by positivity)) (by positivity))
        (by positivity)
    _ = _ := by
      have hf : (m.factorial : ℝ)≠0 := by positivity
      rw [mul_pow,mul_pow,← pow_mul]
      field_simp

lemma forestEval_zero (x : E) : forestEval V 0 x=x := by simp [forestEval,cubicForest,CubicTree.eval]

lemma forestEval_succ (m : ℕ) (x : E) :
    forestEval V (m+1) x=forestDifferential V m x (V ![x,x,x]) := by
  unfold forestEval forestDifferential
  rw [cubicForest,list_sum_flatMap]
  have he : ∀ l : List CubicTree,
      (l.map (fun t ↦ t.differential V x)).sum (V ![x,x,x])=
        (l.map (fun t ↦ t.differential V x (V ![x,x,x]))).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih => simp only [List.map_cons,List.sum_cons,_root_.add_apply,ih]
  rw [he]
  simp only [CubicTree.differential_sprouts]

end
end SYKFastMix.FastMixing

end
end


-- Solutions.RealCLMComplexMatrix
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing
variable {n : ℕ}

def realCLMComplexMatrix (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ := fun i j ↦ (D (EuclideanSpace.single j 1) i : ℂ)

lemma euclidean_real_basis_sum (x : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin n, x j • EuclideanSpace.single j 1)=x := by
  ext i
  simp [EuclideanSpace.single_apply,Pi.single_apply,eq_comm]

lemma realCLM_apply_coordinates (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    D x i=∑ j : Fin n, (D (EuclideanSpace.single j 1) i)*x j := by
  conv_lhs => rw [← euclidean_real_basis_sum x]
  simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma norm_realCLMComplexMatrix_le (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖realCLMComplexMatrix D‖≤‖D‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
  intro z
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ (z i).re)
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ (z i).im)
  let Az : EuclideanSpace ℂ (Fin n) := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (realCLMComplexMatrix D) z
  have hr (i : Fin n) : (Az i).re=D x i := by
    rw [realCLM_apply_coordinates]
    simp [Az,realCLMComplexMatrix,Matrix.toEuclideanCLM_toLp,Matrix.mulVec,
      dotProduct,Complex.re_sum,Complex.mul_re,x]
  have hi (i : Fin n) : (Az i).im=D y i := by
    rw [realCLM_apply_coordinates]
    simp [Az,realCLMComplexMatrix,Matrix.toEuclideanCLM_toLp,Matrix.mulVec,
      dotProduct,Complex.im_sum,Complex.mul_im,y]
  have hnorm : ‖Az‖^2=‖D x‖^2+‖D y‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,Complex.normSq_apply,hr,hi,Real.norm_eq_abs,sq_abs,
      Finset.sum_add_distrib]
    simp only [pow_two]
  have hxy : ‖z‖^2=‖x‖^2+‖y‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,Complex.normSq_apply,x,y,WithLp.ofLp_toLp,Real.norm_eq_abs,
      sq_abs,Finset.sum_add_distrib]
    simp only [pow_two]
  have hx := pow_le_pow_left₀ (norm_nonneg (D x)) (D.le_opNorm x) 2
  have hy := pow_le_pow_left₀ (norm_nonneg (D y)) (D.le_opNorm y) 2
  change ‖Az‖≤‖D‖*‖z‖
  have he := congrArg (fun r : ℝ ↦ ‖D‖^2*r) hxy
  nlinarith [he,norm_nonneg Az,mul_nonneg (norm_nonneg D) (norm_nonneg z)]

end SYKFastMix.FastMixing

end
end


-- Solutions.CubicClassicalAdapter
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def euclidify : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap

def realCoordinate (i : Fin N) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).toContinuousLinearMap

def classicalVelocity (w : Disorder N) (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i ↦ 2*coordinateDerivative (classicalG w) i (WithLp.ofLp x))

lemma coordinateDerivative_vector_function (f : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (x : Fin N → ℝ)
    (hf : HasFDerivAt f D (WithLp.toLp 2 x)) (i j : Fin N) :
    coordinateDerivative (fun y ↦ f (WithLp.toLp 2 y) i) j x=D (EuclideanSpace.single j 1) i := by
  have hh := ((realCoordinate i).hasFDerivAt.comp (WithLp.toLp 2 x) hf).comp x
    (euclidify (N := N)).hasFDerivAt
  have he : HasFDerivAt (fun y ↦ f (WithLp.toLp 2 y) i)
      ((realCoordinate i).comp (D.comp euclidify)) x := by
    convert! hh using 1
  rw [coordinateDerivative,he.fderiv]
  rfl

lemma classicalGenerator_vector_function (w : Disorder N)
    (f : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (x : Fin N → ℝ)
    (hf : HasFDerivAt f D (WithLp.toLp 2 x)) (i : Fin N) :
    classicalGenerator w (fun y ↦ f (WithLp.toLp 2 y) i) x=
      D (classicalVelocity w (WithLp.toLp 2 x)) i := by
  unfold classicalGenerator
  simp_rw [coordinateDerivative_vector_function f D x hf]
  rw [realCLM_apply_coordinates]
  simp only [classicalVelocity,WithLp.ofLp_toLp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change 2*(coordinateDerivative (classicalG w) j x*D (EuclideanSpace.single j 1) i)=
    D (EuclideanSpace.single j 1) i*(2*coordinateDerivative (classicalG w) j x)
  ring

lemma forest_classicalIterate (w : Disorder N)
    (V : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ EuclideanSpace ℝ (Fin N))
      (EuclideanSpace ℝ (Fin N)))
    (hV : ∀ x, V ![x,x,x]=classicalVelocity w x) (m : ℕ) (x : Fin N → ℝ) (i : Fin N) :
    forestEval V m (WithLp.toLp 2 x) i=classicalIterate w m i x := by
  induction m generalizing x with
  | zero => simp [forestEval_zero,classicalIterate]
  | succ m ih =>
    rw [forestEval_succ,hV]
    rw [← classicalGenerator_vector_function w (forestEval V m) _ x (forest_hasFDerivAt V m _) i]
    have he : (fun y ↦ forestEval V m (WithLp.toLp 2 y) i)=classicalIterate w m i := funext ih
    rw [he]
    simp only [classicalIterate,Function.iterate_succ_apply']

lemma classicalCoefficient_forest_matrix (w : Disorder N)
    (V : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ EuclideanSpace ℝ (Fin N))
      (EuclideanSpace ℝ (Fin N)))
    (hV : ∀ x, V ![x,x,x]=classicalVelocity w x) (m : ℕ) (σ : Fin N → ℝ) :
    classicalCoefficient w m σ=realCLMComplexMatrix
      ((m.factorial : ℝ)⁻¹ • forestDifferential V m (WithLp.toLp 2 σ)) := by
  ext i j
  have he : classicalIterate w m i=fun y ↦ forestEval V m (WithLp.toLp 2 y) i := by
    funext y
    exact (forest_classicalIterate w V hV m y i).symm
  simp only [classicalCoefficient,he]
  rw [coordinateDerivative_vector_function _ _ _ (forest_hasFDerivAt V m _) i j]
  change ((forestDifferential V m (WithLp.toLp 2 σ) (EuclideanSpace.single j 1) i : ℝ) : ℂ)/
    (m.factorial : ℂ)=
    (((m.factorial : ℝ)⁻¹*forestDifferential V m (WithLp.toLp 2 σ) (EuclideanSpace.single j 1) i : ℝ) : ℂ)
  simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast]
  ring

lemma classicalCoefficient_cubic_norm_bound (w : Disorder N)
    (V : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ EuclideanSpace ℝ (Fin N))
      (EuclideanSpace ℝ (Fin N)))
    (hV : ∀ x, V ![x,x,x]=classicalVelocity w x) (m : ℕ) :
    ‖classicalCoefficient w m (fun _ ↦ 1)‖≤(3*‖V‖*(N : ℝ))^m := by
  rw [classicalCoefficient_forest_matrix w V hV]
  apply (norm_realCLMComplexMatrix_le _).trans
  have hn : ‖(WithLp.toLp 2 (fun _ : Fin N ↦ (1 : ℝ)) : EuclideanSpace ℝ (Fin N))‖^2=(N : ℝ) := by
    simp [EuclideanSpace.norm_sq_eq]
  simpa only [hn] using forest_normalized_differential_norm V m (WithLp.toLp 2 (fun _ : Fin N ↦ (1 : ℝ)))

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticTensor
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Matrix
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def quarticLabel (A : SYKEdge.KSet N 4) (r : Fin 4) : Fin N :=
  (A.1.orderIsoOfFin A.2 r).1

lemma quarticLabel_injective (A : SYKEdge.KSet N 4) : Function.Injective (quarticLabel A) := by
  intro r s h
  exact (A.1.orderIsoOfFin A.2).injective (Subtype.ext h)

lemma quarticLabel_prod (A : SYKEdge.KSet N 4) (x : Fin N → ℝ) :
    (∏ r : Fin 4,x (quarticLabel A r))=∏ i∈A.1,x i := by
  calc
    _=∏ i : A.1,x i := Fintype.prod_equiv (A.1.orderIsoOfFin A.2).toEquiv _ _ (fun r ↦ rfl)
    _=_ := by
      change (∏ i∈A.1.attach,x i.1)=_
      rw [Finset.prod_attach]

def quarticMonomialForm (A : SYKEdge.KSet N 4) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin N)) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
    (fun r ↦ realCoordinate (quarticLabel A r))

def symmetricQuarticForm (A : SYKEdge.KSet N 4) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin N)) ℝ :=
  (1/24 : ℝ) • ∑ π : Equiv.Perm (Fin 4), (quarticMonomialForm A).domDomCongr π

def disorderQuarticForm (w : Disorder N) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin N)) ℝ :=
  ∑ A : SYKEdge.KSet N 4,w A • symmetricQuarticForm A

lemma quarticMonomialForm_apply (A : SYKEdge.KSet N 4) (u : Fin 4 → EuclideanSpace ℝ (Fin N)) :
    quarticMonomialForm A u=∏ r : Fin 4,u r (quarticLabel A r) := by
  simp [quarticMonomialForm,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply,realCoordinate]

lemma symmetricQuarticForm_apply (A : SYKEdge.KSet N 4) (u : Fin 4 → EuclideanSpace ℝ (Fin N)) :
    symmetricQuarticForm A u=(1/24 : ℝ)*∑ π : Equiv.Perm (Fin 4),
      ∏ r : Fin 4,u (π r) (quarticLabel A r) := by
  simp [symmetricQuarticForm,ContinuousMultilinearMap.domDomCongr_apply,quarticMonomialForm_apply]

lemma symmetricQuarticForm_symmetric (A : SYKEdge.KSet N 4)
    (u : Fin 4 → EuclideanSpace ℝ (Fin N)) (σ : Equiv.Perm (Fin 4)) :
    symmetricQuarticForm A (u ∘ σ)=symmetricQuarticForm A u := by
  rw [symmetricQuarticForm_apply,symmetricQuarticForm_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft σ)
  intro π
  rfl

lemma symmetricQuarticForm_diagonal (A : SYKEdge.KSet N 4) (x : EuclideanSpace ℝ (Fin N)) :
    symmetricQuarticForm A (fun _ ↦ x)=∏ i∈A.1,x i := by
  rw [symmetricQuarticForm_apply]
  simp only [quarticLabel_prod,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Fintype.card_perm]
  ring

lemma disorderQuarticForm_diagonal (w : Disorder N) (x : EuclideanSpace ℝ (Fin N)) :
    disorderQuarticForm w (fun _ ↦ x)=classicalG w (WithLp.ofLp x) := by
  simp [disorderQuarticForm,symmetricQuarticForm_diagonal,classicalG]

lemma disorderQuarticForm_symmetric (w : Disorder N) (u : Fin 4 → EuclideanSpace ℝ (Fin N))
    (σ : Equiv.Perm (Fin 4)) : disorderQuarticForm w (u ∘ σ)=disorderQuarticForm w u := by
  simp [disorderQuarticForm,symmetricQuarticForm_symmetric]

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticCubicVelocity
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def quarticCubicVelocity (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ E) E :=
  (8 : ℝ) • (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap T.curryRight

lemma quarticCubicVelocity_norm (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) :
    ‖quarticCubicVelocity T‖=8*‖T‖ := by
  unfold quarticCubicVelocity
  rw [norm_smul]
  have he := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.norm_compContinuousMultilinearMap T.curryRight
  rw [he,ContinuousMultilinearMap.curryRight_norm]
  norm_num

lemma quarticCubicVelocity_inner (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
    (x : Fin 3 → E) (h : E) :
    inner ℝ (quarticCubicVelocity T x) h=8*T (Fin.snoc x h) := by
  simp [quarticCubicVelocity,ContinuousLinearMap.compContinuousMultilinearMap_coe,
    real_inner_smul_left, InnerProductSpace.toDual_symm_apply,ContinuousMultilinearMap.curryRight_apply]

lemma quartic_update_symmetry (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
    (hT : ∀ u (π : Equiv.Perm (Fin 4)),T (u ∘ π)=T u) (x h : E) (i : Fin 4) :
    T (Function.update (fun _ ↦ x) i h)=T (Fin.snoc (fun _ : Fin 3 ↦ x) h) := by
  have hh := hT (Function.update (fun _ ↦ x) i h) (Equiv.swap i 3)
  have he : (Function.update (fun _ : Fin 4 ↦ x) i h) ∘ Equiv.swap i 3=
      Fin.snoc (fun _ : Fin 3 ↦ x) h := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [Function.update,Equiv.swap_apply_def,Fin.ext_iff] <;> rfl
  rw [he] at hh
  exact hh.symm

lemma quartic_diagonal_hasFDerivAt (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
    (hT : ∀ u (π : Equiv.Perm (Fin 4)),T (u ∘ π)=T u) (x : E) :
    HasFDerivAt (fun y ↦ T (fun _ ↦ y)) ((4 : ℝ) • T.curryRight (fun _ ↦ x)) x := by
  have hdiag : HasFDerivAt (fun y : E ↦ fun _ : Fin 4 ↦ y)
      (ContinuousLinearMap.pi (fun _ : Fin 4 ↦ ContinuousLinearMap.id ℝ E)) x :=
    hasFDerivAt_pi.2 (fun _ ↦ hasFDerivAt_id x)
  have hh := (T.hasFDerivAt (fun _ : Fin 4 ↦ x)).comp x hdiag
  convert! hh using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.id_apply,ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousMultilinearMap.curryRight_apply]
  simp only [quartic_update_symmetry T hT x h,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  simp only [smul_eq_mul, nsmul_eq_mul]
  rfl

end

variable {N : ℕ}
lemma classicalG_quartic_gradient (w : Disorder N) (x : Fin N → ℝ) (i : Fin N) :
    coordinateDerivative (classicalG w) i x=
      4*disorderQuarticForm w (Fin.snoc (fun _ : Fin 3 ↦ WithLp.toLp 2 x) (EuclideanSpace.single i 1)) := by
  have hT := quartic_diagonal_hasFDerivAt (disorderQuarticForm w) (disorderQuarticForm_symmetric w)
    (WithLp.toLp 2 x)
  have hh := hT.comp x (euclidify (N := N)).hasFDerivAt
  have he : HasFDerivAt (classicalG w)
      (((4 : ℝ) • (disorderQuarticForm w).curryRight (fun _ ↦ WithLp.toLp 2 x)).comp euclidify) x := by
    convert! hh using 1
    funext y
    exact (disorderQuarticForm_diagonal w _).symm
  rw [coordinateDerivative,he.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [ContinuousMultilinearMap.curryRight_apply]
  rfl

lemma disorderQuarticVelocity_diagonal (w : Disorder N) (x : EuclideanSpace ℝ (Fin N)) :
    quarticCubicVelocity (disorderQuarticForm w) ![x,x,x]=classicalVelocity w x := by
  ext i
  have hh := quarticCubicVelocity_inner (disorderQuarticForm w) ![x,x,x] (EuclideanSpace.single i 1)
  have hi : inner ℝ (quarticCubicVelocity (disorderQuarticForm w) ![x,x,x]) (EuclideanSpace.single i 1)=
      quarticCubicVelocity (disorderQuarticForm w) ![x,x,x] i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,EuclideanSpace.single_apply]
  rw [hi] at hh
  change _=2*coordinateDerivative (classicalG w) i (WithLp.ofLp x)
  rw [classicalG_quartic_gradient]
  have heq : (Fin.snoc ![x,x,x] (EuclideanSpace.single i (1 : ℝ)) : Fin 4 → EuclideanSpace ℝ (Fin N))=
      (Fin.snoc (fun _ : Fin 3 ↦ x) (EuclideanSpace.single i (1 : ℝ)) : Fin 4 → EuclideanSpace ℝ (Fin N)) := by
    congr 1
    ext j
    fin_cases j <;> rfl
  rw [hh,heq]
  ring

lemma classicalCoefficient_tensor_norm_bound (w : Disorder N) (m : ℕ) :
    ‖classicalCoefficient w m (fun _ ↦ 1)‖≤(24*(N : ℝ)*‖disorderQuarticForm w‖)^m := by
  have hh := classicalCoefficient_cubic_norm_bound w (quarticCubicVelocity (disorderQuarticForm w))
    (disorderQuarticVelocity_diagonal w) m
  rw [quarticCubicVelocity_norm] at hh
  convert hh using 1
  congr 1
  ring

end SYKFastMix.FastMixing

end
end


-- Solutions.ProductTensorMetric
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open scoped RealInnerProductSpace
namespace SYKFastMix.FastMixing
variable {r n : ℕ}

def productTensor (u : Fin r → EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin r → Fin n) :=
  WithLp.toLp 2 (fun a ↦ ∏ i : Fin r,u i (a i))

lemma productTensor_norm_sq (u : Fin r → EuclideanSpace ℝ (Fin n)) :
    ‖productTensor u‖^2=∏ i : Fin r,‖u i‖^2 := by
  simp only [productTensor,EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs,
    ← Finset.prod_pow]
  exact (Fintype.prod_sum (fun (i : Fin r) (j : Fin n) ↦ (u i j)^2)).symm

lemma productTensor_inner (u v : Fin r → EuclideanSpace ℝ (Fin n)) :
    inner ℝ (productTensor u) (productTensor v)=∏ i : Fin r,inner ℝ (u i) (v i) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,productTensor,WithLp.ofLp_toLp,
    Pi.star_apply,star_trivial,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin r) (j : Fin n) ↦ v i j*u i j)).symm

lemma one_sub_prod_le_sum (s : Finset (Fin r)) (a : Fin r → ℝ) (ha : ∀ i∈s, |a i|≤1) :
    1-∏ i∈s,a i≤∑ i∈s,(1-a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    have hai := (abs_le.mp (ha i (by simp))).2
    have has (j : Fin r) (hj : j∈s) := ha j (by simp [hj])
    have hp : ∏ j∈s,a j≤1 := by
      apply (le_abs_self _).trans
      rw [Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun j hj ↦ abs_nonneg (a j)) has
    have hh := ih has
    rw [Finset.prod_cons,Finset.sum_cons]
    nlinarith [mul_nonneg (sub_nonneg.mpr hai) (sub_nonneg.mpr hp)]

lemma productTensor_dist_sq_le (u v : Fin r → EuclideanSpace ℝ (Fin n))
    (hu : ∀ i,‖u i‖=1) (hv : ∀ i,‖v i‖=1) :
    ‖productTensor u-productTensor v‖^2≤∑ i : Fin r,‖u i-v i‖^2 := by
  rw [norm_sub_sq_real,productTensor_norm_sq,productTensor_norm_sq,productTensor_inner]
  simp only [hu,hv,one_pow,Finset.prod_const_one]
  have ha (i : Fin r) : |inner ℝ (u i) (v i)|≤1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm (u i) (v i)
  have hh := one_sub_prod_le_sum Finset.univ (fun i ↦ inner ℝ (u i) (v i)) (fun i hi ↦ ha i)
  have he : (∑ i : Fin r,‖u i-v i‖^2)=2*(∑ i : Fin r,(1-inner ℝ (u i) (v i))) := by
    simp_rw [norm_sub_sq_real,hu,hv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  nlinarith

end SYKFastMix.FastMixing

end
end


-- Solutions.MultilinearSphereNorm
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open scoped RealInnerProductSpace
namespace SYKFastMix.FastMixing

abbrev QuarticInputs (N : ℕ) := Fin 4 → {x : EuclideanSpace ℝ (Fin N) // ‖x‖=1}

lemma multilinear_norm_le_of_unit {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) {C : ℝ} (hC : 0≤C)
    (h : ∀ u : Fin 4 → E, (∀ r,‖u r‖=1) → ‖T u‖≤C) : ‖T‖≤C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro u
  by_cases hz : ∃ r,u r=0
  · obtain ⟨r,hr⟩ := hz
    rw [T.map_coord_zero r hr,norm_zero]
    positivity
  push_neg at hz
  let v : Fin 4 → E := fun r ↦ ‖u r‖⁻¹ • u r
  have hv : ∀ r,‖v r‖=1 := by
    intro r
    simp [v,norm_smul,abs_of_nonneg (norm_nonneg _),norm_ne_zero_iff.mpr (hz r)]
  have hu : u=fun r ↦ ‖u r‖ • v r := by
    funext r
    dsimp [v]
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz r)),one_smul]
  conv_lhs => rw [hu,T.map_smul_univ,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun r hr ↦ norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (h v hv) (Finset.prod_nonneg (fun r hr ↦ norm_nonneg _))).trans_eq (mul_comm _ _)

lemma quartic_norm_eq_sup {N : ℕ} [Nonempty (QuarticInputs N)]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin N)) ℝ) :
    ‖T‖=⨆ u : QuarticInputs N,T (fun r ↦ (u r).1) := by
  classical
  let f : QuarticInputs N → ℝ := fun u ↦ T (fun r ↦ (u r).1)
  have hb : BddAbove (Set.range f) := by
    refine ⟨‖T‖,?_⟩
    rintro y ⟨u,rfl⟩
    exact (le_abs_self _).trans (by simpa [f,Real.norm_eq_abs,(u _).2] using T.le_opNorm (fun r ↦ (u r).1))
  have hle (u : QuarticInputs N) : f u≤(⨆ u,f u) := le_ciSup hb u
  have hn (u : QuarticInputs N) : -f u≤(⨆ u,f u) := by
    let v : QuarticInputs N := Function.update u 0 ⟨-(u 0).1,by simp [(u 0).2]⟩
    have he : f v = -f u := by
      change T (fun r ↦ (v r).1) = -T (fun r ↦ (u r).1)
      have heq : (fun r ↦ (v r).1)=Function.update (fun r ↦ (u r).1) 0 (-(u 0).1) := by
        ext r
        by_cases hr : r=0 <;> simp [v,hr]
      rw [heq]
      change T.toMultilinearMap (Function.update (fun r ↦ (u r).1) 0 (-(u 0).1)) = -T.toMultilinearMap (fun r ↦ (u r).1)
      rw [MultilinearMap.map_update_neg]
      simp
    rw [←he]
    exact hle v
  have hpos : 0≤(⨆ u,f u) := by
    let u := Classical.choice (inferInstance : Nonempty (QuarticInputs N))
    linarith [hle u,hn u]
  apply le_antisymm
  · apply multilinear_norm_le_of_unit T hpos
    intro u hu
    let v : QuarticInputs N := fun r ↦ ⟨u r,hu r⟩
    exact abs_le.mpr ⟨by simpa [f,v] using neg_le.mp (hn v),by simpa [f,v] using hle v⟩
  · apply ciSup_le
    intro u
    exact (le_abs_self _).trans (by simpa [f,Real.norm_eq_abs,(u _).2] using T.le_opNorm (fun r ↦ (u r).1))

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticFeatures
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def quarticTuple (a : SYKEdge.KSet N 4 × Equiv.Perm (Fin 4)) : Fin 4 → Fin N :=
  quarticLabel a.1 ∘ a.2

lemma quarticLabel_image (A : SYKEdge.KSet N 4) :
    Finset.univ.image (quarticLabel A)=A.1 := by
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,rfl⟩
    exact (A.1.orderIsoOfFin A.2 r).2
  · intro hi
    obtain ⟨r,hr⟩ := (A.1.orderIsoOfFin A.2).surjective ⟨i,hi⟩
    exact ⟨r,congrArg Subtype.val hr⟩

lemma quarticTuple_image (a : SYKEdge.KSet N 4 × Equiv.Perm (Fin 4)) :
    Finset.univ.image (quarticTuple a)=a.1.1 := by
  rw [quarticTuple,← Finset.image_image]
  rw [Finset.image_univ_of_surjective a.2.surjective]
  exact quarticLabel_image a.1

lemma quarticTuple_injective : Function.Injective (quarticTuple (N := N)) := by
  rintro ⟨A,π⟩ ⟨B,σ⟩ h
  have hab : A=B := by
    apply Subtype.ext
    rw [←quarticTuple_image (A,π),←quarticTuple_image (B,σ),h]
  subst B
  have hp : π=σ := by
    apply Equiv.ext
    intro r
    exact quarticLabel_injective A (congrFun h r)
  subst σ
  rfl

def quarticFeatureMap (v : EuclideanSpace ℝ (Fin 4 → Fin N)) (A : SYKEdge.KSet N 4) : ℝ :=
  (1/24 : ℝ)*∑ π : Equiv.Perm (Fin 4),v (quarticTuple (A,π))

lemma quarticFeatureMap_sq_le (v : EuclideanSpace ℝ (Fin 4 → Fin N)) :
    (∑ A : SYKEdge.KSet N 4,(quarticFeatureMap v A)^2)≤(1/24 : ℝ)*‖v‖^2 := by
  have hc : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ)=24 := by norm_num [Fintype.card_perm]
  have hA (A : SYKEdge.KSet N 4) :
      (quarticFeatureMap v A)^2 ≤ (1/24 : ℝ)*∑ π : Equiv.Perm (Fin 4),(v (quarticTuple (A,π)))^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
      (fun _ : Equiv.Perm (Fin 4) ↦ (1 : ℝ)) (fun π ↦ v (quarticTuple (A,π)))
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hc] at hh
    unfold quarticFeatureMap
    nlinarith
  calc
    _≤∑ A : SYKEdge.KSet N 4,(1/24 : ℝ)*∑ π : Equiv.Perm (Fin 4),(v (quarticTuple (A,π)))^2 :=
      Finset.sum_le_sum (fun A _ ↦ hA A)
    _=(1/24 : ℝ)*∑ a : SYKEdge.KSet N 4 × Equiv.Perm (Fin 4),(v (quarticTuple a))^2 := by
      rw [←Finset.mul_sum,Fintype.sum_prod_type]
    _≤(1/24 : ℝ)*∑ b : Fin 4 → Fin N,(v b)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _=∑ b∈Finset.univ.image quarticTuple,(v b)^2 := by
          rw [Finset.sum_image]
          exact quarticTuple_injective.injOn
        _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b hb hnot ↦ sq_nonneg (v b))
    _=(1/24 : ℝ)*‖v‖^2 := by simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]

lemma symmetricQuarticForm_feature (A : SYKEdge.KSet N 4)
    (u : Fin 4 → EuclideanSpace ℝ (Fin N)) :
    symmetricQuarticForm A u=quarticFeatureMap (productTensor u) A := by
  rw [symmetricQuarticForm_apply,quarticFeatureMap]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin 4)))
  intro π
  change (∏ r : Fin 4,u (π r) (quarticLabel A r))=
    ∏ r : Fin 4,u r (quarticLabel A (π.symm r))
  apply Fintype.prod_equiv π
  intro r
  simp

lemma quarticFeatureMap_sub (v w : EuclideanSpace ℝ (Fin 4 → Fin N)) (A : SYKEdge.KSet N 4) :
    quarticFeatureMap (v-w) A=quarticFeatureMap v A-quarticFeatureMap w A := by
  simp [quarticFeatureMap,PiLp.sub_apply,Finset.sum_sub_distrib,mul_sub]

lemma quartic_features_increment_sq (u v : Fin 4 → EuclideanSpace ℝ (Fin N))
    (hu : ∀ r,‖u r‖=1) (hv : ∀ r,‖v r‖=1) :
    (∑ A : SYKEdge.KSet N 4,(symmetricQuarticForm A u-symmetricQuarticForm A v)^2)≤
      (1/24 : ℝ)*∑ r : Fin 4,‖u r-v r‖^2 := by
  simp_rw [symmetricQuarticForm_feature,←quarticFeatureMap_sub]
  exact (quarticFeatureMap_sq_le _).trans
    (mul_le_mul_of_nonneg_left (productTensor_dist_sq_le u v hu hv) (by norm_num))

lemma disorderQuarticForm_sub (w z : Disorder N) :
    disorderQuarticForm (w-z)=disorderQuarticForm w-disorderQuarticForm z := by
  unfold disorderQuarticForm
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  change (w A-z A) • symmetricQuarticForm A = _
  module

lemma disorderQuarticForm_smul (c : ℝ) (w : Disorder N) :
    disorderQuarticForm (c • w)=c • disorderQuarticForm w := by
  simp [disorderQuarticForm,smul_smul,Finset.smul_sum]

lemma disorderQuarticForm_norm_le (w : Disorder N) :
    ‖disorderQuarticForm w‖≤Real.sqrt (1/24 : ℝ)*‖(WithLp.toLp 2 w : EuclideanSpace ℝ (SYKEdge.KSet N 4))‖ := by
  apply multilinear_norm_le_of_unit _ (by positivity)
  intro u hu
  have hf := quarticFeatureMap_sq_le (productTensor u)
  rw [productTensor_norm_sq] at hf
  simp only [hu,one_pow,Finset.prod_const_one,mul_one] at hf
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ w
    (fun A ↦ symmetricQuarticForm A u)
  simp_rw [symmetricQuarticForm_feature] at hc
  have he : (∑ A : SYKEdge.KSet N 4,w A^2)=
      ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (SYKEdge.KSet N 4))‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs]
  rw [he] at hc
  have hsq := mul_le_mul_of_nonneg_left hf (sq_nonneg ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (SYKEdge.KSet N 4))‖)
  have hs : (Real.sqrt (1/24 : ℝ))^2=(1/24 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [disorderQuarticForm,ContinuousMultilinearMap.sum_apply,ContinuousMultilinearMap.smul_apply,smul_eq_mul,Real.norm_eq_abs]
  change |∑ A : SYKEdge.KSet N 4,w A*symmetricQuarticForm A u|≤_
  simp_rw [symmetricQuarticForm_feature]
  have habs := sq_abs (∑ A : SYKEdge.KSet N 4,w A*quarticFeatureMap (productTensor u) A)
  nlinarith [abs_nonneg (∑ A : SYKEdge.KSet N 4,w A*quarticFeatureMap (productTensor u) A),
    mul_nonneg (Real.sqrt_nonneg (1/24 : ℝ))
      (norm_nonneg (WithLp.toLp 2 w : EuclideanSpace ℝ (SYKEdge.KSet N 4)))]

end SYKFastMix.FastMixing

end
end


-- Solutions.GaussianLinearFields
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace SYKFastMix.FastMixing

lemma hasGaussianLaw_standard_coordinates {ι : Type} [Fintype ι] :
    HasGaussianLaw (id : (ι → ℝ) → (ι → ℝ)) (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) := by
  let U : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toContinuousLinearMap
  have hG : HasGaussianLaw (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) := by
    constructor
    rw [map_pi_eq_stdGaussian]
    infer_instance
  simpa only [Function.comp_def,U,PiLp.continuousLinearEquiv_apply,WithLp.ofLp_toLp] using! hG.map U

lemma standard_coordinates_isGaussian {ι : Type} [Fintype ι] :
    IsGaussian (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) := by
  have hh := (hasGaussianLaw_standard_coordinates (ι := ι)).isGaussian_map
  simpa only [Measure.map_id] using hh

def linearField {ι : Type} [Fintype ι] (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ where
  toFun z := ∑ i,a i*z i
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum,mul_assoc,mul_left_comm]
  cont := by fun_prop

lemma linearField_isGaussianProcess {T ι : Type} [Fintype ι] (a : T → ι → ℝ) :
    IsGaussianProcess (fun t z ↦ linearField (a t) z) (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) := by
  constructor
  intro s
  let L : (ι → ℝ) →L[ℝ] (s → ℝ) := ContinuousLinearMap.pi (fun t ↦ linearField (a t))
  exact (hasGaussianLaw_standard_coordinates (ι := ι)).map L

lemma integral_standard_coordinate {ι : Type} [Fintype ι] (i : ι) :
    (∫ z : ι → ℝ,z i ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))=0 := by
  simpa using (MeasureTheory.integral_comp_eval (μ := fun _ : ι ↦ gaussianReal 0 1) (i := i)
    aestronglyMeasurable_id).trans integral_id_gaussianReal

lemma integral_linearField {ι : Type} [Fintype ι] (a : ι → ℝ) :
    (∫ z : ι → ℝ,linearField a z ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))=0 := by
  have hI (i : ι) : Integrable (fun z : ι → ℝ ↦ z i)
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).integrable_comp_of_integrable
      (IsGaussian.integrable_id (μ := gaussianReal 0 1))
  simp only [linearField,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk]
  rw [integral_finset_sum]
  · simp only [integral_const_mul,integral_standard_coordinate,mul_zero,Finset.sum_const_zero]
  · intro i hi
    exact (hI i).const_mul _

lemma standard_coordinate_covariance {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun z : ι → ℝ ↦ z i, fun z : ι → ℝ ↦ z j;
      Measure.pi (fun _ : ι ↦ gaussianReal 0 1)]=(if i=j then 1 else 0) := by
  have hG (k : ι) : MemLp (fun z : ι → ℝ ↦ z k) 2
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving (measurePreserving_eval _ k)
  rw [← covarianceBilin_apply_basisFun hG i j]
  change covarianceBilin ((Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map (WithLp.toLp 2))
    (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)=_
  rw [map_pi_eq_stdGaussian,covarianceBilin_stdGaussian]
  rw [innerSL_apply_apply,EuclideanSpace.basisFun_inner]
  simp

lemma integral_linearField_sq {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (∫ z : ι → ℝ,(linearField a z)^2 ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))=∑ i,a i^2 := by
  have hG (k : ι) : MemLp (fun z : ι → ℝ ↦ z k) 2
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving (measurePreserving_eval _ k)
  have hI : MemLp (linearField a) 2 (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) :=
    ((hasGaussianLaw_standard_coordinates (ι := ι)).map (linearField a)).memLp_two
  have hc : cov[linearField a,linearField a;Measure.pi (fun _ : ι ↦ gaussianReal 0 1)]=∑ i,a i^2 := by
    change cov[fun z : ι → ℝ ↦ ∑ i,a i*z i,fun z : ι → ℝ ↦ ∑ i,a i*z i;
      Measure.pi (fun _ : ι ↦ gaussianReal 0 1)]=_
    rw [covariance_fun_sum_fun_sum (fun k ↦ (hG k).const_mul _) (fun k ↦ (hG k).const_mul _)]
    simp_rw [covariance_const_mul_left,covariance_const_mul_right,standard_coordinate_covariance]
    simp [pow_two]
  rw [covariance_eq_sub hI hI,integral_linearField,mul_zero,sub_zero] at hc
  simpa only [pow_two] using! hc

end SYKFastMix.FastMixing

end
end


-- Solutions.FiniteSupIntegration
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MeasureTheory Filter Topology TopologicalSpace
namespace SYKFastMix.FastMixing

lemma integrable_finset_sup' {T Ω : Type} [DecidableEq T] [MeasurableSpace Ω]
    (P : Measure Ω) (X : T → Ω → ℝ) (s : Finset T) (hs : s.Nonempty)
    (hX : ∀ t∈s, Integrable (X t) P) : Integrable (fun ω ↦ s.sup' hs (fun t ↦ X t ω)) P := by
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert t s ht ih =>
    by_cases hne : s.Nonempty
    · have he (ω : Ω) : (insert t s).sup' hs (fun t ↦ X t ω)=
          max (X t ω) (s.sup' hne (fun t ↦ X t ω)) := by rw [Finset.sup'_insert]
      simp_rw [he]
      exact (hX t (by simp)).sup (ih hne (fun u hu ↦ hX u (by simp [hu])))
    · have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      simpa using hX t (by simp)

lemma integral_iSup_le_of_finite_sup {T Ω : Type} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ) (bound : Ω → ℝ)
    (hB : Integrable bound P) (hX : ∀ t, AEStronglyMeasurable (X t) P)
    (hbound : ∀ ω t, ‖X t ω‖≤bound ω) (hcont : ∀ ω, Continuous (fun t ↦ X t ω))
    (C : ℝ) (hfinite : ∀ (s : Finset T) (hs : s.Nonempty),
      (∫ ω, s.sup' hs (fun t ↦ X t ω) ∂P)≤C) :
    Integrable (fun ω ↦ ⨆ t,X t ω) P ∧ (∫ ω, (⨆ t,X t ω) ∂P)≤C := by
  classical
  let u := TopologicalSpace.denseSeq T
  let s (n : ℕ) := (Finset.range (n+1)).image u
  have hs (n : ℕ) : (s n).Nonempty := by exact Finset.Nonempty.image (by simp) _
  let f (n : ℕ) (ω : Ω) := (s n).sup' (hs n) (fun t ↦ X t ω)
  have hiX (t : T) : Integrable (X t) P := hB.mono' (hX t) (ae_of_all _ (fun ω ↦ hbound ω t))
  have hif (n : ℕ) : Integrable (f n) P := integrable_finset_sup' P X (s n) (hs n) (fun t ht ↦ hiX t)
  have hfbound (n : ℕ) (ω : Ω) : ‖f n ω‖≤bound ω := by
    obtain ⟨t,ht,he⟩ := Finset.exists_mem_eq_sup' (hs n) (fun t ↦ X t ω)
    change ‖(s n).sup' (hs n) (fun t ↦ X t ω)‖≤_
    rw [he]
    exact hbound ω t
  have hlim (ω : Ω) : Tendsto (fun n ↦ f n ω) atTop (nhds (⨆ t,X t ω)) := by
    have hm : Monotone (fun n ↦ f n ω) := by
      intro n m hnm
      exact Finset.sup'_mono (fun t ↦ X t ω) (Finset.image_subset_image (Finset.range_mono (by omega))) (hs n)
    have hb : BddAbove (Set.range (fun n ↦ f n ω)) := by
      refine ⟨bound ω,?_⟩
      rintro y ⟨n,rfl⟩
      exact (le_abs_self _).trans (hfbound n ω)
    have hbX : BddAbove (Set.range (fun t ↦ X t ω)) := by
      refine ⟨bound ω,?_⟩
      rintro y ⟨t,rfl⟩
      exact (le_abs_self _).trans (hbound ω t)
    have he : (⨆ n,f n ω)=(⨆ t,X t ω) := by
      apply le_antisymm
      · apply ciSup_le
        intro n
        apply Finset.sup'_le (hs n)
        intro t ht
        exact le_ciSup hbX t
      · apply ciSup_le
        intro t
        refine (TopologicalSpace.denseRange_denseSeq T).induction_on
          (p := fun t ↦ X t ω≤⨆ n,f n ω) t (isClosed_le (hcont ω) continuous_const) ?_
        intro n
        have hmem : u n∈s n := Finset.mem_image.mpr ⟨n,by simp,rfl⟩
        have hlow : X (u n) ω≤f n ω := Finset.le_sup' (fun t ↦ X t ω) hmem
        exact hlow.trans (le_ciSup hb n)
    rw [← he]
    exact tendsto_atTop_ciSup hm hb
  have ht := tendsto_integral_of_dominated_convergence bound (fun n ↦ (hif n).aestronglyMeasurable)
    hB (fun n ↦ ae_of_all _ (hfbound n)) (ae_of_all _ hlim)
  refine ⟨?_,le_of_tendsto ht (Eventually.of_forall (fun n ↦ hfinite (s n) (hs n)))⟩
  apply hB.mono' (aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ (hif n).aestronglyMeasurable) (ae_of_all _ hlim))
  exact ae_of_all _ (fun ω ↦ le_of_tendsto (hlim ω).norm
    (Eventually.of_forall (fun n ↦ hfbound n ω)))

end SYKFastMix.FastMixing

end
end


-- Solutions.GaussianSupremumAdapter
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory HighDimProb.RandomProcesses TopologicalSpace
namespace SYKFastMix.FastMixing

lemma integral_sup_gaussian_comparison {T Ω : Type} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ t, ∫ ω, X t ω ∂P=0) (hYmean : ∀ t, ∫ ω, Y t ω ∂P=0)
    (hinc : ∀ t s, (∫ ω,(X t ω-X s ω)^2 ∂P)≤∫ ω,(Y t ω-Y s ω)^2 ∂P)
    (bound upper : Ω → ℝ) (hbound : Integrable bound P) (hupper : Integrable upper P)
    (hXbound : ∀ ω t, ‖X t ω‖≤bound ω) (hYupper : ∀ ω t, Y t ω≤upper ω)
    (hcont : ∀ ω, Continuous (fun t ↦ X t ω)) :
    Integrable (fun ω ↦ ⨆ t,X t ω) P ∧
      (∫ ω,(⨆ t,X t ω) ∂P)≤∫ ω,upper ω ∂P := by
  classical
  have hcomp := sudakov_fernique P X Y hXG hYG hXmean hYmean hinc
  have hYint (t : T) : Integrable (Y t) P := (hYG.hasGaussianLaw_eval t).integrable
  have hYsup : processESup P Y≤((∫ ω,upper ω ∂P : ℝ) : EReal) := by
    unfold processESup
    apply iSup_le
    intro s
    apply EReal.coe_le_coe_iff.mpr
    apply integral_mono (integrable_finset_sup' P Y s.1 s.2 (fun t ht ↦ hYint t)) hupper
    intro ω
    apply Finset.sup'_le
    intro t ht
    exact hYupper ω t
  apply integral_iSup_le_of_finite_sup P X bound hbound
    (fun t ↦ (hXG.hasGaussianLaw_eval t).integrable.aestronglyMeasurable) hXbound hcont
  intro s hs
  apply EReal.coe_le_coe_iff.mp
  calc
    _≤processESup P X := by
      unfold processESup
      exact le_iSup (fun s : {s : Finset T // s.Nonempty} ↦
        ((∫ ω,s.1.sup' s.2 (fun t ↦ X t ω) ∂P : ℝ) : EReal)) ⟨s,hs⟩
    _≤processESup P Y := hcomp
    _≤_ := hYsup

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticGaussianFields
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory
namespace SYKFastMix.FastMixing
variable {N : ℕ}

abbrev QuarticGaussianIndex (N : ℕ) := SYKEdge.KSet N 4 ⊕ (Fin 4 × Fin N)

def quarticGaussianFeatures (σ : ℝ) (u : QuarticInputs N) : QuarticGaussianIndex N → ℝ
  | Sum.inl A => σ*symmetricQuarticForm A (fun r ↦ (u r).1)
  | Sum.inr _ => 0

def referenceGaussianFeatures (c : ℝ) (u : QuarticInputs N) : QuarticGaussianIndex N → ℝ
  | Sum.inl _ => 0
  | Sum.inr a => c*(u a.1).1 a.2

lemma quarticGaussian_increment (σ : ℝ) (u v : QuarticInputs N) :
    (∫ z : QuarticGaussianIndex N → ℝ,
      (linearField (quarticGaussianFeatures σ u) z-linearField (quarticGaussianFeatures σ v) z)^2
      ∂Measure.pi (fun _ ↦ gaussianReal 0 1))≤
    (σ^2/24)*∑ r : Fin 4,‖(u r).1-(v r).1‖^2 := by
  have he : (fun z ↦ linearField (quarticGaussianFeatures σ u) z-linearField (quarticGaussianFeatures σ v) z)=
      fun z ↦ linearField (fun i ↦ quarticGaussianFeatures σ u i-quarticGaussianFeatures σ v i) z := by
    funext z
    simp [linearField,sub_mul,Finset.sum_sub_distrib]
  have he2 := congrArg (fun f : (QuarticGaussianIndex N → ℝ) → ℝ ↦
    ∫ z,(f z)^2 ∂Measure.pi (fun _ ↦ gaussianReal 0 1)) he
  rw [he2,integral_linearField_sq]
  simp only [Fintype.sum_sum_type,quarticGaussianFeatures,sub_zero,sub_self,
    zero_pow (by omega : (2 : ℕ)≠0),Finset.sum_const_zero,add_zero]
  simp_rw [←mul_sub,mul_pow,←Finset.mul_sum]
  have h := quartic_features_increment_sq (fun r ↦ (u r).1) (fun r ↦ (v r).1)
    (fun r ↦ (u r).2) (fun r ↦ (v r).2)
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg σ)).trans_eq (by ring)

lemma referenceGaussian_increment (c : ℝ) (u v : QuarticInputs N) :
    (∫ z : QuarticGaussianIndex N → ℝ,
      (linearField (referenceGaussianFeatures c u) z-linearField (referenceGaussianFeatures c v) z)^2
      ∂Measure.pi (fun _ ↦ gaussianReal 0 1))=
    c^2*∑ r : Fin 4,‖(u r).1-(v r).1‖^2 := by
  have he : (fun z ↦ linearField (referenceGaussianFeatures c u) z-linearField (referenceGaussianFeatures c v) z)=
      fun z ↦ linearField (fun i ↦ referenceGaussianFeatures c u i-referenceGaussianFeatures c v i) z := by
    funext z
    simp [linearField,sub_mul,Finset.sum_sub_distrib]
  have he2 := congrArg (fun f : (QuarticGaussianIndex N → ℝ) → ℝ ↦
    ∫ z,(f z)^2 ∂Measure.pi (fun _ ↦ gaussianReal 0 1)) he
  rw [he2,integral_linearField_sq]
  simp only [Fintype.sum_sum_type,referenceGaussianFeatures,sub_self,
    zero_pow (by omega : (2 : ℕ)≠0),Finset.sum_const_zero,zero_add,Fintype.sum_prod_type,
    ←mul_sub,mul_pow,←Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [EuclideanSpace.norm_sq_eq,PiLp.sub_apply,Real.norm_eq_abs,sq_abs]

end SYKFastMix.FastMixing

end
end


-- Solutions.GaussianBlockNorm
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
namespace SYKFastMix.FastMixing

variable {ι κ : Type} [Fintype ι] [Fintype κ]

def coordinateBlock (a : κ → ι) : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun k ↦ ContinuousLinearMap.proj (a k)))

lemma coordinateBlock_apply (a : κ → ι) (z : ι → ℝ) :
    coordinateBlock a z=WithLp.toLp 2 (fun k ↦ z (a k)) := rfl

lemma integral_standard_coordinate_sq [DecidableEq ι] (i : ι) :
    (∫ z : ι → ℝ,(z i)^2 ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))=1 := by
  have h := integral_linearField_sq (Pi.single i 1)
  simpa [linearField,Pi.single_apply] using! h

lemma coordinateBlock_memLp (a : κ → ι) :
    MemLp (fun z ↦ ‖coordinateBlock a z‖) 2 (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) :=
  ((hasGaussianLaw_standard_coordinates (ι := ι)).map (coordinateBlock a)).memLp_two.norm

lemma integral_coordinateBlock_norm_sq [DecidableEq ι] (a : κ → ι) :
    (∫ z : ι → ℝ,‖coordinateBlock a z‖^2 ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))=Fintype.card κ := by
  simp only [coordinateBlock_apply,EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs]
  rw [integral_finset_sum]
  · simp only [integral_standard_coordinate_sq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  · intro k hk
    exact (IsGaussian.memLp_two_id.comp_measurePreserving
      (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) (a k))).integrable_sq

lemma integral_coordinateBlock_norm_le [DecidableEq ι] (a : κ → ι) :
    (∫ z : ι → ℝ,‖coordinateBlock a z‖ ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))≤
      Real.sqrt (Fintype.card κ) := by
  have h := variance_nonneg (fun z ↦ ‖coordinateBlock a z‖) (Measure.pi (fun _ : ι ↦ gaussianReal 0 1))
  rw [variance_eq_sub (coordinateBlock_memLp a)] at h
  change 0≤(∫ z,‖coordinateBlock a z‖^2 ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))-_ at h
  rw [integral_coordinateBlock_norm_sq] at h
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card κ) : (0 : ℝ)≤_)
  nlinarith [Real.sqrt_nonneg (Fintype.card κ)]

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticGaussianSupremum
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped RealInnerProductSpace
namespace SYKFastMix.FastMixing
variable {N : ℕ}

instance quarticInputs_nonempty [NeZero N] : Nonempty (QuarticInputs N) :=
  ⟨fun _ ↦ ⟨EuclideanSpace.single (0 : Fin N) 1,by simp⟩⟩

lemma quarticGaussian_field (σ : ℝ) (u : QuarticInputs N) (z : QuarticGaussianIndex N → ℝ) :
    linearField (quarticGaussianFeatures σ u) z=
      disorderQuarticForm (fun A ↦ σ*z (Sum.inl A)) (fun r ↦ (u r).1) := by
  simp [linearField,Fintype.sum_sum_type,quarticGaussianFeatures,disorderQuarticForm,mul_assoc,mul_comm,mul_left_comm]

lemma referenceGaussian_field (c : ℝ) (u : QuarticInputs N) (z : QuarticGaussianIndex N → ℝ) :
    linearField (referenceGaussianFeatures c u) z=
      c*∑ r : Fin 4,inner ℝ ((u r).1) (coordinateBlock (fun i ↦ Sum.inr (r,i)) z) := by
  simp [linearField,Fintype.sum_sum_type,Fintype.sum_prod_type,referenceGaussianFeatures,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,coordinateBlock_apply,Finset.mul_sum,mul_assoc,mul_comm]

lemma referenceGaussian_field_le (c : ℝ) (hc : 0≤c) (u : QuarticInputs N)
    (z : QuarticGaussianIndex N → ℝ) :
    linearField (referenceGaussianFeatures c u) z≤
      c*∑ r : Fin 4,‖coordinateBlock (fun i ↦ Sum.inr (r,i)) z‖ := by
  rw [referenceGaussian_field]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Finset.sum_le_sum
  intro r hr
  exact (real_inner_le_norm _ _).trans_eq (by rw [(u r).2,one_mul])

lemma integral_quarticGaussian_norm_le [NeZero N] (σ c : ℝ) (hc : 0≤c)
    (hscale : σ^2/24≤c^2) :
    Integrable (fun z : QuarticGaussianIndex N → ℝ ↦
      ‖disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))‖)
      (Measure.pi (fun _ ↦ gaussianReal 0 1)) ∧
    (∫ z : QuarticGaussianIndex N → ℝ,
      ‖disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))‖ ∂Measure.pi (fun _ ↦ gaussianReal 0 1))≤
      4*c*Real.sqrt N := by
  let P : Measure (QuarticGaussianIndex N → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)
  let X : QuarticInputs N → (QuarticGaussianIndex N → ℝ) → ℝ := fun u ↦ linearField (quarticGaussianFeatures σ u)
  let Y : QuarticInputs N → (QuarticGaussianIndex N → ℝ) → ℝ := fun u ↦ linearField (referenceGaussianFeatures c u)
  let B := fun z : QuarticGaussianIndex N → ℝ ↦
    |σ| *Real.sqrt (1/24 : ℝ)*‖coordinateBlock Sum.inl z‖
  let U := fun z : QuarticGaussianIndex N → ℝ ↦
    c*∑ r : Fin 4,‖coordinateBlock (fun i ↦ Sum.inr (r,i)) z‖
  have hB : Integrable B P := ((coordinateBlock_memLp Sum.inl).integrable (by norm_num)).const_mul _
  have hU : Integrable U P := (integrable_finset_sum _ (fun r hr ↦
    (coordinateBlock_memLp (fun i ↦ Sum.inr (r,i))).integrable (by norm_num))).const_mul c
  have h := integral_sup_gaussian_comparison P X Y
    (linearField_isGaussianProcess _) (linearField_isGaussianProcess _)
    (fun u ↦ integral_linearField _) (fun u ↦ integral_linearField _) ?_ B U hB hU ?_ ?_ ?_
  · have he : (fun z ↦ ⨆ u,X u z)=fun z ↦ ‖disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))‖ := by
      funext z
      simp only [X,quarticGaussian_field,←quartic_norm_eq_sup]
    rw [he] at h
    refine ⟨h.1,h.2.trans ?_⟩
    dsimp [U]
    rw [integral_const_mul,integral_finset_sum]
    · calc
        _≤c*∑ r : Fin 4,Real.sqrt N := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun r hr ↦ by simpa using integral_coordinateBlock_norm_le (fun i : Fin N ↦ Sum.inr (r,i)))) hc
        _=_ := by simp; ring
    · intro r hr
      exact (coordinateBlock_memLp (fun i ↦ Sum.inr (r,i))).integrable (by norm_num)
  · intro u v
    exact (quarticGaussian_increment σ u v).trans
      ((mul_le_mul_of_nonneg_right hscale (Finset.sum_nonneg (fun r hr ↦ sq_nonneg _))).trans_eq
        (referenceGaussian_increment c u v).symm)
  · intro z u
    dsimp [X,B]
    rw [quarticGaussian_field]
    calc
      _≤‖disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))‖ := by
        simpa only [(u _).2,Finset.prod_const_one,mul_one,Real.norm_eq_abs] using
          (disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))).le_opNorm (fun r ↦ (u r).1)
      _≤_ := by
        have hn := disorderQuarticForm_norm_le (fun A ↦ σ*z (Sum.inl A))
        have he : (WithLp.toLp 2 (fun A ↦ σ*z (Sum.inl A)) : EuclideanSpace ℝ (SYKEdge.KSet N 4))=
            σ • coordinateBlock Sum.inl z := by ext A; rfl
        rw [he,norm_smul,Real.norm_eq_abs] at hn
        simpa only [mul_assoc,mul_left_comm,mul_comm] using hn
  · intro z u
    exact referenceGaussian_field_le c hc u z
  · intro z
    change Continuous (fun u : QuarticInputs N ↦ linearField (quarticGaussianFeatures σ u) z)
    simp_rw [quarticGaussian_field]
    apply (disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))).cont.comp
    exact continuous_pi (fun r ↦ continuous_subtype_val.comp (continuous_apply r))

end SYKFastMix.FastMixing

end
end


-- Solutions.ExponentialTailMoments
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory Set
namespace SYKFastMix.FastMixing

lemma exponential_tail_moments {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (hY : Measurable Y) (hpos : ∀ ω,0≤Y ω)
    (htail : ∀ t : ℝ,0<t → μ {ω | t≤Y ω}≤ENNReal.ofReal (Real.exp (-t))) (n : ℕ) :
    Integrable (fun ω ↦ Y ω^(n+1)) μ ∧ (∫ ω,Y ω^(n+1) ∂μ)≤(n+1).factorial := by
  have hp (x : ℝ) : (∫ t in (0 : ℝ)..x,((n+1 : ℕ) : ℝ)*t^n)=x^(n+1) := by
    rw [intervalIntegral.integral_const_mul,integral_pow]
    have hn : ((n+1 : ℕ) : ℝ)≠0 := by positivity
    simp only [zero_pow (by omega : n+1≠0),sub_zero]
    field_simp
    push_cast
    ring
  have hG : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)*t^n) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := (n+1 : ℕ)) (by positivity) using 1
    funext t
    rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast]
  have hGn := hG.const_mul ((n+1 : ℕ) : ℝ)
  have hEval : (∫ t in Ioi (0 : ℝ),((n+1 : ℕ) : ℝ)*(Real.exp (-t)*t^n))=(n+1).factorial := by
    rw [integral_const_mul]
    have hh := Real.Gamma_eq_integral (s := ((n+1 : ℕ) : ℝ)) (by positivity)
    have he : (fun t : ℝ ↦ Real.exp (-t)*t^(((n+1 : ℕ) : ℝ)-1))=
        fun t ↦ Real.exp (-t)*t^n := by
      funext t
      rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast]
    rw [he] at hh
    rw [←hh,show ((n+1 : ℕ) : ℝ)=(n : ℝ)+1 by norm_cast,Real.Gamma_nat_eq_factorial,
      Nat.factorial_succ,Nat.cast_mul]
    norm_cast
  have hl := lintegral_comp_eq_lintegral_meas_le_mul μ (Filter.Eventually.of_forall hpos)
    hY.aemeasurable (g := fun t : ℝ ↦ ((n+1 : ℕ) : ℝ)*t^n)
    (fun t ht ↦ (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 t)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.le _))
  simp_rw [hp] at hl
  have hbound : (∫⁻ ω,ENNReal.ofReal (Y ω^(n+1)) ∂μ)≤ENNReal.ofReal ((n+1).factorial : ℝ) := by
    rw [hl]
    calc
      _≤∫⁻ t in Ioi (0 : ℝ),ENNReal.ofReal (((n+1 : ℕ) : ℝ)*(Real.exp (-t)*t^n)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have hh : μ {ω | t≤Y ω} * ENNReal.ofReal (((n+1 : ℕ) : ℝ)*t^n) ≤
            ENNReal.ofReal (Real.exp (-t))*ENNReal.ofReal (((n+1 : ℕ) : ℝ)*t^n) := by
          gcongr
          exact htail t ht
        exact hh.trans_eq (by
          rw [←ENNReal.ofReal_mul (Real.exp_nonneg _)]
          congr 1
          ring)
      _=ENNReal.ofReal ((n+1).factorial : ℝ) := by
        rw [←ofReal_integral_eq_lintegral_ofReal hGn]
        · rw [hEval]
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_nonneg _) (pow_nonneg ht.le _))
  have hI : Integrable (fun ω ↦ Y ω^(n+1)) μ := by
    refine ⟨(hY.pow_const _).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hpos _) _)]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hI,?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall (fun ω ↦ pow_nonneg (hpos ω) (n+1)))
  rw [←he] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp hbound

end SYKFastMix.FastMixing

end
end


-- Solutions.GaussianLipschitzMoments
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory Set
namespace SYKFastMix.FastMixing

lemma memLp_nat_iff_integrable_pow_nonneg {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hpos : ∀ ω,0≤f ω) (n : ℕ) (hn : n≠0) :
    MemLp f n μ ↔ Integrable (fun ω ↦ f ω^n) μ := by
  have hh := integrable_norm_rpow_iff hf (p := (n : ENNReal)) (by exact_mod_cast hn) (by simp)
  simpa only [ENNReal.toReal_natCast,Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (hpos _)] using hh.symm

lemma lpNorm_nat_eq_integral_pow_nonneg {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hpos : ∀ ω,0≤f ω) (n : ℕ) (hn : n≠0) :
    lpNorm f n μ=(∫ ω,f ω^n ∂μ)^((n : ℝ)⁻¹) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hn) (by simp) hf]
  simp only [ENNReal.toReal_natCast,Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (hpos _)]

lemma gaussian_lipschitz_moments {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (hpos : ∀ z,0≤f z) (L : ℝ) (hL : 0<L)
    (hLip : ∀ x y,|f x-f y|≤L*Real.sqrt (∑ i,(x i-y i)^2))
    (k : ℕ) (hk : 1≤k) :
    MemLp f (2*k : ℕ) (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) ∧
    lpNorm f (2*k : ℕ) (Measure.pi (fun _ : ι ↦ gaussianReal 0 1))≤
      (∫ z,f z ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1))+L*Real.sqrt (2*k) := by
  let P : Measure (ι → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)
  let b : ℝ := ∫ z,f z ∂P
  let h : (ι → ℝ) → ℝ := fun z ↦ max ((f z-b)/L) 0
  let Y : (ι → ℝ) → ℝ := fun z ↦ (h z)^2/2
  have hh : Measurable h := (hf.sub measurable_const).div_const L |>.max measurable_const
  have hY : Measurable Y := (hh.pow_const 2).div_const 2
  have hp (z) : 0≤h z := le_max_right _ _
  have hb : 0≤b := integral_nonneg hpos
  have htail (t : ℝ) (ht : 0<t) : P {z | t≤Y z}≤ENNReal.ofReal (Real.exp (-t)) := by
    have hs := Real.sq_sqrt (by positivity : 0≤2*t)
    have hincl : {z | t≤Y z}⊆{z | b+L*Real.sqrt (2*t)≤f z} := by
      intro z hz
      change t≤h z^2/2 at hz
      have hst : 0<Real.sqrt (2*t) := Real.sqrt_pos.2 (by positivity)
      have hhge : Real.sqrt (2*t)≤h z := by nlinarith [hp z]
      have hhpos : 0<h z := lt_of_lt_of_le hst hhge
      have he : h z=(f z-b)/L := max_eq_left (by
        by_contra hn
        have : h z=0 := max_eq_right (le_of_not_ge hn)
        linarith)
      rw [he] at hhge
      have ht := (le_div_iff₀ hL).mp hhge
      change b+L*Real.sqrt (2*t)≤f z
      calc
        _=b+Real.sqrt (2*t)*L := by ring
        _≤b+(f z-b) := add_le_add le_rfl ht
        _=f z := by ring
    have hc := (GaussianMatrix.gaussian_concentration_vector f L hL hLip
      (Real.sqrt (2*t)) (Real.sqrt_nonneg _)).2
    apply (measure_mono hincl).trans
    have heq : -(Real.sqrt (2*t))^2/2 = -t := by rw [hs]; ring
    rw [heq] at hc
    exact hc
  obtain ⟨hI,hbound⟩ := exponential_tail_moments P Y hY (fun z ↦ by dsimp [Y]; positivity) htail (k-1)
  have he : k-1+1=k := by omega
  rw [he] at hI hbound
  have hrel (z) : h z^(2*k)=(2 : ℝ)^k*Y z^k := by
    dsimp [Y]
    rw [div_pow,←pow_mul]
    field_simp
  have hIp : Integrable (fun z ↦ h z^(2*k)) P := (hI.const_mul ((2 : ℝ)^k)).congr
    (Filter.Eventually.of_forall (fun z ↦ (hrel z).symm))
  have hmoment : (∫ z,h z^(2*k) ∂P)≤(Real.sqrt (2*k))^(2*k) := by
    calc
      _=(2 : ℝ)^k*∫ z,Y z^k ∂P := by simp_rw [hrel]; rw [integral_const_mul]
      _≤(2 : ℝ)^k*(k.factorial : ℝ) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _≤(2 : ℝ)^k*(k : ℝ)^k := by
        gcongr
        exact_mod_cast Nat.factorial_le_pow k
      _=(Real.sqrt (2*k))^(2*k) := by
        rw [pow_mul,Real.sq_sqrt (by positivity),mul_pow]
  have hmem := (memLp_nat_iff_integrable_pow_nonneg P h hh.aestronglyMeasurable hp (2*k) (by omega)).2 hIp
  have hlp : lpNorm h (2*k : ℕ) P≤Real.sqrt (2*k) := by
    rw [lpNorm_nat_eq_integral_pow_nonneg P h hh.aestronglyMeasurable hp _ (by omega)]
    calc
      _≤((Real.sqrt (2*k))^(2*k))^(((2*k : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (integral_nonneg (fun z ↦ pow_nonneg (hp z) _)) hmoment (by positivity)
      _=Real.sqrt (2*k) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (Real.sqrt_nonneg _)]
        rw [mul_inv_cancel₀ (by positivity : ((2*k : ℕ) : ℝ)≠0),Real.rpow_one]
  have hsMem : MemLp (fun z ↦ b+L*h z) (2*k : ℕ) P := (memLp_const b).add (hmem.const_mul L)
  have hpoint (z) : f z≤b+L*h z := by
    have hg := le_max_left ((f z-b)/L) (0 : ℝ)
    have hmul := mul_le_mul_of_nonneg_left hg hL.le
    dsimp [h]
    field_simp at hmul
    linarith
  have hfMem : MemLp f (2*k : ℕ) P := hsMem.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z ↦ by rw [Real.norm_of_nonneg (hpos z)]; exact hpoint z))
  refine ⟨hfMem,?_⟩
  calc
    _≤lpNorm (fun z ↦ b+L*h z) (2*k : ℕ) P := lpNorm_mono_real hsMem (fun z ↦ by
      rw [Real.norm_of_nonneg (hpos z)]; exact hpoint z)
    _≤lpNorm (fun _ : ι → ℝ ↦ b) (2*k : ℕ) P+lpNorm (fun z ↦ L*h z) (2*k : ℕ) P :=
      lpNorm_add_le (memLp_const b) (by norm_cast; omega)
    _=b+L*lpNorm h (2*k : ℕ) P := by
      change lpNorm (fun _ : ι → ℝ ↦ b) (2*k : ℕ) P+lpNorm (L • h) (2*k : ℕ) P = _
      rw [lpNorm_const (by norm_cast; omega) (by exact MeasureTheory.IsProbabilityMeasure.ne_zero P),
        lpNorm_const_smul]
      simp [P,Real.norm_of_nonneg hb,Real.norm_of_nonneg hL.le]
    _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlp hL.le)

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticGaussianMoments
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory
namespace SYKFastMix.FastMixing
variable {N : ℕ}

def quarticGaussianNorm (σ : ℝ) (z : QuarticGaussianIndex N → ℝ) : ℝ :=
  ‖disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))‖

lemma quarticGaussianNorm_measurable (σ : ℝ) : Measurable (quarticGaussianNorm (N := N) σ) := by
  apply Continuous.measurable
  unfold quarticGaussianNorm disorderQuarticForm
  fun_prop

lemma quarticGaussianNorm_lipschitz (σ : ℝ) (x y : QuarticGaussianIndex N → ℝ) :
    |quarticGaussianNorm σ x-quarticGaussianNorm σ y|≤
      ((abs σ) *Real.sqrt (1/24 : ℝ))*Real.sqrt (∑ i : QuarticGaussianIndex N,(x i-y i)^2) := by
  have hd := norm_sub_norm_le (disorderQuarticForm (fun A ↦ σ*x (Sum.inl A)))
    (disorderQuarticForm (fun A ↦ σ*y (Sum.inl A)))
  have hn := disorderQuarticForm_norm_le (fun A ↦ σ*(x (Sum.inl A)-y (Sum.inl A)))
  have he : disorderQuarticForm (fun A ↦ σ*(x (Sum.inl A)-y (Sum.inl A)))=
      disorderQuarticForm (fun A ↦ σ*x (Sum.inl A))-disorderQuarticForm (fun A ↦ σ*y (Sum.inl A)) := by
    rw [←disorderQuarticForm_sub]
    congr 1
    ext A
    simp [mul_sub]
  rw [he] at hn
  have hv : (WithLp.toLp 2 (fun A ↦ σ*(x (Sum.inl A)-y (Sum.inl A))) : EuclideanSpace ℝ (SYKEdge.KSet N 4))=
      σ • WithLp.toLp 2 (fun A ↦ x (Sum.inl A)-y (Sum.inl A)) := by ext A; rfl
  rw [hv,norm_smul,Real.norm_eq_abs] at hn
  have hb : ‖(WithLp.toLp 2 (fun A ↦ x (Sum.inl A)-y (Sum.inl A)) : EuclideanSpace ℝ (SYKEdge.KSet N 4))‖≤
      Real.sqrt (∑ i : QuarticGaussianIndex N,(x i-y i)^2) := by
    apply Real.le_sqrt_of_sq_le
    simp only [EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi ↦ sq_nonneg _))
  have hn' := (mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg σ) (Real.sqrt_nonneg (1/24 : ℝ))))
  have hn2 : ‖disorderQuarticForm (fun A ↦ σ*x (Sum.inl A))-disorderQuarticForm (fun A ↦ σ*y (Sum.inl A))‖≤
      ((abs σ) *Real.sqrt (1/24 : ℝ))*Real.sqrt (∑ i : QuarticGaussianIndex N,(x i-y i)^2) := by
    exact hn.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hn')
  apply abs_le.mpr
  constructor
  · have hrev := norm_sub_norm_le (disorderQuarticForm (fun A ↦ σ*y (Sum.inl A)))
      (disorderQuarticForm (fun A ↦ σ*x (Sum.inl A)))
    rw [norm_sub_rev] at hrev
    dsimp [quarticGaussianNorm]
    linarith
  · exact hd.trans hn2

lemma quarticGaussianNorm_moments [NeZero N] (σ : ℝ) (hσ : σ≠0) (k : ℕ) (hk : 1≤k) :
    MemLp (quarticGaussianNorm (N := N) σ) (2*k : ℕ) (Measure.pi (fun _ ↦ gaussianReal 0 1)) ∧
    lpNorm (quarticGaussianNorm (N := N) σ) (2*k : ℕ) (Measure.pi (fun _ ↦ gaussianReal 0 1))≤
      ((abs σ) *Real.sqrt (1/24 : ℝ))*(4*Real.sqrt N+Real.sqrt (2*k)) := by
  have hL : 0<(abs σ) *Real.sqrt (1/24 : ℝ) := mul_pos (abs_pos.2 hσ) (Real.sqrt_pos.2 (by norm_num))
  have h := gaussian_lipschitz_moments (quarticGaussianNorm (N := N) σ)
    (quarticGaussianNorm_measurable σ) (fun z ↦ norm_nonneg _)
    ((abs σ) *Real.sqrt (1/24 : ℝ)) hL (quarticGaussianNorm_lipschitz σ) k hk
  have hmean := (integral_quarticGaussian_norm_le (N := N) σ ((abs σ) *Real.sqrt (1/24 : ℝ)) hL.le (by
    rw [mul_pow,sq_abs,Real.sq_sqrt (by norm_num : (0 : ℝ)≤1/24)]
    ring_nf
    exact le_rfl)).2
  refine ⟨h.1,h.2.trans ?_⟩
  change (∫ z : QuarticGaussianIndex N → ℝ,‖disorderQuarticForm (fun A ↦ σ*z (Sum.inl A))‖ ∂Measure.pi (fun _ ↦ gaussianReal 0 1)) + _ ≤ _
  nlinarith

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticGaussianLaw
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma standard_quartic_marginal :
    MeasurePreserving (fun z : QuarticGaussianIndex N → ℝ ↦ fun A : SYKEdge.KSet N 4 ↦ z (Sum.inl A))
      (Measure.pi (fun _ ↦ gaussianReal 0 1)) (Measure.pi (fun _ ↦ gaussianReal 0 1)) := by
  have h := measurePreserving_sumPiEquivProdPi (fun _ : QuarticGaussianIndex N ↦ gaussianReal 0 1)
  exact (measurePreserving_fst (μ := Measure.pi (fun _ : SYKEdge.KSet N 4 ↦ gaussianReal 0 1))
    (ν := Measure.pi (fun _ : Fin 4 × Fin N ↦ gaussianReal 0 1))).comp h

def disorderSigma (Q : Model N) : ℝ := Real.sqrt (6*Q.J^2/(N : ℝ)^3)

def disorderScale (Q : Model N) (z : QuarticGaussianIndex N → ℝ) : Disorder N :=
  fun A ↦ disorderSigma Q*z (Sum.inl A)

lemma disorderSigma_pos (Q : Model N) : 0<disorderSigma Q := by
  have hJ := Q.positive
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by have := Q.size; omega)
  unfold disorderSigma
  positivity

lemma disorderScale_map (Q : Model N) :
    (Measure.pi (fun _ : QuarticGaussianIndex N ↦ gaussianReal 0 1)).map (disorderScale Q)=disorderLaw Q := by
  have he : disorderScale Q=(fun w : Disorder N ↦ fun A ↦ disorderSigma Q*w A) ∘
      (fun z : QuarticGaussianIndex N → ℝ ↦ fun A : SYKEdge.KSet N 4 ↦ z (Sum.inl A)) := rfl
  rw [he,←Measure.map_map (by fun_prop) (by fun_prop),standard_quartic_marginal.map_eq,
    Measure.pi_map_pi (f := fun _ : SYKEdge.KSet N 4 ↦ fun x : ℝ ↦ disorderSigma Q*x) (fun A ↦ (measurable_const.mul measurable_id).aemeasurable)]
  unfold disorderLaw
  congr 1
  funext A
  rw [gaussianReal_map_const_mul,mul_zero,mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk]
  have hJ := Q.positive
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by have := Q.size; omega)
  rw [disorderSigma,Real.sq_sqrt (by positivity),Real.coe_toNNReal _ (by positivity)]

lemma disorder_tensornorm_measurable : Measurable (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) := by
  apply Continuous.measurable
  unfold disorderQuarticForm
  fun_prop

lemma disorder_tensornorm_moments (Q : Model N) (k : ℕ) (hk : 1≤k) :
    MemLp (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) (2*k : ℕ) (disorderLaw Q) ∧
    lpNorm (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) (2*k : ℕ) (disorderLaw Q)≤
      (|disorderSigma Q| *Real.sqrt (1/24 : ℝ))*(4*Real.sqrt N+Real.sqrt (2*k)) := by
  letI : NeZero N := ⟨by have := Q.size; omega⟩
  have h := quarticGaussianNorm_moments (N := N) (disorderSigma Q) (disorderSigma_pos Q).ne' k hk
  have hm := disorder_tensornorm_measurable (N := N)
  have hmap := disorderScale_map Q
  have hmem : MemLp (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) (2*k : ℕ) (disorderLaw Q) := by
    rw [←hmap]
    exact (memLp_map_measure_iff hm.aestronglyMeasurable (by apply Measurable.aemeasurable; unfold disorderScale; fun_prop)).2 h.1
  refine ⟨hmem,?_⟩
  have hi : lpNorm (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) (2*k : ℕ) (disorderLaw Q)=
      lpNorm (quarticGaussianNorm (N := N) (disorderSigma Q)) (2*k : ℕ) (Measure.pi (fun _ ↦ gaussianReal 0 1)) := by
    rw [lpNorm_nat_eq_integral_pow_nonneg _ _ hm.aestronglyMeasurable (fun w ↦ norm_nonneg _) _ (by omega),
      lpNorm_nat_eq_integral_pow_nonneg _ _ (quarticGaussianNorm_measurable _).aestronglyMeasurable (fun z ↦ norm_nonneg _) _ (by omega)]
    congr 1
    rw [←hmap,integral_map (by apply Measurable.aemeasurable; unfold disorderScale; fun_prop) (hm.pow_const _).aestronglyMeasurable]
    rfl
  exact hi.le.trans h.2

end SYKFastMix.FastMixing

end
end


-- Solutions.QuarticGaussianConstant
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory ProbabilityTheory
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma disorder_tensornorm_scaled_moment (Q : Model N) (k : ℕ) (hk : 1≤k) (hkN : k≤7*N) :
    24*(N : ℝ)*lpNorm (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) (2*k : ℕ) (disorderLaw Q)≤105*Q.J := by
  have hJ := Q.positive
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by have := Q.size; omega)
  have hNk : (k : ℝ)≤7*N := by exact_mod_cast hkN
  let L := |disorderSigma Q| *Real.sqrt (1/24 : ℝ)
  have hL : 0≤L := by dsimp [L]; positivity
  have hNne := hN.ne'
  have hLsq : L^2=Q.J^2/(4*(N : ℝ)^3) := by
    dsimp [L,disorderSigma]
    rw [mul_pow,sq_abs,Real.sq_sqrt (by positivity),Real.sq_sqrt (by norm_num : (0 : ℝ)≤1/24)]
    ring
  have hsN : (Real.sqrt N)^2=(N : ℝ) := Real.sq_sqrt hN.le
  have hP : (2*(N : ℝ)*L*Real.sqrt N)^2=Q.J^2 := by
    rw [mul_pow,mul_pow,mul_pow,hLsq,hsN]
    field_simp
    ring
  have hPe : 2*(N : ℝ)*L*Real.sqrt N=Q.J := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) hN.le) hL) (Real.sqrt_nonneg (N : ℝ))]
  have hks : Real.sqrt (2*k)≤4*Real.sqrt N := by
    have hsk := Real.sq_sqrt (show (0 : ℝ)≤2*k by positivity)
    nlinarith [Real.sqrt_nonneg (2*(k : ℝ)),Real.sqrt_nonneg (N : ℝ)]
  have hb := (disorder_tensornorm_moments Q k hk).2
  have hm : lpNorm (fun w : Disorder N ↦ ‖disorderQuarticForm w‖) (2*k : ℕ) (disorderLaw Q)≤
      L*(8*Real.sqrt N) := by
    exact hb.trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hks) hL).trans_eq (by ring))
  have hh := mul_le_mul_of_nonneg_left hm (show 0≤24*(N : ℝ) by positivity)
  have hEq : 24*(N : ℝ)*(L*(8*Real.sqrt N))=96*Q.J := by
    calc
      _=96*(2*(N : ℝ)*L*Real.sqrt N) := by ring
      _=_ := by rw [hPe]
  rw [hEq] at hh
  exact hh.trans (by nlinarith)

end SYKFastMix.FastMixing

end
end


-- Solutions.PolynomialMomentMajorant
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open MeasureTheory
namespace SYKFastMix.FastMixing

lemma lpNorm_pow_nat_nonneg {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g μ) (hpos : ∀ ω,0≤g ω) (m q : ℕ) (hm : 0 < m) (hq : 0 < q) :
    lpNorm (fun ω ↦ g ω^m) q μ=(lpNorm g (m*q : ℕ) μ)^m := by
  rw [lpNorm_nat_eq_integral_pow_nonneg μ (fun ω ↦ g ω^m) (hg.pow m) (fun ω ↦ pow_nonneg (hpos ω) _) q hq.ne',
    lpNorm_nat_eq_integral_pow_nonneg μ _ hg hpos (m*q) (Nat.mul_ne_zero hm.ne' hq.ne')]
  simp_rw [←pow_mul]
  rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg (fun ω ↦ pow_nonneg (hpos ω) _))]
  congr 1
  push_cast
  field_simp

lemma polynomial_moment_majorant {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfp : ∀ ω,0≤f ω) (hgp : ∀ ω,0≤g ω) (B C : ℝ) (hB : 0≤B)
    (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hq1 : 1≤(q : ENNReal))
    (hmem : MemLp g (m*q : ℕ) μ) (hmajor : ∀ ω,f ω≤(B*g ω)^m)
    (hbound : B*lpNorm g (m*q : ℕ) μ≤C) :
    Integrable (fun ω ↦ f ω^q) μ ∧ lpNorm f q μ≤C^m := by
  have hgI := (memLp_nat_iff_integrable_pow_nonneg μ g hg hgp (m*q) (Nat.mul_ne_zero hm.ne' hq.ne')).1 hmem
  have hpowI : Integrable (fun ω ↦ (g ω^m)^q) μ := by simpa only [←pow_mul] using hgI
  have hpowMem := (memLp_nat_iff_integrable_pow_nonneg μ (fun ω ↦ g ω^m)
    (hg.pow m) (fun ω ↦ pow_nonneg (hgp ω) _) q hq.ne').2 hpowI
  have hsMem : MemLp (fun ω ↦ B^m*g ω^m) q μ := hpowMem.const_mul (B^m)
  have hnorm (ω) : ‖f ω‖≤B^m*g ω^m := by
    rw [Real.norm_of_nonneg (hfp ω)]
    simpa only [mul_pow] using hmajor ω
  have hfMem := hsMem.mono' hf (Filter.Eventually.of_forall hnorm)
  refine ⟨(memLp_nat_iff_integrable_pow_nonneg μ f hf hfp q hq.ne').1 hfMem,?_⟩
  calc
    _≤lpNorm (fun ω ↦ B^m*g ω^m) q μ := lpNorm_mono_real hsMem hnorm
    _=B^m*lpNorm (fun ω ↦ g ω^m) q μ := by
      change lpNorm ((B^m) • (fun ω ↦ g ω^m)) q μ=_
      rw [lpNorm_const_smul]
      change ‖B^m‖ * _ = _
      rw [Real.norm_of_nonneg (pow_nonneg hB m)]
    _=(B*lpNorm g (m*q : ℕ) μ)^m := by rw [lpNorm_pow_nat_nonneg μ g hg hgp m q hm hq,mul_pow]
    _≤C^m := pow_le_pow_left₀ (mul_nonneg hB lpNorm_nonneg) hbound m

end SYKFastMix.FastMixing

end
end


-- Solutions.GibbsCalculus
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)

lemma mexp_smul_add (H : Mat ι) (a b : ℂ) :
    mexp (a • H) * mexp (b • H) = mexp ((a+b) • H) := by
  have hc : Commute (a • H) (b • H) := by
    change (a • H) * (b • H) = (b • H) * (a • H)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm a b]
  exact (NormedSpace.exp_add_of_commute (𝔸 := Mat ι) hc).symm.trans (by rw [← add_smul]; rfl)

lemma mexp_smul_cancel (H : Mat ι) (a : ℂ) : mexp (a • H) * mexp ((-a) • H) = 1 := by
  rw [mexp_smul_add]
  simp [mexp]

lemma mexp_norm_le [Nonempty ι] (H : Mat ι) : ‖mexp H‖ ≤ Real.exp ‖H‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H
  have hr := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖H‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  apply h.norm_le_of_bounded hr
  intro n
  simp only [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le H n) (by positivity)

lemma mexp_smul_norm_le [Nonempty ι] (H : Mat ι) (a : ℝ) :
    ‖mexp ((a : ℂ) • H)‖ ≤ Real.exp (|a| * ‖H‖) := by
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using mexp_norm_le ((a : ℂ) • H)

lemma mexp_hermitian (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    (mexp ((a : ℂ) • H)).IsHermitian := by
  exact (hH.smul (by simp [IsSelfAdjoint])).exp

lemma mexp_spectral (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    mexp ((a : ℂ) • H) = Unitary.conjStarAlgAut ℂ (Mat ι) hH.eigenvectorUnitary
      (Matrix.diagonal (fun i ↦ (Real.exp (a * hH.eigenvalues i) : ℂ))) := by
  let U := Unitary.conjStarAlgAut ℂ (Mat ι) hH.eigenvectorUnitary
  letI : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)
  have hm := NormedSpace.map_exp U U.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
    (Matrix.diagonal (fun i ↦ (a * hH.eigenvalues i : ℂ)))
  have hdiag : (a : ℂ) • H = U (Matrix.diagonal (fun i ↦ (a * hH.eigenvalues i : ℂ))) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [← map_smul, ← Matrix.diagonal_smul]
    rfl
  change NormedSpace.exp ((a : ℂ) • H) = _
  rw [hdiag, ← hm, Matrix.exp_diagonal]
  congr 1
  congr 1
  funext i
  simp only [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_mul,
    Complex.ofReal_exp]

lemma mexp_trace (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    Matrix.trace (mexp ((a : ℂ) • H)) = (∑ i, Real.exp (a * hH.eigenvalues i) : ℝ) := by
  rw [mexp_spectral H hH a, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp

lemma mexp_trace_pos [Nonempty ι] (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    0 < (Matrix.trace (mexp ((a : ℂ) • H))).re := by
  rw [mexp_trace H hH a, Complex.ofReal_re]
  exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _) Finset.univ_nonempty

lemma mexp_half_hsSq (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) :
    hsSq (mexp (((-(β/2) : ℝ) : ℂ) • H)) =
      (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re := by
  rw [hsSq, hsInner, (mexp_hermitian H hH (-(β/2))).eq, mexp_smul_add]
  congr 3
  push_cast
  ring

lemma weighted_density_inner (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) (X : Mat ι) :
    hsInner (mexp (((-(β/2) : ℝ) : ℂ) • H))
      (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)) = Matrix.trace X := by
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  have hBRB : B*R*B=1 := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((-(β/2) : ℝ) : ℂ) • H) *
      mexp (((β/4 : ℝ) : ℂ) • H) = 1
    rw [mexp_smul_add, mexp_smul_add]
    have hz : (((β/4 : ℝ) : ℂ) + ((-(β/2) : ℝ) : ℂ) + ((β/4 : ℝ) : ℂ)) = 0 := by
      push_cast
      ring
    rw [hz]
    simp [mexp]
  change Matrix.trace (Rᴴ * (B*X*B)) = _
  rw [(mexp_hermitian H hH (-(β/2))).eq]
  calc
    Matrix.trace (R * (B*X*B)) = Matrix.trace ((R*B)*X*B) := by congr 1; noncomm_ring
    _ = Matrix.trace (B*(R*B)*X) := Matrix.trace_mul_cycle (R*B) X B
    _ = Matrix.trace ((B*R*B)*X) := by congr 1; noncomm_ring
    _ = _ := by rw [hBRB, one_mul]

lemma weighted_density_hs_le [Nonempty ι] (H : Mat ι) (β : ℝ) (hβ : 0 ≤ β)
    (X : Mat ι) (hX : IsDensity X) :
    hs (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)) ≤
      Real.exp (β * ‖H‖ / 2) := by
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  have hB : ‖B‖ ≤ Real.exp (β/4 * ‖H‖) := by
    simpa only [abs_of_nonneg (by positivity : 0 ≤ β/4)] using mexp_smul_norm_le H (β/4)
  have hnorm : hs X ≤ 1 := by
    have h := density_hsSq_le_one X hX
    have hsqr := Real.sq_sqrt (hsSq_nonneg X)
    change Real.sqrt (hsSq X) ≤ 1
    nlinarith [Real.sqrt_nonneg (hsSq X)]
  calc
    _ = hs (B*(X*B)) := by rw [mul_assoc]
    _ ≤ ‖B‖ * hs (X*B) := hs_mul_left_le B (X*B)
    _ ≤ Real.exp (β/4*‖H‖) * (1 * Real.exp (β/4*‖H‖)) := by
      apply mul_le_mul hB ?_ (Real.sqrt_nonneg _) (Real.exp_pos _).le
      exact (hs_mul_right_le X B).trans (mul_le_mul hnorm hB (norm_nonneg _) (by norm_num))
    _ = _ := by rw [one_mul, ← Real.exp_add]; congr 1 <;> ring

lemma weighted_density_projection [Nonempty ι] (H : Mat ι) (hH : H.IsHermitian)
    (β : ℝ) (hβ : 0 ≤ β) (X : Mat ι) (hX : IsDensity X) :
    let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
    let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
    let W := mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)
    hsInner (gibbsRoot H β) (W - (Z⁻¹ : ℂ) • R) = 0 ∧
      hs (W - (Z⁻¹ : ℂ) • R) ≤ Real.exp (β * ‖H‖ / 2) := by
  dsimp only
  have hZ := mexp_trace_pos H hH (-β)
  have hp := hs_projection_bound (mexp (((-(β/2) : ℝ) : ℂ) • H))
    (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H))
    ((Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re) hZ (mexp_half_hsSq H hH β)
    (by rw [weighted_density_inner H hH β X, hX.2])
  constructor
  · unfold gibbsRoot
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] at hp ⊢
    rw [hsInner_smul_left, hp.1, mul_zero]
  · apply le_trans (Real.sqrt_le_sqrt hp.2)
    exact weighted_density_hs_le H β hβ X hX

lemma gibbs_congruence_identity (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) :
    let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
    let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
    let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
    C * ((Z⁻¹ : ℂ) • R) * C = gibbs H β := by
  dsimp only
  rw [mul_smul_comm, smul_mul_assoc]
  have he : mexp (((-(β/4) : ℝ) : ℂ) • H) * mexp (((-(β/2) : ℝ) : ℂ) • H) *
      mexp (((-(β/4) : ℝ) : ℂ) • H) = mexp (((-β : ℝ) : ℂ) • H) := by
    rw [mexp_smul_add, mexp_smul_add]
    congr 1
    congr 1
    push_cast
    ring
  rw [he]
  have hz : Matrix.trace (mexp (((-β : ℝ) : ℂ) • H)) =
      ((Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re : ℂ) := by
    rw [mexp_trace H hH (-β)]
    simp only [Complex.ofReal_re]
  unfold gibbs
  simp only [Complex.ofReal_neg] at hz ⊢
  rw [hz]
  simp only [Complex.ofReal_re]

end SYKFastMix.FastMixing

end
end


-- Solutions.DiagonalGap
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexConjugate

lemma diagonal_gap_decay {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ev : ι → ℝ) (r x : ι → ℂ) (rate t : ℝ) (hrate : 0 < rate) (ht : 0 ≤ t)
    (hr : ∀ i, (ev i : ℂ)*r i=0)
    (hgap : ∀ y : ι → ℂ, star r ⬝ᵥ y=0 →
      rate * (∑ i, ‖y i‖^2) ≤ ∑ i, ev i * ‖y i‖^2)
    (hx : star r ⬝ᵥ x=0) :
    (∑ i, ‖(Real.exp (-t*ev i) : ℂ) * x i‖^2) ≤
      (Real.exp (-rate*t))^2 * ∑ i, ‖x i‖^2 := by
  have hrzero (i : ι) (hi : ev i ≠ 0) : r i=0 :=
    (mul_eq_zero.mp (hr i)).resolve_left (by exact_mod_cast hi)
  let z : ι → ℂ := fun i ↦ if ev i=0 then x i else 0
  have hzortho : star r ⬝ᵥ z=0 := by
    calc
      _ = star r ⬝ᵥ x := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : ev i=0
        · simp [z, he]
        · simp [z, he, hrzero i he]
      _ = 0 := hx
  have hzquad : (∑ i, ev i * ‖z i‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases he : ev i=0 <;> simp [z, he]
  have hzsum : (∑ i, ‖z i‖^2)=0 := by
    have h := hgap z hzortho
    rw [hzquad] at h
    have hn : 0 ≤ ∑ i, ‖z i‖^2 := by positivity
    nlinarith
  have hxzero (i : ι) (hi : ev i=0) : x i=0 := by
    have hs : ‖z i‖^2 ≤ ∑ j, ‖z j‖^2 :=
      Finset.single_le_sum (f := fun j ↦ ‖z j‖^2) (fun j hj ↦ sq_nonneg _) (Finset.mem_univ i)
    rw [hzsum] at hs
    have hzi : z i=0 := by simpa only [sq_nonpos_iff, norm_eq_zero] using hs
    simpa only [z, if_pos hi] using hzi
  have hev (i : ι) (hi : ev i ≠ 0) : rate ≤ ev i := by
    have ho : star r ⬝ᵥ Pi.single i (1 : ℂ)=0 := by simp [dotProduct, Pi.single_apply, apply_ite, hrzero i hi]
    have h := hgap (Pi.single i (1 : ℂ)) ho
    simpa [Pi.single_apply, apply_ite, eq_comm] using h
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hzero : ev i=0
  · simp [hxzero i hzero]
  · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have he := hev i hzero
    nlinarith

end
end


-- Solutions.SpectralDecay
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma hermitian_repr_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Mat ι) (hA : A.IsHermitian) (x : EuclideanSpace ℂ ι) (i : ι) :
    hA.eigenvectorBasis.repr ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) i =
      (hA.eigenvalues i : ℂ) * hA.eigenvectorBasis.repr x i := by
  have he : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    change (A *ᵥ (hA.eigenvectorBasis i : ι → ℂ)) j = _
    rw [hA.mulVec_eigenvectorBasis]
    rfl
  have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (hA.eigenvectorBasis i) x
  change inner ℂ ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (hA.eigenvectorBasis i)) x =
    inner ℂ (hA.eigenvectorBasis i) ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) at hs
  simp only [OrthonormalBasis.repr_apply_apply]
  rw [← hs, he, inner_smul_left]
  simp

lemma repr_exp_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℂ)
    (hdiag : ∀ x i, b.repr (T x) i = ev i * b.repr x i) (x : E) (i : ι) :
    b.repr ((NormedSpace.exp T) x) i = Complex.exp (ev i) * b.repr x i := by
  let L : (E →L[ℂ] E) →L[ℂ] ℂ := {
    toFun := fun U ↦ b.repr (U x) i
    map_add' := by intro U V; simp
    map_smul' := by intro z U; simp
    cont := by fun_prop }
  have hp (n : ℕ) : L (T^n) = (ev i)^n * b.repr x i := by
    induction n with
    | zero => simp [L]
    | succ n ih =>
      change b.repr ((T^(n+1)) x) i = _
      rw [pow_succ', ContinuousLinearMap.mul_apply, hdiag]
      change ev i * L (T^n) = _
      rw [ih, pow_succ]
      ring
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL L
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (ev i)).mul_right (b.repr x i)
  apply HasSum.unique h
  convert! hscalar using 1
  · funext n
    rw [map_smul, hp]
    simp only [smul_eq_mul]
    ring
  · rw [Complex.exp_eq_exp_ℂ]

lemma basis_qform {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (ev i : ℂ) * b.repr x i) (x : E) :
    (inner ℂ x (T x)).re = ∑ i, ev i * ‖b.repr x i‖^2 := by
  rw [← b.repr.inner_map_map x (T x), EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, hdiag]
  apply Finset.sum_congr rfl
  intro i hi
  change ((ev i : ℂ) * b.repr x i * conj (b.repr x i)).re = _
  rw [mul_assoc, mul_comm (b.repr x i), ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.normSq_eq_norm_sq]

lemma basis_gap_decay {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (ev i : ℂ) * b.repr x i)
    (r x : E) (rate t : ℝ) (hrate : 0 < rate) (ht : 0 ≤ t) (hr : T r=0)
    (hgap : ∀ y : E, inner ℂ r y=0 → rate * ‖y‖^2 ≤ (inner ℂ y (T y)).re)
    (hx : inner ℂ r x=0) :
    ‖(NormedSpace.exp (((-t : ℝ) : ℂ) • T)) x‖ ≤ Real.exp (-rate*t) * ‖x‖ := by
  have hroot (i : ι) : (ev i : ℂ) * b.repr r i=0 := by
    rw [← hdiag, hr, map_zero]
    rfl
  have hgapdiag (y : ι → ℂ) (hy : star (fun i ↦ b.repr r i) ⬝ᵥ y=0) :
      rate * (∑ i, ‖y i‖^2) ≤ ∑ i, ev i * ‖y i‖^2 := by
    let Y := b.repr.symm (WithLp.toLp 2 y)
    have hY : inner ℂ r Y=0 := by
      rw [← b.repr.inner_map_map r Y]
      simpa [Y, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hy
    have h := hgap Y hY
    rw [basis_qform b T ev hdiag, ← b.repr.norm_map Y, EuclideanSpace.norm_sq_eq] at h
    simpa only [Y, LinearIsometryEquiv.apply_symm_apply, WithLp.ofLp_toLp] using h
  have hxdiag : star (fun i ↦ b.repr r i) ⬝ᵥ (fun i ↦ b.repr x i)=0 := by
    rw [← b.repr.inner_map_map r x] at hx
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hx
  have hdecay := diagonal_gap_decay ev (fun i ↦ b.repr r i) (fun i ↦ b.repr x i)
    rate t hrate ht hroot hgapdiag hxdiag
  have hsdiag : ∀ y i, b.repr ((((-t : ℝ) : ℂ) • T) y) i =
      (((-t : ℝ) : ℂ) * (ev i : ℂ)) * b.repr y i := by
    intro y i
    change b.repr (((-t : ℝ) : ℂ) • T y) i = _
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, hdiag, mul_assoc]
  have hcoord (i : ι) : b.repr ((NormedSpace.exp (((-t : ℝ) : ℂ) • T)) x) i =
      (Real.exp (-t*ev i) : ℂ) * b.repr x i := by
    have h := repr_exp_apply b (((-t : ℝ) : ℂ) • T)
      (fun i ↦ (((-t : ℝ) : ℂ) * (ev i : ℂ))) hsdiag x i
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_exp] using h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [mul_pow, ← b.repr.norm_map ((NormedSpace.exp (((-t : ℝ) : ℂ) • T)) x),
    ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [hcoord]
  exact hdecay

lemma basis_exp_fixed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℂ)
    (hdiag : ∀ x i, b.repr (T x) i = ev i * b.repr x i)
    (r : E) (hr : T r=0) (a : ℂ) : (NormedSpace.exp (a • T)) r=r := by
  have hscaled : ∀ y i, b.repr ((a • T) y) i = (a * ev i) * b.repr y i := by
    intro y i
    change b.repr (a • T y) i = _
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, hdiag, mul_assoc]
  apply b.repr.injective
  apply PiLp.ext
  intro i
  rw [repr_exp_apply b (a • T) (fun i ↦ a*ev i) hscaled]
  have hroot : ev i * b.repr r i=0 := by rw [← hdiag, hr, map_zero]; rfl
  rcases mul_eq_zero.mp hroot with hi | hi <;> simp [hi]

end SYKFastMix.FastMixing

end
end


-- Solutions.QuadraticGap
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexConjugate
namespace SYKFastMix.FastMixing

lemma basis_positive_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (ev i : ℂ)*b.repr x i)
    (r : E) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x, 0 ≤ (inner ℂ x (T x)).re)
    (hsq : ∀ x, c*(inner ℂ x (T x)).re ≤ ‖T x‖^2)
    (hker : ∀ x, T x=0 ↔ ∃ z : ℂ, x=z • r)
    (x : E) (hx : inner ℂ r x=0) : c*‖x‖^2 ≤ (inner ℂ x (T x)).re := by
  have heigen (i : ι) : T (b i)=(ev i : ℂ) • b i := by
    apply b.repr.injective
    apply PiLp.ext
    intro j
    rw [hdiag, map_smul, b.repr_self]
    change (ev j : ℂ) * (Pi.single i (1 : ℂ) : ι → ℂ) j =
      (ev i : ℂ) * (Pi.single i (1 : ℂ) : ι → ℂ) j
    by_cases hji : j=i
    · subst j; rfl
    · simp [Pi.single_apply, Ne.symm hji]
  have hnorm (i : ι) : ‖b i‖=1 := b.orthonormal.norm_eq_one i
  have hq (i : ι) : (inner ℂ (b i) (T (b i))).re=ev i := by
    rw [heigen, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hevsq (i : ι) : ‖T (b i)‖^2=(ev i)^2 := by
    rw [heigen, norm_smul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hev (i : ι) (hi : ev i ≠ 0) : c ≤ ev i := by
    have hn := hpos (b i)
    have hs := hsq (b i)
    rw [hq] at hn hs
    rw [hevsq] at hs
    have hp : 0 < ev i := lt_of_le_of_ne hn (Ne.symm hi)
    nlinarith
  have hzero (i : ι) (hi : ev i=0) : b.repr x i=0 := by
    have ht : T (b i)=0 := by rw [heigen, hi]; simp
    obtain ⟨z, hz⟩ := (hker (b i)).mp ht
    rw [b.repr_apply_apply, hz, inner_smul_left, hx, mul_zero]
  rw [basis_qform b T ev hdiag, ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases he : ev i=0
  · rw [hzero i he]
    simp
  · exact mul_le_mul_of_nonneg_right (hev i he) (sq_nonneg _)

end SYKFastMix.FastMixing

end
end


-- Solutions.HermitianSimilarity
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

lemma hermitian_similar_near_identity {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B S Sinv : Mat ι) (hA : A.IsHermitian) (hS : S*Sinv=1) (hiS : Sinv*S=1)
    (hB : B=Sinv*A*S) (δ : ℝ) (hδ : ‖B-1‖ ≤ δ) :
    ∀ x : EuclideanSpace ℂ ι, (1-δ)*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x)).re := by
  let L := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
  have heA (i : ι) : L A (hA.eigenvectorBasis i)=(hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    change (A *ᵥ (hA.eigenvectorBasis i : ι → ℂ)) j = _
    rw [hA.mulVec_eigenvectorBasis]
    rfl
  have hevlower (i : ι) : 1-δ ≤ hA.eigenvalues i := by
    let v := hA.eigenvectorBasis i
    let y := L Sinv v
    have hcancel : L S y=v := by
      change L S (L Sinv v)=v
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hS, map_one]
      rfl
    have hy : y ≠ 0 := by
      intro hy
      rw [hy, map_zero] at hcancel
      exact hA.eigenvectorBasis.orthonormal.ne_zero i hcancel.symm
    have heig : L B y=(hA.eigenvalues i : ℂ) • y := by
      rw [hB, map_mul, map_mul]
      change L Sinv (L A (L S y))=_
      rw [hcancel, heA, map_smul]
    have hdiff : L (B-1) y=((hA.eigenvalues i-1 : ℝ) : ℂ) • y := by
      rw [map_sub, map_one]
      change L B y-y=_
      rw [heig, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    have hn := (L (B-1)).le_opNorm y
    rw [hdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hn
    change |hA.eigenvalues i-1| * ‖y‖ ≤ ‖B-1‖ * ‖y‖ at hn
    have hbound : |hA.eigenvalues i-1| ≤ δ := by
      apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hy)).mp
      exact hn.trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
    have h := (abs_le.mp hbound).1
    linarith
  intro x
  rw [basis_qform hA.eigenvectorBasis (L A) hA.eigenvalues (hermitian_repr_apply A hA),
    ← hA.eigenvectorBasis.repr.norm_map x, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_right (hevlower i) (sq_nonneg _)

end SYKFastMix.FastMixing

end
end


-- Solutions.BlockForms
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

def subblock {I ι : Type} (M : Matrix (I × ι) (I × ι) ℂ) (i j : I) : Mat ι :=
  Matrix.of (fun a b ↦ M (i,a) (j,b))

def stackRows {I ι : Type} (X : I → Mat ι) : Matrix (I × ι) ι ℂ :=
  Matrix.of (fun p k ↦ X p.1 p.2 k)

lemma trace_rectangular_lower_bound {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m m ℂ) (Z : Matrix m n ℂ) (c : ℝ)
    (hM : ∀ x : EuclideanSpace ℂ m, c*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) M) x)).re) :
    c*(∑ j, ∑ i, ‖Z i j‖^2) ≤ (Matrix.trace (Zᴴ*M*Z)).re := by
  let col (j : n) : EuclideanSpace ℂ m := WithLp.toLp 2 (fun i ↦ Z i j)
  have ht : (Matrix.trace (Zᴴ*M*Z)).re =
      ∑ j, (inner ℂ (col j) ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) M) (col j))).re := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, col,
      Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp, Matrix.mulVec, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [mul_comm]
  rw [ht, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  simpa only [EuclideanSpace.norm_sq_eq, col, WithLp.ofLp_toLp] using hM (col j)

lemma hs_block_form_eq_trace {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (M : Matrix (I × ι) (I × ι) ℂ) (X : I → Mat ι) :
    (∑ i, ∑ j, hsInner (X i) (subblock M i j * X j)) =
      Matrix.trace ((stackRows X)ᴴ * M * stackRows X) := by
  rw [Matrix.mul_assoc]
  simp only [hsInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.mul_sum, subblock, stackRows, Matrix.of_apply]
  calc
    _ = ∑ i : I, ∑ k : ι, ∑ j : I, ∑ a : ι, ∑ b : ι,
        star (X i a k) * (M (i,a) (j,b) * X j b k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ i : I, ∑ j : I, ∑ a : ι, ∑ b : ι,
        star (X i a k) * (M (i,a) (j,b) * X j b k) := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

lemma hs_block_form_lower_bound {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι]
    (M : Matrix (I × ι) (I × ι) ℂ) (c : ℝ)
    (hM : ∀ x : EuclideanSpace ℂ (I × ι), c*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := I × ι) (𝕜 := ℂ) M) x)).re)
    (X : I → Mat ι) :
    c*(∑ i, hsSq (X i)) ≤ (∑ i, ∑ j, hsInner (X i) (subblock M i j * X j)).re := by
  rw [hs_block_form_eq_trace]
  have h := trace_rectangular_lower_bound M (stackRows X) c hM
  have he : (∑ k : ι, ∑ p : I × ι, ‖X p.1 p.2 k‖^2) = ∑ i, hsSq (X i) := by
    simp only [Fintype.sum_prod_type, hsSq_eq_sum_columns]
    rw [Finset.sum_comm]
  simpa only [stackRows, Matrix.of_apply, he] using h

end SYKFastMix.FastMixing

end
end


-- Solutions.HighCoefficientBounds
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

lemma traceMoment_one_eq_sum_norm_sq {ι : Type} [Fintype ι] [DecidableEq ι] (A : Mat ι) :
    traceMoment 1 A = ∑ i, ∑ j, ‖A j i‖^2 := by
  simp only [traceMoment, pow_one, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (conj (A j i) * A j i).re = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma norm_matrix_le_card_mul_entry_bound {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Mat ι) (c : ℝ) (hc : 0 ≤ c) (hA : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ (Fintype.card ι : ℝ) * c := by
  have h := (traceMoment_opNorm_bounds 1 A).1
  change ‖A‖^2 ≤ traceMoment 1 A at h
  have ht : traceMoment 1 A ≤ ((Fintype.card ι : ℝ) * c)^2 := by
    rw [traceMoment_one_eq_sum_norm_sq]
    calc
      (∑ i, ∑ j, ‖A j i‖^2) ≤ ∑ _i : ι, ∑ _j : ι, c^2 := by
        gcongr with i j
        exact hA j i
      _ = _ := by simp; ring
  have hpos : 0 ≤ (Fintype.card ι : ℝ) * c := by positivity
  nlinarith [norm_nonneg A]

lemma norm_matrix_single_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) : ‖(Matrix.single i j 1 : Mat ι)‖ ≤ 1 := by
  letI : Nonempty ι := ⟨i⟩
  have h := (traceMoment_opNorm_bounds 1 (Matrix.single i j (1 : ℂ))).1
  rw [traceMoment_one_eq_sum_norm_sq] at h
  simp only [Nat.mul_one] at h
  have ht : (∑ x, ∑ y, ‖(Matrix.single i j (1 : ℂ)) y x‖^2) = (1 : ℝ) := by
    simp [Matrix.single_apply, ite_and, apply_ite, eq_comm]
  rw [ht] at h
  change ‖(Matrix.single i j 1 : Mat ι)‖^2 ≤ 1 at h
  nlinarith [norm_nonneg (Matrix.single i j (1 : ℂ))]

lemma matrix_entry_norm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Mat ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm x
  have he := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) i
  have hx : ‖x‖ = 1 := by simp [x, PiLp.norm_single]
  rw [hx, mul_one] at h
  change _ ≤ ‖A‖ at h
  apply le_trans ?_ h
  convert! he using 1
  simp [x, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single]

lemma majorana_norm_le_one {N : ℕ} (Q : Model N) (i : Fin N) : ‖Q.γ i‖ ≤ 1 := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0, by positivity⟩⟩
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (Q.γ i)
  rw [(Q.car.herm i).eq, Q.car.sq, norm_one] at h
  nlinarith [norm_nonneg (Q.γ i)]

lemma ad_power_apply_norm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (H X : Mat ι) (m : ℕ) :
    ‖applySuper ((ad H)^m) X‖ ≤ (2 * ‖H‖)^m * ‖X‖ := by
  induction m with
  | zero =>
    have he : applySuper (1 : Super ι) X = X := by ext i j; simp [applySuper, Matrix.one_apply]
    simp [he]
  | succ m ih =>
    rw [pow_succ', applySuper_mul]
    have had (Y : Mat ι) : applySuper (ad H) Y = H*Y-Y*H :=
      applySuper_super (leftAct H - rightAct H).toLinearMap Y
    rw [had]
    calc
      ‖H * applySuper (ad H ^ m) X - applySuper (ad H ^ m) X * H‖ ≤
          ‖H * applySuper (ad H ^ m) X‖ + ‖applySuper (ad H ^ m) X * H‖ := norm_sub_le _ _
      _ ≤ ‖H‖ * ‖applySuper (ad H ^ m) X‖ + ‖applySuper (ad H ^ m) X‖ * ‖H‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (2 * ‖H‖)^(m+1) * ‖X‖ := by rw [pow_succ]; nlinarith [norm_nonneg H]

lemma gammaCoefficient_norm_le {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ) (i : Fin N) :
    ‖gammaCoefficient Q w m i‖ ≤ (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) := by
  rw [gammaCoefficient, norm_smul, norm_div, norm_pow]
  simp only [norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hf : 0 < (m.factorial : ℝ) := by positivity
  calc
    1 / (m.factorial : ℝ) * ‖applySuper (ad (hamiltonian Q w)^m) (Q.γ i)‖ ≤
        1 / (m.factorial : ℝ) * ((2*‖hamiltonian Q w‖)^m * ‖Q.γ i‖) := by
      gcongr
      exact ad_power_apply_norm_le _ _ _
    _ ≤ (2*‖hamiltonian Q w‖)^m / (m.factorial : ℝ) := by
      calc
        _ ≤ 1 / (m.factorial : ℝ) * ((2*‖hamiltonian Q w‖)^m * 1) := by
          gcongr
          exact majorana_norm_le_one Q i
        _ = _ := by ring

lemma nat_pow_div_factorial_le_three_pow {N m : ℕ} (hm : N ≤ m) :
    (N : ℝ)^m / (m.factorial : ℝ) ≤ 3^m := by
  calc
    (N : ℝ)^m / (m.factorial : ℝ) ≤ Real.exp (N : ℝ) :=
      Real.pow_div_factorial_le_exp (N : ℝ) (by positivity) m
    _ = (Real.exp 1)^N := by rw [← Real.exp_nat_mul]; simp
    _ ≤ 3^N := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le N
    _ ≤ 3^m := pow_le_pow_right₀ (by norm_num) hm

lemma fermionCoefficient_norm_le {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ) :
    SYKEdge.opNorm (fermionCoefficient Q w m) ≤
      (N : ℝ) * 2^(N/2) * ((2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) Q.size
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : Nonempty (SiteHilbert N) := ⟨⟨0, by positivity⟩⟩
  have he (a b : Fin N × SiteHilbert N) :
      ‖fermionCoefficient Q w m a b‖ ≤ (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) := by
    apply le_trans (matrix_entry_norm_le _ a.2 b.2)
    rw [norm_smul]
    have hnorm : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hnorm]
    have hsum := norm_add_le (Q.γ b.1 * gammaCoefficient Q w m a.1)
      (gammaCoefficient Q w m a.1 * Q.γ b.1)
    have h1 := norm_mul_le (Q.γ b.1) (gammaCoefficient Q w m a.1)
    have h2 := norm_mul_le (gammaCoefficient Q w m a.1) (Q.γ b.1)
    have hγ := majorana_norm_le_one Q b.1
    have hc := gammaCoefficient_norm_le Q w m a.1
    unfold anticomm
    nlinarith [norm_nonneg (gammaCoefficient Q w m a.1)]
  have h := norm_matrix_le_card_mul_entry_bound (fermionCoefficient Q w m)
    ((2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) (by positivity) he
  change ‖fermionCoefficient Q w m‖ ≤ _
  simpa [Fintype.card_prod, SiteHilbert, Nat.cast_mul, Nat.cast_pow, mul_assoc] using h

lemma gamma_bound_high_order {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ)
    (hm : N ≤ m) (hH : ‖hamiltonian Q w‖ ≤ 2 * Q.J * N) :
    (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) ≤ (12 * Q.J)^m := by
  have hJ := Q.positive
  calc
    (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) ≤
        (4 * Q.J * N)^m / (m.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    _ = (4 * Q.J)^m * ((N : ℝ)^m / (m.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ (4 * Q.J)^m * 3^m := by
      gcongr
      exact nat_pow_div_factorial_le_three_pow hm
    _ = (12 * Q.J)^m := by rw [← mul_pow]; congr 1; ring

lemma fermionCoefficient_high_order {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ)
    (hm : N ≤ m) (hH : SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N) :
    SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133 * Q.J)^m := by
  have hJ := Q.positive
  have hdim : (N : ℝ) * 2^(N/2) ≤ (4 : ℝ)^N := by
    have hn : (N : ℝ) ≤ 2^N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
    have hd : (2 : ℝ)^(N/2) ≤ 2^N := pow_le_pow_right₀ (by norm_num) (Nat.div_le_self N 2)
    calc
      (N : ℝ) * 2^(N/2) ≤ 2^N * 2^N := by gcongr
      _ = (4 : ℝ)^N := by rw [← mul_pow]; norm_num
  calc
    _ ≤ (N : ℝ) * 2^(N/2) * ((2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) :=
      fermionCoefficient_norm_le Q w m
    _ ≤ (4 : ℝ)^N * (12 * Q.J)^m := by
      gcongr
      exact gamma_bound_high_order Q w m hm hH
    _ ≤ (4 : ℝ)^m * (12 * Q.J)^m := by
      gcongr <;> norm_num
    _ = (48 * Q.J)^m := by rw [← mul_pow]; congr 1; ring
    _ ≤ (133 * Q.J)^m := by gcongr <;> linarith

end SYKFastMix.FastMixing

end
end


-- Solutions.BlockDomination
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] [Nonempty ι]

def BlockDominated (A : Mat (I×ι)) (B : Matrix I I ℝ) : Prop :=
  ∀ i j, ‖subblock A i j‖ ≤ B i j

lemma subblock_mul (A C : Mat (I×ι)) (i j : I) :
    subblock (A*C) i j=∑ k, subblock A i k*subblock C k j := by
  ext a b
  simp only [subblock,Matrix.of_apply,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.sum_apply]

lemma subblock_conjTranspose (A : Mat (I×ι)) (i j : I) :
    subblock Aᴴ i j=(subblock A j i)ᴴ := by rfl

lemma blockDominated_mul {A C : Mat (I×ι)} {B D : Matrix I I ℝ}
    (hAB : BlockDominated A B) (hCD : BlockDominated C D) :
    BlockDominated (A*C) (B*D) := by
  intro i j
  rw [subblock_mul]
  calc
    _ ≤ ∑ k, ‖subblock A i k*subblock C k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, B i k*D k j := by
      apply Finset.sum_le_sum
      intro k hk
      exact (norm_mul_le _ _).trans (mul_le_mul (hAB i k) (hCD k j)
        (norm_nonneg _) ((norm_nonneg _).trans (hAB i k)))
    _ = _ := rfl

lemma blockDominated_conjTranspose {A : Mat (I×ι)} {B : Matrix I I ℝ}
    (hAB : BlockDominated A B) : BlockDominated Aᴴ B.transpose := by
  intro i j
  rw [subblock_conjTranspose,Matrix.l2_opNorm_conjTranspose]
  exact hAB j i

lemma blockDominated_zero : BlockDominated (0 : Mat (I×ι)) (0 : Matrix I I ℝ) := by
  intro i j
  have he : subblock (0 : Mat (I×ι)) i j=0 := rfl
  rw [he,norm_zero]
  rfl

lemma blockDominated_one : BlockDominated (1 : Mat (I×ι)) (1 : Matrix I I ℝ) := by
  intro i j
  by_cases hij : i=j
  · subst j
    have he : subblock (1 : Mat (I×ι)) i i=1 := by
      ext a b
      simp [subblock,Matrix.one_apply]
    rw [he,Matrix.one_apply_eq]
    exact le_of_eq norm_one
  · have he : subblock (1 : Mat (I×ι)) i j=0 := by
      ext a b
      simp [subblock,Matrix.one_apply,hij]
    rw [he,norm_zero,Matrix.one_apply_ne hij]

lemma blockDominated_pow {A : Mat (I×ι)} {B : Matrix I I ℝ}
    (hAB : BlockDominated A B) (p : ℕ) : BlockDominated (A^p) (B^p) := by
  induction p with
  | zero => simpa using (blockDominated_one (I := I) (ι := ι))
  | succ p ih => simpa only [pow_succ] using blockDominated_mul ih hAB

lemma blockDominated_trace {A : Mat (I×ι)} {B : Matrix I I ℝ}
    (hAB : BlockDominated A B) :
    (Matrix.trace A).re ≤ (Fintype.card ι : ℝ)*Matrix.trace B := by
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ∑ a : ι, ‖A (i,a) (i,a)‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact Complex.re_le_norm _
    _ ≤ ∑ a : ι, B i i := by
      apply Finset.sum_le_sum
      intro a ha
      exact (matrix_entry_norm_le (subblock A i i) a a).trans (hAB i i)
    _ = _ := by simp

end SYKFastMix.FastMixing

end
end


-- Solutions.GaussianBlockPolynomial
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ} {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] [Nonempty ι]

structure GaussianBlockTerm (N : ℕ) (I ι : Type) [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] where
  monomial : List (SYKEdge.KSet N 4)
  quantum : Mat (I×ι)
  classical : Matrix I I ℝ
  dominated : BlockDominated quantum classical

namespace GaussianBlockTerm
variable (t u : GaussianBlockTerm N I ι)
def qeval (w : Disorder N) := couplingMonomial t.monomial w • t.quantum
def reval (w : Disorder N) := couplingMonomial t.monomial w • t.classical

def mul : GaussianBlockTerm N I ι :=
  ⟨t.monomial++u.monomial,t.quantum*u.quantum,t.classical*u.classical,
    blockDominated_mul t.dominated u.dominated⟩
def adjoint : GaussianBlockTerm N I ι :=
  ⟨t.monomial,t.quantumᴴ,t.classical.transpose,blockDominated_conjTranspose t.dominated⟩
def one : GaussianBlockTerm N I ι := ⟨[],1,1,blockDominated_one⟩

lemma qeval_mul (w : Disorder N) : (t.mul u).qeval w=t.qeval w*u.qeval w := by
  simp only [qeval,mul,couplingMonomial_append,smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
lemma reval_mul (w : Disorder N) : (t.mul u).reval w=t.reval w*u.reval w := by
  simp only [reval,mul,couplingMonomial_append,smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
lemma qeval_adjoint (w : Disorder N) : t.adjoint.qeval w=(t.qeval w)ᴴ := by
  simp only [qeval,adjoint,Matrix.conjTranspose_smul,star_trivial]
lemma reval_adjoint (w : Disorder N) : t.adjoint.reval w=(t.reval w).transpose := by
  simp only [reval,adjoint,Matrix.transpose_smul]
lemma qeval_one (w : Disorder N) : (one : GaussianBlockTerm N I ι).qeval w=1 := by
  simp [qeval,one,couplingMonomial_nil]
lemma reval_one (w : Disorder N) : (one : GaussianBlockTerm N I ι).reval w=1 := by
  simp [reval,one,couplingMonomial_nil]

lemma integrable_qtrace (Q : Model N) :
    Integrable (fun w ↦ (Matrix.trace (t.qeval w)).re) (disorderLaw Q) := by
  have he : (fun w ↦ (Matrix.trace (t.qeval w)).re)=
      fun w ↦ couplingMonomial t.monomial w*(Matrix.trace t.quantum).re := by
    funext w
    simp [qeval,Matrix.trace_smul]
  rw [he]
  exact (integrable_couplingMonomial Q t.monomial).mul_const _
lemma integrable_rtrace (Q : Model N) :
    Integrable (fun w ↦ Matrix.trace (t.reval w)) (disorderLaw Q) := by
  have he : (fun w ↦ Matrix.trace (t.reval w))=
      fun w ↦ couplingMonomial t.monomial w*Matrix.trace t.classical := by
    funext w
    simp [reval,Matrix.trace_smul]
  rw [he]
  exact (integrable_couplingMonomial Q t.monomial).mul_const _

lemma integral_trace_le (Q : Model N) :
    (∫ w, (Matrix.trace (t.qeval w)).re ∂disorderLaw Q) ≤
      (Fintype.card ι : ℝ)*∫ w, Matrix.trace (t.reval w) ∂disorderLaw Q := by
  have hq (w : Disorder N) : (Matrix.trace (t.qeval w)).re=
      couplingMonomial t.monomial w*(Matrix.trace t.quantum).re := by
    simp [qeval,Matrix.trace_smul]
  have hr (w : Disorder N) : Matrix.trace (t.reval w)=
      couplingMonomial t.monomial w*Matrix.trace t.classical := by
    simp [reval,Matrix.trace_smul]
  simp_rw [hq,hr]
  rw [integral_mul_const,integral_mul_const]
  have hh := mul_le_mul_of_nonneg_left (blockDominated_trace t.dominated)
    (couplingMonomial_integral_nonneg Q t.monomial)
  calc
    _ ≤ (∫ w, couplingMonomial t.monomial w ∂disorderLaw Q)*
        ((Fintype.card ι : ℝ)*Matrix.trace t.classical) := hh
    _ = _ := by ring
end GaussianBlockTerm

namespace GaussianBlockPolynomial
abbrev Poly (N : ℕ) (I ι : Type) [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] := List (GaussianBlockTerm N I ι)

def qeval (l : Poly N I ι) (w : Disorder N) := (l.map (fun t ↦ t.qeval w)).sum
def reval (l : Poly N I ι) (w : Disorder N) := (l.map (fun t ↦ t.reval w)).sum

def mul (l k : Poly N I ι) : Poly N I ι := l.flatMap (fun t ↦ k.map t.mul)
def adjoint (l : Poly N I ι) : Poly N I ι := l.map GaussianBlockTerm.adjoint
def one : Poly N I ι := [GaussianBlockTerm.one]
def pow (l : Poly N I ι) : ℕ → Poly N I ι
  | 0 => one
  | p+1 => mul (pow l p) l

lemma qeval_mul (l k : Poly N I ι) (w : Disorder N) :
    qeval (mul l k) w=qeval l w*qeval k w := by
  induction l with
  | nil => simp [mul,qeval]
  | cons t l ih =>
    simp only [mul,List.flatMap_cons,qeval,List.map_append,List.sum_append,List.map_cons,List.sum_cons,add_mul] at *
    rw [ih]
    congr 1
    simp only [List.map_map,Function.comp_def,GaussianBlockTerm.qeval_mul]
    exact List.sum_map_mul_left _ _ _

lemma reval_mul (l k : Poly N I ι) (w : Disorder N) :
    reval (mul l k) w=reval l w*reval k w := by
  induction l with
  | nil => simp [mul,reval]
  | cons t l ih =>
    simp only [mul,List.flatMap_cons,reval,List.map_append,List.sum_append,List.map_cons,List.sum_cons,add_mul] at *
    rw [ih]
    congr 1
    simp only [List.map_map,Function.comp_def,GaussianBlockTerm.reval_mul]
    exact List.sum_map_mul_left _ _ _

lemma qeval_adjoint (l : Poly N I ι) (w : Disorder N) :
    qeval (adjoint l) w=(qeval l w)ᴴ := by
  induction l with
  | nil => simp [adjoint,qeval]
  | cons t l ih =>
    simp only [adjoint,List.map_cons,qeval,List.map_cons,List.sum_cons,Matrix.conjTranspose_add] at *
    rw [GaussianBlockTerm.qeval_adjoint,ih]
lemma reval_adjoint (l : Poly N I ι) (w : Disorder N) :
    reval (adjoint l) w=(reval l w).transpose := by
  induction l with
  | nil => simp [adjoint,reval]
  | cons t l ih =>
    simp only [adjoint,List.map_cons,reval,List.map_cons,List.sum_cons,Matrix.transpose_add] at *
    rw [GaussianBlockTerm.reval_adjoint,ih]
lemma qeval_pow (l : Poly N I ι) (p : ℕ) (w : Disorder N) :
    qeval (pow l p) w=(qeval l w)^p := by
  induction p with
  | zero => simp [pow,one,qeval,GaussianBlockTerm.qeval_one]
  | succ p ih => rw [pow,qeval_mul,ih,pow_succ]
lemma reval_pow (l : Poly N I ι) (p : ℕ) (w : Disorder N) :
    reval (pow l p) w=(reval l w)^p := by
  induction p with
  | zero => simp [pow,one,reval,GaussianBlockTerm.reval_one]
  | succ p ih => rw [pow,reval_mul,ih,pow_succ]

lemma integrable_qtrace (Q : Model N) (l : Poly N I ι) :
    Integrable (fun w ↦ (Matrix.trace (qeval l w)).re) (disorderLaw Q) := by
  induction l with
  | nil => simp only [qeval,List.map_nil,List.sum_nil,Matrix.trace_zero,Complex.zero_re]; exact integrable_zero (Disorder N) ℝ (disorderLaw Q)
  | cons t l ih =>
    simpa only [qeval,List.map_cons,List.sum_cons,Matrix.trace_add,Complex.add_re] using!
      (t.integrable_qtrace Q).add ih

lemma integrable_rtrace (Q : Model N) (l : Poly N I ι) :
    Integrable (fun w ↦ Matrix.trace (reval l w)) (disorderLaw Q) := by
  induction l with
  | nil => simp only [reval,List.map_nil,List.sum_nil,Matrix.trace_zero]; exact integrable_zero (Disorder N) ℝ (disorderLaw Q)
  | cons t l ih =>
    simpa only [reval,List.map_cons,List.sum_cons,Matrix.trace_add] using!
      (t.integrable_rtrace Q).add ih

lemma integral_trace_le (Q : Model N) (l : Poly N I ι) :
    (∫ w, (Matrix.trace (qeval l w)).re ∂disorderLaw Q) ≤
      (Fintype.card ι : ℝ)*∫ w, Matrix.trace (reval l w) ∂disorderLaw Q := by
  induction l with
  | nil => simp [qeval,reval]
  | cons t l ih =>
    simp only [qeval,reval,List.map_cons,List.sum_cons,Matrix.trace_add,Complex.add_re]
    change (∫ w, (Matrix.trace (t.qeval w)).re+(Matrix.trace (qeval l w)).re ∂disorderLaw Q) ≤
      (Fintype.card ι : ℝ)*∫ w, Matrix.trace (t.reval w)+Matrix.trace (reval l w) ∂disorderLaw Q
    rw [integral_add (t.integrable_qtrace Q) (integrable_qtrace Q l),
      integral_add (t.integrable_rtrace Q) (integrable_rtrace Q l),mul_add]
    exact add_le_add (t.integral_trace_le Q) ih

lemma moment_comparison (Q : Model N) (l : Poly N I ι) (p : ℕ) :
    Integrable (fun w ↦ traceMoment p (qeval l w)) (disorderLaw Q) ∧
    Integrable (fun w ↦ Matrix.trace (((reval l w).transpose*reval l w)^p)) (disorderLaw Q) ∧
    (∫ w, traceMoment p (qeval l w) ∂disorderLaw Q) ≤ (Fintype.card ι : ℝ)*
      ∫ w, Matrix.trace (((reval l w).transpose*reval l w)^p) ∂disorderLaw Q := by
  let k := pow (mul (adjoint l) l) p
  have hq (w : Disorder N) : qeval k w=((qeval l w)ᴴ*qeval l w)^p := by
    simp only [k,qeval_pow,qeval_mul,qeval_adjoint]
  have hr (w : Disorder N) : reval k w=((reval l w).transpose*reval l w)^p := by
    simp only [k,reval_pow,reval_mul,reval_adjoint]
  have hiq := integrable_qtrace Q k
  have hir := integrable_rtrace Q k
  have hc := integral_trace_le Q k
  simp only [hq,hr] at hiq hir hc
  exact ⟨hiq,hir,hc⟩

end GaussianBlockPolynomial
end SYKFastMix.FastMixing

end
end


-- Solutions.QuantumPathExpansion
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma list_sum_smul_left {α K M : Type} [Semiring K] [AddCommMonoid M] [Module K M]
    (l : List α) (c : K) (f : α → M) :
    (l.map (fun a ↦ c • f a)).sum=c • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,smul_add]

lemma word_slot_quantum_children (Q : Model N) (w : Disorder N) (s : WordSlot N) :
    (∑ A : SYKEdge.KSet N 4, (w A : ℂ) •
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ (-1 : ℂ)^d.position • cliffordWord Q (s.replace d.remainder))).sum)=
    (1/2 : ℂ) • (cliffordWord Q s.before*
      (Q.γ s.letter*hamiltonian Q w-hamiltonian Q w*Q.γ s.letter)*cliffordWord Q s.after) := by
  rw [majorana_hamiltonian_word_derivative]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul]
  norm_num
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  rw [cliffordWordPartial_deletions,wordDeletions_filter_sum]
  rw [← List.sum_map_mul_left,← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  by_cases he : d.letter=s.letter
  · simp only [he,ite_true,WordSlot.replace,cliffordWord_append,mul_smul_comm,smul_mul_assoc]
  · simp only [he,ite_false,mul_zero,zero_mul]

namespace InteractionPath
variable (t : InteractionPath N)
def qeval (Q : Model N) (w : Disorder N) :=
  ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) • cliffordWord Q t.word

def reval (w : Disorder N) (x : Fin N → ℝ) :=
  couplingMonomial t.couplings w*realWord t.word x

lemma qeval_step (Q : Model N) (w : Disorder N) :
    (t.step.map (fun u ↦ u.qeval Q w)).sum=
      (1/2 : ℂ) • (t.qeval Q w*hamiltonian Q w-hamiltonian Q w*t.qeval Q w) := by
  unfold step
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,qeval,couplingMonomial_cons,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  have hterm (s : WordSlot N) (A : SYKEdge.KSet N 4) :
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ ((t.sign : ℂ)*(-1 : ℂ)^d.position*((w A : ℂ)*
          (couplingMonomial t.couplings w : ℂ))) • cliffordWord Q (s.replace d.remainder))).sum=
      ((t.sign*couplingMonomial t.couplings w : ℝ) : ℂ) • ((w A : ℂ) •
        ((((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
          (fun d ↦ (-1 : ℂ)^d.position • cliffordWord Q (s.replace d.remainder))).sum)) := by
    rw [← list_sum_smul_left,← list_sum_smul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    simp only [smul_smul,Complex.ofReal_mul]
    congr 1
    ring
  simp_rw [hterm]
  simp only [list_sum_smul_left]
  simp_rw [all_list_sum]
  rw [← list_sum_smul_left]
  simp_rw [word_slot_quantum_children]
  simp only [list_sum_smul_left]
  rw [← commutator_word_slots]
  simp only [qeval,Complex.ofReal_mul,smul_mul_assoc,mul_smul_comm,← smul_sub,smul_smul]
  congr 1
  ring
end InteractionPath

lemma quantum_paths_recur (Q : Model N) (w : Disorder N) (j : Fin N) (m : ℕ) :
    ((interactionPaths j (m+1)).map (fun t ↦ t.qeval Q w)).sum=
      (1/2 : ℂ) • ((((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum)*hamiltonian Q w-
        hamiltonian Q w*((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum) := by
  simp only [interactionPaths,list_sum_flatMap,InteractionPath.qeval_step,list_sum_smul_left]
  congr 1
  induction interactionPaths j m with
  | nil => simp
  | cons t l ih => simp only [List.map_cons,List.sum_cons,add_mul,mul_add] at *; rw [ih]; module

lemma quantum_ad_paths (Q : Model N) (w : Disorder N) (j : Fin N) (m : ℕ) :
    (-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j)=
      (2 : ℂ)^m • ((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum := by
  induction m with
  | zero =>
    simp only [pow_zero,one_smul,interactionPaths,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,InteractionPath.qeval,couplingMonomial_nil,mul_one,Complex.ofReal_one]
    have he : applySuper (1 : Super (SiteHilbert N)) (Q.γ j)=Q.γ j := by
      ext a b
      simp [applySuper,Matrix.one_apply]
    rw [he]
    simp [cliffordWord]
  | succ m ih =>
    rw [pow_succ' (ad (hamiltonian Q w)),applySuper_mul]
    have had (X : Mat (SiteHilbert N)) :
        applySuper (ad (hamiltonian Q w)) X=hamiltonian Q w*X-X*hamiltonian Q w :=
      applySuper_super (leftAct (hamiltonian Q w)-rightAct (hamiltonian Q w)).toLinearMap X
    rw [had,quantum_paths_recur]
    calc
      _=-(hamiltonian Q w*((-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j))-
          ((-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j))*hamiltonian Q w) := by
        rw [pow_succ]
        simp only [mul_neg_one,neg_smul,mul_smul_comm,smul_mul_assoc,smul_sub]
        module
      _=_ := by
        rw [ih,pow_succ]
        simp only [mul_smul_comm,smul_mul_assoc,smul_sub,smul_smul]
        have hc : (2 : ℂ)^m*2*(1/2)=(2 : ℂ)^m := by ring
        rw [hc]
        module

lemma gammaCoefficient_paths (Q : Model N) (w : Disorder N) (j : Fin N) (m : ℕ) :
    gammaCoefficient Q w m j=((2 : ℂ)^m/(m.factorial : ℂ)) •
      ((interactionPaths j m).map (fun t ↦ t.qeval Q w)).sum := by
  unfold gammaCoefficient
  calc
    _=(m.factorial : ℂ)⁻¹ • ((-1 : ℂ)^m • applySuper ((ad (hamiltonian Q w))^m) (Q.γ j)) := by
      rw [smul_smul]
      congr 1
      rw [div_eq_mul_inv,mul_comm]
    _=_ := by
      rw [quantum_ad_paths,smul_smul]
      congr 1
      rw [div_eq_mul_inv,mul_comm]

end SYKFastMix.FastMixing

end
end


-- Solutions.SparseGaussianBlocks
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι] [Nonempty ι]

lemma subblock_single_kronecker (i j a b : I) (W : Mat ι) :
    subblock (Matrix.kronecker (Matrix.single i j (1 : ℂ)) W) a b=
      if a=i ∧ b=j then W else 0 := by
  ext x y
  by_cases hai : a=i <;> by_cases hbj : b=j <;>
    simp [subblock,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.single_apply,hai,hbj,
      Ne.symm,eq_comm] <;> aesop

lemma blockDominated_single_kronecker (i j : I) (W : Mat ι) (c : ℝ) (hc : ‖W‖≤c) :
    BlockDominated (Matrix.kronecker (Matrix.single i j (1 : ℂ)) W) (Matrix.single i j c) := by
  intro a b
  rw [subblock_single_kronecker]
  by_cases he : a=i ∧ b=j
  · simp only [he,ite_true]
    simpa [Matrix.single_apply,he.1,he.2] using hc
  · by_cases hai : a=i <;> by_cases hbj : b=j <;> simp_all [Matrix.single_apply,eq_comm]

end SYKFastMix.FastMixing

end
end


-- Solutions.ClassicalPathExpansion
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma word_slot_classical_children (w : Disorder N) (s : WordSlot N) (x : Fin N → ℝ) :
    (∑ A : SYKEdge.KSet N 4, w A*
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ realWord (s.replace d.remainder) x)).sum)=
      coordinateDerivative (classicalG w) s.letter x*realWord (s.replace []) x := by
  rw [classicalG_derivative_words,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [realWordPartial_deletions,wordDeletions_filter_sum,mul_assoc]
  congr 1
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  by_cases he : d.letter=s.letter
  · simp only [he,ite_true,WordSlot.replace,realWord_append]
    simp [realWord]
    ring
  · simp only [he,ite_false,zero_mul]

namespace InteractionPath
variable (t : InteractionPath N)
lemma reval_step (w : Disorder N) (x : Fin N → ℝ) :
    2*(t.step.map (fun u ↦ u.reval w x)).sum=
      couplingMonomial t.couplings w*classicalGenerator w (realWord t.word) x := by
  unfold step
  simp only [list_sum_flatMap,List.map_map,Function.comp_def,reval,couplingMonomial_cons]
  have hterm (s : WordSlot N) (A : SYKEdge.KSet N 4) :
      (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
        (fun d ↦ (w A*couplingMonomial t.couplings w)*realWord (s.replace d.remainder) x)).sum=
      couplingMonomial t.couplings w*(w A*
        (((wordDeletions (A.1.sort (· ≤ ·))).filter (fun d ↦ d.letter=s.letter)).map
          (fun d ↦ realWord (s.replace d.remainder) x)).sum) := by
    rw [← List.sum_map_mul_left,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    ring
  simp_rw [hterm]
  simp only [List.sum_map_mul_left]
  simp_rw [all_list_sum,word_slot_classical_children]
  rw [realWord_generator_slots]
  ring
end InteractionPath

lemma classicalIterate_paths (w : Disorder N) (j : Fin N) (m : ℕ) (x : Fin N → ℝ) :
    classicalIterate w m j x=(2 : ℝ)^m*((interactionPaths j m).map (fun t ↦ t.reval w x)).sum := by
  induction m generalizing x with
  | zero => simp [classicalIterate,interactionPaths,InteractionPath.reval,couplingMonomial_nil,realWord]
  | succ m ih =>
    have he : classicalIterate w m j=fun y ↦ (2 : ℝ)^m*
        ((interactionPaths j m).map (fun t ↦ couplingMonomial t.couplings w*realWord t.word y)).sum := by
      funext y
      exact ih y
    have hrecur : classicalIterate w (m+1) j=classicalGenerator w (classicalIterate w m j) := by
      unfold classicalIterate
      rw [Function.iterate_succ_apply']
    rw [hrecur,he]
    have hscaled : (fun y ↦ (2 : ℝ)^m*
        ((interactionPaths j m).map (fun t ↦ couplingMonomial t.couplings w*realWord t.word y)).sum)=
        fun y ↦ ((interactionPaths j m).map (fun t ↦ ((2 : ℝ)^m*couplingMonomial t.couplings w)*realWord t.word y)).sum := by
      funext y
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      ring
    rw [hscaled,generator_list_words]
    simp only [interactionPaths,list_sum_flatMap,← InteractionPath.reval_step]
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    rw [mul_assoc,← InteractionPath.reval_step,pow_succ]
    ring

end SYKFastMix.FastMixing

end
end


-- Solutions.CoefficientPathPolynomials
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma coefficient_scale_nonneg (m : ℕ) : 0 ≤ (2 : ℝ)^m/(m.factorial : ℝ) := by positivity

lemma path_block_norm (Q : Model N) (m : ℕ) (t : InteractionPath N) (d : WordDeletion N) :
    ‖(((2 : ℝ)^m/(m.factorial : ℝ)*t.sign : ℝ) : ℂ) •
      ((-1 : ℂ)^d.position • cliffordWord Q d.remainder)‖=
      ((2 : ℝ)^m/(m.factorial : ℝ))*|t.sign| := by
  rw [norm_smul,norm_smul,cliffordWord_norm,Complex.norm_real,norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (coefficient_scale_nonneg m),norm_pow]
  norm_num

def fermionPathTerm (Q : Model N) (m : ℕ) (j : Fin N) (t : InteractionPath N)
    (d : WordDeletion N) : GaussianBlockTerm N (Fin N) (SiteHilbert N) :=
  ⟨t.couplings,
    Matrix.kronecker (Matrix.single j d.letter (1 : ℂ))
      ((((2 : ℝ)^m/(m.factorial : ℝ)*t.sign : ℝ) : ℂ) •
        ((-1 : ℂ)^d.position • cliffordWord Q d.remainder)),
    Matrix.single j d.letter (((2 : ℝ)^m/(m.factorial : ℝ))*|t.sign|),
    by
      letI : Nonempty (SiteHilbert N) := ⟨⟨0,by positivity⟩⟩
      exact blockDominated_single_kronecker _ _ _ _ (le_of_eq (path_block_norm Q m t d))⟩

def fermionPathPolynomial (Q : Model N) (m : ℕ) :
    GaussianBlockPolynomial.Poly N (Fin N) (SiteHilbert N) :=
  (Finset.univ.toList : List (Fin N)).flatMap (fun j ↦
    (interactionPaths j m).flatMap (fun t ↦ (wordDeletions t.word).map (fermionPathTerm Q m j t)))

lemma realWord_ones (l : List (Fin N)) : realWord l (fun _ ↦ 1)=1 := by simp [realWord]

lemma classicalCoefficient_paths (w : Disorder N) (m : ℕ) (j i : Fin N) :
    (classicalCoefficient w m 1) j i=
      (((2 : ℝ)^m/(m.factorial : ℝ))*
        ((interactionPaths j m).map (fun t ↦ couplingMonomial t.couplings w*
          ((wordDeletions t.word).map (fun d ↦ if d.letter=i then (1 : ℝ) else 0)).sum)).sum : ℝ) := by
  have he : classicalIterate w m j=fun y ↦
      ((interactionPaths j m).map (fun t ↦ ((2 : ℝ)^m*couplingMonomial t.couplings w)*realWord t.word y)).sum := by
    funext y
    rw [classicalIterate_paths,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    simp only [InteractionPath.reval]
    ring
  unfold classicalCoefficient
  rw [he,derivative_list_words]
  simp only [realWordPartial_deletions]
  have hone (l : List (Fin N)) : realWord l (1 : Fin N → ℝ)=1 := by
    change (l.map (fun _ ↦ (1 : ℝ))).prod=1
    simp
  simp_rw [hone]
  have hs : ((interactionPaths j m).map (fun a ↦ (2 : ℝ)^m*couplingMonomial a.couplings w*
        ((wordDeletions a.word).map (fun d ↦ if d.letter=i then (1 : ℝ) else 0)).sum)).sum=
      (2 : ℝ)^m*((interactionPaths j m).map (fun a ↦ couplingMonomial a.couplings w*
        ((wordDeletions a.word).map (fun d ↦ if d.letter=i then (1 : ℝ) else 0)).sum)).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    ring
  rw [hs]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]
  ring

end SYKFastMix.FastMixing

end
end


-- Solutions.ClassicalCoefficientMeasurable
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma classicalCoefficient_norm_measurable (m : ℕ) :
    Measurable (fun w : Disorder N ↦ ‖classicalCoefficient w m (fun _ ↦ 1)‖) := by
  apply Continuous.measurable
  apply Continuous.norm
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  change Continuous (fun w : Disorder N ↦ (classicalCoefficient w m 1) j i)
  simp_rw [classicalCoefficient_paths]
  unfold couplingMonomial
  fun_prop

end SYKFastMix.FastMixing

end
end


-- Solutions.Lemma10
section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing
variable {N : ℕ}

lemma lemma10_bound (Q : Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m*p ≤ 7*N) :
    Integrable (fun w ↦ ‖classicalCoefficient w m (fun _ ↦ 1)‖^(2*p)) (disorderLaw Q) ∧
    (∫ w,‖classicalCoefficient w m (fun _ ↦ 1)‖^(2*p) ∂disorderLaw Q)^(1/(2*(p : ℝ)))≤(105*Q.J)^m := by
  have hT := disorder_tensornorm_moments Q (m*p) (by nlinarith)
  have hB := disorder_tensornorm_scaled_moment Q (m*p) (by nlinarith) hmp
  have he : m*(2*p)=2*(m*p) := by ring
  rw [←he] at hT hB
  have h := polynomial_moment_majorant (disorderLaw Q)
    (fun w ↦ ‖classicalCoefficient w m (fun _ ↦ 1)‖) (fun w ↦ ‖disorderQuarticForm w‖)
    (classicalCoefficient_norm_measurable m).aestronglyMeasurable
    disorder_tensornorm_measurable.aestronglyMeasurable
    (fun w ↦ norm_nonneg _) (fun w ↦ norm_nonneg _) (24*(N : ℝ)) (105*Q.J) (by positivity)
    m (2*p) (by omega) (by omega) (by norm_cast; omega) hT.1
    (fun w ↦ classicalCoefficient_tensor_norm_bound w m) hB
  refine ⟨h.1,?_⟩
  rw [lpNorm_nat_eq_integral_pow_nonneg (disorderLaw Q)
    (fun w ↦ ‖classicalCoefficient w m (fun _ ↦ 1)‖)
    (classicalCoefficient_norm_measurable m).aestronglyMeasurable (fun w ↦ norm_nonneg _) _ (by omega)] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat,one_div] using h.2

end SYKFastMix.FastMixing

end
end

open SYKFastMix.FastMixing
open MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem solution {N : ℕ} (Q : Model N) (m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m * p ≤ 7 * N) :
  Integrable (fun w => SYKEdge.opNorm (classicalCoefficient w m (fun _ => 1))^(2*p)) (disorderLaw Q) ∧
  Real.rpow (∫ w, SYKEdge.opNorm (classicalCoefficient w m (fun _ => 1))^(2*p) ∂disorderLaw Q)
    (1 / (2 * (p : ℝ))) ≤ (105 * Q.J)^m := by
  exact lemma10_bound Q m p hm hp hmp
