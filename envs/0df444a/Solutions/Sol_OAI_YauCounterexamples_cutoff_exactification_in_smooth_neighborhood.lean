-- Prove2me | solution 1 for OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:27:33.558294+00:00
-- url     : https://prove2.me/submissions/f086e2d7-d06a-4f2c-a3e8-0d719e635ebc

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A006
import Definitions.Def_OAIQ070A007

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_RealMatrixCauchy
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rank_one_mulVec_inverse_direction {A : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (p : ι → ℝ) (a b : ℝ) :
    (a • A + b • Matrix.vecMulVec p p) *ᵥ (A⁻¹ *ᵥ p) =
      (a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p))) • p := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

lemma det_add_vecMulVec {A : Matrix ι ι ℝ} (hA : IsUnit A.det) (u v : ι → ℝ) :
    (A + Matrix.vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have he : Matrix.vecMulVec u v = Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec]
  rw [he, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma det_rank_one_three {A : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (hn : Fintype.card ι = 3) (p : ι → ℝ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    (a • A + b • Matrix.vecMulVec p p).det =
      a ^ 2 * (a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p))) * A.det := by
  have he : a • A + b • Matrix.vecMulVec p p =
      a • (A + Matrix.vecMulVec ((b / a) • p) p) := by
    rw [smul_add, Matrix.smul_vecMulVec, smul_smul]
    congr 1
    congr 1
    field_simp
  rw [he, Matrix.det_smul, hn, det_add_vecMulVec hA,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  field_simp

lemma rank_one_inverse_direction {A : Matrix ι ι ℝ} (hA : IsUnit A.det)
    (p : ι → ℝ) (a b : ℝ)
    (hB : IsUnit (a • A + b • Matrix.vecMulVec p p).det)
    (hc : a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p)) ≠ 0) :
    (a • A + b • Matrix.vecMulVec p p)⁻¹ *ᵥ p =
      (a + b * (p ⬝ᵥ (A⁻¹ *ᵥ p)))⁻¹ • (A⁻¹ *ᵥ p) := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB))
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec,
    Matrix.mulVec_smul, rank_one_mulVec_inverse_direction hA, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ReciprocalIteratedDerivativeBound
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma reciprocal_iterated_derivative_bound (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => 1/y) (Ioi 0) t‖ ≤ (j.factorial : ℝ) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_one_div j isOpen_Ioi ht0]
  have he : (-1-(j:ℤ)) = -((j+1 : ℕ):ℤ) := by omega
  dsimp only
  rw [he,zpow_neg,zpow_natCast]
  simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_neg,abs_one,one_pow,
    Nat.abs_cast,one_mul,norm_inv]
  have hp : 1 ≤ t^(j+1) := one_le_pow₀ ht
  have hi : |(t^(j+1))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _))]
    exact inv_le_one_of_one_le₀ hp
  simpa only [mul_one,abs_inv,abs_pow] using mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg j.factorial)

theorem normalized_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (hx : 1 ≤ f x)
    (h : ℕ) (D : ℝ)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤ (h.factorial : ℝ)^2*D^h := by
  let S := {y | 0 < f y}
  have hS : IsOpen S := isOpen_lt continuous_const hf.continuous
  have hxS : x ∈ S := zero_lt_one.trans_le hx
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => 1/y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => hy.ne')
  have hb := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn (show (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) from le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    isOpen_Ioi.uniqueDiffOn hS.uniqueDiffOn (fun y (hy : y ∈ S) => hy) hxS
    (C:=(h.factorial:ℝ)) (D:=D) (fun j hj =>
      (reciprocal_iterated_derivative_bound j hx).trans (by exact_mod_cast Nat.factorial_le hj))
    (fun j hj hjh => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn (hf.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt hxS]
      exact hD j hj hjh)
  change ‖iteratedFDerivWithin ℝ h (fun y => 1/f y) S x‖ ≤ _ at hb
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt (zero_lt_one.trans_le hx).ne').of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn hrec hxS] at hb
  simpa only [Function.comp_apply,pow_two,mul_assoc] using hb

theorem weighted_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (h : ℕ)
    {δ W M R : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hR : 0 ≤ R) (hx : δ*W^2 ≤ f x)
    (hjet : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ M*R^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤
      (h.factorial : ℝ)^2 * (max 1 (M/δ)*R)^h / (δ*W^2) := by
  let c := δ*W^2
  have hc : 0 < c := mul_pos hδ (sq_pos_of_pos hW)
  let F : E → ℝ := fun y => c⁻¹*f y
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul hf
  have hxF : 1 ≤ F x := by
    dsimp only [F]
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hx)
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ h →
      ‖iteratedFDeriv ℝ j F x‖ ≤ (max 1 (M/δ)*R)^j := by
    intro j hj hjh
    have hej : iteratedFDeriv ℝ j F x = c⁻¹ • iteratedFDeriv ℝ j f x := by
      simpa only [F,smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a:=c⁻¹) (x:=x) (hf.of_le
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)
    rw [hej,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹*‖iteratedFDeriv ℝ j f x‖ ≤ c⁻¹*(M*R^j*W^2) :=
        mul_le_mul_of_nonneg_left (hjet j hj hjh) (inv_nonneg.mpr hc.le)
      _ = (M/δ)*R^j := by dsimp only [c]; field_simp
      _ ≤ (max 1 (M/δ))^j*R^j := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))) (pow_nonneg hR j)
      _ = (max 1 (M/δ)*R)^j := (mul_pow _ _ _).symm
  have hb := normalized_reciprocal_jet_bound hF hxF h (max 1 (M/δ)*R) hD
  have hfx : f x ≠ 0 := (hc.trans_le hx).ne'
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt hfx).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  have he : (fun y => 1/F y) = fun y => c • (1/f y) := by
    funext y
    simp only [F,one_div,smul_eq_mul,mul_inv_rev,inv_inv]
    ring
  rw [he,iteratedFDeriv_const_smul_apply' hrec,norm_smul,
    Real.norm_eq_abs,abs_of_pos hc] at hb
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

lemma geometric_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem weighted_quotient_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h : ℕ)
    {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  have hrec : ContDiff ℝ ∞ (fun y => 1/d y) := contDiff_const.div hd hdne
  have hinv : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => 1/d y) x‖ ≤
      ((h.factorial:ℝ)^2/(δ*W^2))*(max 1 (M/δ)*S)^j := by
    intro j hj
    have hb := weighted_reciprocal_jet_bound hd j hδ hW hS hx
      (fun i hi hij => hdj i hi (hij.trans hj))
    calc
      _ ≤ (j.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := hb
      _ ≤ (h.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := by
        gcongr
      _ = _ := by ring
  have hb := geometric_product_jet_bound hf hrec x h
    (F:=N*W^2) (G:=(h.factorial:ℝ)^2/(δ*W^2))
    (mul_nonneg hN (sq_nonneg _)) (by positivity) hR
    (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hS)
    (fun j hj => by simpa only [mul_assoc,mul_left_comm,mul_comm] using hfj j hj) hinv
  have he : (N*W^2)*((h.factorial:ℝ)^2/(δ*W^2)) = N*(h.factorial:ℝ)^2/δ := by
    field_simp
  simpa only [one_div,← div_eq_mul_inv,he] using hb

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivScalarDirection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem coordinateDivergence_mul (e : ι → E) (ρ f : E → ℝ) (X : ι → E → ℝ)
    (x : E) (hρ : DifferentiableAt ℝ ρ x) (hf : DifferentiableAt ℝ f x)
    (hX : ∀ i, DifferentiableAt ℝ (X i) x) (hρx : ρ x ≠ 0) :
    coordinateDivergence e ρ (fun i y => f y * X i y) x =
      f x * coordinateDivergence e ρ X x +
        ∑ i, fderiv ℝ f x (e i) * X i x := by
  have hprod (i : ι) : (fun y => ρ y * (f y * X i y)) =
      (fun y => f y * (ρ y * X i y)) := by funext y; ring
  unfold coordinateDivergence
  simp only [hprod, fderiv_fun_mul (d := fun y => ρ y * X _ y) hf (hρ.mul (hX _)),
    add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : ∑ i, ρ x * X i x * fderiv ℝ f x (e i) =
      ρ x * ∑ i, fderiv ℝ f x (e i) * X i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma norm_iteratedFDeriv_scalar_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) h.contDiffAt
    (show (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  simpa only [norm_iteratedFDeriv_fderiv] using hb

lemma norm_iteratedFDeriv_scalar_sum (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (h : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ h (fun y => ∑ i, f i y) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ h (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hf i).contDiffAt.of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))))]
  exact norm_sum_le _ _

lemma constant_product_jet_bound {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (h : ℕ)
    {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  intro j hj
  have hb := geometric_product_jet_bound hf hg x j (R:=1) (S:=1) hF hG
    zero_le_one zero_le_one
    (fun i hi => by simpa only [one_pow,mul_one] using hfj i (hi.trans hj))
    (fun i hi => by simpa only [one_pow,mul_one] using hgj i (hi.trans hj))
  calc
    _ ≤ F*G*(1+1)^j := hb
    _ ≤ F*G*(1+1)^h := by gcongr; norm_num
    _ = _ := by norm_num; ring

theorem coordinate_divergence_jet_bound (e : ι → E) (ρ : E → ℝ) (Z : ι → E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρne : ∀ y, ρ y ≠ 0)
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) (x : E) (h : ℕ)
    {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hZj : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (Z i) x‖ ≤ F) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖ ≤
      (2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  have hρZ (i : ι) : ContDiff ℝ ∞ (fun y => ρ y*Z i y) := hρ.mul (hZ i)
  have hp (i : ι) := constant_product_jet_bound hρ (hZ i) x (h+1) hC hF hρj (hZj i)
  have hdf (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => ρ z*Z i z) y (e i)) :=
    ((hρZ i).fderiv_right (by simp)).clm_apply contDiff_const
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, fderiv ℝ (fun z => ρ z*Z i z) y (e i)) :=
    ContDiff.sum (fun i _ => hdf i)
  have hs : ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => ∑ i, fderiv ℝ (fun z => ρ z*Z i z) y (e i)) x‖ ≤
        (∑ i, ‖e i‖)*(2^(h+1)*C*F) := by
    intro j hj
    calc
      _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (fun z => ρ z*Z i z) y (e i)) x‖ :=
        norm_iteratedFDeriv_scalar_sum _ hdf j x
      _ ≤ ∑ i, ‖e i‖*(2^(h+1)*C*F) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (norm_iteratedFDeriv_scalar_direction (hρZ i) (e i) j x).trans
          (mul_le_mul_of_nonneg_left (hp i (j+1) (by omega)) (norm_nonneg _))
      _ = _ := by rw [Finset.sum_mul]
  have hb := constant_product_jet_bound (hρ.inv hρne) hsum x h hC
    (show 0 ≤ (∑ i, ‖e i‖)*(2^(h+1)*C*F) by positivity) hρij hs
  intro j hj
  apply (hb j hj).trans_eq
  rw [show 2*h+1=h+(h+1) by omega,pow_add]
  ring



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SmoothExtension
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

lemma smooth_extension_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ F : E → F, ContDiff ℝ ∞ F ∧ f =ᶠ[𝓝 x] F := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hx) hf
  exact ⟨F,hF,he.filter_mono (nhds_le_nhdsSet (mem_singleton x))⟩

lemma positive_smooth_extension_at {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hfx : 0 < f x) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ (∀ y, 0 < F y) ∧ f =ᶠ[𝓝 x] F := by
  have hp : {y | 0 < f y} ∈ 𝓝 x :=
    (hf.continuousOn.continuousAt (hO.mem_nhds hx)).eventually (isOpen_Ioi.mem_nhds hfx)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hp
  obtain ⟨F,hF,he⟩ := smooth_extension_at (hO.inter hVo) ⟨hx,hxV⟩
    ((hf.mono inter_subset_left).log (fun y hy => (hV hy.2).ne'))
  refine ⟨fun y => Real.exp (F y), hF.exp,fun _ => Real.exp_pos _,?_⟩
  filter_upwards [he, hp] with y hy hpy
  rw [← hy,Real.exp_log hpy]

omit [FiniteDimensional ℝ E] in
lemma coordinateDivergence_eventuallyEq (e : ι → E) {ρ σ : E → ℝ}
    {X Y : ι → E → ℝ} {x : E} (hρ : ρ =ᶠ[𝓝 x] σ)
    (hX : ∀ i, X i =ᶠ[𝓝 x] Y i) :
    coordinateDivergence e ρ X =ᶠ[𝓝 x] coordinateDivergence e σ Y := by
  have hd (i : ι) := (hρ.mul (hX i)).fderiv (𝕜:=ℝ)
  filter_upwards [hρ,eventually_all.mpr hd] with y hy hdy
  simp only [coordinateDivergence,hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e i)) (hdy i)

theorem coordinate_divergence_jet_bound_on (e : ι → E) (ρ : E → ℝ) (Z : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) O)
    (h : ℕ) {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hZj : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (Z i) x‖ ≤ F) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖ ≤
      (2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  obtain ⟨σ,hσ,hσp,hσe⟩ := positive_smooth_extension_at hO hxO hρ (hρp x hxO)
  choose Y hY hYe using fun i => smooth_extension_at hO hxO (hZ i)
  have hq := coordinate_divergence_jet_bound e σ Y hσ (fun y => (hσp y).ne') hY x h hC hF
    (fun j hj => (hσe.iteratedFDeriv ℝ j).self_of_nhds ▸ hρj j hj)
    (fun j hj => (hσe.inv.iteratedFDeriv ℝ j).self_of_nhds ▸ hρij j hj)
    (fun i j hj => ((hYe i).iteratedFDeriv ℝ j).self_of_nhds ▸ hZj i j hj)
  intro j hj
  rw [(coordinateDivergence_eventuallyEq e hσe hYe).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
section ProductCalculus
variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕜]
lemma second_fderiv_mul_at {u v : E → 𝕜} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have hdv' : DifferentiableAt ℝ (fun y => fderiv ℝ v y b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =ᶠ[𝓝 x]
      (fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hy hz
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he.fderiv_eq]
  erw [fderiv_fun_add (hdu.mul hdv') (hdv.mul hdu'),
    fderiv_fun_mul hdu hdv', fderiv_fun_mul hdv hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
end ProductCalculus
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_mul {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y * v y) x =
      u x * laplaceBeltrami g v x + v x * laplaceBeltrami g u x +
        2 * coordinateGradientPair g u v x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hv' := contDiffAt_inChart_C2 hv x hx
  change localLaplacian g _ x (c x) = _
  have huv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (fun y => u y * v y) := hu.mul hv
  rw [localLaplacian_expansion_C2 huv g x hx]
  change _ = u x * localLaplacian g v x (c x) +
    v x * localLaplacian g u x (c x) + 2 * coordinateGradientPair g u v x
  rw [localLaplacian_expansion_C2 hu g x hx, localLaplacian_expansion_C2 hv g x hx]
  have hs (i j : CoordIndex E) : (metricCoefficients g x (c x))⁻¹ j i =
      (metricCoefficients g x (c x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x hx).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hcross : (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i)) =
      coordinateGradientPair g u v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) y (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) *
        fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) = _
  have hd1 (j : CoordIndex E) :
      fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) =
        u x * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
        v x * fderiv ℝ (u ∘ c.symm) (c x) (b j) := by
    erw [fderiv_fun_mul (hu'.differentiableAt (by norm_num))
      (hv'.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z)
        y (b j)) (c x) (b i) =
      u x * fderiv ℝ (fun y => fderiv ℝ (v ∘ c.symm) y (b j)) (c x) (b i) +
      v x * fderiv ℝ (fun y => fderiv ℝ (u ∘ c.symm) y (b j)) (c x) (b i) +
      fderiv ℝ (u ∘ c.symm) (c x) (b i) * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i) := by
    have he := second_fderiv_mul_at hu' hv' (b i) (b j)
    dsimp only [c] at hinv he ⊢
    simpa only [Function.comp_apply, hinv] using he
  simp_rw [hd2, hd1]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, hcross]
  unfold coordinateGradientPair
  dsimp only [c, b]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]
  ring

lemma weightedLaplacian_expansion {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b u x = b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
  let c := chartAt E x
  let a := metricCoefficients g x
  let ρ := fun y => Real.sqrt (Matrix.det (a y))
  let e := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hb' := contDiffAt_inChart_C2 hb x hx
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hρ := Real.sqrt_pos.mpr (metricCoefficients_det_pos g x hx)
  have hρd := ((contDiffOn_metricDensity g x).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hflux (i : CoordIndex E) : DifferentiableAt ℝ
      (fun y => ρ y * ∑ j, (a y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (e j)) (c x) := by
    apply hρd.mul
    apply DifferentiableAt.fun_sum
    intro j _
    apply (((contDiffOn_metricInverse g x i j).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)).mul
    exact ((hu'.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  change (ρ (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) = _
  have hd (i : CoordIndex E) : fderiv ℝ
      (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) =
      b x * fderiv ℝ (fun y => ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j)) (c x) (e i) +
      (ρ (c x) * ∑ j, (a (c x))⁻¹ i j * fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i) := by
    erw [fderiv_fun_mul (hb'.differentiableAt (by norm_num)) (hflux i)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  simp_rw [hd, Finset.sum_add_distrib]
  change (ρ (c x))⁻¹ * ((∑ i, b x * _) +
    ∑ i, (ρ (c x) * ∑ j, (a (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i)) = _
  unfold laplaceBeltrami coordinateGradientPair
  dsimp only
  simp only [Finset.mul_sum, mul_add, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ρ, a, c, e] at hρ ⊢
    field_simp [ne_of_gt hρ]


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiff_coordinateGradientPair {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coordinateGradientPair g u v) := by
  have he : coordinateGradientPair g u v = fun x => (2 : ℝ)⁻¹ *
      (laplaceBeltrami g (fun y => u y * v y) x -
        u x * laplaceBeltrami g v x - v x * laplaceBeltrami g u x) := by
    funext x
    rw [laplaceBeltrami_mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    ring
  rw [he]
  exact contMDiff_const.mul (((contMDiff_laplaceBeltrami (hu.mul hv) g).sub
    (hu.mul (contMDiff_laplaceBeltrami hv g))).sub (hv.mul (contMDiff_laplaceBeltrami hu g)))

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma differentialMetric_coefficients (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y =
      a ((chartAt E p).symm y) • metricCoefficients g p y +
      b ((chartAt E p).symm y) • Matrix.vecMulVec
        (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i))
        (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)) := by
  ext i j
  simp only [metricCoefficients, differentialMetric, rankOneMetric]
  change a ((chartAt E p).symm y) * g.inner _ (coordinateVector p y i) (coordinateVector p y j) +
      b ((chartAt E p).symm y) * inner ℝ
        (scalarDifferential u _ (coordinateVector p y i)) (scalarDifferential u _ (coordinateVector p y j)) =
    a ((chartAt E p).symm y) * g.inner _ (coordinateVector p y i) (coordinateVector p y j) +
      b ((chartAt E p).symm y) *
        (fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) *
          fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j))
  rw [scalarDifferential_coordinateVector hu p hy, scalarDifferential_coordinateVector hu p hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma localGradientPair_eq_global {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localGradientPair g u u p y = coordinateGradientPair g u u ((chartAt E p).symm y) := by
  rw [coordinateGradientPair_inChart hu hu g p ((chartAt E p).symm y) ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]

lemma differentialMetric_density_three (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b d : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (hd0 : ∀ x, 0 ≤ d x)
    (hdet : ∀ x, a x ^ 2 * (a x + b x * coordinateGradientPair g u u x) = d x ^ 2)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    Real.sqrt (Matrix.det (metricCoefficients
      (differentialMetric g u hu a b ha hb ha0 hab0) p y)) =
      d ((chartAt E p).symm y) * Real.sqrt (Matrix.det (metricCoefficients g p y)) := by
  rw [differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy,
    det_rank_one_three (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne')
      (by simpa only [CoordIndex, Fintype.card_fin] using hd) _ (ha0 _).ne']
  change Real.sqrt ((a _ ^ 2 * (a _ + b _ * localGradientPair g u u p y)) * _) = _
  rw [localGradientPair_eq_global hu g p hy, hdet, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (hd0 _)]

lemma differentialMetric_flux (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y)⁻¹ *ᵥ
      (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)) =
      (a ((chartAt E p).symm y) + b ((chartAt E p).symm y) *
        coordinateGradientPair g u u ((chartAt E p).symm y))⁻¹ •
      ((metricCoefficients g p y)⁻¹ *ᵥ
        (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i))) := by
  have hB := isUnit_iff_ne_zero.mpr
    (metricCoefficients_det_pos (differentialMetric g u hu a b ha hb ha0 hab0) p hy).ne'
  rw [differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy] at hB ⊢
  have he := localGradientPair_eq_global hu g p hy
  dsimp only [localGradientPair] at he
  rw [rank_one_inverse_direction
    (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne') _ _ _ hB
      (by rw [he]; exact (hab0 _).ne'), he]

theorem differentialMetric_laplacian_three (hn : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b d q : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (hd0 : ∀ x, 0 < d x)
    (hdet : ∀ x, a x ^ 2 * (a x + b x * coordinateGradientPair g u u x) = d x ^ 2)
    (hflux : ∀ x, d x / (a x + b x * coordinateGradientPair g u u x) = q x)
    (x : M) :
    laplaceBeltrami (differentialMetric g u hu a b ha hb ha0 hab0) u x =
      (d x)⁻¹ * weightedLaplacian g q u x := by
  let c := chartAt E x
  let ĝ := differentialMetric g u hu a b ha hb ha0 hab0
  have hx : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hy : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (Matrix.det (metricCoefficients ĝ x y)) *
        ∑ j, (metricCoefficients ĝ x y)⁻¹ i j *
          fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j)) =ᶠ[𝓝 (c x)]
      (fun y => q (c.symm y) * (Real.sqrt (Matrix.det (metricCoefficients g x y)) *
        ∑ j, (metricCoefficients g x y)⁻¹ i j *
          fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) := by
    filter_upwards [c.open_target.mem_nhds hy] with y hyt
    change Real.sqrt (Matrix.det (metricCoefficients ĝ x y)) *
      ((metricCoefficients ĝ x y)⁻¹ *ᵥ
        (fun j => fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) i = _
    rw [differentialMetric_density_three hn g u hu a b d ha hb ha0 hab0
        (fun z => (hd0 z).le) hdet x hyt,
      differentialMetric_flux g u hu a b ha hb ha0 hab0 x hyt]
    simp only [Pi.smul_apply, smul_eq_mul]
    change d (c.symm y) * _ * ((a _ + b _ * coordinateGradientPair g u u _)⁻¹ * _) = _
    rw [show d (c.symm y) * Real.sqrt (Matrix.det (metricCoefficients g x y)) *
        ((a (c.symm y) + b (c.symm y) * coordinateGradientPair g u u (c.symm y))⁻¹ *
          ((metricCoefficients g x y)⁻¹ *ᵥ
            (fun j => fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) i) =
        (d (c.symm y) / (a (c.symm y) + b (c.symm y) *
          coordinateGradientPair g u u (c.symm y))) *
          (Real.sqrt (Matrix.det (metricCoefficients g x y)) *
            ((metricCoefficients g x y)⁻¹ *ᵥ
              (fun j => fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) i) by
      rw [div_eq_mul_inv]; ring]
    rw [hflux]
    rfl
  unfold laplaceBeltrami weightedLaplacian
  dsimp only
  conv_lhs => arg 2; arg 2; ext i; rw [(he i).fderiv_eq]
  rw [differentialMetric_density_three hn g u hu a b d ha hb ha0 hab0
    (fun z => (hd0 z).le) hdet x hy]
  dsimp only [c] at hx
  rw [hx, _root_.mul_inv_rev]
  ring

lemma compatible_sqrt {q d : ℝ} (hq : 0 < q) (he : d = q ^ 3) :
    d / q = Real.sqrt (d * q) := by
  rw [he, show q ^ 3 * q = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg q)]
  field_simp

theorem determinant_correction_coefficients (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (d q : M → ℝ)
    (hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ d)
    (hq : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q)
    (hd0 : ∀ x, 0 < d x) (hq0 : ∀ x, 0 < q x)
    (hsupp : tsupport (fun x => d x - q x ^ 3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0}) :
    ∃ a b : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x, 0 < a x) ∧ (∀ x, 0 < a x + b x * coordinateGradientPair g u u x) ∧
      (∀ x, a x ^ 2 * (a x + b x * coordinateGradientPair g u u x) = d x ^ 2) ∧
      (∀ x, d x / (a x + b x * coordinateGradientPair g u u x) = q x) ∧
      (∀ x, d x = 1 → q x = 1 → a x = 1 ∧ b x = 0) := by
  let F := coordinateGradientPair g u u
  let a := fun x => Real.sqrt (d x * q x)
  let b := fun x => (d x / q x - a x) / F x
  have hF := contMDiff_coordinateGradientPair hu hu g
  have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a := by
    intro x
    exact (Real.contDiffAt_sqrt (mul_pos (hd0 x) (hq0 x)).ne').contMDiffAt.comp x
      ((hd x).mul (hq x))
  have ha0 : ∀ x, 0 < a x := fun x => Real.sqrt_pos.mpr (mul_pos (hd0 x) (hq0 x))
  have hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b := by
    intro x
    by_cases hx : F x = 0
    · have hn : x ∉ tsupport (fun x => d x - q x ^ 3) := by
        intro h
        exact hsupp h hx
      have he := notMem_tsupport_iff_eventuallyEq.mp hn
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      have hc := compatible_sqrt (hq0 y) (sub_eq_zero.mp hy)
      simp only [b, a, hc, sub_self, zero_div]
    · exact (((hd x).div₀ (hq x) (hq0 x).ne').sub (ha x)).div₀ (hF x) hx
  have hc : ∀ x, a x + b x * F x = d x / q x := by
    intro x
    by_cases hx : F x = 0
    · have hn : x ∉ tsupport (fun x => d x - q x ^ 3) := fun h => hsupp h hx
      have he := image_eq_zero_of_notMem_tsupport hn
      have hcompat := compatible_sqrt (hq0 x) (sub_eq_zero.mp he)
      dsimp only [b, a]
      rw [hx, mul_zero, add_zero]
      exact hcompat.symm
    · dsimp only [b]
      rw [div_mul_cancel₀ _ hx]
      ring
  refine ⟨a, b, ha, hb, ha0, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hc]
    exact div_pos (hd0 x) (hq0 x)
  · intro x
    rw [hc]
    dsimp only [a]
    rw [Real.sq_sqrt (mul_pos (hd0 x) (hq0 x)).le]
    field_simp [(hq0 x).ne', (hd0 x).ne']
  · intro x
    rw [hc]
    field_simp [(hq0 x).ne', (hd0 x).ne']
  · intro x hdx hqx
    simp [a, b, hdx, hqx]


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
section GradientPairCalculus
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_symm (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x = coordinateGradientPair g v u x := by
  have hs (i j : CoordIndex E) : (metricCoefficients g x ((chartAt E x) x))⁻¹ j i =
      (metricCoefficients g x ((chartAt E x) x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x ((chartAt E x).map_source (mem_chart_source E x))).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  unfold coordinateGradientPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]
  ring

end GradientPairCalculus

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiff_weightedLaplacian {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (weightedLaplacian g b u) := by
  have he : weightedLaplacian g b u = fun x =>
      b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
    funext x
    exact weightedLaplacian_expansion (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) g x
  rw [he]
  exact (hb.mul (contMDiff_laplaceBeltrami hu g)).add
    (contMDiff_coordinateGradientPair hb hu g)

lemma coordinateGradientPair_mul_left {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (v : M → ℝ) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y * u y) v x =
      f x * coordinateGradientPair g u v x + u x * coordinateGradientPair g f v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have hf' := (contDiffAt_inChart hf x hx).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu x hx).differentiableAt (by simp)
  have he : ((fun y => f y * u y) ∘ c.symm) =
      fun y => (f ∘ c.symm) y * (u ∘ c.symm) y := rfl
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ ((fun y => f y * u y) ∘ c.symm) (c x) _ * _) = _
  rw [he]
  erw [fderiv_fun_mul hf' hu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Function.comp_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c]
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  ring

lemma intrinsic_conjugation_product {b v w : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g (fun y => b y * v y ^ 2) w x =
      v x * weightedLaplacian g b (fun y => v y * w y) x -
        (v x * w x) * weightedLaplacian g b v x := by
  have hb2 := hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv2 := hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hw2 := hw.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h₁ := weightedLaplacian_expansion (hb2.mul (hv2.pow 2)) hw2 g x
  have h₂ := weightedLaplacian_expansion hb2 (hv2.mul hw2) g x
  have h₃ := weightedLaplacian_expansion hb2 hv2 g x
  have h₄ := laplaceBeltrami_mul hv2 hw2 g x
  change laplaceBeltrami g (v * w) x = _ at h₄
  have h₅ := coordinateGradientPair_mul_left hb (hv.pow 2) w g x
  change coordinateGradientPair g (b * fun y => v y ^ 2) w x = _ at h₅
  have h₆ := coordinateGradientPair_mul_left hv hv w g x
  change coordinateGradientPair g (v * v) w x = _ at h₆
  have he : (fun y => v y ^ 2) = v * v := by funext y; simp only [Pi.mul_apply]; ring
  have h₇ := coordinateGradientPair_mul_left hv hw b g x
  change coordinateGradientPair g (v * w) b x = _ at h₇
  have h₈ := coordinateGradientPair_symm g b (v * w) x
  have h₉ := coordinateGradientPair_symm g w b x
  have h₁₀ := coordinateGradientPair_symm g v b x
  change weightedLaplacian g (b * fun y => v y ^ 2) w x =
    v x * weightedLaplacian g b (v * w) x -
      (v x * w x) * weightedLaplacian g b v x
  rw [h₁, h₂, h₃, h₄, h₅, h₈, h₇, h₉, h₁₀]
  rw [he]
  rw [h₆]
  simp only [Pi.mul_apply]
  ring

theorem intrinsic_conjugated_equation {b s U v : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M)
    {Λ : ℝ} (hΛ : Λ ≠ 0) (hv0 : ∀ x, v x ≠ 0)
    (hweighted : ∀ x, weightedLaplacian g b U x + Λ * s x * U x = 0) :
    ∀ x, weightedLaplacian g (fun y => b y * v y ^ 2) (fun y => U y / v y) x +
      Λ * (s x * v x ^ 2 + Λ⁻¹ * v x * weightedLaplacian g b v x) * (U x / v x) = 0 := by
  intro x
  have hw := hU.div₀ hv hv0
  have he : (fun y => v y * (U y / v y)) = U := by
    funext y
    field_simp [hv0 y]
  erw [intrinsic_conjugation_product hb hv hw, he]
  simp only [Pi.div_apply]
  calc
    _ = v x * (weightedLaplacian g b U x + Λ * s x * U x) := by
      field_simp [hv0 x, hΛ]
      ring
    _ = 0 := by rw [hweighted x, mul_zero]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma chartGradientField_smooth {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    (i : CoordIndex E) :
    ContDiffOn ℝ ∞ (chartGradientField g u p i) (chartAt E p).target := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  unfold chartGradientField coordinateFlux
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).mul
    (((contDiffAt_inChart hu p hy).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

lemma weightedLaplacian_chartGradient {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    weightedLaplacian g f u ((chartAt E p).symm y) =
      coordinateDivergence (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det)
        (fun i z => f ((chartAt E p).symm z)*chartGradientField g u p i z) y := by
  have hρ := (contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)
  have hρp := Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)
  rw [coordinateDivergence_mul (Module.finBasis ℝ E)
    (fun z => Real.sqrt (metricCoefficients g p z).det)
    (fun z => f ((chartAt E p).symm z)) (chartGradientField g u p) y
    (hρ.differentiableAt (by simp)) ((contDiffAt_inChart hf p hy).differentiableAt (by simp))
    (fun i => ((chartGradientField_smooth hu g p i).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)) hρp.ne']
  rw [weightedLaplacian_expansion
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    coordinateGradientPair_inChart hf hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  rfl

lemma compact_derivative_bound_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact hK hO hKO hf
  obtain ⟨C,hC,hFC⟩ := compact_derivative_bound hK hF N
  refine ⟨C,hC,fun j hj x hx => ?_⟩
  have hex := he.filter_mono (nhds_le_nhdsSet hx)
  rw [(hex.iteratedFDeriv ℝ j).self_of_nhds]
  exact hFC j hj x hx

lemma geometric_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hx hg
  have hb := geometric_product_jet_bound hf' hg' x h hF hG hR hS
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  change ‖iteratedFDeriv ℝ h (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hb

lemma norm_iteratedFDeriv_scalar_direction_on {O : Set E} (hO : IsOpen O)
    {x : E} (hx : x ∈ O) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (v : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) f x‖ := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hx hf
  have hd : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y v) :=
    (he.fderiv (𝕜:=ℝ)).mono (fun y hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy)
  rw [(hd.iteratedFDeriv ℝ k).self_of_nhds, (he.iteratedFDeriv ℝ (k+1)).self_of_nhds]
  exact norm_iteratedFDeriv_scalar_direction hF v k x

lemma chartGradientField_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^(k+4)*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^(k+5)*W := by
  let U := u ∘ (chartAt E p).symm
  have hU : ContDiffOn ℝ ∞ U (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hdi (j : CoordIndex E) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  intro i k hk
  have hprod (j : CoordIndex E) :
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j *
        fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
      (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by
    have hder (l : ℕ) (hl : l ≤ k) :
        ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
          ‖Module.finBasis ℝ E j‖*C*n^5*W*n^l := by
      calc
        _ ≤ ‖Module.finBasis ℝ E j‖*‖iteratedFDeriv ℝ (l+1) U y‖ :=
          norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
        _ ≤ ‖Module.finBasis ℝ E j‖*(C*n^((l+1)+4)*W) :=
          mul_le_mul_of_nonneg_left (huj (l+1) (by omega)) (norm_nonneg _)
        _ = _ := by rw [show l+1+4=5+l by omega,pow_add]; ring
    apply (geometric_product_jet_bound_on (chartAt E p).open_target hy
      (contDiffOn_metricInverse g p i j) (hdi j) k hA
      (show 0 ≤ ‖Module.finBasis ℝ E j‖*C*n^5*W by positivity) hn0 hn0
      (fun l hl => (haj i j l (hl.trans hk)).trans (by
        exact le_mul_of_one_le_right hA (one_le_pow₀ hn))) hder).trans
    rw [show n+n=2*n by ring,mul_pow]
    calc
      A*(‖Module.finBasis ℝ E j‖*C*n^5*W)*(2^k*n^k) =
          (2^k*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by rw [pow_add]; ring
      _ ≤ _ := by gcongr; norm_num
  unfold chartGradientField coordinateFlux
  rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
    (((contDiffOn_metricInverse g p i j).mul (hdi j)).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W :=
      Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_mul]

lemma compact_metric_scalar_coefficient_bounds (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      (∀ i j, ∀ k ≤ h+1, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A) ∧
      (∀ k ≤ h+1, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => Real.sqrt (metricCoefficients g p z).det) y‖ ≤ A) ∧
      (∀ k ≤ h, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => (Real.sqrt (metricCoefficients g p z).det)⁻¹) y‖ ≤ A) := by
  classical
  choose a ha haj using fun i j => compact_derivative_bound_on hK
    (chartAt E p).open_target hKt (contDiffOn_metricInverse g p i j) (h+1)
  obtain ⟨b,hb,hbj⟩ := compact_derivative_bound_on hK (chartAt E p).open_target hKt
    (contDiffOn_metricDensity g p) (h+1)
  obtain ⟨c,hc,hcj⟩ := compact_derivative_bound_on hK (chartAt E p).open_target hKt
    ((contDiffOn_metricDensity g p).inv (fun z hz =>
      (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hz)).ne')) h
  let A := 1+b+c+∑ i, ∑ j, a i j
  have ha0 (i j : CoordIndex E) : 0 ≤ a i j := zero_le_one.trans (ha i j)
  have hs0 : 0 ≤ ∑ i, ∑ j, a i j := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => ha0 i j))
  refine ⟨A,by dsimp only [A]; linarith,?_,?_,?_⟩
  · intro i j k hk y hy
    apply (haj i j k hk y hy).trans
    have hai : a i j ≤ ∑ j, a i j :=
      Finset.single_le_sum (fun j _ => ha0 i j) (Finset.mem_univ j)
    have haj' : (∑ j, a i j) ≤ ∑ i, ∑ j, a i j :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => ha0 i j)) (Finset.mem_univ i)
    dsimp only [A]
    linarith
  · intro k hk y hy
    exact (hbj k hk y hy).trans (by dsimp only [A]; linarith)
  · intro k hk y hy
    exact (hcj k hk y hy).trans (by dsimp only [A]; linarith)


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
section ProjectionJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma weighted_quotient_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f d : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hd : ContDiffOn ℝ ∞ d O)
    (h : ℕ) {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨d',hd',hdp,hde⟩ := positive_smooth_extension_at hO hxO hd
    ((by positivity : 0 < δ*W^2).trans_le hx)
  have hq := weighted_quotient_jet_bound hf' hd' (fun y => (hdp y).ne') x h hδ hW
    hN hR hS (hde.self_of_nhds ▸ hx)
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj hjh => (hde.iteratedFDeriv ℝ j).self_of_nhds ▸ hdj j hj hjh)
  change ‖iteratedFDeriv ℝ h (f/d) x‖ ≤ _
  rw [(hfe.div hde).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hq

end ProjectionJets

open scoped Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chartGradientField_sharp_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^k*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^k*(n*W) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hh := chartGradientField_jet_bound hu g p hy h hn
    (show 0 < W/n^4 by positivity) hC hA haj
    (fun k hk => (huj k hk).trans_eq (by rw [pow_add]; field_simp))
  intro i k hk
  apply (hh i k hk).trans_eq
  rw [show k+5=k+1+4 by omega,pow_add,pow_succ]
  field_simp

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chartGradientProjection_smooth_on (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M)
    {O : Set E} (_hO : IsOpen O) (hOT : O ⊆ (chartAt E p).target)
    (hF : ∀ y ∈ O, coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0)
    (i j : CoordIndex E) : ContDiffOn ℝ ∞ (chartGradientProjection g u p i j) O := by
  intro y hy
  have hα : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y :=
    ((contDiffAt_inChart hu p (hOT hy)).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const
  have hgp : ContDiffAt ℝ ∞ (localGradientPair g u u p) y := by
    apply (contDiffAt_inChart (contMDiff_coordinateGradientPair hu hu g) p (hOT hy)).congr_of_eventuallyEq
    filter_upwards [(chartAt E p).open_target.mem_nhds (hOT hy)] with z hz
    exact localGradientPair_eq_global hu g p hz
  have hgp0 : localGradientPair g u u p y ≠ 0 := by
    rw [localGradientPair_eq_global hu g p (hOT hy)]
    exact hF y hy
  exact ((((chartGradientField_smooth hu g p i).contDiffAt
    ((chartAt E p).open_target.mem_nhds (hOT hy))).mul hα).div hgp hgp0).contDiffWithinAt


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ConductivityMetricRealizationComplete
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma metric_mul_chartGradientProjection (g : SmoothMetric E M) (u : M → ℝ) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (i j : CoordIndex E) :
    ∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)*
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)/
      localGradientPair g u u p y := by
  let α := fun k => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E k)
  have he : (metricCoefficients g p y) *ᵥ
      ((metricCoefficients g p y)⁻¹ *ᵥ α) = α := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne'),Matrix.one_mulVec]
  have hei := congrFun he i
  simp only [Matrix.mulVec,dotProduct] at hei
  simp only [chartGradientProjection,chartGradientField,coordinateFlux]
  simp_rw [mul_div_assoc,←mul_assoc]
  dsimp [α] at hei
  rw [←Finset.sum_mul,hei]

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem conductivity_metric_realization_complete (hn : Module.finrank ℝ E=3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (d q : M → ℝ)
    (hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d)
    (hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q)
    (hd0 : ∀ x, 0 < d x) (hq0 : ∀ x, 0 < q x)
    (hsupp : tsupport (fun x => d x-q x^3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0}) :
    ∃ ĝ : SmoothMetric E M,
      (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
      (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) ∧
      (∀ x, d x=q x^3 → ∀ v w, ĝ.inner x v w=q x^2*g.inner x v w) ∧
      (∀ (p : M) (y : E), y ∈ (chartAt E p).target →
        coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0 →
        ∀ i j : CoordIndex E,
        metricCoefficients ĝ p y i j-metricCoefficients g p y i j =
          (Real.sqrt (d ((chartAt E p).symm y)*q ((chartAt E p).symm y))-1)*
            metricCoefficients g p y i j +
          (d ((chartAt E p).symm y)/q ((chartAt E p).symm y)-
            Real.sqrt (d ((chartAt E p).symm y)*q ((chartAt E p).symm y)))*
            ∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y) := by
  obtain ⟨a,b,ha,hb,ha0,hab0,hdet,hflux,hext⟩ :=
    determinant_correction_coefficients g u hu d q hd hq hd0 hq0 hsupp
  let ĝ := differentialMetric g u hu a b ha hb ha0 hab0
  have hdiag (x : M) : a x+b x*coordinateGradientPair g u u x=d x/q x := by
    have hh := (div_eq_iff (hab0 x).ne').mp (hflux x)
    apply (eq_div_iff (hq0 x).ne').mpr
    linarith
  have hsqrt (x : M) : a x=Real.sqrt (d x*q x) := by
    have hh := hdet x
    rw [hdiag x] at hh
    have hqz := (hq0 x).ne'
    have he : a x^2=d x*q x := by
      have hh' := congrArg (fun r : ℝ => r*q x) hh
      field_simp [hqz] at hh'
      apply (mul_right_cancel₀ (hd0 x).ne')
      nlinarith [hh']
    rw [←he,Real.sqrt_sq (ha0 x).le]
  refine ⟨ĝ,differentialMetric_laplacian_three hn g u hu a b d q ha hb ha0 hab0 hd0 hdet hflux,?_,?_,?_⟩
  · intro x hdx hqx v w
    obtain ⟨hax,hbx⟩ := hext x hdx hqx
    change a x*g.inner x v w+b x*inner ℝ (scalarDifferential u x v) (scalarDifferential u x w)=_
    rw [hax,hbx]; simp
  · intro x heq v w
    have haq : a x=q x^2 := by
      rw [hsqrt x,heq,show q x^3*q x=(q x^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
    have hz : b x*coordinateGradientPair g u u x=0 := by
      have hh := hdiag x
      rw [haq,heq] at hh
      have hdiv : q x^3/q x=q x^2 := by field_simp
      rw [hdiv] at hh
      linarith
    change a x*g.inner x v w+b x*inner ℝ (scalarDifferential u x v) (scalarDifferential u x w)=_
    rw [haq]
    rcases mul_eq_zero.mp hz with hbz | hFz
    · rw [hbz]; simp
    · have hv : scalarDifferential u x v=0 := by
        have hj := scalarDifferential_dual_bound hu g x v
        rw [hFz,zero_mul] at hj
        nlinarith [sq_nonneg (scalarDifferential u x v)]
      rw [hv]; simp
  · intro p y hy hF i j
    have hc := differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy
    have hbF : b ((chartAt E p).symm y) =
        (d ((chartAt E p).symm y)/q ((chartAt E p).symm y)-a ((chartAt E p).symm y))/
          coordinateGradientPair g u u ((chartAt E p).symm y) := by
      apply (eq_div_iff hF).mpr
      linarith [hdiag ((chartAt E p).symm y)]
    change metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y i j-_=_
    rw [hc,metric_mul_chartGradientProjection g u p hy i j,
      localGradientPair_eq_global hu g p hy]
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
    rw [hbF,hsqrt]
    ring


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ScalarCauchyCross
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma weightedLaplacian_congr_nhds (g : SmoothMetric E M) {b c u v : M → ℝ} {x : M}
    (hb : b =ᶠ[𝓝 x] c) (hu : u =ᶠ[𝓝 x] v) :
    weightedLaplacian g b u x = weightedLaplacian g c v x := by
  let chart := chartAt E x
  have hx := chart.map_source (mem_chart_source E x)
  have ht : Tendsto chart.symm (𝓝 (chart x)) (𝓝 x) := by
    simpa only [chart.left_inv (mem_chart_source E x)] using
      (chart.continuousAt_symm hx).tendsto
  have hb' := hb.comp_tendsto ht
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => b (chart.symm y) *
        (Real.sqrt (metricCoefficients g x y).det * ∑ j,
          (metricCoefficients g x y)⁻¹ i j *
          fderiv ℝ (u ∘ chart.symm) y (Module.finBasis ℝ E j))) =ᶠ[𝓝 (chart x)]
      (fun y => c (chart.symm y) *
        (Real.sqrt (metricCoefficients g x y).det * ∑ j,
          (metricCoefficients g x y)⁻¹ i j *
          fderiv ℝ (v ∘ chart.symm) y (Module.finBasis ℝ E j))) := by
    filter_upwards [hb',hu'] with y hby huy
    simp only [Function.comp_apply] at hby
    rw [hby,huy]
  unfold weightedLaplacian
  change (Real.sqrt (metricCoefficients g x (chart x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq

lemma weightedLaplacian_const (g : SmoothMetric E M) (b : M → ℝ) (c : ℝ) (x : M) :
    weightedLaplacian g b (fun _ => c) x = 0 := by
  simp [weightedLaplacian,Function.comp_def]

lemma coordinateGradientPair_cauchy (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x ^ 2 ≤
      coordinateGradientPair g u u x * coordinateGradientPair g v v x := by
  let c := chartAt E x
  let a := (metricCoefficients g x (c x))⁻¹
  let du := fun i => fderiv ℝ (u ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  let dv := fun i => fderiv ℝ (v ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  have hp := (metricCoefficients_posDef g x (c.map_source (mem_chart_source E x))).inv
  have he (f h : M → ℝ) : coordinateGradientPair g f h x =
      (fun i => fderiv ℝ (f ∘ c.symm) (c x) (Module.finBasis ℝ E i)) ⬝ᵥ
        (a *ᵥ (fun i => fderiv ℝ (h ∘ c.symm) (c x) (Module.finBasis ℝ E i))) := by
    simp only [coordinateGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum,a,c]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he u v,he u u,he v v]
  exact real_matrix_cauchy hp.posSemidef du dv

lemma conjugate_gradient_nonzero {U v : M → ℝ}
    (hU : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (g : SmoothMetric E M)
    (hv0 : ∀ x, v x ≠ 0) (x : M)
    (hmargin : U x^2*coordinateGradientPair g v v x <
      v x^2*coordinateGradientPair g U U x) :
    coordinateGradientPair g (fun y => U y/v y) (fun y => U y/v y) x ≠ 0 := by
  let u := fun y => U y/v y
  have hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u := hU.div₀ hv hv0
  have he : U = fun y => v y*u y := by funext y; dsimp [u]; field_simp [hv0 y]
  intro hz
  have hc := coordinateGradientPair_cauchy g v u x
  rw [hz,mul_zero] at hc
  have hcross : coordinateGradientPair g v u x=0 := by nlinarith [sq_nonneg (coordinateGradientPair g v u x)]
  have hcross' : coordinateGradientPair g u v x=0 := by rw [coordinateGradientPair_symm,hcross]
  have h₁ := coordinateGradientPair_mul_left hv hu U g x
  have h₂ := coordinateGradientPair_mul_left hv hu u g x
  have h₃ := coordinateGradientPair_mul_left hv hu v g x
  have hpair : coordinateGradientPair g U U x=u x^2*coordinateGradientPair g v v x := by
    rw [←he] at h₁ h₂ h₃
    rw [h₁,coordinateGradientPair_symm g u U x,h₂,
      coordinateGradientPair_symm g v U x,h₃,hz,hcross,hcross']
    ring
  rw [hpair] at hmargin
  have hUx : U x=v x*u x := congrFun he x
  rw [hUx] at hmargin
  nlinarith

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricAllJets
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma scalar_composition_jet_bound_on {O : Set E} {U : Set ℝ}
    (hO : IsOpen O) (hU : IsOpen U) {x : E} (hx : x ∈ O)
    {f : E → ℝ} {g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f O)
    (hg : ContDiffOn ℝ ∞ g U) (hfx : f x ∈ U) (h : ℕ) {C D : ℝ}
    (hgJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hfJ : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ h (g ∘ f) x‖ ≤ (h.factorial:ℝ)*C*D^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hU hfx hg
  have hfxe := hfe.self_of_nhds
  have he : g ∘ f =ᶠ[𝓝 x] g' ∘ f' := by
    have hc := hge.comp_tendsto (hf.continuousOn.continuousAt (hO.mem_nhds hx))
    filter_upwards [hc,hfe] with y hy hy'
    change g (f y)=g' (f' y)
    change g (f y)=g' (f y) at hy
    rw [hy,hy']
  rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
  apply norm_iteratedFDeriv_comp_le hg' hf'
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  · intro j hj
    rw [←hfxe,←(hge.iteratedFDeriv ℝ j).self_of_nhds]
    exact hgJ j hj
  · intro j hj hjh
    rw [←(hfe.iteratedFDeriv ℝ j).self_of_nhds]
    exact hfJ j hj hjh

theorem sqrt_near_one_jet_bound (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (O : Set E), IsOpen O → ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f O → (∀ y ∈ O, 0 < f y) →
      ∀ (x : E), x ∈ O → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y-1) x‖ ≤ ε) →
      (1/4 ≤ f x ∧ f x ≤ 9/4) →
      ‖iteratedFDeriv ℝ h (fun y => Real.sqrt (f y)-1) x‖ ≤ C*ε := by
  let H : ℝ → ℝ := fun z => 1/(Real.sqrt z+1)
  have hH : ContDiffOn ℝ ∞ H (Ioi 0) := by
    intro z hz
    exact (contDiffAt_const.div
      ((Real.contDiffAt_sqrt (ne_of_gt hz)).add contDiffAt_const)
      (ne_of_gt (by have := Real.sqrt_nonneg z; linarith))).contDiffWithinAt
  obtain ⟨B,hB,hBJ⟩ := compact_raw_jet_bound isOpen_Ioi
    (isCompact_Icc : IsCompact (Icc (1/4:ℝ) (9/4)))
    (show Icc (1/4:ℝ) (9/4) ⊆ Ioi 0 by intro z hz; change 0 < z; have := hz.1; linarith)
    hH h
  let A := (h.factorial:ℝ)*B*2^h
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A*2^h,by positivity,?_⟩
  intro O hO f hf hfp x hx ε hε hε1 hfJ hfx
  have hfJ' (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ (2:ℝ)^j := by
    have hfj := hfJ j hjh
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    change ‖iteratedFDeriv ℝ j (f - fun _ => (1:ℝ)) x‖ ≤ ε at hfj
    rw [iteratedFDeriv_sub_apply ((hf.contDiffAt (hO.mem_nhds hx)).of_le hle)
      contDiffAt_const,iteratedFDeriv_const_of_ne (by omega) (1:ℝ),Pi.zero_apply,sub_zero] at hfj
    exact hfj.trans (hε1.trans (one_le_pow₀ (by norm_num)))
  have hHJ (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j (fun y => H (f y)) x‖ ≤ A := by
    have hh := scalar_composition_jet_bound_on hO isOpen_Ioi hx hf hH (hfp x hx) j
      (fun k hk => hBJ k (hk.trans hj) (f x) hfx)
      (fun k hk hkj => hfJ' k hk (hkj.trans hj))
    calc
      _ ≤ (j.factorial:ℝ)*B*2^j := hh
      _ ≤ A := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hB)
          exact_mod_cast Nat.factorial_le hj
        · exact pow_le_pow_right₀ (by norm_num) hj
        · positivity
        · positivity
  have hHf : ContDiffOn ℝ ∞ (fun y => H (f y)) O :=
    hH.comp hf hfp
  have hh := geometric_product_jet_bound_on hO hx (hf.sub contDiffOn_const) hHf h
    hε hA.le (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
    (fun j hj => by simpa using hfJ j hj) (fun j hj => by simpa using hHJ j hj)
  have he : (fun y => Real.sqrt (f y)-1) =ᶠ[𝓝 x]
      (fun y => (f y-1)*H (f y)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    dsimp [H]
    have hs := Real.sq_sqrt (hfp y hy).le
    have hd : Real.sqrt (f y)+1 ≠ 0 := ne_of_gt (by have := Real.sqrt_nonneg (f y); linarith)
    field_simp
    nlinarith
  rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma near_one_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {d q : E → ℝ} (hd : ContDiffOn ℝ ∞ d O) (hq : ContDiffOn ℝ ∞ q O)
    (h : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d y-1) x‖ ≤ ε)
    (hqJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q y-1) x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ h (fun y => d y*q y-1) x‖ ≤ (2^h+2)*ε := by
  have hle : (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))
  have hd' := (hd.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)
  have hq' := (hq.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)
  have hp := geometric_product_jet_bound_on hO hx (hd.sub (contDiffOn_const (c:=(1:ℝ))))
    (hq.sub (contDiffOn_const (c:=(1:ℝ)))) h hε hε (show (0:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ≤ 1 by norm_num) (by simpa using hdJ) (by simpa using hqJ)
  have he : (fun y => d y*q y-1) =
      (fun y => (d y-1)*(q y-1)+(d y-1)+(q y-1)) := by funext y; ring
  rw [he,fun_iteratedFDeriv_add_apply ((hd'.mul hq').add hd' |>.of_le hle) (hq'.of_le hle),
    fun_iteratedFDeriv_add_apply ((hd'.mul hq').of_le hle) (hd'.of_le hle)]
  have hb := norm_add_le
    (iteratedFDeriv ℝ h (fun y => (d y-1)*(q y-1)) x + iteratedFDeriv ℝ h (fun y => d y-1) x)
    (iteratedFDeriv ℝ h (fun y => q y-1) x)
  have hb' := norm_add_le (iteratedFDeriv ℝ h (fun y => (d y-1)*(q y-1)) x)
    (iteratedFDeriv ℝ h (fun y => d y-1) x)
  have hsq : ε*ε ≤ ε := by nlinarith
  have hp' : ‖iteratedFDeriv ℝ h (fun y => (d y-1)*(q y-1)) x‖ ≤ ε*2^h :=
    hp.trans (by norm_num only [one_add_one_eq_two]; exact mul_le_mul_of_nonneg_right hsq (by positivity))
  have := hdJ h le_rfl
  have := hqJ h le_rfl
  linarith

theorem conductivity_response_jet_bound (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (O : Set E), IsOpen O → ∀ (d q : E → ℝ),
      ContDiffOn ℝ ∞ d O → ContDiffOn ℝ ∞ q O →
      (∀ y ∈ O, 0 < d y) → (∀ y ∈ O, 0 < q y) →
      ∀ (x : E), x ∈ O → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d y-1) x‖ ≤ ε) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q y-1) x‖ ≤ ε) →
      ‖iteratedFDeriv ℝ h (fun y => Real.sqrt (d y*q y)-1) x‖ ≤ C*ε ∧
      ‖iteratedFDeriv ℝ h (fun y => d y/q y-1) x‖ ≤ C*ε := by
  let F : ℝ := 2^h+2
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨A,hA,hAJ⟩ := sqrt_near_one_jet_bound (E:=E) h
  let B := 2*(h.factorial:ℝ)^2/(1/2)*(1+max 1 (1/(1/2)))^h
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨min (1/2) (1/F),max (A*F) B,lt_min (by norm_num) (by positivity),
    (mul_pos hA hF).trans_le (le_max_left _ _),?_⟩
  intro O hO d q hd hq hdp hqp x hx ε hε hεδ hdJ hqJ
  have hεhalf : ε ≤ 1/2 := hεδ.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := by linarith
  have hFe : F*ε ≤ 1 := by
    have hh := hεδ.trans (min_le_right _ _)
    have hh' := (le_div_iff₀ hF).mp hh
    nlinarith
  have hd0 := hdJ 0 (Nat.zero_le h)
  have hq0 := hqJ 0 (Nat.zero_le h)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hd0 hq0
  obtain ⟨hdl,hdu⟩ := abs_le.mp hd0
  obtain ⟨hql,hqu⟩ := abs_le.mp hq0
  have hdlo : 1/2 ≤ d x := by linarith
  have hqlo : 1/2 ≤ q x := by linarith
  have hdhi : d x ≤ 3/2 := by linarith
  have hqhi : q x ≤ 3/2 := by linarith
  constructor
  · have hpJ (j : ℕ) (hj : j ≤ h) :
        ‖iteratedFDeriv ℝ j (fun y => d y*q y-1) x‖ ≤ F*ε := by
      have hp := near_one_product_jet_bound_on hO hx hd hq j hε hε1
        (fun k hk => hdJ k (hk.trans hj)) (fun k hk => hqJ k (hk.trans hj))
      apply hp.trans
      apply mul_le_mul_of_nonneg_right _ hε
      dsimp [F]
      exact add_le_add (show (2:ℝ)^j ≤ 2^h from pow_le_pow_right₀ (by norm_num) hj) le_rfl
    have hb := hAJ O hO (fun y => d y*q y) (hd.mul hq)
      (fun y hy => mul_pos (hdp y hy) (hqp y hy)) x hx (F*ε) (by positivity) hFe hpJ
      ⟨by nlinarith [mul_le_mul hdlo hqlo (by norm_num : (0:ℝ) ≤ 1/2) (hdp x hx).le],
       by nlinarith [mul_le_mul hdhi hqhi (hqp x hx).le (by norm_num : (0:ℝ) ≤ 3/2)]⟩
    exact hb.trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hε)
  · have hnumJ (j : ℕ) (hj : j ≤ h) :
        ‖iteratedFDeriv ℝ j (fun y => d y-q y) x‖ ≤ 2*ε := by
      have ht : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
      have he : (fun y => d y-q y)=(fun y => (d y-1)-(q y-1)) := by funext y; ring
      rw [he,fun_iteratedFDeriv_sub_apply
        (((hd.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)).of_le ht)
        (((hq.sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hx)).of_le ht)]
      exact (norm_sub_le _ _).trans (by linarith [hdJ j hj,hqJ j hj])
    have hqJ' (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h) :
        ‖iteratedFDeriv ℝ j q x‖ ≤ 1 := by
      have hh := hqJ j hjh
      have ht : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
      change ‖iteratedFDeriv ℝ j (q - fun _ => (1:ℝ)) x‖ ≤ ε at hh
      rw [iteratedFDeriv_sub_apply ((hq.contDiffAt (hO.mem_nhds hx)).of_le ht)
        contDiffAt_const,iteratedFDeriv_const_of_ne (by omega) (1:ℝ),Pi.zero_apply,sub_zero] at hh
      exact hh.trans hε1
    have hb := weighted_quotient_jet_bound_on hO hx (hd.sub hq) hq h (δ:=1/2) (W:=1)
      (M:=1) (N:=2*ε) (R:=1) (S:=1) (by norm_num) zero_lt_one (by positivity)
      (by norm_num) (by norm_num) (by simpa using hqlo)
      (by simpa using hnumJ) (by simpa using hqJ')
    have he : (fun y => d y/q y-1) =ᶠ[𝓝 x] (fun y => (d y-q y)/q y) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      field_simp [(hqp y hy).ne']
    rw [(he.iteratedFDeriv ℝ h).self_of_nhds]
    apply hb.trans
    change 2*ε*(h.factorial:ℝ)^2/(1/2)*(1+max 1 (1/(1/2))*1)^h ≤ _
    calc
      _ = B*ε := by dsimp [B]; ring
      _ ≤ max (A*F) B*ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem conductivity_response_all_jets (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (O : Set E), IsOpen O → ∀ (d q : E → ℝ),
      ContDiffOn ℝ ∞ d O → ContDiffOn ℝ ∞ q O →
      (∀ y ∈ O, 0 < d y) → (∀ y ∈ O, 0 < q y) →
      ∀ (x : E), x ∈ O → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d y-1) x‖ ≤ ε) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q y-1) x‖ ≤ ε) →
      ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => Real.sqrt (d y*q y)-1) x‖ ≤ C*ε ∧
      ‖iteratedFDeriv ℝ j (fun y => d y/q y-1) x‖ ≤ C*ε := by
  induction h with
  | zero =>
    obtain ⟨δ,C,hδ,hC,hb⟩ := conductivity_response_jet_bound (E:=E) 0
    refine ⟨δ,C,hδ,hC,?_⟩
    intro O hO d q hd hq hdp hqp x hx ε hε hδε hdJ hqJ j hj
    have he : j=0 := by omega
    subst j
    exact hb O hO d q hd hq hdp hqp x hx ε hε hδε hdJ hqJ
  | succ h ih =>
    obtain ⟨δ,C,hδ,hC,hprev⟩ := ih
    obtain ⟨δ',C',hδ',hC',hnew⟩ := conductivity_response_jet_bound (E:=E) (h+1)
    refine ⟨min δ δ',max C C',lt_min hδ hδ',hC.trans_le (le_max_left _ _),?_⟩
    intro O hO d q hd hq hdp hqp x hx ε hε hδε hdJ hqJ j hj
    by_cases hjh : j ≤ h
    · obtain ⟨ha,hc⟩ := hprev O hO d q hd hq hdp hqp x hx ε hε
        (hδε.trans (min_le_left _ _)) (fun k hk => hdJ k (by omega))
        (fun k hk => hqJ k (by omega)) j hjh
      exact ⟨ha.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε),
        hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε)⟩
    · have he : j=h+1 := by omega
      subst j
      obtain ⟨ha,hc⟩ := hnew O hO d q hd hq hdp hqp x hx ε hε
        (hδε.trans (min_le_right _ _)) hdJ hqJ
      exact ⟨ha.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε),
        hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)⟩

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma conductivity_tensor_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    (a c G : E → ℝ) (Gi P : ι → E → ℝ)
    (ha : ContDiffOn ℝ ∞ a O) (hc : ContDiffOn ℝ ∞ c O)
    (hG : ContDiffOn ℝ ∞ G O) (hGi : ∀ i, ContDiffOn ℝ ∞ (Gi i) O)
    (hP : ∀ i, ContDiffOn ℝ ∞ (P i) O)
    (h : ℕ) {ε A C n : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) (hC : 0 ≤ C) (hn : 1 ≤ n)
    (haJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j a x‖ ≤ ε)
    (hcJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j c x‖ ≤ ε)
    (hGJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j G x‖ ≤ A)
    (hGiJ : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (Gi i) x‖ ≤ A)
    (hPJ : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (P i) x‖ ≤ C*n^j) :
    ‖iteratedFDeriv ℝ h (fun y => a y*G y+(c y-a y)*∑ i, Gi i y*P i y) x‖ ≤
      A*(2^h+2*(Fintype.card ι:ℝ)*C*4^h)*ε*n^h := by
  have hn0 := zero_le_one.trans hn
  let Q := fun y => ∑ i, Gi i y*P i y
  have hQ : ContDiffOn ℝ ∞ Q O := ContDiffOn.sum (fun i _ => (hGi i).mul (hP i))
  have hQJ (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j Q x‖ ≤ ((Fintype.card ι:ℝ)*A*C*2^h)*n^j := by
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have hi (i : ι) : ‖iteratedFDeriv ℝ j (fun y => Gi i y*P i y) x‖ ≤ A*C*2^h*n^j := by
      have hb := geometric_product_jet_bound_on hO hx (hGi i) (hP i) j hA hC
        (show (0:ℝ) ≤ 1 by norm_num) hn0
        (fun k hk => by simpa using hGiJ i k (hk.trans hj))
        (fun k hk => hPJ i k (hk.trans hj))
      calc
        _ ≤ A*C*(1+n)^j := hb
        _ ≤ A*C*(2*n)^j := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (show (0:ℝ) ≤ 1+n by positivity) (show (1:ℝ)+n ≤ 2*n by linarith) j) (mul_nonneg hA hC)
        _ = A*C*2^j*n^j := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj)
            (mul_nonneg hA hC)) (pow_nonneg hn0 _)
    dsimp only [Q]
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (((hGi i).mul (hP i)).contDiffAt (hO.mem_nhds hx)).of_le hle)]
    calc
      _ ≤ ∑ i : ι, ‖iteratedFDeriv ℝ j (fun y => Gi i y*P i y) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, A*C*2^h*n^j := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hcaJ (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j (fun y => c y-a y) x‖ ≤ 2*ε := by
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    rw [fun_iteratedFDeriv_sub_apply ((hc.contDiffAt (hO.mem_nhds hx)).of_le hle)
      ((ha.contDiffAt (hO.mem_nhds hx)).of_le hle)]
    exact (norm_sub_le _ _).trans (by linarith [hcJ j hj,haJ j hj])
  have hfirst := geometric_product_jet_bound_on hO hx ha hG h hε hA
    (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
    (by simpa using haJ) (by simpa using hGJ)
  have hsecond := geometric_product_jet_bound_on hO hx (hc.sub ha) hQ h
    (show 0 ≤ 2*ε by positivity) (show 0 ≤ (Fintype.card ι:ℝ)*A*C*2^h by positivity)
    (show (0:ℝ) ≤ 1 by norm_num) hn0 (by simpa using hcaJ) hQJ
  have hpow : (1+n)^h ≤ 2^h*n^h := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (show (0:ℝ) ≤ 1+n by positivity) (show (1:ℝ)+n ≤ 2*n by linarith) h
  have hp : (1:ℝ) ≤ n^h := one_le_pow₀ hn
  have hf' : ‖iteratedFDeriv ℝ h (fun y => a y*G y) x‖ ≤ ε*A*2^h*n^h :=
    hfirst.trans (by norm_num only [one_add_one_eq_two]; exact le_mul_of_one_le_right (by positivity) hp)
  have hs' : ‖iteratedFDeriv ℝ h (fun y => (c y-a y)*Q y) x‖ ≤
      2*ε*((Fintype.card ι:ℝ)*A*C*2^h)*(2^h*n^h) := hsecond.trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hle : (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))
  change ‖iteratedFDeriv ℝ h (fun y => a y*G y+(c y-a y)*Q y) x‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply (((ha.mul hG).contDiffAt (hO.mem_nhds hx)).of_le hle)
    ((((hc.sub ha).mul hQ).contDiffAt (hO.mem_nhds hx)).of_le hle)]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ε*A*2^h*n^h+2*ε*((Fintype.card ι:ℝ)*A*C*2^h)*(2^h*n^h) := add_le_add hf' hs'
    _ = _ := by rw [show (4:ℝ)^h=2^h*2^h by rw [←mul_pow]; norm_num]; ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem conductivity_metric_realization_uniform_all_jets (hn : Module.finrank ℝ E=3) (h : ℕ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ (g : SmoothMetric E M) (u : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u → ∀ (d q : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q →
      (∀ x, 0 < d x) → (∀ x, 0 < q x) →
      tsupport (fun x => d x-q x^3) ⊆ {x | coordinateGradientPair g u u x ≠ 0} →
      ∃ ĝ : SmoothMetric E M,
        (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
        (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) ∧
        ∀ (p : M) (x : E), x ∈ (chartAt E p).target → ∀ ε A C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ A → 0 ≤ C → 1 ≤ n →
        (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => d ((chartAt E p).symm y)-1) x‖ ≤ ε) →
        (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => q ((chartAt E p).symm y)-1) x‖ ≤ ε) →
        (∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (fun y => metricCoefficients g p y i j) x‖ ≤ A) →
        (((chartAt E p).symm x) ∈ tsupport (fun z => d z-q z^3) →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g u p i j) x‖ ≤ C*n^k) →
        ∀ r ≤ h, ∀ i j : CoordIndex E,
        ‖iteratedFDeriv ℝ r (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) x‖ ≤
          L*A*(2^r+2*(Fintype.card (CoordIndex E):ℝ)*C*4^r)*ε*n^r := by
  obtain ⟨δ,L,hδ,hL,hR⟩ := conductivity_response_all_jets (E:=E) h
  refine ⟨δ,L,hδ,hL,?_⟩
  intro g u hu d q hd hq hd0 hq0 hsupp
  obtain ⟨ĝ,hΔ,hout,hcompat,hformula⟩ := conductivity_metric_realization_complete hn g u hu d q hd hq hd0 hq0 hsupp
  refine ⟨ĝ,hΔ,hout,?_⟩
  intro p x hx ε A C n hε hεδ hA hC hn1 hdJ hqJ hGJ hPJ r hr i j
  let d' := d ∘ (chartAt E p).symm
  let q' := q ∘ (chartAt E p).symm
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hd' : ContDiffOn ℝ ∞ d' O := fun y hy => (contDiffAt_inChart hd p hy).contDiffWithinAt
  have hq' : ContDiffOn ℝ ∞ q' O := fun y hy => (contDiffAt_inChart hq p hy).contDiffWithinAt
  let a := fun y => Real.sqrt (d' y*q' y)-1
  let c := fun y => d' y/q' y-1
  have ha : ContDiffOn ℝ ∞ a O := by
    intro y hy
    exact (((Real.contDiffAt_sqrt (mul_pos (hd0 _) (hq0 _)).ne').comp y
      ((hd'.contDiffAt (hO.mem_nhds hy)).mul (hq'.contDiffAt (hO.mem_nhds hy)))).sub
        contDiffAt_const).contDiffWithinAt
  have hc : ContDiffOn ℝ ∞ c O := (hd'.div hq' (fun y _ => (hq0 _).ne')).sub contDiffOn_const
  have hresponse := hR O hO d' q' hd' hq' (fun y _ => hd0 _) (fun y _ => hq0 _) x hx ε hε hεδ hdJ hqJ
  by_cases hs : (chartAt E p).symm x ∈ tsupport (fun z => d z-q z^3)
  · have hne := hsupp hs
    have hFn := (contDiffAt_inChart (contMDiff_coordinateGradientPair hu hu g) p hx).continuousAt.eventually_ne hne
    obtain ⟨V,hVO,hV,hxV⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hx) hFn)
    have hVT : V ⊆ (chartAt E p).target := fun y hy => (hVO hy).1
    have hVF : ∀ y ∈ V, coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0 := fun y hy => (hVO hy).2
    have hbound := conductivity_tensor_jet_bound_on hV hxV a c
      (fun y => metricCoefficients g p y i j)
      (fun k y => metricCoefficients g p y i k) (fun k => chartGradientProjection g u p k j)
      (ha.mono hVT) (hc.mono hVT) ((contDiffOn_metricCoefficient g p i j).mono hVT)
      (fun k => (contDiffOn_metricCoefficient g p i k).mono hVT)
      (fun k => chartGradientProjection_smooth_on g hu p hV hVT hVF k j) r
      (mul_nonneg hL.le hε) hA hC hn1 (fun k hk => (hresponse k (hk.trans hr)).1)
      (fun k hk => (hresponse k (hk.trans hr)).2) (fun k hk => hGJ i j k (hk.trans hr)) (fun l k hk => hGJ i l k (hk.trans hr)) (fun l k hk => hPJ hs l j k (hk.trans hr))
    have he : (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) =ᶠ[𝓝 x]
        (fun y => a y*metricCoefficients g p y i j+(c y-a y)*∑ k, metricCoefficients g p y i k*chartGradientProjection g u p k j y) := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      rw [hformula p y (hVT hy) (hVF y hy) i j]
      dsimp [a,c,d',q']
      ring
    rw [(he.iteratedFDeriv ℝ r).self_of_nhds]
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have he0 := ((chartAt E p).continuousAt_symm hx).tendsto.eventually
      (notMem_tsupport_iff_eventuallyEq.mp hs)
    have he : (fun y => metricCoefficients ĝ p y i j-metricCoefficients g p y i j) =ᶠ[𝓝 x]
        (fun y => a y*metricCoefficients g p y i j) := by
      filter_upwards [he0] with y hy
      have hdy : d ((chartAt E p).symm y)=q ((chartAt E p).symm y)^3 := sub_eq_zero.mp hy
      have hm := hcompat ((chartAt E p).symm y) hdy (coordinateVector p y i) (coordinateVector p y j)
      change metricCoefficients ĝ p y i j=q ((chartAt E p).symm y)^2*metricCoefficients g p y i j at hm
      rw [hm]
      dsimp [a,d',q']
      rw [hdy,show q ((chartAt E p).symm y)^3*q ((chartAt E p).symm y)=
          (q ((chartAt E p).symm y)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
      ring
    have hb := geometric_product_jet_bound_on hO hx ha (contDiffOn_metricCoefficient g p i j) r
      (mul_nonneg hL.le hε) hA (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
      (by simpa using (fun k hk => (hresponse k (hk.trans hr)).1)) (by simpa using (fun k hk => hGJ i j k (hk.trans hr)))
    rw [(he.iteratedFDeriv ℝ r).self_of_nhds]
    apply hb.trans
    norm_num only [one_add_one_eq_two]
    calc
      L*ε*A*2^r = L*A*2^r*ε := by ring
      _ ≤ L*A*(2^r+2*(Fintype.card (CoordIndex E):ℝ)*C*4^r)*ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (mul_nonneg hL.le hA)) hε
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn1)

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma compact_metric_all_jets (g : SmoothMetric E M) (t : CoordinateTest E M) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x ∈ t.compactSet, ∀ i j : CoordIndex E, ∀ k ≤ h,
      ‖iteratedFDeriv ℝ k (fun y => metricCoefficients g t.center y i j) x‖ ≤ A := by
  classical
  have hb (i j : CoordIndex E) := compact_raw_jet_bound (chartAt E t.center).open_target
    t.isCompact t.inTarget (contDiffOn_metricCoefficient g t.center i j) h
  choose B hB using hb
  let A := 1+∑ i : CoordIndex E, ∑ j : CoordIndex E, B i j
  have hB0 (i j : CoordIndex E) : 0 ≤ B i j := zero_le_one.trans (hB i j).1
  refine ⟨A,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)))
  · intro x hx i j k hk
    calc
      _ ≤ B i j := (hB i j).2 k hk x hx
      _ ≤ ∑ j : CoordIndex E, B i j := Finset.single_le_sum (fun l _ => hB0 i l) (Finset.mem_univ _)
      _ ≤ ∑ i : CoordIndex E, ∑ j : CoordIndex E, B i j := Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg (fun j _ => hB0 l j)) (Finset.mem_univ _)
      _ ≤ A := by dsimp [A]; linarith

theorem conductivity_metric_in_smooth_neighborhood (hn : Module.finrank ℝ E=3)
    (g : SmoothMetric E M) (N : Set (SmoothMetric E M)) (hN : IsSmoothNeighborhood g N) :
    ∃ tests : List (CoordinateTest E M), ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (u d q : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q → (∀ x, 0 < d x) → (∀ x, 0 < q x) →
      tsupport (fun x => d x-q x^3) ⊆ {x | coordinateGradientPair g u u x ≠ 0} →
      ∀ ε C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ C → 1 ≤ n → ε*(1+C)*n^h < δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => d ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => q ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet,
        ((chartAt E t.center).symm x) ∈ tsupport (fun z => d z-q z^3) →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g u t.center i j) x‖ ≤ C*n^k) →
      ∃ ĝ ∈ N,
        (∀ x, laplaceBeltrami ĝ u x=(d x)⁻¹*weightedLaplacian g q u x) ∧
        (∀ x, d x=1 → q x=1 → ∀ v w, ĝ.inner x v w=g.inner x v w) := by
  classical
  obtain ⟨tests,τ,hτ,hN⟩ := hN
  let h := tests.toFinset.sup (fun t => t.order)
  obtain ⟨δ,L,hδ,hL,hR⟩ := conductivity_metric_realization_uniform_all_jets (M:=M) hn h
  choose B hB using fun t : CoordinateTest E M => compact_metric_all_jets g t h
  let A := 1+∑ t ∈ tests.toFinset, B t
  have hB0 (t : CoordinateTest E M) : 0 ≤ B t := zero_le_one.trans (hB t).1
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (fun t _ => hB0 t))
  have hBA (t : CoordinateTest E M) (ht : t ∈ tests) : B t ≤ A := by
    have hb := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) => hB0 t)
      (List.mem_toFinset.mpr ht)
    dsimp [A]
    linarith
  let K := L*A*(2^h+2*(Fintype.card (CoordIndex E):ℝ)*4^h)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨tests,h,min δ (τ/K),lt_min hδ (div_pos hτ hK),?_⟩
  intro u d q hu hd hq hd0 hq0 hsupp ε C n hε hεδ hC hn1 hsmall hdJ hqJ hPJ
  obtain ⟨ĝ,hΔ,hout,hjets⟩ := hR g u hu d q hd hq hd0 hq0 hsupp
  refine ⟨ĝ,hN ĝ ?_,hΔ,hout⟩
  intro t ht x hx
  have hr : t.order ≤ h := Finset.le_sup (f:=fun t : CoordinateTest E M => t.order)
    (List.mem_toFinset.mpr ht)
  have hb := hjets t.center x (t.inTarget hx) ε A C n hε (hεδ.trans (min_le_left _ _))
    (zero_le_one.trans hA) hC hn1 (hdJ t ht x hx) (hqJ t ht x hx)
    (fun i j k hk => ((hB t).2 x hx i j k hk).trans (hBA t ht))
    (hPJ t ht x hx) t.order hr t.row t.column
  have hpow2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr
  have hpow4 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hr
  have hcoeff : (2:ℝ)^t.order+2*(Fintype.card (CoordIndex E):ℝ)*C*4^t.order ≤
      ((2:ℝ)^h+2*(Fintype.card (CoordIndex E):ℝ)*4^h)*(1+C) := by
    have hm := mul_le_mul_of_nonneg_left hpow4
      (show 0 ≤ 2*(Fintype.card (CoordIndex E):ℝ)*C by positivity)
    have hpos : 0 ≤ (2:ℝ)^h*C+2*(Fintype.card (CoordIndex E):ℝ)*4^h := by positivity
    nlinarith
  have hbound : L*A*(2^t.order+2*(Fintype.card (CoordIndex E):ℝ)*C*4^t.order)*ε*n^t.order ≤
      K*(ε*(1+C)*n^h) := by
    calc
      _ ≤ L*A*(((2:ℝ)^h+2*(Fintype.card (CoordIndex E):ℝ)*4^h)*(1+C))*ε*n^h := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff (by positivity)) hε
        · exact pow_le_pow_right₀ hn1 hr
        · positivity
        · positivity
      _ = _ := by dsimp [K]; ring
  exact (hb.trans hbound).trans_lt ((mul_lt_mul_of_pos_left
    (hsmall.trans_le (min_le_right _ _)) hK).trans_eq (mul_div_cancel₀ τ hK.ne'))


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CutoffExactificationSmoothNeighborhood
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chartGradientField_sub_const (g : SmoothMetric E M) (w : M → ℝ) (p : M) (c : ℝ) :
    chartGradientField g (fun z => w z-c) p=chartGradientField g w p := by
  funext i y
  simp only [chartGradientField,coordinateFlux,Function.comp_def,fderiv_sub_const]

theorem weightedLaplacian_small_jets_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b w : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w →
      ∀ (x : E), x ∈ K → ∀ B ε : ℝ, 0 ≤ B → 0 ≤ ε →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (b ∘ (chartAt E p).symm) x‖ ≤ B) →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (fun y => w ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j ((weightedLaplacian g b w) ∘ (chartAt E p).symm) x‖ ≤ C*B*ε := by
  obtain ⟨A,hA,ha,hρ,hρi⟩ := compact_metric_scalar_coefficient_bounds g p hK hKt h
  let S := ∑ i : CoordIndex E, ‖Module.finBasis ℝ E i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let C1 := 2^(h+1)*A*S
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let C2 := 2^(2*h+1)*A*A*S
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  let C := C2*2^(h+1)*C1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  intro b w hb hw x hx B ε hB hε hbJ hwJ
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hxO : x ∈ O := hKt hx
  have hb' : ContDiffOn ℝ ∞ (b ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hb p hy).contDiffWithinAt
  have hX (i : CoordIndex E) : ContDiffOn ℝ ∞ (chartGradientField g w p i) O :=
    chartGradientField_smooth hw g p i
  have hgj : ∀ i : CoordIndex E, ∀ k ≤ h+1,
      ‖iteratedFDeriv ℝ k (chartGradientField g w p i) x‖ ≤ C1*ε := by
    have hg := chartGradientField_sharp_jet_bound (hw.sub (contMDiff_const (c := (1:ℝ)))) g p hxO (h+1)
      (n:=1) (W:=1) (C:=ε) (A:=A) le_rfl zero_lt_one hε (zero_le_one.trans hA)
      (fun i j k hk => ha i j k hk x hx)
      (fun k hk => by simpa only [Function.comp_def,one_pow,mul_one] using hwJ k (by omega))
    rw [chartGradientField_sub_const] at hg
    intro i k hk
    exact (hg i k hk).trans_eq (by dsimp [C1,S]; simp only [one_pow,mul_one]; ring)
  let Z := fun i y => b ((chartAt E p).symm y)*chartGradientField g w p i y
  have hZ (i : CoordIndex E) : ContDiffOn ℝ ∞ (Z i) O := hb'.mul (hX i)
  have hzj : ∀ i : CoordIndex E, ∀ k ≤ h+1,
      ‖iteratedFDeriv ℝ k (Z i) x‖ ≤ (2^(h+1)*C1)*B*ε := by
    intro i k hk
    have hh := geometric_product_jet_bound_on hO hxO hb' (hX i) k hB
      (mul_nonneg hC1 hε) zero_le_one zero_le_one
      (fun j hj => by simpa using hbJ j (hj.trans hk))
      (fun j hj => by simpa using hgj i j (hj.trans hk))
    calc
      _ ≤ B*(C1*ε)*(1+1)^k := hh
      _ ≤ B*(C1*ε)*2^(h+1) := mul_le_mul_of_nonneg_left
        (by norm_num only [one_add_one_eq_two]; exact pow_le_pow_right₀ (by norm_num) hk) (by positivity)
      _ = _ := by ring
  have hdiv := coordinate_divergence_jet_bound_on (Module.finBasis ℝ E)
    (fun y => Real.sqrt (metricCoefficients g p y).det) Z hO hxO
    (contDiffOn_metricDensity g p) (fun y hy => Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy))
    hZ h (zero_le_one.trans hA) (show 0 ≤ (2^(h+1)*C1)*B*ε by positivity)
    (fun k hk => hρ k hk x hx) (fun k hk => hρi k hk x hx) hzj
  have he : ((weightedLaplacian g b w) ∘ (chartAt E p).symm) =ᶠ[𝓝 x]
      coordinateDivergence (Module.finBasis ℝ E) (fun y => Real.sqrt (metricCoefficients g p y).det) Z := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact weightedLaplacian_chartGradient hb hw g p hy
  intro j hj
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ (2^(2*h+1)*A*A*S)*((2^(h+1)*C1)*B*ε) := hdiv j hj
    _ = C*B*ε := by dsimp [C,C2]; ring
    _ ≤ (C+1)*B*ε := by nlinarith [mul_nonneg hB hε]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma constant_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  intro j hj
  have hh := geometric_product_jet_bound_on hO hx hf hg j hF hG zero_le_one zero_le_one
    (fun k hk => by simpa only [one_pow,mul_one] using hfj k (hk.trans hj))
    (fun k hk => by simpa only [one_pow,mul_one] using hgj k (hk.trans hj))
  calc
    _ ≤ F*G*(1+1)^j := hh
    _ ≤ F*G*2^h := mul_le_mul_of_nonneg_left
      (by norm_num only [one_add_one_eq_two]; exact pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hF hG)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma raw_jets_of_near_one {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y-1) x‖ ≤ ε) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ 1+ε := by
  intro j hj
  by_cases hj0 : j=0
  · subst j
    simp only [norm_iteratedFDeriv_zero] at hJ ⊢
    have hv := hJ 0 (Nat.zero_le h)
    simp only [norm_iteratedFDeriv_zero] at hv
    rw [Real.norm_eq_abs] at hv ⊢
    apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg zero_le_one hε)).mp
    rw [sq_abs]
    have hbound := (sq_le_sq₀ (abs_nonneg (f x-1)) hε).mpr hv
    rw [sq_abs] at hbound
    have hupper := (abs_le.mp hv).2
    nlinarith
  · have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have hb := hJ j hj
    rw [fun_iteratedFDeriv_sub_apply ((hf.contDiffAt (hO.mem_nhds hx)).of_le hle)
      contDiffAt_const,iteratedFDeriv_const_of_ne hj0,Pi.zero_apply,sub_zero] at hb
    linarith

theorem cutoff_density_small_jets (g : SmoothMetric E M) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (b s v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v → ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ x ∈ K, ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      let w := cutoffFactor χ v
      ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2-1) x‖ ≤ C*ε ∧
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2+
          Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)-1) x‖ ≤ C*ε := by
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hχ' : ContDiffOn ℝ ∞ (χ ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hχ p hy).contDiffWithinAt
  obtain ⟨A,hA,hAj⟩ := compact_raw_jet_bound hO hK hKt hχ' (h+2)
  obtain ⟨L,hL,hLJ⟩ := weightedLaplacian_small_jets_on_compact g p hK hKt h
  let α := max 1 (2^(h+2)*A)
  have hα : 1 ≤ α := le_max_left _ _
  have hα0 : 0 < α := zero_lt_one.trans_le hα
  let β := (2^h+2)*α
  have hαβ : α ≤ β := by dsimp [β]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) h]
  have hβ : 0 < β := hα0.trans_le hαβ
  let Q := (2^h+2)*β
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let R := 2^h*2*(L*2*α)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨min 1 (1/β),Q+R+1,lt_min zero_lt_one (by positivity),by positivity,?_⟩
  intro b s v hb hs hv Λ hΛ x hx ε hε hεδ hbJ hsJ hvJ w
  have hxO : x ∈ O := hKt hx
  have hε1 : ε ≤ 1 := hεδ.trans (min_le_left _ _)
  have hβε : β*ε ≤ 1 := by have := (le_div_iff₀ hβ).mp (hεδ.trans (min_le_right _ _)); nlinarith
  have hαε : α*ε ≤ 1 := (mul_le_mul_of_nonneg_right hαβ hε).trans hβε
  have heα : ε ≤ α*ε := by nlinarith
  have heβ : ε ≤ β*ε := heα.trans (mul_le_mul_of_nonneg_right hαβ hε)
  have hb' : ContDiffOn ℝ ∞ (b ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hb p hy).contDiffWithinAt
  have hs' : ContDiffOn ℝ ∞ (s ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hs p hy).contDiffWithinAt
  have hv' : ContDiffOn ℝ ∞ (v ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hv p hy).contDiffWithinAt
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w := contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hw' : ContDiffOn ℝ ∞ (w ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hw p hy).contDiffWithinAt
  simp only [Function.comp_def] at hb' hs' hv' hw'
  have hwJ : ∀ j ≤ h+2,
      ‖iteratedFDeriv ℝ j (fun y => w ((chartAt E p).symm y)-1) x‖ ≤ α*ε := by
    have hp := constant_product_jet_bound_on hO hxO hχ' (hv'.sub contDiffOn_const) (h+2)
      (zero_le_one.trans hA) hε (fun k hk => hAj k hk x hx) hvJ
    intro j hj
    have he : (fun y => w ((chartAt E p).symm y)-1)=
        (fun y => χ ((chartAt E p).symm y)*(v ((chartAt E p).symm y)-1)) := by
      funext y; dsimp [w,cutoffFactor]; ring
    rw [he]
    exact (hp j hj).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)
  have hw2J : ∀ j ≤ h, ‖iteratedFDeriv ℝ j
      (fun y => w ((chartAt E p).symm y)^2-1) x‖ ≤ β*ε := by
    intro j hj
    have hp := near_one_product_jet_bound_on hO hxO hw' hw' j (mul_nonneg hα0.le hε) hαε
      (fun k hk => hwJ k (by omega)) (fun k hk => hwJ k (by omega))
    calc
      _ ≤ (2^j+2)*(α*ε) := by simpa only [pow_two,Function.comp_apply] using hp
      _ ≤ (2^h+2)*(α*ε) := mul_le_mul_of_nonneg_right
        (add_le_add (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) le_rfl) (by positivity)
      _ = β*ε := by dsimp [β]; ring
  have hbwJ (f : M → ℝ) (hf : ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) O)
      (hfJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f ((chartAt E p).symm y)-1) x‖ ≤ ε) :
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j
        (fun y => f ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2-1) x‖ ≤ Q*ε := by
    intro j hj
    have hp := near_one_product_jet_bound_on hO hxO hf (hw'.pow 2) j (by positivity : 0 ≤ β*ε) hβε
      (fun k hk => (hfJ k (hk.trans hj)).trans heβ) (fun k hk => hw2J k (hk.trans hj))
    calc
      _ ≤ (2^j+2)*(β*ε) := hp
      _ ≤ (2^h+2)*(β*ε) := mul_le_mul_of_nonneg_right
        (add_le_add (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) le_rfl) (by positivity)
      _ = Q*ε := by dsimp [Q]; ring
  have hbraw := raw_jets_of_near_one hO hxO hb' (h+1) hε hbJ
  have hwraw := raw_jets_of_near_one hO hxO hw' (h+2) (mul_nonneg hα0.le hε) hwJ
  have hlapJ := hLJ b w hb hw x hx 2 (α*ε) (by norm_num) (by positivity)
    (fun j hj => (hbraw j hj).trans (by linarith)) hwJ
  have hlap' : ContDiffOn ℝ ∞ ((weightedLaplacian g b w) ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart (contMDiff_weightedLaplacian hb hw g) p hy).contDiffWithinAt
  simp only [Function.comp_def] at hlap'
  have hprod := constant_product_jet_bound_on hO hxO hw' hlap' h (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ L*2*(α*ε) by positivity) (fun j hj => (hwraw j (by omega)).trans (by linarith)) hlapJ
  have hprod' (j : ℕ) (hj : j ≤ h) : ‖iteratedFDeriv ℝ j
      (fun y => Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)) x‖ ≤ R*ε := by
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have he : (fun y => Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y))=
        (fun y => Λ⁻¹ • (w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y))) := by
      funext y; simp only [smul_eq_mul]; ring
    rw [he,iteratedFDeriv_const_smul_apply' (a:=Λ⁻¹) (((hw'.mul hlap').contDiffAt (hO.mem_nhds hxO)).of_le hle),norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hΛ))]
    calc
      _ ≤ 1*(2^h*2*(L*2*(α*ε))) := mul_le_mul ((inv_le_one₀ (zero_lt_one.trans_le hΛ)).mpr hΛ)
        (hprod j hj) (norm_nonneg _) zero_le_one
      _ = R*ε := by dsimp [R]; ring
  intro j hj
  constructor
  · exact (hbwJ b hb' (fun k hk => hbJ k (by omega)) j hj).trans (by nlinarith [mul_nonneg hR hε])
  · have he : (fun y => s ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2+
          Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)-1)=
        (fun y => (s ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2-1)+
          Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)) := by funext y; ring
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    rw [he,fun_iteratedFDeriv_add_apply
      ((((hs'.mul (hw'.pow 2)).sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hxO)).of_le hle)
      (((((contDiffOn_const (c:=Λ⁻¹)).mul hw').mul hlap').contDiffAt (hO.mem_nhds hxO)).of_le hle)]
    exact (norm_add_le _ _).trans (by have := hbwJ s hs' hsJ j hj; have := hprod' j hj; nlinarith)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix

lemma list_positive_common_lower_bound {α : Type*} (l : List α) (f : α → ℝ)
    (hf : ∀ a ∈ l, 0 < f a) : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ l, δ ≤ f a := by
  induction l with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons a l ih =>
    obtain ⟨δ,hδ,hd⟩ := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    refine ⟨min (f a) δ,lt_min (hf a (List.mem_cons_self)) hδ,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hd b hb)

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem cutoff_density_small_jets_finite (g : SmoothMetric E M) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (tests : List (CoordinateTest E M)) (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (b s v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v → ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      let w := cutoffFactor χ v
      ∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)*w ((chartAt E t.center).symm y)^2-1) x‖ ≤ C*ε ∧
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)*w ((chartAt E t.center).symm y)^2+
          Λ⁻¹*w ((chartAt E t.center).symm y)*weightedLaplacian g b w ((chartAt E t.center).symm y)-1) x‖ ≤ C*ε := by
  classical
  choose d C hd hC hJ using fun t : CoordinateTest E M =>
    cutoff_density_small_jets g χ hχ t.center t.isCompact t.inTarget h
  obtain ⟨δ,hδ,hδd⟩ := list_positive_common_lower_bound tests d (fun t _ => hd t)
  let A := 1+∑ t ∈ tests.toFinset, C t
  have hA : 0 < A := by
    dsimp [A]
    have hs : 0 ≤ ∑ t ∈ tests.toFinset, C t := Finset.sum_nonneg (fun t _ => (hC t).le)
    linarith
  have hCA (t : CoordinateTest E M) (ht : t ∈ tests) : C t ≤ A := by
    have hb := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) => (hC t).le)
      (List.mem_toFinset.mpr ht)
    dsimp [A]
    linarith
  refine ⟨δ,A,hδ,hA,?_⟩
  intro b s v hb hs hv Λ hΛ ε hε hεδ hbJ hsJ hvJ w t ht x hx j hj
  have hh := hJ t b s v hb hs hv Λ hΛ x hx ε hε (hεδ.trans (hδd t ht))
    (hbJ t ht x hx) (hsJ t ht x hx) (hvJ t ht x hx) j hj
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_right (hCA t ht) hε),
    hh.2.trans (mul_le_mul_of_nonneg_right (hCA t ht) hε)⟩

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem cutoff_exactification_in_smooth_neighborhood_oai
    (hdim : Module.finrank ℝ E=3) (g : SmoothMetric E M)
    (N : Set (SmoothMetric E M)) (hN : IsSmoothNeighborhood g N)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
    ∃ tests : List (CoordinateTest E M), ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (b s U v : M → ℝ) (Λ : ℝ) (O F : Set M),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      1 ≤ Λ → (∀ x, 0 < b x) → (∀ x, χ x ∈ Icc (0:ℝ) 1) →
      (∀ x, |v x-1| ≤ 1/2) → (∀ x, |s x-1| ≤ 1/2) →
      (∀ x, weightedLaplacian g b U x+Λ*s x*U x=0) →
      (∀ x, weightedLaplacian g b v x=Λ*b x^3*v x^5-Λ*s x*v x) →
      IsOpen O → IsOpen F → (∀ x ∈ O, χ x=1) → (∀ x ∈ F, χ x=0) →
      (∀ x ∈ F, b x=1 ∧ s x=1) →
      (∀ x, |Λ⁻¹*cutoffFactor χ v x*weightedLaplacian g b (cutoffFactor χ v) x| ≤ 1/16) →
      (∀ x ∉ O ∪ F,
        U x^2*coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x <
          cutoffFactor χ v x^2*coordinateGradientPair g U U x) →
      ∀ ε C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ C → 1 ≤ n → ε*(1+C)*n^h < δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, (chartAt E t.center).symm x ∉ O ∪ F →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g (fun z => U z/cutoffFactor χ v z) t.center i j) x‖ ≤ C*n^k) →
      ∃ ĝ ∈ N, ∃ u : M → ℝ,
        ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧
        (∀ x, -laplaceBeltrami ĝ u x=Λ*u x) ∧
        (∀ x, u x=U x/cutoffFactor χ v x) ∧
        (∀ x, u x=0 ↔ U x=0) ∧ (∀ x, 0 < u x ↔ 0 < U x) ∧
        (∀ x ∈ F, (∀ a c, ĝ.inner x a c=g.inner x a c) ∧ u x=U x) := by
  classical
  obtain ⟨tests,h,η,hη,hReal⟩ := conductivity_metric_in_smooth_neighborhood hdim g N hN
  obtain ⟨δ₀,A,hδ₀,hA,hDall⟩ := cutoff_density_small_jets_finite g χ hχ tests h
  refine ⟨tests,h,min δ₀ (η/A),lt_min hδ₀ (div_pos hη hA),?_⟩
  intro b s U v Λ O F hb hs hU hv hΛ1 hbpos hχrange hvsmall hssmall hweighted hfactor
    hO hF hχO hχF hext hsmall hmargin ε C n hε hεδ hC hn hεn hbJ hsJ hvJ hPJ
  have hΛ : Λ ≠ 0 := (zero_lt_one.trans_le hΛ1).ne'
  let w := cutoffFactor χ v
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hwsmall (x : M) : |w x-1| ≤ 1/2 := by
    change |1+χ x*(v x-1)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (hχrange x).1]
    calc
      χ x*|v x-1| ≤ 1*|v x-1| := mul_le_mul_of_nonneg_right (hχrange x).2 (abs_nonneg _)
      _ ≤ 1/2 := by simpa using hvsmall x
  have hwge (x : M) : 1/2 ≤ w x := by have h := (abs_le.mp (hwsmall x)).1; linarith
  have hwpos (x : M) : 0 < w x := by linarith [hwge x]
  let q := fun x => b x*w x^2
  let d := fun x => s x*w x^2+Λ⁻¹*w x*weightedLaplacian g b w x
  have hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q := hb.mul (hw.pow 2)
  have hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d :=
    (hs.mul (hw.pow 2)).add ((contMDiff_const.mul hw).mul (contMDiff_weightedLaplacian hb hw g))
  have hqpos (x : M) : 0 < q x := mul_pos (hbpos x) (sq_pos_of_pos (hwpos x))
  have hdpos (x : M) : 0 < d x := by
    have hsge : 1/2 ≤ s x := by have h := (abs_le.mp (hssmall x)).1; linarith
    have hw2 : 1/4 ≤ w x^2 := by nlinarith [hwge x]
    have hsw : 1/8 ≤ s x*w x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsge) (sq_nonneg (w x))]
    have hz := (abs_le.mp (hsmall x)).1
    change -(1/16) ≤ Λ⁻¹*w x*weightedLaplacian g b w x at hz
    dsimp only [d]
    linarith
  have hwO {x : M} (hx : x ∈ O) : w =ᶠ[𝓝 x] v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    simp [w,cutoffFactor,hχO y hy]
  have hwF {x : M} (hx : x ∈ F) : w =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hF.mem_nhds hx] with y hy
    simp [w,cutoffFactor,hχF y hy]
  have hcompat {x : M} (hx : x ∈ O) : d x=q x^3 := by
    have he := weightedLaplacian_congr_nhds g (Filter.EventuallyEq.rfl (f:=b)) (hwO hx)
    dsimp only [d,q]
    rw [he,(hwO hx).eq_of_nhds,hfactor x]
    field_simp [hΛ]
    ring
  have hde {x : M} (hx : x ∈ F) : d x=1 ∧ q x=1 := by
    have he := weightedLaplacian_congr_nhds g (Filter.EventuallyEq.rfl (f:=b)) (hwF hx)
    rw [weightedLaplacian_const] at he
    dsimp only [d,q]
    rw [he,(hwF hx).eq_of_nhds,(hext x hx).1,(hext x hx).2]
    simp
  have hsupp : tsupport (fun x => d x-q x^3) ⊆ (O ∪ F)ᶜ := by
    apply closure_minimal _ (hO.union hF).isClosed_compl
    intro x hx
    rw [mem_compl_iff,mem_union]
    rintro (hxo|hxf)
    · exact hx (sub_eq_zero.mpr (hcompat hxo))
    · obtain ⟨hde,hqe⟩ := hde hxf
      exact hx (by change d x-q x^3=0; rw [hde,hqe]; norm_num)
  let u := fun x => U x/w x
  have hu := hU.div₀ hw (fun x => (hwpos x).ne')
  have hsupp' : tsupport (fun x => d x-q x^3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0} := by
    intro x hx
    exact conjugate_gradient_nonzero hU hw g (fun y => (hwpos y).ne') x (hmargin x (hsupp hx))
  have hD := hDall b s v hb hs hv Λ hΛ1 ε hε (hεδ.trans (min_le_left _ _)) hbJ hsJ hvJ
  have hAε : A*ε ≤ η := by
    have he := (le_div_iff₀ hA).mp (hεδ.trans (min_le_right _ _))
    nlinarith
  have hAεn : (A*ε)*(1+C)*n^h < η := by
    have he := (lt_div_iff₀ hA).mp (hεn.trans_le (min_le_right _ _))
    nlinarith
  obtain ⟨ĝ,hĝN,heq,hmetric⟩ := hReal u d q hu hd hq hdpos hqpos hsupp'
    (A*ε) C n (mul_nonneg hA.le hε) hAε hC hn hAεn
    (fun t ht x hx j hj => (hD t ht x hx j hj).2)
    (fun t ht x hx j hj => (hD t ht x hx j hj).1)
    (fun t ht x hx hdX i j k hk => hPJ t ht x hx (hsupp hdX) i j k hk)
  refine ⟨ĝ,hĝN,u,hu,?_,fun _ => rfl,?_,?_,?_⟩
  · intro x
    have hz := intrinsic_conjugated_equation hb hU hw g hΛ (fun x => (hwpos x).ne') hweighted x
    change weightedLaplacian g q u x+Λ*d x*u x=0 at hz
    rw [heq]
    have hdn := (hdpos x).ne'
    field_simp
    nlinarith [hz]
  · intro x
    change U x/w x=0 ↔ U x=0
    simp [(hwpos x).ne']
  · intro x
    exact div_pos_iff_of_pos_right (hwpos x)
  · intro x hx
    obtain ⟨hdx,hqx⟩ := hde hx
    refine ⟨hmetric x hdx hqx,?_⟩
    change U x/w x=U x
    rw [(hwF hx).eq_of_nhds,div_one]


end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood_oai.{u_1, u_2} := @OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood_oai.{u_1, u_2}
