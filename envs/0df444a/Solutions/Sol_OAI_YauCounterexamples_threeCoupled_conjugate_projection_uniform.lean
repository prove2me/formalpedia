-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:26:46.758623+00:00
-- url     : https://prove2.me/submissions/ebc1eec9-92b1-4e98-88b5-8675139ad579

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_conjugate_gradient_lower

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearPowerDirectional
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_smooth (p : E) (L : F →ₗᵢ[ℝ] E) : ContDiff ℝ ∞ (roundChart p L) :=
  contDiff_stereoInvFunAux.comp L.contDiff


end

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
open scoped ContDiff InnerProductSpace Topology




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}

attribute [local instance] OAI.YauCounterexamples.instFactEqNatFinrankRealEuclideanHAddOfNat
lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl


end

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
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
variable {n : ℕ}

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma planarLinear_apply (a b x : E) :
    planarLinear a b x = (inner ℝ a x : ℂ) + Complex.I * (inner ℝ b x : ℂ) := by
  rfl
end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_UnitSphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ProductSphereFstContraction
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma complexIdentityPlanar (z : ℂ) : planarLinear (1:ℂ) Complex.I z = z := by
  apply Complex.ext <;> simp [planarLinear_apply,Complex.inner,Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProductSphereFstPower
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ A] in
lemma productSphere_fstPower_smooth (p : Metric.sphere (0:A) 1) (ℓ : A →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_fstPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.fstL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
omit [FiniteDimensional ℝ B] in
lemma productSphere_sndPower_smooth (p : Metric.sphere (0:B) 1) (ℓ : B →L[ℝ] ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (productSphere_sndPower (n:=n) (m:=m) p ℓ k) :=
  ((ℓ.contDiff.comp (roundChart_smooth _ _)).pow k).comp
    (WithLp.sndL 2 ℝ (Euclidean n) (Euclidean m)).contDiff
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

variable {ι : Type*} [Fintype ι]

theorem rankOne_projection_jet_bound_on (X α : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hα : ∀ i, ContDiffOn ℝ ∞ (α i) O)
    (h : ℕ) {δ W n C B : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hx : δ*W^2 ≤ ∑ i, α i x*X i x)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^j*W)
    (hαj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B*n^j*W)
    (i j : ι) :
    ‖iteratedFDeriv ℝ h
      (fun y => X i y*α j y/(∑ l, α l y*X l y)) x‖ ≤
      (C*B*(h.factorial:ℝ)^2/δ*
        (2+2*max 1 ((Fintype.card ι:ℝ)*C*B/δ))^h)*n^h := by
  have hprod (i j : ι) (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (fun y => X i y*α j y) x‖ ≤ C*B*(2*n)^k*W^2 := by
    have hh := geometric_product_jet_bound_on hO hxO (hX i) (hα j) k
      (show 0 ≤ C*W by positivity) (show 0 ≤ B*W by positivity) hn hn
      (fun l hl => by simpa only [mul_assoc,mul_comm,mul_left_comm] using hXj i l (hl.trans hk))
      (fun l hl => by simpa only [mul_assoc,mul_comm,mul_left_comm] using hαj j l (hl.trans hk))
    convert hh using 1 <;> first | rfl | ring
  have hden : ContDiffOn ℝ ∞ (fun y => ∑ l, α l y*X l y) O :=
    ContDiffOn.sum (fun l _ => (hα l).mul (hX l))
  have hdenj (k : ℕ) (_hk : 1 ≤ k) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (fun y => ∑ l, α l y*X l y) x‖ ≤
        ((Fintype.card ι:ℝ)*C*B)*(2*n)^k*W^2 := by
    rw [iteratedFDeriv_fun_sum_apply (fun l _ =>
      (((hα l).mul (hX l)).contDiffAt (hO.mem_nhds hxO)).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
    calc
      _ ≤ ∑ l : ι, ‖iteratedFDeriv ℝ k (fun y => α l y*X l y) x‖ := norm_sum_le _ _
      _ ≤ ∑ l : ι, C*B*(2*n)^k*W^2 := by
        apply Finset.sum_le_sum
        intro l _
        simpa only [mul_comm] using hprod l l k hk
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hq := weighted_quotient_jet_bound_on hO hxO ((hX i).mul (hα j)) hden h hδ hW
    (mul_nonneg hC hB) (show 0 ≤ 2*n by positivity) (show 0 ≤ 2*n by positivity)
    hx (hprod i j) hdenj
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 2*n+max 1 ((Fintype.card ι:ℝ)*C*B/δ)*(2*n) =
    (2+2*max 1 ((Fintype.card ι:ℝ)*C*B/δ))*n by ring,mul_pow]
  ring
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

theorem chartGradientProjection_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {δ n W C A L : ℝ}
    (hδ : 0 < δ) (hn : 1 ≤ n) (hW : 0 < W)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (he : ∀ i, ‖Module.finBasis ℝ E i‖ ≤ L)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^k*W)
    (hgrad : δ*(n*W)^2 ≤ coordinateGradientPair g u u ((chartAt E p).symm y)) :
    let K := 2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖)
    ∀ i j, ‖iteratedFDeriv ℝ h (chartGradientProjection g u p i j) y‖ ≤
      (K*(C*L)*(h.factorial:ℝ)^2/δ*
        (2+2*max 1 ((Fintype.card (CoordIndex E):ℝ)*K*(C*L)/δ))^h)*n^h := by
  intro K i j
  let α := fun i z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E i)
  have hα (i : CoordIndex E) : ContDiffOn ℝ ∞ (α i) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  have hU : ContDiffOn ℝ ∞ (u ∘ (chartAt E p).symm) (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hαj (i : CoordIndex E) (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (α i) y‖ ≤ (C*L)*n^k*(n*W) := by
    calc
      _ ≤ ‖Module.finBasis ℝ E i‖*‖iteratedFDeriv ℝ (k+1) (u ∘ (chartAt E p).symm) y‖ :=
        norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
      _ ≤ L*(C*n^(k+1)*W) := mul_le_mul (he i) (huj (k+1) (by omega))
        (norm_nonneg _) hL
      _ = _ := by rw [pow_succ]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpair (z : E) : localGradientPair g u u p z =
      ∑ l, α l z*chartGradientField g u p l z := rfl
  have hg : δ*(n*W)^2 ≤ ∑ l, α l y*chartGradientField g u p l y := by
    rw [coordinateGradientPair_inChart hu hu g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy,hpair] at hgrad
    exact hgrad
  have hh := rankOne_projection_jet_bound_on (chartGradientField g u p) α
    (chartAt E p).open_target hy (chartGradientField_smooth hu g p) hα h hδ
    (mul_pos (zero_lt_one.trans_le hn) hW) (zero_le_one.trans hn) hK
    (mul_nonneg hC hL) hg (chartGradientField_sharp_jet_bound hu g p hy h hn hW hC hA haj huj)
    hαj i j
  have hfun : chartGradientProjection g u p i j =
      (fun z => chartGradientField g u p i z*α j z/(∑ l, α l z*chartGradientField g u p l z)) := by
    funext z
    rw [chartGradientProjection,hpair]
  rw [hfun]
  exact hh

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

lemma sharp_conjugate_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f w : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hw : ContDiffOn ℝ ∞ w O)
    (h : ℕ) {δ W n C D : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hn : 1 ≤ n)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : δ ≤ w x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ C*n^j*W)
    (hwj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j w x‖ ≤ D) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/w y) x‖ ≤
      (C*(h.factorial:ℝ)^2/δ*(1+max 1 (D/δ))^h)*n^j*W := by
  intro j hj
  have hh := weighted_quotient_jet_bound_on hO hxO hf hw j hδ zero_lt_one
    (show 0 ≤ C*W by positivity) (zero_le_one.trans hn) (zero_le_one.trans hn)
    (by simpa only [one_pow,mul_one] using hx)
    (fun k hk => by simpa only [one_pow,mul_one,mul_assoc,mul_comm,mul_left_comm] using
        (hfj k (hk.trans hj))) (fun k hk hkj => by
      calc
        _ ≤ D := hwj k hk (hkj.trans hj)
        _ ≤ D*n^k*1^2 := by
          simpa only [one_pow,mul_one] using
            (le_mul_of_one_le_right hD (one_le_pow₀ hn)))
  have hp : (j.factorial:ℝ)^2 ≤ (h.factorial:ℝ)^2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.factorial_le hj
  have hR : 1 ≤ 1+max 1 (D/δ) := by have := le_max_left (1:ℝ) (D/δ); linarith
  calc
    _ ≤ (C*W)*(j.factorial:ℝ)^2/δ*(n+max 1 (D/δ)*n)^j := hh
    _ = (C*(j.factorial:ℝ)^2/δ*(1+max 1 (D/δ))^j)*n^j*W := by
      rw [show n+max 1 (D/δ)*n=(1+max 1 (D/δ))*n by ring,mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hn) _)
      exact mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hδ.le)
        (pow_le_pow_right₀ hR hj) (pow_nonneg (zero_le_one.trans hR) _)
        (div_nonneg (mul_nonneg hC (sq_nonneg _)) hδ.le)

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


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
lemma geometric_complex_product_jet_bound
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
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
lemma complex_power_envelope_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg hA _) hA (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb


end

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_power_weighted_jets {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
        C*(n:ℝ)^j*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ K) hf.contDiffOn h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := Real.exp (-B)
  have hr : 0 < r := Real.exp_pos _
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n x hx j hj
  let A := max ‖f x‖ (Real.exp (φ x))
  have hA : 0 ≤ A := (norm_nonneg _).trans (le_max_left _ _)
  have hrA : r ≤ A := by
    have hlow : -B ≤ φ x := by
      have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hB x hx))
      simpa only [Real.norm_eq_abs] using hh
    exact (Real.exp_le_exp.mpr hlow).trans (le_max_right _ _)
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k f x‖ ≤ A*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using
        (le_max_left ‖f x‖ (Real.exp (φ x)))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk x hx
        _ = r*(D/r) := by field_simp
        _ ≤ A*T^k := mul_le_mul hrA ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) hA
  have hp := complex_power_envelope_jet_bound hf x h n hA hT0 hraw j hj
  have hreal : ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
      A^n*((n:ℝ)*T)^j := by
    calc
      _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
          (hf.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
      _ ≤ 1*(A^n*((n:ℝ)*T)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
        hp (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hAn : A^n ≤ Real.exp ((n:ℝ)*φ x)+‖f x‖^n := by
    by_cases he : ‖f x‖ ≤ Real.exp (φ x)
    · dsimp [A]
      rw [max_eq_right he,←Real.exp_nat_mul]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · dsimp [A]
      rw [max_eq_left (le_of_not_ge he)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have he : A^n*((n:ℝ)*T)^j = T^j*(n:ℝ)^j*A^n := by rw [mul_pow]; ring
  rw [he] at hreal
  exact hreal.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    hAn (pow_nonneg hA _) (by positivity))

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
section CompactInverseJets
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma compact_metric_inverse_jets (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i j : CoordIndex E, ∀ k ≤ h, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A := by
  classical
  choose B hB hBj using fun i j : CoordIndex E =>
    compact_raw_jet_bound (chartAt E p).open_target hK hKO (contDiffOn_metricInverse g p i j) h
  let A := 1+∑ i, ∑ j, B i j
  have hB0 (i j : CoordIndex E) : 0 ≤ B i j := zero_le_one.trans (hB i j)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)))
  refine ⟨A,hA,?_⟩
  intro i j k hk y hy
  calc
    _ ≤ B i j := hBj i j k hk y hy
    _ ≤ ∑ j, B i j := Finset.single_le_sum (fun j _ => hB0 i j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)) (Finset.mem_univ i)
    _ ≤ A := by dsimp [A]; linarith
end CompactInverseJets


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm (p : ThreeManifold) :
    threeImmersion ∘ (chartAt ThreeModel p).symm = threeChartMap p := by
  funext y
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · change ((chartAt (Euclidean 2) p.1).symm y.fst : Euclidean 3) = _
    exact congrFun (sphere_chart_symm p.1) y.fst
  · change ((chartAt (Euclidean 1) p.2).symm y.snd : ℂ) = _
    exact congrFun (unitSphere_chart_symm (n:=1) p.2) y.snd
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
attribute [local instance] OAI.YauCounterexamples.threeModelNormedSpace'
local instance threeModelContinuousSMul'_r09319b_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_r09319b_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
lemma threeComplexPower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℂ) ∞ (threeComplexPower a b k) := by
  let L : ThreeAmbient →L[ℝ] ℂ := (planarLinear a b).comp (WithLp.fstL 2 ℝ (Euclidean 3) ℂ)
  let R : ThreeAmbient →L[ℝ] ℂ := WithLp.sndL 2 ℝ (Euclidean 3) ℂ
  have hh : ContDiff ℝ ∞ (fun x : ThreeAmbient => (L x)^k*(R x)^k) :=
    (L.contDiff.pow k).mul (R.contDiff.pow k)
  have hc := hh.contMDiff.comp (I:=𝓘(ℝ,ThreeModel)) threeImmersion_smooth
  exact hc
lemma threePower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threePower a b k) :=
  Complex.reCLM.contMDiff.comp (threeComplexPower_smooth a b k)
attribute [local instance] OAI.YauCounterexamples.sphereN_dimension_fact
lemma threeComplexPower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threeComplexPower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z := by
  funext y
  have hh := congrFun (three_chart_symm p) y
  have h₁ := congrArg (fun q : ThreeAmbient => q.fst) hh
  have h₂ := congrArg (fun q : ThreeAmbient => q.snd) hh
  change (((chartAt ThreeModel p).symm y).1:Euclidean 3) =
    roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst at h₁
  change (((chartAt ThreeModel p).symm y).2:ℂ) =
    roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd at h₂
  simp only [Function.comp_apply,threeComplexPower,h₁,h₂]
  simp only [productSphere_fstPower,productSphere_sndPower,Function.comp_apply]
  rw [complexIdentityPlanar]
  rfl
end


section
open Set Filter
open scoped Topology

lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ) ≤ productWaveFrequency k ∧ productWaveFrequency k ≤ 2*(k:ℝ) := by
  have hp : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  have hs0 := Real.sqrt_nonneg (productFrequency k+1)
  dsimp [productFrequency] at hs hs0 ⊢
  unfold productWaveFrequency productFrequency
  constructor <;> nlinarith [sq_nonneg ((k:ℝ)-1)]
end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeFirstNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
attribute [local instance] OAI.YauCounterexamples.threeFirstNormedSpace
local instance threeFirstContinuousSMul_r09319b_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.sphereFirst_dimension_fact
lemma threeComplexPower_chart_smooth (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ∞ (threeComplexPower a b k ∘ (chartAt ThreeModel p).symm) := by
  rw [threeComplexPower_chart]
  exact (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
lemma productAxis_coord (i : Fin 3) (x : Euclidean 3) : inner ℝ (productAxis i) x = x i := by
  simp [productAxis,EuclideanSpace.inner_single_left]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
attribute [local instance] OAI.YauCounterexamples.threeCoupledNormedSpace
local instance threeCoupledContinuousSMul_r09319b_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_smooth (r : ℝ) (k : ℕ) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeCoupled r k) := by
  rw [threeCoupled_eq]
  exact (threePower_smooth _ _ _).add (contMDiff_const.mul (threePower_smooth _ _ _))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ThreeNoncancelNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
lemma productSphere_norm_sq (p : Sphere 2) : (p:Euclidean 3) 0^2+(p:Euclidean 3) 1^2+(p:Euclidean 3) 2^2=1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (p:Euclidean 3)
  simpa [hn,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,add_assoc] using hh.symm
lemma productB_norm_le (p : Sphere 2) : ‖productB p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productB p)
  simp only [Complex.normSq_apply,productB_re,productB_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 1),norm_nonneg (productB p)]

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeCoupledCleanChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma real_smooth_add_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f+h) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖+‖iteratedFDeriv ℝ j h x‖ := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  rw [iteratedFDeriv_add_apply (hf.of_le hj).contDiffAt (hh.of_le hj).contDiffAt]
  exact norm_add_le _ _

end


section
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

lemma real_power_variable_weighted_jets {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C > 0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^k).re) x‖ ≤
        C*(k:ℝ)^j*(Real.exp (productWaveFrequency k*φ x)+‖f x‖^k) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  obtain ⟨C,hC,hjet⟩ := real_power_weighted_jets hf hK (fun _ => -2*D)
    continuousOn_const h
  refine ⟨C,hC,?_⟩
  intro k hk x hx j hj
  have hp : (0:ℝ)≤k := Nat.cast_nonneg _
  have hν := productWaveFrequency_bounds hk
  have hν0 : 0≤productWaveFrequency k := hp.trans hν.1
  have hm : -D≤φ x := by
    have hb := hB x hx
    rw [Real.norm_eq_abs] at hb
    exact (neg_le_neg (le_max_left B 0)).trans ((neg_le_neg hb).trans (neg_abs_le _))
  have he : Real.exp ((k:ℝ)*(-2*D))≤Real.exp (productWaveFrequency k*φ x) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = (2*(k:ℝ))*(-D) := by ring
      _ ≤ productWaveFrequency k*(-D) := mul_le_mul_of_nonpos_right hν.2 (neg_nonpos.mpr hD)
      _ ≤ _ := mul_le_mul_of_nonneg_left hm hν0
  exact (hjet k x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add he le_rfl) (by positivity))

lemma threeCoupled_split_powers (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    threeCoupled r k p =
      ((threeComplexPower (productAxis 0) (productAxis 1) 1 p)^k).re+
      (((r:ℂ)*threeComplexPower (productAxis 0) (productAxis 2) 1 p)^k).re := by
  simp only [threeCoupled,threeCoupledComplex,threeComplexPower,pow_one,mul_pow,
    Complex.add_re,add_mul,productA,productB,mul_assoc]

attribute [local instance] OAI.YauCounterexamples.threeWeightedNormedSpace
local instance threeWeightedContinuousSMul_r09319b_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
theorem threeCoupled_weighted_chart_jets {φ : ThreeManifold → ℝ}
    (hφ : Continuous φ) (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h : ℕ) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ x ∈ K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘
        (chartAt ThreeModel p).symm) x‖ ≤ C*(k:ℝ)^j*
          threeWeight φ k ((chartAt ThreeModel p).symm x) := by
  let a := threeComplexPower (productAxis 0) (productAxis 1) 1 ∘ (chartAt ThreeModel p).symm
  let b := fun x => (threeCouplingRadius:ℂ)*
    (threeComplexPower (productAxis 0) (productAxis 2) 1 ∘ (chartAt ThreeModel p).symm) x
  have ha : ContDiff ℝ ∞ a := threeComplexPower_chart_smooth _ _ _ _
  have hb : ContDiff ℝ ∞ b := contDiff_const.mul (threeComplexPower_chart_smooth _ _ _ _)
  have hc : ContinuousOn (φ ∘ (chartAt ThreeModel p).symm) K :=
    (hφ.comp (three_chart_symm_continuous p)).continuousOn
  obtain ⟨A,hA,haj⟩ := real_power_variable_weighted_jets ha hK _ hc h
  obtain ⟨B,hB,hbj⟩ := real_power_variable_weighted_jets hb hK _ hc h
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro k hk x hx j hj
  have he : threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm =
      (fun y => (a y^k).re)+(fun y => (b y^k).re) := by
    funext y
    exact threeCoupled_split_powers _ _ _
  have han : ‖a x‖≤threeGlobalRadius ((chartAt ThreeModel p).symm x) := by
    dsimp [a,threeComplexPower]
    simp only [pow_one,norm_mul,Circle.norm_coe,mul_one]
    exact le_max_left _ _
  have hbn : ‖b x‖≤threeGlobalRadius ((chartAt ThreeModel p).symm x) := by
    dsimp [b,threeComplexPower]
    simp only [pow_one,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<threeCouplingRadius by norm_num [threeCouplingRadius])]
    exact le_max_right _ _
  have hja := (haj k hk x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) han k)) (by positivity))
  have hjb := (hbj k hk x hx j hj).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hbn k)) (by positivity))
  rw [he]
  exact (real_smooth_add_jet_bound (Complex.reCLM.contDiff.comp (ha.pow k))
    (Complex.reCLM.contDiff.comp (hb.pow k)) j x).trans
    (calc
      _ ≤ A*(k:ℝ)^j*threeWeight φ k ((chartAt ThreeModel p).symm x)+
          B*(k:ℝ)^j*threeWeight φ k ((chartAt ThreeModel p).symm x) := add_le_add hja hjb
      _ = _ := by ring)
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
lemma threeCoupled_clean_chart_jets (p : ThreeManifold) {K : Set ThreeModel}
    (hK : IsCompact K) (h : ℕ)
    (hρ : ∀ y∈K, 1/2≤‖productA ((chartAt ThreeModel p).symm y).1‖) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ y∈K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm) y‖
        ≤ C*(k:ℝ)^j*‖productA ((chartAt ThreeModel p).symm y).1‖^k := by
  obtain ⟨C,hC,hj⟩ := threeCoupled_weighted_chart_jets
    (φ:=fun _ => Real.log (1/2)) continuous_const p hK h
  refine ⟨2*C,by positivity,?_⟩
  intro k hk y hy j hjh
  let q := (chartAt ThreeModel p).symm y
  have hr : threeGlobalRadius q=‖productA q.1‖ := by
    apply max_eq_left
    have hb := mul_le_mul_of_nonneg_left (productB_norm_le q.1)
      (show 0≤threeCouplingRadius by norm_num [threeCouplingRadius])
    norm_num [threeCouplingRadius] at hb ⊢
    linarith [hρ y hy]
  have he : Real.exp (productWaveFrequency k*Real.log (1/2))≤‖productA q.1‖^k := by
    calc
      _ ≤ Real.exp ((k:ℝ)*Real.log (1/2)) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (productWaveFrequency_bounds hk).1
          (Real.log_nonpos (by norm_num) (by norm_num)))
      _ = (1/2:ℝ)^k := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<1/2)]
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (hρ y hy) k
  have hh := hj k hk y hy j hjh
  change _ ≤ C*(k:ℝ)^j*(Real.exp (productWaveFrequency k*Real.log (1/2))+threeGlobalRadius q^k) at hh
  rw [hr] at hh
  exact hh.trans (calc
    _ ≤ C*(k:ℝ)^j*(‖productA q.1‖^k+‖productA q.1‖^k) :=
      mul_le_mul_of_nonneg_left (add_le_add he le_rfl) (by positivity)
    _ = _ := by ring)

theorem threeCoupled_conjugate_projection_uniform_oai
    (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold)
    {K : Set ThreeModel} (hK : IsCompact K)
    (hKO : K ⊆ (chartAt ThreeModel p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) ((chartAt ThreeModel p).symm y),
      g.inner _ v z = threeBackgroundMetric.inner _ v z)
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, 1/2 ≤ ‖productA ((chartAt ThreeModel p).symm y).1‖)
    (hKt : ∀ y ∈ K, ‖productA ((chartAt ThreeModel p).symm y).1‖ ≤ 3/4)
    : ∃ C : ℝ, 0 < C ∧ ∀ (w : ThreeManifold → ℝ),
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
      (∀ x, w x ≠ 0) →
      (∀ y ∈ K, 1/2 ≤ w ((chartAt ThreeModel p).symm y)) →
      (∀ y ∈ K, w ((chartAt ThreeModel p).symm y) ≤ 2) →
      (∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel p).symm) y‖ ≤ D) →
      (∀ y ∈ K, coordinateGradientPair g w w ((chartAt ThreeModel p).symm y) ≤ 1/4096) →
    ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex ThreeModel,
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => threeCoupled threeCouplingRadius n x/w x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  obtain ⟨C0,hC0,hCj⟩ := threeCoupled_clean_chart_jets p hK (h+1) hKr
  obtain ⟨A,hA,hAj⟩ := compact_metric_inverse_jets g p hK hKO h
  let C1 := C0*((h+1).factorial:ℝ)^2/(1/2)*(1+max 1 (D/(1/2)))^(h+1)
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let L := ∑ j, ‖Module.finBasis ℝ ThreeModel j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he (i : CoordIndex ThreeModel) : ‖Module.finBasis ℝ ThreeModel i‖ ≤ L :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  let δ := (1/1024:ℝ)
  have hδ : 0 < δ := by norm_num [δ]
  let J := 2^h*A*C1*L
  let C := J*(C1*L)*(h.factorial:ℝ)^2/δ*
    (2+2*max 1 ((Fintype.card (CoordIndex ThreeModel):ℝ)*J*(C1*L)/δ))^h
  refine ⟨max C 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro w hw hw0 hwl hwu hwj hwG n hn y hy i j
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let W := ‖productA ((chartAt ThreeModel p).symm y).1‖^n
  have hrY : 0 < ‖productA ((chartAt ThreeModel p).symm y).1‖ :=
    (by norm_num : (0:ℝ)<1/2).trans_le (hKr y hy)
  have hW : 0 < W := pow_pos hrY _
  let u := fun x => threeCoupled threeCouplingRadius n x/w x
  have hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u :=
    (threeCoupled_smooth _ _).div₀ hw hw0
  have huw : ContDiffOn ℝ ∞ (w ∘ (chartAt ThreeModel p).symm)
      (chartAt ThreeModel p).target := fun z hz => (contDiffAt_inChart hw p hz).contDiffWithinAt
  have hu0 : ContDiffOn ℝ ∞ (threeCoupled threeCouplingRadius n ∘ (chartAt ThreeModel p).symm)
      (chartAt ThreeModel p).target :=
    fun z hz => (contDiffAt_inChart (threeCoupled_smooth _ _) p hz).contDiffWithinAt
  have huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt ThreeModel p).symm) y‖ ≤
      C1*(n:ℝ)^k*W := by
    exact sharp_conjugate_jet_bound_on (chartAt ThreeModel p).open_target (hKO hy)
      hu0 huw (h+1) (by norm_num : (0:ℝ)<1/2) hW hnR hC0.le hD (hwl y hy)
      (fun k hk => hCj n hn y hy k hk) (fun k hk hkh => hwj k hk hkh y hy)
  have hgrad : δ*((n:ℝ)*W)^2 ≤ coordinateGradientPair g u u ((chartAt ThreeModel p).symm y) :=
    threeCoupled_conjugate_gradient_lower g _ (hg y hy) n hn (hKr y hy) (hKt y hy)
      w hw hw0 (hwl y hy) (hwu y hy) (hwG y hy)
  have hp := chartGradientProjection_jet_bound hu g p (hKO hy) h hδ hnR hW hC1
    (zero_le_one.trans hA) hL he (fun i j k hk => hAj i j k hk y hy) huj hgrad i j
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg (Nat.cast_nonneg _) _))

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform_oai := @OAI.YauCounterexamples.threeCoupled_conjugate_projection_uniform_oai
