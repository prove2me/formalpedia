-- Prove2me | solution 1 for OAI.YauCounterexamples.threeCoupled_dominated_residual_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:27:31.39503+00:00
-- url     : https://prove2.me/submissions/bbd2c804-e312-453b-ae73-80aa292d5dd1

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

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
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_TransverseZeroKernel
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
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_const (g : SmoothMetric E M) (c : ℝ) (x : M) :
    laplaceBeltrami g (fun _ => c) x = 0 := by
  simp [laplaceBeltrami, Function.comp_def]

lemma laplaceBeltrami_add {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y + v y) x =
      laplaceBeltrami g u x + laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_add
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

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
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_small_jets_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ (x : E), x ∈ K → ∀ ε : ℝ, 0 ≤ ε →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) x‖ ≤ ε) →
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j ((laplaceBeltrami g u) ∘ (chartAt E p).symm) x‖ ≤ C*ε := by
  obtain ⟨C,hC,hJ⟩ := weightedLaplacian_small_jets_on_compact g p hK hKt h
  refine ⟨C,hC,?_⟩
  intro u hu x hx ε hε huJ
  have he : weightedLaplacian g (fun _ => 1) (fun z => u z+1) = laplaceBeltrami g u := by
    funext z
    have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => u z+1) := hu.add contMDiff_const
    rw [weightedLaplacian_expansion (b := fun _ => 1) (u := fun z => u z+1) contMDiff_const
      (hw.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    rw [laplaceBeltrami_add (u := u) (v := fun _ => 1)
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) contMDiff_const,laplaceBeltrami_const]
    simp [coordinateGradientPair,Function.comp_def]
  have hh := hJ (fun _ => 1) (fun z => u z+1) contMDiff_const (hu.add contMDiff_const)
    x hx 1 ε zero_le_one hε (by
      intro j hj
      cases j with
      | zero => simp
      | succ j => simp [Function.comp_def,iteratedFDeriv_succ_const]) (by
      intro j hj
      simpa only [add_sub_cancel_right,Function.comp_def] using huJ j hj)
  rw [he] at hh
  simpa only [mul_one] using hh

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
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_residual_small_jets_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ (x : E), x ∈ K → ∀ ε Λ : ℝ, 0 ≤ ε → 0 ≤ Λ →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) x‖ ≤ ε) →
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g u z+Λ*u z) ∘ (chartAt E p).symm) x‖ ≤ (C+Λ)*ε := by
  obtain ⟨C,hC,hJ⟩ := laplaceBeltrami_small_jets_on_compact g p hK hKt h
  refine ⟨C,hC,?_⟩
  intro u hu x hx ε Λ hε hΛ huJ j hj
  have hc : ContDiffAt ℝ ∞ (u ∘ (chartAt E p).symm) x := contDiffAt_inChart hu p (hKt hx)
  have hl : ContDiffAt ℝ ∞ ((laplaceBeltrami g u) ∘ (chartAt E p).symm) x :=
    contDiffAt_inChart (contMDiff_laplaceBeltrami hu g) p (hKt hx)
  have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have he : ((fun z => laplaceBeltrami g u z+Λ*u z) ∘ (chartAt E p).symm) =
      (fun y => ((laplaceBeltrami g u) ∘ (chartAt E p).symm) y + Λ • (u ∘ (chartAt E p).symm) y) := rfl
  rw [he, fun_iteratedFDeriv_add_apply (hl.of_le hle) ((hc.const_smul Λ).of_le hle),
    iteratedFDeriv_const_smul_apply' (hc.of_le hle)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j ((laplaceBeltrami g u) ∘ (chartAt E p).symm) x‖ +
        ‖Λ • iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) x‖ := norm_add_le _ _
    _ ≤ C*ε + Λ*ε := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hΛ]
      exact add_le_add (hJ u hu x hx ε hε huJ j hj)
        (mul_le_mul_of_nonneg_left (huJ j (by omega)) hΛ)
    _ = (C+Λ)*ε := by ring

end

open Set Filter Function Manifold
open scoped Topology ContDiff



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
local instance threeModelContinuousSMul'_r6ed6af_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_r6ed6af_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
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
lemma productWaveFrequency_equation (k : ℕ) :
    productWaveFrequency k*(productWaveFrequency k+2)=productFrequency k := by
  have h := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  unfold productWaveFrequency
  nlinarith
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
local instance threeFirstContinuousSMul_r6ed6af_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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
lemma productA_re (x : Euclidean 3) : (productA x).re=x 0 := by simp [productA,planarLinear,productAxis_coord]
lemma productA_im (x : Euclidean 3) : (productA x).im=x 1 := by simp [productA,planarLinear,productAxis_coord]
lemma productB_re (x : Euclidean 3) : (productB x).re=x 0 := by simp [productB,planarLinear,productAxis_coord]
lemma productB_im (x : Euclidean 3) : (productB x).im=x 2 := by simp [productB,planarLinear,productAxis_coord]
lemma threeCoupled_eq (r : ℝ) (k : ℕ) : threeCoupled r k =
    fun p => threePower (productAxis 0) (productAxis 1) k p+r^k*threePower (productAxis 0) (productAxis 2) k p := by
  funext p
  simp only [threeCoupled,threeCoupledComplex,add_mul,mul_assoc,Complex.add_re,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul,threePower,threeComplexPower,productA,productB]
attribute [local instance] OAI.YauCounterexamples.threeCoupledNormedSpace
local instance threeCoupledContinuousSMul_r6ed6af_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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
lemma productA_norm_le (p : Sphere 2) : ‖productA p‖≤1 := by
  have hh := productSphere_norm_sq p
  have hn := Complex.normSq_eq_norm_sq (productA p)
  simp only [Complex.normSq_apply,productA_re,productA_im] at hn
  nlinarith [sq_nonneg ((p:Euclidean 3) 2),norm_nonneg (productA p)]
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
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeEnvelopeExponent_pos : 0<threeEnvelopeExponent := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
lemma threeEnvelopeExponent_lt : threeEnvelopeExponent<1 := by
  unfold threeEnvelopeExponent
  have h : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg 2]
  exact (inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h
lemma threeEnvelopeExponent_mul : threeEnvelopeExponent*Real.sqrt 2=1 := by
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))

end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeGlobalRadius_lower (p : ThreeManifold) : (1/200:ℝ) ≤ threeGlobalRadius p := by
  have ha := Complex.normSq_eq_norm_sq (productA p.1)
  have hb := Complex.normSq_eq_norm_sq (productB p.1)
  simp only [Complex.normSq_apply,productA_re,productA_im,productB_re,productB_im] at ha hb
  have hs := productSphere_norm_sq p.1
  by_contra hn
  have hn : threeGlobalRadius p < 1/200 := lt_of_not_ge hn
  have hA := (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  have hB := (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)).trans_lt hn
  dsimp [threeCouplingRadius] at hB
  have hB' : ‖productB p.1‖<1/2 := by linarith
  have hA' : ‖productA p.1‖<1/2 := by linarith
  nlinarith [norm_nonneg (productA p.1), norm_nonneg (productB p.1),sq_nonneg ((p.1:Euclidean 3) 0)]
lemma threeGlobalRadius_pos (p : ThreeManifold) : 0<threeGlobalRadius p :=
  lt_of_lt_of_le (by norm_num) (threeGlobalRadius_lower p)
lemma threeGlobalRadius_le_one (p : ThreeManifold) : threeGlobalRadius p≤1 := by
  apply max_le (productA_norm_le p.1)
  have hb:=productB_norm_le p.1
  dsimp [threeCouplingRadius]
  nlinarith [norm_nonneg (productB p.1)]
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma productWaveFrequency_scaled_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ)-1 ≤ productWaveFrequency k*threeEnvelopeExponent ∧
      productWaveFrequency k*threeEnvelopeExponent ≤ k := by
  have hn : (0:ℝ)≤k := Nat.cast_nonneg _
  have hb := productWaveFrequency_bounds hk
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have he := productWaveFrequency_equation k
  dsimp [productFrequency] at he
  have hsK : (Real.sqrt 2*(k:ℝ))^2=2*(k:ℝ)^2 := by rw [mul_pow,hs]
  have hupper : productWaveFrequency k≤Real.sqrt 2*(k:ℝ) := by
    have hv : productWaveFrequency k ^ 2 ≤ 2*(k:ℝ)^2 := by nlinarith [hb.1]
    exact (sq_le_sq₀ (hn.trans hb.1) (mul_nonneg hp.le hn)).mp (by simpa only [hsK] using hv)
  have hlower : Real.sqrt 2*(k:ℝ)≤productWaveFrequency k+1 := by
    have hh := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
    have hz := Real.sqrt_nonneg (productFrequency k+1)
    dsimp [productWaveFrequency,productFrequency] at hh hz ⊢
    nlinarith [sq_nonneg (Real.sqrt (2*(k:ℝ)^2+(k:ℝ)+1)-Real.sqrt 2*(k:ℝ))]
  have hc := threeEnvelopeExponent_pos
  have hc1 := threeEnvelopeExponent_lt
  have hmul := threeEnvelopeExponent_mul
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlower hc.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hupper hc.le
    nlinarith

lemma three_radius_pow_eq_exp (p : ThreeManifold) (k : ℕ) :
    threeGlobalRadius p^k=Real.exp ((k:ℝ)*Real.log (threeGlobalRadius p)) := by
  rw [Real.exp_nat_mul,Real.exp_log (threeGlobalRadius_pos p)]

lemma three_positive_envelope_gap (p : ThreeManifold) {k : ℕ} (hk : 1≤k)
    {φ δ : ℝ} (hgap : threeGlobalLog p+δ≤φ) :
    threeGlobalRadius p^k ≤ Real.exp (productWaveFrequency k*(φ-δ)) := by
  have hc := (productWaveFrequency_scaled_bounds hk).2
  have hn := (Nat.cast_nonneg k).trans (productWaveFrequency_bounds hk).1
  have hl := Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p)
  rw [three_radius_pow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonpos_right hc hl
  have hg := mul_le_mul_of_nonneg_left hgap hn
  dsimp [threeGlobalLog] at hg
  nlinarith

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
local instance threeWeightedContinuousSMul_r6ed6af_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
attribute [local instance] OAI.YauCounterexamples.threeResidualNormedSpace
local instance threeResidualContinuousSMul_r6ed6af_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeCoupled_dominated_chart_jets {φ : ThreeManifold → ℝ} (hφ : Continuous φ)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h : ℕ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ x∈K, threeGlobalLog ((chartAt ThreeModel p).symm x)+δ ≤ φ ((chartAt ThreeModel p).symm x)) :
    ∃ C>0, ∀ k : ℕ, 1≤k → ∀ x∈K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j (threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm) x‖ ≤
        C*(k:ℝ)^j*(Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x)) := by
  obtain ⟨C,hC,hJ⟩ := threeCoupled_weighted_chart_jets (hφ.sub continuous_const) p hK h (φ:=fun z => φ z-δ/2)
  refine ⟨2*C,by positivity,?_⟩
  intro k hk x hx j hj
  let z := (chartAt ThreeModel p).symm x
  have hb := productWaveFrequency_bounds hk
  have hn : 0≤productWaveFrequency k := (Nat.cast_nonneg k).trans hb.1
  have hrad : threeGlobalRadius z^k≤ Real.exp (productWaveFrequency k*(φ z-δ/2)) := by
    apply three_positive_envelope_gap z hk (δ:=δ/2)
    dsimp [z]
    linarith [hgap x hx]
  have he : Real.exp (productWaveFrequency k*(φ z-δ/2)) ≤
      (Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ z) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hb.1 (half_pos hδ).le
    nlinarith
  have hw : threeWeight (fun z => φ z-δ/2) k z ≤
      2*((Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ z)) := by
    dsimp [threeWeight]
    linarith
  apply (hJ k hk x hx j hj).trans
  calc
    _ ≤ C*(k:ℝ)^j*(2*((Real.exp (-δ/2))^k*Real.exp (productWaveFrequency k*φ z))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

theorem threeCoupled_dominated_residual_rapid_decay_oai
    (g : SmoothMetric ThreeModel ThreeManifold) {φ : ThreeManifold → ℝ} (hφ : Continuous φ)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (h P : ℕ)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ x∈K, threeGlobalLog ((chartAt ThreeModel p).symm x)+δ ≤ φ ((chartAt ThreeModel p).symm x)) :
    ∃ N : ℕ, 1≤N ∧ ∀ k≥N, ∀ x∈K, ∀ j≤h,
      ‖iteratedFDeriv ℝ j ((fun z => laplaceBeltrami g (threeCoupled threeCouplingRadius k) z+
        productFrequency k*threeCoupled threeCouplingRadius k z) ∘ (chartAt ThreeModel p).symm) x‖ ≤
          ((k:ℝ)^P)⁻¹*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x)) := by
  obtain ⟨A,hA,hAJ⟩ := threeCoupled_dominated_chart_jets hφ p hK (h+2) hδ hgap
  obtain ⟨L,hL,hLJ⟩ := laplaceBeltrami_residual_small_jets_on_compact g p hK
    (by rw [three_chart_target]; exact subset_univ _) h
  let ρ := Real.exp (-δ/2)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  let D := (L+3)*A
  have ht : Tendsto (fun k : ℕ => D*((k:ℝ)^(h+4+P)*ρ^k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (h+4+P) hρ.le hρ1).const_mul D
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro k hk x hx j hj
  have hk1 : 1≤k := (le_max_right _ _).trans hk
  have hkR : 1≤(k:ℝ) := by exact_mod_cast hk1
  have hkpos : 0<(k:ℝ) := zero_lt_one.trans_le hkR
  have hsmall : D*(k:ℝ)^(h+4)*ρ^k≤((k:ℝ)^P)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hkpos P)).mpr
    have he : D*(k:ℝ)^(h+4)*ρ^k*(k:ℝ)^P=D*((k:ℝ)^(h+4+P)*ρ^k) := by rw [pow_add]; ring
    rw [he]
    exact (hN k ((le_max_left _ _).trans hk)).le
  let ε := A*(k:ℝ)^(h+2)*ρ^k*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x))
  have hε : 0≤ε := by dsimp [ε]; positivity
  have hraw : ∀ q≤h+2, ‖iteratedFDeriv ℝ q (threeCoupled threeCouplingRadius k ∘ (chartAt ThreeModel p).symm) x‖ ≤ ε := by
    intro q hq
    apply (hAJ k hk1 x hx q hq).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hkR hq) hA.le) (pow_nonneg hρ.le k)) (Real.exp_pos _).le
  have hh := hLJ _ (threeCoupled_smooth _ _) x hx ε (productFrequency k) hε
    (productFrequency_nonneg k) hraw j hj
  have hquad : (k:ℝ)≤(k:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hkpos.le]
  have hLb : L≤L*(k:ℝ)^2 := le_mul_of_one_le_right hL.le (one_le_pow₀ hkR)
  have hLam : L+productFrequency k≤(L+3)*(k:ℝ)^2 := by dsimp [productFrequency]; nlinarith
  apply hh.trans
  calc
    _ ≤ ((L+3)*(k:ℝ)^2)*ε := mul_le_mul_of_nonneg_right hLam hε
    _ = (D*(k:ℝ)^(h+4)*ρ^k)*Real.exp (productWaveFrequency k*φ ((chartAt ThreeModel p).symm x)) := by
      dsimp [D,ε]
      rw [show h+4=2+(h+2) by omega,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeCoupled_dominated_residual_rapid_decay_oai := @OAI.YauCounterexamples.threeCoupled_dominated_residual_rapid_decay_oai
