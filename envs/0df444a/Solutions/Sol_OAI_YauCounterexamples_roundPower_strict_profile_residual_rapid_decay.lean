-- Prove2me | solution 1 for OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:41:51.590933+00:00
-- url     : https://prove2.me/submissions/133a6a92-f5c3-4af2-af1c-5fc845e9c85d

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactStrictProfileRatio
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open Set Filter
namespace YauCounterexamples
lemma compact_strict_profile_ratio {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {r φ : X → ℝ}
    (hr : ContinuousOn r K) (hφ : ContinuousOn φ K)
    (hr0 : ∀ y ∈ K, 0 ≤ r y)
    (hgap : ∀ y ∈ K, r y ≠ 0 → Real.log (r y) < φ y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ y ∈ K, r y ≤ ρ*Real.exp (φ y) := by
  classical
  by_cases hne : K.Nonempty
  · let f := fun y => r y / Real.exp (φ y)
    have hf : ContinuousOn f K := hr.div hφ.rexp (fun y _ => (Real.exp_pos _).ne')
    obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne hf
    have hlt : f z < 1 := by
      dsimp [f]
      apply (div_lt_one (Real.exp_pos _)).mpr
      by_cases hz0 : r z=0
      · rw [hz0]; exact Real.exp_pos _
      · have hrpos : 0 < r z := lt_of_le_of_ne (hr0 z hz) (Ne.symm hz0)
        rw [←Real.exp_log hrpos]
        exact Real.exp_lt_exp.mpr (hgap z hz hz0)
    have hnonneg : 0 ≤ f z := div_nonneg (hr0 z hz) (Real.exp_pos _).le
    refine ⟨(f z+1)/2,by linarith,by linarith,?_⟩
    intro y hy
    apply (div_le_iff₀ (Real.exp_pos (φ y))).mp
    have hh : f y ≤ f z := hm hy
    change f y ≤ _
    linarith
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro y hy
    exact (hne ⟨y,hy⟩).elim

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPlanarChart_smooth (a b : Euclidean (d+1)) (p : Sphere d) :
    ContDiffOn ℝ ∞ (roundPlanarChart a b p) (chartAt (Euclidean d) p).target := by
  have hs : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℂ) ∞
      (fun q : Sphere d => planarLinear a b (q : Euclidean (d+1))) :=
    (planarLinear a b).contDiff.contMDiff.comp contMDiff_coe_sphere
  intro y hy
  exact (contMDiffAt_iff_contDiffAt.mp (hs.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))).contDiffWithinAt

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


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
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_smooth (a b : Euclidean (d+1)) (k : ℕ) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (roundPower a b k) := by
  have hc : ContDiff ℝ ∞ (fun x : Euclidean (d+1) => (planarLinear a b x)^k) :=
    (planarLinear a b).contDiff.pow k
  exact (Complex.reCLM.contDiff.comp hc).contMDiff.comp contMDiff_coe_sphere


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_RoundPowerWeightedChartJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open scoped Topology ContDiff Manifold InnerProductSpace
section EnvelopePowers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_power_envelope_jet_bound_on [FiniteDimensional ℝ E]
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f O) (h n : ℕ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hxO hf
  have hh := complex_power_envelope_jet_bound hF x h n hA hC (fun j hj => by
    rw [←(he.iteratedFDeriv ℝ j).self_of_nhds]
    exact hfj j hj)
  intro j hj
  have heRe : (fun y => (f y^n).re) =ᶠ[𝓝 x] (fun y => (F y^n).re) :=
    he.mono (fun y hy => congrArg (fun z : ℂ => (z^n).re) hy)
  rw [(heRe.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => F y^n) x‖ :=
      ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
        (hF.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
    _ ≤ 1*(A^n*((n:ℝ)*C)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
      (hh j hj) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end EnvelopePowers

variable {d : ℕ}

theorem roundPower_dominated_chart_jets
    (a b : Euclidean (d+1)) (p : Sphere d) {K : Set (Euclidean d)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (φ : Euclidean d → ℝ) (hφ : ContinuousOn φ K) (h : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : ∀ y ∈ K, ‖roundPlanarChart a b p y‖ ≤ ρ*Real.exp (φ y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        C*(n:ℝ)^j*ρ^n*Real.exp ((n:ℝ)*φ y) := by
  have hf := roundPlanarChart_smooth a b p
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound (chartAt (Euclidean d) p).open_target hK hKO hf h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := ρ*Real.exp (-B)
  have hr : 0 < r := mul_pos hρ (Real.exp_pos _)
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n y hy j hj
  have hry : r ≤ ρ*Real.exp (φ y) := by
    have hlow : -B ≤ φ y := by
      have hh := (neg_abs_le (φ y)).trans' (neg_le_neg (hB y hy))
      simpa only [Real.norm_eq_abs] using hh
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlow) hρ.le
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k (roundPlanarChart a b p) y‖ ≤
      (ρ*Real.exp (φ y))*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hdom y hy
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk y hy
        _ = r*(D/r) := by field_simp
        _ ≤ (ρ*Real.exp (φ y))*T^k := mul_le_mul hry ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) (by positivity)
  have hp := real_power_envelope_jet_bound_on (chartAt (Euclidean d) p).open_target
    (hKO hy) hf h n (by positivity : 0 ≤ ρ*Real.exp (φ y)) hT0 hraw j hj
  have he : (ρ*Real.exp (φ y))^n*((n:ℝ)*T)^j =
      T^j*(n:ℝ)^j*ρ^n*Real.exp ((n:ℝ)*φ y) := by
    rw [mul_pow,mul_pow,Real.exp_nat_mul]
    ring
  rw [he] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg hρ.le _)) (Real.exp_pos _).le)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RoundPowerDominatedResidualRapid
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
namespace YauCounterexamples

theorem roundPower_dominated_residual_rapid_decay
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b : Euclidean (3+1)) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hdom : ∀ y ∈ K, ‖roundPlanarChart a b p y‖ ≤ ρ*Real.exp (φ y)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  obtain ⟨A,hA,hAj⟩ := roundPower_dominated_chart_jets a b p hK hKO φ hφ (h+2) hρ hdom
  obtain ⟨L,hL,hLj⟩ := laplaceBeltrami_residual_small_jets_on_compact g p hK hKO h
  let D := (L+3)*A
  have hD : 0 < D := by dsimp [D]; positivity
  have ht : Tendsto (fun n : ℕ => D*((n:ℝ)^(h+4+P)*ρ^n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (h+4+P) hρ.le hρ1).const_mul D
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn y hy j hj
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n:ℝ) := zero_lt_one.trans_le hnR
  have hsmall : D*(n:ℝ)^(h+4)*ρ^n ≤ ((n:ℝ)^P)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos hnpos P)).mpr
    have he : D*(n:ℝ)^(h+4)*ρ^n*(n:ℝ)^P = D*((n:ℝ)^(h+4+P)*ρ^n) := by
      rw [pow_add]; ring
    rw [he]
    exact (hN n ((le_max_left _ _).trans hn)).le
  let ε := A*(n:ℝ)^(h+2)*ρ^n*Real.exp ((n:ℝ)*φ y)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hraw : ∀ k ≤ h+2,
      ‖iteratedFDeriv ℝ k (roundPower a b n ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤ ε := by
    intro k hk
    apply (hAj n y hy k hk).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hk) hA.le)
        (pow_nonneg hρ.le n)) (Real.exp_pos _).le
  have hjb := hLj (roundPower a b n) (roundPower_smooth a b n) y hy ε
    ((n:ℝ)*((n:ℝ)+2)) hε (by positivity) hraw j hj
  have hquad : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hnpos.le]
  have hLbound : L ≤ L*(n:ℝ)^2 := le_mul_of_one_le_right hL.le (one_le_pow₀ hnR)
  have hLam : L+(n:ℝ)*((n:ℝ)+2) ≤ (L+3)*(n:ℝ)^2 := by nlinarith
  apply hjb.trans
  calc
    _ ≤ ((L+3)*(n:ℝ)^2)*ε := mul_le_mul_of_nonneg_right hLam hε
    _ = (D*(n:ℝ)^(h+4)*ρ^n)*Real.exp ((n:ℝ)*φ y) := by
      dsimp [D,ε]
      rw [show h+4 = 2+(h+2) by omega,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundPowerGlobalProfileResidual
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace

theorem roundPower_strict_profile_residual_rapid_decay_oai
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b : Euclidean (3+1)) (p : Sphere 3) {K : Set (Euclidean 3)}
    (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean 3) p).target)
    (φ : Euclidean 3 → ℝ) (hφ : ContinuousOn φ K) (h P : ℕ)
    (hgap : ∀ y ∈ K, roundPlanarChart a b p y ≠ 0 →
      Real.log ‖roundPlanarChart a b p y‖ < φ y) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g (roundPower a b n) z +
          (n:ℝ)*((n:ℝ)+2)*roundPower a b n z) ∘ (chartAt (Euclidean 3) p).symm) y‖ ≤
        ((n:ℝ)^P)⁻¹*Real.exp ((n:ℝ)*φ y) := by
  have hr := (roundPlanarChart_smooth a b p).continuousOn.norm.mono hKO
  obtain ⟨ρ,hρ,hρ1,hrho⟩ := compact_strict_profile_ratio hK hr hφ
    (fun y _ => norm_nonneg _) (fun y hy hny => hgap y hy (norm_ne_zero_iff.mp hny))
  exact roundPower_dominated_residual_rapid_decay g a b p hK hKO φ hφ h P hρ hρ1 hrho

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
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay_oai := @OAI.YauCounterexamples.roundPower_strict_profile_residual_rapid_decay_oai
