-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:16:32.486231+00:00
-- url     : https://prove2.me/submissions/fc1fdc71-7faa-4775-bab5-8be8f3351f00

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A007

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
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
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

lemma localGradientPair_eq_global {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localGradientPair g u u p y = coordinateGradientPair g u u ((chartAt E p).symm y) := by
  rw [coordinateGradientPair_inChart hu hu g p ((chartAt E p).symm y) ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartGradientProjectionSmooth
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

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CutoffExactificationSmoothNeighborhood
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CutoffFactorCompactRaw
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
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chart_inverse_differential_bound (g : SmoothMetric E M) (p : M) (y : E)
    (L : E →L[ℝ] ℝ) :
    (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j*L (Module.finBasis ℝ E i)*L (Module.finBasis ℝ E j)) ≤
      chartInverseDifferentialBound g p y*‖L‖^2 := by
  unfold chartInverseDifferentialBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hi : |L (Module.finBasis ℝ E i)| ≤ ‖L‖*‖Module.finBasis ℝ E i‖ := L.le_opNorm _
  have hj : |L (Module.finBasis ℝ E j)| ≤ ‖L‖*‖Module.finBasis ℝ E j‖ := L.le_opNorm _
  calc
    _ ≤ |(metricCoefficients g p y)⁻¹ i j*L (Module.finBasis ℝ E i)*L (Module.finBasis ℝ E j)| :=
      le_abs_self _
    _ = |(metricCoefficients g p y)⁻¹ i j| *|L (Module.finBasis ℝ E i)| *|L (Module.finBasis ℝ E j)| := by
      rw [abs_mul,abs_mul]
    _ ≤ |(metricCoefficients g p y)⁻¹ i j| *(‖L‖*‖Module.finBasis ℝ E i‖)*
        (‖L‖*‖Module.finBasis ℝ E j‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg _)) hj
        (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

lemma chartInverseDifferentialBound_continuous (g : SmoothMetric E M) (p : M) :
    ContinuousOn (chartInverseDifferentialBound g p) (chartAt E p).target := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (((contDiffOn_metricInverse g p i j).continuousOn.abs).mul continuousOn_const).mul continuousOn_const

theorem compact_chart_intrinsic_gradient_bound (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) :
    ∃ C > 0, ∀ (U : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ∀ y ∈ K,
      Real.sqrt (coordinateGradientPair g U U ((chartAt E p).symm y)) ≤
        C*‖fderiv ℝ (U ∘ (chartAt E p).symm) y‖ := by
  obtain ⟨T,hT⟩ := hK.exists_bound_of_continuousOn
    ((chartInverseDifferentialBound_continuous g p).mono hKt)
  let C := Real.sqrt (max 1 T)
  have hC : 0 < C := Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro U hU y hy
  have hbound := chart_inverse_differential_bound g p y (fderiv ℝ (U ∘ (chartAt E p).symm) y)
  have hG : coordinateGradientPair g U U ((chartAt E p).symm y) ≤
      chartInverseDifferentialBound g p y*‖fderiv ℝ (U ∘ (chartAt E p).symm) y‖^2 := by
    rw [←localGradientPair_eq_global hU g p (hKt hy)]
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    simp only [localGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTb : chartInverseDifferentialBound g p y ≤ max 1 T :=
    (le_abs_self _).trans ((hT y hy).trans (le_max_right _ _))
  have hG' := hG.trans (mul_le_mul_of_nonneg_right hTb (sq_nonneg _))
  have hG0 := coordinateGradientPair_nonneg g U ((chartAt E p).symm y)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mp
  have hCsq : (C:ℝ)^2 = max 1 T := Real.sq_sqrt (zero_le_one.trans (le_max_left _ _))
  rw [Real.sq_sqrt hG0,mul_pow,hCsq]
  exact hG'

end



open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
theorem cutoffFactor_compact_raw (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (m : ℕ) :
    ∃ C > 0, ∀ (v : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      ∀ y ∈ K, ∀ ε : ℝ, 0 ≤ ε →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E p).symm) y‖ ≤ ε) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j
        ((fun x => cutoffFactor χ v x-1) ∘ (chartAt E p).symm) y‖ ≤ C*ε := by
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hχ' : ContDiffOn ℝ ∞ (χ ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hχ p hy).contDiffWithinAt
  obtain ⟨A,hA,hAj⟩ := compact_raw_jet_bound hO hK hKt hχ' m
  refine ⟨2^m*A,by positivity,?_⟩
  intro v hv y hy ε hε hvJ j hj
  have hv' : ContDiffOn ℝ ∞ ((fun x => v x-1) ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart (hv.sub contMDiff_const) p hy).contDiffWithinAt
  have hp := constant_product_jet_bound_on hO (hKt hy) hχ' hv' m
    (zero_le_one.trans hA) hε (fun k hk => hAj k hk y hy) hvJ j hj
  simpa only [Function.comp_def,cutoffFactor,add_sub_cancel_left] using hp

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma coveringRawTest_mem (i₀ : CoordIndex E) (i : A.t) :
    A.coveringRawTest i₀ i ∈ A.coveringRawTests i₀ := by
  classical
  exact List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩

omit [T2Space M] in
lemma coveringRawTests_cover (i₀ : CoordIndex E) (x : M) :
    ∃ t ∈ A.coveringRawTests i₀, ∃ y ∈ t.compactSet, (chartAt E t.center).symm y=x := by
  classical
  have hex : ∃ i : A.t, A.η i x ≠ 0 := by
    by_contra h
    push Not at h
    have hh := A.sum_η x
    simp only [h,Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  obtain ⟨i,hi⟩ := hex
  have hx : x ∈ tsupport (A.η i) := subset_tsupport _ hi
  refine ⟨A.coveringRawTest i₀ i,A.coveringRawTest_mem i₀ i,
    chartAt E (A.p i) x,⟨x,hx,rfl⟩,?_⟩
  exact (chartAt E (A.p i)).left_inv (A.chart_η i hx)

omit [T2Space M] in
theorem global_cutoff_raw_controls_oai (i₀ : CoordIndex E) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
    ∃ C > 0, ∀ (b v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
      (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
      ∀ x : M,
        |weightedLaplacian g b (cutoffFactor χ v) x| ≤ C*ε ∧
        Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x) ≤ C*ε := by
  classical
  choose D hD hDj using fun t : CoordinateTest E M =>
    cutoffFactor_compact_raw χ hχ t.center t.isCompact t.inTarget 2
  choose L hL hLj using fun t : CoordinateTest E M =>
    weightedLaplacian_small_jets_on_compact g t.center t.isCompact t.inTarget 0
  choose G hG hGj using fun t : CoordinateTest E M =>
    compact_chart_intrinsic_gradient_bound g t.center t.isCompact t.inTarget
  let cs (t : CoordinateTest E M) := L t*2*D t+G t*D t
  let C := 1+∑ t ∈ (A.coveringRawTests i₀).toFinset, cs t
  have hcs (t : CoordinateTest E M) : 0 ≤ cs t := by dsimp [cs]; exact add_nonneg (mul_nonneg (mul_nonneg (hL t).le (by norm_num)) (hD t).le) (mul_nonneg (hG t).le (hD t).le)
  have hC : 0 < C := by
    have hsum := Finset.sum_nonneg (fun t (_ : t ∈ (A.coveringRawTests i₀).toFinset) => hcs t)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcsC (t : CoordinateTest E M) (ht : t ∈ A.coveringRawTests i₀) : cs t ≤ C := by
    have hh := Finset.single_le_sum (fun t (_ : t ∈ (A.coveringRawTests i₀).toFinset) => hcs t)
      (List.mem_toFinset.mpr ht)
    dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro b v hb hv ε hε hε1 hbJ hvJ x
  obtain ⟨t,ht,y,hy,hxy⟩ := A.coveringRawTests_cover i₀ x
  let w := cutoffFactor χ v
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hwJ := hDj t v hv y hy ε hε (hvJ t ht y hy)
  have hb' : ContDiffOn ℝ ∞ (b ∘ (chartAt E t.center).symm) (chartAt E t.center).target :=
    fun z hz => (contDiffAt_inChart hb t.center hz).contDiffWithinAt
  have hbraw := raw_jets_of_near_one (chartAt E t.center).open_target
    (t.inTarget hy) hb' 1 hε (hbJ t ht y hy)
  have hb2 : ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (b ∘ (chartAt E t.center).symm) y‖ ≤ (2:ℝ) := by
    intro j hj
    exact (hbraw j hj).trans (by linarith)
  have hlap := hLj t b w hb hw y hy 2 (D t*ε) (by norm_num) (mul_nonneg (hD t).le hε)
    hb2 hwJ 0 (by omega)
  simp only [norm_iteratedFDeriv_zero,Function.comp_apply,hxy,Real.norm_eq_abs] at hlap
  have hgrad := hGj t w hw y hy
  have hfd : ‖fderiv ℝ (w ∘ (chartAt E t.center).symm) y‖ ≤ D t*ε := by
    have hh := hwJ 1 (by omega)
    simpa only [norm_iteratedFDeriv_one,Function.comp_def,fderiv_sub_const] using hh
  rw [hxy] at hgrad
  constructor
  · calc
      _ ≤ L t*2*(D t*ε) := hlap
      _ = (L t*2*D t)*ε := by ring
      _ ≤ C*ε := mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right (mul_nonneg (hG t).le (hD t).le)).trans (hcsC t ht)) hε
  · calc
      _ ≤ G t*(D t*ε) := hgrad.trans (mul_le_mul_of_nonneg_left hfd (hG t).le)
      _ = (G t*D t)*ε := by ring
      _ ≤ C*ε := mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_left (mul_nonneg (mul_nonneg (hL t).le (by norm_num)) (hD t).le)).trans (hcsC t ht)) hε
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.global_cutoff_raw_controls_oai.{u_1, u_2}
