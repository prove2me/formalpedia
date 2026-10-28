-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_spherical_chart_quasimodes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:10:27.887257+00:00
-- url     : https://prove2.me/submissions/72f4c3c4-64e9-4acb-930f-0031353b7ca4

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_global_spherical_wave_profile
import Theorems.Thm_OAI_YauCounterexamples_exists_supported_box_nodal_quasimodes_subregions

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
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

lemma sphericalRadius_nonneg (a b : Euclidean 4) (q : Sphere 3) :
    0 ≤ sphericalRadius a b q := Real.sqrt_nonneg _

lemma sphericalRadius_sq (a b : Euclidean 4) (q : Sphere 3) :
    (sphericalRadius a b q)^2 =
      (inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma sphericalCoverage_mono (p : Sphere 3) (a b : Euclidean 4) {R S : ℝ} (h : R ≤ S) :
    sphericalCoverage p a b R ⊆ sphericalCoverage p a b S :=
  image_mono (fun _ hx => hx.trans h)

lemma sphericalCoverage_subset_open (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R S : ℝ} (hR : R < 1) (hRS : R < S) :
    sphericalCoverage p a b R ⊆
      {y | sphericalRadius a b ((chartAt (Euclidean 3) p).symm y) < S} := by
  intro y hy
  exact ((mem_sphericalCoverage_iff p a b hp hR y).mp hy).trans_lt hRS

lemma sphericalCoverage_open (p : Sphere 3) (a b : Euclidean 4) (S : ℝ) :
    IsOpen {y | sphericalRadius a b ((chartAt (Euclidean 3) p).symm y) < S} :=
  isOpen_lt ((sphericalRadius_continuous a b).comp (sphere_chart_symm_continuous p)) continuous_const


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarPredPowerWeightBound
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
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

lemma scalar_pred_power_weight_bound {r m a : ℝ} (hr : 0 ≤ r) (hm : 0 < m)
    (hma : m ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    m*r^(n-1) ≤ a^n+r^n := by
  have ha : 0 ≤ a := hm.le.trans hma
  have hn' : n-1+1=n := Nat.sub_add_cancel hn
  by_cases hmr : m ≤ r
  · calc
      _ ≤ r*r^(n-1) := mul_le_mul_of_nonneg_right hmr (pow_nonneg hr _)
      _ = r^n := by rw [←pow_succ',hn']
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg ha _)
  · calc
      _ ≤ a*a^(n-1) := mul_le_mul hma (pow_le_pow_left₀ hr ((le_of_not_ge hmr).trans hma) (n-1))
        (pow_nonneg hr _) ha
      _ = a^n := by rw [←pow_succ',hn']
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hr _)

theorem positive_wave_weight_control
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (φ : E → ℝ) (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ContDiff ℝ 1 (fun x => Real.exp ((n:ℝ)*φ x)+‖f x‖^n) ∧
      (∀ x : E, 0 < Real.exp ((n:ℝ)*φ x)+‖f x‖^n) ∧
      ∀ x ∈ K, ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)+‖f y‖^n) x‖ ≤
        C*(n:ℝ)*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨A,hAf⟩ := hK.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨B,hBp⟩ := hK.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨R,hRp⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  let D := max 1 (max A B)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hAD : A ≤ D := (le_max_left A B).trans (le_max_right _ _)
  have hBD : B ≤ D := (le_max_right A B).trans (le_max_right _ _)
  let m := Real.exp (-R)
  have hm : 0 < m := Real.exp_pos _
  refine ⟨D+D/m,by positivity,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have hfn : ContDiff ℝ 1 (fun x => ‖f x‖^n) := by
    simpa only [Real.rpow_natCast] using hf.norm_rpow hnR
  have hex : ContDiff ℝ 1 (fun x => Real.exp ((n:ℝ)*φ x)) := (contDiff_const.mul hφ).exp
  refine ⟨hex.add hfn,fun x => add_pos_of_pos_of_nonneg (Real.exp_pos _) (pow_nonneg (norm_nonneg _) _),?_⟩
  intro x hx
  let W := Real.exp ((n:ℝ)*φ x)+‖f x‖^n
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hem : m ≤ Real.exp (φ x) := by
    apply Real.exp_le_exp.mpr
    have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hRp x hx))
    simpa only [Real.norm_eq_abs] using hh
  have hpred : ‖f x‖^(n-1) ≤ W/m := by
    apply (le_div_iff₀ hm).mpr
    have hh := scalar_pred_power_weight_bound (norm_nonneg (f x)) hm hem hn1
    rw [←Real.exp_nat_mul] at hh
    simpa only [W, mul_comm] using hh
  have hnorm : ‖fderiv ℝ (fun y => ‖f y‖^n) x‖ ≤ (n:ℝ)*‖f x‖^(n-1)*D := by
    have hh := norm_fderiv_norm_rpow_le (x:=x) (hf.differentiable one_ne_zero) hnR
    have hcast : (n:ℝ)-1 = ((n-1:ℕ):ℝ) := by rw [Nat.cast_sub hn1]; norm_num
    rw [hcast,Real.rpow_natCast] at hh
    simp only [Real.rpow_natCast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ((hAf x hx).trans hAD) (by positivity))
  have he : HasFDerivAt (fun y => Real.exp ((n:ℝ)*φ y))
      (Real.exp ((n:ℝ)*φ x) • ((n:ℝ) • fderiv ℝ φ x)) x :=
    (((hφ.differentiable one_ne_zero x).hasFDerivAt).const_mul (n:ℝ)).exp
  have heNorm : ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)) x‖ ≤
      (n:ℝ)*D*Real.exp ((n:ℝ)*φ x) := by
    rw [he.fderiv]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
    calc
      _ ≤ Real.exp ((n:ℝ)*φ x)*((n:ℝ)*D) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((hBp x hx).trans hBD) (Nat.cast_nonneg _)) (Real.exp_pos _).le
      _ = _ := by ring
  change ‖fderiv ℝ ((fun y => Real.exp ((n:ℝ)*φ y)) + (fun y => ‖f y‖^n)) x‖ ≤ _
  rw [fderiv_add (hex.differentiable one_ne_zero x) (hfn.differentiable one_ne_zero x)]
  calc
    _ ≤ ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)) x‖ +
      ‖fderiv ℝ (fun y => ‖f y‖^n) x‖ := norm_add_le _ _
    _ ≤ (n:ℝ)*D*Real.exp ((n:ℝ)*φ x)+(n:ℝ)*‖f x‖^(n-1)*D := add_le_add heNorm hnorm
    _ ≤ (n:ℝ)*D*W+(n:ℝ)*(W/m)*D := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)) (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpred (Nat.cast_nonneg _)) hD.le)
    _ = _ := by dsimp [W]; field_simp

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SourceSignBox
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

lemma sourceSignBox_band (y : NormalWaveSpace)
    (hy : y ∈ normalWaveEquiv '' Box.Icc sourceSignBox) :
    (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) ∧
    sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < 1/8 :=
  Classical.choose_spec exists_spherical_sign_box y hy

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactExteriorBackgroundDomination
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
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
namespace YauCounterexamples

theorem compact_exterior_background_domination {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {r φ : X → ℝ}
    (hr : ContinuousOn r K) (hφ : ContinuousOn φ K)
    (hrpos : ∀ x ∈ K, 0 < r x) (hgap : ∀ x ∈ K, φ x < Real.log (r x)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, (n:ℝ)^k*Real.exp ((n:ℝ)*φ x) < (r x)^n := by
  classical
  by_cases hne : K.Nonempty
  · let f := fun x => Real.exp (φ x)/r x
    have hf : ContinuousOn f K := hφ.rexp.div hr (fun x hx => (hrpos x hx).ne')
    obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne hf
    have hfz : 0 < f z := div_pos (Real.exp_pos _) (hrpos z hz)
    have hlt : f z < 1 := by
      apply (div_lt_one (hrpos z hz)).mpr
      rw [←Real.exp_log (hrpos z hz)]
      exact Real.exp_lt_exp.mpr (hgap z hz)
    have ht := tendsto_pow_const_mul_const_pow_of_lt_one k hfz.le hlt
    filter_upwards [ht.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    intro x hx
    have hfx : Real.exp (φ x) ≤ f z*r x := (div_le_iff₀ (hrpos x hx)).mp (hm hx)
    have hp := pow_le_pow_left₀ (Real.exp_pos (φ x)).le hfx n
    rw [←Real.exp_nat_mul,mul_pow] at hp
    calc
      _ ≤ (n:ℝ)^k*((f z)^n*(r x)^n) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((n:ℝ)^k*(f z)^n)*(r x)^n := by ring
      _ < 1*(r x)^n := mul_lt_mul_of_pos_right hn (pow_pos (hrpos x hx) n)
      _ = _ := one_mul _
  · exact Filter.Eventually.of_forall (fun n x hx => (hne ⟨x,hx⟩).elim)
end YauCounterexamples

end

end OAI
end

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Function Manifold BoxIntegral Metric
open scoped Topology ContDiff

lemma sphericalRadius_eq_planar_norm (a b : Euclidean 4) (q : Sphere 3) :
    sphericalRadius a b q = ‖planarLinear a b q‖ := by
  have hh := Complex.sq_norm (planarLinear a b q)
  simp only [planarLinear_apply,Complex.normSq_apply,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    zero_mul,sub_zero,add_zero,Complex.add_im,Complex.mul_im,zero_add] at hh
  have hs := sphericalRadius_sq a b q
  apply (sq_eq_sq₀ (sphericalRadius_nonneg a b q) (norm_nonneg _)).mp
  rw [hs]
  change _ = ‖(⟪a,(q : Euclidean 4)⟫_ℝ : ℂ)+Complex.I*⟪b,(q : Euclidean 4)⟫_ℝ‖^2
  nlinarith only [hh]

lemma spherical_chart_pullback_smooth {φ : Sphere 3 → ℝ}
    (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ) (p : Sphere 3) :
    ContDiff ℝ ∞ (φ ∘ (chartAt (Euclidean 3) p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hφ p (by rw [sphere_chart_target]; trivial)

lemma roundPlanarChart_contDiff (a b : Euclidean 4) (p : Sphere 3) :
    ContDiff ℝ ∞ (roundPlanarChart a b p) :=
  contDiffOn_univ.mp (by simpa only [sphere_chart_target] using roundPlanarChart_smooth a b p)

lemma sphericalChartWeight_lower (φ : Sphere 3 → ℝ) (n : ℕ) (y : Fin 3 → ℝ) :
    Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y))) ≤
      sphericalChartWeight φ n y := le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)

lemma sphericalChartWeight_upper (φ : Sphere 3 → ℝ) (n : ℕ) (y : Fin 3 → ℝ)
    (hy : y ∈ sphericalExceptionalInChart φ n) :
    sphericalChartWeight φ n y ≤ (1+(n:ℝ)^6)*
      Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y))) := by
  dsimp [sphericalExceptionalInChart] at hy
  dsimp [sphericalChartWeight]
  nlinarith

theorem spherical_background_input_bounds {φ : Sphere 3 → ℝ}
    (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ)
    {S : Set (Fin 3 → ℝ)} (hS : IsCompact S) :
    ∃ T₀ > 0, ∃ H > 0, ∀ n : ℕ, 2 ≤ n →
      Differentiable ℝ (sphericalChartWeight φ n) ∧
      (∀ y, 0 < sphericalChartWeight φ n y) ∧
      (∀ y ∈ S, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) y‖ ≤
          T₀*(n:ℝ)^j*sphericalChartWeight φ n y) ∧
      (∀ y ∈ S, ‖fderiv ℝ (sphericalChartWeight φ n) y‖ ≤ H*(n:ℝ)*sphericalChartWeight φ n y) := by
  let f := roundPlanarChart sourceAxisOne sourceAxisTwo sourcePole ∘ normalWaveEquiv
  let ψ := (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv
  have hf : ContDiff ℝ ∞ f :=
    (roundPlanarChart_contDiff sourceAxisOne sourceAxisTwo sourcePole).comp normalWaveEquiv.contDiff
  have hψ : ContDiff ℝ ∞ ψ := (spherical_chart_pullback_smooth hφ sourcePole).comp normalWaveEquiv.contDiff
  obtain ⟨T,hT,hTbound⟩ := real_power_weighted_jets hf hS ψ hψ.continuous.continuousOn 2
  obtain ⟨H,hH,hHb⟩ := positive_wave_weight_control f ψ (hf.of_le (by simp)) (hψ.of_le (by simp)) hS
  refine ⟨T,hT,H,hH,?_⟩
  intro n hn
  obtain ⟨hW,hW0,hWD⟩ := hHb n hn
  exact ⟨hW.differentiable one_ne_zero,hW0,fun y hy j hj => hTbound n y hy j hj,hWD⟩

theorem spherical_exceptional_eventually_coverage {φ : Sphere 3 → ℝ}
    (hφ : Continuous φ) {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s < 1)
    (hgap : ∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
      φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) :
    ∀ᶠ n : ℕ in atTop, sphericalExceptionalInChart φ n ⊆ normalWaveEquiv.symm ''
      sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo s := by
  let K : Set (Sphere 3) := {q | s ≤ sphericalRadius sourceAxisOne sourceAxisTwo q}
  have hK : IsCompact K := (isClosed_le continuous_const (sphericalRadius_continuous _ _)).isCompact
  have hd := compact_exterior_background_domination hK
    (sphericalRadius_continuous sourceAxisOne sourceAxisTwo).continuousOn hφ.continuousOn
    (fun q hq => ht.trans_le (hts.le.trans hq))
    (fun q hq => hgap q (hts.trans_le hq)) 6
  filter_upwards [hd] with n hn
  intro y hy
  refine ⟨normalWaveEquiv y,?_,normalWaveEquiv.symm_apply_apply y⟩
  apply (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole hs _).mpr
  by_contra hm
  have hrad : s ≤ sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)) := (lt_of_not_ge hm).le
  have hh := hn _ hrad
  rw [sphericalRadius_eq_planar_norm] at hh
  exact (not_lt_of_ge hy) hh

lemma roundPower_abs_le_radius_pow (a b : Euclidean 4) (n : ℕ) (q : Sphere 3) :
    |roundPower a b n q| ≤ (sphericalRadius a b q)^n := by
  rw [sphericalRadius_eq_planar_norm,←norm_pow]
  exact Complex.abs_re_le_norm _

theorem spherical_background_sign_small {φ : Sphere 3 → ℝ} (hφ : Continuous φ)
    (I : Box (Fin 3)) {t : ℝ}
    (hI : ∀ y ∈ normalWaveEquiv '' Box.Icc I,
      sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) sourcePole).symm y) < t)
    (hgap : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ y ∈ normalWaveEquiv '' Box.Icc I,
      |roundPower sourceAxisOne sourceAxisTwo n ((chartAt (Euclidean 3) sourcePole).symm y)| ≤
        c*Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y)) := by
  let K := normalWaveEquiv '' Box.Icc I
  have hK : IsCompact K := I.isCompact_Icc.image normalWaveEquiv.continuous
  let r := sphericalRadius sourceAxisOne sourceAxisTwo ∘ (chartAt (Euclidean 3) sourcePole).symm
  let ψ := φ ∘ (chartAt (Euclidean 3) sourcePole).symm
  have hr : Continuous r := (sphericalRadius_continuous _ _).comp (sphere_chart_symm_continuous _)
  have hψ : Continuous ψ := hφ.comp (sphere_chart_symm_continuous _)
  obtain ⟨ρ,hρ,hρ1,hdom⟩ := compact_strict_profile_ratio hK hr.continuousOn hψ.continuousOn
    (fun y _ => sphericalRadius_nonneg _ _ _) (fun y hy hn => hgap _
      (lt_of_le_of_ne (sphericalRadius_nonneg _ _ _) (Ne.symm hn)) (hI y hy))
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1
  filter_upwards [htend.eventually (Iio_mem_nhds hc)] with n hn
  intro y hy
  calc
    _ ≤ r y^n := roundPower_abs_le_radius_pow _ _ _ _
    _ ≤ (ρ*Real.exp (ψ y))^n := pow_le_pow_left₀ (sphericalRadius_nonneg _ _ _) (hdom y hy) n
    _ = ρ^n*Real.exp ((n:ℝ)*ψ y) := by rw [mul_pow,←Real.exp_nat_mul]
    _ ≤ c*Real.exp ((n:ℝ)*ψ y) := mul_le_mul_of_nonneg_right hn.le (Real.exp_pos _).le


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
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_ExistsSphericalGlobalQuasimodes
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
open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_spherical_chart_quasimodes_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    (A : ℝ) :
    ∃ φ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ ∧
      (∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
        sphericalRadius sourceAxisOne sourceAxisTwo q < t →
        Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q) ∧
      (∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
        φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) ∧
      ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
        (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
      ∀ m D : ℕ, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
            ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*(n:ℝ)^(j+4)*
              Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x)) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (sphereChartMetric g sourcePole) u y+
                (n:ℝ)*(n+2)*u y) x‖ ≤ C*((n:ℝ)^(D+1))⁻¹*
              Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm x))) ∧
          (∀ y ∈ sphericalExceptionalInChart φ n,
            1/(n:ℝ)^110 ≤ ‖realWaveJet n (sphericalChartWeight φ n y)
              (((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
            (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
            (fun a => ε/((n:ℝ)*ℓ a.val))
            (((roundPower sourceAxisOne sourceAxisTwo n ∘
              (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal (A*(n:ℝ)) < 36*Measure.hausdorffMeasure 2
            ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩
              {x | ((roundPower sourceAxisOne sourceAxisTwo n ∘
                (chartAt (Euclidean 3) sourcePole).symm)+u) (normalWaveEquiv x)=0}) := by
  let G := sphereChartMetric g sourcePole
  let K := sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo s
  let O := {y | sphericalRadius sourceAxisOne sourceAxisTwo
    ((chartAt (Euclidean 3) sourcePole).symm y) < r}
  have hs : s < 1 := by linarith
  have hK : IsCompact K := sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole hs
  have hO : IsOpen O := sphericalCoverage_open sourcePole sourceAxisOne sourceAxisTwo r
  have hKO : K ⊆ O := sphericalCoverage_subset_open sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole hs hsr
  obtain ⟨ε,hε,hε1,p₀,hp₀,hproduce⟩ :=
    exists_supported_box_nodal_quasimodes_subregions G hK hO hKO
  let a := p₀/(16*ε)
  have ha : 0 < a := div_pos hp₀ (mul_pos (by norm_num) hε)
  obtain ⟨φ,hφ,hsp,hclose,hin,hout,hnc,hcrit,hinside,hmass⟩ :=
    exists_global_spherical_wave_profile g₀ hg₀ g hg t ⟨ht,by linarith⟩ (A/a) zero_lt_one
  let ψ := φ ∘ (chartAt (Euclidean 3) sourcePole).symm
  have hψ : ContDiff ℝ ∞ ψ := spherical_chart_pullback_smooth hφ sourcePole
  have hKP : K ⊆ sourceProfileCoverage := sphericalCoverage_mono sourcePole sourceAxisOne sourceAxisTwo
    (by linarith)
  have hIK : normalWaveEquiv '' Box.Icc sourceSignBox ⊆ K := by
    intro y hy
    apply (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole hs y).mpr
    exact ((sourceSignBox_band y hy).2).le.trans (by linarith)
  obtain ⟨partition,hπ,ℓ,hℓ,hproduce⟩ := hproduce ψ hψ (fun x hx => hnc x (hKP hx))
    (fun x hx => hcrit x (hKP hx)) sourceSignBox hIK
  have hmass' : A < a*(∫ x in Box.Icc sourceSignBox, profileFrequencyScale G ψ (normalWaveEquiv x)) :=
    (div_lt_iff₀ ha).mp hmass |>.trans_eq (mul_comm _ _)
  have hK' : IsCompact (normalWaveEquiv.symm '' K) := hK.image normalWaveEquiv.symm.continuous
  obtain ⟨R,hR⟩ := hK'.isBounded.subset_closedBall (0 : Fin 3 → ℝ)
  let S := closedBall (0 : Fin 3 → ℝ) R
  obtain ⟨T₀,hT₀,H,hH,hinputs⟩ := spherical_background_input_bounds hφ (isCompact_closedBall (0 : Fin 3 → ℝ) R)
  refine ⟨φ,hφ,hin,hout,partition,hπ,ℓ,hℓ,ε,hε,?_⟩
  intro m D
  obtain ⟨c₀,hc₀,C,hC,N,hN,hproduce⟩ := hproduce m D T₀ H hT₀.le hH.le
  refine ⟨C,hC,?_⟩
  have hfreq : ∀ᶠ n : ℕ in atTop, N ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually (eventually_ge_atTop N)
  have hsign := spherical_background_sign_small hφ.continuous sourceSignBox
    (fun y hy => (sourceSignBox_band y hy).2.trans (by linarith)) hin hc₀
  have hexcept := spherical_exceptional_eventually_coverage hφ.continuous
    (show 0 < t by linarith) hts hs hout
  filter_upwards [hfreq,eventually_ge_atTop (2:ℕ),hsign,hexcept] with n hn hn2 hsign hexcept
  obtain ⟨hW,hW0,hwjet,hlog⟩ := hinputs n hn2
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ := hproduce n hn S (convex_closedBall _ _)
    (sphericalExceptionalInChart φ n) (hexcept.trans hR) hexcept
    (roundPower sourceAxisOne sourceAxisTwo n ∘ (chartAt (Euclidean 3) sourcePole).symm)
    (spherical_chart_pullback_smooth (roundPower_smooth sourceAxisOne sourceAxisTwo n) sourcePole)
    (sphericalChartWeight φ n) hW hW0 (fun y _ => sphericalChartWeight_lower φ n y)
    (fun y hy => sphericalChartWeight_upper φ n y hy) hwjet hlog hsign
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le (hN.trans hn)
  have hle : A*(n:ℝ) ≤ a*(n:ℝ)*(∫ x in Box.Icc sourceSignBox,
      profileFrequencyScale G ψ (normalWaveEquiv x)) := by nlinarith [mul_pos (sub_pos.mpr hmass') hn0]
  exact ⟨u,hu,huc,hus,hder,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩


end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_spherical_chart_quasimodes_oai := @OAI.YauCounterexamples.exists_spherical_chart_quasimodes_oai
