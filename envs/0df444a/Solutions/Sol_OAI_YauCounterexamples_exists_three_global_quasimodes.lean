-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_global_quasimodes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:14:17.709431+00:00
-- url     : https://prove2.me/submissions/f4914972-9a05-4792-ba98-18f51b0f8b72

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_three_chart_quasimodes_with_gaps
import Theorems.Thm_OAI_YauCounterexamples_three_exceptional_intrinsic_margin
import Theorems.Thm_OAI_YauCounterexamples_three_exterior_intrinsic_margin
import Theorems.Thm_OAI_YauCounterexamples_three_wave_background_chart_bounds

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldChartPush
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
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_apply (p : M) (f : E → V) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    manifoldChartPush p f ((chartAt E p).symm y) = f y := by
  simp only [manifoldChartPush, Set.indicator_of_mem ((chartAt E p).map_target hy),
    Function.comp_apply, (chartAt E p).right_inv hy]

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
local instance threeModelContinuousSMul'_re52fd5_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
attribute [local instance] OAI.YauCounterexamples.threeAmbientNormedSpace'
local instance threeAmbientContinuousSMul'_re52fd5_1 : ContinuousSMul ℝ ThreeAmbient := inferInstance
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
lemma productWaveFrequency_tendsto : Tendsto productWaveFrequency atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) _ _)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  exact (productWaveFrequency_bounds hk).1
end


open Set Filter Function Manifold
open scoped Topology ContDiff

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
local instance threeCoupledContinuousSMul_re52fd5_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
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

lemma three_negative_envelope_gap (p : ThreeManifold) {k : ℕ} (hk : 1≤k)
    {φ δ : ℝ} (hδ : 0≤δ) (hgap : φ≤threeGlobalLog p-δ) :
    Real.exp (productWaveFrequency k*φ) ≤
      200*(threeGlobalRadius p)^k*Real.exp (-(k:ℝ)*δ) := by
  have hc := (productWaveFrequency_scaled_bounds hk).1
  have hb := productWaveFrequency_bounds hk
  have hn := (Nat.cast_nonneg k).trans hb.1
  have hl := Real.log_nonpos (threeGlobalRadius_pos p).le (threeGlobalRadius_le_one p)
  have hlb := Real.log_le_log (show (0:ℝ)<1/200 by norm_num) (threeGlobalRadius_lower p)
  have hlog : -Real.log (threeGlobalRadius p) ≤ Real.log 200 := by
    have he : Real.log (1/200:ℝ) = -Real.log 200 := by rw [one_div,Real.log_inv]
    rw [he] at hlb
    linarith
  have hex : productWaveFrequency k*φ ≤ Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ := by
    have h1 := mul_le_mul_of_nonpos_right hc hl
    have h2 := mul_le_mul_of_nonneg_left hgap hn
    have h3 := mul_le_mul_of_nonneg_right hb.1 hδ
    dsimp [threeGlobalLog] at h2
    nlinarith
  calc
    _ ≤ Real.exp (Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ) := Real.exp_le_exp.mpr hex
    _ = _ := by
      rw [show Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p)-(k:ℝ)*δ =
        (Real.log 200+(k:ℝ)*Real.log (threeGlobalRadius p))+(-(k:ℝ)*δ) by ring,
        Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<200),←three_radius_pow_eq_exp]
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
open Set Filter Function Manifold Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace
lemma threeWeight_pos (φ : ThreeManifold → ℝ) (k : ℕ) (p : ThreeManifold) :
    0<threeWeight φ k p := add_pos_of_pos_of_nonneg (Real.exp_pos _)
      (pow_nonneg (threeGlobalRadius_pos p).le _)

end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace Matrix

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeExceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma three_global_radius_weight_bound (k : ℕ) (p : ThreeManifold) :
    threeGlobalRadius p^k≤productWeight threeCouplingRadius k p ∧
    productWeight threeCouplingRadius k p≤2*threeGlobalRadius p^k := by
  have hr : 0≤threeCouplingRadius := by norm_num [threeCouplingRadius]
  have h1 := pow_le_pow_left₀ (norm_nonneg (productA p.1)) (le_max_left ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)) k
  have h2 := pow_le_pow_left₀ (mul_nonneg hr (norm_nonneg (productB p.1))) (le_max_right ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖)) k
  rw [mul_pow] at h2
  constructor
  · dsimp [threeGlobalRadius,productWeight]
    rcases le_total ‖productA p.1‖ (threeCouplingRadius*‖productB p.1‖) with h|h
    · rw [max_eq_right h,mul_pow]; exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  · dsimp [productWeight,threeGlobalRadius] at *; linarith
lemma three_exceptional_global_coverage (φ : ThreeManifold → ℝ) {K : Set ThreeManifold}
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ y∉K, φ y≤threeGlobalLog y-δ) :
    ∀ᶠ k : ℕ in atTop, threeExceptional φ k⊆K := by
  let ρ := Real.exp (-δ)
  have hρ : 0<ρ := Real.exp_pos _
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht : Tendsto (fun k : ℕ => 12800*((k:ℝ)^6*ρ^k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_const_mul_const_pow_of_lt_one 6 hρ.le hρ1).const_mul 12800
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds zero_lt_one)] with k hk hsmall
  intro y hy
  by_contra hout
  have hν := productWaveFrequency_bounds hk
  have he := three_negative_envelope_gap y hk hδ.le (hgap _ hout)
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  have hν6 := pow_le_pow_left₀ hν0 hν.2 6
  have hpos := pow_pos (threeGlobalRadius_pos y) k
  have hb := (three_global_radius_weight_bound k y).1.trans hy
  have hh := hb.trans (mul_le_mul_of_nonneg_left he (pow_nonneg hν0 6))
  have heρ : Real.exp (-(k:ℝ)*δ)=ρ^k := by dsimp [ρ]; rw [←Real.exp_nat_mul]; congr 1; ring
  rw [heρ] at hh
  have hbig : (productWaveFrequency k)^6*(200*threeGlobalRadius y^k*ρ^k) ≤
      (12800*((k:ℝ)^6*ρ^k))*threeGlobalRadius y^k := by
    calc
      _ ≤ (2*(k:ℝ))^6*(200*threeGlobalRadius y^k*ρ^k) :=
        mul_le_mul_of_nonneg_right hν6 (by positivity)
      _ = _ := by ring
  have hbad := hh.trans hbig
  have hs := mul_lt_mul_of_pos_right hsmall hpos
  norm_num at hs
  exact (not_lt_of_ge hbad) hs

lemma three_core_exceptional {φ : ThreeManifold → ℝ} {δ : ℝ} (hδ : 0<δ)
    {F : Set ThreeManifold} (hgap : ∀ q∈F, threeGlobalLog q+δ≤φ q) :
    ∀ᶠ k : ℕ in atTop, F⊆threeExceptional φ k := by
  filter_upwards [eventually_ge_atTop (2:ℕ)] with k hk q hq
  have hk1 : 1≤k := by omega
  have hν := productWaveFrequency_bounds hk1
  have hν2 : 2≤productWaveFrequency k := by
    exact (show (2:ℝ)≤k by exact_mod_cast hk).trans hν.1
  have hν6 : 2≤productWaveFrequency k^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hν2 6
    norm_num at hh
    linarith
  have hb := (three_global_radius_weight_bound k q).2
  have he := three_positive_envelope_gap q hk1 (hgap q hq)
  have he' : Real.exp (productWaveFrequency k*(φ q-δ))≤Real.exp (productWaveFrequency k*φ q) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  change productWeight threeCouplingRadius k q≤_
  exact hb.trans ((mul_le_mul_of_nonneg_left (he.trans he') (by norm_num)).trans
    (mul_le_mul_of_nonneg_right hν6 (Real.exp_pos _).le))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeWaveLift_apply (u : NormalWaveSpace → ℝ) (y : NormalWaveSpace) :
    threeWaveLift u (threeNormalInv y)=u y := by
  dsimp [threeWaveLift,threeNormalInv]
  rw [manifoldChartPush_apply _ _ (by rw [three_chart_target]; trivial)]
  simp
attribute [local instance] OAI.YauCounterexamples.threeLiftNormedSpace
local instance threeLiftContinuousSMul_re52fd5_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeWaveLift_smooth {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threeWaveLift u) :=
  contMDiff_manifoldChartPush _ (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
theorem exists_three_global_quasimodes_oai :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric ∈ N ∧
      ∀ g ∈ N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
      ∃ Φ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ Φ ∧
        ContDiff ℝ ∞ (Φ ∘ threeNormalInv) ∧ ∃ δ>0,
        (∀ y∈closedBall 0 a, threeGlobalLog (threeNormalInv y)+δ<Φ (threeNormalInv y)) ∧
        (∀ p ∉ threeNormalInv '' closedBall 0 b, Φ p ≤ threeGlobalLog p-2*δ) ∧
        ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ closedBall 0 a ∧
        ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
          (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
        ∀ (ι : Type) [Fintype ι] (p : ι → ThreeManifold) (K : ι → Set ThreeModel),
          (∀ i, IsCompact (K i)) → ∀ m D : ℕ, ∃ C>0, ∀ᶠ k : ℕ in atTop,
          ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
            tsupport u ⊆ ball 0 ((b+R/2)/2) ∧
            (∀ q : ThreeManifold, threeWeight Φ k q/productWaveFrequency k^111  ≤
              |(threeCoupled threeCouplingRadius k+threeWaveLift u) q|+
                Real.sqrt (coordinateGradientPair g
                  (threeCoupled threeCouplingRadius k+threeWaveLift u)
                  (threeCoupled threeCouplingRadius k+threeWaveLift u) q)/productWaveFrequency k) ∧
            (∀ i, ∀ y∈K i, ∀ j  ≤  m,
              ‖iteratedFDeriv ℝ j ((threeCoupled threeCouplingRadius k+threeWaveLift u) ∘
                (chartAt ThreeModel (p i)).symm) y‖  ≤
                C*productWaveFrequency k^(j+4)*threeWeight Φ k ((chartAt ThreeModel (p i)).symm y) ∧
              ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
                (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
                  productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q) ∘
                (chartAt ThreeModel (p i)).symm) y‖  ≤
                C*productWaveFrequency k^4/productWaveFrequency k^D*
                  threeWeight Φ k ((chartAt ThreeModel (p i)).symm y)) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < SignTests.signCertificate
              (fun z : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo z.val)
              (fun z => ε/(productWaveFrequency k*ℓ z.val))
              (((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) ∘ normalWaveEquiv) ∧
            ENNReal.ofReal (A*productWaveFrequency k) < 36*Measure.hausdorffMeasure 2
              ((⋃ z : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo z.val) ∩
                {x | ((threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hproduce⟩ := exists_three_chart_quasimodes_with_gaps
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR F hF hFa hext A
  obtain ⟨Φ,hΦ,hφ,δ,hδ,hin,hout,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    hproduce g hg a b ha hab hbR A
  refine ⟨Φ,hΦ,hφ,δ,hδ,hin,hout,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro ι _ p K hK m D
  obtain ⟨C₀,hC₀,hproduce⟩ := hproduce (max m 1) D
  let C₁ := C₀*2^(max m 1+4)
  have hC₁ : 0<C₁ := by dsimp [C₁]; positivity
  have hgap : ∀ q∈F, threeGlobalLog q+δ  ≤  Φ q := by
    intro q hq
    obtain ⟨y,hy,rfl⟩ := hFa hq
    exact (hin y hy).le
  have hbound (i : ι) := three_wave_background_chart_bounds g hF hext hΦ hδ hgap
    (p i) (hK i) (R/2) m D hC₁
  choose Cs hCs hb using hbound
  let C := (1+∑ i, Cs i)*2^D
  have hsum0 : 0  ≤  ∑ i, Cs i := Finset.sum_nonneg (fun i _ => (hCs i).le)
  have hC : 0<C := by dsimp [C]; positivity
  have hCi (i : ι) : Cs i  ≤  1+∑ j, Cs j :=
    (Finset.single_le_sum (fun j _ => (hCs j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Cc,hCc,hmargin⟩ := three_exceptional_intrinsic_margin g b
  have hfreq := productWaveFrequency_tendsto.eventually (eventually_ge_atTop Cc)
  have hcover := three_exceptional_global_coverage Φ (mul_pos (by norm_num : (0:ℝ)<2) hδ) hout
  have hcore := three_core_exceptional hδ hgap
  have hexterior := three_exterior_intrinsic_margin (φ:=Φ) g (R/2) C₁ hC₁
  refine ⟨C,hC,?_⟩
  filter_upwards [hproduce,eventually_all.mpr hb,hfreq,hcover,hcore,hexterior,eventually_ge_atTop (2:ℕ)]
    with k hproduce hb hfreq hcover hcore hexterior hk
  obtain ⟨u,hu,hc,hs,hj,hjet,hscore,hnod⟩ := hproduce
  have hk1 : 1  ≤  k := by omega
  have hkR : (1:ℝ)  ≤  k := by exact_mod_cast hk1
  have hk0 : (0:ℝ)<k := zero_lt_one.trans_le hkR
  have hνb := productWaveFrequency_bounds hk1
  have hν0 : 0<productWaveFrequency k := hk0.trans_le hνb.1
  have hs' : tsupport u⊆closedBall 0 (R/2) := hs.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hj' (y : NormalWaveSpace) (j : ℕ) (hjm : j  ≤  max m 1) :
      ‖iteratedFDeriv ℝ j u y‖  ≤  C₁*(k:ℝ)^(j+4)*Real.exp (productWaveFrequency k*Φ (threeNormalInv y)) ∧
      ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+
          productFrequency k*u y) y‖  ≤  C₁*((k:ℝ)^(D+1))⁻¹*
          Real.exp (productWaveFrequency k*Φ (threeNormalInv y)) := by
    have hbd := hj y j hjm
    have hC01 : C₀  ≤  C₁ := le_mul_of_one_le_right hC₀.le (one_le_pow₀ (by norm_num))
    constructor
    · apply hbd.1.trans
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      calc
        _  ≤  C₀*(2*(k:ℝ))^(j+4) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν0.le hνb.2 _) hC₀.le
        _ = (C₀*2^(j+4))*(k:ℝ)^(j+4) := by rw [mul_pow]; ring
        _  ≤  _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)  ≤  2) (by omega)) hC₀.le)
          (pow_nonneg hk0.le _)
    · apply hbd.2.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul hC01
        (inv_anti₀ (pow_pos hk0 _) (pow_le_pow_left₀ hk0.le hνb.1 _))
        (by positivity) hC₁.le) (Real.exp_pos _).le
  have hU := (threeCoupled_smooth threeCouplingRadius k).add (threeWaveLift_smooth hu hc)
  have heq : (threeCoupled threeCouplingRadius k+threeWaveLift u) ∘ threeNormalInv=
      (threeCoupled threeCouplingRadius k ∘ threeNormalInv)+u := by
    funext y; simp only [Function.comp_apply,Pi.add_apply,threeWaveLift_apply]
  have hlow (q : ThreeManifold) : threeWeight Φ k q/productWaveFrequency k^111  ≤
      |(threeCoupled threeCouplingRadius k+threeWaveLift u) q|+
        Real.sqrt (coordinateGradientPair g
          (threeCoupled threeCouplingRadius k+threeWaveLift u)
          (threeCoupled threeCouplingRadius k+threeWaveLift u) q)/productWaveFrequency k := by
    by_cases hq : q∈threeExceptional Φ k
    · exact hmargin k hk1 hfreq Φ hcover _ hU (by simpa only [heq] using hjet) q hq
    · exact hexterior u hu hc hs' (fun y j hj1 => (hj' y j (hj1.trans (le_max_right _ _))).1)
        q hq (hext q (fun hqF => hq (hcore hqF)))
  refine ⟨u,hu,hc,hs,hlow,?_,hscore,hnod⟩
  intro i y hy j hjm
  have hbd := hb i u hu hc hs' (fun y j hjm => hj' y j (hjm.trans (le_max_left _ _))) y hy j hjm
  have hCsum : 1+∑ i, Cs i  ≤  C := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
  have hCinc : Cs i  ≤  C := (hCi i).trans hCsum
  have hW := (threeWeight_pos Φ k ((chartAt ThreeModel (p i)).symm y)).le
  constructor
  · exact hbd.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hCinc (pow_le_pow_left₀ hk0.le hνb.1 _) (by positivity) hC.le) hW)
  · apply hbd.2.trans
    apply mul_le_mul_of_nonneg_right _ hW
    apply (div_le_div_iff₀ (pow_pos hk0 D) (pow_pos hν0 D)).mpr
    have hνD : productWaveFrequency k^D  ≤  2^D*(k:ℝ)^D := by
      simpa only [mul_pow] using pow_le_pow_left₀ hν0.le hνb.2 D
    calc
      _  ≤  (Cs i*(k:ℝ)^4)*(2^D*(k:ℝ)^D) :=
        mul_le_mul_of_nonneg_left hνD (mul_nonneg (hCs i).le (by positivity))
      _ = ((Cs i*2^D)*(k:ℝ)^4)*(k:ℝ)^D := by ring
      _  ≤  (C*productWaveFrequency k^4)*(k:ℝ)^D := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hk0.le D)
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hCi i) (by positivity))
          (pow_le_pow_left₀ hk0.le hνb.1 4) (by positivity) hC.le
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_global_quasimodes_oai := @OAI.YauCounterexamples.exists_three_global_quasimodes_oai
