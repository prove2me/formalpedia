-- Prove2me | solution 1 for OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:07:40.725913+00:00
-- url     : https://prove2.me/submissions/ba7b834e-3160-4563-9db4-a5b829fab2bb

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_contraction_weighted
import Theorems.Thm_OAI_WeakHessian_RCD_test_gradientSquare_sobolev

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SlopeApproxAntitone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set
open scoped NNReal


namespace WeakHessian
variable {X : Type*} [PseudoMetricSpace X]

lemma lipschitz_exp_bounded {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    {B : ℝ} (hB : ∀ x, V x ≤ B) :
    LipschitzWith (⟨Real.exp B,(Real.exp_pos B).le⟩*L) (fun x => Real.exp (V x)) := by
  have he : LipschitzOnWith ⟨Real.exp B,(Real.exp_pos B).le⟩ Real.exp (Iic B) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => Real.differentiableAt_exp) _ (convex_Iic B)
    intro x hx
    change ‖deriv Real.exp x‖ ≤ Real.exp B
    simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr hx
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (he.dist_le_mul (V x) (hB x) (V y) (hB y)).trans (by
    change Real.exp B * dist (V x) (V y) ≤ (Real.exp B * (L:ℝ))*dist x y
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hV.dist_le_mul x y) (Real.exp_pos B).le)

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_NonnegativeParallelogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianFunctional
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable {q : V → ℝ} (hq : NonnegativeParallelogram q)
include hq

lemma NonnegativeParallelogram.polar_cauchySchwarz (f g : V) :
    (energyPolar q f g)^2 ≤ q f * q g := by
  have H : ∀ t : ℝ, 0 ≤ q f + 2*t*energyPolar q f g + t^2*q g := by
    intro t
    have h := hq.nonneg (f + t • g)
    rw [hq.polar_add, hq.polar_comm f, hq.polar_smul_left, hq.polar_comm g, hq.smul] at h
    nlinarith
  by_cases hg : q g = 0
  · have h1 := H (-(q f+1)/(2*energyPolar q f g))
    by_cases hp : energyPolar q f g = 0
    · simp [hp, hg]
    · have heq : q f + 2 * (-(q f+1)/(2*energyPolar q f g)) * energyPolar q f g +
          (-(q f+1)/(2*energyPolar q f g))^2 * q g = -1 := by
        rw [hg]
        field_simp [hp]
        ring
      rw [heq] at h1
      linarith
  · have h1 := H (-energyPolar q f g/q g)
    have hgpos : 0 < q g := lt_of_le_of_ne (hq.nonneg g) (Ne.symm hg)
    field_simp at h1
    nlinarith [sq_nonneg (energyPolar q f g)]

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_HopfObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X]

lemma hopf_minimizer_distance_lipschitz {f : X → ℝ} {L : ℝ≥0} {B t : ℝ}
    (hf : LipschitzWith L f) (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) : dist x y ≤ 2*t*(L:ℝ) := by
  have H := hopfLax_le_self hlower ht x
  rw [← hy] at H
  have Hd := hf.dist_le_mul x y
  rw [Real.dist_eq] at Hd
  have Hd' := (abs_le.mp Hd).2
  have Hdiv : dist x y^2/(2*t) ≤ (L:ℝ)*dist x y := by
    dsimp [hopfObjective] at H
    linarith
  have Hmul := (div_le_iff₀ (by positivity : 0 < 2*t)).mp Hdiv
  by_cases hd : dist x y = 0
  · rw [hd]
    positivity
  · have hd0 : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    apply le_of_mul_le_mul_left (a := dist x y) _ hd0
    convert Hmul using 1 <;> ring

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_DensityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

namespace WeakHessianTransport
variable {X : Type*} [MeasurableSpace X] (m : Measure X)

lemma densityMeasure_ac (ρ : Lp ℝ 2 m) : densityMeasure m ρ ≪ m :=
  withDensity_absolutelyContinuous _ _

end WeakHessianTransport

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientTendstoNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

section NormConvergence
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_tendsto_of_norm_tendsto {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) := by
  let fm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • fn n + (1/2 : ℝ) • f
  let Dm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • Dn n + (1/2 : ℝ) • D
  have hmid (n : ℕ) : IsLocalWeakUpperGradient m (fm n) (Dm n) := by
    exact convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (fn n, Dn n)) (y := WithLp.toLp 2 (f,D))
      (hn n) hD (by norm_num) (by norm_num) (by norm_num)
  have hfm : Tendsto fm atTop (𝓝 f) := by
    have H := (hf.const_smul (1/2 : ℝ)).add
      (tendsto_const_nhds (x := (1/2 : ℝ) • f))
    simpa only [← add_smul, show (1/2:ℝ)+(1/2)=1 by norm_num, one_smul] using H
  have hlow (a : ℝ) (ha : a < ‖D‖) : ∀ᶠ n in atTop, a < ‖Dm n‖ := by
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    have H := hfm.eventually ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)
    filter_upwards [H] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dm n,hmid n,hle⟩)
  have hupper (n : ℕ) : ‖Dm n‖ ≤ (‖Dn n‖+‖D‖)/2 := by
    calc
      ‖Dm n‖ ≤ ‖(1/2 : ℝ) • Dn n‖ + ‖(1/2 : ℝ) • D‖ := norm_add_le _ _
      _ = (‖Dn n‖+‖D‖)/2 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        ring
  have hmajor : Tendsto (fun n => (‖Dn n‖+‖D‖)/2) atTop (𝓝 ‖D‖) := by
    convert (hNorm.add_const ‖D‖).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hmidNorm : Tendsto (fun n => ‖Dm n‖) atTop (𝓝 ‖D‖) := by
    apply tendsto_order.mpr
    refine ⟨hlow, fun b hb => ?_⟩
    filter_upwards [hmajor.eventually (gt_mem_nhds hb)] with n hn'
    exact (hupper n).trans_lt hn'
  have hsq (n : ℕ) : ‖Dn n - D‖^2 = 2*‖Dn n‖^2+2*‖D‖^2-4*‖Dm n‖^2 := by
    have hm : ‖Dm n‖ = ‖Dn n+D‖/2 := by
      simp only [Dm, ← smul_add, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      ring
    rw [hm]
    nlinarith [parallelogram_law_with_norm ℝ (Dn n) D]
  have hs : Tendsto (fun n => ‖Dn n-D‖^2) atTop (𝓝 0) := by
    simp_rw [hsq]
    convert ((hNorm.pow 2).const_mul 2 |>.add_const (2*‖D‖^2)).sub
      ((hmidNorm.pow 2).const_mul 4) using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using H

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.norm_le {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    {E : Lp ℝ 2 m} (hE : IsLocalWeakUpperGradient m f E) : ‖D‖ ≤ ‖E‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hD.2 E hE, hD.1.2.1, hE.2.1] with x hx hd he
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd, abs_of_nonneg he] using hx

lemma IsMinimalLocalWeakUpperGradient.tendsto_of_norm_tendsto
    {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) :=
  upperGradient_tendsto_of_norm_tendsto hn hf hD.1 (fun _ hE => hD.norm_le hE) hNorm
end NormConvergence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientNormTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_norm_tendsto_of_sq_upper {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, ‖Dn n‖^2 ≤ ‖D‖^2+ε n) :
    Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    filter_upwards [hf.eventually
      ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dn n,hn n,hle⟩)
  · intro b hb
    have hbpos : 0 < b := lt_of_le_of_lt (norm_nonneg D) hb
    have hgap : 0 < b^2-‖D‖^2 := by nlinarith [norm_nonneg D]
    filter_upwards [hε.eventually (gt_mem_nhds hgap)] with n hn'
    nlinarith [hbound n, norm_nonneg (Dn n)]

lemma exists_lipschitz_strong_slopes (hfinite : FiniteOnBoundedSets m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ hDs : ∀ n, MemLp (fun x => (localSlope (fs n) x).toReal) 2 m,
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 f) ∧
        Tendsto (fun n => (hDs n).toLp (fun x => (localSlope (fs n) x).toReal))
          atTop (𝓝 D) := by
  have hex (n : ℕ) := cheegerEnergy_lt_approx (f := f)
    (a := ENNReal.ofReal (‖D‖^2/2+1/((n:ℝ)+1)))
    (by rw [henergy]; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (lt_add_of_pos_right _ (by positivity)))
    (ε := 1/((n:ℝ)+1)) (by positivity)
  choose fs hLip hfs hdist hEn using hex
  have hfin (n : ℕ) : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) < ∞ := by
    by_contra hh
    have ht : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) = ∞ := top_le_iff.mp (not_lt.mp hh)
    have H := hEn n
    norm_num [ht] at H
  let hDs (n : ℕ) : MemLp (fun x => (localSlope (fs n) x).toReal) 2 m :=
    memLp_localSlope_of_lintegral_lt_top (hLip n).choose_spec (hfin n)
  let fn (n : ℕ) := (hfs n).toLp (fs n)
  let Dn (n : ℕ) := (hDs n).toLp (fun x => (localSlope (fs n) x).toReal)
  have hfn : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hDn (n : ℕ) : IsLocalWeakUpperGradient m (fn n) (Dn n) := by
    exact (localSlope_isLocalWeakUpperGradient hfinite (hLip n).choose_spec).congr_ae
      (hfs n).coeFn_toLp.symm (hDs n).coeFn_toLp.symm
  have hbound (n : ℕ) : ‖Dn n‖^2 ≤ ‖D‖^2 + 2*(1/((n:ℝ)+1)) := by
    have H := hEn n
    rw [half_lintegral_localSlope_eq (hLip n).choose_spec (hDs n)] at H
    have H' : ‖Dn n‖^2/2 < ‖D‖^2/2+1/((n:ℝ)+1) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp H
    linarith
  refine ⟨fs,hLip,hfs,hDs,hfn,?_⟩
  apply hD.tendsto_of_norm_tendsto hDn hfn
  exact upperGradient_norm_tendsto_of_sq_upper hDn hfn (fun _ hE => hD.norm_le hE)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))) hbound

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactSlopeApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile95
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
lemma localSlope_cutoff_le (o : X) (n : ℕ) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) :
    (localSlope (fun y => radialCutoff o n y * f y) x).toReal ≤
      (localSlope f x).toReal + (1/((n:ℝ)+1))*|f x| := by
  have hs := localSlope_product_le (radialCutoff_lipschitz o n) hf x
  have hc := localSlope_le_lipschitz (radialCutoff_lipschitz o n) x
  have hsf := localSlope_le_lipschitz hf x
  have hct : localSlope (radialCutoff o n) x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hc
  have hft : localSlope f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hsf
  have H := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hft, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct⟩) hs
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hft)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (radialCutoff_nonneg o n x)] at H
  have hc' := ENNReal.toReal_mono ENNReal.coe_ne_top hc
  simp only [ENNReal.coe_toReal,NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hc'
  calc
    _ ≤ _ := H
    _ ≤ 1*(localSlope f x).toReal+|f x| * ((n:ℝ)+1)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_right (radialCutoff_le_one o n x) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left hc' (abs_nonneg _))
    _ = _ := by ring

lemma exists_compact_cutoff_approx (o : X) {f : X → ℝ}
    (hf : GloballyLipschitz f) (hf2 : MemLp f 2 m)
    (hs2 : MemLp (fun x => (localSlope f x).toReal) 2 m) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n,HasCompactSupport (fs n)) ∧ ∃ hfs : ∀ n,MemLp (fs n) 2 m,
      ∃ Ds : ℕ → Lp ℝ 2 m,
      (∀ n,∀ᵐ x ∂m,0 ≤ Ds n x ∧ (localSlope (fs n) x).toReal ≤ Ds n x) ∧
      Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf2.toLp f)) ∧
      Tendsto Ds atTop (𝓝 (hs2.toLp (fun x => (localSlope f x).toReal))) := by
  let fs := fun n x => radialCutoff o n x*f x
  have hLip (n : ℕ) : GloballyLipschitz (fs n) :=
    lipschitz_mul_compact ⟨_,radialCutoff_lipschitz o n⟩ hf (radialCutoff_compact o n)
  have hc (n : ℕ) : HasCompactSupport (fs n) := (radialCutoff_compact o n).mul_right
  have hm (n : ℕ) := (radialCutoff_lipschitz o n).continuous.measurable.aestronglyMeasurable (μ := m)
  have hb (n : ℕ) : ∀ᵐ x ∂m,|radialCutoff o n x| ≤ 1 := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hfs (n : ℕ) : MemLp (fs n) 2 m := by
    simpa only [fs,mul_comm] using memLp_mul_bounded hf2 (hm n) (hb n)
  let S := hs2.toLp (fun x => (localSlope f x).toReal)
  let A := hf2.norm.toLp (fun x => ‖f x‖)
  let Ds := fun n : ℕ => S+(1/((n:ℝ)+1)) • A
  have hD (n : ℕ) : ∀ᵐ x ∂m,Ds n x = (localSlope f x).toReal+(1/((n:ℝ)+1))*|f x| := by
    filter_upwards [Lp.coeFn_add S ((1/((n:ℝ)+1)) • A),Lp.coeFn_smul (1/((n:ℝ)+1)) A,
      hs2.coeFn_toLp,hf2.norm.coeFn_toLp] with x h1 h2 h3 h4
    change (S+(1/((n:ℝ)+1)) • A) x = _
    rw [h1]
    change S x+((1/((n:ℝ)+1)) • A) x = _
    rw [h2]
    change S x+(1/((n:ℝ)+1))*A x = _
    rw [h3,h4,Real.norm_eq_abs]
  refine ⟨fs,hLip,hc,hfs,Ds,fun n => ?_,?_,?_⟩
  · filter_upwards [hD n] with x hx
    rw [hx]
    exact ⟨by positivity,localSlope_cutoff_le o n hf.choose_spec x⟩
  · have H := boundedMulLp_tendsto hm hb (ae_of_all _ (radialCutoff_tendsto o)) (hf2.toLp f)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply Lp.ext
    filter_upwards [(hfs n).coeFn_toLp,boundedMulLp_ae (hm n) (hb n) (hf2.toLp f),hf2.coeFn_toLp] with x h1 h2 h3
    calc
      _ = fs n x := h1
      _ = f x*radialCutoff o n x := mul_comm _ _
      _ = _ := by rw [h2,h3]
  · simpa only [Ds,zero_smul,add_zero,S] using (tendsto_const_nhds (x := S)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const A)

lemma exists_compact_strong_slope_majorants (hfinite : FiniteOnBoundedSets m) (o : X)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n,HasCompactSupport (fs n)) ∧ ∃ hfs : ∀ n,MemLp (fs n) 2 m,
      ∃ Ds : ℕ → Lp ℝ 2 m,
      (∀ n,∀ᵐ x ∂m,0 ≤ Ds n x ∧ (localSlope (fs n) x).toReal ≤ Ds n x) ∧
      Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 f) ∧
      Tendsto Ds atTop (𝓝 D) := by
  obtain ⟨gs,hg,hg2,hs2,hgt,hst⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  choose fs hfs hfc hf2 Ds hDs hft hDt using fun n => exists_compact_cutoff_approx o (hg n) (hg2 n) (hs2 n)
  have hex (n : ℕ) : ∃ k : ℕ,
      dist ((hf2 n k).toLp (fs n k)) ((hg2 n).toLp (gs n)) < 1/((n:ℝ)+1) ∧
      dist (Ds n k) ((hs2 n).toLp (fun x => (localSlope (gs n) x).toReal)) < 1/((n:ℝ)+1) := by
    have H1 := (hft n).eventually (Metric.ball_mem_nhds _ (by positivity : 0 < 1/((n:ℝ)+1)))
    have H2 := (hDt n).eventually (Metric.ball_mem_nhds _ (by positivity : 0 < 1/((n:ℝ)+1)))
    exact (H1.and H2).exists
  choose k hk using hex
  refine ⟨fun n => fs n (k n),fun n => hfs n (k n),fun n => hfc n (k n),
    fun n => hf2 n (k n),fun n => Ds n (k n),fun n => hDs n (k n),?_,?_⟩
  · apply tendsto_of_tendsto_of_dist hgt
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hk n).1.le) tendsto_one_div_add_atTop_nhds_zero_nat
  · apply tendsto_of_tendsto_of_dist hst
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hk n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat
end WeakHessian

end
end InlinedFile95

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HopfInitialSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile84
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

lemma slopeApprox_quotient_le {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (n : ℕ) {x y : X} (hy : dist x y < 1/(n+1:ℝ)) :
    |f x-f y| ≤ (slopeApprox f n x).toReal*dist x y := by
  have hfin : slopeApprox f n x ≠ ∞ := ne_of_lt ((slopeApprox_le_lipschitz hf n x).trans_lt ENNReal.coe_lt_top)
  have H : ENNReal.ofReal (|f y-f x|/dist y x) ≤ slopeApprox f n x :=
    le_iSup_of_le y (le_iSup_of_le (by simpa only [dist_comm] using hy) le_rfl)
  have H' := ENNReal.toReal_mono hfin H
  rw [ENNReal.toReal_ofReal (by positivity)] at H'
  by_cases hxy : x = y
  · simp [hxy]
  · have hp : 0 < dist y x := dist_pos.mpr (Ne.symm hxy)
    simpa only [abs_sub_comm,dist_comm] using (div_le_iff₀ hp).mp H'

lemma hopf_initial_slopeApprox_bound [ProperSpace X] (f : X →ᵇ ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : X) {s : ℝ} (hs : 0 < s)
    (hsmall : 2*s*(L:ℝ) < 1/(n+1:ℝ)) :
    (f x-hopfLax f s x)/s ≤ (slopeApprox f n x).toReal^2/2 := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (fun z => (boundedContinuous_bounds f z).1) hs x
  have hd := hopf_minimizer_distance_lipschitz hf (fun z => (boundedContinuous_bounds f z).1) hs hy
  have hb := (abs_le.mp (slopeApprox_quotient_le hf n (hd.trans_lt hsmall))).2
  rw [← hy]
  dsimp only [hopfObjective]
  apply (div_le_iff₀ hs).mpr
  have hq : (slopeApprox f n x).toReal*dist x y-s*(slopeApprox f n x).toReal^2/2 ≤ dist x y^2/(2*s) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*s)).mpr
    nlinarith [sq_nonneg (dist x y-s*(slopeApprox f n x).toReal)]
  linarith

lemma tendsto_slopeApprox_toReal {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : X) :
    Tendsto (fun n : ℕ => (slopeApprox f n x).toReal) atTop (𝓝 (localSlope f x).toReal) := by
  have hlfin : localSlope f x ≠ ∞ :=
    ne_of_lt ((localSlope_le_lipschitz hf x).trans_lt ENNReal.coe_lt_top)
  have hmono : Antitone (fun n : ℕ => slopeApprox f n x) := by
    intro n k hnk
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    have hrad : 1/(k+1:ℝ) ≤ 1/(n+1:ℝ) := by gcongr
    exact le_iSup_of_le y (le_iSup_of_le (hy.trans_le hrad) le_rfl)
  apply (ENNReal.tendsto_toReal hlfin).comp
  rw [localSlope_eq_iInf_slopeApprox]
  exact tendsto_atTop_ciInf hmono ⟨0,fun _ _ => bot_le⟩

end WeakHessianTransport

end
end InlinedFile84

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integrable_density_slope_sq (_ : FiniteOnBoundedSets m)
    {u φ : X → ℝ} (hi : Integrable u m) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Integrable (fun x => u x*(localSlope φ x).toReal^2) m := by
  apply hi.mul_bdd ((measurable_localSlope hφ.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
    (c := (L:ℝ)^2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hφ x)).trans_eq (ENNReal.coe_toReal L))

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfMapLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open WeakHessian MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma integrable_bounded_pairing {u : X → ℝ} (hi : Integrable u m) (f : X →ᵇ ℝ) :
    Integrable (fun x => u x*f x) m :=
  hi.mul_bdd f.continuous.aestronglyMeasurable (ae_of_all _ fun x => f.norm_coe_le_norm x)

omit [BorelSpace X] [ProperSpace X] in
lemma norm_integral_bounded_pairing {u : X → ℝ} (hi : Integrable u m) (f : X →ᵇ ℝ) :
    ‖∫ x,u x*f x ∂m‖ ≤ ‖f‖*(∫ x,‖u x‖ ∂m) := by
  have H := norm_integral_le_of_norm_le (f := fun x => u x*f x) (hi.norm.const_mul ‖f‖) (by
    apply ae_of_all
    intro x
    rw [norm_mul,mul_comm ‖f‖]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
  simpa only [integral_const_mul] using H

omit [ProperSpace X] in
lemma integral_bounded_pairing_sub_left {u v : X → ℝ} (hu : Integrable u m)
    (hv : Integrable v m) (q : X →ᵇ ℝ) :
    (∫ x,(v x-u x)*q x ∂m) = (∫ x,v x*q x ∂m)-(∫ x,u x*q x ∂m) := by
  rw [← integral_sub (integrable_bounded_pairing hv q) (integrable_bounded_pairing hu q)]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

omit [ProperSpace X] in
lemma integral_bounded_pairing_sub_right {u : X → ℝ} (hu : Integrable u m)
    (q r : X →ᵇ ℝ) :
    (∫ x,u x*(r-q) x ∂m) = (∫ x,u x*r x ∂m)-(∫ x,u x*q x ∂m) := by
  rw [← integral_sub (integrable_bounded_pairing hu r) (integrable_bounded_pairing hu q)]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [BoundedContinuousFunction.sub_apply]; ring)

lemma boundedHopfMap_L1_increment (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    {u : X → ℝ} (hi : Integrable u m) (hu : ∀ᵐ x ∂m,0 ≤ u x)
    {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    (∫ x,u x*(boundedHopfMap f s-boundedHopfMap f t) x ∂m) ≤
      (-(s-t)*t/(2*s))*(∫ x,u x*(localSlope (boundedHopfMap f t) x).toReal^2 ∂m) := by
  obtain ⟨L,hL⟩ := boundedHopfMap_lipschitz f ht
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_bounded_pairing hi _) ((integrable_density_slope_sq hfin hi hL).const_mul _)
  filter_upwards [hu] with x hx
  have H := mul_le_mul_of_nonneg_left (hopf_forward_increment f.continuous
    (fun x => (boundedContinuous_bounds f x).1) (fun x => (boundedContinuous_bounds f x).2)
    (by linarith [norm_nonneg f]) ht hts x) hx
  have hqt : (boundedHopfMap f t : X → ℝ) = hopfLax f t := funext (boundedHopfMap_apply_pos f ht)
  simpa only [BoundedContinuousFunction.sub_apply,boundedHopfMap_apply_pos f ht,
    boundedHopfMap_apply_pos f (ht.trans_le hts),hqt,mul_left_comm,mul_assoc] using H

omit [ProperSpace X] in
lemma tendsto_bounded_pairing_L1 {ι : Type*} {l : Filter ι}
    {u : ι → X → ℝ} {v : X → ℝ} (hu : ∀ i,Integrable (u i) m) (hv : Integrable v m)
    {q : ι → X →ᵇ ℝ} {r : X →ᵇ ℝ} (hq : Tendsto q l (𝓝 r))
    (hL1 : Tendsto (fun i => ∫ x,‖u i x-v x‖ ∂m) l (𝓝 0)) :
    Tendsto (fun i => ∫ x,u i x*q i x ∂m) l (𝓝 (∫ x,v x*r x ∂m)) := by
  have hD : Tendsto (fun i => ‖q i-r‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hq.sub (tendsto_const_nhds (x := r))).norm
  have H (i : ι) : ‖(∫ x,u i x*q i x ∂m)-(∫ x,v x*r x ∂m)‖ ≤
      ‖q i-r‖*(∫ x,‖v x‖ ∂m)+‖q i‖*(∫ x,‖u i x-v x‖ ∂m) := by
    have he : (∫ x,u i x*q i x ∂m)-(∫ x,v x*r x ∂m) =
        (∫ x,v x*(q i-r) x ∂m)+(∫ x,(u i x-v x)*q i x ∂m) := by
      rw [integral_bounded_pairing_sub_right hv,integral_bounded_pairing_sub_left hv (hu i)]
      ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_integral_bounded_pairing hv _)
      (norm_integral_bounded_pairing ((hu i).sub hv) _))
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm H
  simpa only [zero_mul,mul_zero,add_zero] using (hD.mul_const _).add (hq.norm.mul hL1)

end WeakHessianTransport
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_IntegralHopfInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile85
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma integrable_density_slopeApprox_sq {u f : X → ℝ} (hu : Integrable u m)
    {L : ℝ≥0} (hf : LipschitzWith L f) (n : ℕ) :
    Integrable (fun x => u x*(slopeApprox f n x).toReal^2) m := by
  apply hu.mul_bdd ((lowerSemicontinuous_slopeApprox hf.continuous n).measurable.ennreal_toReal.pow_const 2).aestronglyMeasurable (c := (L:ℝ)^2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (slopeApprox_le_lipschitz hf n x)).trans_eq (ENNReal.coe_toReal L))

omit [ProperSpace X] in
lemma tendsto_integral_slopeApprox {u f : X → ℝ} (hu : Integrable u m)
    {L : ℝ≥0} (hf : LipschitzWith L f) :
    Tendsto (fun n : ℕ => ∫ x,u x*(slopeApprox f n x).toReal^2 ∂m) atTop
      (𝓝 (∫ x,u x*(localSlope f x).toReal^2 ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖u x‖*(L:ℝ)^2)
  · intro n
    exact (integrable_density_slopeApprox_sq hu hf n).aestronglyMeasurable
  · exact hu.norm.mul_const _
  · intro n
    apply ae_of_all
    intro x
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg ((slopeApprox f n x).toReal))]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
      ((ENNReal.toReal_mono ENNReal.coe_ne_top (slopeApprox_le_lipschitz hf n x)).trans_eq (ENNReal.coe_toReal L))
  · exact ae_of_all _ fun x => ((tendsto_slopeApprox_toReal hf x).pow 2).const_mul (u x)

lemma integral_hopf_initial_eventually_lt (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {u : X → ℝ} (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {a : ℝ} (ha : (∫ x,u x*(localSlope f x).toReal^2 ∂m)/2 < a) :
    ∀ᶠ s in 𝓝[>] (0:ℝ),(∫ x,u x*(f x-boundedHopfMap f s x) ∂m)/s < a := by
  obtain ⟨n,hn⟩ := ((tendsto_integral_slopeApprox hu hf).div_const 2).eventually_lt_const ha |>.exists
  have ht : Tendsto (fun s : ℝ => 2*s*(L:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (ht.const_mul 2).mul_const (L:ℝ)
  filter_upwards [ht.eventually_lt_const (by positivity : (0:ℝ) < 1/(n+1:ℝ)),self_mem_nhdsWithin] with s hs hs0
  apply lt_of_le_of_lt _ hn
  rw [← integral_div,← integral_div]
  apply integral_mono_ae
  · simpa only [BoundedContinuousFunction.sub_apply,div_eq_mul_inv,mul_assoc] using
      (integrable_bounded_pairing hu (f-boundedHopfMap f s)).mul_const s⁻¹
  · exact (integrable_density_slopeApprox_sq hu hf n).div_const 2
  · filter_upwards [hun] with x hx
    rw [boundedHopfMap_apply_pos f hs0,mul_div_assoc,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hopf_initial_slopeApprox_bound f hf n x hs0 hs) hx
end WeakHessianTransport

end
end InlinedFile85

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_RightEndpointDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile107
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

lemma hasDerivWithinAt_Ici_of_tendsto_right_deriv {J d : ℝ → ℝ} {v : ℝ}
    (hc : ContinuousOn J (Ici 0))
    (hd : ∀ t, 0 < t → HasDerivWithinAt J (d t) (Ici t) t)
    (hv : Tendsto d (𝓝[>] 0) (𝓝 v)) : HasDerivWithinAt J v (Ici 0) 0 := by
  have HB (a t b : ℝ) (ha : 0 < a) (hat : a ≤ t)
      (hb : ∀ s ∈ Ico a t, d s ≤ b) : J t ≤ J a+b*(t-a) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary (f := J)
      (B := fun s => J a+b*(s-a)) (B' := fun _ => b)
      (hc.mono (fun _ hx => ha.le.trans hx.1)) (by simp) (by fun_prop)
      (fun s _ => by simpa using ((((hasDerivAt_id s).sub_const a).const_mul b).const_add (J a)).hasDerivWithinAt (s := Ici s))
      _ ⟨hat,le_rfl⟩
    intro s hs r hr
    exact (hd s (ha.trans_le hs.1)).liminf_right_slope_le ((hb s hs).trans_lt hr)
  have HL (a t b : ℝ) (ha : 0 < a) (hat : a ≤ t)
      (hb : ∀ s ∈ Ico a t, b ≤ d s) : J a+b*(t-a) ≤ J t := by
    have H : -J t ≤ -J a+(-b)*(t-a) := by
      apply image_le_of_liminf_slope_right_le_deriv_boundary (f := fun s => -J s)
        (B := fun s => -J a+(-b)*(s-a)) (B' := fun _ => -b)
        ((hc.neg).mono (fun _ hx => ha.le.trans hx.1)) (by simp) (by fun_prop)
        (fun s _ => by simpa using ((((hasDerivAt_id s).sub_const a).const_mul (-b)).const_add (-J a)).hasDerivWithinAt (s := Ici s))
        _ ⟨hat,le_rfl⟩
      intro s hs r hr
      exact ((hd s (ha.trans_le hs.1)).neg).liminf_right_slope_le ((neg_le_neg (hb s hs)).trans_lt hr)
    linarith
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hv (ε/2) (half_pos hε))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp hev
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hδ)] with t ht htd
  change 0 < t at ht
  have htδ : t < δ := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htd
  have Hs (s : ℝ) (hs : 0 < s) (hst : s ≤ t) : v-ε/2 ≤ d s ∧ d s ≤ v+ε/2 := by
    have HH := hδb (show s ∈ Metric.ball (0:ℝ) δ ∩ Ioi 0 from
      ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hs] using hst.trans_lt htδ,hs⟩)
    change dist (d s) v < ε/2 at HH
    rw [Real.dist_eq,abs_sub_lt_iff] at HH
    exact ⟨by linarith,by linarith⟩
  have hup : J t ≤ J 0+(v+ε/2)*t := by
    have hj0 := (hc 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hj0
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hh : Tendsto (fun a : ℝ => J a+(v+ε/2)*(t-a)) (𝓝[>] 0) (𝓝 (J 0+(v+ε/2)*t)) := by
      simpa using hj0.add (((tendsto_const_nhds (x := t)).sub hid).const_mul (v+ε/2))
    apply ge_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const ht] with a ha hat
    exact HB a t (v+ε/2) ha hat.le (fun s hs => (Hs s (ha.trans_le hs.1) hs.2.le).2)
  have hlo : J 0+(v-ε/2)*t ≤ J t := by
    have hj0 := (hc 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hj0
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hh : Tendsto (fun a : ℝ => J a+(v-ε/2)*(t-a)) (𝓝[>] 0) (𝓝 (J 0+(v-ε/2)*t)) := by
      simpa using hj0.add (((tendsto_const_nhds (x := t)).sub hid).const_mul (v-ε/2))
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const ht] with a ha hat
    exact HL a t (v-ε/2) ha hat.le (fun s hs => (Hs s (ha.trans_le hs.1) hs.2.le).1)
  rw [Real.dist_eq,slope_def_field,sub_zero,abs_sub_lt_iff]
  constructor
  · have HH := (div_le_iff₀ ht).mpr (show J t-J 0 ≤ (v+ε/2)*t by linarith)
    linarith
  · have HH := (le_div_iff₀ ht).mpr (show (v-ε/2)*t ≤ J t-J 0 by linarith)
    linarith

end
end InlinedFile107

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Curvature_Doubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile79
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma CurvatureDimension.uniform_local_doubling {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) :
    IsUnifLocDoublingMeasure m := by
  let A : ℝ := 4*N*Real.log 2+24*Real.sqrt (|K|/(N-1))*(N-1)
  let C : ℝ≥0 := ⟨Real.exp A,(Real.exp_pos _).le⟩
  refine ⟨C,?_⟩
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with r hr hr1 x
  have hr0 : 0 < r := hr
  have hp (R : ℝ) (hR : 0 < R) : 0 < (m (Metric.ball x R)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hR⟩).ne' (hfin _ Metric.isBounded_ball).ne
  have H := cd_log_iterated_ball hN hcd hfull hfin x (by positivity : 0 < 3*r) 4
  have hsmall : (3/4:ℝ)^4*(3*r) ≤ r := by nlinarith
  have hlog : Real.log (m (Metric.ball x ((3/4:ℝ)^4*(3*r)))).toReal ≤ Real.log (m (Metric.closedBall x r)).toReal := by
    apply Real.log_le_log (hp _ (by positivity))
    exact ENNReal.toReal_mono (hfin _ Metric.isBounded_closedBall).ne
      (measure_mono ((Metric.ball_subset_ball hsmall).trans Metric.ball_subset_closedBall))
  have hcpos : 0 < (m (Metric.closedBall x r)).toReal :=
    (hp r hr0).trans_le (ENNReal.toReal_mono (hfin _ Metric.isBounded_closedBall).ne (measure_mono Metric.ball_subset_closedBall))
  have hS : 0 ≤ Real.sqrt (|K|/(N-1))*(N-1) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have H' : Real.log (m (Metric.ball x (3*r))).toReal ≤ Real.log (m (Metric.closedBall x r)).toReal+A := by
    norm_num only [Nat.cast_ofNat] at H
    have hprod : 8*Real.sqrt (|K|/(N-1))*(N-1)*(3*r)*(1-(3/4:ℝ)^4) ≤ 24*Real.sqrt (|K|/(N-1))*(N-1) := by
      nlinarith
    dsimp only [A]
    linarith
  have HE := Real.exp_le_exp.mpr H'
  rw [Real.exp_log (hp _ (by positivity)),Real.exp_add,Real.exp_log hcpos] at HE
  calc
    m (Metric.closedBall x (2*r)) ≤ m (Metric.ball x (3*r)) := measure_mono (Metric.closedBall_subset_ball (by linarith))
    _ ≤ (C:ℝ≥0∞)*m (Metric.closedBall x r) := by
      rw [← ENNReal.ofReal_toReal (hfin (Metric.ball x (3*r)) Metric.isBounded_ball).ne,
        ← ENNReal.ofReal_toReal (hfin (Metric.closedBall x r) Metric.isBounded_closedBall).ne]
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal _ ≤ ENNReal.ofReal (Real.exp A)*ENNReal.ofReal _
      rw [← ENNReal.ofReal_mul (Real.exp_pos A).le,mul_comm (Real.exp A)]
      exact ENNReal.ofReal_le_ofReal HE
end WeakHessian

end
end InlinedFile79

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology


namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma quadraticTransportCost_eq_integral [SecondCountableTopology X] {q : Measure (X×X)}
    (hq : QuadraticTransportCost q ≠ ∞) :
    QuadraticTransportCost q = ENNReal.ofReal (∫ p : X×X, dist p.1 p.2^2 ∂q) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_squared_distance_of_cost hq)
    (ae_of_all _ fun _ => sq_nonneg _)]
  simp only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg]

end WeakHessian
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ZeroDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile3
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integrable {n : Measure X} {w f : X → ℝ} (hw : Measurable w) :
    Integrable f (squareDensityMeasure n w) ↔ Integrable (fun x => w x^2*f x) n := by
  rw [squareDensityMeasure,integrable_withDensity_iff_integrable_smul₀'
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

end WeakHessian

end
end InlinedFile3

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropySlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile5
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma integral_mul_le_sqrt_integral_sq {m : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x,f x*g x ∂m) ≤ Real.sqrt (∫ x,f x^2 ∂m)*Real.sqrt (∫ x,g x^2 ∂m) := by
  have he : (∫ x,f x*g x ∂m) = ⟪hf.toLp f,hg.toLp g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [he,← norm_toLp_sq_eq_integral hf,← norm_toLp_sq_eq_integral hg,
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

end WeakHessian

end
end InlinedFile5

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_StrongEntropyConfinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
lemma CurvatureDimension.exists_strong_entropy_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => Real.exp (-(a*dist x o/2))) 2 m ∧
      Integrable (fun x => Real.exp (-(a*dist x o/2))) m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  let d := |C|+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hCd : C < d := by dsimp [d]; linarith [le_abs_self C]
  have hvol := cd_ball_volume_bound hN hcd hfull hfin o
  have hbase : MemLp (fun x => Real.exp (-(d*dist x o))) 2 m := by
    simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le
      (show C < 2*d by linarith) hvol
  have hbI : Integrable (fun x => Real.exp (-(d*dist x o))) m := by
    simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le hCd hvol
  refine ⟨2*d,by positivity,?_,?_,?_,?_,?_⟩
  · simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*d by linarith) hvol
  · simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*(2*d) by linarith) hvol
  · apply (hbase.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*d*dist x o)*Real.exp (-(2*d*dist x o))| ≤ |2*Real.exp (-(d*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      have H := (Real.mul_exp_neg_le_exp_neg_one (d*dist x o)).trans
        (show Real.exp (-1) ≤ 1 by rw [Real.exp_le_one_iff]; norm_num)
      have he : (2*d*dist x o)*Real.exp (-(2*d*dist x o)) =
          2*(d*dist x o*Real.exp (-(d*dist x o)))*Real.exp (-(d*dist x o)) := by
        rw [show -(2*d*dist x o) = -(d*dist x o)+(-(d*dist x o)) by ring,Real.exp_add]
        ring
      rw [he]
      nlinarith [Real.exp_pos (-(d*dist x o))]
  · convert! hbase using 1; funext x; congr 1; ring
  · convert! hbI using 1; funext x; congr 1; ring
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional


open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolventHeat_strong_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hd : R.toLinearMap.range.topologicalClosure = ⊤) (u : H) :
    Tendsto (fun t : ℝ => resolventHeat R t u) (𝓝[≥] (0:ℝ)) (𝓝 u) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd' := Submodule.dense_iff_topologicalClosure_eq_top.mpr hd
  obtain ⟨w, hw, hwR⟩ := Metric.dense_iff.mp hd' u (ε/4) (by positivity)
  obtain ⟨v,rfl⟩ := hwR
  have hv : dist (R v) u < ε/4 := hw
  have htend : Tendsto (fun t : ℝ => t*‖v‖) (𝓝[≥] (0:ℝ)) (𝓝 0) := by
    simpa using ((continuous_id.mul_const ‖v‖).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => t*‖v‖) (𝓝[≥] (0:ℝ)) (𝓝 (0*‖v‖)))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≥] (0:ℝ), t*‖v‖ < ε/2 :=
    (tendsto_order.1 htend).2 _ (by positivity)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
  have hn := resolventHeat_range_error_apply hR hR1 ht0 v
  have hcon := resolventHeat_contractive hR hR1 ht0 u (R v)
  have htri := dist_triangle (resolventHeat R t u) (resolventHeat R t (R v)) u
  have htri2 := dist_triangle (resolventHeat R t (R v)) (R v) u
  rw [dist_comm u (R v)] at hcon
  rw [dist_eq_norm (resolventHeat R t (R v)) (R v)] at htri2
  linarith

end WeakHessianFunctional

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_RealHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

lemma realHeat_strong_zero {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hi : Function.Injective R) (u : Lp ℝ 2 m) :
    Tendsto (fun t : ℝ => realHeat m R t u) (𝓝[≥] (0:ℝ)) (𝓝 u) := by
  have hc := resolventHeat_strong_zero (complexify_positive m hR) (complexify_le_one m hR1)
    (complexify_range_dense m hR.isSymmetric hi) (ofRealLp m u)
  have hr := (reLp m).continuous.continuousAt.tendsto.comp hc
  simpa only [← ofReal_realHeat, Function.comp_def, re_ofRealLp] using hr

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheegerHeat_add (h : QuadraticCheegerEnergy m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cheegerHeat h (t+s) = cheegerHeat h t * cheegerHeat h s := realHeat_add m _ ht hs

lemma cheegerHeat_strong_zero [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [IsLocallyFiniteMeasure m] (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    Tendsto (fun t : ℝ => cheegerHeat h t u) (𝓝[≥] (0:ℝ)) (𝓝 u) :=
  realHeat_strong_zero m (cheeger_closedQuadraticEnergy h).resolvent_positive
    (cheeger_closedQuadraticEnergy h).resolvent_le_one
    ((cheeger_closedQuadraticEnergy h).resolvent_injective (cheeger_domain_dense h)) u


lemma cheegerHeat_bounded (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    {B : ℝ} (hB : 0 ≤ B) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, |cheegerHeat h t u x| ≤ B := by
  have hu' : ∀ᵐ x ∂m, u x ∈ Icc (-B) B := hu.mono fun _ hx => abs_le.mp hx
  exact (cheegerHeat_interval h ht (neg_nonpos.mpr hB) hB u hu').mono fun _ hx => abs_le.mpr hx

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatInverseSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma heatInverseSymbol_continuous (t : ℝ) : Continuous (heatInverseSymbol t) := by
  have hc := expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ)
  simp only [Polynomial.eval_X] at hc
  exact continuous_const.mul (hc.comp (continuous_id.div_const t))

lemma heatInverseSymbol_mul {t : ℝ} (ht : 0 < t) (s : ℝ) :
    s * heatInverseSymbol t s = heatSymbol t s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [zero_mul, heatSymbol_nonpos ht le_rfl]
  · rw [heatInverseSymbol, heatSymbol, ite_eq_right ht.ne', inv_div]
    field_simp

lemma heatSymbol_maps_range {t : ℝ} (ht : 0 < t) (s : ℝ) :
    heatSymbol t s = s*heatInverseSymbol t s := (heatInverseSymbol_mul ht s).symm

lemma resolventHeat_eq_resolvent_mul {R : H →L[ℂ] H} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) :
    resolventHeat R t = R*cfc (heatInverseSymbol t) R := by
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  calc
    resolventHeat R t = cfc (fun s : ℝ => s*heatInverseSymbol t s) R :=
      cfc_congr fun s _ => heatSymbol_maps_range ht s
    _ = cfc (fun s : ℝ => s) R*cfc (heatInverseSymbol t) R :=
      cfc_mul _ _ _ continuous_id.continuousOn (heatInverseSymbol_continuous t).continuousOn
    _ = _ := by rw [hid]

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatGeneratorOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

local instance instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions_3_r0aaddb_1 : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
lemma realHeat_mem_range {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) : realHeat m R t u ∈ R.toLinearMap.range := by
  refine ⟨realCfc m R (heatInverseSymbol t) u, ?_⟩
  apply ofRealLp_injective m
  change ofRealLp m (R (realCfc m R (heatInverseSymbol t) u)) = _
  rw [← complexify_ofReal m R, ofReal_realCfc, ofReal_realHeat,
    resolventHeat_eq_resolvent_mul (complexify_positive m hR) ht]
  rfl

end WeakHessianFunctional
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_hasFormGenerator {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    ∃ A, hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u) A := by
  obtain ⟨v,hv⟩ := realHeat_mem_range m hQ.resolvent_positive ht u
  change hQ.resolvent v = realHeat m hQ.resolventLinear t u at hv
  refine ⟨hQ.resolvent v-v, ?_⟩
  rw [← hv]
  exact hQ.isFormGenerator_resolvent v

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GlobalCheegerEnergyReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma CurvatureDimension.global_formGenerator_of_isLaplacian {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : IsLaplacian m (u : X → ℝ) (A : X → ℝ)) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator u A := by
  have huf := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp u)).mp hu.1
  refine ⟨huf, fun v => ?_⟩
  rw [← hcd.global_integral_gamma_form hfinite o h ⟨u,huf⟩ v]
  have hv := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp v.val)).mpr v.property
  rw [hu.2.2 v.val hv, L2.inner_def]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm (A x) (v.val x)

end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_ResolventEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.resolvent_energy_le (u : E) : Q (hQ.resolvent u) ≤ Q u := by
  have H := hQ.resolvent_minimizes u u
  have hle : Q (hQ.resolvent u) ≤ proximalFunctional Q u (hQ.resolvent u) := le_add_right le_rfl
  simpa only [proximalFunctional, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, ENNReal.ofReal_zero, add_zero] using hle.trans H

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_energy_le {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    Q (realHeat m hQ.resolventLinear t u) ≤ Q u := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [realHeat_zero m hQ.resolvent_positive]
    rfl
  have hstep {s : ℝ} (hs : 0 < s) (v : Lp ℝ 2 m) :
      Q ((hQ.scale hs).resolventLinear v) ≤ Q v := by
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top).mp
    exact (hQ.scale hs).resolvent_energy_le v
  have hp {s : ℝ} (hs : 0 < s) (n : ℕ) :
      Q ((((hQ.scale hs).resolventLinear)^n) u) ≤ Q u := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        (hstep hs ((((hQ.scale hs).resolventLinear)^n) u)).trans ih
  exact (hQ.lowerSemicontinuous.isClosed_preimage (Q u)).mem_of_tendsto
    (hQ.euler_tendsto_heat m ht u) (Eventually.of_forall fun n => hp (by positivity) (2^n))

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m]

omit [IsFiniteMeasure m] in
lemma cheegerHeat_energy_le (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    cheegerEnergy m (cheegerHeat h t u : X → ℝ) ≤ cheegerEnergy m (u : X → ℝ) :=
  (cheeger_closedQuadraticEnergy h).heat_energy_le m ht u

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma cheegerHeat_abs_le (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {t : ℝ} (ht : 0 ≤ t) : ∀ᵐ x ∂m, |cheegerHeat h t u x| ≤ cheegerHeat h t |u| x := by
  have hplus : ∀ᵐ x ∂m, u x ≤ |u| x := by
    filter_upwards [Lp.coeFn_abs u] with x hx
    rw [hx]; exact le_abs_self _
  have hminus : ∀ᵐ x ∂m, (-u) x ≤ |u| x := by
    filter_upwards [Lp.coeFn_abs u,Lp.coeFn_neg u] with x hx hy
    rw [hx,hy]; exact neg_le_abs _
  have H := cheegerHeat_order h ht (-u) |u| hminus
  rw [map_neg] at H
  filter_upwards [cheegerHeat_order h ht u |u| hplus,H,Lp.coeFn_neg (cheegerHeat h t u)] with x hp hn he
  rw [he] at hn
  exact abs_le.mpr ⟨by simpa only [Pi.neg_apply,neg_neg] using neg_le_neg hn,hp⟩

lemma cheegerHeat_integrable (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hi : Integrable u m)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (cheegerHeat h t u) m ∧
      (∫ x, ‖cheegerHeat h t u x‖ ∂m) ≤ ∫ x,‖u x‖ ∂m := by
  have hia : Integrable (fun x => (|u| : Lp ℝ 2 m) x) m := hi.abs.congr (Lp.coeFn_abs u).symm
  have hpa : ∀ᵐ x ∂m, 0 ≤ |u| x := (Lp.coeFn_abs u).mono fun x hx => hx ▸ abs_nonneg _
  have H := cheegerHeat_submass hfinite o h |u| hpa hia ht
  have hb : ∀ᵐ x ∂m, ‖cheegerHeat h t u x‖ ≤ cheegerHeat h t |u| x := cheegerHeat_abs_le h u ht
  have hj := H.1.mono' (Lp.memLp _).aestronglyMeasurable hb
  refine ⟨hj,(integral_mono_ae hj.norm H.1 hb).trans (H.2.trans_eq ?_)⟩
  exact integral_congr_ae ((Lp.coeFn_abs u).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile75
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma integral_densityMeasure_L2 (u f : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    (∫ x,f x ∂densityMeasure m u) = ⟪f,u⟫_ℝ := by
  rw [integral_densityMeasure,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  exact hun

omit [BorelSpace X] in
lemma cheegerHeat_density_duality (h : QuadraticCheegerEnergy m) (u f : Lp ℝ 2 m)
    {t : ℝ} (ht : 0 ≤ t) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    (∫ x,f x ∂densityMeasure m (cheegerHeat h t u)) = ⟪cheegerHeat h t f,u⟫_ℝ := by
  rw [integral_densityMeasure_L2 _ _ (cheegerHeat_nonneg h ht u hun)]
  exact ((cheegerHeat_symmetric h t) f u).symm

variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.heatProbability_coe {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) {t : ℝ} (ht : 0 ≤ t) :
    (hcd.heatProbability hN hfull hfin o h u hun hm t:Measure X) = densityMeasure m (cheegerHeat h t u) := by
  simp only [heatProbability,integrableDensityProbability,max_eq_left ht]
  rfl
end WeakHessian

end
end InlinedFile75

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma weighted_pairing {V f g : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hg : MemLp (fun x => g x*Real.exp (-V x)) 2 m) :
    Integrable (fun x => f x*g x) m ∧ ‖∫ x,f x*g x ∂m‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*‖hg.toLp (fun x => g x*Real.exp (-V x))‖ := by
  have he (x : X) : (f x*Real.exp (V x))*(g x*Real.exp (-V x)) = f x*g x := by
    calc
      _ = (f x*g x)*(Real.exp (V x)*Real.exp (-V x)) := by ring
      _ = _ := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  refine ⟨(hf.integrable_mul hg).congr (ae_of_all _ he),?_⟩
  have hin : (∫ x,f x*g x ∂m) =
      ⟪hf.toLp (fun x => f x*Real.exp (V x)),hg.toLp (fun x => g x*Real.exp (-V x))⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x h1 h2
    rw [h1,h2]
    simp only [RCLike.inner_apply,conj_trivial]
    convert (he x).symm using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hin]
  exact norm_inner_le_norm _ _
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_GeneratorSubgradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile46
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_eq_square_sqrt (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x) :
    densityMeasure m u = squareDensityMeasure m (fun x => Real.sqrt (u x)) := by
  apply withDensity_congr_ae
  filter_upwards [hun] with x hx
  rw [Real.sq_sqrt hx]

end WeakHessian

end
end InlinedFile46

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile48
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsOptimalCoupling.quadraticWassersteinSq_eq {μ ν : Measure X} {q : Measure (X×X)}
    (hq : IsOptimalCoupling q μ ν) : quadraticWassersteinSq μ ν = (QuadraticTransportCost q).toReal := by
  unfold quadraticWassersteinSq
  congr 1
  exact le_antisymm (iInf_le_of_le q (iInf_le _ hq.1))
    (le_iInf fun q' => le_iInf fun hq' => hq.2 q' hq')

variable [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [SigmaFinite m] in
lemma densityMeasure_quadratic_integrable (o : X) (T : ℝ≥0) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) {V : X → ℝ}
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    Integrable (fun x => (dist x o+T)^2) (densityMeasure m u) := by
  rw [densityMeasure_eq_square_sqrt u hun]
  apply (squareDensity_integrable (Lp.stronglyMeasurable u |>.measurable.sqrt)).mpr
  exact (weighted_pairing hU hW).1.congr (hun.mono fun x hx => by simp only [Real.sq_sqrt hx])
end WeakHessian

end
end InlinedFile48

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CostExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile57
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma hopf_dual_le_coupling_cost (μ ν : ProbabilityMeasure X)
    {q : Measure (X×X)} (hq : IsCoupling q μ ν) (hqt : QuadraticTransportCost q ≠ ∞)
    (f : X →ᵇ ℝ) :
    (∫ x,hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X)) ≤ (QuadraticTransportCost q).toReal/2 := by
  let Q := boundedHopfMap f 1
  have hqp : IsProbabilityMeasure q := by
    constructor
    have H := congrArg (fun r : Measure X => r univ) hq.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using H
  let := hqp
  have he : (Q:X → ℝ) = hopfLax f 1 := funext (boundedHopfMap_apply_pos f (by norm_num))
  have iQ : Integrable (fun p : X×X => Q p.1) q := Integrable.of_bound
    (Q.continuous.comp continuous_fst).aestronglyMeasurable ‖Q‖ (ae_of_all _ fun p => Q.norm_coe_le_norm p.1)
  have iF : Integrable (fun p : X×X => f p.2) q := Integrable.of_bound
    (f.continuous.comp continuous_snd).aestronglyMeasurable ‖f‖ (ae_of_all _ fun p => f.norm_coe_le_norm p.2)
  have H : (∫ p : X×X,Q p.1-f p.2 ∂q) ≤ (∫ p : X×X,dist p.1 p.2^2 ∂q)/2 := by
    apply (integral_mono (iQ.sub iF) ((integrable_squared_distance_of_cost hqt).div_const 2) ?_).trans_eq (integral_div _ _)
    intro p
    rw [he]
    have H := hopfLax_le_objective (fun x => (boundedContinuous_bounds f x).1) (by norm_num : (0:ℝ)<1) p.1 p.2
    simp only [hopfObjective,mul_one] at H
    dsimp only [Pi.sub_apply]
    linarith
  rw [integral_sub iQ iF,← integral_map measurable_fst.aemeasurable Q.continuous.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable,hq.1,hq.2,he] at H
  rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  exact H

lemma exists_optimal_coupling_of_finite (μ ν : ProbabilityMeasure X)
    {p : Measure (X×X)} (hp : IsCoupling p μ ν) (hpt : QuadraticTransportCost p ≠ ∞) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ := by
  let I : ℝ≥0∞ := ⨅ q : Measure (X×X),⨅ _ : IsCoupling q μ ν,QuadraticTransportCost q
  have hI : I ≠ ∞ := ne_top_of_le_ne_top hpt (iInf_le_of_le p (iInf_le _ hp))
  have H (f : X →ᵇ ℝ) : (∫ x,hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X)) ≤ I.toReal/2 := by
    let D := (∫ x,hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X))
    have hd : ENNReal.ofReal (2*D) ≤ I := by
      apply le_iInf; intro q; apply le_iInf; intro hq
      by_cases hqt : QuadraticTransportCost q = ∞
      · rw [hqt]; exact le_top
      · apply (ENNReal.ofReal_le_iff_le_toReal hqt).mpr
        have J := hopf_dual_le_coupling_cost μ ν hq hqt f
        dsimp only [D]; linarith
    have J := ENNReal.toReal_mono hI hd
    have : 2*D ≤ I.toReal := by
      by_cases hD : 0 ≤ 2*D
      · rwa [ENNReal.toReal_ofReal hD] at J
      · exact (le_of_lt (lt_of_not_ge hD)).trans ENNReal.toReal_nonneg
    dsimp only [D] at this
    linarith
  obtain ⟨q,hqp,hq0,hq1,hcost⟩ := exists_proper_coupling_cost_of_hopf_bound
    (μ:Measure X) (ν:Measure X) I.toReal (fun f _ => H f)
  rw [ENNReal.ofReal_toReal hI] at hcost
  exact ⟨q,hqp,⟨⟨hq0,hq1⟩,fun r hr => hcost.trans (iInf_le_of_le r (iInf_le _ hr))⟩,
    ne_top_of_le_ne_top hI hcost⟩
end WeakHessian

end
end InlinedFile57

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CostMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile58
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] in
lemma cost_ne_top_iff_integrable_sq {q : Measure (X×X)} :
    QuadraticTransportCost q ≠ ∞ ↔ Integrable (fun p : X×X => dist p.1 p.2^2) q := by
  simpa only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg] using
    lintegral_ofReal_ne_top_iff_integrable
      (measurable_fst.dist measurable_snd |>.pow_const 2).aestronglyMeasurable
      (ae_of_all q fun p : X×X => sq_nonneg (dist p.1 p.2))

lemma product_coupling_finite_cost (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X)) :
    IsCoupling ((μ:Measure X).prod (ν:Measure X)) μ ν ∧
      QuadraticTransportCost ((μ:Measure X).prod (ν:Measure X)) ≠ ∞ := by
  refine ⟨⟨by simp [Measure.map_fst_prod],by simp [Measure.map_snd_prod]⟩,?_⟩
  apply cost_ne_top_iff_integrable_sq.mpr
  apply (((hμ.comp_fst (ν:Measure X)).add (hν.comp_snd (μ:Measure X))).const_mul 2).mono' (by fun_prop)
  exact ae_of_all _ fun p => by
    change |dist p.1 p.2^2| ≤ 2*(dist p.1 o^2+dist p.2 o^2)
    rw [abs_of_nonneg (sq_nonneg _)]
    have H := dist_triangle p.1 o p.2
    rw [dist_comm o p.2] at H
    nlinarith [dist_nonneg (x := p.1) (y := p.2),sq_nonneg (dist p.1 o-dist p.2 o)]

lemma exists_optimal_coupling_of_moments (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X)) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ :=
  exists_optimal_coupling_of_finite μ ν (product_coupling_finite_cost μ ν o hμ hν).1
    (product_coupling_finite_cost μ ν o hμ hν).2

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma quadraticWassersteinSq_le_cost {μ ν : Measure X} {q : Measure (X×X)}
    (hq : IsCoupling q μ ν) (hqt : QuadraticTransportCost q ≠ ∞) :
    quadraticWassersteinSq μ ν ≤ (QuadraticTransportCost q).toReal :=
  ENNReal.toReal_mono hqt (iInf_le_of_le q (iInf_le _ hq))

end WeakHessian

end
end InlinedFile58

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_BoundedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile60
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadraticWassersteinSq_le_of_balls (μ ν : ProbabilityMeasure X) (a b : X) {r s : ℝ}
    (_hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hμ : ∀ᵐ x ∂(μ:Measure X),dist x a ≤ r) (hν : ∀ᵐ x ∂(ν:Measure X),dist x b ≤ s) :
    quadraticWassersteinSq (μ:Measure X) (ν:Measure X) ≤ (r+s+dist a b)^2 := by
  let q : Measure (X×X) := (μ:Measure X).prod (ν:Measure X)
  have hq : IsCoupling q μ ν := ⟨by simp [q],by simp [q]⟩
  have hc : ∀ᵐ p ∂q,dist p.1 p.2 ≤ r+s+dist a b := by
    have hu : ∀ᵐ p : X×X ∂q,dist p.1 a ≤ r := ae_of_ae_map measurable_fst.aemeasurable (by rw [hq.1]; exact hμ)
    have hv : ∀ᵐ p : X×X ∂q,dist p.2 b ≤ s := ae_of_ae_map measurable_snd.aemeasurable (by rw [hq.2]; exact hν)
    filter_upwards [hu,hv] with p hp hq
    have h1 := dist_triangle p.1 a p.2
    have h2 := dist_triangle a b p.2
    rw [dist_comm b p.2] at h2
    linarith
  have hI : Integrable (fun p : X×X => dist p.1 p.2^2) q := Integrable.of_bound (by fun_prop) ((r+s+dist a b)^2) (hc.mono fun p hp => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ dist_nonneg hp 2)
  have hqt : QuadraticTransportCost q ≠ ∞ := (cost_ne_top_iff_integrable_sq).mpr hI
  apply (quadraticWassersteinSq_le_cost hq hqt).trans
  rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  apply (integral_mono_ae hI (integrable_const ((r+s+dist a b)^2))
    (hc.mono fun p hp => pow_le_pow_left₀ dist_nonneg hp 2)).trans_eq
  simp [q]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_ae_ball {m : Measure X} (u : Lp ℝ 2 m) (a : X) {r : ℝ}
    (hu : ∀ᵐ x ∂m,r < dist x a → u x = 0) :
    ∀ᵐ x ∂densityMeasure m u,dist x a ≤ r := by
  apply (ae_withDensity_iff (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)).mpr
  filter_upwards [hu] with x hx hn
  by_contra H
  have hzero := hx (lt_of_not_ge H)
  exact hn (by rw [hzero,ENNReal.ofReal_zero])
end WeakHessian

end
end InlinedFile60

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile69
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma densityMeasure_le_const {u : Lp ℝ 2 m} {B : ℝ} (hu : ∀ᵐ x ∂m,u x ≤ B) :
    densityMeasure m u ≤ ENNReal.ofReal B • m := by
  rw [densityMeasure,← withDensity_const]
  exact withDensity_mono (hu.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

end WeakHessian

end
end InlinedFile69

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Confinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile64
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma polynomial_exp_bound {a r T : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hT : 0 ≤ T) :
    (r+T)^2*Real.exp (-(a*r)) ≤ 4/a^2+2*T^2 := by
  have hE := Real.pow_div_factorial_le_exp (a*r) (mul_nonneg ha.le hr) 2
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, pow_two] at hE
  have hE' := mul_le_mul_of_nonneg_right hE (Real.exp_pos (-(a*r))).le
  have he : Real.exp (a*r)*Real.exp (-(a*r)) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hE'
  have hsq : r^2*Real.exp (-(a*r)) ≤ 2/a^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith
  have hsmall : Real.exp (-(a*r)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le hr))
  have hab : (r+T)^2 ≤ 2*r^2+2*T^2 := by nlinarith [sq_nonneg (r-T)]
  have H := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-(a*r))).le
  have H' := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hT 2)
  rw [show 4/a^2 = 2*(2/a^2) by ring]
  nlinarith

omit [ProperSpace X] in
lemma CurvatureDimension.exists_comparison_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => Real.exp (-(a*dist x o/2))) 2 m ∧
      Integrable (fun x => Real.exp (-(a*dist x o/2))) m ∧
      ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-(a*dist x o))) 2 m ∧
        MemLp (fun x => (dist x o+T)*Real.exp (-(a*dist x o))) 2 m := by
  obtain ⟨a,ha,hi,h2,hD,hh,hhi⟩ := hcd.exists_strong_entropy_confinement hN hfull hfin o
  have he (x : X) : Real.exp (-(2*a*dist x o)) ≤ Real.exp (-(a*dist x o)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [dist_nonneg (x := x) (y := o)]
  have hi' : Integrable (fun x => Real.exp (-(2*a*dist x o))) m := hi.mono' (by fun_prop)
    (ae_of_all _ fun x => by simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using he x)
  have h2' : MemLp (fun x => Real.exp (-(2*a*dist x o))) 2 m := h2.mono (by fun_prop)
    (ae_of_all _ fun x => by simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using he x)
  have hD' : MemLp (fun x => (2*a*dist x o)*Real.exp (-(2*a*dist x o))) 2 m := by
    apply (hD.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*a*dist x o)*Real.exp (-(2*a*dist x o))| ≤ |2*((a*dist x o)*Real.exp (-(a*dist x o)))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (he x) (by positivity : 0 ≤ 2*a*dist x o)]
  refine ⟨2*a,by positivity,hi',h2',hD',?_,?_,?_⟩
  · convert! h2 using 1; funext x; congr 1; ring
  · convert! hi using 1; funext x; congr 1; ring
  intro T
  have hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-(2*a*dist x o))) 2 m := by
    apply (h2.const_mul (4/a^2+2*(T:ℝ)^2)).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(dist x o+T)^2*Real.exp (-(2*a*dist x o))| ≤ |(4/a^2+2*(T:ℝ)^2)*Real.exp (-(a*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity),
        show -(2*a*dist x o) = -(a*dist x o)+(-(a*dist x o)) by ring,Real.exp_add,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (polynomial_exp_bound ha dist_nonneg T.coe_nonneg) (Real.exp_pos _).le
  refine ⟨hW,?_⟩
  apply (h2'.add hW).mono (by fun_prop)
  exact ae_of_all _ fun x => by
    simp only [Pi.add_apply,Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    have H : dist x o+T ≤ 1+(dist x o+T)^2 := by nlinarith [sq_nonneg (dist x o+T-1/2)]
    nlinarith [mul_le_mul_of_nonneg_right H (Real.exp_pos (-(2*a*dist x o))).le]

omit [ProperSpace X] in
lemma memLp_exp_weight_of_supported (u : Lp ℝ 2 m) (o : X) {R a : ℝ}
    (ha : 0 ≤ a) (hs : ∀ᵐ x ∂m,dist x o > R → u x = 0) :
    MemLp (fun x => u x*Real.exp (a*dist x o)) 2 m := by
  apply ((Lp.memLp u).const_mul (Real.exp (a*R))).mono (by fun_prop)
  filter_upwards [hs] with x hx
  change |u x*Real.exp (a*dist x o)| ≤ |Real.exp (a*R)*u x|
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
  by_cases hR : dist x o ≤ R
  · rw [mul_comm (Real.exp (a*R))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR ha)) (abs_nonneg _)
  · rw [hx (lt_of_not_ge hR)]; simp

end WeakHessian

end
end InlinedFile64

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LipschitzMulDist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_mul_dist (o : X) (a : ℝ) :
    LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |a*dist x o-a*dist y o| ≤ |a| * dist x y
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CompactContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile74
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_contraction_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C R S : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    (hsu : ∀ᵐ x ∂m,dist x o > R → u x = 0) (hsv : ∀ᵐ x ∂m,dist x o > S → v x = 0)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (2*K*b)*quadraticWassersteinSq (μ b:Measure X) (ν b:Measure X) ≤
      quadraticWassersteinSq (μ 0:Measure X) (ν 0:Measure X) := by
  obtain ⟨a,ha,hi,h2,hD,hh,hhi,hW⟩ := hrcd.1.exists_comparison_confinement hN hfull hfin o
  exact hrcd.cheegerHeat_contraction_weighted hN hfull hfin o h u v hun hvn hum hvm hB hC huB hvC
    (lipschitz_mul_dist o a) (memLp_exp_weight_of_supported u o ha.le hsu)
    (memLp_exp_weight_of_supported v o ha.le hsv) h2 hD hi hh hhi hW μ ν hμ hν hb
end WeakHessian

end
end InlinedFile74

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LipschitzTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile59
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma lipschitz_integral_sub_le_cost (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {B : ℝ} (hB : ∀ x,|f x| ≤ B) :
    |(∫ x,f x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X))| ≤
      (L:ℝ)*Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X)) := by
  obtain ⟨q,hqp,hq,hqt⟩ := exists_optimal_coupling_of_moments μ ν o hμ hν
  let : IsProbabilityMeasure q := hqp
  have hfq : Integrable (fun p : X×X => f p.1) q := Integrable.of_bound
    (hf.continuous.comp continuous_fst).aestronglyMeasurable B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p.1)
  have hgq : Integrable (fun p : X×X => f p.2) q := Integrable.of_bound
    (hf.continuous.comp continuous_snd).aestronglyMeasurable B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hB p.2)
  have hd : MemLp (fun p : X×X => dist p.1 p.2) 2 q :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hqt)
  have hI : (∫ p : X×X,dist p.1 p.2 ∂q) ≤ Real.sqrt (∫ p : X×X,dist p.1 p.2^2 ∂q) := by
    simpa using
      integral_mul_le_sqrt_integral_sq hd (memLp_const (1:ℝ))
  have hF : |(∫ p : X×X,f p.1-f p.2 ∂q)| ≤ (L:ℝ)*(∫ p : X×X,dist p.1 p.2 ∂q) := by
    apply abs_integral_le_integral_abs.trans
    rw [← integral_const_mul]
    apply integral_mono_ae (hfq.sub hgq).abs ((hd.integrable (by norm_num)).const_mul (L:ℝ))
    exact ae_of_all _ fun p => by simpa only [Real.dist_eq,Pi.sub_apply] using hf.dist_le_mul p.1 p.2
  rw [integral_sub hfq hgq,← integral_map measurable_fst.aemeasurable hf.continuous.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable,hq.1.1,hq.1.2] at hF
  have he : quadraticWassersteinSq (μ:Measure X) (ν:Measure X) = ∫ p : X×X,dist p.1 p.2^2 ∂q := by
    rw [hq.quadraticWassersteinSq_eq,quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [he]
  exact hF.trans (mul_le_mul_of_nonneg_left hI L.coe_nonneg)
end WeakHessian

end
end InlinedFile59

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CompactHeatPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile77
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [SigmaFinite m] in
lemma CurvatureDimension.heatProbability_moment {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) {R : ℝ} (hsu : ∀ᵐ x ∂m,R < dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => dist x o^2) (hcd.heatProbability hN hfull hfin o h u hun hm t:Measure X) := by
  rw [hcd.heatProbability_coe hN hfull hfin o h u hun hm ht]
  obtain ⟨a,ha,hi,h2,hD,hh,hhi,hW⟩ := hcd.exists_comparison_confinement hN hfull hfin o
  simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _
    (cheegerHeat_nonneg h ht u hun)
    (hcd.cheegerHeat_weighted hfin o h u (lipschitz_mul_dist o a)
      (memLp_exp_weight_of_supported u o ha.le hsu) ht).1 (hW 0).1

lemma sqrt_transport_contraction {c R z : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    (h : Real.exp (2*z)*c ≤ R^2) : Real.sqrt c ≤ Real.exp (-z)*R := by
  have he : Real.exp (2*z) = (Real.exp z)^2 := by rw [two_mul,Real.exp_add,pow_two]
  rw [he] at h
  have hsq := Real.sq_sqrt hc
  have hmul : Real.exp z*Real.sqrt c ≤ R := by
    nlinarith [Real.exp_pos z,Real.sqrt_nonneg c]
  have H := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (-z)).le
  simpa only [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul] using H

lemma RCD.cheegerHeat_pairing_balls {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) {D : ℝ} (hfB : ∀ x,|f x| ≤ D)
    (u v : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    (a b : X) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsu : ∀ᵐ x ∂m,r < dist x a → u x = 0) (hsv : ∀ᵐ x ∂m,s < dist x b → v x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    |⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ-⟪cheegerHeat h t (hf2.toLp f),v⟫_ℝ| ≤
      (L:ℝ)*Real.exp (-K*t)*(r+s+dist a b) := by
  let μ := hrcd.1.heatProbability hN hfull hfin a h u hun hum
  let ν := hrcd.1.heatProbability hN hfull hfin a h v hvn hvm
  have hμ (t : ℝ) (ht : 0 ≤ t) : (μ t:Measure X) = densityMeasure m (cheegerHeat h t u) :=
    hrcd.1.heatProbability_coe hN hfull hfin a h u hun hum ht
  have hν (t : ℝ) (ht : 0 ≤ t) : (ν t:Measure X) = densityMeasure m (cheegerHeat h t v) :=
    hrcd.1.heatProbability_coe hN hfull hfin a h v hvn hvm ht
  have hsv' : ∀ᵐ x ∂m,s+dist b a < dist x a → v x = 0 := by
    filter_upwards [hsv] with x hx hh
    apply hx
    have := dist_triangle x b a
    linarith
  have hμm := hrcd.1.heatProbability_moment hN hfull hfin a h u hun hum hsu ht
  have hνm := hrcd.1.heatProbability_moment hN hfull hfin a h v hvn hvm hsv' ht
  have H := lipschitz_integral_sub_le_cost (μ t) (ν t) a hμm hνm hf hfB
  have hc := hrcd.cheegerHeat_contraction_compact hN hfull hfin a h u v hun hvn hum hvm
    hB hC huB hvC hsu hsv' μ ν hμ hν ht
  have hμ0 : (μ 0:Measure X) = densityMeasure m u := by rw [hμ 0 le_rfl,cheegerHeat_zero h]; rfl
  have hν0 : (ν 0:Measure X) = densityMeasure m v := by rw [hν 0 le_rfl,cheegerHeat_zero h]; rfl
  have h0 := quadraticWassersteinSq_le_of_balls (μ 0) (ν 0) a b hr hs
    (by rw [hμ0]; exact densityMeasure_ae_ball u a hsu)
    (by rw [hν0]; exact densityMeasure_ae_ball v b hsv)
  have hsq := sqrt_transport_contraction (show 0 ≤ quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X) from ENNReal.toReal_nonneg) (show 0 ≤ r+s+dist a b by positivity)
    (show Real.exp (2*(K*t))*quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X) ≤ (r+s+dist a b)^2 by
      simpa only [mul_assoc] using hc.trans h0)
  have huI : (∫ x,f x ∂(μ t:Measure X)) = ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ := by
    rw [hμ t ht,← cheegerHeat_density_duality h u _ ht hun]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hf2.coeFn_toLp.symm
  have hvI : (∫ x,f x ∂(ν t:Measure X)) = ⟪cheegerHeat h t (hf2.toLp f),v⟫_ℝ := by
    rw [hν t ht,← cheegerHeat_density_duality h v _ ht hvn]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hf2.coeFn_toLp.symm
  rw [huI,hvI] at H
  exact H.trans (by simpa only [neg_mul,mul_assoc] using mul_le_mul_of_nonneg_left hsq L.coe_nonneg)
end WeakHessian

end
end InlinedFile77

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_DualHeatPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile78
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadratic_dual_integral_le_cost (μ ν : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C A : ℝ} (hfB : ∀ x,|f x| ≤ B) (hgC : ∀ x,|g x| ≤ C)
    (hdual : ∀ x y,f x-g y ≤ A*dist x y^2) :
    (∫ x,f x ∂(μ:Measure X))-(∫ x,g x ∂(ν:Measure X)) ≤
      A*quadraticWassersteinSq (μ:Measure X) (ν:Measure X) := by
  obtain ⟨q,hqp,hq,hqt⟩ := exists_optimal_coupling_of_moments μ ν o hμ hν
  let : IsProbabilityMeasure q := hqp
  have hfq : Integrable (fun p : X×X => f p.1) q := Integrable.of_bound
    (hf.comp continuous_fst).aestronglyMeasurable B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hfB p.1)
  have hgq : Integrable (fun p : X×X => g p.2) q := Integrable.of_bound
    (hg.comp continuous_snd).aestronglyMeasurable C (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hgC p.2)
  have H := integral_mono_ae (hfq.sub hgq)
    ((integrable_squared_distance_of_cost hqt).const_mul A) (ae_of_all _ fun p : X×X => hdual p.1 p.2)
  simp only [Pi.sub_apply] at H
  rw [integral_sub hfq hgq,integral_const_mul,
    ← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,hq.1.1,hq.1.2] at H
  have he : quadraticWassersteinSq (μ:Measure X) (ν:Measure X) = ∫ p : X×X,dist p.1 p.2^2 ∂q := by
    rw [hq.quadraticWassersteinSq_eq,quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  simpa only [he] using H

variable {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_dual_pairing_balls {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    {D E A : ℝ} (hfB : ∀ x,|f x| ≤ D) (hgB : ∀ x,|g x| ≤ E) (hA : 0 ≤ A)
    (hdual : ∀ x y,f x-g y ≤ A*dist x y^2)
    (u v : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    (a b : X) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsu : ∀ᵐ x ∂m,r < dist x a → u x = 0) (hsv : ∀ᵐ x ∂m,s < dist x b → v x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ-⟪cheegerHeat h t (hg2.toLp g),v⟫_ℝ ≤
      A*Real.exp (-2*K*t)*(r+s+dist a b)^2 := by
  let μ := hrcd.1.heatProbability hN hfull hfin a h u hun hum
  let ν := hrcd.1.heatProbability hN hfull hfin a h v hvn hvm
  have hμ (t : ℝ) (ht : 0 ≤ t) : (μ t:Measure X) = densityMeasure m (cheegerHeat h t u) :=
    hrcd.1.heatProbability_coe hN hfull hfin a h u hun hum ht
  have hν (t : ℝ) (ht : 0 ≤ t) : (ν t:Measure X) = densityMeasure m (cheegerHeat h t v) :=
    hrcd.1.heatProbability_coe hN hfull hfin a h v hvn hvm ht
  have hsv' : ∀ᵐ x ∂m,s+dist b a < dist x a → v x = 0 := by
    filter_upwards [hsv] with x hx hh
    apply hx
    have := dist_triangle x b a
    linarith
  have H := quadratic_dual_integral_le_cost (μ t) (ν t) a
    (hrcd.1.heatProbability_moment hN hfull hfin a h u hun hum hsu ht)
    (hrcd.1.heatProbability_moment hN hfull hfin a h v hvn hvm hsv' ht) hf hg hfB hgB hdual
  have hc := hrcd.cheegerHeat_contraction_compact hN hfull hfin a h u v hun hvn hum hvm
    hB hC huB hvC hsu hsv' μ ν hμ hν ht
  have hμ0 : (μ 0:Measure X) = densityMeasure m u := by rw [hμ 0 le_rfl,cheegerHeat_zero h]; rfl
  have hν0 : (ν 0:Measure X) = densityMeasure m v := by rw [hν 0 le_rfl,cheegerHeat_zero h]; rfl
  have h0 := quadraticWassersteinSq_le_of_balls (μ 0) (ν 0) a b hr hs
    (by rw [hμ0]; exact densityMeasure_ae_ball u a hsu)
    (by rw [hν0]; exact densityMeasure_ae_ball v b hsv)
  have hc' : quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X) ≤
      Real.exp (-2*K*t)*(r+s+dist a b)^2 := by
    have H := mul_le_mul_of_nonneg_left (hc.trans h0) (Real.exp_pos (-2*K*t)).le
    have he : Real.exp (-2*K*t)*Real.exp (2*K*t) = 1 := by
      rw [← Real.exp_add, show -2*K*t+2*K*t = 0 by ring, Real.exp_zero]
    simpa only [← mul_assoc,he,one_mul] using H
  have huI : (∫ x,f x ∂(μ t:Measure X)) = ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ := by
    rw [hμ t ht,← cheegerHeat_density_duality h u _ ht hun]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hf2.coeFn_toLp.symm
  have hvI : (∫ x,g x ∂(ν t:Measure X)) = ⟪cheegerHeat h t (hg2.toLp g),v⟫_ℝ := by
    rw [hν t ht,← cheegerHeat_density_duality h v _ ht hvn]
    apply integral_congr_ae
    exact (densityMeasure_ac m _).ae_le hg2.coeFn_toLp.symm
  rw [huI,hvI] at H
  exact H.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc' hA)
end WeakHessian

end
end InlinedFile78

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEnergyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile105
noncomputable section
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ClosedQuadraticEnergy.energy_sub_tendsto_zero {Q : E → ℝ≥0∞}
    (hQ : ClosedQuadraticEnergy Q) {ι : Type*} {l : Filter ι} {f : ι → E} {u : E}
    (hu : Q u < ∞) (hf : Tendsto f l (𝓝 u)) (hb : ∀ᶠ i in l, Q (f i) ≤ Q u) :
    Tendsto (fun i => (Q (f i-u)).toReal) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsum := hf.add_const u
  let r := 4*(Q u).toReal-ε
  have h2 := hQ.add_lt_top hu hu
  have he2 : (Q (u+u)).toReal = 4*(Q u).toReal := by
    rw [show u+u = (2:ℝ) • u by simp [two_smul],hQ.smul,ENNReal.toReal_mul]
    norm_num
  have HH (i : ι) (hi : Q (f i) ≤ Q u) :
      (Q (f i+u)).toReal+(Q (f i-u)).toReal ≤ 4*(Q u).toReal := by
    have hfi := hi.trans_lt hu
    have hp := congrArg ENNReal.toReal (hQ.parallelogram (f i) u hfi hu)
    rw [ENNReal.toReal_add (hQ.add_lt_top hfi hu).ne (hQ.sub_lt_top hfi hu).ne,
      ENNReal.toReal_add (by finiteness) (by finiteness)] at hp
    simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at hp
    have he := ENNReal.toReal_mono hu.ne hi
    linarith
  by_cases hr : r < 0
  · filter_upwards [hb] with i hi
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg]
    have hs := ENNReal.toReal_nonneg (a := Q (f i+u))
    dsimp only [r] at hr
    linarith [HH i hi]
  · have hr0 : 0 ≤ r := le_of_not_gt hr
    have hh : ENNReal.ofReal r < Q (u+u) := by
      rw [← ENNReal.ofReal_toReal h2.ne]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0).mpr
      rw [he2]
      dsimp only [r]
      linarith
    have hev := hsum.eventually ((hQ.lowerSemicontinuous.lowerSemicontinuousAt (u+u)) _ hh)
    filter_upwards [hb,hev] with i hi hs
    have hfi := hi.trans_lt hu
    have hs' := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hQ.add_lt_top hfi hu).ne).mpr hs
    rw [ENNReal.toReal_ofReal hr0] at hs'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg]
    dsimp only [r] at hs'
    linarith [HH i hi]
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma cheegerHeat_energy_sub_zero (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u : Lp ℝ 2 m} (hu : cheegerEnergy m (u : X → ℝ) < ∞) :
    Tendsto (fun t => (cheegerEnergy m (cheegerHeat h t u-u : Lp ℝ 2 m)).toReal)
      (𝓝[≥] 0) (𝓝 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  exact (cheeger_closedQuadraticEnergy h).energy_sub_tendsto_zero hu
    (cheegerHeat_strong_zero h u) (by filter_upwards [self_mem_nhdsWithin] with t ht; exact cheegerHeat_energy_le h ht u)
end WeakHessian

end
end InlinedFile105

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEnergyQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile103
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_right_of_generator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m} {t : ℝ} (ht : 0 ≤ t)
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A) :
    HasDerivWithinAt (fun s => cheegerHeat h s u) A (Ici t) t := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hg := (cheeger_closedQuadraticEnergy h).heat_deriv_form_zero m (cheeger_domain_dense h) hu
  change HasDerivWithinAt (fun r => cheegerHeat h r (cheegerHeat h t u)) A (Ici 0) 0 at hg
  have hc : HasDerivWithinAt (fun s : ℝ => s-t) 1 (Ici t) t :=
    (hasDerivWithinAt_id t (Ici t)).sub_const t
  have H := hg.scomp_of_eq (h := fun s : ℝ => s-t) t hc
    (show MapsTo (fun s : ℝ => s-t) (Ici t) (Ici 0) from
      fun s hs => (show 0 ≤ s-t from sub_nonneg.mpr hs)) (by simp)
  simp only [one_smul,Function.comp_def] at H
  apply H.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have he := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (cheegerHeat_add h (sub_nonneg.mpr hs) ht)
    simpa only [mul_apply_eq_comp,sub_add_cancel] using he
  · rw [sub_self,cheegerHeat_zero,one_apply_eq_self]

end WeakHessian

end
end InlinedFile103

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatFormContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile106
noncomputable section
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma ClosedQuadraticEnergy.form_tendsto_of_energy_sub {Q : E → ℝ≥0∞}
    (hQ : ClosedQuadraticEnergy Q) {ι : Type*} {l : Filter ι}
    {f : ι → hQ.domain} {u : hQ.domain} (q : hQ.domain)
    (he : Tendsto (fun i => hQ.realEnergy (f i-u)) l (𝓝 0)) :
    Tendsto (fun i => hQ.form (f i) q) l (𝓝 (hQ.form u q)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh : Tendsto (fun i => hQ.realEnergy (f i-u)*hQ.realEnergy q) l (𝓝 0) := by
    simpa using he.mul_const (hQ.realEnergy q)
  filter_upwards [hh.eventually_lt_const (sq_pos_of_pos hε)] with i hi
  have hcs := hQ.realEnergy_quadratic.polar_cauchySchwarz (f i-u) q
  change (hQ.form (f i-u) q)^2 ≤ _ at hcs
  rw [map_sub,LinearMap.sub_apply] at hcs
  rw [Real.dist_eq,abs_lt]
  constructor <;> nlinarith
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_integral_gamma_zero {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u q : Lp ℝ 2 m}
    (hu : Sobolev m (u : X → ℝ)) (hq : Sobolev m (q : X → ℝ)) :
    Tendsto (fun t => ∫ x,gamma m (cheegerHeat h t u) q x ∂m)
      (𝓝[>] 0) (𝓝 (∫ x,gamma m (u : X → ℝ) q x ∂m)) := by
  let Q := cheeger_closedQuadraticEnergy h
  have hue : cheegerEnergy m (u : X → ℝ) < ∞ := (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp u)).mp hu
  have hqe : cheegerEnergy m (q : X → ℝ) < ∞ := (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp q)).mp hq
  let f (t : ℝ) : Q.domain := ⟨cheegerHeat h (max t 0) u,(cheegerHeat_energy_le h (le_max_right _ _) u).trans_lt hue⟩
  have hE : Tendsto (fun t => Q.realEnergy (f t-⟨u,hue⟩)) (𝓝[>] 0) (𝓝 0) := by
    have HH := (cheegerHeat_energy_sub_zero hfin h hue).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    apply HH.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change (cheegerEnergy m (cheegerHeat h t u-u : Lp ℝ 2 m)).toReal = (cheegerEnergy m (cheegerHeat h (max t 0) u-u : Lp ℝ 2 m)).toReal
    rw [max_eq_left ht.le]
  have HH := (Q.form_tendsto_of_energy_sub ⟨q,hqe⟩ hE).const_mul 2
  rw [hcd.global_integral_gamma_form hfin o h ⟨u,hue⟩ ⟨q,hqe⟩]
  apply HH.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [hcd.global_integral_gamma_form hfin o h ⟨cheegerHeat h t u,(cheegerHeat_energy_le h ht.le u).trans_lt hue⟩ ⟨q,hqe⟩]
  have hf : f t = ⟨cheegerHeat h t u,(cheegerHeat_energy_le h ht.le u).trans_lt hue⟩ := by
    apply Subtype.ext
    simp only [f,max_eq_left ht.le]
  rw [hf]

end WeakHessian

end
end InlinedFile106

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SetDensities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile76
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma setDensity_coe (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    setDensity S hS hfin =ᵐ[m] S.indicator (fun _ => (m S).toReal⁻¹) := MemLp.coeFn_toLp _

lemma setDensity_nonneg (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    ∀ᵐ x ∂m,0 ≤ setDensity S hS hfin x :=
  (setDensity_coe S hS hfin).mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => by positivity) x

lemma setDensity_bounded (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    ∀ᵐ x ∂m,|setDensity S hS hfin x| ≤ (m S).toReal⁻¹ := by
  filter_upwards [setDensity_coe S hS hfin] with x hx
  rw [hx]
  by_cases hs : x ∈ S <;> simp [hs,abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),inv_nonneg.mpr ENNReal.toReal_nonneg]

lemma setDensity_mass (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) (hpos : m S ≠ 0) :
    (∫ x,setDensity S hS hfin x ∂m) = 1 := by
  rw [integral_congr_ae (setDensity_coe S hS hfin),integral_indicator hS,integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hpos,hfin⟩)

lemma setDensity_pairing (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) (f : Lp ℝ 2 m) :
    (∫ x,setDensity S hS hfin x*f x ∂m) = (m S).toReal⁻¹*(∫ x in S,f x ∂m) := by
  rw [← integral_const_mul,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [setDensity_coe S hS hfin] with x hx
  rw [hx]
  by_cases hs : x ∈ S <;> simp [hs]

lemma setDensity_supported [MetricSpace X] (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞)
    (a : X) {r : ℝ} (hs : S ⊆ Metric.closedBall a r) :
    ∀ᵐ x ∂m,r < dist x a → setDensity S hS hfin x = 0 := by
  filter_upwards [setDensity_coe S hS hfin] with x hx hr
  rw [hx,indicator_of_notMem]
  exact fun hmem => (not_le_of_gt hr) (hs hmem)
end WeakHessian

end
end InlinedFile76

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_SpatialHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile80
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma exists_lipschitz_of_ball_averages [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    (g : Lp ℝ 2 m) {C : ℝ≥0}
    (h : ∀ x y : X, ∀ r : ℝ,0 < r →
      |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤
        (C:ℝ)*(2*r+dist x y)) :
    ∃ g' : X → ℝ,LipschitzWith C g' ∧ g' =ᵐ[m] g := by
  let S : Set X := {x | Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,g z ∂m) (𝓝[>] 0) (𝓝 (g x))}
  have hS : ∀ᵐ x ∂m,x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average m ((Lp.memLp g).locallyIntegrable (by norm_num)) 1] with x hx
    apply hx (fun _ : ℝ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.le
  have hLip : LipschitzOnWith C (g : X → ℝ) S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq]
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have H := le_of_tendsto_of_tendsto (hx.sub hy |>.abs)
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hr).add tendsto_const_nhds))
      (show ∀ᶠ r in 𝓝[>] (0:ℝ), |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤ (C:ℝ)*(2*r+dist x y) from
        by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h x y r hr)
    simpa only [mul_zero,zero_add] using H
  obtain ⟨g',hg',heq⟩ := hLip.extend_real
  exact ⟨g',hg',hS.mono fun x hx => (heq hx).symm⟩

variable [ProperSpace X] [SigmaFinite m]

lemma RCD.cheegerHeat_lipschitzVersion {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) {D : ℝ} (hfB : ∀ x,|f x| ≤ D)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] cheegerHeat h t (hf2.toLp f) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  apply exists_lipschitz_of_ball_averages
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hb (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  have H := hrcd.cheegerHeat_pairing_balls hN hfull hfin h hf hf2 hfB (u x) (u y)
    (hn x) (hn y) (hmass x) (hmass y) (by positivity) (by positivity) (hb x) (hb y) x y hr.le hr.le (hs x) (hs y) ht
  have heq (x : X) : ⟪cheegerHeat h t (hf2.toLp f),u x⟫_ℝ =
      (⨍ z in Metric.closedBall x r,cheegerHeat h t (hf2.toLp f) z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  rw [heq x,heq y] at H
  change _ ≤ (L:ℝ)*Real.exp (-K*t)*(2*r+dist x y)
  simpa only [two_mul] using H
end WeakHessian

end
end InlinedFile80

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SpatialDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile81
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FullSupport.openPosMeasure (h : FullSupport m) : Measure.IsOpenPosMeasure m :=
  ⟨fun U ho hn => (h U ho hn).ne'⟩

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma continuous_le_of_ae_le (hfull : FullSupport m) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ᵐ x ∂m,f x ≤ g x) : ∀ x,f x ≤ g x := by
  let : Measure.IsOpenPosMeasure m := hfull.openPosMeasure
  exact fun x => (isClosed_le hf hg).closure_subset (m.dense_of_ae h x)

lemma continuous_dual_of_ball_averages [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    (hfull : FullSupport m) (f g : Lp ℝ 2 m) {F G : X → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hFe : F =ᵐ[m] f) (hGe : G =ᵐ[m] g)
    {A : ℝ} (h : ∀ x y : X, ∀ r : ℝ,0 < r →
      (⨍ z in Metric.closedBall x r,f z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m) ≤
        A*(2*r+dist x y)^2) : ∀ x y,F x-G y ≤ A*dist x y^2 := by
  let : Measure.IsOpenPosMeasure m := hfull.openPosMeasure
  let S : Set X := {x | Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,f z ∂m) (𝓝[>] 0) (𝓝 (F x)) ∧
    Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,g z ∂m) (𝓝[>] 0) (𝓝 (G x))}
  have hS : ∀ᵐ x ∂m,x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average m ((Lp.memLp f).locallyIntegrable (by norm_num)) 1,
      IsUnifLocDoublingMeasure.ae_tendsto_average m ((Lp.memLp g).locallyIntegrable (by norm_num)) 1,hFe,hGe] with x hf hg heF heG
    constructor
    · rw [heF]
      apply hf (fun _ : ℝ => x) id tendsto_id
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr.le
    · rw [heG]
      apply hg (fun _ : ℝ => x) id tendsto_id
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr.le
  have HS : S ×ˢ S ⊆ {p : X×X | F p.1-G p.2 ≤ A*dist p.1 p.2^2} := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have H := le_of_tendsto_of_tendsto (hx.1.sub hy.2)
      (tendsto_const_nhds.mul (((tendsto_const_nhds.mul hr).add tendsto_const_nhds).pow 2))
      (show ∀ᶠ r in 𝓝[>] (0:ℝ),(⨍ z in Metric.closedBall x r,f z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m) ≤ A*(2*r+dist x y)^2 from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h x y r hr)
    change F x-G y ≤ A*dist x y^2
    simpa only [mul_zero,zero_add] using H
  have hclos : IsClosed {p : X×X | F p.1-G p.2 ≤ A*dist p.1 p.2^2} := isClosed_le (by fun_prop) (by fun_prop)
  exact fun x y => hclos.closure_subset (closure_mono HS ((m.dense_of_ae hS).prod (m.dense_of_ae hS) (x,y)))

variable [ProperSpace X] [SigmaFinite m]

lemma RCD.cheegerHeat_dual_pointwise {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    {D E A : ℝ} (hfB : ∀ x,|f x| ≤ D) (hgB : ∀ x,|g x| ≤ E) (hA : 0 ≤ A)
    (hdual : ∀ x y,f x-g y ≤ A*dist x y^2)
    {t : ℝ} (ht : 0 ≤ t) {F G : X → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFe : F =ᵐ[m] cheegerHeat h t (hf2.toLp f)) (hGe : G =ᵐ[m] cheegerHeat h t (hg2.toLp g)) :
    ∀ x y,F x-G y ≤ A*Real.exp (-2*K*t)*dist x y^2 := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  apply continuous_dual_of_ball_averages hfull _ _ hF hG hFe hGe
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hb (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  have H := hrcd.cheegerHeat_dual_pairing_balls hN hfull hfin h hf hg hf2 hg2 hfB hgB hA hdual
    (u x) (u y) (hn x) (hn y) (hmass x) (hmass y) (by positivity) (by positivity) (hb x) (hb y) x y hr.le hr.le (hs x) (hs y) ht
  have heq (x : X) (v : Lp ℝ 2 m) : ⟪v,u x⟫_ℝ = (⨍ z in Metric.closedBall x r,v z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  rw [heq x,heq y] at H
  simpa only [two_mul] using H

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [ProperSpace X] [SigmaFinite m] in
lemma heat_continuousVersion_bounded (hfull : FullSupport m) (h : QuadraticCheegerEnergy m)
    (f : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B) (hfb : ∀ᵐ x ∂m,|f x| ≤ B)
    {t : ℝ} (ht : 0 ≤ t) {F : X → ℝ} (hF : Continuous F)
    (hFe : F =ᵐ[m] cheegerHeat h t f) : ∀ x,|F x| ≤ B := by
  apply continuous_le_of_ae_le hfull hF.abs continuous_const
  filter_upwards [hFe,cheegerHeat_bounded h ht hB f hfb] with x hx hb
  simpa only [hx] using hb
end WeakHessian

end
end InlinedFile81

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HopfHeatCommutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile83
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.exists_boundedLipschitz_heatVersion {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (f : X →ᵇ ℝ) (hf : GloballyLipschitz (f : X → ℝ))
    (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ∃ F : X →ᵇ ℝ,GloballyLipschitz (F : X → ℝ) ∧
      F =ᵐ[m] cheegerHeat h t (hf2.toLp f) ∧ ‖F‖ ≤ ‖f‖ := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨F,hF,hFe⟩ := hrcd.cheegerHeat_lipschitzVersion hN hfull hfin h hL hf2
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) ht
  have hfb : ∀ᵐ x ∂m,|hf2.toLp f x| ≤ ‖f‖ := by
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hFb := heat_continuousVersion_bounded hfull h _ (norm_nonneg f) hfb ht hF.continuous hFe
  let F' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF.continuous ‖f‖
    (fun x => by simpa only [Real.norm_eq_abs] using hFb x)
  refine ⟨F',⟨_,hF⟩,hFe,?_⟩
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖F x‖ ≤ ‖f‖
  simpa only [Real.norm_eq_abs] using hFb x

lemma RCD.hopf_heat_commutation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (f : X →ᵇ ℝ) (hf : GloballyLipschitz (f : X → ℝ))
    (hf2 : MemLp f 2 m) {s : ℝ} (hs : 0 < s) (hQ2 : MemLp (boundedHopfMap f s) 2 m)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ F Q : X →ᵇ ℝ, GloballyLipschitz (F : X → ℝ) ∧ GloballyLipschitz (Q : X → ℝ) ∧
      F =ᵐ[m] cheegerHeat h t (hf2.toLp f) ∧
      Q =ᵐ[m] cheegerHeat h t (hQ2.toLp (boundedHopfMap f s)) ∧
      ‖F‖ ≤ ‖f‖ ∧ ∀ x,Q x ≤ hopfLax F (s*Real.exp (2*K*t)) x := by
  obtain ⟨F,hF,hFe,hFb⟩ := hrcd.exists_boundedLipschitz_heatVersion hN hfull hfin h f hf hf2 ht
  obtain ⟨Q,hQ,hQe,hQb⟩ := hrcd.exists_boundedLipschitz_heatVersion hN hfull hfin h (boundedHopfMap f s)
    (boundedHopfMap_lipschitz f hs) hQ2 ht
  refine ⟨F,Q,hF,hQ,hFe,hQe,hFb,?_⟩
  have hdual : ∀ x y,boundedHopfMap f s x-f y ≤ (1/(2*s))*dist x y^2 := by
    intro x y
    rw [boundedHopfMap_apply_pos f hs]
    have H := hopfLax_le_objective (fun x => (boundedContinuous_bounds f x).1) hs x y
    dsimp only [hopfObjective] at H
    linarith [show dist x y^2/(2*s) = (1/(2*s))*dist x y^2 by ring]
  have HD := hrcd.cheegerHeat_dual_pointwise hN hfull hfin h (boundedHopfMap f s).continuous f.continuous
    hQ2 hf2 (fun x => by simpa only [Real.norm_eq_abs] using (boundedHopfMap f s).norm_coe_le_norm x)
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (by positivity) hdual ht
    Q.continuous F.continuous hQe hFe
  have he : (1/(2*s))*Real.exp (-2*K*t) = 1/(2*(s*Real.exp (2*K*t))) := by
    have hn : -2*K*t = -(2*K*t) := by ring
    rw [hn,Real.exp_neg]
    field_simp
  intro x
  apply le_csInf ⟨hopfObjective F (s*Real.exp (2*K*t)) x x,mem_range_self x⟩
  rintro z ⟨y,rfl⟩
  have H := HD x y
  rw [he] at H
  dsimp only [hopfObjective]
  linarith [show dist x y^2/(2*(s*Real.exp (2*K*t))) = (1/(2*(s*Real.exp (2*K*t))))*dist x y^2 by ring]

end WeakHessian

end
end InlinedFile83

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HopfEnergyLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile87
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma continuousOn_integral_boundedHopfMap (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (fun s => ∫ x,boundedHopfMap f s x ∂m) (Ici 0) := by
  intro t ht
  have H := tendsto_bounded_pairing_L1 (m := m)
    (u := fun _ : ℝ => fun _ : X => (1:ℝ)) (v := fun _ : X => (1:ℝ))
    (fun _ => integrable_const _) (integrable_const _)
    (q := boundedHopfMap f) (r := boundedHopfMap f t)
    (continuousOn_boundedHopfMap hf t ht) (by simpa using (tendsto_const_nhds (x := (0:ℝ)) : Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[Ici 0] t) (𝓝 0)))
  change Tendsto _ _ _
  simpa using H

lemma integral_hopf_positive_slope (f : X →ᵇ ℝ) {t r : ℝ} (ht : 0 < t)
    (hr : -(∫ x,(localSlope (boundedHopfMap f t) x).toReal^2 ∂m)/2 < r) :
    ∀ᶠ s in 𝓝[>] t,slope (fun z => ∫ x,boundedHopfMap f z x ∂m) t s < r := by
  let D := ∫ x,(localSlope (boundedHopfMap f t) x).toReal^2 ∂m
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] t) (𝓝 t) := tendsto_id.mono_left nhdsWithin_le_nhds
  have Hlim : Tendsto (fun s : ℝ => -t/(2*s)*D) (𝓝[>] t) (𝓝 (-D/2)) := by
    convert ((tendsto_const_nhds (x := -t)).div (hid.const_mul 2) (by positivity : 2*t ≠ 0)).mul_const D using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    field_simp
  filter_upwards [Hlim.eventually_lt_const hr,self_mem_nhdsWithin] with s hs hst
  have H := boundedHopfMap_L1_increment (m := m) (fun _ _ => measure_lt_top _ _) f
    (u := fun _ : X => (1:ℝ)) (integrable_const _) (ae_of_all _ fun _ => zero_le_one) ht hst.le
  simp only [BoundedContinuousFunction.sub_apply,one_mul] at H
  rw [integral_sub ((boundedHopfMap f s).integrable (μ := m)) ((boundedHopfMap f t).integrable (μ := m))] at H
  rw [slope_def_field]
  apply lt_of_le_of_lt _ hs
  apply (div_le_iff₀ (sub_pos.mpr hst)).mpr
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [D]
  ring

lemma integral_hopf_falling (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {a b : ℝ} (hb : 0 < b)
    (hE : ∀ t,0 < t → t < b → a ≤ (∫ x,(localSlope (boundedHopfMap f t) x).toReal^2 ∂m)/2) :
    (∫ x,boundedHopfMap f b x ∂m) ≤ (∫ x,f x ∂m)-a*b := by
  let J (t : ℝ) := ∫ x,boundedHopfMap f t x ∂m
  have hJ := continuousOn_integral_boundedHopfMap (m := m) f hf
  have H (c : ℝ) (hc : 0 < c) (hcb : c ≤ b) : J b ≤ J c-a*(b-c) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary (f := J)
      (B := fun z => J c-a*(z-c)) (B' := fun _ => -a)
      (hJ.mono (fun _ hx => hc.le.trans hx.1)) (by simp) (by fun_prop)
      (fun x _ => by
        have hd := (((hasDerivAt_id x).sub_const c).const_mul a).const_sub (J c)
        convert! hd.hasDerivWithinAt (s := Ici x) using 1
        all_goals try with_reducible_and_instances rfl
        simp only [mul_one])
      _ ⟨hcb,le_rfl⟩
    intro x hx r hr
    exact (integral_hopf_positive_slope f (hc.trans_le hx.1)
      (lt_of_le_of_lt (by linarith [hE x (hc.trans_le hx.1) hx.2]) hr)).frequently
  have ht : Tendsto (fun c : ℝ => J c-a*(b-c)) (𝓝[>] 0) (𝓝 ((∫ x,f x ∂m)-a*b)) := by
    have hc := (hJ 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    have hid : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hc
    simpa only [J,boundedHopfMap_zero,sub_zero] using hc.sub (((tendsto_const_nhds (x := b)).sub hid).const_mul a)
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0)).eventually_lt_const hb)] with c hc hcb
  exact H c hc hcb.le
end WeakHessianTransport

end
end InlinedFile87

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HopfEnergyInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile88
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma integral_hopf_initial_energy_lower (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {a : ℝ} (ha : 0 ≤ a) (hE : ENNReal.ofReal a < cheegerEnergy m f) :
    ∀ᶠ s in 𝓝[>] (0:ℝ),a ≤ (∫ x,f x-boundedHopfMap f s x ∂m)/s := by
  have hc := continuousOn_boundedHopfLp (m := m) hf 0 (by simp)
  have hzero : cheegerEnergy m (boundedHopfLp m f 0 : X → ℝ) = cheegerEnergy m f := by
    apply cheegerEnergy_congr_ae
    simpa only [boundedHopfLp,boundedHopfMap_zero] using BoundedContinuousFunction.coeFn_toLp 2 m ℝ f
  have he := hc ((lowerSemicontinuous_cheegerEnergy (m := m) (boundedHopfLp m f 0))
    (ENNReal.ofReal a) (by dsimp; rwa [hzero]))
  obtain ⟨ε,hε,hεe⟩ := Metric.mem_nhdsWithin_iff.mp he
  filter_upwards [self_mem_nhdsWithin,
    ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).eventually_lt_const hε)] with s hs hsε
  have hbound := integral_hopf_falling (m := m) f hf hs (a := a) (fun t ht hts => by
    have H : ENNReal.ofReal a < cheegerEnergy m (boundedHopfLp m f t : X → ℝ) :=
      hεe ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using hts.trans hsε,ht.le⟩
    have hb := boundedHopfLp_energy_bound (m := m) f ht
    have H' : a < (cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal ha hb.1.ne).mp H
    have hb' := H'.le.trans hb.2
    have hfun : (boundedHopfMap f t : X → ℝ) = hopfLax f t := funext (boundedHopfMap_apply_pos f ht)
    simpa only [hfun] using hb')
  rw [integral_sub (f.integrable (μ := m)) ((boundedHopfMap f s).integrable (μ := m))]
  exact (le_div_iff₀ hs).mpr (by linarith)
end WeakHessianTransport

end
end InlinedFile88

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HopfEnergyComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile90
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X} [IsFiniteMeasure ν]

lemma energy_le_of_hopf_integral_comparison
    (f F : X →ᵇ ℝ) {L M : ℝ≥0} (hf : LipschitzWith L f) (hF : LipschitzWith M F)
    {v : X → ℝ} (hv : Integrable v m) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {C : ℝ} (hC : 0 < C)
    (hcomm : ∀ s : ℝ,0 < s →
      (∫ x,F x-boundedHopfMap F (s*C) x ∂ν) ≤ ∫ x,v x*(f x-boundedHopfMap f s x) ∂m) :
    cheegerEnergy ν F ≤ ENNReal.ofReal ((∫ x,v x*(localSlope f x).toReal^2 ∂m)/(2*C)) := by
  have hfin : cheegerEnergy ν F < ∞ :=
    (cheegerEnergy_le_integral_localSlope ν hF ((F.memLp_top (μ := ν)).mono_exponent le_top)).trans_lt ENNReal.ofReal_lt_top
  let E := (cheegerEnergy ν F).toReal
  let R := (∫ x,v x*(localSlope f x).toReal^2 ∂m)/2
  have hRn : 0 ≤ R := div_nonneg (integral_nonneg_of_ae (hvn.mono fun x hx => mul_nonneg hx (sq_nonneg _))) (by norm_num)
  have hEC : E ≤ R/C := by
    apply le_of_forall_lt_imp_le_of_dense
    intro a ha
    by_cases han : a ≤ 0
    · exact han.trans (div_nonneg hRn hC.le)
    have hap := lt_of_not_ge han
    have hea : ENNReal.ofReal a < cheegerEnergy ν F :=
      (ENNReal.ofReal_lt_iff_lt_toReal hap.le hfin.ne).mpr ha
    have hlow := integral_hopf_initial_energy_lower (m := ν) F hF hap.le hea
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hscale : Tendsto (fun s : ℝ => s*C) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨by simpa using hid.mul_const C,?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hs hC
    have haC : a*C ≤ R := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro b hb
      have hupp := integral_hopf_initial_eventually_lt f hf hv hvn hb
      obtain ⟨s,hs,hl,hu⟩ := ((show ∀ᶠ s : ℝ in 𝓝[>] 0,0 < s from self_mem_nhdsWithin).and (Filter.Eventually.and (hscale hlow) hupp)).exists
      have HH := div_le_div_of_nonneg_right (hcomm s hs) hs.le
      have he : a*C ≤ (∫ x,F x-boundedHopfMap F (s*C) x ∂ν)/s := by
        apply (le_div_iff₀ hs).mpr
        have H := (le_div_iff₀ (mul_pos hs hC)).mp hl
        nlinarith
      exact he.trans (HH.trans hu.le)
    exact (le_div_iff₀ hC).mpr haC
  rw [← ENNReal.ofReal_toReal hfin.ne]
  apply ENNReal.ofReal_le_ofReal
  convert hEC using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [E,R]
  ring
end WeakHessianTransport

end
end InlinedFile90

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HopfWeightedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile89
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma finite_densityMeasure (u : Lp ℝ 2 m) (hu : Integrable u m) :
    IsFiniteMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (lintegral_mono fun x => Real.ofReal_le_enorm (u x)).trans_lt hu.hasFiniteIntegral

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma heat_integral_bounded_version (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (f F : X →ᵇ ℝ) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f)) :
    (∫ x,F x ∂densityMeasure m u) = ∫ x,cheegerHeat h t u x*f x ∂m := by
  rw [← integral_densityMeasure m _ (cheegerHeat_nonneg h ht u hun)]
  calc
    (∫ x,F x ∂densityMeasure m u) = (∫ x,cheegerHeat h t (hf2.toLp f) x ∂densityMeasure m u) :=
      integral_congr_ae ((densityMeasure_ac m u).ae_le hF)
    _ = ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ := integral_densityMeasure_L2 _ _ hun
    _ = ∫ x,hf2.toLp f x ∂densityMeasure m (cheegerHeat h t u) :=
      (cheegerHeat_density_duality h u _ ht hun).symm
    _ = ∫ x,f x ∂densityMeasure m (cheegerHeat h t u) :=
      integral_congr_ae ((densityMeasure_ac m _).ae_le hf2.coeFn_toLp)

lemma RCD.hopf_heat_integral_commutation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f))
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {s : ℝ} (hs : 0 < s) :
    (∫ x,F x-boundedHopfMap F (s*Real.exp (2*K*t)) x ∂densityMeasure m u) ≤
      ∫ x,cheegerHeat h t u x*(f x-boundedHopfMap f s x) ∂m := by
  let : IsFiniteMeasure (densityMeasure m u) := finite_densityMeasure u hu
  let : Measure.IsOpenPosMeasure m := hfull.openPosMeasure
  have hQ2 := boundedHopfMap_memLp_compact hfin f o hfc hs
  obtain ⟨F',Q,hFl,hQl,hFe,hQe,hFb,hcomm⟩ :=
    hrcd.hopf_heat_commutation hN hfull hfin h f hf hf2 hs hQ2 ht
  have he : F' = F := BoundedContinuousFunction.ext fun x => congrFun (Measure.eq_of_ae_eq (hFe.trans hF.symm) F'.continuous F.continuous) x
  subst F'
  have hPu := (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hu ht).1
  have H := integral_mono_ae ((F-boundedHopfMap F (s*Real.exp (2*K*t))).integrable (μ := densityMeasure m u))
    ((F-Q).integrable (μ := densityMeasure m u)) (ae_of_all _ fun x => by
      simp only [BoundedContinuousFunction.sub_apply,boundedHopfMap_apply_pos F (mul_pos hs (Real.exp_pos _))]
      linarith [hcomm x])
  simp only [BoundedContinuousFunction.sub_apply] at H
  rw [integral_sub (F.integrable (μ := densityMeasure m u)) (Q.integrable (μ := densityMeasure m u)),
    heat_integral_bounded_version h u hun f F hf2 ht hF,
    heat_integral_bounded_version h u hun _ Q hQ2 ht hQe] at H
  have hsub : (∫ x,cheegerHeat h t u x*(f x-boundedHopfMap f s x) ∂m) =
      (∫ x,cheegerHeat h t u x*f x ∂m)-(∫ x,cheegerHeat h t u x*boundedHopfMap f s x ∂m) := by
    simp_rw [mul_sub]
    exact integral_sub (integrable_bounded_pairing hPu f) (integrable_bounded_pairing hPu _)
  rwa [hsub]
end WeakHessian

end
end InlinedFile89

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LocalMeasureGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile86
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m ν : Measure X}

lemma IsTestPlan.of_local_measure_le_smul {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • ν) :
    IsTestPlan ν π := by
  obtain ⟨o,R,hR,htracks⟩ := hb
  obtain ⟨C,hC⟩ := hm o (R+1) (by linarith)
  obtain ⟨D,hD⟩ := hπ.2.1
  refine ⟨hπ.1,⟨D*C,fun t => ?_⟩,hπ.2.2⟩
  have ha : ∀ᵐ x ∂Measure.map (fun γ : Curve X => γ t) π,x ∈ Metric.ball o (R+1) := by
    apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable Metric.isOpen_ball.measurableSet).mpr
    filter_upwards [htracks] with γ hγ
    exact lt_of_le_of_lt (hγ t) (by linarith)
  calc
    Measure.map (fun γ : Curve X => γ t) π = (Measure.map (fun γ : Curve X => γ t) π).restrict (Metric.ball o (R+1)) :=
      (Measure.restrict_eq_self_of_ae_mem ha).symm
    _ ≤ ((D:ℝ≥0∞) • m).restrict (Metric.ball o (R+1)) := Measure.restrict_mono_measure (hD t) _
    _ = (D:ℝ≥0∞) • m.restrict (Metric.ball o (R+1)) := Measure.restrict_smul _ _ _
    _ ≤ (D:ℝ≥0∞) • ((C:ℝ≥0∞) • ν) := by gcongr
    _ = ((D*C:ℝ≥0):ℝ≥0∞) • ν := by rw [smul_smul,ENNReal.coe_mul]

lemma LocallyL2.of_local_measure_le_smul {f : X → ℝ} (hf : LocallyL2 m f)
    (hm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m) :
    LocallyL2 ν f := by
  intro o R hR
  obtain ⟨C,hC⟩ := hm o R hR
  apply MemLp.of_measure_le_smul (c := (C:ℝ≥0∞)) (by simp) _ (hf o R hR)
  simpa only [Measure.restrict_smul,Measure.restrict_restrict Metric.isOpen_ball.measurableSet,inter_self] using
    Measure.restrict_mono_measure hC (Metric.ball o R)

lemma IsLocalWeakUpperGradient.of_local_measure_le_smul {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hν : ν ≪ m)
    (hm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m) :
    IsLocalWeakUpperGradient ν f D := by
  refine ⟨hD.1.of_local_measure_le_smul hm,hν.ae_le hD.2.1,?_⟩
  intro π hπ hb
  exact hD.2.2 π (hπ.of_local_measure_le_smul hb hm) hb

lemma IsMinimalLocalWeakUpperGradient.change_measure_local {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) (hν : ν ≪ m) (hm : m ≪ ν)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • ν) :
    IsMinimalLocalWeakUpperGradient ν f D := by
  refine ⟨hD.1.of_local_measure_le_smul hν hνm,?_⟩
  intro E hE
  exact hν.ae_le (hD.2 E (hE.of_local_measure_le_smul hm hmν))

lemma weakGradient_eq_of_locally_comparable (hν : ν ≪ m) (hm : m ≪ ν)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • ν)
    (f : X → ℝ) : weakGradient m f =ᵐ[m] weakGradient ν f := by
  by_cases hf : ∃ D,IsMinimalLocalWeakUpperGradient m f D
  · have hfν : ∃ D,IsMinimalLocalWeakUpperGradient ν f D :=
      ⟨hf.choose,hf.choose_spec.change_measure_local hν hm hνm hmν⟩
    have hDm := weakGradient_isMinimal hf
    have hDν := (weakGradient_isMinimal hfν).change_measure_local hm hν hmν hνm
    filter_upwards [hDm.2 _ hDν.1,hDν.2 _ hDm.1] with x hx hy
    exact le_antisymm hx hy
  · have hfν : ¬∃ D,IsMinimalLocalWeakUpperGradient ν f D := by
      rintro ⟨D,hD⟩
      exact hf ⟨D,hD.change_measure_local hm hν hmν hνm⟩
    simp only [weakGradient,dite_eq_right hf,dite_eq_right hfν]
    exact Filter.EventuallyEq.rfl
end WeakHessian

end
end InlinedFile86

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile91
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_weightedEnergy_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hFl : GloballyLipschitz (F : X → ℝ)) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f))
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    cheegerEnergy (densityMeasure m u) F ≤
      ENNReal.ofReal (Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(localSlope f x).toReal^2 ∂m)/2) := by
  let : IsFiniteMeasure (densityMeasure m u) := finite_densityMeasure u hu
  have H := energy_le_of_hopf_integral_comparison f F hf.choose_spec hFl.choose_spec
    (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hu ht).1
    (cheegerHeat_nonneg h ht u hun) (Real.exp_pos (2*K*t))
    (fun s hs => hrcd.hopf_heat_integral_commutation hN hfull hfin h o f F hf hfc hf2 ht hF u hu hun hs)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [show -2*K*t = -(2*K*t) by ring,Real.exp_neg]
  ring

end WeakHessian

end

end InlinedFile91

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_PositiveProbes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile92
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma densityMeasure_ac_of_pos (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 < u x) :
    m ≪ densityMeasure m u := by
  apply withDensity_absolutelyContinuous' (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal.aemeasurable)
  exact hu.mono fun _ hx => (ENNReal.ofReal_pos.mpr hx).ne'

lemma restrict_le_densityMeasure (u : Lp ℝ 2 m) {S : Set X} (hS : MeasurableSet S)
    {c : ℝ} (hc : 0 < c) (hu : ∀ᵐ x ∂m,x ∈ S → c ≤ u x) :
    m.restrict S ≤ ENNReal.ofReal c⁻¹ • densityMeasure m u := by
  rw [← withDensity_indicator_one hS,densityMeasure,
    ← withDensity_smul _ (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)]
  apply withDensity_mono
  filter_upwards [hu] with x hx
  by_cases hs : x ∈ S
  · simp only [indicator_of_mem hs,Pi.one_apply,Pi.smul_apply,smul_eq_mul]
    have H : (1:ℝ) ≤ c⁻¹*u x := by
      rw [inv_mul_eq_div]; exact (le_div_iff₀ hc).mpr (by simpa using hx hs)
    simpa only [ENNReal.ofReal_one,ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] using ENNReal.ofReal_le_ofReal H
  · simp [hs]

variable [MetricSpace X]

lemma densityMeasure_locally_le (u : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂m,u x ≤ B) :
    ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m := by
  intro o R hR
  refine ⟨⟨B,hB⟩,?_⟩
  apply Measure.restrict_le_self.trans
  rw [densityMeasure,← withDensity_const]
  apply withDensity_mono
  filter_upwards [hu] with x hx
  exact (ENNReal.ofReal_le_ofReal hx).trans_eq (ENNReal.ofReal_eq_coe_nnreal hB)

variable (o : X) {a : ℝ} (ha : 0 < a)
variable (hw : MemLp (fun x => Real.exp (-(a*dist x o))) 2 m)

lemma positiveProbe_coe (u : Lp ℝ 2 m) (ε : ℝ) :
    positiveProbe o hw u ε =ᵐ[m] (fun x => u x+ε*Real.exp (-(a*dist x o))) := by
  filter_upwards [Lp.coeFn_add u (ε • hw.toLp _),Lp.coeFn_smul ε (hw.toLp _),hw.coeFn_toLp] with x h1 h2 h3
  simp only [positiveProbe,h1,Pi.add_apply,h2,Pi.smul_apply,smul_eq_mul,h3]

lemma positiveProbe_pos (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂m,0 < positiveProbe o hw u ε x := by
  filter_upwards [positiveProbe_coe o hw u ε,hu] with x hx hn
  rw [hx]
  positivity

lemma positiveProbe_integrable (u : Lp ℝ 2 m) (hu : Integrable u m)
    (hwi : Integrable (fun x => Real.exp (-(a*dist x o))) m) (ε : ℝ) :
    Integrable (positiveProbe o hw u ε) m :=
  (hu.add (hwi.const_mul ε)).congr (positiveProbe_coe o hw u ε).symm

include ha

lemma positiveProbe_le (u : Lp ℝ 2 m) {B : ℝ} (hu : ∀ᵐ x ∂m,u x ≤ B)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ x ∂m,positiveProbe o hw u ε x ≤ B+ε := by
  have haa := ha
  filter_upwards [positiveProbe_coe o hw u ε,hu] with x hx hn
  rw [hx]
  have hsmall : Real.exp (-(a*dist x o)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le dist_nonneg))
  nlinarith

variable [BorelSpace X]

lemma positiveProbe_locally_dominates (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ p : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball p R) ≤ (C:ℝ≥0∞) • densityMeasure m (positiveProbe o hw u ε) := by
  intro p R hR
  let c := ε*Real.exp (-(a*(R+dist p o)))
  have hc : 0 < c := mul_pos hε (Real.exp_pos _)
  refine ⟨Real.toNNReal c⁻¹,?_⟩
  change m.restrict (Metric.ball p R) ≤ ENNReal.ofReal c⁻¹ • _
  apply restrict_le_densityMeasure _ Metric.isOpen_ball.measurableSet hc
  filter_upwards [positiveProbe_coe o hw u ε,hu] with x hx hn hs
  rw [hx]
  have hd : dist x o ≤ R+dist p o := by
    have hs' := Metric.mem_ball.mp hs
    linarith [dist_triangle x p o]
  have he : Real.exp (-(a*(R+dist p o))) ≤ Real.exp (-(a*dist x o)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hd ha.le))
  dsimp [c]
  nlinarith
end WeakHessian

end
end InlinedFile92

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GradientProbes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile93
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrable_density_localSlope_sq {f u : X → ℝ} (hu : Integrable u m)
    {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable (fun x => u x*(localSlope f x).toReal^2) m := by
  apply hu.mul_bdd ((measurable_localSlope hf.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable (c := (L:ℝ)^2)
  apply ae_of_all
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)).trans_eq (ENNReal.coe_toReal L))

omit [MetricSpace X] [BorelSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_Lp_add_smul_mul (u v : Lp ℝ 2 m) (g : X → ℝ)
    (hu : Integrable (fun x => u x*g x) m) (hv : Integrable (fun x => v x*g x) m) (ε : ℝ) :
    (∫ x,(u+ε • v) x*g x ∂m) = (∫ x,u x*g x ∂m)+ε*(∫ x,v x*g x ∂m) := by
  calc
    _ = ∫ x,u x*g x+ε*(v x*g x) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add u (ε • v),Lp.coeFn_smul ε v] with x h1 h2
      simp only [h1,Pi.add_apply,h2,Pi.smul_apply,smul_eq_mul]
      ring
    _ = _ := by rw [integral_add hu (hv.const_mul ε),integral_const_mul]

end WeakHessian

end
end InlinedFile93

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedEnergyClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile96
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma exists_boundedContinuous_of_compact {f : X → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ F : X →ᵇ ℝ,(F : X → ℝ) = f := by
  obtain ⟨R,hR⟩ := (hc.isCompact.image hf).isBounded.subset_closedBall 0
  have hb (x : X) : ‖f x‖ ≤ |R| := by
    by_cases hx : f x = 0
    · simp [hx]
    have H := hR (mem_image_of_mem _ (subset_tsupport _ (Function.mem_support.mpr hx)))
    exact (show ‖f x‖ ≤ R by simpa only [Metric.mem_closedBall,dist_zero_right] using H).trans (le_abs_self _)
  exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hf |R| hb,rfl⟩

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrable_bounded_Lp_sq {v : X → ℝ} (hv : AEStronglyMeasurable v m)
    {B : ℝ} (hvB : ∀ᵐ x ∂m,|v x| ≤ B) (D : Lp ℝ 2 m) :
    Integrable (fun x => v x*(D x)^2) m := by
  apply ((memLp_two_iff_integrable_sq (Lp.memLp D).aestronglyMeasurable).mp (Lp.memLp D)).bdd_mul hv
  simpa only [Real.norm_eq_abs] using hvB

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_bounded_Lp_sq {v : X → ℝ} (hv : AEStronglyMeasurable v m)
    {B : ℝ} (hvB : ∀ᵐ x ∂m,|v x| ≤ B) (D : Lp ℝ 2 m) :
    (∫ x,v x*(D x)^2 ∂m) = ⟪D,boundedMulLp hv hvB D⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulLp_ae hv hvB D] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma tendsto_integral_bounded_Lp_sq {v : X → ℝ} (hv : AEStronglyMeasurable v m)
    {B : ℝ} (hvB : ∀ᵐ x ∂m,|v x| ≤ B) {Ds : ℕ → Lp ℝ 2 m} {D : Lp ℝ 2 m}
    (hDs : Tendsto Ds atTop (𝓝 D)) :
    Tendsto (fun n => ∫ x,v x*(Ds n x)^2 ∂m) atTop (𝓝 (∫ x,v x*(D x)^2 ∂m)) := by
  simp_rw [integral_bounded_Lp_sq hv hvB]
  exact hDs.inner ((boundedMulLp hv hvB).continuous.continuousAt.tendsto.comp hDs)

lemma RCD.cheegerHeat_weightedEnergy {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B) :
    cheegerEnergy (densityMeasure m u) (cheegerHeat h t f : X → ℝ) ≤
      ENNReal.ofReal (Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m)/2) := by
  obtain ⟨fs,hfl,hfc,hf2,Ds,hDs,hft,hDt⟩ := exists_compact_strong_slope_majorants hfin o hD
    (hrcd.1.global_cheegerEnergy_eq_minimal hfin o hD)
  choose fs' hfs' using fun n => exists_boundedContinuous_of_compact (hfl n).choose_spec.continuous (hfc n)
  have hfl' (n : ℕ) : GloballyLipschitz (fs' n : X → ℝ) := by rw [hfs']; exact hfl n
  have hf2' (n : ℕ) : MemLp (fs' n) 2 m := by rw [hfs']; exact hf2 n
  choose Fs hFl hFe hFb using fun n => hrcd.exists_boundedLipschitz_heatVersion hN hfull hfin h (fs' n) (hfl' n) (hf2' n) ht
  have hn := cheegerHeat_nonneg h ht u hun
  have huabs : ∀ᵐ x ∂m,|u x| ≤ B := by filter_upwards [hun,huB] with x hx hy; rwa [abs_of_nonneg hx]
  have hb := cheegerHeat_bounded h ht hB u huabs
  have hm : densityMeasure m u ≤ ENNReal.ofReal B • m := densityMeasure_le_const huB
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 (densityMeasure m u) := Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hm
  have hconv : Tendsto (fun n => T (cheegerHeat h t ((hf2 n).toLp (fs n)))) atTop
      (𝓝 (T (cheegerHeat h t f))) :=
    T.continuous.continuousAt.tendsto.comp ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hft)
  have hval := tendsto_integral_bounded_Lp_sq (Lp.memLp (cheegerHeat h t u)).aestronglyMeasurable hb hDt
  have hval' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hval.const_mul (Real.exp (-2*K*t))).div_const 2)
  have H : cheegerEnergy (densityMeasure m u) (T (cheegerHeat h t f) : X → ℝ) ≤
      ENNReal.ofReal (Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m)/2) := by
    apply lowerSemicontinuous_cheegerEnergy.isClosed_epigraph.mem_of_tendsto (hconv.prodMk_nhds hval')
    apply Eventually.of_forall
    intro n
    have hfc' : HasCompactSupport (fs' n : X → ℝ) := by rw [hfs']; exact hfc n
    have He := hrcd.cheegerHeat_weightedEnergy_compact hN hfull hfin h o (fs' n) (Fs n)
      (hfl' n) hfc' (hFl n) (hf2' n) ht (hFe n) u hu hun
    have heq : (hf2' n).toLp (fs' n) = (hf2 n).toLp (fs n) := by
      apply Lp.ext
      filter_upwards [(hf2' n).coeFn_toLp,(hf2 n).coeFn_toLp] with x h1 h2
      rw [h1,h2]; exact congrFun (hfs' n) x
    have heq' : (T (cheegerHeat h t ((hf2 n).toLp (fs n))) : X → ℝ) =ᵐ[densityMeasure m u] Fs n := by
      have he := (densityMeasure_ac m u).ae_le (hFe n).symm
      rw [heq] at he
      exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hm _).trans he
    change cheegerEnergy _ _ ≤ _
    rw [cheegerEnergy_congr_ae heq']
    apply He.trans
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply integral_mono_ae (integrable_density_localSlope_sq (cheegerHeat_integrable hfin o h u hu ht).1 (hfl' n).choose_spec)
      (integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t u)).aestronglyMeasurable hb (Ds n))
    filter_upwards [hn,hDs n] with x hx hy
    apply mul_le_mul_of_nonneg_left _ hx
    apply sq_le_sq₀ ENNReal.toReal_nonneg hy.1 |>.mpr
    simpa only [hfs' n] using hy.2
  rwa [cheegerEnergy_congr_ae (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top hm _)] at H
end WeakHessian

end
end InlinedFile96

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_SharpHeatGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile97
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma weighted_gradient_le_finite_energy (u : Lp ℝ 2 m) (hu : Integrable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hm : m ≪ densityMeasure m u)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • densityMeasure m u)
    (F : X → ℝ) (hF2 : MemLp F 2 (densityMeasure m u))
    (hfin : cheegerEnergy (densityMeasure m u) F < ∞) :
    ENNReal.ofReal ((∫ x,u x*(weakGradient m F x)^2 ∂m)/2) ≤ cheegerEnergy (densityMeasure m u) F := by
  let ν := densityMeasure m u
  let : IsFiniteMeasure ν := finite_densityMeasure u hu
  obtain ⟨D,hD,hE⟩ := exists_minimalGradient_energy_le_cheeger (m := ν) (fun _ _ => measure_lt_top _ _) hF2 hfin
  have hchange := weakGradient_eq_of_locally_comparable (densityMeasure_ac m u) hm hνm hmν F
  have hDm : weakGradient m F =ᵐ[ν] D :=
    Filter.EventuallyEq.trans ((densityMeasure_ac m u).ae_le hchange) (weakGradient_ae_eq_of_isMinimal hD)
  have he : (∫ x,u x*(weakGradient m F x)^2 ∂m) = ‖D‖^2 := by
    rw [← integral_densityMeasure m u hun]
    have heq : (fun x => weakGradient m F x ^ 2) =ᵐ[ν] (fun x => (D x)^2) := by
      filter_upwards [hDm] with x hx; rw [hx]
    change (∫ x,weakGradient m F x ^ 2 ∂ν) = _
    rw [integral_congr_ae heq]
    simpa only [Lp.toLp_coeFn] using (norm_toLp_sq_eq_integral (Lp.memLp D)).symm
  rwa [he]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerHeat_sobolev {K N : ℝ}
    (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (o : X)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t) :
    Sobolev m (cheegerHeat h t f : X → ℝ) := by
  apply (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp _)).mpr
  exact (cheegerHeat_energy_le h ht f).trans_lt
    ((hrcd.1.global_cheegerEnergy_le_weak hfin o hD.1).trans_lt ENNReal.ofReal_lt_top)

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [SigmaFinite m] in
lemma integrable_bounded_weakGradient_sq {F u : X → ℝ} (hF : Sobolev m F)
    (hu : AEStronglyMeasurable u m) {B : ℝ} (huB : ∀ᵐ x ∂m,|u x| ≤ B) :
    Integrable (fun x => u x*(weakGradient m F x)^2) m := by
  apply hF.2.2.integrable_sq.bdd_mul hu
  simpa only [Real.norm_eq_abs] using huB

lemma RCD.cheegerHeat_weightedGradient {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    (hm : m ≪ densityMeasure m u)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • densityMeasure m u) :
    (∫ x,u x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m) ≤
      Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m) := by
  have he := hrcd.cheegerHeat_weightedEnergy hN hfull hfin h o hD ht u hu hun hB huB
  have hf2 := (Lp.memLp (cheegerHeat h t f)).of_measure_le_smul ENNReal.ofReal_ne_top (densityMeasure_le_const huB)
  have H := (weighted_gradient_le_finite_energy u hu hun hm hνm hmν _ hf2
    (he.trans_lt ENNReal.ofReal_lt_top)).trans he
  have Hn : 0 ≤ Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m)/2 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (Real.exp_pos _).le
    exact integral_nonneg_of_ae ((cheegerHeat_nonneg h ht u hun).mono fun _ hx => mul_nonneg hx (sq_nonneg _))
  have HH := (ENNReal.ofReal_le_ofReal_iff Hn).mp H
  linarith

lemma RCD.cheegerHeat_gradient_integral {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B) :
    (∫ x,u x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m) ≤
      Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m) := by
  obtain ⟨a,ha,hwi,hw,-⟩ := hrcd.1.exists_comparison_confinement hN hfull hfin o
  let w := hw.toLp (fun x => Real.exp (-(a*dist x o)))
  have hwi' : Integrable w m := hwi.congr hw.coeFn_toLp.symm
  have hwa : ∀ᵐ x ∂m,|w x| ≤ 1 := by
    filter_upwards [hw.coeFn_toLp] with x hx
    rw [hx,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [dist_nonneg (x := x) (y := o)])
  have hua : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hun,huB] with x hx hy; rwa [abs_of_nonneg hx]
  have hHs := hrcd.cheegerHeat_sobolev hfin h o hD ht
  have hgu := integrable_bounded_weakGradient_sq hHs (Lp.memLp u).aestronglyMeasurable hua
  have hgw := integrable_bounded_weakGradient_sq hHs (Lp.memLp w).aestronglyMeasurable hwa
  have hsu := integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t u)).aestronglyMeasurable (cheegerHeat_bounded h ht hB u hua) D
  have hsw := integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t w)).aestronglyMeasurable (cheegerHeat_bounded h ht zero_le_one w hwa) D
  have H (ε : ℝ) (hε : 0 < ε) :
      (∫ x,u x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m)+
        ε*(∫ x,w x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m) ≤
      Real.exp (-2*K*t)*((∫ x,cheegerHeat h t u x*(D x)^2 ∂m)+
        ε*(∫ x,cheegerHeat h t w x*(D x)^2 ∂m)) := by
    have hpos := positiveProbe_pos o hw u hun hε
    have hbound := positiveProbe_le o ha hw u huB hε.le
    have HH := hrcd.cheegerHeat_weightedGradient hN hfull hfin h o hD ht
      (positiveProbe o hw u ε) (positiveProbe_integrable o hw u hu hwi ε) (hpos.mono fun _ hx => hx.le)
      (add_nonneg hB hε.le) hbound
      (densityMeasure_ac_of_pos _ hpos)
      (densityMeasure_locally_le _ (add_nonneg hB hε.le) hbound)
      (positiveProbe_locally_dominates o ha hw u hun hε)
    dsimp only [positiveProbe] at HH
    rw [integral_Lp_add_smul_mul u w _ hgu hgw,map_add,map_smul,
      integral_Lp_add_smul_mul _ _ _ hsu hsw] at HH
    exact HH
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have HH := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (he.mul_const _))
    (tendsto_const_nhds.mul (tendsto_const_nhds.add (he.mul_const _)))
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ),_ from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact H ε hε)
  simpa only [zero_mul,add_zero] using HH
end WeakHessian

end
end InlinedFile97

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_SobolevHeatPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile108
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_pairing_deriv_zero {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u q : Lp ℝ 2 m}
    (hu : Sobolev m (u : X → ℝ)) (hq : Sobolev m (q : X → ℝ)) :
    HasDerivWithinAt (fun t => ⟪q,cheegerHeat h t u⟫_ℝ)
      (-(∫ x,gamma m (u : X → ℝ) q x ∂m)) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_right_deriv
    (d := fun t => -(∫ x,gamma m (cheegerHeat h t u) q x ∂m))
  · exact continuousOn_const.inner (cheegerHeat_continuousOn hfin h u)
  · intro t ht
    obtain ⟨A,hA⟩ := (cheeger_closedQuadraticEnergy h).heat_hasFormGenerator m ht u
    change (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A at hA
    have hd := cheegerHeat_deriv_right_of_generator hfin h ht.le hA
    have HH := (hasDerivWithinAt_const t (Ici t) q).inner ℝ hd
    simp only [inner_zero_left,add_zero] at HH
    have hqe := (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp q)).mp hq
    have hpair := hA.2 ⟨q,hqe⟩
    rw [← hcd.global_integral_gamma_form hfin o h ⟨cheegerHeat h t u,hA.1⟩ ⟨q,hqe⟩] at hpair
    have he : ⟪q,A⟫_ℝ = -(∫ x,gamma m (cheegerHeat h t u) q x ∂m) := by
      rw [real_inner_comm]
      linarith
    rwa [he] at HH
  · exact (hcd.cheegerHeat_integral_gamma_zero hfin h o hu hq).neg
end WeakHessian

end
end InlinedFile108

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CoreAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile110
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma driftBochner_eq_sub_hessian (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V g ξ : X → ℝ}
    (hg : IsTestFunction m g) (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x, |V x| ≤ B) (hC : ∀ x, |ξ x| ≤ C)
    (hξS : Sobolev m ξ) :
    driftBochner m V g ξ =
      integratedBochner m g (fun x => ξ x*Real.exp (V x)) -
      weakHessian m V g (fun x => ξ x*Real.exp (V x)) := by
  have hgS := (laplacian_isLaplacian hg.1).1
  have hA := (laplacian_isLaplacian hg.1).2.1
  have hVS := localSobolev_of_lipschitz hfinite hV
  have hb := memLp_gamma_of_lipschitz hfinite hpar hV hgS
  have hc := memLp_gamma_of_lipschitz hfinite hpar hξ hgS
  have hxb : MemLp (fun x => ξ x*gamma m V g x) 2 m := by
    simpa only [mul_comm] using memLp_mul_bounded hb hξ.continuous.aestronglyMeasurable (ae_of_all m hC)
  have hxA : MemLp (fun x => ξ x*laplacian m g x) 2 m := by
    simpa only [mul_comm] using memLp_mul_bounded hA hξ.continuous.aestronglyMeasurable (ae_of_all m hC)
  have hU : MemLp (fun x => ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x) 2 m := by
    convert (hxA.add hxb).add hc using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.add_apply]
    ring
  have hw : AEStronglyMeasurable (fun x => Real.exp (V x)) m :=
    (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable
  have hwB : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := ae_of_all m fun x => by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hB' : ∀ᵐ x ∂m, V x ≤ B := ae_of_all m fun x => (le_abs_self _).trans (hB x)
  have hxp := gamma_mul_exp_left hfinite hpar hξS.2.1 hVS hgS.2.1 hB'
    (weakGradient_le_lipschitz hfinite hV)
  have hxq := gamma_mul_exp_left hfinite hpar hξS.2.1 hVS hq.2.1 hB'
    (weakGradient_le_lipschitz hfinite hV)
  have hi1 : Integrable (fun x => Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x) m :=
    (integrable_gamma hfinite hξS hq).bdd_mul hw hwB
  have hi2 : Integrable (fun x => Real.exp (V x)*(ξ x*gamma m V (fun y => gamma m g g y/2) x)) m :=
    (hξS.1.integrable_mul (memLp_gamma_of_lipschitz hfinite hpar hV hq)).bdd_mul hw hwB
  have hiA : Integrable (fun x => Real.exp (V x)*
      ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*laplacian m g x)) m :=
    (hU.integrable_mul hA).bdd_mul hw hwB
  have hib : Integrable (fun x => Real.exp (V x)*
      ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*gamma m V g x)) m :=
    (hU.integrable_mul hb).bdd_mul hw hwB
  have eq1 : (∫ x, gamma m (fun y => ξ y*Real.exp (V y)) (fun y => gamma m g g y/2) x ∂m) =
      (∫ x, Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x ∂m) +
      ∫ x, Real.exp (V x)*(ξ x*gamma m V (fun y => gamma m g g y/2) x) ∂m := by
    rw [← integral_add hi1 hi2]
    apply integral_congr_ae
    filter_upwards [hxq] with x hx
    rw [hx]
    ring
  have eq2 : (∫ x, ((ξ x*Real.exp (V x))*laplacian m g x+
      gamma m (fun y => ξ y*Real.exp (V y)) g x)*laplacian m g x ∂m) =
      ∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*laplacian m g x) ∂m := by
    apply integral_congr_ae
    filter_upwards [hxp] with x hx
    rw [hx]
    ring
  have eq3 : (∫ x, (gamma m (fun y => ξ y*Real.exp (V y)) g x+
      (ξ x*Real.exp (V x))*laplacian m g x)*gamma m V g x ∂m) =
      ∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*gamma m V g x) ∂m := by
    apply integral_congr_ae
    filter_upwards [hxp] with x hx
    rw [hx]
    ring
  have eq4 : (∫ x, (ξ x*Real.exp (V x))*gamma m V (fun y => gamma m g g y/2) x ∂m) =
      ∫ x, Real.exp (V x)*(ξ x*gamma m V (fun y => gamma m g g y/2) x) ∂m := by
    congr 1
    funext x
    ring
  have eq5 : (∫ x, Real.exp (V x)*(ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*
      (laplacian m g x+gamma m V g x) ∂m) =
      (∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*laplacian m g x) ∂m) +
      ∫ x, Real.exp (V x)*
        ((ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*gamma m V g x) ∂m := by
    rw [← integral_add hiA hib]
    congr 1
    funext x
    ring
  unfold driftBochner integratedBochner weakHessian
  rw [eq1,eq2,eq3,eq4,eq5]
  ring
end WeakHessian

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakHessian_const_mul (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {F g h : X → ℝ}
    (hF : LocalSobolev m F) (hg : LocalSobolev m g)
    (hq : LocalSobolev m (fun y => gamma m g g y/2)) (c : ℝ) :
    weakHessian m (fun x => c*F x) g h = c*weakHessian m F g h := by
  have hfg := gamma_const_mul_left hfinite hpar hF hg c
  have hfq := gamma_const_mul_left hfinite hpar hF hq c
  unfold weakHessian
  have e1 : (∫ x, (gamma m h g x+h x*laplacian m g x)*gamma m (fun y => c*F y) g x ∂m) =
      c*(∫ x, (gamma m h g x+h x*laplacian m g x)*gamma m F g x ∂m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
    ring
  have e2 : (∫ x, h x*gamma m (fun y => c*F y) (fun y => gamma m g g y/2) x ∂m) =
      c*(∫ x, h x*gamma m F (fun y => gamma m g g y/2) x ∂m) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hfq] with x hx
    rw [hx]
    ring
  rw [e1,e2]
  ring
end WeakHessian

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma WeakHessianUpperBound.core_dual (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {F G g ξ : X → ℝ}
    (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x, |F x| ≤ B) (hC : ∀ x, |ξ x| ≤ C)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x, 0 ≤ ξ x)
    {a K : ℝ} (ha : 0 ≤ a)
    (horig : K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) ≤
      integratedBochner m g (fun x => ξ x*Real.exp (a*F x))) :
    K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) -
      a*(∫ x, (ξ x*Real.exp (a*F x))*G x*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x, |a*F x| ≤ |a| * B := fun x => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg a)
  have hw := lipschitz_exp_bounded hV (fun x => (le_abs_self _).trans (hVB x))
  have hwB : ∀ x, |Real.exp (a*F x)| ≤ Real.exp (|a| * B) := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hVB x))
  have hφ := lipschitz_mul_bounded hξ hw hC hwB
  have hh := hHess g hg hgc (fun x => ξ x*Real.exp (a*F x)) ⟨_,hφ⟩
    hξc.mul_right (fun x => mul_nonneg (hξ0 x) (Real.exp_pos _).le)
  rw [driftBochner_eq_sub_hessian hfinite hpar hg hq hV hξ hVB hC
    (sobolev_of_lipschitz_compactSupport hfinite hξ hξc),
    weakHessian_const_mul hfinite hpar (localSobolev_of_lipschitz hfinite hF)
      (laplacian_isLaplacian hg.1).1.2.1 hq.2.1]
  linarith [mul_le_mul_of_nonneg_left hh ha]

lemma WeakHessianUpperBound.core_integrated (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {F G g ξ : X → ℝ}
    (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x, |F x| ≤ B) (hC : ∀ x, |ξ x| ≤ C)
    (hG : ∀ x, |G x| ≤ D) (hGc : Continuous G)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x, 0 ≤ ξ x)
    {a K : ℝ} (ha : 0 ≤ a)
    (horig : K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) ≤
      integratedBochner m g (fun x => ξ x*Real.exp (a*F x))) :
    (∫ x, Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hgS := (laplacian_isLaplacian hg.1).1
  have hφB : ∀ᵐ x ∂m, ‖ξ x*Real.exp (a*F x)‖ ≤ |C| * Real.exp (|a| * B) := by
    filter_upwards [] with x
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul ((hC x).trans (le_abs_self _)) _ (Real.exp_pos _).le (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    calc a*F x ≤ |a*F x| := le_abs_self _
      _ = |a| * |F x| := abs_mul _ _
      _ ≤ |a| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  have hφm : AEStronglyMeasurable (fun x => ξ x*Real.exp (a*F x)) m :=
    (hξ.continuous.mul (Real.continuous_exp.comp (continuous_const.mul hF.continuous))).aestronglyMeasurable
  have hi := (integrable_gamma hfinite hgS hgS).bdd_mul hφm hφB
  have hiG : Integrable (fun x => (ξ x*Real.exp (a*F x))*G x*gamma m g g x) m := by
    have ht := hi.bdd_mul hGc.aestronglyMeasurable (ae_of_all m fun x => by
      simpa only [Real.norm_eq_abs] using hG x)
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    ring
  calc
    (∫ x, Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) =
        K*(∫ x, (ξ x*Real.exp (a*F x))*gamma m g g x ∂m) -
        a*(∫ x, (ξ x*Real.exp (a*F x))*G x*gamma m g g x ∂m) := by
      rw [← integral_const_mul,← integral_const_mul,← integral_sub (hi.const_mul K) (hiG.const_mul a)]
      congr 1
      funext x
      ring
    _ ≤ _ := hHess.core_dual hfinite hpar hg hgc hq hF hξ hB hC hξc hξ0 ha horig
end WeakHessian

end
end InlinedFile110

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_BochnerConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile99
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma integrable_bounded_gamma (hfin : FiniteOnBoundedSets m) {u v e : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) (he : AEStronglyMeasurable e m)
    {C : ℝ} (hC : ∀ᵐ x ∂m,|e x| ≤ C) : Integrable (fun x => e x*gamma m u v x) m := by
  apply (integrable_gamma hfin hu hv).bdd_mul he
  simpa only [Real.norm_eq_abs] using hC

omit [ProperSpace X] [SigmaFinite m] in
lemma weighted_gradient_tangent (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v e : X → ℝ} (hu : Sobolev m u) (hv : Sobolev m v)
    (he : AEStronglyMeasurable e m) (hen : ∀ᵐ x ∂m,0 ≤ e x)
    {C : ℝ} (hC : ∀ᵐ x ∂m,|e x| ≤ C) :
    2*(∫ x,e x*gamma m u v x ∂m)-(∫ x,e x*(weakGradient m u x)^2 ∂m) ≤
      ∫ x,e x*(weakGradient m v x)^2 ∂m := by
  have hiu := integrable_bounded_weakGradient_sq hu he hC
  have hiv := integrable_bounded_weakGradient_sq hv he hC
  have hig := integrable_bounded_gamma hfin hu hv he hC
  rw [← integral_const_mul,← integral_sub (hig.const_mul 2) hiu]
  apply integral_mono_ae ((hig.const_mul 2).sub hiu) hiv
  filter_upwards [abs_gamma_le hfin hpar hu.2.1 hv.2.1,hen] with x hx hn
  have hb : 2*gamma m u v x-(weakGradient m u x)^2 ≤ (weakGradient m v x)^2 := by
    have hh := (le_abs_self (gamma m u v x)).trans hx
    nlinarith [sq_nonneg (weakGradient m u x-weakGradient m v x)]
  change 2*(e x*gamma m u v x)-e x*(weakGradient m u x)^2 ≤ e x*(weakGradient m v x)^2
  nlinarith [mul_le_mul_of_nonneg_left hb hn]

omit [ProperSpace X] [SigmaFinite m] in
lemma IsLaplacian.weighted_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A v e : X → ℝ}
    (hu : IsLaplacian m u A) (hv : Sobolev m v)
    {L : ℝ≥0} (he : LipschitzWith L e) {C : ℝ} (hC : ∀ᵐ x ∂m,|e x| ≤ C) :
    (∫ x,e x*gamma m u v x ∂m) =
      -(∫ x,v x*(e x*A x+gamma m e u x) ∂m) := by
  have hes := localSobolev_of_lipschitz hfin he
  have heD : ∀ᵐ x ∂m,|weakGradient m e x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_le_lipschitz hfin he,weakGradient_nonneg (m := m) e] with x hx hn
    rwa [abs_of_nonneg hn]
  have hve := hv.mul_bounded hfin hes hC heD
  have hAu := memLp_mul_bounded hu.2.1 he.continuous.aestronglyMeasurable hC
  have hΓ := memLp_gamma_of_lipschitz hfin hpar he hu.1
  have h1 : Integrable (fun x => v x*gamma m e u x) m := hv.1.integrable_mul hΓ
  have h2 := integrable_bounded_gamma hfin hu.1 hv he.continuous.aestronglyMeasurable hC
  have h3 : Integrable (fun x => v x*(A x*e x)) m := hv.1.integrable_mul hAu
  have H := hu.2.2 (fun x => v x*e x) hve
  have heq : gamma m u (fun x => v x*e x) =ᵐ[m]
      (fun x => v x*gamma m e u x+e x*gamma m u v x) := by
    filter_upwards [gamma_comm (m := m) u (fun x => v x*e x),
      gamma_mul_left hfin hpar hv.2.1 hes hu.1.2.1 hC heD,gamma_comm (m := m) v u] with x hx hy hz
    rw [hx,hy,hz]
  rw [integral_congr_ae heq,integral_add h1 h2] at H
  have h3' : Integrable (fun x => v x*(e x*A x)) m := by simpa only [mul_comm (e _)] using h3
  rw [show (fun x => v x*(e x*A x+gamma m e u x)) =
      (fun x => v x*(e x*A x)+v x*gamma m e u x) by funext x; ring,
    integral_add h3' h1]
  have HE : (∫ x,A x*(v x*e x) ∂m) = ∫ x,v x*(e x*A x) ∂m := by congr 1; funext x; ring
  rw [HE] at H
  linarith

lemma right_deriv_nonneg_of_nonneg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivWithinAt f d (Ici 0) 0) (h0 : f 0 = 0)
    (hn : ∀ t,0 ≤ t → 0 ≤ f t) : 0 ≤ d := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hf.Ioi_of_Ici
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_field,h0,sub_zero]
  exact div_nonneg (hn t ht.le) ht.le
end WeakHessian

end
end InlinedFile99

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_OriginalBochner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile100
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_Lp_function_eq_inner (a : Lp ℝ 2 m) {b : X → ℝ} (hb : MemLp b 2 m) :
    (∫ x,a x*b x ∂m) = ⟪hb.toLp b,a⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]

end WeakHessian

end
end InlinedFile100

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevBochner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile109
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.original_bochner_sobolev_multiplier {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u A ξ : Lp ℝ 2 m}
    (hu : IsLaplacian m (u : X → ℝ) A)
    (hξ : Sobolev m (ξ : X → ℝ))
    (hξi : Integrable ξ m) {e : X → ℝ} {L : ℝ≥0} (hel : LipschitzWith L e)
    (heξ : e =ᵐ[m] ξ) (hen : ∀ᵐ x ∂m,0 ≤ e x) {C : ℝ} (hC : 0 ≤ C)
    (heC : ∀ᵐ x ∂m,|e x| ≤ C)
    (hqs : Sobolev m (fun x => (weakGradient m (u : X → ℝ) x)^2)) :
    K*(∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m) ≤
      -(1/2)*(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m)+
        (∫ x,A x*(e x*A x+gamma m e u x) ∂m) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hpar := hrcd.1.global_localGradientParallelogram hfin o h
  have hq := hqs.1
  let q := hq.toLp (fun x => (weakGradient m (u : X → ℝ) x)^2)
  have hW : MemLp (fun x => e x*A x+gamma m e u x) 2 m := by
    apply MemLp.add _ (memLp_gamma_of_lipschitz hfin hpar hel hu.1)
    simpa only [mul_comm] using memLp_mul_bounded (Lp.memLp A) hel.continuous.aestronglyMeasurable heC
  let W := hW.toLp (fun x => e x*A x+gamma m e u x)
  let E := ∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m
  have hE : E = ⟪q,ξ⟫_ℝ := by
    rw [← integral_Lp_function_eq_inner ξ hq]
    exact integral_congr_ae (heξ.fun_mul .rfl)
  have hWu : (∫ x,e x*gamma m (u : X → ℝ) u x ∂m) = -⟪W,u⟫_ℝ := by
    rw [hu.weighted_pairing hfin hpar hu.1 hel heC,integral_Lp_function_eq_inner u hW]
  have hzero : E = -⟪W,u⟫_ℝ := by
    rw [← hWu]
    exact integral_congr_ae (by filter_upwards [gamma_self (m := m) (u : X → ℝ)] with x hx; rw [hx])
  let D := hu.1.2.2.toLp (weakGradient m (u : X → ℝ))
  have hD : IsMinimalLocalWeakUpperGradient m (u : X → ℝ) D :=
    (weakGradient_isMinimal hu.1.2.1.2).congr_ae .rfl hu.1.2.2.coeFn_toLp.symm
  have hξn : ∀ᵐ x ∂m,0 ≤ ξ x := by filter_upwards [heξ,hen] with x hx hn; simpa only [← hx] using hn
  have hξC : ∀ᵐ x ∂m,ξ x ≤ C := by filter_upwards [heξ,heC] with x hx hn; rw [← hx]; exact (le_abs_self _).trans hn
  have H (t : ℝ) (ht : 0 ≤ t) :
      -2*⟪W,cheegerHeat h t u⟫_ℝ-E ≤ Real.exp (-2*K*t)*⟪q,cheegerHeat h t ξ⟫_ℝ := by
    have hS := hrcd.cheegerHeat_sobolev hfin h o hD ht
    have hlow := weighted_gradient_tangent hfin hpar hu.1 hS hel.continuous.aestronglyMeasurable hen heC
    rw [hu.weighted_pairing hfin hpar hS hel heC,
      integral_Lp_function_eq_inner (cheegerHeat h t u) hW] at hlow
    have hhi := hrcd.cheegerHeat_gradient_integral hN hfull hfin h o hD ht ξ hξi hξn hC hξC
    have helhs : (∫ x,ξ x*(weakGradient m (cheegerHeat h t u : X → ℝ) x)^2 ∂m) =
        ∫ x,e x*(weakGradient m (cheegerHeat h t u : X → ℝ) x)^2 ∂m :=
      integral_congr_ae (heξ.symm.fun_mul .rfl)
    have herhs : (∫ x,cheegerHeat h t ξ x*(D x)^2 ∂m) = ⟪q,cheegerHeat h t ξ⟫_ℝ := by
      rw [← integral_Lp_function_eq_inner (cheegerHeat h t ξ) hq]
      exact integral_congr_ae (by filter_upwards [hu.1.2.2.coeFn_toLp] with x hx; rw [hx])
    rw [helhs,herhs] at hhi
    calc
      _ = 2*(-⟪W,cheegerHeat h t u⟫_ℝ)-E := by ring
      _ ≤ _ := hlow.trans hhi
  have hud := (cheeger_closedQuadraticEnergy h).heat_deriv_form_zero m (cheeger_domain_dense h)
    (hrcd.1.global_formGenerator_of_isLaplacian hfin o h u A hu)
  have hξd := hrcd.1.cheegerHeat_pairing_deriv_zero hfin h o hξ ((sobolev_congr_ae hq.coeFn_toLp.symm).mp hqs)
  let d := -(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m)
  have heq : (-(∫ x,gamma m (ξ : X → ℝ) q x ∂m)) = d := by
    congr 1
    exact integral_congr_ae (gamma_congr_ae heξ.symm hq.coeFn_toLp)
  rw [heq] at hξd
  change HasDerivWithinAt (fun t => cheegerHeat h t u) A (Ici 0) 0 at hud
  have h1 : HasDerivWithinAt (fun t => ⟪W,cheegerHeat h t u⟫_ℝ) ⟪W,A⟫_ℝ (Ici 0) 0 := by
    simpa only [inner_zero_left,add_zero] using (hasDerivWithinAt_const 0 (Ici 0) W).inner ℝ hud
  have h2 : HasDerivWithinAt (fun t => ⟪q,cheegerHeat h t ξ⟫_ℝ) d (Ici 0) 0 := hξd
  have hexd : HasDerivWithinAt (fun t : ℝ => Real.exp (-2*K*t)) (-2*K) (Ici 0) 0 := by
    simpa using (((hasDerivWithinAt_id 0 (Ici 0)).const_mul (-2*K)).exp)
  have hd : HasDerivWithinAt
      (fun t => Real.exp (-2*K*t)*⟪q,cheegerHeat h t ξ⟫_ℝ-(-2*⟪W,cheegerHeat h t u⟫_ℝ-E))
      ((-2*K)*⟪q,ξ⟫_ℝ+d+2*⟪W,A⟫_ℝ) (Ici 0) 0 := by
    have HH := (hexd.mul h2).sub ((h1.const_mul (-2)).sub_const E)
    simp only [mul_zero,Real.exp_zero,cheegerHeat_zero,one_apply_eq_self,one_mul] at HH
    convert! HH using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hnon := right_deriv_nonneg_of_nonneg hd (by simp [cheegerHeat_zero,← hE]; linarith [hzero])
    (fun t ht => sub_nonneg.mpr (H t ht))
  rw [integral_Lp_function_eq_inner A hW]
  change K*E ≤ -(1/2)*(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m)+⟪W,A⟫_ℝ
  change (-2*K)*⟪q,ξ⟫_ℝ+d+2*⟪W,A⟫_ℝ ≥ 0 at hnon
  rw [← hE] at hnon
  dsimp only [d] at hnon
  linarith
end WeakHessian

end
end InlinedFile109

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_TestBochner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile111
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.test_gammaHalf_sobolev {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g) :
    Sobolev m (fun x => gamma m g g x/2) := by
  have HH := (hrcd.test_gradientSquare_sobolev hN hfull hfin o hg).const_mul (1/2)
  apply (sobolev_congr_ae _).mp HH
  filter_upwards [gamma_self (m := m) g] with x hx
  rw [hx]
  ring

lemma RCD.test_integratedBochner {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g e : X → ℝ} (hg : IsTestFunction m g)
    {L : ℝ≥0} (hel : LipschitzWith L e) (hec : HasCompactSupport e)
    (hen : ∀ x,0 ≤ e x) :
    K*(∫ x,e x*gamma m g g x ∂m) ≤ integratedBochner m g e := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hp := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hL := laplacian_isLaplacian hg.1
  let u := hL.1.1.toLp g
  let A := hL.2.1.toLp (laplacian m g)
  have hu : IsLaplacian m (u : X → ℝ) A := hL.congr_ae hL.1.1.coeFn_toLp.symm hL.2.1.coeFn_toLp.symm
  have hes := sobolev_of_lipschitz_compactSupport hfin hel hec
  let ξ := hes.1.toLp e
  have hξ := (sobolev_congr_ae hes.1.coeFn_toLp.symm).mp hes
  have hξi : Integrable (ξ : X → ℝ) m := (hel.continuous.integrable_of_hasCompactSupport hec).congr hes.1.coeFn_toLp.symm
  obtain ⟨C,hC⟩ := (hec.isCompact_range hel.continuous).isBounded |>.exists_norm_le
  have heB : ∀ x,|e x| ≤ |C| := fun x => by
    have HH : |e x| ≤ C := by simpa only [Real.norm_eq_abs] using hC (e x) ⟨x,rfl⟩
    exact HH.trans (le_abs_self C)
  have hgs := hrcd.test_gradientSquare_sobolev hN hfull hfin o hg
  have hgrad := weakGradient_congr_ae hL.1.1.coeFn_toLp
  have hqu : Sobolev m (fun x => (weakGradient m (u : X → ℝ) x)^2) := (sobolev_congr_ae (hgrad.pow_const 2).symm).mp hgs
  have HH := hrcd.original_bochner_sobolev_multiplier hN hfull hfin hrcd.2 o hu hξ hξi hel
    hes.1.coeFn_toLp.symm (ae_of_all m hen) (abs_nonneg C) (ae_of_all m heB) hqu
  have eq1 : (∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m) = ∫ x,e x*gamma m g g x ∂m := by
    apply integral_congr_ae
    filter_upwards [hgrad,gamma_self (m := m) g] with x hx hy
    rw [hx,hy]
  have eq2 : (1/2)*(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m) =
      ∫ x,gamma m e (fun y => gamma m g g y/2) x ∂m := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    have heq : (fun y => gamma m g g y/2) =ᵐ[m] (fun y => (1/2)*(weakGradient m (u : X → ℝ) y)^2) := by
      filter_upwards [hgrad,gamma_self (m := m) g] with x hx hy
      rw [hx,hy]
      ring
    filter_upwards [gamma_congr_ae (m := m) (f := e) .rfl heq,
      gamma_const_mul_right hfin hp hes.2.1 hqu.2.1 (1/2)] with x hx hy
    rw [hx,hy]
  have eq3 : (∫ x,A x*(e x*A x+gamma m e u x) ∂m) =
      ∫ x,(e x*laplacian m g x+gamma m e g x)*laplacian m g x ∂m := by
    apply integral_congr_ae
    filter_upwards [hL.2.1.coeFn_toLp,gamma_congr_ae (m := m) (f := e) .rfl hL.1.1.coeFn_toLp] with x hx hy
    rw [hx,hy]
    ring
  rw [eq1,neg_mul,eq2,eq3] at HH
  exact HH
end WeakHessian

end
end InlinedFile111

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ActualCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile112
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_core_integrated_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G g ξ : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x,|F x| ≤ B) (hC : ∀ x,|ξ x| ≤ C)
    (hG : ∀ x,|G x| ≤ D) (hGc : Continuous G)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hq := hrcd.test_gammaHalf_sobolev hN hfull hfin o hg
  have hp := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  apply hHess.core_integrated hfin hp hg hgc hq hF hξ hB hC hG hGc hξc hξ0 ha
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|a*F x| ≤ |a| *B := fun x => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg a)
  have hw := lipschitz_exp_bounded hV (fun x => (le_abs_self _).trans (hVB x))
  have hwB : ∀ x,|Real.exp (a*F x)| ≤ Real.exp (|a| *B) := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hVB x))
  exact hrcd.test_integratedBochner hN hfull hfin o hg (lipschitz_mul_bounded hξ hw hC hwB)
    hξc.mul_right (fun x => mul_nonneg (hξ0 x) (Real.exp_pos _).le)
end WeakHessian

end
end InlinedFile112

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated_oai.{u_1} := @OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated_oai.{u_1}
