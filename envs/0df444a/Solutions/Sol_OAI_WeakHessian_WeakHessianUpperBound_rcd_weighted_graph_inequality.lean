-- Prove2me | solution 1 for OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:08:05.618349+00:00
-- url     : https://prove2.me/submissions/97bc934f-c4ed-4acd-8dea-0611cc50eaf6

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_contraction_weighted
import Theorems.Thm_OAI_WeakHessian_RCD_compact_core_localized_sobolev
import Theorems.Thm_OAI_WeakHessian_RCD_compact_core_weak_equation
import Theorems.Thm_OAI_WeakHessian_RCD_test_comp_contDiff_bounded_laplacian
import Theorems.Thm_OAI_WeakHessian_RCD_test_gradientSquare_sobolev
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_rcd_core_integrated

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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_DriftResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile148
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma norm_gamma_toLp_le (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V u : X → ℝ}
    {L : ℝ≥0} (hV : LipschitzWith L V) (hu : Sobolev m u) :
    ‖(memLp_gamma_of_lipschitz hfinite hpar hV hu).toLp (gamma m V u)‖ ≤
      (L:ℝ)*‖hu.2.2.toLp (weakGradient m u)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(memLp_gamma_of_lipschitz hfinite hpar hV hu).coeFn_toLp,hu.2.2.coeFn_toLp,
    abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.2.1,
    weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u]
    with x hb hd hab hv hn
  rw [hb,hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hn]
  exact hab.trans (mul_le_mul_of_nonneg_right hv hn)
end WeakHessian

end
end InlinedFile148

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Smul
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

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FiniteOnBoundedSets.of_le_smul (hfinite : FiniteOnBoundedSets m) {C : ℝ≥0}
    (hν : ν ≤ (C:ℝ≥0∞) • m) : FiniteOnBoundedSets ν := by
  intro s hs
  have H : (C:ℝ≥0∞)*m s < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hfinite s hs)
  exact lt_of_le_of_lt (hν s) (by simpa only [Measure.smul_apply,smul_eq_mul] using H)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalGradientParallelogram.change_measure (hpar : LocalGradientParallelogram m)
    {C D : ℝ≥0} (hm : m ≤ (C:ℝ≥0∞) • ν) (hν : ν ≤ (D:ℝ≥0∞) • m) :
    LocalGradientParallelogram ν := by
  intro f g hf hg
  have hfm := (localSobolev_iff_of_comparable hm hν f).mpr hf
  have hgm := (localSobolev_iff_of_comparable hm hν g).mpr hg
  apply (Measure.absolutelyContinuous_of_le_smul hν).ae_le
  filter_upwards [hpar f g hfm hgm,weakGradient_eq_of_comparable hm hν f,
    weakGradient_eq_of_comparable hm hν g,
    weakGradient_eq_of_comparable hm hν (fun x => f x+g x),
    weakGradient_eq_of_comparable hm hν (fun x => f x-g x)] with x hp hf hg hplus hminus
  rwa [hf,hg,hplus,hminus] at hp

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma exponentialMeasure_neg {V : X → ℝ} (hV : AEMeasurable V m) :
    exponentialMeasure (exponentialMeasure m V) (fun x => -V x) = m := by
  change (m.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-V x))) = m
  have h1 : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (V x))) m :=
    (Real.measurable_exp.comp_aemeasurable hV).ennreal_ofReal
  have h2 : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (-V x))) m :=
    (Real.measurable_exp.comp_aemeasurable hV.neg).ennreal_ofReal
  rw [← withDensity_mul₀ h1 h2]
  convert withDensity_one (μ := m) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add,add_neg_cancel,Real.exp_zero,ENNReal.ofReal_one,Pi.one_apply]

lemma IsLaplacian.of_exponentialMeasure (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A V : X → ℝ}
    {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (hA : IsLaplacian (exponentialMeasure m V) u A) :
    IsLaplacian m u (fun x => A x-gamma m V u x) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hnfinite := hfinite.of_le_smul (C := (Real.exp B).toNNReal) hν
  have hnpar := hpar.change_measure (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν
  have hnB : ∀ x, |(-V x)| ≤ B := fun x => by simpa only [abs_neg] using hB x
  have H := hA.reweight hnfinite hnpar hV.neg hnB
  dsimp only [Pi.neg_def] at H
  rw [exponentialMeasure_neg hV.continuous.aemeasurable] at H
  apply H.congr_ae EventuallyEq.rfl
  have hu : Sobolev m u := (sobolev_exponentialMeasure_iff hB u).mpr hA.1
  filter_upwards [gamma_exponentialMeasure (m := m) hB (fun x => -V x) u,
    gamma_neg_left hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.2.1] with x hc hn
  rw [← hc,hn,sub_eq_add_neg]

end WeakHessian

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
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ChangeLpLp
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
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma changeLp_toLp {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Lp.LpToLpOfMeasureLeSMul hc hν (hf.toLp f) =
      (hf.of_measure_le_smul hc hν).toLp f := by
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν (hf.toLp f)).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.coeFn_toLp).trans
      (hf.of_measure_le_smul hc hν).coeFn_toLp.symm)

omit [MetricSpace X] [BorelSpace X] in
lemma tendsto_toLp_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {fs : ℕ → X → ℝ} {f : X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m)
    (h : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ((hfs n).of_measure_le_smul hc hν).toLp (fs n))
      atTop (𝓝 ((hf.of_measure_le_smul hc hν).toLp f)) := by
  have H := (Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν).continuous.tendsto _ |>.comp h
  simpa only [Function.comp_def, changeLp_toLp] using H

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
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RootApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile6
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

lemma rootClip_lipschitz (B : ℝ) : LipschitzWith 1 (rootClip B) :=
  (LipschitzWith.const_min LipschitzWith.id B).const_max 0
lemma rootClip_nonneg (B r : ℝ) : 0 ≤ rootClip B r := le_max_left _ _
lemma rootClip_le {B : ℝ} (hB : 0 ≤ B) (r : ℝ) : rootClip B r ≤ B :=
  max_le hB (min_le_left _ _)
end WeakHessian

end
end InlinedFile6

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

end WeakHessian

end
end InlinedFile80

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

end WeakHessian

end
end InlinedFile111

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_LipschitzPointLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile123
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

lemma lipschitz_point_pairing_bound {g : X → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (u q : Lp ℝ 2 m) (he : g =ᵐ[m] u)
    (hq : Integrable (q : X → ℝ) m) (hqn : ∀ᵐ y ∂m,0 ≤ q y)
    (hqm : ∫ y,q y ∂m = 1) (x : X) {r : ℝ} (hr : 0 ≤ r)
    (hqs : ∀ᵐ y ∂m,r < dist y x → q y = 0) :
    |g x-⟪u,q⟫_ℝ| ≤ (L:ℝ)*r := by
  have hg2 : MemLp g 2 m := (memLp_congr_ae he).mpr (Lp.memLp u)
  have hi1 : Integrable (fun y => q y*g x) m := hq.mul_const _
  have hi2 : Integrable (fun y => q y*g y) m := (Lp.memLp q).integrable_mul hg2
  have hei : (∫ y,q y*g y ∂m) = ⟪u,q⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    simp only [RCLike.inner_apply,conj_trivial,hy]
  have hi : Integrable (fun y => q y*g x-q y*g y) m := hi1.sub hi2
  have hh : (∫ y,q y*g x-q y*g y ∂m) = g x-⟪u,q⟫_ℝ := by
    rw [integral_sub hi1 hi2,integral_mul_const,hqm,hei,one_mul]
  rw [← hh]
  calc
    |∫ y,q y*g x-q y*g y ∂m| ≤ ∫ y,|q y*g x-q y*g y| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ y,q y*((L:ℝ)*r) ∂m := by
      apply integral_mono_ae hi.norm (hq.mul_const _)
      filter_upwards [hqn,hqs] with y hn hs
      change |q y*g x-q y*g y| ≤ _
      rw [← mul_sub,abs_mul,abs_of_nonneg hn]
      by_cases hb : dist y x ≤ r
      · simpa only [mul_comm] using mul_le_mul ((show |g x-g y| ≤ (L:ℝ)*dist y x by
          simpa only [Real.dist_eq,dist_comm] using hg.dist_le_mul x y).trans
          (mul_le_mul_of_nonneg_left hb L.coe_nonneg)) (le_refl (q y)) hn
          (mul_nonneg L.coe_nonneg hr)
      · simp only [hs (lt_of_not_ge hb),zero_mul,le_refl]
    _ = (L:ℝ)*r := by rw [integral_mul_const,hqm,one_mul]

omit [MetricSpace X] in
lemma setDensity_integrable (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    Integrable (setDensity S hS hfin : X → ℝ) m := by
  apply Integrable.congr _ (setDensity_coe S hS hfin).symm
  exact (integrableOn_const (C := (m S).toReal⁻¹) hfin).integrable_indicator hS

lemma lipschitz_point_tendsto_of_L2 [BorelSpace X] {ι : Type*} {l : Filter ι}
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {gs : ι → X → ℝ} {g : X → ℝ} {L M : ℝ≥0}
    (hg : ∀ i,LipschitzWith L (gs i)) (hg0 : LipschitzWith M g)
    (us : ι → Lp ℝ 2 m) (u : Lp ℝ 2 m)
    (he : ∀ i,gs i =ᵐ[m] us i) (he0 : g =ᵐ[m] u)
    (ht : Tendsto us l (𝓝 u)) (x : X) :
    Tendsto (fun i => gs i x) l (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := ε/(4*((L:ℝ)+(M:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hm : m (Metric.closedBall x r) ≠ ∞ := ne_of_lt (hfin _ Metric.isBounded_closedBall)
  have hp : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let q := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet hm
  have hq := setDensity_integrable _ Metric.isClosed_closedBall.measurableSet hm
  have hqn := setDensity_nonneg _ Metric.isClosed_closedBall.measurableSet hm
  have hqm := setDensity_mass _ Metric.isClosed_closedBall.measurableSet hm hp
  have hqs := setDensity_supported _ Metric.isClosed_closedBall.measurableSet hm x (Subset.refl _)
  have Ht : Tendsto (fun i => ⟪us i,q⟫_ℝ) l (𝓝 ⟪u,q⟫_ℝ) := ht.inner tendsto_const_nhds
  filter_upwards [Metric.tendsto_nhds.mp Ht (ε/2) (half_pos hε)] with i hi
  rw [Real.dist_eq] at hi ⊢
  have H1 := lipschitz_point_pairing_bound (hg i) (us i) q (he i) hq hqn hqm x hr.le hqs
  have H2 := lipschitz_point_pairing_bound hg0 u q he0 hq hqn hqm x hr.le hqs
  have H3 : |gs i x-g x| ≤ |gs i x-⟪us i,q⟫_ℝ|+|⟪us i,q⟫_ℝ-⟪u,q⟫_ℝ|+|g x-⟪u,q⟫_ℝ| := by
    have HH := abs_add_le (gs i x-⟪us i,q⟫_ℝ) (⟪us i,q⟫_ℝ-g x)
    have HH2 := abs_sub_le ⟪us i,q⟫_ℝ ⟪u,q⟫_ℝ (g x)
    rw [abs_sub_comm ⟪u,q⟫_ℝ (g x)] at HH2
    ring_nf at HH
    linarith
  have hsmall : ((L:ℝ)+(M:ℝ))*r < ε/2 := by
    dsimp [r]
    have hp : 0 < 4*((L:ℝ)+(M:ℝ)+1) := by positivity
    apply (lt_div_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
    field_simp
    nlinarith [L.coe_nonneg,M.coe_nonneg]
  linarith
end WeakHessian

end
end InlinedFile123

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CaccioppoliAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile166
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_caccioppoli_identity (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {w η : X → ℝ} (hw : Sobolev m w) {L : ℝ≥0} (hη : LipschitzWith L η)
    (hη1 : ∀ x,|η x| ≤ 1) :
    ∀ᵐ x ∂m,gamma m w (fun y => w y*(η y*η y)) x + w x^2*(weakGradient m η x)^2 =
      (weakGradient m (fun y => w y*η y) x)^2 := by
  have hηs := localSobolev_of_lipschitz hfin hη
  have hηB := ae_of_all m hη1
  have hηD : ∀ᵐ x ∂m,|weakGradient m η x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) η,weakGradient_le_lipschitz hfin hη] with x hn hb
    rwa [abs_of_nonneg hn]
  have hus := hw.mul_bounded hfin hηs hηB hηD
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hηsqB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hηsqD : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  filter_upwards [gamma_mul_left hfin hpar hw.2.1 (localSobolev_of_lipschitz hfin hηsq) hw.2.1 hηsqB hηsqD,
    gamma_mul_left hfin hpar hηs hηs hw.2.1 hηB hηD,
    gamma_mul_left hfin hpar hw.2.1 hηs hus.2.1 hηB hηD,
    gamma_mul_left hfin hpar hw.2.1 hηs hηs hηB hηD,
    gamma_mul_left hfin hpar hw.2.1 hηs hw.2.1 hηB hηD,
    gamma_comm (m := m) w (fun y => w y*(η y*η y)),
    gamma_comm (m := m) η (fun y => w y*η y),
    gamma_comm (m := m) w (fun y => w y*η y),gamma_comm (m := m) η w,
    gamma_self (m := m) η,gamma_self (m := m) (fun y => w y*η y)]
    with x h1 h2 h3 h4 h5 hc1 hc2 hc3 hc4 hs1 hs2
  rw [hc1,h1,h2,← hs2,h3,hc2,hc3,h4,h5,hs1,hc4]
  ring

lemma integral_gamma_caccioppoli_lower (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {w η : X → ℝ} (hw : Sobolev m w) {L : ℝ≥0} (hη : LipschitzWith L η)
    (hη1 : ∀ x,|η x| ≤ 1) :
    -((L:ℝ)^2*(∫ x,w x^2 ∂m)) ≤ ∫ x,gamma m w (fun y => w y*(η y*η y)) x ∂m := by
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hD : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  have hv := hw.mul_bounded hfin (localSobolev_of_lipschitz hfin hηsq) hB hD
  have hpoint : ∀ᵐ x ∂m,-((L:ℝ)^2*w x^2) ≤ gamma m w (fun y => w y*(η y*η y)) x := by
    filter_upwards [gamma_caccioppoli_identity hfin hpar hw hη hη1,
      weakGradient_le_lipschitz hfin hη,weakGradient_nonneg (m := m) η] with x he hl hn
    have hsq := sq_le_sq₀ hn L.coe_nonneg |>.mpr hl
    have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (w x))
    nlinarith only [he,hm,sq_nonneg (weakGradient m (fun y => w y*η y) x)]
  simpa only [Pi.neg_apply,integral_neg,integral_const_mul] using
    integral_mono_ae ((hw.1.integrable_sq.const_mul ((L:ℝ)^2)).neg) (integrable_gamma hfin hw hv) hpoint
end WeakHessian

end
end InlinedFile166

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AverageConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile122
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_average_tendsto (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    Tendsto (fun t : ℝ => t⁻¹ • ∫ s in 0..t,cheegerHeat h s u) (𝓝[>] 0) (𝓝 u) := by
  let f (s : ℝ) := cheegerHeat h (max s 0) u
  have hc : Continuous f := by
    apply (cheegerHeat_continuousOn hfin h u).comp_continuous (continuous_id.max continuous_const)
    exact fun s => le_max_right s 0
  have hd := intervalIntegral.integral_hasDerivAt_right
    (f := f) (a := 0) (b := 0) (by simp)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have HH := hd.tendsto_slope_zero_right
  simp only [zero_add,intervalIntegral.integral_same,sub_zero,f,max_self,cheegerHeat_zero,one_apply_eq_self] at HH
  apply HH.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (le_of_lt ht)] at hs
  dsimp only
  rw [max_eq_left hs.1]
end WeakHessian

end
end InlinedFile122

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile116
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_integral_formGenerator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator
      (∫ s in 0..t,cheegerHeat h s u) (cheegerHeat h t u-u) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := Q.resolventLinear
  have hi (v : Lp ℝ 2 m) : IntervalIntegrable (fun s => cheegerHeat h s v) volume 0 t :=
    ((cheegerHeat_continuousOn hfin h v).mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
  have he : ∀ s,cheegerHeat h s (R u) = R (cheegerHeat h s u) :=
    fun s => realHeat_resolvent m Q.resolvent_positive s u
  have H := cheegerHeat_integral_generator hfin h (Q.isFormGenerator_resolvent u) ht
  change (∫ s in 0..t,cheegerHeat h s (R u-u)) = cheegerHeat h t (R u)-R u at H
  simp_rw [map_sub,he] at H
  rw [intervalIntegral.integral_sub ⟨R.integrable_comp (hi u).1,R.integrable_comp (hi u).2⟩ (hi u),
    R.intervalIntegral_comp_comm (hi u)] at H
  apply (Q.isFormGenerator_iff _ _).mpr
  change R ((∫ s in 0..t,cheegerHeat h s u)-(cheegerHeat h t u-u)) = _
  rw [map_sub,map_sub]
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp H).trans (add_comm _ _))

lemma cheegerHeat_average_formGenerator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator
      (t⁻¹ • ∫ s in 0..t,cheegerHeat h s u) (t⁻¹ • (cheegerHeat h t u-u)) :=
  (cheeger_closedQuadraticEnergy h).formGenerator_smul _ (cheegerHeat_integral_formGenerator hfin h u ht)
end WeakHessian

end
end InlinedFile116

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AverageLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile117
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma inner_heat_average_bound (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (u w : Lp ℝ 2 m) {t C : ℝ} (ht : 0 < t)
    (hb : ∀ s ∈ Ioc (0:ℝ) t, |⟪cheegerHeat h s u,w⟫_ℝ| ≤ C) :
    |⟪t⁻¹ • (∫ s in 0..t,cheegerHeat h s u),w⟫_ℝ| ≤ C := by
  have hi : IntervalIntegrable (fun s => cheegerHeat h s u) volume 0 t :=
    ((cheegerHeat_continuousOn hfin h u).mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have he : ⟪(∫ s in 0..t,cheegerHeat h s u),w⟫_ℝ = ∫ s in 0..t,⟪cheegerHeat h s u,w⟫_ℝ := by
    calc
      _ = ⟪w,(∫ s in 0..t,cheegerHeat h s u)⟫_ℝ := real_inner_comm _ _
      _ = ∫ s in 0..t,⟪w,cheegerHeat h s u⟫_ℝ := ((innerSL ℝ w).intervalIntegral_comp_comm hi).symm
      _ = _ := intervalIntegral.integral_congr (fun s _ => real_inner_comm _ _)
  rw [real_inner_smul_left,he,abs_mul,abs_inv,abs_of_pos ht]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => ⟪cheegerHeat h s u,w⟫_ℝ) (C := C) (fun s hs => by
      rw [uIoc_of_le ht.le] at hs
      simpa only [Real.norm_eq_abs] using hb s hs)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos ht] at H
  calc t⁻¹ * |∫ s in 0..t,⟪cheegerHeat h s u,w⟫_ℝ| ≤ t⁻¹*(C*t) := mul_le_mul_of_nonneg_left H (by positivity)
       _ = C := by field_simp

lemma RCD.cheegerHeat_average_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) {D : ℝ} (hfB : ∀ x,|f x| ≤ D)
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (|K| *t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] (t⁻¹ • ∫ s in 0..t,cheegerHeat h s (hf2.toLp f) : Lp ℝ 2 m) := by
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
  have heq (v : Lp ℝ 2 m) (x : X) : ⟪v,u x⟫_ℝ = (⨍ z in Metric.closedBall x r,v z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  have H := inner_heat_average_bound hfin h (hf2.toLp f) (u x-u y) ht
    (C := (L:ℝ)*Real.exp (|K| *t)*(2*r+dist x y)) (by
      intro s hst
      rw [inner_sub_right]
      have H := hrcd.cheegerHeat_pairing_balls hN hfull hfin h hf hf2 hfB (u x) (u y)
        (hn x) (hn y) (hmass x) (hmass y) (by positivity) (by positivity) (hb x) (hb y) x y hr.le hr.le (hs x) (hs y) hst.1.le
      apply H.trans
      rw [← two_mul r]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right (neg_le_abs K) hst.1.le).trans
        (mul_le_mul_of_nonneg_left hst.2 (abs_nonneg K)))
  rw [inner_sub_right,heq _ x,heq _ y] at H
  exact H
end WeakHessian

end
end InlinedFile117

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_VolumeLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile113
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma CurvatureDimension.ball_measure_lower_exp {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {r : ℝ} (hr : 0 < r) :
    ∃ A B : ℝ,0 < A ∧ 0 ≤ B ∧ ∀ x : X,
      A*Real.exp (-B*dist x o) ≤ (m (Metric.ball x r)).toReal := by
  let C := N*Real.log 2+4*Real.sqrt (|K|/(N-1))*(N-1)*r
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
      (by positivity)
  have hp (x : X) (s : ℝ) (hs : 0 < s) : 0 < (m (Metric.ball x s)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hs⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  refine ⟨(m (Metric.ball o (r/2))).toReal*Real.exp (-3*C),2*C/r,
    mul_pos (hp o _ (by positivity)) (Real.exp_pos _),by positivity,?_⟩
  intro x
  let n := ⌈2*dist x o/r+1⌉₊+1
  have hd : 0 ≤ 2*dist x o/r+1 := by positivity
  have hnL : 2*dist x o/r+1 < (n:ℝ) := by
    have h := Nat.le_ceil (2*dist x o/r+1)
    dsimp only [n]
    push_cast
    linarith
  have hnU : (n:ℝ) < 2*dist x o/r+3 := by
    have h := Nat.ceil_lt_add_one hd
    dsimp only [n]
    push_cast
    linarith
  have hn : 0 < (n:ℝ) := lt_of_le_of_lt hd hnL
  have hR : 0 < r/2*(n:ℝ) := by positivity
  have hsub : Metric.ball o (r/2) ⊆ Metric.ball x (r/2*(n:ℝ)) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm o]
    have hh := (div_lt_iff₀ hr).mp (by linarith : 2*dist x o/r < (n:ℝ)-1)
    linarith
  have hsmall : (3/4:ℝ)^n*(r/2*(n:ℝ)) ≤ r := by
    have hh := mul_le_mul_of_nonneg_left (decay_times_nat_le_two n) (show 0 ≤ r/2 by positivity)
    nlinarith
  have H := cd_log_iterated_ball hN hcd hfull hfin x hR n
  have HS := Real.log_le_log (hp x _ (by positivity : 0 < (3/4:ℝ)^n*(r/2*(n:ℝ))))
    (ENNReal.toReal_mono (hfin _ Metric.isBounded_ball).ne
      (measure_mono (Metric.ball_subset_ball hsmall)))
  have HB := Real.log_le_log (hp o _ (by positivity))
    (ENNReal.toReal_mono (hfin _ Metric.isBounded_ball).ne (measure_mono hsub))
  have hS : 0 ≤ 4*Real.sqrt (|K|/(N-1))*(N-1)*r*(n:ℝ) := by positivity
  have HI : Real.log (m (Metric.ball o (r/2))).toReal ≤
      Real.log (m (Metric.ball x r)).toReal+C*(n:ℝ) := by
    have hprod := mul_nonneg hS (pow_nonneg (by norm_num : 0 ≤ (3/4:ℝ)) n)
    dsimp only [C]
    nlinarith
  have HU := mul_le_mul_of_nonneg_left hnU.le hC
  have HE := Real.exp_le_exp.mpr (show
      Real.log (m (Metric.ball o (r/2))).toReal-3*C-(2*C/r)*dist x o ≤
        Real.log (m (Metric.ball x r)).toReal from by
      have he : C*(2*dist x o/r+3) = 3*C+(2*C/r)*dist x o := by ring
      rw [he] at HU
      linarith)
  rw [Real.exp_log (hp x r hr),Real.exp_sub,Real.exp_sub,
    Real.exp_log (hp o _ (by positivity))] at HE
  simpa only [neg_mul,Real.exp_neg,div_eq_mul_inv] using HE
end WeakHessian

end
end InlinedFile113

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedCZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile114
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma lipschitz_vanishes_of_expWeighted (hfin : FiniteOnBoundedSets m) (o : X)
    (hvol : ∀ r : ℝ,0 < r → ∃ A B : ℝ,0 < A ∧ 0 ≤ B ∧ ∀ x : X,
      A*Real.exp (-B*dist x o) ≤ (m (Metric.ball x r)).toReal)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hw : ∀ a : ℝ,0 ≤ a → MemLp (fun x => g x*Real.exp (a*dist x o)) 2 m) :
    ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε := by
  intro ε hε
  let r := ε/(2*((L:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r*(2*((L:ℝ)+1)) = ε := by dsimp [r]; field_simp
  have hrL : (L:ℝ)*r ≤ ε/2 := by nlinarith
  obtain ⟨A,B,hA,hB,hvolr⟩ := hvol r hr
  let a := (B+1)/2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have haa : 2*a-B = 1 := by dsimp [a]; ring
  let I := ∫ y,(g y*Real.exp (a*dist y o))^2 ∂m
  have hi := (memLp_two_iff_integrable_sq (hw a ha).aestronglyMeasurable).mp (hw a ha)
  let c := A*(ε/2)^2*Real.exp (-2*a*r)
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨max 0 (I/c+1),le_max_left _ _,?_⟩
  intro x hx
  by_contra hbad
  have hgx : ε ≤ |g x| := le_of_not_gt hbad
  have hball (y : X) (hy : y ∈ Metric.ball x r) :
      (ε/2)^2*Real.exp (2*a*(dist x o-r)) ≤ (g y*Real.exp (a*dist y o))^2 := by
    have hxy : dist x y < r := by simpa only [Metric.mem_ball,dist_comm] using hy
    have hl := hg.dist_le_mul x y
    rw [Real.dist_eq] at hl
    have hab : |g x|-|g y| ≤ |g x-g y| := abs_sub_abs_le_abs_sub _ _
    have hgy : ε/2 ≤ |g y| := by
      have hh := mul_le_mul_of_nonneg_left hxy.le L.2
      have H := hab.trans (hl.trans (hh.trans hrL))
      have H' : ε-ε/2 ≤ |g y| := (sub_le_iff_le_add'.mpr (hgx.trans (sub_le_iff_le_add.mp H)))
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hd : dist x o-r ≤ dist y o := by linarith [dist_triangle x y o]
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*a by positivity))
    have hs : (ε/2)^2 ≤ (g y)^2 := by
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ε/2) hgy 2
      simpa only [sq_abs] using hh
    rw [mul_pow,sq_exp_eq]
    have heq : 2*(a*dist y o) = 2*a*dist y o := by ring
    rw [heq]
    exact mul_le_mul hs he (Real.exp_pos _).le (sq_nonneg _)
  have hlocal := setIntegral_ge_of_const_le_real Metric.isOpen_ball.measurableSet
    (hfin _ Metric.isBounded_ball).ne hball hi.integrableOn
  have htot : (∫ y in Metric.ball x r,(g y*Real.exp (a*dist y o))^2 ∂m) ≤ I := integral_mono_measure m.restrict_le_self (ae_of_all _ (fun y => sq_nonneg (g y*Real.exp (a*dist y o)))) hi
  have hv := mul_le_mul_of_nonneg_left (hvolr x)
    (show 0 ≤ (ε/2)^2*Real.exp (2*a*(dist x o-r)) by positivity)
  have heq : (ε/2)^2*Real.exp (2*a*(dist x o-r))*(A*Real.exp (-B*dist x o)) = c*Real.exp (dist x o) := by
    dsimp only [c]
    rw [show 2*a*(dist x o-r) = -2*a*r+2*a*dist x o by ring,Real.exp_add]
    calc
      _ = A*(ε/2)^2*Real.exp (-2*a*r)*(Real.exp (2*a*dist x o)*Real.exp (-B*dist x o)) := by ring
      _ = _ := by
        rw [← Real.exp_add,show 2*a*dist x o+-B*dist x o = dist x o by
          calc
            _ = (2*a-B)*dist x o := by ring
            _ = _ := by rw [haa,one_mul]]
  rw [heq] at hv
  have hupper : c*Real.exp (dist x o) ≤ I := by
    exact hv.trans (hlocal.trans htot)
  have hlarge : I/c+1 < dist x o := (le_max_right _ _).trans_lt hx
  have hd := Real.add_one_le_exp (dist x o)
  have hiC : I/c*c = I := div_mul_cancel₀ _ hc.ne'
  have hstrict := mul_lt_mul_of_pos_left hlarge hc
  have hlow := mul_le_mul_of_nonneg_left hd hc.le
  nlinarith

lemma CurvatureDimension.lipschitz_vanishes_of_expWeighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hN : 1 < N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {g : X → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g)
    (hw : ∀ a : ℝ,0 ≤ a → MemLp (fun x => g x*Real.exp (a*dist x o)) 2 m) :
    ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε :=
  WeakHessian.lipschitz_vanishes_of_expWeighted hfin o
    (fun _ hr => hcd.ball_measure_lower_exp hN hfull hfin o hr) hg hw
end WeakHessian

end
end InlinedFile114

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AverageWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile118
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.cheegerHeat_average_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {V : X → ℝ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    {t : ℝ} (ht : 0 < t) :
    MemLp (fun x => (t⁻¹ • ∫ s in 0..t,cheegerHeat h s u : Lp ℝ 2 m) x*Real.exp (V x)) 2 m ∧
      (∫ x,((t⁻¹ • ∫ s in 0..t,cheegerHeat h s u : Lp ℝ 2 m) x*Real.exp (V x))^2 ∂m) ≤
      (‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t))^2 := by
  let C := ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)
  have hi : IntervalIntegrable (fun s => cheegerHeat h s u) volume 0 t :=
    ((cheegerHeat_continuousOn hfin h u).mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  apply memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
  intro n
  let T := expMulLp (m := m) (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ)))
  have hb (s : ℝ) (hs : s ∈ Ioc (0:ℝ) t) : ‖T (cheegerHeat h s u)‖ ≤ C := by
    have H := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable (cheegerHeat h s u)
      (hcd.cheegerHeat_weighted hfin o h u hV hU hs.1.le).1 n
    exact H.trans ((hcd.cheegerHeat_weighted_norm hfin o h u hV hU hs.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))) (norm_nonneg _)))
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => T (cheegerHeat h s u)) (C := C) (fun s hs => by
      rw [uIoc_of_le ht.le] at hs
      exact hb s hs)
  rw [T.intervalIntegral_comp_comm hi,sub_zero,abs_of_pos ht] at H
  have Hav : ‖T (t⁻¹ • ∫ s in 0..t,cheegerHeat h s u)‖ ≤ C := by
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
    calc t⁻¹ * ‖T (∫ s in 0..t,cheegerHeat h s u)‖ ≤ t⁻¹*(C*t) := mul_le_mul_of_nonneg_left H (by positivity)
         _ = C := by field_simp
  exact pow_le_pow_left₀ (norm_nonneg _) Hav 2

lemma RCD.cheegerHeat_average_compactDatum_CZero {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m)
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (|K| *t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] (t⁻¹ • ∫ s in 0..t,cheegerHeat h s (hf2.toLp f) : Lp ℝ 2 m) ∧
      ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  obtain ⟨g,hg,hge⟩ := hrcd.cheegerHeat_average_lipschitz hN hfull hfin h hf hf2
    (fun x => by simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩) ht
  refine ⟨g,hg,hge,hrcd.1.lipschitz_vanishes_of_expWeighted hN hfull hfin o hg ?_⟩
  intro a ha
  have hV := lipschitz_mul_dist o a
  have hWf : MemLp (fun x => f x*Real.exp (a*dist x o)) 2 m :=
    (hf.continuous.mul (Real.continuous_exp.comp hV.continuous)).memLp_of_hasCompactSupport hfc.mul_right
  have hWu : MemLp (fun x => hf2.toLp f x*Real.exp (a*dist x o)) 2 m :=
    (memLp_congr_ae (hf2.coeFn_toLp.mul (Filter.EventuallyEq.rfl)).symm).mp hWf
  have H := (hrcd.1.cheegerHeat_average_weighted hfin o h (hf2.toLp f) hV hWu ht).1
  exact (memLp_congr_ae (hge.mul Filter.EventuallyEq.rfl).symm).mp H
end WeakHessian

end
end InlinedFile118

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AverageTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile119
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma bounded_of_vanishes_infinity (o : X) {g : X → ℝ} (hg : Continuous g)
    (hv : ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε) :
    BoundedFunction g := by
  obtain ⟨R,_hR,hgR⟩ := hv 1 zero_lt_one
  obtain ⟨B,hB⟩ := ((isCompact_closedBall o R).image hg).isBounded.exists_norm_le
  refine ⟨max B 1,fun x => ?_⟩
  by_cases hx : dist x o ≤ R
  · exact (show |g x| ≤ B from by simpa only [Real.norm_eq_abs] using hB (g x) ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  · exact ((hgR x (lt_of_not_ge hx)).le).trans (le_max_right _ _)

lemma RCD.cheegerHeat_average_test {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m)
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,IsTestFunction m g ∧
      LipschitzWith (L*⟨Real.exp (|K| *t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] (t⁻¹ • ∫ s in 0..t,cheegerHeat h s (hf2.toLp f) : Lp ℝ 2 m) ∧
      (∃ B : ℝ,∀ᵐ x ∂m,|laplacian m g x| ≤ B) ∧
      ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε := by
  obtain ⟨g,hg,hge,hgz⟩ := hrcd.cheegerHeat_average_compactDatum_CZero hN hfull hfin h o hf hfc hf2 ht
  let u := hf2.toLp f
  let v := t⁻¹ • ∫ s in 0..t,cheegerHeat h s u
  let A := t⁻¹ • (cheegerHeat h t u-u)
  have hgen := hrcd.1.global_isLaplacian_of_formGenerator hfin o h v A
    (cheegerHeat_average_formGenerator hfin h u ht.le)
  have hggen : IsLaplacian m g A := hgen.congr_ae hge.symm Filter.EventuallyEq.rfl
  have hsf := sobolev_of_lipschitz_compactSupport hfin hf hfc
  have hsu : Sobolev m u := (sobolev_congr_ae hf2.coeFn_toLp).mpr hsf
  have hPt : Sobolev m (cheegerHeat h t u) :=
    (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp _)).mpr
      ((cheegerHeat_energy_le h ht.le u).trans_lt
        ((hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp u)).mp hsu))
  have hAs : Sobolev m A := by
    have H := (hPt.sub hfin hsu).const_mul t⁻¹
    apply (sobolev_congr_ae ?_).mp H
    filter_upwards [Lp.coeFn_smul t⁻¹ (cheegerHeat h t u-u),Lp.coeFn_sub (cheegerHeat h t u) u] with x hx hy
    dsimp only [A]
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,hy] using hx.symm
  have hlap := hggen.ae_laplacian hfin
  have gtest : IsTestFunction m g := ⟨⟨A,hggen⟩,bounded_of_vanishes_infinity o hg.continuous hgz,
    ⟨_,hg⟩,(sobolev_congr_ae hlap).mpr hAs⟩
  refine ⟨g,gtest,hg,hge,?_,hgz⟩
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  have huB : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [show u x = f x from hx]
    simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩
  have hptB := cheegerHeat_bounded h ht.le (le_trans (norm_nonneg (f o)) (hB (f o) ⟨o,rfl⟩)) u huB
  refine ⟨t⁻¹*(B+B),?_⟩
  filter_upwards [hlap,Lp.coeFn_smul t⁻¹ (cheegerHeat h t u-u),Lp.coeFn_sub (cheegerHeat h t u) u,huB,hptB] with x hl hx hy hu hp
  rw [hl]
  change |(t⁻¹ • (cheegerHeat h t u-u) : Lp ℝ 2 m) x| ≤ _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hy,Pi.sub_apply,abs_mul,abs_inv,abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hp hu)) (by positivity)
end WeakHessian

end
end InlinedFile119

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_UniformTestAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile124
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_tendstoUniformlyOn_compact {ι : Type*} {l : Filter ι}
    {gs : ι → X → ℝ} {g : X → ℝ} {L : ℝ≥0}
    (hg : ∀ i,LipschitzWith L (gs i)) (ht : ∀ x,Tendsto (fun i => gs i x) l (𝓝 (g x)))
    {S : Set X} (hS : IsCompact S) : TendstoUniformlyOn gs g l S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hl (i : ι) : LipschitzWith L (fun x : S => gs i x) := by
    simpa only [mul_one,Function.comp_def] using (hg i).comp (LipschitzWith.subtype_val S)
  have he := (LipschitzWith.uniformEquicontinuous (fun i (x:S) => gs i x) L hl).equicontinuous
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (he.tendsto_uniformFun_iff_pi l (fun x : S => g x)).mpr
  exact tendsto_pi_nhds.mpr fun x => ht x

end WeakHessian

end
end InlinedFile124

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_UniformWeightedCZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile125
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma lipschitz_uniformly_vanishes_of_expWeighted (hfin : FiniteOnBoundedSets m) (o : X)
    (hvol : ∀ r : ℝ,0 < r → ∃ A B : ℝ,0 < A ∧ 0 ≤ B ∧ ∀ x : X,
      A*Real.exp (-B*dist x o) ≤ (m (Metric.ball x r)).toReal)
    {ι : Type*} {gs : ι → X → ℝ} {L : ℝ≥0} (hg : ∀ i,LipschitzWith L (gs i))
    (hw : ∀ a : ℝ,0 ≤ a → ∃ J : ℝ,∀ i,MemLp (fun x => gs i x*Real.exp (a*dist x o)) 2 m ∧
      (∫ x,(gs i x*Real.exp (a*dist x o))^2 ∂m) ≤ J) :
    ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ i,∀ x : X,R < dist x o → |gs i x| < ε := by
  intro ε hε
  let r := ε/(2*((L:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r*(2*((L:ℝ)+1)) = ε := by dsimp [r]; field_simp
  have hrL : (L:ℝ)*r ≤ ε/2 := by nlinarith
  obtain ⟨A,B,hA,hB,hvolr⟩ := hvol r hr
  let a := (B+1)/2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have haa : 2*a-B = 1 := by dsimp [a]; ring
  obtain ⟨I,hI⟩ := hw a ha
  let c := A*(ε/2)^2*Real.exp (-2*a*r)
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨max 0 (I/c+1),le_max_left _ _,?_⟩
  intro i x hx
  let g := gs i
  change |g x| < ε
  have hi := (memLp_two_iff_integrable_sq (hI i).1.aestronglyMeasurable).mp (hI i).1
  by_contra hbad
  have hgx : ε ≤ |g x| := le_of_not_gt hbad
  have hball (y : X) (hy : y ∈ Metric.ball x r) :
      (ε/2)^2*Real.exp (2*a*(dist x o-r)) ≤ (g y*Real.exp (a*dist y o))^2 := by
    have hxy : dist x y < r := by simpa only [Metric.mem_ball,dist_comm] using hy
    have hl := (hg i).dist_le_mul x y
    rw [Real.dist_eq] at hl
    have hab : |g x|-|g y| ≤ |g x-g y| := abs_sub_abs_le_abs_sub _ _
    have hgy : ε/2 ≤ |g y| := by
      have hh := mul_le_mul_of_nonneg_left hxy.le L.2
      have H := hab.trans (hl.trans (hh.trans hrL))
      have H' : ε-ε/2 ≤ |g y| := (sub_le_iff_le_add'.mpr (hgx.trans (sub_le_iff_le_add.mp H)))
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hd : dist x o-r ≤ dist y o := by linarith [dist_triangle x y o]
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*a by positivity))
    have hs : (ε/2)^2 ≤ (g y)^2 := by
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ε/2) hgy 2
      simpa only [sq_abs] using hh
    rw [mul_pow,sq_exp_eq]
    have heq : 2*(a*dist y o) = 2*a*dist y o := by ring
    rw [heq]
    exact mul_le_mul hs he (Real.exp_pos _).le (sq_nonneg _)
  have hlocal := setIntegral_ge_of_const_le_real Metric.isOpen_ball.measurableSet
    (hfin _ Metric.isBounded_ball).ne hball hi.integrableOn
  have htot : (∫ y in Metric.ball x r,(g y*Real.exp (a*dist y o))^2 ∂m) ≤ I := (integral_mono_measure m.restrict_le_self (ae_of_all _ (fun y => sq_nonneg (g y*Real.exp (a*dist y o)))) hi).trans (hI i).2
  have hv := mul_le_mul_of_nonneg_left (hvolr x)
    (show 0 ≤ (ε/2)^2*Real.exp (2*a*(dist x o-r)) by positivity)
  have heq : (ε/2)^2*Real.exp (2*a*(dist x o-r))*(A*Real.exp (-B*dist x o)) = c*Real.exp (dist x o) := by
    dsimp only [c]
    rw [show 2*a*(dist x o-r) = -2*a*r+2*a*dist x o by ring,Real.exp_add]
    calc
      _ = A*(ε/2)^2*Real.exp (-2*a*r)*(Real.exp (2*a*dist x o)*Real.exp (-B*dist x o)) := by ring
      _ = _ := by
        rw [← Real.exp_add,show 2*a*dist x o+-B*dist x o = dist x o by
          calc
            _ = (2*a-B)*dist x o := by ring
            _ = _ := by rw [haa,one_mul]]
  rw [heq] at hv
  have hupper : c*Real.exp (dist x o) ≤ I := by
    exact hv.trans (hlocal.trans htot)
  have hlarge : I/c+1 < dist x o := (le_max_right _ _).trans_lt hx
  have hd := Real.add_one_le_exp (dist x o)
  have hiC : I/c*c = I := div_mul_cancel₀ _ hc.ne'
  have hstrict := mul_lt_mul_of_pos_left hlarge hc
  have hlow := mul_le_mul_of_nonneg_left hd hc.le
  nlinarith

end WeakHessian

end
end InlinedFile125

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GlobalTestAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile126
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_global_test_average_approximation {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m) :
    ∃ gs : ℕ → X → ℝ,
      (∀ n,IsTestFunction m (gs n)) ∧
      (∀ n,LipschitzWith (L*⟨Real.exp |K|,(Real.exp_pos _).le⟩) (gs n)) ∧
      (∀ n,∃ B : ℝ,∀ᵐ x ∂m,|laplacian m (gs n) x| ≤ B) ∧
      (∀ n,∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |gs n x| < ε) ∧
      TendstoUniformly gs f atTop ∧
      ∃ us : ℕ → Lp ℝ 2 m,(∀ n,gs n =ᵐ[m] us n) ∧ Tendsto us atTop (𝓝 (hf2.toLp f)) := by
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let us (n : ℕ) := (t n)⁻¹ • ∫ s in 0..t n,cheegerHeat hrcd.2 s (hf2.toLp f)
  have ht0 : Tendsto t atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall ht⟩
  have hus : Tendsto us atTop (𝓝 (hf2.toLp f)) := (cheegerHeat_average_tendsto hfin hrcd.2 _).comp ht0
  choose gs hgs hgl hge hgb hgz using fun n =>
    hrcd.cheegerHeat_average_test hN hfull hfin hrcd.2 o hf hfc hf2 (ht n)
  have hgl' (n : ℕ) : LipschitzWith (L*⟨Real.exp |K|,(Real.exp_pos _).le⟩) (gs n) := by
    apply (hgl n).weaken
    apply mul_le_mul_of_nonneg_left _ (show 0 ≤ L from zero_le)
    change Real.exp (|K| *t n) ≤ Real.exp |K|
    exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg K,ht1 n])
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hv : ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ n,∀ x : X,R < dist x o → |gs n x| < ε := by
    apply lipschitz_uniformly_vanishes_of_expWeighted hfin o
      (fun _ hr => hrcd.1.ball_measure_lower_exp hN hfull hfin o hr) hgl'
    intro a ha
    have hV := lipschitz_mul_dist o a
    have hWf : MemLp (fun x => f x*Real.exp (a*dist x o)) 2 m :=
      (hf.continuous.mul (Real.continuous_exp.comp hV.continuous)).memLp_of_hasCompactSupport hfc.mul_right
    have hWu : MemLp (fun x => hf2.toLp f x*Real.exp (a*dist x o)) 2 m :=
      (memLp_congr_ae (hf2.coeFn_toLp.mul Filter.EventuallyEq.rfl).symm).mp hWf
    let W := ‖hWu.toLp (fun x => hf2.toLp f x*Real.exp (a*dist x o))‖
    refine ⟨(W*Real.exp (a^2))^2,fun n => ?_⟩
    have H := hrcd.1.cheegerHeat_average_weighted hfin o hrcd.2 (hf2.toLp f) hV hWu (ht n)
    have he : (fun x => gs n x*Real.exp (a*dist x o)) =ᵐ[m]
        (fun x => us n x*Real.exp (a*dist x o)) := (hge n).mul Filter.EventuallyEq.rfl
    refine ⟨(memLp_congr_ae he.symm).mp H.1,?_⟩
    rw [integral_congr_ae (he.mono fun x hx => congrArg (fun z : ℝ => z^2) hx)]
    apply H.2.trans
    apply pow_le_pow_left₀ (by positivity) _ 2
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    change |a|^2*t n ≤ a^2
    rw [sq_abs]
    nlinarith [sq_nonneg a,ht1 n]
  have hu : ∀ S : Set X,IsCompact S → TendstoUniformlyOn gs f atTop S := by
    intro S hS
    apply lipschitz_tendstoUniformlyOn_compact hgl' _ hS
    intro x
    exact lipschitz_point_tendsto_of_L2 hfull hfin hgl' hf us _ hge hf2.coeFn_toLp.symm hus x
  refine ⟨gs,hgs,hgl',hgb,hgz,?_,us,hge,hus⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨R,hR,hRgs⟩ := hv (ε/2) (by positivity)
  obtain ⟨S,hS⟩ := hfc.isCompact.isBounded.subset_closedBall o
  have H := Metric.tendstoUniformlyOn_iff.mp (hu (Metric.closedBall o (max R S)) (isCompact_closedBall o _)) ε hε
  filter_upwards [H] with n hn x
  by_cases hx : dist x o ≤ max R S
  · exact hn x hx
  · have hxR : R < dist x o := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hx)
    have hfx : f x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      have hh := hS hxt
      exact hx ((show dist x o ≤ S from hh).trans (le_max_right _ _))
    rw [hfx,dist_zero_left,Real.norm_eq_abs]
    exact (hRgs n x hxR).trans (by linarith)

end WeakHessian

end
end InlinedFile126

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_LocalizedTestCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile127
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_test_cutoff_of_compact_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hfc : HasCompactSupport f) :
    ∃ χ : X → ℝ,IsTestFunction m χ ∧ HasCompactSupport χ ∧
      (∀ x,0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ tsupport f ∧
      (∀ x,f x = 1 → χ x = 1) ∧
      ∃ B : ℝ,∀ᵐ x ∂m,|laplacian m χ x| ≤ B := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hf2 : MemLp f 2 m := hf.continuous.memLp_of_hasCompactSupport hfc
  obtain ⟨gs,hgs,hgl,hgb,hgz,hgu,us,hge,hus⟩ :=
    hrcd.exists_global_test_average_approximation hN hfull hfin o hf hfc hf2
  have HH := Metric.tendstoUniformly_iff.mp hgu (1/4) (by norm_num)
  obtain ⟨n,hn⟩ := HH.exists
  let φ : ContDiffBump (1:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have hφ : ContDiff ℝ 3 (φ : ℝ → ℝ) := φ.contDiff
  have hφ2 : ContDiff ℝ 2 (deriv (φ : ℝ → ℝ)) := hφ.deriv'
  have hφ1 : ContDiff ℝ 1 (deriv (deriv (φ : ℝ → ℝ))) := hφ2.deriv'
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport hφ (by norm_num)
  obtain ⟨D,hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport.deriv hφ2 (by norm_num)
  obtain ⟨E,hE⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport.deriv.deriv hφ1 (by norm_num)
  have hφ0 : φ 0 = 0 := φ.zero_of_le_dist (by norm_num [φ,Real.dist_eq])
  obtain ⟨B,hB⟩ := hgb n
  obtain ⟨hχ,A,hA⟩ := hrcd.test_comp_contDiff_bounded_laplacian hN hfull hfin o (hgs n) hB hφ hC hD hE hφ0
  have hsupp : tsupport (φ ∘ gs n) ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra hxt
    have hf0 := image_eq_zero_of_notMem_tsupport hxt
    have hh := hn x
    rw [hf0,dist_zero_left,Real.norm_eq_abs] at hh
    apply hx
    apply φ.zero_of_le_dist
    change (1/2:ℝ) ≤ dist (gs n x) 1
    rw [Real.dist_eq,abs_of_neg (by linarith [le_abs_self (gs n x)] : gs n x-1<0)]
    linarith [le_abs_self (gs n x)]
  refine ⟨φ ∘ gs n,hχ,hfc.of_isClosed_subset (isClosed_tsupport _) hsupp,
    fun x => ⟨φ.nonneg,φ.le_one⟩,hsupp,?_,A,hA⟩
  intro x hx
  apply φ.one_of_mem_closedBall
  have hh := hn x
  rw [hx,Real.dist_eq] at hh
  change |gs n x-1| ≤ (1/4:ℝ)
  simpa only [abs_sub_comm] using hh.le
end WeakHessian

end
end InlinedFile127

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_MetricPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile168
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma exists_compact_lipschitz_plateau {E U : Set X} (hE : IsCompact E) (hU : IsOpen U)
    (hEU : E ⊆ U) :
    ∃ f : X → ℝ,GloballyLipschitz f ∧ HasCompactSupport f ∧
      (∀ x,0 ≤ f x ∧ f x ≤ 1) ∧ tsupport f ⊆ U ∧
      ∃ V : Set X,IsOpen V ∧ E ⊆ V ∧ ∀ x ∈ V,f x = 1 := by
  by_cases hEn : E.Nonempty
  swap
  · have he : E = ∅ := not_nonempty_iff_eq_empty.mp hEn
    refine ⟨fun _ => 0,⟨0,LipschitzWith.const 0⟩,?_,fun _ => ⟨le_rfl,zero_le_one⟩,?_,∅,isOpen_empty,?_,?_⟩
    · simp [HasCompactSupport]
    · simp
    · simp [he]
    · simp
  obtain ⟨δ,hδ,hδU⟩ := hE.exists_cthickening_subset_open hU hEU
  let c : ℝ := 2/δ
  have hc : 0 < c := by dsimp [c]; positivity
  have hce : c*δ = 2 := by dsimp [c]; field_simp
  let f (x : X) : ℝ := rootClip 1 (2-c*Metric.infDist x E)
  have hfl : LipschitzWith ‖c‖₊ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (f x) (f y) ≤ dist (2-c*Metric.infDist x E) (2-c*Metric.infDist y E) := by
        simpa only [NNReal.coe_one,one_mul,f] using
          (rootClip_lipschitz 1).dist_le_mul (2-c*Metric.infDist x E) (2-c*Metric.infDist y E)
      _ = |c| *dist (Metric.infDist x E) (Metric.infDist y E) := by
        rw [dist_sub_left,Real.dist_eq,← mul_sub,abs_mul,Real.dist_eq]
      _ ≤ |c| *dist x y := mul_le_mul_of_nonneg_left
        (by simpa using (Metric.lipschitz_infDist_pt E).dist_le_mul x y) (abs_nonneg c)
  have hs : tsupport f ⊆ Metric.cthickening δ E := by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    apply Metric.thickening_subset_cthickening δ E
    apply (Metric.mem_thickening_iff_infDist_lt hEn).mpr
    by_contra HH
    have hge : δ ≤ Metric.infDist x E := le_of_not_gt HH
    have hraw : 2-c*Metric.infDist x E ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left hge hc.le]
    exact hx (show f x = 0 from max_eq_left ((min_le_right 1 _).trans hraw))
  refine ⟨f,⟨_,hfl⟩,(hE.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport f) hs,
    fun x => ⟨rootClip_nonneg _ _,rootClip_le zero_le_one _⟩,hs.trans hδU,
    Metric.thickening (δ/2) E,Metric.isOpen_thickening,
    Metric.self_subset_thickening (by positivity) E,?_⟩
  intro x hx
  have hh := (Metric.mem_thickening_iff_infDist_lt hEn).mp hx
  have hraw : 1 ≤ 2-c*Metric.infDist x E := by nlinarith [mul_le_mul_of_nonneg_left hh.le hc.le]
  simp only [f,rootClip,min_eq_left hraw,max_eq_right zero_le_one]

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_test_cutoff_in_open {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {E U : Set X} (hE : IsCompact E) (hU : IsOpen U) (hEU : E ⊆ U) :
    ∃ χ : X → ℝ,IsTestFunction m χ ∧ HasCompactSupport χ ∧
      (∀ x,0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ U ∧
      (∃ V : Set X,IsOpen V ∧ E ⊆ V ∧ ∀ x ∈ V,χ x = 1) ∧
      ∃ B : ℝ,∀ᵐ x ∂m,|laplacian m χ x| ≤ B := by
  obtain ⟨f,hf,hfc,hfb,hfU,V,hV,hEV,hfV⟩ := exists_compact_lipschitz_plateau hE hU hEU
  obtain ⟨χ,hχ,hχc,hχb,hχf,hχ1,B,hB⟩ := hrcd.exists_test_cutoff_of_compact_lipschitz hN hfull hfin o hf.choose_spec hfc
  exact ⟨χ,hχ,hχc,hχb,hχf.trans hfU,⟨V,hV,hEV,fun x hx => hχ1 x (hfV x hx)⟩,B,hB⟩
end WeakHessian

end
end InlinedFile168

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactCoreAnnihilator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile169
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_caccioppoli {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {η : X → ℝ} {L : ℝ≥0} (hη : LipschitzWith L η) (hηc : HasCompactSupport η)
    (hη1 : ∀ x,|η x| ≤ 1) :
    ‖boundedMulLp hη.continuous.aestronglyMeasurable (ae_of_all m hη1) f‖^2 ≤ (L:ℝ)^2*‖f‖^2 := by
  obtain ⟨χ,hχ,hχc,hχ1,-,⟨V,-,hηV,hV⟩,D,hD⟩ :=
    hrcd.exists_test_cutoff_in_open hN hfull hfin o hηc isOpen_univ (subset_univ _)
  have hc : ∀ x,η x ≠ 0 → χ x=1 := fun x hx => hV x (hηV (subset_tsupport η hx))
  let w := fun x => f x*χ x
  have hw : Sobolev m w := hrcd.compact_core_localized_sobolev hN hfull hfin o f hof hχ hχc hD
  have H := hrcd.compact_core_weak_equation hN hfull hfin o f hof hχ hχc hD hη hη1 hc
  have HG := integral_gamma_caccioppoli_lower hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) hw hη hη1
  have hE : (∫ x,(w x*η x)^2 ∂m) ≤ (L:ℝ)^2*(∫ x,w x^2 ∂m) := by
    linarith only [H,HG]
  have hwf : (∫ x,w x^2 ∂m) ≤ ∫ x,(f x)^2 ∂m := by
    apply integral_mono_ae hw.1.integrable_sq (Lp.memLp f).integrable_sq
    exact ae_of_all _ fun x => by
      have hb : (χ x)^2 ≤ 1 := by nlinarith only [(hχ1 x).1,(hχ1 x).2]
      have HH := mul_le_mul_of_nonneg_left hb (sq_nonneg (f x))
      simpa only [w,mul_pow,mul_one] using HH
  let P := boundedMulLp hη.continuous.aestronglyMeasurable (ae_of_all m hη1)
  have hnorm : ‖P f‖^2 = ∫ x,(w x*η x)^2 ∂m := by
    have hn := norm_toLp_sq_eq_integral (Lp.memLp (P f))
    rw [Lp.toLp_coeFn] at hn
    apply hn.trans
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae _ (ae_of_all m hη1) f] with x hx
    change (P f) x = f x*η x at hx
    rw [hx]
    dsimp [w]
    by_cases he : η x=0
    · rw [he]; ring
    · rw [hc x he]; ring
  have hf : ‖f‖^2 = ∫ x,(f x)^2 ∂m := by
    simpa only [Lp.toLp_coeFn] using norm_toLp_sq_eq_integral (Lp.memLp f)
  rw [hnorm,hf]
  exact hE.trans (mul_le_mul_of_nonneg_left hwf (sq_nonneg _))

lemma RCD.compact_core_annihilator_zero {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0) : f = 0 := by
  have hb (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let P (n : ℕ) := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all m (hb n))
  have hT : Tendsto (fun n => P n f) atTop (𝓝 f) :=
    boundedMulLp_tendsto (fun n => (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
      (fun n => ae_of_all m (hb n)) (ae_of_all m (radialCutoff_tendsto o)) f
  have he (n : ℕ) : ‖P n f‖^2 ≤ (1/((n:ℝ)+1))^2*‖f‖^2 := by
    simpa only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,one_div] using
      hrcd.compact_core_caccioppoli hN hfull hfin o f hof (radialCutoff_lipschitz o n) (radialCutoff_compact o n) (hb n)
  have hl : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))^2*‖f‖^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.mul_const (‖f‖^2)
  have hh : ‖f‖^2 ≤ 0 := le_of_tendsto_of_tendsto (hT.norm.pow 2) hl (Eventually.of_forall he)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _)))
end WeakHessian

end
end InlinedFile169

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CompactGeneratorRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile171
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

variable [SigmaFinite m]
lemma RCD.compactGeneratorRange_dense {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    (compactGeneratorRange hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply hrcd.compact_core_annihilator_zero hN hfull hfin o f
  intro g hg hgc u A hgu hgA
  have hm : u-A ∈ compactGeneratorRange hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) :=
    ⟨g,hg,hgc,u,A,hgu,(laplacian_isLaplacian hg.1).congr_ae EventuallyEq.rfl hgA,rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hm hf

end WeakHessian

end
end InlinedFile171

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactOriginalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile172
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.original_compact_test_graph_approx {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A) :
    ∃ gs : ℕ → X → ℝ,(∀ n,IsTestFunction m (gs n)) ∧ (∀ n,HasCompactSupport (gs n)) ∧
      ∃ us As : ℕ → Lp ℝ 2 m,(∀ n,gs n =ᵐ[m] us n) ∧
      (∀ n,laplacian m (gs n) =ᵐ[m] As n) ∧
      Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let M := compactGeneratorRange hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
  have hcl : u-A ∈ closure (M : Set (Lp ℝ 2 m)) := by
    change u-A ∈ M.topologicalClosure
    rw [hrcd.compactGeneratorRange_dense hN hfull hfin o]
    trivial
  obtain ⟨ys,hys,hyt⟩ := mem_closure_iff_seq_limit.mp hcl
  choose gs hgs hgsc us As hge hgA he using hys
  have hgen := hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A hu
  have heu : Q.resolvent (u-A) = u := (Q.isFormGenerator_iff u A).mp hgen
  have heuN (n : ℕ) : Q.resolvent (ys n) = us n := by
    rw [he n]
    exact (Q.isFormGenerator_iff (us n) (As n)).mp
      (hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 (us n) (As n)
        ((hgA n).congr_ae (hge n) EventuallyEq.rfl))
  have hT : Tendsto us atTop (𝓝 u) := by
    have H := Q.resolventLinear.continuous.tendsto (u-A) |>.comp hyt
    change Tendsto (fun n => Q.resolvent (ys n)) atTop (𝓝 (Q.resolvent (u-A))) at H
    simpa only [heu,heuN] using H
  refine ⟨gs,hgs,hgsc,us,As,hge,fun n => (hgA n).ae_laplacian hfin,hT,?_⟩
  have hA (n : ℕ) : As n = us n-ys n := by rw [he n]; abel
  simpa only [← hA,sub_sub_cancel] using hT.sub hyt
end WeakHessian

end
end InlinedFile172

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GraphReuse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile173
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsLaplacian.gradient_energy {u A : X → ℝ} (hu : IsLaplacian m u A) :
    ‖hu.1.2.2.toLp (weakGradient m u)‖^2 = -(∫ x, A x*u x ∂m) := by
  rw [norm_toLp_sq_eq_integral,← integral_congr_ae (gamma_self u)]
  exact hu.2.2 u hu.1

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsLaplacian.gradient_norm_sq_le {u A : X → ℝ} (hu : IsLaplacian m u A) :
    ‖hu.1.2.2.toLp (weakGradient m u)‖^2 ≤ ‖hu.1.1.toLp u‖*‖hu.2.1.toLp A‖ := by
  have hinner : (∫ x, A x*u x ∂m) = ⟪hu.1.1.toLp u,hu.2.1.toLp A⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.1.1.coeFn_toLp,hu.2.1.coeFn_toLp] with x hx hy
    simp only [hx,hy]
    rfl
  rw [hu.gradient_energy,hinner]
  exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_gradient_difference (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => ‖((hn n).sub hfinite hpar hu).1.2.2.toLp
      (weakGradient m (fun x => un n x-u x))‖) atTop (𝓝 0) := by
  have hU : Tendsto (fun n => ‖(hn n).1.1.toLp (un n)-hu.1.1.toLp u‖) atTop (𝓝 0) := by
    simpa using (ht.sub_const (hu.1.1.toLp u)).norm
  have hA : Tendsto (fun n => ‖(hn n).2.1.toLp (An n)-hu.2.1.toLp A‖) atTop (𝓝 0) := by
    simpa using (hAt.sub_const (hu.2.1.toLp A)).norm
  have hb (n : ℕ) := ((hn n).sub hfinite hpar hu).gradient_norm_sq_le
  have hb' (n : ℕ) : ‖((hn n).sub hfinite hpar hu).1.2.2.toLp
      (weakGradient m (fun x => un n x-u x))‖^2 ≤
        ‖(hn n).1.1.toLp (un n)-hu.1.1.toLp u‖ *
        ‖(hn n).2.1.toLp (An n)-hu.2.1.toLp A‖ := by
    have eu : ((hn n).sub hfinite hpar hu).1.1.toLp (fun x => un n x-u x) =
        (hn n).1.1.toLp (un n)-hu.1.1.toLp u := by
      simpa only [Pi.sub_def] using (hn n).1.1.toLp_sub hu.1.1
    have ea : ((hn n).sub hfinite hpar hu).2.1.toLp (fun x => An n x-A x) =
        (hn n).2.1.toLp (An n)-hu.2.1.toLp A := by
      simpa only [Pi.sub_def] using (hn n).2.1.toLp_sub hu.2.1
    simpa only [eu,ea] using hb n
  have hs := squeeze_zero (fun n => sq_nonneg _) hb' (by simpa using hU.mul hA)
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using H

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_weakGradient (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => (hn n).1.2.2.toLp (weakGradient m (un n))) atTop
      (𝓝 (hu.1.2.2.toLp (weakGradient m u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (graph_tendsto_gradient_difference hfinite hpar hn hu ht hAt)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub ((hn n).1.2.2.toLp (weakGradient m (un n)))
      (hu.1.2.2.toLp (weakGradient m u)), (hn n).1.2.2.coeFn_toLp,
    hu.1.2.2.coeFn_toLp,((hn n).sub hfinite hpar hu).1.2.2.coeFn_toLp,
    weakGradient_dist_le hfinite (hn n).1.2.1 hu.1.2.1,
    weakGradient_nonneg (m := m) (fun x => un n x-u x)] with x hs hn' hu' hd hab hp
  rw [hs,Pi.sub_apply,hn',hu',hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
  exact hab

section
omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma tendsto_toLp_mul_bounded {fn : ℕ → X → ℝ} {f b : X → ℝ}
    (hn : ∀ n, MemLp (fn n) 2 m) (hf : MemLp f 2 m)
    (hb : AEStronglyMeasurable b m) {B : ℝ} (hB : ∀ᵐ x ∂m, |b x| ≤ B)
    (ht : Tendsto (fun n => (hn n).toLp (fn n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => (memLp_mul_bounded (hn n) hb hB).toLp (fun x => fn n x*b x))
      atTop (𝓝 ((memLp_mul_bounded hf hb hB).toLp (fun x => f x*b x))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hzero : Tendsto (fun n => |B| * ‖(hn n).toLp (fn n)-hf.toLp f‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((ht.sub_const (hf.toLp f)).norm))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hzero
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((memLp_mul_bounded (hn n) hb hB).toLp _) ((memLp_mul_bounded hf hb hB).toLp _),
    (memLp_mul_bounded (hn n) hb hB).coeFn_toLp,(memLp_mul_bounded hf hb hB).coeFn_toLp,
    Lp.coeFn_sub ((hn n).toLp _) (hf.toLp _),(hn n).coeFn_toLp,hf.coeFn_toLp,hB]
    with x hs hfn hf' hd hn' hff hx
  rw [hs,Pi.sub_apply,hfn,hf',hd,Pi.sub_apply,hn',hff,← sub_mul]
  simp only [Real.norm_eq_abs,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)).trans_eq
    (mul_comm _ _)

lemma integral_mul_eq_inner {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x, f x*g x ∂m) = ⟪hg.toLp g,hf.toLp f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp only [hx,hy]
  rfl

lemma tendsto_integral_mul_L2 {fn gn : ℕ → X → ℝ} {f g : X → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 m) (hf : MemLp f 2 m)
    (hgn : ∀ n, MemLp (gn n) 2 m) (hg : MemLp g 2 m)
    (htf : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)))
    (htg : Tendsto (fun n => (hgn n).toLp (gn n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => ∫ x, fn n x*gn n x ∂m) atTop (𝓝 (∫ x, f x*g x ∂m)) := by
  simpa only [integral_mul_eq_inner (hfn _) (hgn _),integral_mul_eq_inner hf hg] using
    htg.inner htf

end

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_gamma (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A ξ : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => (memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).toLp (gamma m ξ (un n)))
      atTop (𝓝 ((memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).toLp (gamma m ξ u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht0 := graph_tendsto_gradient_difference hfinite hpar hn hu ht hAt
  have htB : Tendsto (fun n => (L:ℝ)*‖((hn n).sub hfinite hpar hu).1.2.2.toLp
      (weakGradient m (fun x => un n x-u x))‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht0
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) htB
  have he : (memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).toLp (gamma m ξ (un n)) -
      (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).toLp (gamma m ξ u) =
      (memLp_gamma_of_lipschitz hfinite hpar hξ ((hn n).sub hfinite hpar hu).1).toLp
        (gamma m ξ (fun x => un n x-u x)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub ((memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).toLp _)
        ((memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).toLp _),
      (memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1).coeFn_toLp,
      (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).coeFn_toLp,
      (memLp_gamma_of_lipschitz hfinite hpar hξ ((hn n).sub hfinite hpar hu).1).coeFn_toLp,
      gamma_comm (m := m) ξ (fun x => un n x-u x),
      gamma_sub_left hfinite hpar (hn n).1.2.1 hu.1.2.1 (localSobolev_of_lipschitz hfinite hξ),
      gamma_comm (m := m) ξ (un n),gamma_comm (m := m) ξ u] with x hs h1 h2 h3 hc hd hc1 hc2
    rw [hs,Pi.sub_apply,h1,h2,h3,hc,hd,← hc1,← hc2]
  rw [he]
  exact norm_gamma_toLp_le hfinite hpar hξ ((hn n).sub hfinite hpar hu).1

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_tendsto (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A ξ B : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ)
    {C D : ℝ} (hC : ∀ x, |ξ x| ≤ C) (hB : AEStronglyMeasurable B m)
    (hD : ∀ᵐ x ∂m, |B x| ≤ D)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => graphBochner m (un n) (An n) ξ B) atTop
      (𝓝 (graphBochner m u A ξ B)) := by
  have hDt := graph_tendsto_weakGradient hfinite hpar hn hu ht hAt
  have hξM := hξ.continuous.aestronglyMeasurable (μ := m)
  have hξB : ∀ᵐ x ∂m, |ξ x| ≤ C := ae_of_all _ hC
  have h1 := tendsto_integral_mul_L2 (fun n => memLp_mul_bounded (hn n).1.2.2 hB hD)
    (memLp_mul_bounded hu.1.2.2 hB hD) (fun n => (hn n).1.2.2) hu.1.2.2
    (tendsto_toLp_mul_bounded _ _ hB hD hDt) hDt
  have h1' : Tendsto (fun n => ∫ x, B x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x, B x*gamma m u u x ∂m)) := by
    have he (v : X → ℝ) : (∫ x, B x*gamma m v v x ∂m) =
        ∫ x, (weakGradient m v x*B x)*weakGradient m v x ∂m := by
      apply integral_congr_ae
      filter_upwards [gamma_self (m := m) v] with x hx
      rw [hx]; ring
    simpa only [he] using h1
  have h2 := tendsto_integral_mul_L2 (fun n => (hn n).2.1) hu.2.1
    (fun n => memLp_gamma_of_lipschitz hfinite hpar hξ (hn n).1)
    (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1) hAt
    (graph_tendsto_gamma hfinite hpar hn hu hξ ht hAt)
  have h3 := tendsto_integral_mul_L2 (fun n => memLp_mul_bounded (hn n).2.1 hξM hξB)
    (memLp_mul_bounded hu.2.1 hξM hξB) (fun n => (hn n).2.1) hu.2.1
    (tendsto_toLp_mul_bounded _ _ hξM hξB hAt) hAt
  have h3' : Tendsto (fun n => ∫ x, ξ x*(An n x)^2 ∂m) atTop
      (𝓝 (∫ x, ξ x*(A x)^2 ∂m)) := by
    have he (v : X → ℝ) : (∫ x, ξ x*(v x)^2 ∂m) = ∫ x, (v x*ξ x)*v x ∂m := by
      congr 1
      funext x
      ring
    simpa only [he] using h3
  exact (h1'.const_mul (1/2) |>.add h2).add h3'

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_weighted_gamma (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A b : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    (hb : AEStronglyMeasurable b m) {B : ℝ} (hB : ∀ᵐ x ∂m, |b x| ≤ B)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => ∫ x, b x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x, b x*gamma m u u x ∂m)) := by
  have hD := graph_tendsto_weakGradient hfinite hpar hn hu ht hAt
  have H := tendsto_integral_mul_L2 (fun n => memLp_mul_bounded (hn n).1.2.2 hb hB)
    (memLp_mul_bounded hu.1.2.2 hb hB) (fun n => (hn n).1.2.2) hu.1.2.2
    (tendsto_toLp_mul_bounded _ _ hb hB hD) hD
  have he (v : X → ℝ) : (∫ x, b x*gamma m v v x ∂m) =
      ∫ x, (weakGradient m v x*b x)*weakGradient m v x ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) v] with x hx
    rw [hx]; ring
  simpa only [he] using H

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_bound_of_approx (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A ξ B b : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ)
    {C D E : ℝ} (hC : ∀ x, |ξ x| ≤ C) (hB : AEStronglyMeasurable B m)
    (hD : ∀ᵐ x ∂m, |B x| ≤ D) (hb : AEStronglyMeasurable b m)
    (hE : ∀ᵐ x ∂m, |b x| ≤ E)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A)))
    (hcore : ∀ n, (∫ x, b x*gamma m (un n) (un n) x ∂m) ≤
      graphBochner m (un n) (An n) ξ B) :
    (∫ x, b x*gamma m u u x ∂m) ≤ graphBochner m u A ξ B := by
  exact le_of_tendsto_of_tendsto (graph_tendsto_weighted_gamma hfinite hpar hn hu hb hE ht hAt)
    (graphBochner_tendsto hfinite hpar hn hu hξ hC hB hD ht hAt) (Eventually.of_forall hcore)

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_eq_core (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ B q : X → ℝ}
    (hu : IsLaplacian m u A) (hξA : IsLaplacian m ξ B)
    {L : ℝ≥0} (hξ : LipschitzWith L ξ) {C : ℝ} (hC : ∀ x, |ξ x| ≤ C)
    (hq : Sobolev m q) (heq : gamma m u u =ᵐ[m] (fun x => 2*q x)) :
    graphBochner m u A ξ B =
      -(∫ x, gamma m ξ q x ∂m) + ∫ x, (ξ x*A x+gamma m ξ u x)*A x ∂m := by
  have hfirst : (1/2)*(∫ x, B x*gamma m u u x ∂m) = -(∫ x, gamma m ξ q x ∂m) := by
    have he : (∫ x, B x*gamma m u u x ∂m) = 2*(∫ x, B x*q x ∂m) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]; ring
    rw [he,hξA.2.2 q hq]
    ring
  have hprod : MemLp (fun x => A x*ξ x) 2 m :=
    memLp_mul_bounded hu.2.1 hξ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hIA : Integrable (fun x => (ξ x*A x)*A x) m := by
    have htmp : Integrable (fun x => (A x*ξ x)*A x) m := hprod.integrable_mul hu.2.1
    convert htmp using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    ring
  have hIG : Integrable (fun x => gamma m ξ u x*A x) m :=
    (memLp_gamma_of_lipschitz hfinite hpar hξ hu.1).integrable_mul hu.2.1
  unfold graphBochner
  rw [hfirst]
  simp_rw [add_mul]
  rw [integral_add hIA hIG]
  have hE1 : (∫ x, (ξ x*A x)*A x ∂m) = ∫ x, ξ x*(A x)^2 ∂m := by
    congr 1; funext x; ring
  rw [hE1]
  have hE2 : (∫ x, gamma m ξ u x*A x ∂m) = ∫ x, A x*gamma m ξ u x ∂m := by
    congr 1; funext x; ring
  rw [hE2]
  ring

omit [ProperSpace X] [SigmaFinite m] in
lemma graph_tendsto_reweight (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {un An : ℕ → X → ℝ} {u A V : X → ℝ}
    (hn : ∀ n, IsLaplacian m (un n) (An n)) (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (ht : Tendsto (fun n => (hn n).1.1.toLp (un n)) atTop (𝓝 (hu.1.1.toLp u)))
    (hAt : Tendsto (fun n => (hn n).2.1.toLp (An n)) atTop (𝓝 (hu.2.1.toLp A))) :
    Tendsto (fun n => ((hn n).reweight hfinite hpar hV hB).1.1.toLp (un n)) atTop
      (𝓝 ((hu.reweight hfinite hpar hV hB).1.1.toLp u)) ∧
    Tendsto (fun n => ((hn n).reweight hfinite hpar hV hB).2.1.toLp
      (fun x => An n x+gamma m V (un n) x)) atTop
      (𝓝 ((hu.reweight hfinite hpar hV hB).2.1.toLp (fun x => A x+gamma m V u x))) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  refine ⟨tendsto_toLp_changeMeasure ENNReal.ofReal_ne_top hν (fun n => (hn n).1.1) hu.1.1 ht, ?_⟩
  have hg := graph_tendsto_gamma hfinite hpar hn hu hV ht hAt
  have hsum : Tendsto (fun n => ((hn n).2.1.add
      (memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1)).toLp
      (fun x => An n x+gamma m V (un n) x)) atTop
      (𝓝 ((hu.2.1.add (memLp_gamma_of_lipschitz hfinite hpar hV hu.1)).toLp
        (fun x => A x+gamma m V u x))) := by
    have en (n : ℕ) : ((hn n).2.1.add
        (memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1)).toLp
        (fun x => An n x+gamma m V (un n) x) =
        (hn n).2.1.toLp (An n)+(memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1).toLp
          (gamma m V (un n)) := by
      simpa only [Pi.add_def] using (hn n).2.1.toLp_add
        (memLp_gamma_of_lipschitz hfinite hpar hV (hn n).1)
    have e0 : (hu.2.1.add (memLp_gamma_of_lipschitz hfinite hpar hV hu.1)).toLp
        (fun x => A x+gamma m V u x) = hu.2.1.toLp A+
        (memLp_gamma_of_lipschitz hfinite hpar hV hu.1).toLp (gamma m V u) := by
      simpa only [Pi.add_def] using hu.2.1.toLp_add
        (memLp_gamma_of_lipschitz hfinite hpar hV hu.1)
    simp_rw [en,e0]
    exact hAt.add hg
  exact tendsto_toLp_changeMeasure ENNReal.ofReal_ne_top hν _ _ hsum

omit [ProperSpace X] [SigmaFinite m] in
lemma graphBochner_reweight_eq_drift (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {V g ξ B : X → ℝ}
    (hg : IsTestFunction m g) (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {C D : ℝ} (hC : ∀ x, |V x| ≤ C) (hD : ∀ x, |ξ x| ≤ D)
    (hξA : IsLaplacian (exponentialMeasure m V) ξ B) :
    graphBochner (exponentialMeasure m V) g (fun x => laplacian m g x+gamma m V g x) ξ B =
      driftBochner m V g ξ := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hC
  have hnfinite := hfinite.of_le_smul (C := (Real.exp C).toNNReal) hν
  have hnpar := hpar.change_measure (C := (Real.exp C).toNNReal)
    (D := (Real.exp C).toNNReal) hm hν
  have hgA := (laplacian_isLaplacian hg.1).reweight hfinite hpar hV hC
  have hqn := (sobolev_exponentialMeasure_iff hC (fun y => gamma m g g y/2)).mp hq
  have heq : gamma (exponentialMeasure m V) g g =ᵐ[exponentialMeasure m V]
      (fun x => 2*(gamma m g g x/2)) := by
    apply (Measure.absolutelyContinuous_of_le_smul hν).ae_eq
    filter_upwards [gamma_exponentialMeasure (m := m) hC g g] with x hx
    rw [hx]; ring
  rw [graphBochner_eq_core hnfinite hnpar hgA hξA hξ hD hqn heq]
  rw [integral_exponentialMeasure hV.continuous.aemeasurable,
    integral_exponentialMeasure hV.continuous.aemeasurable]
  unfold driftBochner
  congr 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [gamma_exponentialMeasure (m := m) hC ξ (fun y => gamma m g g y/2)] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [gamma_exponentialMeasure (m := m) hC ξ g] with x hx
    rw [hx]
    ring

omit [ProperSpace X] [SigmaFinite m] in
lemma OriginalTestGraphCore.reweight_approx (hcore : OriginalTestGraphCore m)
    (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V u A : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    {C : ℝ} (hC : ∀ x, |V x| ≤ C) (hu : IsLaplacian (exponentialMeasure m V) u A) :
    ∃ (gs : ℕ → X → ℝ) (htest : ∀ n, IsTestFunction m (gs n)),
      (∀ n, HasCompactSupport (gs n)) ∧
      Tendsto (fun n => ((laplacian_isLaplacian (htest n).1).reweight hfinite hpar hV hC).1.1.toLp
        (gs n)) atTop (𝓝 (hu.1.1.toLp u)) ∧
      Tendsto (fun n => ((laplacian_isLaplacian (htest n).1).reweight hfinite hpar hV hC).2.1.toLp
        (fun x => laplacian m (gs n) x+gamma m V (gs n) x)) atTop (𝓝 (hu.2.1.toLp A)) := by
  have hu0 := hu.of_exponentialMeasure hfinite hpar hV hC
  obtain ⟨gs,htest,hsupp,ht,hAt⟩ := hcore u (fun x => A x-gamma m V u x) hu0
  refine ⟨gs,htest,hsupp,?_⟩
  have H := graph_tendsto_reweight hfinite hpar (fun n => laplacian_isLaplacian (htest n).1)
    hu0 hV hC ht hAt
  have he : (fun x => A x-gamma m V u x+gamma m V u x) = A := by funext x; ring
  aesop

end WeakHessian

end
end InlinedFile173

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_RadialGammaLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile175
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma radialCutoff_gamma_toLp_tendsto_zero (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {q : X → ℝ} (hq : Sobolev m q) :
    Tendsto (fun n => (memLp_gamma_of_lipschitz hfin hpar (radialCutoff_lipschitz o n) hq).toLp
      (gamma m (radialCutoff o n) q)) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    simpa only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,one_div] using
      norm_gamma_toLp_le hfin hpar (radialCutoff_lipschitz o n) hq
  · simpa only [one_div,zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖hq.2.2.toLp (weakGradient m q)‖

lemma integral_gamma_radialCutoff_tendsto (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {ξ q b : X → ℝ}
    (hξ : LocalSobolev m ξ) (hq : Sobolev m q)
    (hi : Integrable (fun x => b x*gamma m ξ q x) m)
    (hbξ : MemLp (fun x => b x*ξ x) 2 m) :
    Tendsto (fun n => ∫ x,b x*gamma m (fun y => ξ y*radialCutoff o n y) q x ∂m)
      atTop (𝓝 (∫ x,b x*gamma m ξ q x ∂m)) := by
  have hcB (n : ℕ) : ∀ᵐ x ∂m, |radialCutoff o n x| ≤ 1 := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hDcB (n : ℕ) : ∀ᵐ x ∂m, |weakGradient m (radialCutoff o n) x| ≤ ((n:ℝ)+1)⁻¹ := by
    filter_upwards [weakGradient_nonneg (m := m) (radialCutoff o n),
      weakGradient_le_lipschitz hfin (radialCutoff_lipschitz o n)] with x hn hb
    rwa [abs_of_nonneg hn]
  have hγ (n : ℕ) := memLp_gamma_of_lipschitz hfin hpar (radialCutoff_lipschitz o n) hq
  have he (n : ℕ) : (∫ x,b x*gamma m (fun y => ξ y*radialCutoff o n y) q x ∂m) =
      (∫ x,(b x*ξ x)*gamma m (radialCutoff o n) q x ∂m)+
      (∫ x,(b x*gamma m ξ q x)*radialCutoff o n x ∂m) := by
    have hi0 : Integrable (fun x => (b x*ξ x)*gamma m (radialCutoff o n) q x) m :=
      hbξ.integrable_mul (hγ n)
    rw [← integral_add hi0
      (hi.mul_bdd (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
        (by simpa only [Real.norm_eq_abs] using hcB n))]
    apply integral_congr_ae
    filter_upwards [gamma_mul_left hfin hpar hξ
      (localSobolev_of_lipschitz hfin (radialCutoff_lipschitz o n)) hq.2.1 (hcB n) (hDcB n)] with x hx
    rw [hx]; ring
  have ht : Tendsto (fun n => ∫ x,(b x*ξ x)*gamma m (radialCutoff o n) q x ∂m) atTop (𝓝 0) := by
    simpa only [integral_mul_eq_inner hbξ (hγ _),inner_zero_left] using
      (radialCutoff_gamma_toLp_tendsto_zero hfin hpar o hq).inner
        (tendsto_const_nhds (x := hbξ.toLp _))
  simpa only [he,zero_add] using ht.add (integral_radialCutoff_tendsto o hi)
end WeakHessian

end
end InlinedFile175

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_DriftRadialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile176
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma driftBochner_split (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V g ξ : X → ℝ} (hg : IsTestFunction m g)
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x,|V x| ≤ B) (hC : ∀ x,|ξ x| ≤ C) :
    driftBochner m V g ξ =
      -(∫ x,Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x ∂m)+
      (∫ x,Real.exp (V x)*ξ x*(laplacian m g x+gamma m V g x)^2 ∂m)+
      (∫ x,(Real.exp (V x)*(laplacian m g x+gamma m V g x))*gamma m ξ g x ∂m) := by
  have hgs := (laplacian_isLaplacian hg.1).1
  have hA := (laplacian_isLaplacian hg.1).2.1.add (memLp_gamma_of_lipschitz hfin hpar hV hgs)
  have hw := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hwb : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hi : Integrable (fun x => Real.exp (V x)*ξ x*(laplacian m g x+gamma m V g x)^2) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_sq.bdd_mul hξ.continuous.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using ae_of_all m hC)).bdd_mul hw hwb
  have hj : Integrable (fun x => (Real.exp (V x)*(laplacian m g x+gamma m V g x))*gamma m ξ g x) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_mul (memLp_gamma_of_lipschitz hfin hpar hξ hgs)).bdd_mul hw hwb
  unfold driftBochner
  rw [add_assoc,← integral_add hi hj]
  congr 1
  congr 1
  funext x
  ring

omit [ProperSpace X] [SigmaFinite m] in
lemma driftBochner_radialCutoff_tendsto (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {V g ξ : X → ℝ}
    (hg : IsTestFunction m g) (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x,|V x| ≤ B) (hC : ∀ x,|ξ x| ≤ C) (hξS : Sobolev m ξ) :
    Tendsto (fun n => driftBochner m V g (fun x => ξ x*radialCutoff o n x)) atTop
      (𝓝 (driftBochner m V g ξ)) := by
  have hgs := (laplacian_isLaplacian hg.1).1
  let A := fun x => laplacian m g x+gamma m V g x
  have hA : MemLp A 2 m := (laplacian_isLaplacian hg.1).2.1.add (memLp_gamma_of_lipschitz hfin hpar hV hgs)
  have hw := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hwb : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B := ae_of_all _ fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hwb' : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := by simpa only [Real.norm_eq_abs] using hwb
  have hi1 : Integrable (fun x => Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x) m :=
    (integrable_gamma hfin hξS hq).bdd_mul hw hwb'
  have hm1 : MemLp (fun x => Real.exp (V x)*ξ x) 2 m := by
    simpa only [mul_comm,Function.comp_apply] using memLp_mul_bounded hξS.1 hw hwb
  have ht1 := integral_gamma_radialCutoff_tendsto hfin hpar o hξS.2.1 hq hi1 hm1
  have hi2 : Integrable (fun x => Real.exp (V x)*ξ x*A x^2) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_sq.bdd_mul hξ.continuous.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using ae_of_all m hC)).bdd_mul hw hwb'
  have ht2 := integral_radialCutoff_tendsto o hi2
  have hi3 : Integrable (fun x => (Real.exp (V x)*A x)*gamma m ξ g x) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_mul (memLp_gamma_of_lipschitz hfin hpar hξ hgs)).bdd_mul hw hwb'
  have hm3 : MemLp (fun x => (Real.exp (V x)*A x)*ξ x) 2 m := by
    have H := memLp_mul_bounded (memLp_mul_bounded hA hξ.continuous.aestronglyMeasurable (ae_of_all m hC)) hw hwb
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext x; simp only [Function.comp_apply]; ring
  have ht3 := integral_gamma_radialCutoff_tendsto hfin hpar o hξS.2.1 hgs hi3 hm3
  have hcB (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hcutL (n : ℕ) := lipschitz_mul_bounded hξ (radialCutoff_lipschitz o n) hC (hcB n)
  have hcutB (n : ℕ) (x : X) : |ξ x*radialCutoff o n x| ≤ |C| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hcB n x) (abs_nonneg _)).trans (by simpa using (hC x).trans (le_abs_self C))
  have he (n : ℕ) : (∫ x,Real.exp (V x)*(ξ x*radialCutoff o n x)*A x^2 ∂m) =
      ∫ x,(Real.exp (V x)*ξ x*A x^2)*radialCutoff o n x ∂m := by
    congr 1; funext x; ring
  have ht2' : Tendsto (fun n => ∫ x,Real.exp (V x)*(ξ x*radialCutoff o n x)*A x^2 ∂m) atTop
      (𝓝 (∫ x,Real.exp (V x)*ξ x*A x^2 ∂m)) := by
    simpa only [he] using ht2
  simpa only [driftBochner_split hfin hpar hg hV (hcutL _) hB (hcutB _),
    driftBochner_split hfin hpar hg hV hξ hB hC,A] using (ht1.neg.add ht2').add ht3
end WeakHessian

end
end InlinedFile176

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GlobalMultiplierCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile177
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_global_multiplier_core {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G g ξ : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x,|F x| ≤ B) (hC : ∀ x,|ξ x| ≤ C)
    (hG : ∀ x,|G x| ≤ D) (hGc : Continuous G)
    (hξS : Sobolev m ξ) (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hq := hrcd.test_gammaHalf_sobolev hN hfull hfin o hg
  have hgs := (laplacian_isLaplacian hg.1).1
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|a*F x| ≤ |a| *B := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg a)
  have hw := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hwB : ∀ᵐ x ∂m, ‖Real.exp (a*F x)‖ ≤ Real.exp (|a| *B) := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hVB x))
  have hk : Continuous (fun x => K-a*G x) := continuous_const.sub (continuous_const.mul hGc)
  have hkB : ∀ᵐ x ∂m, ‖K-a*G x‖ ≤ |K| + |a| *|D| := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    calc
      |K-a*G x| ≤ |K|+|a*G x| := abs_sub _ _
      _ = |K|+|a| *|G x| := by rw [abs_mul]
      _ ≤ |K|+|a| *|D| := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left ((hG x).trans (le_abs_self _)) (abs_nonneg a))
  have hi : Integrable (fun x => Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.mul_apply] using (((integrable_gamma hfin hgs hgs).bdd_mul
      hk.aestronglyMeasurable hkB).bdd_mul hξ.continuous.aestronglyMeasurable
        (by simpa only [Real.norm_eq_abs] using ae_of_all m hC)).bdd_mul hw hwB
  have hcB (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hcutL (n : ℕ) := lipschitz_mul_bounded hξ (radialCutoff_lipschitz o n) hC (hcB n)
  have hcutB (n : ℕ) (x : X) : |ξ x*radialCutoff o n x| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hcB n x) (abs_nonneg _)).trans (by simpa using hC x)
  have he (n : ℕ) : (∫ x,Real.exp (a*F x)*(ξ x*radialCutoff o n x)*(K-a*G x)*gamma m g g x ∂m) =
      ∫ x,(Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x)*radialCutoff o n x ∂m := by
    congr 1; funext x; ring
  have hbound (n : ℕ) : (∫ x,(Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x)*radialCutoff o n x ∂m) ≤
      driftBochner m (fun x => a*F x) g (fun x => ξ x*radialCutoff o n x) := by
    rw [← he]
    exact hHess.rcd_core_integrated hN hrcd hfull hfin o hg hgc hF (hcutL n)
      hB (hcutB n) hG hGc ((radialCutoff_compact o n).mul_left)
      (fun x => mul_nonneg (hξ0 x) (radialCutoff_nonneg o n x)) ha
  exact le_of_tendsto_of_tendsto (integral_radialCutoff_tendsto o hi)
    (driftBochner_radialCutoff_tendsto hfin hpar o hg hq hV hξ hVB hC hξS)
    (Eventually.of_forall hbound)
end WeakHessian

end
end InlinedFile177

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_OriginalCoreProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile178
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.originalTestGraphCore {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) : OriginalTestGraphCore m := by
  intro u A hu
  obtain ⟨gs,hgs,hgsc,us,As,hge,hAe,hut,hAt⟩ :=
    hrcd.original_compact_test_graph_approx hN hfull hfin o
      (hu.congr_ae hu.1.1.coeFn_toLp.symm hu.2.1.coeFn_toLp.symm)
  have eu (n : ℕ) : (laplacian_isLaplacian (hgs n).1).1.1.toLp (gs n) = us n := by
    apply Lp.ext
    exact (laplacian_isLaplacian (hgs n).1).1.1.coeFn_toLp.trans (hge n)
  have eA (n : ℕ) : (laplacian_isLaplacian (hgs n).1).2.1.toLp (laplacian m (gs n)) = As n := by
    apply Lp.ext
    exact (laplacian_isLaplacian (hgs n).1).2.1.coeFn_toLp.trans (hAe n)
  exact ⟨gs,hgs,hgsc,by simpa only [eu] using hut,by simpa only [eA] using hAt⟩
end WeakHessian

end
end InlinedFile178

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedGraphInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile179
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_graph_inequality_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G u A ξ B : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {CF Cξ CG CB : ℝ} (hFbounded : ∀ x,|F x| ≤ CF) (hξbounded : ∀ x,|ξ x| ≤ Cξ)
    (hGbounded : ∀ x,|G x| ≤ CG) (hGc : Continuous G)
    (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a)
    (hu : IsLaplacian (exponentialMeasure m (fun x => a*F x)) u A)
    (hξA : IsLaplacian (exponentialMeasure m (fun x => a*F x)) ξ B)
    (hBbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|B x| ≤ CB) :
    (∫ x,(ξ x*(K-a*G x))*gamma (exponentialMeasure m (fun x => a*F x)) u u x
      ∂exponentialMeasure m (fun x => a*F x)) ≤
      graphBochner (exponentialMeasure m (fun x => a*F x)) u A ξ B := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFbounded x) (abs_nonneg a)
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hν
  have hnpar := hpar.change_measure (C := (Real.exp (|a| *CF)).toNNReal)
    (D := (Real.exp (|a| *CF)).toNNReal) hm hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hξS : Sobolev m ξ := (sobolev_exponentialMeasure_iff hVB ξ).mpr hξA.1
  obtain ⟨gs,hgs,hgc,hut,hAt⟩ := (hrcd.originalTestGraphCore hN hfull hfin o).reweight_approx
    hfin hpar hV hVB hu
  have hk : Continuous (fun x => ξ x*(K-a*G x)) :=
    hξ.continuous.mul (continuous_const.sub (continuous_const.mul hGc))
  have hkBound : ∀ᵐ x ∂ν,|ξ x*(K-a*G x)| ≤ |Cξ| *(|K| + |a| *|CG|) := ae_of_all _ fun x => by
    have ht : |K-a*G x| ≤ |K| + |a| *|CG| := by
      calc
        |K-a*G x| ≤ |K|+|a*G x| := abs_sub _ _
        _ = |K|+|a| *|G x| := by rw [abs_mul]
        _ ≤ |K|+|a| *|CG| := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left ((hGbounded x).trans (le_abs_self _)) (abs_nonneg a))
    rw [abs_mul]
    exact mul_le_mul ((hξbounded x).trans (le_abs_self _)) ht (abs_nonneg _) (abs_nonneg _)
  apply graphBochner_bound_of_approx hnfin hnpar
    (fun n => (laplacian_isLaplacian (hgs n).1).reweight hfin hpar hV hVB) hu
    hξ hξbounded hξA.2.1.aestronglyMeasurable hBbounded hk.aestronglyMeasurable hkBound hut hAt
  intro n
  rw [graphBochner_reweight_eq_drift hfin hpar (hgs n)
    (hrcd.test_gammaHalf_sobolev hN hfull hfin o (hgs n)) hV hξ hVB hξbounded hξA]
  have he : (∫ x,(ξ x*(K-a*G x))*gamma ν (gs n) (gs n) x ∂ν) =
      ∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m (gs n) (gs n) x ∂m := by
    rw [integral_exponentialMeasure hV.continuous.aemeasurable]
    apply integral_congr_ae
    filter_upwards [gamma_exponentialMeasure (m := m) hVB (gs n) (gs n)] with x hx
    change gamma m (gs n) (gs n) x = gamma ν (gs n) (gs n) x at hx
    rw [← hx]; ring
  rw [he]
  exact hHess.rcd_global_multiplier_core hN hrcd hfull hfin o (hgs n) (hgc n) hF hξ
    hFbounded hξbounded hGbounded hGc hξS hξ0 ha
end WeakHessian

end
end InlinedFile179

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality_oai.{u_1} := @OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality_oai.{u_1}
