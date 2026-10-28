-- Prove2me | solution 1 for OAI.WeakHessian.RCD.compact_core_weak_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:10:43.033381+00:00
-- url     : https://prove2.me/submissions/98ee3b46-e263-4e89-b477-5dd077d76fd3

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_reversePoincare_pointwise
import Theorems.Thm_OAI_WeakHessian_RCD_compact_core_localized_sobolev
import Theorems.Thm_OAI_WeakHessian_RCD_compact_core_product_identity

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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_FormGenerator
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

namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.formGenerator_add {u v A B : E}
    (hu : hQ.IsFormGenerator u A) (hv : hQ.IsFormGenerator v B) :
    hQ.IsFormGenerator (u+v) (A+B) := by
  rw [hQ.isFormGenerator_iff]
  have he : u+v-(A+B) = (u-A)+(v-B) := by abel
  rw [he, hQ.resolvent_add, (hQ.isFormGenerator_iff _ _).mp hu,
    (hQ.isFormGenerator_iff _ _).mp hv]

lemma ClosedQuadraticEnergy.formGenerator_sub {u v A B : E}
    (hu : hQ.IsFormGenerator u A) (hv : hQ.IsFormGenerator v B) :
    hQ.IsFormGenerator (u-v) (A-B) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    hQ.formGenerator_add hu (hQ.formGenerator_smul (-1) hv)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.formGenerator_energy {u A : E}
    (hu : hQ.IsFormGenerator u A) : 2*(Q u).toReal = -⟪A,u⟫_ℝ := by
  rcases hu with ⟨hfin,hgen⟩
  simpa only [hQ.form_self, ClosedQuadraticEnergy.realEnergy] using hgen ⟨u,hfin⟩

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

local instance instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions_3_r30871c_1 : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
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

end WeakHessianFunctional

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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_FormGeneratorSymmetric
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
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
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

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheeger_scaled_resolvent_bounded (h : QuadraticCheegerEnergy m)
    {t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) :
    ∀ᵐ x ∂m, |((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x| ≤ B := by
  let η : ℝ → ℝ := fun r => max (-B) (min r B)
  have hη : LipschitzWith 1 η := (LipschitzWith.id.min_const B).const_max (-B)
  have hη0 : η 0 = 0 := by simp only [η, min_eq_left hB, max_eq_right (neg_nonpos.mpr hB)]
  have hfixu : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u, hu] with x hx hu
    simpa only [Function.comp_apply, η, min_eq_left (abs_le.mp hu).2,
      max_eq_right (abs_le.mp hu).1] using hx
  have hQη (f : Lp ℝ 2 m) :
      cheegerEnergy m (hη.compLp hη0 f : X → ℝ) ≤ cheegerEnergy m (f : X → ℝ) := by
    rw [cheegerEnergy_congr_ae (hη.coeFn_compLp hη0 f)]
    exact cheegerEnergy_normalContraction hη hη0 f
  have hfix := ((cheeger_closedQuadraticEnergy h).scale ht).resolvent_normal_fixed m hη hη0
    (fun f => by gcongr; exact hQη f) u hfixu
  filter_upwards [hη.coeFn_compLp hη0 (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u)] with x hx
  rw [hfix] at hx
  change ((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x =
    max (-B) (min (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x) B) at hx
  rw [hx]
  exact abs_le.mpr ⟨le_max_left _ _,max_le (by linarith) (min_le_right _ _)⟩

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_FormLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile13
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.form_cauchySchwarz (u v : hQ.domain) :
    (hQ.form u v)^2 ≤ hQ.realEnergy u*hQ.realEnergy v :=
  hQ.realEnergy_quadratic.polar_cauchySchwarz u v

lemma ClosedQuadraticEnergy.scaled_resolvent_energy_le {t : ℝ} (ht : 0 < t) (u : E) :
    Q ((hQ.scale ht).resolvent u) ≤ Q u := by
  have H := (hQ.scale ht).resolvent_energy_le u
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top).mp H

lemma ClosedQuadraticEnergy.scaled_resolvent_energy_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    {ts : ι → ℝ} (hts : ∀ i, 0 < ts i) (hl : Tendsto ts l (𝓝 0)) (v : hQ.domain) :
    Tendsto (fun i => (Q ((hQ.scale (hts i)).resolvent v)).toReal) l (𝓝 (hQ.realEnergy v)) := by
  have hv := hQ.scaled_resolvent_tendsto hd hts hl (v:E)
  have H : Tendsto (fun i => Q ((hQ.scale (hts i)).resolvent v)) l (𝓝 (Q v)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact hv (hQ.lowerSemicontinuous v a ha)
    · intro b hb
      exact Eventually.of_forall fun i => (hQ.scaled_resolvent_energy_le (hts i) v).trans_lt hb
  exact (ENNReal.continuousAt_toReal v.property.ne).tendsto.comp H

lemma ClosedQuadraticEnergy.scaled_resolvent_form_error_le (v : hQ.domain) {t : ℝ} (ht : 0 < t) :
    (Q ((v:E)-(hQ.scale ht).resolvent v)).toReal ≤
      hQ.realEnergy v-(Q ((hQ.scale ht).resolvent v)).toReal := by
  let r : E := (hQ.scale ht).resolvent v
  let A : E := t⁻¹ • (r-v)
  have hg : hQ.IsFormGenerator r A := (hQ.scaled_resolvent_iff ht v r).mp rfl
  let u : hQ.domain := ⟨r,hg.1⟩
  have he : t • A = r-v := by dsimp [A]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hp := hg.2 (v-u)
  have hi : 0 ≤ -⟪A,(v-u:E)⟫_ℝ := by
    change 0 ≤ -⟪A,(v:E)-r⟫_ℝ
    have H : (v:E)-r = -(t • A) := by rw [he]; abel
    rw [H,inner_neg_right,neg_neg,real_inner_smul_right,real_inner_self_eq_norm_sq]
    positivity
  change 0 ≤ -⟪A,((v-u : hQ.domain):E)⟫_ℝ at hi
  change 2*hQ.form u (v-u) = _ at hp
  have H := hQ.realEnergy_add u (v-u)
  rw [add_sub_cancel] at H
  change (Q ((v:E)-r)).toReal ≤ _
  change hQ.realEnergy (v-u) ≤ hQ.realEnergy v-hQ.realEnergy u
  linarith

end WeakHessianFunctional

end
end InlinedFile13

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_SquareControl
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
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.squareControl {γ : Curve X} (h : IsGeodesic γ) :
    IsSquareControl γ (fun _ => dist (γ timeZero) (γ timeOne)) := by
  refine ⟨measurable_const,memLp_const _,ae_of_all _ (fun _ => dist_nonneg),?_⟩
  intro s t hst
  rw [h s t,intervalIntegral.integral_const,smul_eq_mul,
    abs_sub_comm (s:ℝ),abs_of_nonneg (sub_nonneg.mpr hst)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.ae_metricSpeed_le {γ : Curve X} (h : IsGeodesic γ) :
    ∀ᵐ s ∂volume.restrict (Icc (0:ℝ) 1),
      metricSpeed γ s ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) :=
  h.squareControl.metricSpeed_le

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile1
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsTestPlan.restrict_reference_of_tracks {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ᵐ γ ∂π, ∀ t : Time, γ t ∈ S) : IsTestPlan (m.restrict S) π := by
  refine ⟨hπ.1,?_,hπ.2.2⟩
  obtain ⟨C,hC⟩ := hπ.2.1
  refine ⟨C,fun t => ?_⟩
  have ha : ∀ᵐ x ∂(π.map (fun γ => γ t)), x ∈ S :=
    (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hS).mpr
      (hs.mono fun γ hγ => hγ t)
  rw [← Measure.restrict_eq_self_of_ae_mem ha]
  convert Measure.restrict_mono le_rfl (hC t) using 1
  all_goals try with_reducible_and_instances rfl
  exact (Measure.restrict_smul _ _ _).symm

lemma IsTestPlan.ball_localization {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) :
    ∃ o : X, ∃ R : ℝ, 0 < R ∧ IsTestPlan (m.restrict (Metric.ball o R)) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  refine ⟨o,R+1,by linarith,hπ.restrict_reference_of_tracks measurableSet_ball ?_⟩
  filter_upwards [hb] with γ hγ t
  exact (hγ t).trans_lt (by linarith)

lemma IsTestPlan.integrable_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : Integrable f m) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  obtain ⟨C,hC⟩ := hπ.2.1
  exact ((hf.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable
    (continuous_eval_const t).measurable.aemeasurable

lemma IsTestPlan.integrable_eval_local {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) {f : X → ℝ}
    (hf : ∀ o : X, ∀ R : ℝ, 0 < R → Integrable f (m.restrict (Metric.ball o R)))
    (t : Time) : Integrable (fun γ => f (γ t)) π := by
  obtain ⟨o,R,hR,hplan⟩ := hπ.ball_localization hb
  exact hplan.integrable_eval (hf o R hR) t

lemma LocallyL2.integrable_eval (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocallyL2 m f) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) (t : Time) :
    Integrable (fun γ => f (γ t)) π := by
  apply hπ.integrable_eval_local hb _ t
  intro o R hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact (hf o R hR).integrable (by norm_num)

end WeakHessian

end
end InlinedFile1

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_MulLogFenchel
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

lemma mul_log_fenchel {r a : ℝ} (hr : 0 ≤ r) : r*a-Real.exp a+r ≤ r*Real.log r := by
  rcases hr.eq_or_lt with hr|hr
  · simp only [← hr,zero_mul,add_zero,sub_nonpos]
    exact (Real.exp_pos _).le
  · have H := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos a) hr)
    rw [Real.log_div (Real.exp_pos _).ne' hr.ne',Real.log_exp] at H
    have := (mul_le_mul_of_nonneg_left H hr.le)
    simp only [mul_sub,mul_div_cancel₀ _ hr.ne',mul_one] at this
    nlinarith

lemma mul_log_floor_gap {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    r*Real.log r - (r*Real.log (max δ r)-max δ r+r) ≤ δ := by
  by_cases h : δ ≤ r
  · rw [max_eq_right h]
    linarith
  · have hrd : r ≤ δ := (le_of_not_ge h)
    rw [max_eq_left hrd]
    rcases hr.eq_or_lt with hr|hr
    · simp [← hr]
    · have H := mul_le_mul_of_nonneg_left (Real.log_le_log hr hrd) hr.le
      nlinarith

lemma exp_sub_bound {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    ‖Real.exp a-Real.exp b‖ ≤ Real.exp M*‖a-b‖ := by
  apply (convex_Iic M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_ hb ha
  intro x hx
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)] using Real.exp_le_exp.mpr hx

lemma min_sub_clamp {x a b : ℝ} (ha : a ≤ b) : ‖a-min x b‖ ≤ ‖a-x‖ := by
  simp only [Real.norm_eq_abs]
  by_cases hx : x ≤ b
  · simp [min_eq_left hx]
  · rw [min_eq_right (le_of_not_ge hx),abs_of_nonpos (sub_nonpos.mpr ha),
      abs_of_nonpos (sub_nonpos.mpr (ha.trans (le_of_not_ge hx)))]
    linarith

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_fenchel (hμ : FiniteEntropy m μ) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) + μ.real univ ≤ entropyReal m μ := by
  have hfμ : Integrable (fun x => f x) μ := f.integrable μ
  have hm : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have he : Integrable (fun x => Real.exp (f x)) m := by
    apply (integrable_const (Real.exp ‖f‖)).mono'
      (Real.continuous_exp.comp f.continuous).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (f.norm_coe_le_norm x))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono (hm.sub he |>.add hr) hlog (fun x => mul_log_fenchel ENNReal.toReal_nonneg)
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hm.sub he) hr,integral_sub hm he,integral_toReal_rnDeriv_mul hμ.1,
    Measure.integral_toReal_rnDeriv hμ.1,← entropyReal_eq_integral_density hμ.1] at H
  exact H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegrableExpBounded
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_exp_of_bounded {f : X → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : ∀ x, f x ≤ A) (ν : Measure X) [IsFiniteMeasure ν] :
    Integrable (fun x => Real.exp (f x)) ν := by
  apply Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp A)
  exact ae_of_all _ fun x => by
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hA x)

lemma exists_continuous_fenchel_approx {f : X → ℝ} (hf : Measurable f) {A M : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hM : 0 < M) (hfM : ∀ x, f x ≤ Real.log M)
    {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) ≤
        (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + ε := by
  let ν := μ+m
  have hfν : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hA)
  let η := ε/(1+M)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨h,hh,_⟩ := hfν.exists_boundedContinuous_integral_sub_le hη
  let g : X →ᵇ ℝ := h ⊓ BoundedContinuousFunction.const X (Real.log M)
  have hg (x : X) : g x = min (h x) (Real.log M) := rfl
  have hfg : Integrable (fun x => ‖f x-g x‖) ν := (hfν.sub (g.integrable ν)).norm
  have hL : (∫ x, ‖f x-g x‖ ∂ν) ≤ η := by
    apply le_trans (integral_mono hfg (hfν.sub (h.integrable ν)).norm ?_) hh
    intro x
    change ‖f x-g x‖ ≤ ‖f x-h x‖
    rw [hg]
    exact min_sub_clamp (hfM x)
  have hμν : μ ≤ ν := Measure.le_add_right le_rfl
  have hmν : m ≤ ν := Measure.le_add_left le_rfl
  have hfμ := hfν.mono_measure hμν
  have hμL : (∫ x, ‖f x-g x‖ ∂μ) ≤ η :=
    (integral_mono_measure hμν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hmL : (∫ x, ‖f x-g x‖ ∂m) ≤ η :=
    (integral_mono_measure hmν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hfirst : (∫ x, f x ∂μ) - (∫ x, g x ∂μ) ≤ η := by
    rw [← integral_sub hfμ (g.integrable μ)]
    exact (le_trans (Real.le_norm_self _) (norm_integral_le_integral_norm _)).trans hμL
  have hgM (x : X) : g x ≤ Real.log M := by rw [hg]; exact min_le_right _ _
  have heF := integrable_exp_of_bounded hf hfM m
  have heG := integrable_exp_of_bounded g.continuous.measurable hgM m
  have heDiff : (∫ x, Real.exp (g x) ∂m) - (∫ x, Real.exp (f x) ∂m) ≤ M*η := by
    calc
      _ = ∫ x, Real.exp (g x)-Real.exp (f x) ∂m := (integral_sub heG heF).symm
      _ ≤ ∫ x, M*‖f x-g x‖ ∂m := by
        apply integral_mono (heG.sub heF) ((hfg.mono_measure hmν).const_mul M)
        intro x
        have H := exp_sub_bound (hgM x) (hfM x)
        rw [Real.exp_log hM,norm_sub_rev (g x)] at H
        exact (le_trans (Real.le_norm_self _) H)
      _ = M*(∫ x, ‖f x-g x‖ ∂m) := integral_const_mul _ _
      _ ≤ M*η := mul_le_mul_of_nonneg_left hmL hM.le
  refine ⟨g,?_⟩
  have H : (1+M)*η = ε := mul_div_cancel₀ ε (by linarith : (1+M) ≠ 0)
  nlinarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyRealContinuousSupport
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      entropyReal m μ ≤ (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ + ε := by
  have hμ := finiteEntropy_of_bounded_density hB hd
  let C := max 1 B.toReal
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := ε/(4*(1+m.real univ))
  have hmnon : 0 ≤ m.real univ := ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by positivity)
  let M := C+δ
  have hM : 0 < M := add_pos hC hδ
  let r := fun x => min (μ.rnDeriv m x).toReal C
  have hrnon (x : X) : 0 ≤ r x := le_min ENNReal.toReal_nonneg hC.le
  have hrC (x : X) : r x ≤ C := min_le_right _ _
  have hrEq : r =ᵐ[m] fun x => (μ.rnDeriv m x).toReal := by
    filter_upwards [rnDeriv_le_of_domination hd hμ.1] with x hx
    exact min_eq_left ((ENNReal.toReal_mono hB hx).trans (le_max_right _ _))
  let f := fun x => Real.log (max δ (r x))
  have hf : Measurable f := Real.measurable_log.comp
    (measurable_const.max ((Measure.measurable_rnDeriv μ m).ennreal_toReal.min measurable_const))
  have htpos (x : X) : 0 < max δ (r x) := lt_of_lt_of_le hδ (le_max_left _ _)
  have hflo (x : X) : Real.log δ ≤ f x :=
    Real.log_le_log hδ (le_max_left _ _)
  have hfM (x : X) : f x ≤ Real.log M :=
    Real.log_le_log (htpos x) (max_le (by dsimp [M]; linarith) (by dsimp [M]; linarith [hrC x]))
  let A := |Real.log δ|+|Real.log M|
  have hfA (x : X) : ‖f x‖ ≤ A := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · dsimp [A]
      have H := neg_abs_le (Real.log δ)
      linarith [hflo x,abs_nonneg (Real.log M)]
    · dsimp [A]
      have H := le_abs_self (Real.log M)
      linarith [hfM x,abs_nonneg (Real.log δ)]
  have hfμ : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have hfm : Integrable f m := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have he := integrable_exp_of_bounded hf hfM m
  have hrf : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have hpoint : ∀ᵐ x ∂m, (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal ≤
      (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal+δ := by
    filter_upwards [hrEq] with x hx
    have H := mul_log_floor_gap (r := (μ.rnDeriv m x).toReal) ENNReal.toReal_nonneg hδ
    have hfexp : Real.exp (f x) = max δ (μ.rnDeriv m x).toReal := by
      dsimp [f]
      rw [Real.exp_log (htpos x),hx]
    have hfeq : f x = Real.log (max δ (μ.rnDeriv m x).toReal) := by dsimp [f]; rw [hx]
    rw [hfexp,hfeq]
    linarith
  have H := integral_mono_ae hlog (((hrf.sub he).add hr).add (integrable_const δ)) hpoint
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal)
      ((hrf.sub he).add hr) (integrable_const δ),
    integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hrf.sub he) hr,
    integral_sub hrf he,integral_toReal_rnDeriv_mul (f := f) hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1,integral_const,smul_eq_mul] at H
  obtain ⟨g,hg⟩ := exists_continuous_fenchel_approx (m := m) (μ := μ) hf hfA hM hfM (half_pos hε)
  refine ⟨g,?_⟩
  have hδeq : δ*(4*(1+m.real univ)) = ε := div_mul_cancel₀ ε (by positivity)
  have hδerr : m.real univ*δ ≤ ε/4 := by nlinarith
  linarith

lemma entropyReal_le_iff_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {a : ℝ} :
    entropyReal m μ ≤ a ↔ ∀ g : X →ᵇ ℝ,
      (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ ≤ a := by
  constructor
  · intro ha g
    exact (entropyReal_fenchel (finiteEntropy_of_bounded_density hB hd) g).trans ha
  · intro ha
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg⟩ := entropyReal_continuous_support hB hd hε
    exact hg.trans (by linarith [ha g])

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ClosedEntropyAlong
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u v
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma isClosed_entropy_le_along {T : Type v} [TopologicalSpace T]
    (μ : T → ProbabilityMeasure X) (hμ : Continuous μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hd : ∀ t, (μ t:Measure X) ≤ B • m)
    (a : T → ℝ) (ha : Continuous a) :
    IsClosed {t | entropyReal m (μ t:Measure X) ≤ a t} := by
  have he : {t | entropyReal m (μ t:Measure X) ≤ a t} =
      ⋂ g : X →ᵇ ℝ, {t | (∫ x, g x ∂(μ t:Measure X))-(∫ x, Real.exp (g x) ∂m)+1 ≤ a t} := by
    ext t
    simp only [mem_ofPred_eq,mem_iInter]
    have H := entropyReal_le_iff_continuous_support hB (hd t) (a := a t)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using H
  rw [he]
  apply isClosed_iInter
  intro g
  apply isClosed_le ?_ ha
  exact (((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp hμ).sub continuous_const).add continuous_const

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_OptimalPlansShort
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

lemma optimalPlansShort_of_ball {μ₀ μ₁ : Measure X} (o : X) (R : ℝ≥0)
    (hb₀ : μ₀ (Metric.closedBall o R)ᶜ = 0) (hb₁ : μ₁ (Metric.closedBall o R)ᶜ = 0) :
    OptimalPlansShort μ₀ μ₁ (2*R) := by
  intro π hp hg hopt
  let := hp
  let : IsProbabilityMeasure μ₀ := by rw [← hopt.1.interpolation_endpoints.1]; exact interpolation_probability π _
  let : IsProbabilityMeasure μ₁ := by rw [← hopt.1.interpolation_endpoints.2]; exact interpolation_probability π _
  have H := optimalPlan_supported_tube (μ₀ := ⟨μ₀,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩) (μ₁ := ⟨μ₁,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩)
    (⟨π,hp⟩ : ProbabilityMeasure (Curve X)) hg hopt.1 hb₀ hb₁
  exact (ae_iff.mpr H).mono fun _ h => boundedEndpointTube_length_le h

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyCell
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

lemma optimal_planEnergy_eq {μ₀ μ₁ : Measure X} {π η : Measure (Curve X)}
    (hπ : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hη : IsOptimalCoupling (endpointCoupling η) μ₀ μ₁)
    (hIπ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π)
    (hIη : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) η) :
    planEnergy π = planEnergy η := by
  apply (ENNReal.ofReal_eq_ofReal_iff (planEnergy_nonneg π) (planEnergy_nonneg η)).mp
  rw [← planCost_eq_ofReal_energy hIπ,← planCost_eq_ofReal_energy hIη]
  exact le_antisymm (hπ.2 _ hη.1) (hη.2 _ hπ.1)

variable {m : Measure X} {K N : ℝ}

namespace EntropyCell

omit [BorelSpace X] [SecondCountableTopology X] in
lemma uniformCap_finite (c : EntropyCell m K N) : c.uniformCap ≠ ∞ :=
  ENNReal.mul_ne_top c.cap_finite ENNReal.ofReal_ne_top
omit [BorelSpace X] [SecondCountableTopology X] in
lemma cap_le_uniformCap (env : CDEnvironment m K N) (c : EntropyCell m K N) : c.cap ≤ c.uniformCap := by
  have H : (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (2*compressionRate K N*c.length)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg (by norm_num) (compressionRate_nonneg (K:=K) env.dimension)) c.length.property))
  simpa only [uniformCap, mul_one] using mul_le_mul' (le_refl c.cap) H

end EntropyCell

namespace CellPlan
lemma energy_eq {c : EntropyCell m K N} (p q : CellPlan c) :
    planEnergy (p.law:Measure (Curve X)) = planEnergy (q.law:Measure (Curve X)) :=
  optimal_planEnergy_eq p.optimal q.optimal p.integrable_energy q.integrable_energy
end CellPlan

variable [ProperSpace X] [SigmaFinite m]

omit [SigmaFinite m]

namespace CellMidpoint
variable {c : EntropyCell m K N}

lemma left_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.leftCell env).uniformCap = c.uniformCap := by
  change (c.cap*ENNReal.ofReal (Real.exp (compressionRate K N*c.length)))*
    ENNReal.ofReal (Real.exp (2*compressionRate K N*((c.length:ℝ)/2))) = _
  rw [mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  congr 1
  ring

lemma right_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.rightCell env).uniformCap = c.uniformCap := p.left_uniformCap env

end CellMidpoint
end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_Join
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CellMidpoint
variable {c : EntropyCell m K N} (p : CellMidpoint c) (env : CDEnvironment m K N)

lemma left_energy (l : CellPlan (p.leftCell env)) :
    planEnergy (l.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let r := (env.midpoint (p.rightCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.1
  change ((p.join env l r).law:Measure (Curve X)).map halfCurve = (l.law:Measure (Curve X)) at H
  rw [← H,planEnergy_half (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

lemma right_energy (r : CellPlan (p.rightCell env)) :
    planEnergy (r.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let l := (env.midpoint (p.leftCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.2
  change ((p.join env l r).law:Measure (Curve X)).map rightCurve = (r.law:Measure (Curve X)) at H
  rw [← H,planEnergy_right (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

end CellMidpoint

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma build_dominated (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.build n c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      exact dominated_mono_constant c.left_dominated (c.cap_le_uniformCap env)
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      exact dominated_mono_constant c.right_dominated (c.cap_le_uniformCap env)
  | succ n ih =>
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half,← (env.midpoint c).left_uniformCap env]
      exact ih _ s hs
    · rw [env.build_right,← (env.midpoint c).right_uniformCap env]
      exact ih _ s hs

lemma entropy_chord_half {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : 0 ≤ s) :
    (1-s)*A+s*M-K/2*(s*(1-s))*(E/4) ≤
      (1-s/2)*A+(s/2)*B-K/2*((s/2)*(1-s/2))*E := by
  calc
    _ ≤ (1-s)*A+s*((A+B)/2-K/8*E)-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM hs
      linarith only [H]
    _ = _ := by ring

lemma entropy_chord_right {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : s ≤ 1) :
    (1-s)*M+s*B-K/2*(s*(1-s))*(E/4) ≤
      (1-(s+1)/2)*A+((s+1)/2)*B-K/2*(((s+1)/2)*(1-(s+1)/2))*E := by
  calc
    _ ≤ (1-s)*((A+B)/2-K/8*E)+s*B-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hs)
      linarith only [H]
    _ = _ := by ring

lemma build_entropy_bound (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.build n c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.build n c).law:Measure (Curve X)) := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      simp only [timeZero,sub_zero,one_mul,zero_mul,mul_zero,add_zero,le_refl]
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      simp only [timeOne,sub_self,zero_mul,one_mul,zero_add,mul_zero,sub_zero,le_refl]
  | succ n ih =>
    have hE := (env.build (n+1) c).energy_eq (env.midpoint c).toCellPlan
    rw [hE]
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half]
      apply (ih ((env.midpoint c).leftCell env) s hs).trans
      rw [(env.midpoint c).left_energy env]
      exact entropy_chord_half (env.midpoint c).entropy_bound s.2.1
    · rw [env.build_right]
      apply (ih ((env.midpoint c).rightCell env) s hs).trans
      rw [(env.midpoint c).right_energy env]
      exact entropy_chord_right (env.midpoint c).entropy_bound s.2.2

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Law
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

omit [SecondCountableTopology X] [ProperSpace X] in
lemma continuous_lawAt_time (π : ProbabilityMeasure (Curve X)) : Continuous (lawAt π) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have he (t : Time) : (∫ x, f x ∂(lawAt π t:Measure X)) = ∫ γ, f (γ t) ∂(π:Measure (Curve X)) :=
    integral_map (continuous_eval_const t).measurable.aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t; exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  · intro t; exact ae_of_all _ fun γ => f.norm_coe_le_norm (γ t)
  · exact integrable_const ‖f‖
  · exact ae_of_all _ fun γ => f.continuous.comp γ.continuous

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [ProperSpace X] in
lemma IsGeodesic.speed_energy_le {γ : Curve X} (hγ : IsGeodesic γ) :
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)^2) := by
  calc
    _ ≤ ∫⁻ _t in Icc (0:ℝ) 1, (ENNReal.ofReal (dist (γ timeZero) (γ timeOne)))^2 := by
      apply lintegral_mono_ae
      exact hγ.squareControl.metricSpeed_le.mono fun t ht => pow_le_pow_left' ht 2
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        sub_zero,ENNReal.ofReal_one,mul_one,ENNReal.ofReal_pow dist_nonneg]

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t =
      interpolation ((env.build n c).law:Measure (Curve X)) t :=
  Classical.choose_spec (env.exists_stable_plan c) n t ht

lemma limitPlan_entropy_bound_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  rw [env.limitPlan_dyadic c n t ht,(env.limitPlan c).energy_eq (env.build n c)]
  exact env.build_entropy_bound n c t ht

lemma limitPlan_dominated_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  rw [env.limitPlan_dyadic c n t ht]
  exact env.build_dominated n c t ht

lemma limitPlan_dominated (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  have hnu : IsFiniteMeasure (c.uniformCap • m.restrict Q) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top c.uniformCap_finite.lt_top (measure_lt_top _ _)⟩
  let := hnu
  have hclosed : IsClosed {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} :=
    (isClosed_probability_dominated _).preimage (continuous_lawAt_time _)
  have hdyadic : (⋃ n, dyadicTimes n) ⊆ {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    have hd := env.limitPlan_dominated_dyadic c n s hn
    have hsupport : interpolation ((env.limitPlan c).law:Measure (Curve X)) s Qᶜ = 0 :=
      geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) s
    have H := Measure.restrict_mono_measure hd Q
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport),Measure.restrict_smul] at H
  have H : (lawAt (env.limitPlan c).law t:Measure X) ≤ c.uniformCap • m.restrict Q :=
    (closure_minimal hdyadic hclosed) (dense_dyadicTimes t)
  exact H.trans (smul_le_smul_left _ Measure.restrict_le_self)

lemma limitPlan_supported (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t (Metric.closedBall c.center (3*(c.radius:ℝ)))ᶜ = 0 :=
  geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) t

lemma limitPlan_finite_entropy (c : EntropyCell m K N) (t : Time) :
    FiniteEntropy m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let : IsProbabilityMeasure (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) :=
    interpolation_probability _ _
  have hs : ∀ᵐ x ∂interpolation ((env.limitPlan c).law:Measure (Curve X)) t, x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c t)
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs).mp
  apply finiteEntropy_of_bounded_density c.uniformCap_finite
  have H := Measure.restrict_mono_measure (env.limitPlan_dominated c t) Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs,Measure.restrict_smul] at H

lemma limitPlan_boundedTracks (c : EntropyCell m K N) :
    BoundedTracks ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨c.center,3*(c.radius:ℝ)+1,by positivity,?_⟩
  have H := optimalPlan_supported_tube (env.limitPlan c).law (env.limitPlan c).geodesic
    (env.limitPlan c).optimal.1 c.left_supported c.right_supported
  filter_upwards [ae_iff.mpr H] with γ hγ
  intro t
  exact (boundedEndpointTube_range hγ t).trans (by linarith)

lemma limitPlan_isTestPlan (c : EntropyCell m K N) :
    IsTestPlan m ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),⟨c.uniformCap.toNNReal,?_⟩,?_,?_⟩
  · intro t
    rw [ENNReal.coe_toNNReal c.uniformCap_finite]
    exact env.limitPlan_dominated c t
  · exact (env.limitPlan c).geodesic.mono fun γ hγ => hγ.squareControl.isAC2
  · have hB : (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2
        ∂volume ∂((env.limitPlan c).law:Measure (Curve X))) ≤ ENNReal.ofReal ((c.length:ℝ)^2) := by
      calc
        _ ≤ ∫⁻ _γ, ENNReal.ofReal ((c.length:ℝ)^2) ∂((env.limitPlan c).law:Measure (Curve X)) := by
          apply lintegral_mono_ae
          filter_upwards [(env.limitPlan c).geodesic,
            c.short _ inferInstance (env.limitPlan c).geodesic (env.limitPlan c).optimal] with γ hγ hlen
          exact hγ.speed_energy_le.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ dist_nonneg hlen 2))
        _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
    exact hB.trans_lt ENNReal.ofReal_lt_top

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LimitPlanEntropyBound
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
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
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_entropy_bound (c : EntropyCell m K N) (t : Time) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let p := (env.limitPlan c).law
  have hs (s : Time) : ∀ᵐ x ∂(lawAt p s:Measure X), x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c s)
  have hd (s : Time) : (lawAt p s:Measure X) ≤ c.uniformCap • m.restrict Q := by
    have H := Measure.restrict_mono_measure (env.limitPlan_dominated c s) Q
    change (lawAt p s:Measure X).restrict Q ≤ (c.uniformCap • m).restrict Q at H
    rwa [Measure.restrict_eq_self_of_ae_mem (hs s),Measure.restrict_smul] at H
  have he (s : Time) : entropyReal (m.restrict Q) (lawAt p s:Measure X) =
      entropyReal m (lawAt p s:Measure X) :=
    entropyReal_restrict_reference Metric.isClosed_closedBall.measurableSet
      (env.limitPlan_finite_entropy c s).1 (hs s)
  let a : Time → ℝ := fun s =>
      (1-(s:ℝ))*entropyReal m (c.leftLaw:Measure X)+(s:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((s:ℝ)*(1-(s:ℝ)))*planEnergy (p:Measure (Curve X))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hc : IsClosed {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    simp_rw [← he]
    exact isClosed_entropy_le_along (lawAt p) (continuous_lawAt_time p) c.uniformCap_finite hd a ha
  have hdy : (⋃ n, dyadicTimes n) ⊆ {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    exact env.limitPlan_entropy_bound_dyadic c n s hn
  exact (closure_minimal hdy hc) (dense_dyadicTimes t)

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FiniteEntropyBoundedSupported
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

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology



open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology


open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable




























open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable













open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory InformationTheory
open scoped Topology


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology



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

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

omit [SecondCountableTopology X] [ProperSpace X] in
lemma finiteEntropy_of_bounded_supported (hf : FiniteOnBoundedSets m)
    (μ : ProbabilityMeasure X) (o : X) (R : ℝ≥0)
    (hs : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hd : (μ:Measure X) ≤ C • m) : FiniteEntropy m (μ:Measure X) := by
  let Q := Metric.closedBall o (R:ℝ)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hf Q Metric.isBounded_closedBall⟩
  have hs' : ∀ᵐ x ∂(μ:Measure X), x ∈ Q := ae_iff.mpr hs
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs').mp
  apply finiteEntropy_of_bounded_density hC
  have H := Measure.restrict_mono_measure hd Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs',Measure.restrict_smul] at H

theorem CurvatureDimension.exists_entropy_testPlan (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hf : FiniteOnBoundedSets m)
    (μ₀ μ₁ : ProbabilityMeasure X) (o : X) (R : ℝ≥0)
    (hs₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hs₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (h₀ : (μ₀:Measure X) ≤ C • m) (h₁ : (μ₁:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), IsTestPlan m (π:Measure (Curve X)) ∧
      BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
      (∀ t : Time, FiniteEntropy m (interpolation (π:Measure (Curve X)) t)) ∧
      (∀ t : Time,
        entropyReal m (interpolation (π:Measure (Curve X)) t) ≤
          (1-(t:ℝ))*entropyReal m (μ₀:Measure X) +
          (t:ℝ)*entropyReal m (μ₁:Measure X) -
          K/2*(t:ℝ)*(1-(t:ℝ))*planEnergy (π:Measure (Curve X))) ∧
      (∀ t : Time, interpolation (π:Measure (Curve X)) t ≤
        (C*ENNReal.ofReal (Real.exp (4*compressionRate K N*R))) • m) := by
  let env : CDEnvironment m K N := ⟨hN,hCD,hf⟩
  let c : EntropyCell m K N := {
    leftLaw := μ₀, rightLaw := μ₁, center := o, radius := R, length := 2*R,
    cap := C, cap_pos := hC0, cap_finite := hCt,
    left_supported := hs₀, right_supported := hs₁,
    left_dominated := h₀, right_dominated := h₁,
    left_entropy := finiteEntropy_of_bounded_supported hf μ₀ o R hs₀ hCt h₀,
    right_entropy := finiteEntropy_of_bounded_supported hf μ₁ o R hs₁ hCt h₁,
    short := by simpa using optimalPlansShort_of_ball o R hs₀ hs₁ }
  refine ⟨(env.limitPlan c).law,env.limitPlan_isTestPlan c,env.limitPlan_boundedTracks c,
    (env.limitPlan c).geodesic,(env.limitPlan c).optimal,
    env.limitPlan_finite_entropy c,?_,?_⟩
  · intro t
    simpa only [c,mul_assoc] using env.limitPlan_entropy_bound c t
  · intro t
    have h := env.limitPlan_dominated c t
    have hcap : c.uniformCap = C*ENNReal.ofReal (Real.exp (4*compressionRate K N*R)) := by
      dsimp only [EntropyCell.uniformCap,c]
      congr 3
      push_cast
      ring
    rwa [hcap] at h

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SquareSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile17
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma gamma_locality_left (hfin : FiniteOnBoundedSets m) {f g v : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ᵐ x ∂m, x ∈ Q → f x = g x) :
    ∀ᵐ x ∂m, x ∈ Q → gamma m f v x = gamma m g v x := by
  have hp := weakGradient_locality (hf.add hfin hv) (hg.add hfin hv) hQ
    (he.mono fun x hx hxQ => by rw [hx hxQ])
  have hn := weakGradient_locality (hf.sub hfin hv) (hg.sub hfin hv) hQ
    (he.mono fun x hx hxQ => by rw [hx hxQ])
  filter_upwards [hp,hn] with x hx hy h
  simp only [gamma,hx h,hy h]

lemma gamma_zero_off_set (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f v : X → ℝ}
    (hf : LocalSobolev m f) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ᵐ x ∂m, x ∉ Q → f x = 0) :
    ∀ᵐ x ∂m, x ∉ Q → gamma m f v x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [gamma_locality_left hfin hf hz hv hQ.compl he,
    abs_gamma_le hfin hpar hz hv,weakGradient_const (m := m) 0] with x hx hy hz h
  rw [hx h]
  apply abs_nonpos_iff.mp
  simpa only [hz,zero_mul] using hy
end WeakHessian

end
end InlinedFile17

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

end WeakHessian

end
end InlinedFile81

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactLipDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile155
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma compactLipLp_dense (hfin : FiniteOnBoundedSets m) :
    (compactLipLp m).topologicalClosure = ⊤ := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro H hH
  change H=0
  have he : (H:X → ℝ) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro f hfc hf
    have hf2 : MemLp f 2 m := hf.choose_spec.continuous.memLp_of_hasCompactSupport hfc
    have hm : hf2.toLp f ∈ compactLipLp m := ⟨f,hf,hfc,hf2.coeFn_toLp.symm⟩
    have hz := Submodule.inner_left_of_mem_orthogonal hm hH
    rw [L2.inner_def] at hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial,mul_comm]
  apply Lp.ext
  exact he.trans (Lp.coeFn_zero ℝ 2 m).symm

lemma exists_compactLip_L2_approx (hfin : FiniteOnBoundedSets m) (u : Lp ℝ 2 m) :
    ∃ us : ℕ → Lp ℝ 2 m,(∀ n,us n ∈ compactLipLp m) ∧ Tendsto us atTop (𝓝 u) := by
  have hcl : u ∈ closure (compactLipLp m : Set (Lp ℝ 2 m)) := by
    change u ∈ (compactLipLp m).topologicalClosure
    rw [compactLipLp_dense hfin]
    trivial
  exact mem_closure_iff_seq_limit.mp hcl
end WeakHessian

end
end InlinedFile155

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_InverseSqrtIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile145
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma inv_sqrt_eq_rpow {s : ℝ} (hs : 0 ≤ s) : (Real.sqrt s)⁻¹ = s ^ (-(1/2:ℝ)) := by
  rw [Real.rpow_neg hs,Real.sqrt_eq_rpow]

lemma integrableOn_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun s : ℝ => (Real.sqrt s)⁻¹) (Ioc 0 b) volume := by
  have integrablePower := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
    (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ)< -(1/2:ℝ) by norm_num))
  apply integrablePower.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (inv_sqrt_eq_rpow hs.1.le).symm

lemma integral_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in Ioc 0 b,(Real.sqrt s)⁻¹) = 2*Real.sqrt b := by
  calc
    _ = ∫ s in Ioc 0 b,s ^ (-(1/2:ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact inv_sqrt_eq_rpow hs.1.le
    _ = ∫ s in (0:ℝ)..b,s ^ (-(1/2:ℝ)) := (intervalIntegral.integral_of_le hb).symm
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -(1/2:ℝ)))]
      norm_num [Real.sqrt_eq_rpow]
      ring
end WeakHessian

end
end InlinedFile145

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile130
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_generator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => cheegerHeat h s u) (cheegerHeat h t A) t := by
  have hc := cheegerHeat_continuousOn hfin h A
  have hat := (hc t ht.le).continuousAt (Ici_mem_nhds ht)
  have hi : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := (hc.mono (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hc.mono Ioi_subset_Ici_self) t ht) hat).add_const u
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [cheegerHeat_integral_generator hfin h hu hs.le, sub_add_cancel]
end WeakHessian

end
end InlinedFile130

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatPositiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile131
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_positive (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t) :
    ∃ A : Lp ℝ 2 m, (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A ∧
      HasDerivAt (fun s => cheegerHeat h s u) A t := by
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨B,hB⟩ := Q.heat_hasFormGenerator m (half_pos ht) u
  change Q.IsFormGenerator (cheegerHeat h (t/2) u) B at hB
  let A := cheegerHeat h (t/2) B
  have hg := Q.formGenerator_heat m hB (t/2)
  have he : cheegerHeat h (t/2) (cheegerHeat h (t/2) u) = cheegerHeat h t u := by
    have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (cheegerHeat_add h (half_pos ht).le (half_pos ht).le)
    simpa only [add_halves,mul_apply_eq_comp] using H.symm
  change Q.IsFormGenerator (cheegerHeat h (t/2) (cheegerHeat h (t/2) u)) A at hg
  refine ⟨A,he ▸ hg,?_⟩
  have HD := cheegerHeat_deriv_at_generator hfin h hB (half_pos ht)
  have hc := (hasDerivAt_id t).sub_const (t/2)
  have H := HD.scomp_of_eq t hc (by rw [id_eq, sub_half] : t/2 = id t-t/2)
  simp only [Function.comp_def,one_smul,id_eq] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show t/2<t by linarith)] with s hs
  have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
    (cheegerHeat_add h (show 0 ≤ s-t/2 by linarith) (half_pos ht).le)
  simpa only [sub_add_cancel,mul_apply_eq_comp] using H
end WeakHessian

end
end InlinedFile131

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_BoundedLipschitzDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile141
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma bounded_lipschitz_L2_approx (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (n : ℕ) (hu : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) :
    ∃ fs : ℕ → X → ℝ,(∀ k,GloballyLipschitz (fs k)) ∧
      (∀ k x,|fs k x| ≤ (n:ℝ)) ∧ ∃ hfs : ∀ k,MemLp (fs k) 2 m,
        Tendsto (fun k => (hfs k).toLp (fs k)) atTop (𝓝 u) := by
  let τ (k : ℕ) := 1/((k:ℝ)+1)
  have hτ (k : ℕ) : 0 < τ k := by dsimp [τ]; positivity
  let vs (k : ℕ) := cheegerHeat h (τ k) u
  have hvT : Tendsto vs atTop (𝓝 u) := by
    have H := (cheegerHeat_continuousOn hfin h u 0 (show (0:ℝ) ∈ Ici 0 by simp)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun k => (hτ k).le⟩)
    simpa only [cheegerHeat_zero,one_apply_eq_self,Function.comp_def,vs,τ] using H
  have hex (k : ℕ) : ∃ f : X → ℝ,GloballyLipschitz f ∧ ∃ hf : MemLp f 2 m,dist (hf.toLp f) (vs k) < τ k := by
    obtain ⟨A,hA,-⟩ := cheegerHeat_deriv_at_positive hfin h u (hτ k)
    obtain ⟨f,hf,hf2,hd,-⟩ := cheegerEnergy_lt_approx hA.1 (hτ k)
    exact ⟨f,hf,hf2,hd⟩
  choose gs hgs hgs2 hdist using hex
  have hgT : Tendsto (fun k => (hgs2 k).toLp (gs k)) atTop (𝓝 u) := by
    apply Filter.Tendsto.congr_dist hvT
    exact squeeze_zero (fun _ => dist_nonneg) (fun k => by simpa only [dist_comm] using (hdist k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  let fs (k : ℕ) (x : X) := realClip n (gs k x)
  have hfs (k : ℕ) : MemLp (fs k) 2 m := (realClip_lipschitz n).comp_memLp (realClip_zero n) (hgs2 k)
  refine ⟨fs,fun k => ⟨(hgs k).choose,by simpa only [one_mul,Function.comp_def,fs] using (realClip_lipschitz n).comp (hgs k).choose_spec⟩,
    fun k x => realClip_abs_le n (gs k x),hfs,?_⟩
  let T := (realClip_lipschitz n).compLp (μ := m) (p := 2) (realClip_zero n)
  have hTe : T u = u := by
    apply Lp.ext
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) u,hu] with x hx hb
    simpa only [Function.comp_apply,realClip,min_eq_left (abs_le.mp hb).2,max_eq_right (abs_le.mp hb).1] using hx
  have hTk (k : ℕ) : T ((hgs2 k).toLp (gs k)) = (hfs k).toLp (fs k) := by
    apply Lp.ext
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) ((hgs2 k).toLp (gs k)),
      (hgs2 k).coeFn_toLp,(hfs k).coeFn_toLp] with x hx hy hz
    rw [hx,Function.comp_apply,hy,hz]
  have H := ((realClip_lipschitz n).lipschitzWith_compLp (μ := m) (p := 2) (realClip_zero n)).continuous.tendsto u |>.comp hgT
  change Tendsto (fun k => T ((hgs2 k).toLp (gs k))) atTop (𝓝 (T u)) at H
  simpa only [hTe,hTk] using H
end WeakHessian

end
end InlinedFile141

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LpLipschitzClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile140
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma exists_lipschitz_of_tendsto_Lp {L : ℝ≥0} {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hu : Tendsto us atTop (𝓝 u)) {fs : ℕ → X → ℝ}
    (hf : ∀ n,LipschitzWith L (fs n)) (he : ∀ n,fs n =ᵐ[m] us n) :
    ∃ f : X → ℝ,LipschitzWith L f ∧ f =ᵐ[m] u := by
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have H : ∀ᵐ x ∂m,Tendsto (fun n => fs (ns n) x) atTop (𝓝 (u x)) := by
    filter_upwards [hlim,ae_all_iff.mpr he] with x hx he
    exact hx.congr (fun n => (he (ns n)).symm)
  let S := {x | Tendsto (fun n => fs (ns n) x) atTop (𝓝 (u x))}
  have hLip : LipschitzOnWith L (u : X → ℝ) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hx : Tendsto (fun n => fs (ns n) x) atTop (𝓝 (u x))).dist hy)
      (Eventually.of_forall fun n => (hf (ns n)).dist_le_mul x y)
  obtain ⟨f,hf,hfe⟩ := hLip.extend_real
  refine ⟨f,hf,?_⟩
  exact H.mono fun x hx => (hfe hx).symm
end WeakHessian

end
end InlinedFile140

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile137
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocallyL2.locallyIntegrable (hfin : FiniteOnBoundedSets m) {f : X → ℝ}
    (hf : LocallyL2 m f) : LocallyIntegrable f m := by
  intro x
  let : IsFiniteMeasure (m.restrict (Metric.ball x 1)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,(hf x 1 zero_lt_one).integrable (by norm_num)⟩

lemma exists_lipschitz_of_local_ball_averages [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    {g : X → ℝ} (hg : LocallyIntegrable g m) {C : ℝ≥0}
    (h : ∀ x y : X, ∀ r : ℝ,0 < r →
      |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤
        (C:ℝ)*(2*r+dist x y)) :
    ∃ g' : X → ℝ,LipschitzWith C g' ∧ g' =ᵐ[m] g := by
  let S : Set X := {x | Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,g z ∂m) (𝓝[>] 0) (𝓝 (g x))}
  have hS : ∀ᵐ x ∂m,x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average m hg 1] with x hx
    apply hx (fun _ : ℝ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.le
  have hLip : LipschitzOnWith C g S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq]
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have H := le_of_tendsto_of_tendsto (hx.sub hy |>.abs)
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hr).add tendsto_const_nhds))
      (show ∀ᶠ r in 𝓝[>] (0:ℝ), |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤ (C:ℝ)*(2*r+dist x y) from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h x y r hr)
    simpa only [mul_zero,zero_add] using H
  obtain ⟨g',hg',heq⟩ := hLip.extend_real
  exact ⟨g',hg',hS.mono fun x hx => (heq hx).symm⟩

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsLocalWeakUpperGradient.geodesic_endpoint_lipschitz {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {C : ℝ≥0} (hbD : ∀ᵐ x ∂m,D x ≤ C) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ) :
    ∀ᵐ γ ∂π,|f (γ timeOne)-f (γ timeZero)| ≤ (C:ℝ)*dist (γ timeZero) (γ timeOne) := by
  filter_upwards [hD.ae_endpoint_le hf hπ hb,hπ.ae_ae_eval_of_ae hbD,hgeo] with γ hγ hDγ hg
  have H : (∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (D (evalReal γ t))*metricSpeed γ t) ≤
      ENNReal.ofReal ((C:ℝ)*dist (γ timeZero) (γ timeOne)) := by
    calc
      _ ≤ ∫⁻ _t in Icc (0:ℝ) 1,ENNReal.ofReal (C:ℝ)*ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) := by
        apply lintegral_mono_ae
        filter_upwards [hDγ,hg.ae_metricSpeed_le] with t ht hs
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal ht) hs
      _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
        ENNReal.ofReal_one,mul_one,ENNReal.ofReal_mul C.coe_nonneg]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mp (hγ.trans H)

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_setDensity (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) (f : X → ℝ) :
    (∫ x,f x ∂densityMeasure m (setDensity S hS hfin)) = ⨍ x in S,f x ∂m := by
  rw [integral_densityMeasure m _ (setDensity_nonneg S hS hfin),setAverage_eq,measureReal_def,smul_eq_mul,
    ← integral_const_mul,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [setDensity_coe S hS hfin] with x hx
  rw [hx]
  by_cases hxs : x ∈ S <;> simp [hxs]

end WeakHessian

end
end InlinedFile137

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CDSobolevLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile138
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

theorem CurvatureDimension.sobolev_to_lipschitz {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hN : 1 < N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) {f D : X → ℝ} (hf : LocallyL2 m f)
    (hD : IsLocalWeakUpperGradient m f D) {L : ℝ≥0} (hbD : ∀ᵐ x ∂m,D x ≤ L) :
    ∃ f' : X → ℝ,LipschitzWith L f' ∧ f' =ᵐ[m] f := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hcd.uniform_local_doubling hN hfull hfin
  apply exists_lipschitz_of_local_ball_averages (hf.locallyIntegrable hfin)
  intro a b r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hbound (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  let μ (x : X) := integrableDensityProbability (u x) (hn x) (hmass x)
  have hμ (x : X) : (μ x:Measure X) = densityMeasure m (u x) := rfl
  have hball (x : X) : ∀ᵐ z ∂(μ x:Measure X),dist z x ≤ r := densityMeasure_ae_ball (u x) x (hs x)
  let R : ℝ≥0 := ⟨2*r+dist a b,by positivity⟩
  have hsa : (μ a:Measure X) (Metric.closedBall a R)ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hball a] with z hz
    change dist z a ≤ 2*r+dist a b
    linarith [dist_nonneg (x := a) (y := b)]
  have hsb : (μ b:Measure X) (Metric.closedBall a R)ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hball b] with z hz
    change dist z a ≤ 2*r+dist a b
    have H := dist_triangle z b a
    rw [dist_comm b a] at H
    linarith
  let C : ℝ := max (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹+1
  have hC : 0 < C := by
    have hA : 0 ≤ (m (Metric.closedBall a r)).toReal⁻¹ := by positivity
    have := le_max_left (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹
    dsimp only [C]; linarith
  have hdua : (μ a:Measure X) ≤ ENNReal.ofReal C • m := by
    rw [hμ a]
    apply densityMeasure_le_const
    filter_upwards [hbound a] with z hz
    have := le_max_left (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹
    exact (le_abs_self _).trans (hz.trans (by dsimp only [C]; linarith))
  have hdub : (μ b:Measure X) ≤ ENNReal.ofReal C • m := by
    rw [hμ b]
    apply densityMeasure_le_const
    filter_upwards [hbound b] with z hz
    have := le_max_right (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹
    exact (le_abs_self _).trans (hz.trans (by dsimp only [C]; linarith))
  obtain ⟨π,hπ,htracks,hgeo,hopt,hent,hconv,hdom⟩ := hcd.exists_entropy_testPlan hN hfin (μ a) (μ b) a R hsa hsb
    (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hdua hdub
  have he := hopt.1.interpolation_endpoints
  have hpa : ∀ᵐ γ ∂(π:Measure (Curve X)),dist (γ timeZero) a ≤ r := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero) (p := fun z => dist z a ≤ r) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ z ∂interpolation (π:Measure (Curve X)) timeZero,dist z a ≤ r
    rw [he.1]
    exact hball a
  have hpb : ∀ᵐ γ ∂(π:Measure (Curve X)),dist (γ timeOne) b ≤ r := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne) (p := fun z => dist z b ≤ r) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ z ∂interpolation (π:Measure (Curve X)) timeOne,dist z b ≤ r
    rw [he.2]
    exact hball b
  have hE : ∀ᵐ γ ∂(π:Measure (Curve X)),|f (γ timeOne)-f (γ timeZero)| ≤ (L:ℝ)*(2*r+dist a b) := by
    filter_upwards [hD.geodesic_endpoint_lipschitz hf.aemeasurable hbD hπ htracks hgeo,hpa,hpb] with γ hγ ha hb
    apply hγ.trans (mul_le_mul_of_nonneg_left _ L.coe_nonneg)
    have h1 := dist_triangle (γ timeZero) a (γ timeOne)
    have h2 := dist_triangle a b (γ timeOne)
    rw [dist_comm b (γ timeOne)] at h2
    linarith
  have hint0 := hf.integrable_eval hfin hπ htracks timeZero
  have hint1 := hf.integrable_eval hfin hπ htracks timeOne
  have HI : |(∫ γ,f (γ timeOne) ∂(π:Measure (Curve X)))-(∫ γ,f (γ timeZero) ∂(π:Measure (Curve X)))| ≤ (L:ℝ)*(2*r+dist a b) := by
    rw [← integral_sub hint1 hint0]
    apply abs_integral_le_integral_abs.trans
    exact (integral_mono_ae (hint1.sub hint0).abs (integrable_const _) hE).trans_eq (by simp)
  have hmap (t : Time) : (∫ γ,f (γ t) ∂(π:Measure (Curve X))) = ∫ x,f x ∂interpolation (π:Measure (Curve X)) t := by
    symm
    exact integral_map (continuous_eval_const t).measurable.aemeasurable
      (hf.aemeasurable.mono_ac (Measure.absolutelyContinuous_of_le_smul (hπ.2.1.choose_spec t))).aestronglyMeasurable
  rw [hmap timeOne,hmap timeZero,he.1,he.2,hμ a,hμ b,integral_setDensity,integral_setDensity,abs_sub_comm] at HI
  exact HI

end WeakHessian

end
end InlinedFile138

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ReversePoincarePointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile139
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_reversePoincare_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (Real.sqrt ((n:ℝ)^2/(2*t*Real.exp (-2*|K| *t))))) g ∧
      g =ᵐ[m] cheegerHeat h t (hf2.toLp f) := by
  obtain ⟨A,hA,-⟩ := cheegerHeat_deriv_at_positive hfin h (hf2.toLp f) ht
  have hS := (hrcd.1.global_isLaplacian_of_formGenerator hfin o h _ _ hA).1
  apply hrcd.1.sobolev_to_lipschitz hN hfull hfin hS.2.1.1
    (weakGradient_isMinimal hS.2.1.2).1
  have H := hrcd.cheegerHeat_reversePoincare_pointwise hN hfull hfin h o hf hf2 n hfb ht
  filter_upwards [H] with x hx
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hc : 0 < 2*t*Real.exp (-2*|K| *t) := by positivity
  have HH : (weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2 ≤ (n:ℝ)^2/(2*t*Real.exp (-2*|K| *t)) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hx)
  have hroot := Real.sq_sqrt (show 0 ≤ (n:ℝ)^2/(2*t*Real.exp (-2*|K| *t)) by positivity)
  nlinarith only [HH,hroot,Real.sqrt_nonneg ((n:ℝ)^2/(2*t*Real.exp (-2*|K| *t)))]
end WeakHessian

end
end InlinedFile139

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatBoundedRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile142
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_bounded_regularization {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    (n : ℕ) (hu : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (Real.sqrt ((n:ℝ)^2/(2*t*Real.exp (-2*|K| *t))))) g ∧
      g =ᵐ[m] cheegerHeat h t u := by
  obtain ⟨fs,hf,hb,hf2,hT⟩ := bounded_lipschitz_L2_approx hfin h u n hu
  have hex (k : ℕ) := hrcd.cheegerHeat_reversePoincare_lipschitz hN hfull hfin h o
    (hf k).choose_spec (hf2 k) n (hb k) ht
  choose gs hLip he using hex
  have HT := (cheegerHeat h t).continuous.tendsto u |>.comp hT
  exact exists_lipschitz_of_tendsto_Lp HT hLip he
end WeakHessian

end
end InlinedFile142

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatSmoothingCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile143
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma reversePoincare_sqrt_le (K : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1/(2*t*Real.exp (-2*|K| *t))) ≤ Real.exp (|K| *t)/Real.sqrt t := by
  have he : Real.exp (-2*|K| *t) = (Real.exp (|K| *t)^2)⁻¹ := by
    rw [show -2*|K| *t= -((|K| *t)+(|K| *t)) by ring,Real.exp_neg,Real.exp_add,pow_two]
  rw [he]
  have H : 1/(2*t*(Real.exp (|K| *t)^2)⁻¹) = Real.exp (|K| *t)^2/(2*t) := by field_simp
  rw [H,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.sqrt_pos.mpr ht)
    (Real.sqrt_le_sqrt (by linarith : t ≤ 2*t))

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_bounded_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (B*Real.exp (|K| *t)/Real.sqrt t)) g ∧
      g =ᵐ[m] cheegerHeat h t u := by
  by_cases hb : B = 0
  · have huz : u = 0 := by
      apply Lp.ext
      filter_upwards [hu,Lp.coeFn_zero ℝ 2 m] with x hx he
      rw [he]
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa [hb] using hx) (abs_nonneg _)
    refine ⟨fun _ => 0,?_,?_⟩
    · simp [hb]
    · rw [huz,map_zero]
      exact (Lp.coeFn_zero ℝ 2 m).symm
  have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
  let v := B⁻¹ • u
  have hv : ∀ᵐ x ∂m,|v x| ≤ (1:ℝ) := by
    filter_upwards [hu,Lp.coeFn_smul B⁻¹ u] with x hx he
    rw [show v x=B⁻¹*u x from he,abs_mul,abs_inv,abs_of_pos hp]
    exact (inv_mul_le_iff₀ hp).mpr (by simpa using hx)
  obtain ⟨g,hg,he⟩ := hrcd.cheegerHeat_bounded_regularization hN hfull hfin h o v 1 (by simpa using hv) ht
  refine ⟨fun x => B*g x,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg hB]
    have HG := hg.dist_le_mul x y
    simp only [Real.dist_eq,Real.coe_toNNReal _ (Real.sqrt_nonneg _),Nat.cast_one,one_pow] at HG
    rw [Real.coe_toNNReal _ (by positivity)]
    calc
      _ ≤ B*(Real.sqrt (1/(2*t*Real.exp (-2*|K| *t)))*dist x y) := mul_le_mul_of_nonneg_left HG hB
      _ = (B*Real.sqrt (1/(2*t*Real.exp (-2*|K| *t))))*dist x y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (reversePoincare_sqrt_le K ht) hB) dist_nonneg
  · have hvU : B • cheegerHeat h t v = cheegerHeat h t u := by
      rw [← map_smul,show B • v=u by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hb,one_smul]]
    filter_upwards [he,Lp.coeFn_smul B (cheegerHeat h t v)] with x hx hy
    rw [hx]
    change (B • (cheegerHeat h t v : X → ℝ)) x = _
    rw [← hy,hvU]
end WeakHessian

end
end InlinedFile143

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

end WeakHessian

end
end InlinedFile123

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LipschitzBochnerIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile144
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] in
lemma exists_lipschitz_integral [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {T : Type*} [MeasurableSpace T] {μ : Measure T}
    {us : T → Lp ℝ 2 m} (hu : Integrable us μ) {cs : T → ℝ≥0}
    (hc : Integrable (fun t => (cs t:ℝ)) μ)
    (hLip : ∀ᵐ t ∂μ,∃ g : X → ℝ,LipschitzWith (cs t) g ∧ g =ᵐ[m] us t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (∫ t,(cs t:ℝ) ∂μ)) g ∧ g =ᵐ[m] ((∫ t,us t ∂μ) : Lp ℝ 2 m) := by
  apply exists_lipschitz_of_ball_averages
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let q (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hqi (x : X) := setDensity_integrable (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hqn (x : X) := setDensity_nonneg (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hqm (x : X) := setDensity_mass (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x) (hp x)
  have hqs (x : X) := setDensity_supported (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x) x (Subset.refl _)
  have heq (v : Lp ℝ 2 m) (x : X) : ⟪v,q x⟫_ℝ = (⨍ z in Metric.closedBall x r,v z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  let w := q x-q y
  have hpoint : ∀ᵐ t ∂μ,|⟪w,us t⟫_ℝ| ≤ (cs t:ℝ)*(2*r+dist x y) := by
    filter_upwards [hLip] with t ht
    obtain ⟨g,hg,he⟩ := ht
    have Hx := lipschitz_point_pairing_bound hg (us t) (q x) he (hqi x) (hqn x) (hqm x) x hr.le (hqs x)
    have Hy := lipschitz_point_pairing_bound hg (us t) (q y) he (hqi y) (hqn y) (hqm y) y hr.le (hqs y)
    have Hxy := hg.dist_le_mul x y
    rw [Real.dist_eq] at Hxy
    rw [real_inner_comm,show w=q x-q y from rfl,inner_sub_right]
    have H1 := abs_sub_le ⟪us t,q x⟫_ℝ (g x) ⟪us t,q y⟫_ℝ
    have H2 := abs_sub_le (g x) (g y) ⟪us t,q y⟫_ℝ
    rw [abs_sub_comm ⟪us t,q x⟫_ℝ (g x)] at H1
    nlinarith only [H1,H2,Hx,Hy,Hxy]
  have hi : Integrable (fun t => ⟪w,us t⟫_ℝ) μ := (innerSL ℝ w).integrable_comp hu
  have HB : |∫ t,⟪w,us t⟫_ℝ ∂μ| ≤ (∫ t,(cs t:ℝ) ∂μ)*(2*r+dist x y) := by
    calc
      _ ≤ ∫ t,|⟪w,us t⟫_ℝ| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ t,(cs t:ℝ)*(2*r+dist x y) ∂μ := integral_mono_ae hi.norm (hc.mul_const _) hpoint
      _ = _ := integral_mul_const _ _
  have HH := (innerSL ℝ w).integral_comp_comm hu
  change (∫ t,⟪w,us t⟫_ℝ ∂μ) = ⟪w,(∫ t,us t ∂μ)⟫_ℝ at HH
  rw [HH] at HB
  change |⟪w,(∫ t,us t ∂μ)⟫_ℝ| ≤ _ at HB
  rw [real_inner_comm,show w=q x-q y from rfl,inner_sub_right,heq _ x,heq _ y] at HB
  simpa only [Real.coe_toNNReal _ (integral_nonneg fun t => (cs t).coe_nonneg)] using HB
end WeakHessian

end
end InlinedFile144

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatIntegralSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile146
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_integral_bounded_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {b : ℝ} (hb : 0 < b) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (2*B*Real.exp (|K| *b)*Real.sqrt b)) g ∧
      g =ᵐ[m] ((∫ s in (0:ℝ)..b,cheegerHeat h s u) : Lp ℝ 2 m) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  let cs (s : ℝ) := Real.toNNReal (B*Real.exp (|K| *b)/Real.sqrt s)
  have hcs (s : ℝ) : (cs s:ℝ) = (B*Real.exp (|K| *b))*(Real.sqrt s)⁻¹ := by
    rw [show (cs s:ℝ)=↑(Real.toNNReal (B*Real.exp (|K| *b)/Real.sqrt s)) from rfl,
      Real.coe_toNNReal _ (by positivity),div_eq_mul_inv]
  have hci : Integrable (fun s => (cs s:ℝ)) (volume.restrict (Ioc 0 b)) := by
    simp_rw [hcs]
    exact (integrableOn_inv_sqrt hb.le).const_mul _
  have hui : Integrable (fun s => cheegerHeat h s u) (volume.restrict (Ioc 0 b)) :=
    ((cheegerHeat_continuousOn hfin h u).mono (by rw [uIcc_of_le hb.le]; exact Icc_subset_Ici_self)).intervalIntegrable.1
  have hLip : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) b),∃ g : X → ℝ,LipschitzWith (cs s) g ∧ g =ᵐ[m] cheegerHeat h s u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    obtain ⟨g,hg,he⟩ := hrcd.cheegerHeat_bounded_lipschitz hN hfull hfin h o u hB hu hs.1
    refine ⟨g,hg.weaken ?_,he⟩
    apply Real.toNNReal_mono
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg K))) hB) (Real.sqrt_nonneg _)
  obtain ⟨g,hg,he⟩ := exists_lipschitz_integral hfull hfin hui hci hLip
  have hi : (∫ s in Ioc (0:ℝ) b,(cs s:ℝ)) = 2*B*Real.exp (|K| *b)*Real.sqrt b := by
    simp_rw [hcs]
    rw [integral_const_mul,integral_inv_sqrt hb.le]
    ring
  rw [hi] at hg
  refine ⟨g,hg,?_⟩
  rwa [intervalIntegral.integral_of_le hb.le]
end WeakHessian

end
end InlinedFile146

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_ResolventSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile147
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheeger_scaled_resolvent_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {τ : ℝ} (hτ : 0 < τ) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (5*B*Real.exp (|K| *τ)/Real.sqrt τ)) g ∧
      g =ᵐ[m] ((cheeger_closedQuadraticEnergy h).scale hτ).resolvent u := by
  let Q := cheeger_closedQuadraticEnergy h
  let z := (Q.scale hτ).resolvent u
  let A := τ⁻¹ • (z-u)
  have hz : Q.IsFormGenerator z A := (Q.scaled_resolvent_iff hτ u z).mp rfl
  have hzb : ∀ᵐ x ∂m,|z x| ≤ B := cheeger_scaled_resolvent_bounded h hτ hB u hu
  have hAb : ∀ᵐ x ∂m,|A x| ≤ 2*B/τ := by
    filter_upwards [hzb,hu,Lp.coeFn_sub z u,Lp.coeFn_smul τ⁻¹ (z-u)] with x hx hy hs hm
    rw [show A x=τ⁻¹*(z-u) x from hm,hs,abs_mul,abs_inv,abs_of_pos hτ]
    calc
      _ ≤ τ⁻¹*(|z x|+|u x|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (inv_nonneg.mpr hτ.le)
      _ ≤ τ⁻¹*(B+B) := mul_le_mul_of_nonneg_left (add_le_add hx hy) (inv_nonneg.mpr hτ.le)
      _ = _ := by ring
  obtain ⟨p,hp,hep⟩ := hrcd.cheegerHeat_bounded_lipschitz hN hfull hfin h o z hB hzb hτ
  obtain ⟨q,hq,heq⟩ := hrcd.cheegerHeat_integral_bounded_lipschitz hN hfull hfin h o A
    (by positivity : 0 ≤ 2*B/τ) hAb hτ
  have hi := cheegerHeat_integral_generator hfin h hz hτ.le
  have he : (fun x => p x-q x) =ᵐ[m] z := by
    filter_upwards [hep,heq,Lp.coeFn_sub (cheegerHeat h τ z) z] with x hx hy hs
    rw [hx,hy,hi,hs]
    change cheegerHeat h τ z x - (cheegerHeat h τ z x - z x) = z x
    ring
  refine ⟨fun x => p x-q x,?_,he⟩
  apply (hp.sub hq).weaken
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add,Real.coe_toNNReal _ (by positivity : 0 ≤ B*Real.exp (|K| *τ)/Real.sqrt τ),
    Real.coe_toNNReal _ (by positivity : 0 ≤ 2*(2*B/τ)*Real.exp (|K| *τ)*Real.sqrt τ),
    Real.coe_toNNReal _ (by positivity : 0 ≤ 5*B*Real.exp (|K| *τ)/Real.sqrt τ)]
  have hs := Real.sq_sqrt hτ.le
  have hsp := Real.sqrt_pos.mpr hτ
  apply le_of_eq
  field_simp
  nlinarith [hs]

end WeakHessian

end
end InlinedFile147

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GlobalTestCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile156
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.resolvent_compactLip_test {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (u : Lp ℝ 2 m) (hu : u ∈ compactLipLp m) :
    ∃ g : X → ℝ,IsTestFunction m g ∧
      g =ᵐ[m] ((cheeger_closedQuadraticEnergy hrcd.2).scale zero_lt_one).resolvent u := by
  obtain ⟨f,⟨L,hf⟩,hfc,hfe⟩ := hu
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg (f o)).trans (hB (f o) ⟨o,rfl⟩)
  have hub : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hfe] with x hx
    rw [← hx]
    simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let r := (Q.scale zero_lt_one).resolvent u
  obtain ⟨g,hg,hge⟩ := hrcd.cheeger_scaled_resolvent_lipschitz hN hfull hfin hrcd.2 o u hB0 hub zero_lt_one
  have hgen : Q.IsFormGenerator r (r-u) := by
    simpa only [inv_one,one_smul] using (Q.scaled_resolvent_iff zero_lt_one u r).mp rfl
  have hlap := hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 r (r-u) hgen
  have hgs : IsLaplacian m g (r-u : Lp ℝ 2 m) := hlap.congr_ae hge.symm EventuallyEq.rfl
  have hsu : Sobolev m u := (sobolev_congr_ae hfe).mp (sobolev_of_lipschitz_compactSupport hfin hf hfc)
  have hAs : Sobolev m (r-u : Lp ℝ 2 m) :=
    (sobolev_congr_ae (Lp.coeFn_sub r u).symm).mp (hlap.1.sub hfin hsu)
  have hgb : BoundedFunction g := by
    refine ⟨B,continuous_le_of_ae_le hfull hg.continuous.abs continuous_const ?_⟩
    filter_upwards [hge,cheeger_scaled_resolvent_bounded hrcd.2 zero_lt_one hB0 u hub] with x hx hb
    rwa [hx]
  exact ⟨g,⟨⟨(r-u : Lp ℝ 2 m),hgs⟩,hgb,⟨_,hg⟩,(sobolev_congr_ae (hgs.ae_laplacian hfin)).mpr hAs⟩,hge⟩

lemma RCD.original_test_graph_approx {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A) :
    ∃ gs : ℕ → X → ℝ,(∀ n,IsTestFunction m (gs n)) ∧
      ∃ us As : ℕ → Lp ℝ 2 m,(∀ n,gs n =ᵐ[m] us n) ∧
      (∀ n,laplacian m (gs n) =ᵐ[m] As n) ∧
      Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  obtain ⟨fs,hfs,hft⟩ := exists_compactLip_L2_approx hfin (u-A)
  let us (n : ℕ) := (Q.scale zero_lt_one).resolvent (fs n)
  let As (n : ℕ) := us n-fs n
  choose gs hgs hge using fun n => hrcd.resolvent_compactLip_test hN hfull hfin o (fs n) (hfs n)
  have hgen := hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A hu
  have heu : (Q.scale zero_lt_one).resolvent (u-A) = u := by
    apply (Q.scaled_resolvent_iff zero_lt_one (u-A) u).mpr
    simpa only [inv_one,one_smul,sub_sub_cancel] using hgen
  have hT : Tendsto us atTop (𝓝 u) := by
    have H := (Q.scale zero_lt_one).resolventLinear.continuous.tendsto (u-A) |>.comp hft
    change Tendsto (fun n => (Q.scale zero_lt_one).resolvent (fs n)) atTop (𝓝 ((Q.scale zero_lt_one).resolvent (u-A))) at H
    rw [heu] at H
    exact H
  refine ⟨gs,hgs,us,As,hge,?_,hT,?_⟩
  · intro n
    have hG : Q.IsFormGenerator (us n) (As n) := by
      simpa only [inv_one,one_smul] using (Q.scaled_resolvent_iff zero_lt_one (fs n) (us n)).mp rfl
    have hL := hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 (us n) (As n) hG
    exact (hL.congr_ae (hge n).symm EventuallyEq.rfl).ae_laplacian hfin
  · simpa only [sub_sub_cancel] using hT.sub hft
end WeakHessian

end
end InlinedFile156

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_FormCoreDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile162
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.form_linear_zero_of_graph_core
    (hd : hQ.domain.topologicalClosure = ⊤) (S : E → E → Prop)
    (hS : ∀ u A,S u A → hQ.IsFormGenerator u A)
    (hcore : ∀ u A,hQ.IsFormGenerator u A → ∃ us As : ℕ → E,
      (∀ n,S (us n) (As n)) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A))
    (F : hQ.domain →ₗ[ℝ] ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ u,|F u| ≤ C*(‖(u:E)‖+Real.sqrt (hQ.realEnergy u)))
    (hz : ∀ u A,(hs : S u A) → F ⟨u,(hS u A hs).1⟩ = 0) : ∀ u,F u = 0 := by
  have hgen : ∀ u A,(hg : hQ.IsFormGenerator u A) → F ⟨u,hg.1⟩=0 := by
    intro u A hg
    obtain ⟨us,As,hs,hu,hA⟩ := hcore u A hg
    let vs (n : ℕ) : hQ.domain := ⟨us n,(hS _ _ (hs n)).1⟩
    let v : hQ.domain := ⟨u,hg.1⟩
    have he : Tendsto (fun n => hQ.realEnergy (vs n-v)) atTop (𝓝 0) := by
      have HE (n : ℕ) : hQ.realEnergy (vs n-v) = -⟪As n-A,us n-u⟫_ℝ/2 := by
        have H := hQ.formGenerator_energy (hQ.formGenerator_sub (hS _ _ (hs n)) hg)
        change 2*hQ.realEnergy (vs n-v) = _ at H
        linarith only [H]
      simp_rw [HE]
      simpa only [sub_self,inner_zero_right,neg_zero,zero_div] using ((hA.sub_const A).inner (𝕜 := ℝ) (hu.sub_const u)).neg.div_const 2
    have hn : Tendsto (fun n => ‖((vs n-v : hQ.domain):E)‖) atTop (𝓝 0) := by
      change Tendsto (fun n => ‖us n-u‖) atTop (𝓝 0)
      simpa only [sub_self,norm_zero] using (hu.sub_const u).norm
    have ht := (hn.add he.sqrt).const_mul C
    simp only [Real.sqrt_zero,add_zero,mul_zero] at ht
    have hlim : Tendsto (fun n => F (vs n-v)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hb (vs n-v)) ht
    have hzero (n : ℕ) : F (vs n-v) = -F v := by rw [map_sub,hz _ _ (hs n),zero_sub]
    simp_rw [hzero] at hlim
    exact neg_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hlim)
  intro v
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let us (n : ℕ) := (hQ.scale (ht n)).resolvent (v:E)
  let As (n : ℕ) := (t n)⁻¹ • (us n-(v:E))
  have hg (n : ℕ) : hQ.IsFormGenerator (us n) (As n) :=
    (hQ.scaled_resolvent_iff (ht n) (v:E) (us n)).mp rfl
  let vs (n : ℕ) : hQ.domain := ⟨us n,(hg n).1⟩
  have hu := hQ.scaled_resolvent_tendsto hd ht tendsto_one_div_add_atTop_nhds_zero_nat (v:E)
  have hE := (tendsto_const_nhds (x := hQ.realEnergy v)).sub
    (hQ.scaled_resolvent_energy_tendsto hd ht tendsto_one_div_add_atTop_nhds_zero_nat v)
  simp only [sub_self] at hE
  have he : Tendsto (fun n => hQ.realEnergy (v-vs n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hQ.realEnergy_quadratic.nonneg _) (fun n => hQ.scaled_resolvent_form_error_le v (ht n)) hE
  have hn : Tendsto (fun n => ‖((v-vs n : hQ.domain):E)‖) atTop (𝓝 0) := by
    change Tendsto (fun n => ‖(v:E)-us n‖) atTop (𝓝 0)
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x := (v:E))).sub hu).norm
  have hlim : Tendsto (fun n => F (v-vs n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hb (v-vs n))
    simpa only [Real.sqrt_zero,add_zero,mul_zero] using (hn.add he.sqrt).const_mul C
  have hzero (n : ℕ) : F (v-vs n) = F v := by rw [map_sub,hgen _ _ (hg n),sub_zero]
  simp_rw [hzero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim
end WeakHessianFunctional

end
end InlinedFile162

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_FormGamma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile163
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
variable {K N : ℝ} (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
variable (h : QuadraticCheegerEnergy m) (o : X) {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)

omit [SigmaFinite m] in
lemma CurvatureDimension.formGammaLp_ae (u : (cheeger_closedQuadraticEnergy h).domain) :
    hcd.formGammaLp hfin h o hχ u =ᵐ[m] gamma m χ (u : Lp ℝ 2 m) := by
  exact (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ
    (hcd.sobolev_formDomain hfin h o u)).coeFn_toLp

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.formDomain_gradient_norm_sq (u : (cheeger_closedQuadraticEnergy h).domain) :
    ‖(hcd.sobolev_formDomain hfin h o u).2.2.toLp (weakGradient m (u : Lp ℝ 2 m))‖^2 =
      2*(cheeger_closedQuadraticEnergy h).realEnergy u := by
  change _ = 2*(cheegerEnergy m ((u : Lp ℝ 2 m) : X → ℝ)).toReal
  rw [hcd.global_cheegerEnergy_toReal hfin o h (hcd.sobolev_formDomain hfin h o u),norm_toLp_sq_eq_integral]
  ring

omit [SigmaFinite m] in
lemma CurvatureDimension.formGammaLp_norm_le (u : (cheeger_closedQuadraticEnergy h).domain) :
    ‖hcd.formGammaLp hfin h o hχ u‖ ≤
      (2*(L:ℝ))*Real.sqrt ((cheeger_closedQuadraticEnergy h).realEnergy u) := by
  apply (norm_gamma_toLp_le hfin (hcd.global_localGradientParallelogram hfin o h) hχ
    (hcd.sobolev_formDomain hfin h o u)).trans
  have H := hcd.formDomain_gradient_norm_sq hfin h o u
  have Hs := Real.sq_sqrt ((cheeger_closedQuadraticEnergy h).realEnergy_quadratic.nonneg u)
  have hs := Real.sqrt_nonneg ((cheeger_closedQuadraticEnergy h).realEnergy u)
  have hn : ‖(hcd.sobolev_formDomain hfin h o u).2.2.toLp (weakGradient m (u : Lp ℝ 2 m))‖ ≤
      2*Real.sqrt ((cheeger_closedQuadraticEnergy h).realEnergy u) := by
    nlinarith only [H,Hs,hs,norm_nonneg ((hcd.sobolev_formDomain hfin h o u).2.2.toLp (weakGradient m (u : Lp ℝ 2 m)))]
  simpa only [mul_assoc,mul_left_comm (L:ℝ) 2] using mul_le_mul_of_nonneg_left hn L.coe_nonneg
end WeakHessian

end
end InlinedFile163

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactCoreForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile164
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_form_identity {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B)
    (v : (cheeger_closedQuadraticEnergy hrcd.2).domain) :
    (∫ x,gamma m (fun x => f x*χ x) (v : Lp ℝ 2 m) x ∂m) +
      ⟪f,boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) v -
        boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD v -
        (2:ℝ) • hrcd.1.formGammaLp hfin hrcd.2 o hχ.2.2.1.choose_spec v⟫_ℝ = 0 := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let L := hχ.2.2.1.choose
  let G := hrcd.1.formGammaLp hfin hrcd.2 o hχ.2.2.1.choose_spec
  have hs := hrcd.compact_core_localized_sobolev hN hfull hfin o f hof hχ hχc hD
  have hsM : Sobolev m (M f : X → ℝ) := (sobolev_congr_ae (boundedMulLp_ae _ (ae_of_all m hB) f)).mpr hs
  let U : Q.domain := ⟨M f,(hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp (M f))).mp hsM⟩
  let F : Q.domain →ₗ[ℝ] ℝ := {
    toFun := fun w => 2*Q.form U w+⟪f,M w-T w-(2:ℝ) • G w⟫_ℝ
    map_add' := by
      intro w z
      simp only [map_add,Submodule.coe_add,smul_add,inner_sub_right,inner_add_right,real_inner_smul_right]
      ring
    map_smul' := by
      intro c w
      simp only [map_smul,Submodule.coe_smul,smul_comm (2:ℝ) c,inner_sub_right,real_inner_smul_right,RingHom.id_apply,smul_eq_mul]
      ring }
  let C := 2*Real.sqrt (Q.realEnergy U)+‖f‖*(‖M‖+‖T‖+4*(L:ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ w,|F w| ≤ C*(‖(w : Lp ℝ 2 m)‖+Real.sqrt (Q.realEnergy w)) := by
    intro w
    have hQn := Q.realEnergy_quadratic.nonneg
    have hp : |Q.form U w| ≤ Real.sqrt (Q.realEnergy U)*Real.sqrt (Q.realEnergy w) := by
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
      rw [sq_abs,mul_pow,Real.sq_sqrt (hQn U),Real.sq_sqrt (hQn w)]
      exact Q.form_cauchySchwarz U w
    have hG := hrcd.1.formGammaLp_norm_le hfin hrcd.2 o hχ.2.2.1.choose_spec w
    have hn := (norm_sub_le (M w-T w) ((2:ℝ) • G w)).trans
      (add_le_add (norm_sub_le (M w) (T w)) le_rfl)
    norm_num only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hn
    have hR : ‖M w-T w-(2:ℝ) • G w‖ ≤ (‖M‖+‖T‖)*‖(w:Lp ℝ 2 m)‖+4*(L:ℝ)*Real.sqrt (Q.realEnergy w) := by
      nlinarith only [hn,M.le_opNorm (w:Lp ℝ 2 m),T.le_opNorm (w:Lp ℝ 2 m),hG]
    have hi := (abs_real_inner_le_norm f (M w-T w-(2:ℝ) • G w)).trans
      (mul_le_mul_of_nonneg_left hR (norm_nonneg f))
    have htri := abs_add_le (2*Q.form U w) ⟪f,M w-T w-(2:ℝ) • G w⟫_ℝ
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at htri
    change |2*Q.form U w+⟪f,M w-T w-(2:ℝ) • G w⟫_ℝ| ≤ _
    dsimp [C]
    nlinarith only [htri,hi,hp,
      mul_nonneg (Real.sqrt_nonneg (Q.realEnergy U)) (norm_nonneg (w:Lp ℝ 2 m)),
      mul_nonneg (mul_nonneg (norm_nonneg f) (add_nonneg (norm_nonneg M) (norm_nonneg T))) (Real.sqrt_nonneg (Q.realEnergy w)),
      mul_nonneg (mul_nonneg (norm_nonneg f) L.coe_nonneg) (norm_nonneg (w:Lp ℝ 2 m))]
  let S (u A : Lp ℝ 2 m) := ∃ g,IsTestFunction m g ∧ g =ᵐ[m] u ∧ laplacian m g =ᵐ[m] A
  have hS : ∀ u A,S u A → Q.IsFormGenerator u A := by
    intro u A ⟨g,hg,hgu,hgA⟩
    exact hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A
      ((laplacian_isLaplacian hg.1).congr_ae hgu hgA)
  have hd : ∀ u A,Q.IsFormGenerator u A → ∃ us As : ℕ → Lp ℝ 2 m,
      (∀ n,S (us n) (As n)) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
    intro u A hgen
    obtain ⟨gs,hgs,us,As,hgu,hgA,hu,hA⟩ := hrcd.original_test_graph_approx hN hfull hfin o
      (hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 u A hgen)
    exact ⟨us,As,fun n => ⟨gs n,hgs n,hgu n,hgA n⟩,hu,hA⟩
  have hz : ∀ u A,(hs : S u A) → F ⟨u,(hS u A hs).1⟩ = 0 := by
    intro u A hh
    obtain ⟨g,hg,hgu,hgA⟩ := hh
    let w : Q.domain := ⟨u,(hS u A ⟨g,hg,hgu,hgA⟩).1⟩
    have hprod := hrcd.compact_core_product_identity hN hfull hfin o f hof hχ hχc hD hB g hg u A hgu hgA
    let Gg := (memLp_gamma_of_lipschitz hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
      hχ.2.2.1.choose_spec (laplacian_isLaplacian hg.1).1).toLp (gamma m χ g)
    have hGe : Gg = G w := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans ((gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl hgu).trans
        (hrcd.1.formGammaLp_ae hfin hrcd.2 o hχ.2.2.1.choose_spec w).symm)
    change ⟪M f,A⟫_ℝ = ⟪f,M u-T u-(2:ℝ) • Gg⟫_ℝ at hprod
    rw [hGe] at hprod
    have hform := (hS u A ⟨g,hg,hgu,hgA⟩).2 U
    rw [Q.form_comm,real_inner_comm] at hform
    change 2*Q.form U w = -⟪M f,A⟫_ℝ at hform
    change 2*Q.form U w+⟪f,M u-T u-(2:ℝ) • G w⟫_ℝ = 0
    linarith only [hprod,hform]
  have hzero := Q.form_linear_zero_of_graph_core (cheeger_domain_dense hrcd.2) S hS hd F hC hb hz v
  have hgamma : (∫ x,gamma m (fun x => f x*χ x) (v : Lp ℝ 2 m) x ∂m) = 2*Q.form U v := by
    rw [← hrcd.1.global_integral_gamma_form hfin o hrcd.2 U v]
    apply integral_congr_ae
    exact gamma_congr_ae (boundedMulLp_ae _ (ae_of_all m hB) f).symm EventuallyEq.rfl
  rw [hgamma]
  exact hzero
end WeakHessian

end
end InlinedFile164

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LaplacianLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile165
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_zero_of_const_on_support (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {χ v η : X → ℝ} (hχ : LocalSobolev m χ) (hv : LocalSobolev m v)
    (hη : Measurable η) {c : ℝ} (hc : ∀ x,η x ≠ 0 → χ x=c)
    (hv0 : ∀ x,η x=0 → v x=0) : gamma m χ v =ᵐ[m] 0 := by
  have hS : MeasurableSet (Function.support η) := measurableSet_support hη
  have h1 := gamma_zero_on_const_set hfin hpar hχ hv hS (ae_of_all _ hc)
  have h2 := gamma_zero_off_set hfin hpar hv hχ hS (ae_of_all _ fun x hx => hv0 x (not_not.mp hx))
  filter_upwards [h1,h2,gamma_comm (m := m) χ v] with x ha hb he
  by_cases hx : η x=0
  · rw [he,hb (by simpa only [Function.mem_support,not_not] using hx)]
    rfl
  · exact ha hx

lemma IsTestFunction.laplacian_mul_eq_zero_on_plateau
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {χ η : X → ℝ} (hχ : IsTestFunction m χ) {L : ℝ≥0} (hη : LipschitzWith L η)
    (hη1 : ∀ x,|η x| ≤ 1) {c : ℝ} (hc : ∀ x,η x ≠ 0 → χ x=c) :
    (fun x => laplacian m χ x*η x) =ᵐ[m] 0 := by
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hηB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hηD : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  let A := laplacian m χ
  have hu : Sobolev m (fun x => A x*(η x*η x)) :=
    hχ.2.2.2.mul_bounded hfin (localSobolev_of_lipschitz hfin hηsq) hηB hηD
  have hz : gamma m χ (fun x => A x*(η x*η x)) =ᵐ[m] 0 :=
    gamma_zero_of_const_on_support hfin hpar (laplacian_isLaplacian hχ.1).1.2.1 hu.2.1 hη.continuous.measurable hc
      (fun x hx => by rw [hx]; ring)
  have HH := (laplacian_isLaplacian hχ.1).2.2 (fun x => A x*(η x*η x)) hu
  rw [integral_congr_ae hz] at HH
  simp only [Pi.zero_apply,integral_zero] at HH
  have hAη : MemLp (fun x => A x*η x) 2 m :=
    memLp_mul_bounded (laplacian_isLaplacian hχ.1).2.1 hη.continuous.aestronglyMeasurable (ae_of_all _ hη1)
  have he : (∫ x,(A x*η x)^2 ∂m) = 0 := by
    have HH' : (∫ x,A x*(A x*(η x*η x)) ∂m) = 0 := by linarith only [HH]
    convert HH' using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (A x*η x)) (hAη.integrable_sq)).mp he
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp hx
end WeakHessian

end
end InlinedFile165

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactCoreEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile167
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_weak_equation_oai {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ η : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {L : ℝ≥0} (hη : LipschitzWith L η) (hη1 : ∀ x,|η x| ≤ 1)
    (hc : ∀ x,η x ≠ 0 → χ x = 1) :
    (∫ x,gamma m (fun y => f y*χ y) (fun y => (f y*χ y)*(η y*η y)) x ∂m) +
      (∫ x,((f x*χ x)*η x)^2 ∂m) = 0 := by
  let w := fun x => f x*χ x
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hw : Sobolev m w := hrcd.compact_core_localized_sobolev hN hfull hfin o f hof hχ hχc hD
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hDs : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  have hv : Sobolev m (fun x => w x*(η x*η x)) :=
    hw.mul_bounded hfin (localSobolev_of_lipschitz hfin hηsq) hB hDs
  let v := hv.1.toLp (fun x => w x*(η x*η x))
  have hve : (v : X → ℝ) =ᵐ[m] (fun x => w x*(η x*η x)) := hv.1.coeFn_toLp
  let V : (cheeger_closedQuadraticEnergy hrcd.2).domain := ⟨v,
    (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp v)).mp ((sobolev_congr_ae hve).mpr hv)⟩
  obtain ⟨Bχ,hBχ⟩ := hχ.2.1
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hBχ)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let G := hrcd.1.formGammaLp hfin hrcd.2 o hχ.2.2.1.choose_spec
  have hT : T v = 0 := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae _ hD v,hve,
      hχ.laplacian_mul_eq_zero_on_plateau hfin hpar hη hη1 hc,Lp.coeFn_zero ℝ 2 m] with x ht hvx hl hz
    change (T v) x = v x*laplacian m χ x at ht
    rw [ht,hvx,hz]
    change w x*(η x*η x)*laplacian m χ x = 0
    calc
      _ = w x*η x*(laplacian m χ x*η x) := by ring
      _ = 0 := by rw [hl]; simp only [Pi.zero_apply,mul_zero]
  have hg0 : gamma m χ (fun x => w x*(η x*η x)) =ᵐ[m] 0 :=
    gamma_zero_of_const_on_support hfin hpar (laplacian_isLaplacian hχ.1).1.2.1 hv.2.1
      hη.continuous.measurable hc (fun x hx => by rw [hx]; ring)
  have hG : G V = 0 := by
    apply Lp.ext
    exact (hrcd.1.formGammaLp_ae hfin hrcd.2 o hχ.2.2.1.choose_spec V).trans
      ((gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl hve).trans (hg0.trans (Lp.coeFn_zero ℝ 2 m).symm))
  have H := hrcd.compact_core_form_identity hN hfull hfin o f hof hχ hχc hD hBχ V
  change (∫ x,gamma m w (v : X → ℝ) x ∂m)+⟪f,M v-T v-(2:ℝ) • G V⟫_ℝ = 0 at H
  rw [hT,hG,smul_zero,sub_zero,sub_zero] at H
  have hg : (∫ x,gamma m w (v : X → ℝ) x ∂m) =
      ∫ x,gamma m w (fun y => w y*(η y*η y)) x ∂m :=
    integral_congr_ae (gamma_congr_ae (m := m) (f := w) EventuallyEq.rfl hve)
  have hi : ⟪f,M v⟫_ℝ = ∫ x,(w x*η x)^2 ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae _ (ae_of_all m hBχ) v,hve] with x hm hvx
    change (M v) x = v x*χ x at hm
    simp only [RCLike.inner_apply,conj_trivial,hm,hvx]
    dsimp [w]
    by_cases he : η x=0
    · rw [he]; ring
    · rw [hc x he]; ring
  rw [hg,hi] at H
  exact H
end WeakHessian

end
end InlinedFile167

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.compact_core_weak_equation_oai.{u_1} := @OAI.WeakHessian.RCD.compact_core_weak_equation_oai.{u_1}
