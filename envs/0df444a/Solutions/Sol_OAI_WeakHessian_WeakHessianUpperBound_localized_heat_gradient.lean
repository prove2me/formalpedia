-- Prove2me | solution 1 for OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:15:52.217696+00:00
-- url     : https://prove2.me/submissions/98c34513-80d2-483c-8f28-fb38e2909c2a

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_boundedLipschitzRepresentative
import Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_curvature_continuousOn
import Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_gamma_continuousOn
import Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_gamma_memLp
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_heatBridge_bounds
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_rcd_weighted_BE

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

lemma ClosedQuadraticEnergy.resolvent_norm_le_one : ‖hQ.resolventLinear‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖hQ.resolvent u‖ ≤ 1*‖u‖
  simpa [hQ.resolvent_zero] using hQ.resolvent_nonexpansive u 0

lemma ClosedQuadraticEnergy.formGenerator_unique (hd : hQ.domain.topologicalClosure = ⊤)
    {u A B : E} (hA : hQ.IsFormGenerator u A) (hB : hQ.IsFormGenerator u B) : A = B := by
  have he : hQ.resolvent (u-A) = hQ.resolvent (u-B) :=
    ((hQ.isFormGenerator_iff _ _).mp hA).trans ((hQ.isFormGenerator_iff _ _).mp hB).symm
  exact (sub_right_inj).mp (hQ.resolvent_injective hd he)

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
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_InlinedFile0
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
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

theorem weakGradient_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f : X → ℝ) :
    weakGradient m f =ᵐ[m] weakGradient (exponentialMeasure m V) f := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact weakGradient_eq_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f

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

lemma ClosedQuadraticEnergy.exists_formGenerator_approx
    (hd : hQ.domain.topologicalClosure = ⊤) (v : hQ.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ u A : E, hQ.IsFormGenerator u A ∧ (Q ((v:E)-u)).toReal < ε := by
  let t : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hl : Tendsto t atTop (𝓝 0) := by
    simpa only [t,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have H := (tendsto_const_nhds (x := hQ.realEnergy v)).sub (hQ.scaled_resolvent_energy_tendsto hd ht hl v)
  simp only [sub_self] at H
  obtain ⟨n,hn⟩ := (H.eventually_lt_const hε).exists
  refine ⟨(hQ.scale (ht n)).resolvent v,(t n)⁻¹ • ((hQ.scale (ht n)).resolvent v-v),
    (hQ.scaled_resolvent_iff (ht n) v _).mp rfl,?_⟩
  exact (hQ.scaled_resolvent_form_error_le v (ht n)).trans_lt hn

lemma ClosedQuadraticEnergy.form_tendsto_zero_of_bounded_energy
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (hu : Tendsto (fun i => (us i:E)) l (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M) (v : hQ.domain) :
    Tendsto (fun i => hQ.form (us i) v) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r,A,hg,hr⟩ := hQ.exists_formGenerator_approx hd v
    (show 0 < (ε/2)^2/(M+1) by positivity)
  let r' : hQ.domain := ⟨r,hg.1⟩
  have hrem (i : ι) : |hQ.form (us i) (v-r')| < ε/2 := by
    have H := hQ.form_cauchySchwarz (us i) (v-r')
    have hener : hQ.realEnergy (v-r') < (ε/2)^2/(M+1) := hr
    have hn := hQ.realEnergy_quadratic.nonneg (v-r')
    have H' := mul_le_mul_of_nonneg_right (hbound i) hn
    have hp : (M+1)*hQ.realEnergy (v-r') < (ε/2)^2 := by
      have hh := (lt_div_iff₀ (by linarith : (0:ℝ) < M+1)).mp hener
      nlinarith
    rw [abs_lt]
    constructor <;> nlinarith
  have he (i : ι) : hQ.form (us i) r' = -⟪A,(us i:E)⟫_ℝ/2 := by
    rw [hQ.form_comm]
    have H := hg.2 (us i)
    change 2*hQ.form r' (us i) = _ at H
    linarith
  have Hinner : Tendsto (fun i => hQ.form (us i) r') l (𝓝 0) := by
    simp_rw [he]
    simpa using ((tendsto_const_nhds (x := A)).inner (𝕜 := ℝ) hu).neg.div_const 2
  have Habs := Hinner.norm
  simp only [norm_zero,Real.norm_eq_abs] at Habs
  filter_upwards [Habs.eventually_lt_const (half_pos hε)] with i hi
  have H : hQ.form (us i) v = hQ.form (us i) (v-r')+hQ.form (us i) r' := by rw [map_sub]; ring
  rw [Real.dist_eq,sub_zero,H]
  exact (abs_add_le _ _).trans_lt (by linarith [hrem i])

lemma ClosedQuadraticEnergy.form_tendsto_of_bounded_energy
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (u v : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M) :
    Tendsto (fun i => hQ.form (us i) v) l (𝓝 (hQ.form u v)) := by
  have hsub : Tendsto (fun i => ((us i-u : hQ.domain):E)) l (𝓝 0) := by simpa using hu.sub_const (u:E)
  have he (i : ι) : hQ.realEnergy (us i-u) ≤ 2*M+2*hQ.realEnergy u := by
    have H := hQ.realEnergy_quadratic.parallelogram (us i) u
    have hn := hQ.realEnergy_quadratic.nonneg (us i+u)
    linarith [hbound i]
  have H := hQ.form_tendsto_zero_of_bounded_energy hd (fun i => us i-u) hsub
    (show 0 ≤ 2*M+2*hQ.realEnergy u from by have h := hQ.realEnergy_quadratic.nonneg u; positivity) he v
  simp only [map_sub,LinearMap.sub_apply] at H
  simpa using H.add_const (hQ.form u v)

lemma ClosedQuadraticEnergy.form_energy_sub_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    (us : ι → hQ.domain) (u : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, hQ.realEnergy (us i) ≤ M)
    (hener : Tendsto (fun i => hQ.realEnergy (us i)) l (𝓝 (hQ.realEnergy u))) :
    Tendsto (fun i => hQ.realEnergy (us i-u)) l (𝓝 0) := by
  have hf := hQ.form_tendsto_of_bounded_energy hd us u u hu hM hbound
  rw [hQ.form_self] at hf
  have he (i : ι) : hQ.realEnergy (us i-u) =
      hQ.realEnergy (us i)+hQ.realEnergy u-2*hQ.form (us i) u := by
    rw [← hQ.form_self (us i-u)]
    simp only [map_sub,LinearMap.sub_apply,hQ.form_self,hQ.form_comm u (us i)]
    ring
  simp_rw [he]
  simpa only [two_mul, sub_self] using
    (hener.add_const (hQ.realEnergy u)).sub (hf.const_mul 2)

end WeakHessianFunctional

end
end InlinedFile13

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

omit [BorelSpace X] in
lemma FiniteOnBoundedSets.of_measure_le_smul (hm : FiniteOnBoundedSets m)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m) : FiniteOnBoundedSets ν := by
  intro B hB
  exact lt_of_le_of_lt (hν B) (by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hm B hB))

end WeakHessian

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
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyComparable
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

lemma cheegerEnergy_eq_of_comparable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] (hfinite : FiniteOnBoundedSets m)
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    cheegerEnergy ν (f : X → ℝ) =
      ENNReal.ofReal (‖Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D‖^2/2) := by
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 ν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν
  obtain ⟨fs,hLip,hfs,hDs,hf,hG⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  have hfn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hfs (Lp.memLp f)
    (by simpa only [Lp.toLp_coeFn] using hf)
  have hDn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hDs (Lp.memLp D)
    (by simpa only [Lp.toLp_coeFn] using hG)
  have hDf : ((Lp.memLp D).of_measure_le_smul ENNReal.coe_ne_top hν).toLp (D : X → ℝ) = T D := rfl
  rw [hDf] at hDn
  have he : Tendsto (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂ν) atTop (𝓝 (ENNReal.ofReal (‖T D‖^2/2))) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hDn.norm.pow 2).div_const 2)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact half_lintegral_localSlope_eq (hLip n).choose_spec
      ((hDs n).of_measure_le_smul ENNReal.coe_ne_top hν)
  have hle : cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖T D‖^2/2) := by
    have H := cheegerEnergy_le_liminf
      ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
      (fun n => ⟨hLip n,(hfs n).of_measure_le_smul ENNReal.coe_ne_top hν⟩)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
        (fun n => (hfs n).of_measure_le_smul ENNReal.coe_ne_top hν)
        (f : X → ℝ) ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)).mp hfn)
    rwa [he.liminf_eq] at H
  have hDν : IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (T D) :=
    (hD.change_measure hm hν).congr_ae Filter.EventuallyEq.rfl
      (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D).symm
  obtain ⟨D',hD',hlo⟩ := exists_minimalGradient_energy_le_cheeger
    (hfinite.of_measure_le_smul ENNReal.coe_ne_top hν)
    ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
    (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have heq : D' = T D := Lp.ext (hD'.ae_eq hDν)
  rw [heq] at hlo
  exact le_antisymm hle hlo

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevCheegerEnergyTop
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
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

lemma cheegerEnergy_integral_of_comparable (hfinite : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy ν f = ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂ν)/2) := by
  let f' := hf.1.toLp f
  let D' := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (f' : X → ℝ) (D' : X → ℝ) :=
    (weakGradient_isMinimal hf.2.1.2).congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (f' : X → ℝ) = ENNReal.ofReal (‖D'‖^2/2) := by
    rw [cheegerEnergy_congr_ae hf.1.coeFn_toLp,hID f hf,norm_toLp_sq_eq_integral]
  have H := cheegerEnergy_eq_of_comparable hfinite hm hν hD he
  have ha : (f' : X → ℝ) =ᵐ[ν] f := (Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.1.coeFn_toLp
  rw [cheegerEnergy_congr_ae ha] at H
  rw [H]
  congr 2
  let Dν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D'
  have heq : Dν = (hf.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).toLp (weakGradient m f) :=
    changeLp_toLp ENNReal.coe_ne_top hν hf.2.2
  change ‖Dν‖^2 = _
  rw [heq,norm_toLp_sq_eq_integral]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EnergyIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile182
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable (hfin : FiniteOnBoundedSets m)
variable (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
  ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))

include hfin hID

lemma identified_formGenerator_of_isLaplacian (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : IsLaplacian m (u : X → ℝ) A) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator u A := by
  have huf := (identified_sobolev_iff_energy hfin hID).mp hu.1
  refine ⟨huf,fun v => ?_⟩
  rw [← identified_integral_gamma_form hfin hID h ⟨u,huf⟩ v]
  have hv := (identified_sobolev_iff_energy hfin hID).mpr v.property
  rw [hu.2.2 v.val hv,L2.inner_def]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm (A x) (v.val x))

end WeakHessian

end
end InlinedFile182

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

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerScaledResolventNonneg
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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {m : Measure X}
lemma cheeger_scaled_resolvent_nonneg (h : QuadraticCheegerEnergy m)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x) :
    ∀ᵐ x ∂m,0 ≤ ((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u x := by
  let η : ℝ → ℝ := fun r => max r 0
  have hη : LipschitzWith 1 η := lipschitzWith_posPart
  have hη0 : η 0 = 0 := max_self _
  have hufix : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u,hu] with x hx hu
    simpa only [Function.comp_apply,η,max_eq_left hu] using hx
  have hQη (f : Lp ℝ 2 m) :
      cheegerEnergy m (hη.compLp hη0 f : X → ℝ) ≤ cheegerEnergy m (f : X → ℝ) := by
    rw [cheegerEnergy_congr_ae (hη.coeFn_compLp hη0 f)]
    exact cheegerEnergy_normalContraction hη hη0 f
  have hfix := ((cheeger_closedQuadraticEnergy h).scale ht).resolvent_normal_fixed m hη hη0
    (fun f => by gcongr; exact hQη f) u hufix
  filter_upwards [hη.coeFn_compLp hη0 (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u)] with x hx
  rw [hfix] at hx
  change ((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x =
    max (((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x) 0 at hx
  change 0 ≤ ((cheeger_closedQuadraticEnergy h).scale ht).resolvent u x
  rw [hx]
  exact le_max_right _ _

end WeakHessian

end
end InlinedFile0

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

end WeakHessian

end
end InlinedFile96

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

end WeakHessian

end
end InlinedFile99

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_VariableDissipationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma abs_integral_bounded_gamma_self_le_energy
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {u q : X → ℝ} (hu : Sobolev m u)
    (hqm : AEStronglyMeasurable q m) {B : ℝ} (hqb : ∀ᵐ x ∂m, |q x| ≤ B) :
    |∫ x, q x * gamma m u u x ∂m| ≤ B * (2 * (cheegerEnergy m u).toReal) := by
  have hi := integrable_bounded_gamma hfin hu hu hqm hqb
  have hD : Integrable (fun x => (weakGradient m u x)^2) m := hu.2.2.integrable_sq
  calc
    _ ≤ ∫ x, |q x * gamma m u u x| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * (weakGradient m u x)^2 ∂m := by
      apply integral_mono_ae hi.abs (hD.const_mul B)
      filter_upwards [hqb, gamma_self (m := m) u] with x hx hΓ
      rw [hΓ, abs_mul, abs_of_nonneg (sq_nonneg (weakGradient m u x))]
      exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    _ = _ := by rw [integral_const_mul, identified_cheegerEnergy_toReal hID hu]; ring

omit [SigmaFinite m] in
lemma abs_weighted_heat_gamma_le
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m, |ξ x| ≤ Cξ)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m)
    {B : ℝ} (hB : 0 ≤ B) (hkb : ∀ᵐ x ∂m, |k x| ≤ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |∫ x, (cheegerHeat h s ξ x * k x) *
      gamma m (cheegerHeat h t f) (cheegerHeat h t f) x ∂m| ≤
      (Cξ * B) * (2 * (cheegerEnergy m (f : X → ℝ)).toReal) := by
  have hfd := (identified_sobolev_iff_energy hfin hID).mp hf
  have hht := cheegerHeat_energy_le h ht f
  have hft : Sobolev m (cheegerHeat h t f) :=
    (identified_sobolev_iff_energy hfin hID).mpr (hht.trans_lt hfd)
  have hq : AEStronglyMeasurable (fun x => cheegerHeat h s ξ x * k x) m :=
    (Lp.memLp _).aestronglyMeasurable.mul hkm
  have hqb : ∀ᵐ x ∂m, |cheegerHeat h s ξ x * k x| ≤ Cξ * B := by
    filter_upwards [cheegerHeat_bounded h hs hCξ ξ hξb, hkb] with x hx hk
    rw [abs_mul]
    exact mul_le_mul hx hk (abs_nonneg _) hCξ
  exact (abs_integral_bounded_gamma_self_le_energy hfin hID hft hq hqb).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfd.ne hht) (by norm_num))
      (mul_nonneg hCξ hB))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_BoundedSecondGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile201
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

omit [MetricSpace X] in
lemma lp_scaled_sub_bounded {u v : Lp ℝ 2 m} {B C a : ℝ}
    (hu : ∀ᵐ x ∂m,|u x| ≤ B) (hv : ∀ᵐ x ∂m,|v x| ≤ C) :
    ∀ᵐ x ∂m,|(a • (u-v)) x| ≤ |a| *(B+C) := by
  filter_upwards [hu,hv,Lp.coeFn_smul a (u-v),Lp.coeFn_sub u v] with x hx hy hs hd
  rw [hs,Pi.smul_apply,smul_eq_mul,hd,Pi.sub_apply,abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hx hy)) (abs_nonneg _)

lemma cheeger_double_resolvent_core (h : QuadraticCheegerEnergy m)
    {t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (u : Lp ℝ 2 m)
    (hub : ∀ᵐ x ∂m,|u x| ≤ B) :
    ∃ v A AA : Lp ℝ 2 m,
      v = ((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear
        (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) ∧
      (cheeger_closedQuadraticEnergy h).IsFormGenerator v A ∧
      (cheeger_closedQuadraticEnergy h).IsFormGenerator A AA ∧
      (∀ᵐ x ∂m,|v x| ≤ B) ∧
      (∀ᵐ x ∂m,|A x| ≤ |t⁻¹| *(B+B)) ∧
      (∀ᵐ x ∂m,|AA x| ≤ |t⁻¹| *(|t⁻¹| *(B+B)+|t⁻¹| *(B+B))) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := (Q.scale ht).resolventLinear
  let v := R (R u)
  let A := t⁻¹ • (v-R u)
  let Au := t⁻¹ • (R u-u)
  have hg : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht (R u) v).mp rfl
  have hu : Q.IsFormGenerator (R u) Au := (Q.scaled_resolvent_iff ht u (R u)).mp rfl
  have hA : Q.IsFormGenerator A (t⁻¹ • (A-Au)) := Q.formGenerator_smul _ (Q.formGenerator_sub hg hu)
  have hb1 : ∀ᵐ x ∂m,|R u x| ≤ B := cheeger_scaled_resolvent_bounded h ht hB u hub
  have hb2 : ∀ᵐ x ∂m,|v x| ≤ B := cheeger_scaled_resolvent_bounded h ht hB (R u) hb1
  have hbA : ∀ᵐ x ∂m,|A x| ≤ |t⁻¹| *(B+B) := lp_scaled_sub_bounded hb2 hb1
  have hbAu : ∀ᵐ x ∂m,|Au x| ≤ |t⁻¹| *(B+B) := lp_scaled_sub_bounded hb1 hub
  exact ⟨v,A,t⁻¹ • (A-Au),rfl,hg,hA,hb2,hbA,lp_scaled_sub_bounded hbA hbAu⟩

lemma cheeger_double_resolvent_nonneg (h : QuadraticCheegerEnergy m)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x) :
    ∀ᵐ x ∂m,0 ≤ ((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear
      (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x :=
  cheeger_scaled_resolvent_nonneg h ht _ (cheeger_scaled_resolvent_nonneg h ht u hu)

variable [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable [IsLocallyFiniteMeasure m]

lemma cheeger_double_resolvent_tendsto (h : QuadraticCheegerEnergy m)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : ∀ i,0 < t i)
    (hl : Tendsto t l (𝓝 0)) (u : Lp ℝ 2 m) :
    Tendsto (fun i => ((cheeger_closedQuadraticEnergy h).scale (ht i)).resolventLinear
      (((cheeger_closedQuadraticEnergy h).scale (ht i)).resolventLinear u)) l (𝓝 u) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := fun i => (Q.scale (ht i)).resolventLinear
  have H : Tendsto (fun i => R i u) l (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) ht hl u
  have hb (i : ι) : ‖R i (R i u)-u‖ ≤ 2*‖R i u-u‖ := by
    calc
      _ ≤ ‖R i (R i u)-R i u‖+‖R i u-u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖R i (R i u-u)‖+‖R i u-u‖ := by rw [map_sub]
      _ ≤ ‖R i u-u‖+‖R i u-u‖ := by
        gcongr
        exact ((R i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right
          (Q.scale (ht i)).resolvent_norm_le_one (norm_nonneg _)).trans_eq (one_mul _))
      _ = _ := by ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [sub_self,norm_zero,mul_zero] using (H.sub_const u).norm.const_mul 2
end WeakHessian

end
end InlinedFile201

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_HessianMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma WeakHessianUpperBound.mono_bounded (hfin : FiniteOnBoundedSets m)
    {F G H : X → ℝ} (h : WeakHessianUpperBound m F G)
    (hGm : AEStronglyMeasurable G m) (hHm : AEStronglyMeasurable H m)
    {CG CH : ℝ} (hGb : ∀ x, |G x| ≤ CG) (hHb : ∀ x, |H x| ≤ CH)
    (hGH : ∀ x, G x ≤ H x) : WeakHessianUpperBound m F H := by
  intro g hg hgs φ hφ hφs hφn
  obtain ⟨L,hL⟩ := hg.1
  obtain ⟨Lφ,hLφ⟩ := hφ
  obtain ⟨B,hB⟩ := hφs.exists_bound_of_continuous hLφ.continuous
  have hφb (x : X) : |φ x| ≤ max B 0 := by
    exact (show |φ x| ≤ B by simpa only [Real.norm_eq_abs] using hB x).trans (le_max_left _ _)
  have hi (J : X → ℝ) (hJm : AEStronglyMeasurable J m) {C : ℝ}
      (hJb : ∀ x, |J x| ≤ C) : Integrable (fun x => φ x*J x*gamma m g g x) m := by
    apply integrable_bounded_gamma hfin hL.1 hL.1 (hLφ.continuous.aestronglyMeasurable.mul hJm)
      (C := max B 0*max C 0)
    exact ae_of_all _ fun x => by
      rw [Pi.mul_apply,abs_mul]
      exact mul_le_mul (hφb x) ((hJb x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  apply (h g hg hgs φ ⟨Lφ,hLφ⟩ hφs hφn).trans
  apply integral_mono_ae (hi G hGm hGb) (hi H hHm hHb)
  filter_upwards [gamma_self (m := m) g] with x hx
  rw [hx]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hGH x) (hφn x)) (sq_nonneg _)

lemma abs_max_le_of_abs_le {x B c : ℝ} (hx : |x| ≤ B) : |max x c| ≤ B+|c| := by
  apply abs_le.mpr
  constructor
  · have H := (abs_le.mp hx).1
    linarith [le_max_left x c,abs_nonneg c]
  · exact max_le (by linarith [(abs_le.mp hx).2,abs_nonneg c])
      (by linarith [le_abs_self c,(abs_nonneg x).trans hx])

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_ResolventGraphConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile203
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.formGenerator_scaled_resolvent {u A : E}
    (hu : hQ.IsFormGenerator u A) {t : ℝ} (ht : 0 < t) :
    hQ.IsFormGenerator ((hQ.scale ht).resolventLinear u) ((hQ.scale ht).resolventLinear A) := by
  let R := (hQ.scale ht).resolventLinear
  let B := t⁻¹ • (R u-u)
  have hB : hQ.IsFormGenerator (R u) B := (hQ.scaled_resolvent_iff ht u _).mp rfl
  have hBB : hQ.IsFormGenerator B (t⁻¹ • (B-A)) :=
    hQ.formGenerator_smul _ (hQ.formGenerator_sub hB hu)
  have he : R A = B := (hQ.scaled_resolvent_iff ht A B).mpr hBB
  rwa [he]
end WeakHessianFunctional
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [IsLocallyFiniteMeasure m]

lemma cheeger_double_resolvent_graph_tendsto (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : ∀ i,0 < t i)
    (hl : Tendsto t l (𝓝 0)) :
    let R := fun i => ((cheeger_closedQuadraticEnergy h).scale (ht i)).resolventLinear
    (∀ i,(cheeger_closedQuadraticEnergy h).IsFormGenerator (R i (R i u)) (R i (R i A))) ∧
      Tendsto (fun i => R i (R i u)) l (𝓝 u) ∧ Tendsto (fun i => R i (R i A)) l (𝓝 A) := by
  refine ⟨fun i => ?_,cheeger_double_resolvent_tendsto h ht hl u,
    cheeger_double_resolvent_tendsto h ht hl A⟩
  exact (cheeger_closedQuadraticEnergy h).formGenerator_scaled_resolvent
    ((cheeger_closedQuadraticEnergy h).formGenerator_scaled_resolvent hu (ht i)) (ht i)
end WeakHessian

end
end InlinedFile203

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
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TestProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile129
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma IsLaplacian.mul_lipschitz (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v B)
    {L M : ℝ≥0} (huL : LipschitzWith L u) (hvL : LipschitzWith M v)
    {C D : ℝ} (huB : ∀ x,|u x| ≤ C) (hvB : ∀ x,|v x| ≤ D) :
    IsLaplacian m (fun x => u x*v x)
      (fun x => A x*v x+B x*u x+2*gamma m u v x) := by
  have huD : ∀ᵐ x ∂m,|weakGradient m u x| ≤ L := by
    filter_upwards [weakGradient_nonneg (m := m) u,weakGradient_le_lipschitz hfin huL] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hvD : ∀ᵐ x ∂m,|weakGradient m v x| ≤ M := by
    filter_upwards [weakGradient_nonneg (m := m) v,weakGradient_le_lipschitz hfin hvL] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hAv := memLp_mul_bounded hu.2.1 hvL.continuous.aestronglyMeasurable (ae_of_all _ hvB)
  have hBu := memLp_mul_bounded hv.2.1 huL.continuous.aestronglyMeasurable (ae_of_all _ huB)
  have hgam := memLp_gamma_lipschitz hfin hpar hu.1 hvL
  refine ⟨hu.1.mul_bounded hfin hv.1.2.1 (ae_of_all _ hvB) hvD,(hAv.add hBu).add (hgam.const_mul 2),?_⟩
  intro w hw
  have h1 := hu.2.2 (fun x => w x*v x) (hw.mul_bounded hfin hv.1.2.1 (ae_of_all _ hvB) hvD)
  have h2 := hv.2.2 (fun x => w x*u x) (hw.mul_bounded hfin hu.1.2.1 (ae_of_all _ huB) huD)
  have hiu : Integrable (fun x => u x*gamma m v w x) m :=
    (integrable_gamma hfin hv.1 hw).bdd_mul huL.continuous.aestronglyMeasurable (ae_of_all _ huB)
  have hiv : Integrable (fun x => v x*gamma m u w x) m :=
    (integrable_gamma hfin hu.1 hw).bdd_mul hvL.continuous.aestronglyMeasurable (ae_of_all _ hvB)
  have hic : Integrable (fun x => gamma m u v x*w x) m := hgam.integrable_mul hw.1
  have hiA := hAv.integrable_mul hw.1
  have hiB := hBu.integrable_mul hw.1
  change Integrable (fun x => A x*v x*w x) m at hiA
  change Integrable (fun x => B x*u x*w x) m at hiB
  have he1 : (∫ x,gamma m u (fun y => w y*v y) x ∂m) =
      (∫ x,gamma m u v x*w x ∂m)+(∫ x,v x*gamma m u w x ∂m) := by
    rw [← integral_add hic hiv]
    apply integral_congr_ae
    filter_upwards [gamma_mul_left hfin hpar hw.2.1 hv.1.2.1 hu.1.2.1 (ae_of_all _ hvB) hvD,
      gamma_comm (m := m) u (fun y => w y*v y),gamma_comm (m := m) v u,gamma_comm (m := m) w u] with x hh h0 h3 h4
    rw [h0,hh,h3,h4]
    ring
  have he2 : (∫ x,gamma m v (fun y => w y*u y) x ∂m) =
      (∫ x,gamma m u v x*w x ∂m)+(∫ x,u x*gamma m v w x ∂m) := by
    rw [← integral_add hic hiu]
    apply integral_congr_ae
    filter_upwards [gamma_mul_left hfin hpar hw.2.1 hu.1.2.1 hv.1.2.1 (ae_of_all _ huB) huD,
      gamma_comm (m := m) v (fun y => w y*u y),gamma_comm (m := m) w v] with x hh h0 h3
    rw [h0,hh,h3]
    ring
  rw [he1] at h1
  rw [he2] at h2
  have hp : (∫ x,gamma m (fun y => u y*v y) w x ∂m) =
      (∫ x,u x*gamma m v w x ∂m)+(∫ x,v x*gamma m u w x ∂m) := by
    rw [← integral_add hiu hiv]
    exact integral_congr_ae (gamma_mul_left hfin hpar hu.1.2.1 hv.1.2.1 hw.2.1 (ae_of_all _ hvB) hvD)
  have hA : (∫ x,A x*(w x*v x) ∂m) = ∫ x,(A x*v x)*w x ∂m := integral_congr_ae (ae_of_all _ fun x => by ring)
  have hB : (∫ x,B x*(w x*u x) ∂m) = ∫ x,(B x*u x)*w x ∂m := integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hA] at h1
  rw [hB] at h2
  have hr : (∫ x,(A x*v x+B x*u x+2*gamma m u v x)*w x ∂m) =
      (∫ x,(A x*v x)*w x ∂m)+(∫ x,(B x*u x)*w x ∂m)+2*(∫ x,gamma m u v x*w x ∂m) := by
    simp_rw [add_mul,mul_assoc (2:ℝ)]
    rw [integral_add (f := fun x => A x*v x*w x+B x*u x*w x) (hiA.add hiB) (hic.const_mul 2),integral_add hiA hiB,integral_const_mul]
  rw [hp,hr]
  linarith

end WeakHessian

end
end InlinedFile129

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SquareTimePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile133
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma clipSquareLp_ae (n : ℕ) (u : Lp ℝ 2 m) :
    clipSquareLp n u =ᵐ[m] fun x => (realClip n (u x))^2 :=
  (clipSquare_lipschitz n).coeFn_compLp (by simp [realClip_zero]) u

lemma clipSquareLp_eq_square {n : ℕ} {u : Lp ℝ 2 m}
    (hu : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) :
    clipSquareLp n u =ᵐ[m] fun x => (u x)^2 := by
  filter_upwards [clipSquareLp_ae n u,hu] with x hx hb
  rw [hx,realClip,min_eq_left (abs_le.mp hb).2,max_eq_right (abs_le.mp hb).1]

lemma continuous_clipSquareLp (n : ℕ) : Continuous (clipSquareLp (m := m) n) :=
  (clipSquare_lipschitz n).lipschitzWith_compLp (by simp [realClip_zero]) |>.continuous

lemma hasDerivAt_integral_square_mul {u v : ℝ → Lp ℝ 2 m} {u' v' : Lp ℝ 2 m}
    {a : ℝ} (hu : HasDerivAt u u' a) (hv : HasDerivAt v v' a)
    (n : ℕ) (hub : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    {B : ℝ} (hvb : ∀ᵐ x ∂m,|v a x| ≤ B) :
    HasDerivAt (fun t => ∫ x,(u t x)^2*v t x ∂m)
      (2*(∫ x,u a x*u' x*v a x ∂m)+(∫ x,(u a x)^2*v' x ∂m)) a := by
  let M := boundedMulLp (Lp.aestronglyMeasurable (v a)) hvb
  let q := fun t => clipSquareLp n (u t)
  have hq : ContinuousAt q a := (continuous_clipSquareLp n).continuousAt.comp hu.continuousAt
  have hd1 := hu.inner ℝ (M.hasFDerivAt.comp_hasDerivAt a hu)
  have hd2 : HasDerivAt (fun t => ⟪q t,v t-v a⟫_ℝ) ⟪q a,v'⟫_ℝ a := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have HH := (hq.tendsto.mono_left nhdsWithin_le_nhds).inner (𝕜 := ℝ) hv.tendsto_slope
    convert! HH using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [slope_def_module, inner_sub_right, sub_self, sub_zero,
      real_inner_smul_right, smul_eq_mul]
  have hd := hd1.add hd2
  have huba := mem_of_mem_nhds hub
  have heq : (fun t => ∫ x,(u t x)^2*v t x ∂m) =ᶠ[𝓝 a]
      (fun t => ⟪u t,M (u t)⟫_ℝ+⟪q t,v t-v a⟫_ℝ) := by
    filter_upwards [hub] with t ht
    rw [L2.inner_def,L2.inner_def,← integral_add]
    · apply integral_congr_ae
      filter_upwards [boundedMulLp_ae (Lp.aestronglyMeasurable (v a)) hvb (u t),
        clipSquareLp_eq_square ht,Lp.coeFn_sub (v t) (v a)] with x hM hq hv
      simp only [RCLike.inner_apply,conj_trivial]
      dsimp only [M,q] at *
      rw [hM,hq,hv]
      simp only [Pi.sub_apply]
      ring
    · exact L2.integrable_inner (u t) (M (u t))
    · exact L2.integrable_inner (q t) (v t-v a)
  have hresult := hd.congr_of_eventuallyEq heq
  convert! hresult using 1
  all_goals try with_reducible_and_instances rfl
  rw [L2.inner_def,L2.inner_def,L2.inner_def]
  have h1 : (∫ x,⟪u' x,M (u a) x⟫_ℝ ∂m) = ∫ x,u a x*u' x*v a x ∂m := by
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae (Lp.aestronglyMeasurable (v a)) hvb (u a)] with x hx
    simp only [RCLike.inner_apply,conj_trivial]
    dsimp only [M] at *
    rw [hx]; ring
  have h2 : (∫ x,⟪u a x,M u' x⟫_ℝ ∂m) = ∫ x,u a x*u' x*v a x ∂m := by
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae (Lp.aestronglyMeasurable (v a)) hvb u'] with x hx
    simp only [RCLike.inner_apply,conj_trivial]
    dsimp only [M] at *
    rw [hx]; ring
  have h3 : (∫ x,⟪q a x,v' x⟫_ℝ ∂m) = ∫ x,(u a x)^2*v' x ∂m := by
    apply integral_congr_ae
    filter_upwards [clipSquareLp_eq_square huba] with x hx
    simp only [RCLike.inner_apply,conj_trivial]
    dsimp only [q] at *
    rw [hx]; ring
  dsimp only [Function.comp_def]
  rw [h1,h2,h3]
  ring
end WeakHessian

end
end InlinedFile133

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile181
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2) := by
  rw [hrcd.1.global_cheegerEnergy_eq_weakGradient hfin o hf,norm_toLp_sq_eq_integral]

omit [SigmaFinite m] in
lemma RCD.weighted_cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B)
    {f : X → ℝ} (hf : Sobolev (exponentialMeasure m V) f) :
    cheegerEnergy (exponentialMeasure m V) f =
      ENNReal.ofReal ((∫ x,(weakGradient (exponentialMeasure m V) f x)^2
        ∂exponentialMeasure m V)/2) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hfm := (sobolev_exponentialMeasure_iff hB f).mpr hf
  have H := cheegerEnergy_integral_of_comparable hfin
    (fun f hf => hrcd.cheegerEnergy_integral hfin o hf)
    (C := (Real.exp B).toNNReal) (E := (Real.exp B).toNNReal) hm hν hfm
  rw [H]
  congr 2
  apply integral_congr_ae
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (weakGradient_exponentialMeasure (m := m) hB f)] with x hx
  rw [hx]

end WeakHessian

end
end InlinedFile181

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile184
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma RCD.weighted_formGenerator_iff {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u A : Lp ℝ 2 (exponentialMeasure m V)) :
    IsLaplacian (exponentialMeasure m V) (u : X → ℝ) A ↔
      (cheeger_closedQuadraticEnergy h).IsFormGenerator u A := by
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal)
    (exponentialMeasure_comparable (m := m) hBV).2
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  exact ⟨identified_formGenerator_of_isLaplacian hnfin hID h u A,
    identified_isLaplacian_of_formGenerator hnfin hID h u A⟩

end WeakHessian

end
end InlinedFile184

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_MixedGeneratorPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile189
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma IsLaplacian.mixed_pairing (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A C ξ B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v C)
    (hξ : IsLaplacian m ξ B) {L M : ℝ≥0} (huL : LipschitzWith L u) (hvL : LipschitzWith M v)
    {Cu Cv Cξ : ℝ} (huB : ∀ x,|u x| ≤ Cu) (hvB : ∀ x,|v x| ≤ Cv)
    (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    2*(∫ x,ξ x*gamma m u v x ∂m) =
      (∫ x,u x*v x*B x ∂m)-(∫ x,A x*v x*ξ x ∂m)-(∫ x,u x*C x*ξ x ∂m) := by
  have hp := hu.mul_lipschitz hfin hpar hv huL hvL huB hvB
  have h1 := hp.2.2 ξ hξ.1
  have h2 := hξ.2.2 (fun x => u x*v x) hp.1
  have hc : (∫ x,gamma m (fun y => u y*v y) ξ x ∂m) =
      ∫ x,gamma m ξ (fun y => u y*v y) x ∂m := integral_congr_ae (gamma_comm _ _)
  have i1 : Integrable (fun x => A x*v x*ξ x) m :=
    (memLp_mul_bounded hu.2.1 hvL.continuous.aestronglyMeasurable (ae_of_all _ hvB)).integrable_mul hξ.1.1
  have i2 : Integrable (fun x => u x*C x*ξ x) m := by
    have H := (memLp_mul_bounded hv.2.1 huL.continuous.aestronglyMeasurable (ae_of_all _ huB)).integrable_mul hξ.1.1
    change Integrable (fun x => C x*u x*ξ x) m at H
    simpa only [mul_comm (C _)] using H
  have ig := integrable_bounded_gamma hfin hu.1 hv.1 hξ.1.1.aestronglyMeasurable hξB
  have he : (∫ x,(A x*v x+C x*u x+2*gamma m u v x)*ξ x ∂m) =
      (∫ x,A x*v x*ξ x ∂m)+(∫ x,u x*C x*ξ x ∂m)+2*(∫ x,ξ x*gamma m u v x ∂m) := by
    calc
      _ = ∫ x,(A x*v x*ξ x+u x*C x*ξ x)+2*(ξ x*gamma m u v x) ∂m := by
        congr 1; funext x; ring
      _ = _ := by
        rw [integral_add (f := fun x => A x*v x*ξ x+u x*C x*ξ x) (i1.add i2) (ig.const_mul 2),
          integral_add i1 i2,integral_const_mul]
  have he' : (∫ x,B x*(u x*v x) ∂m) = ∫ x,u x*v x*B x ∂m := by
    congr 1; funext x; ring
  rw [he] at h1
  rw [he'] at h2
  linarith

end WeakHessian

end
end InlinedFile189

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GammaRepresentativePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile190
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma IsLaplacian.mixed_pairing_ae (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A C ξ B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v C)
    (hξ : IsLaplacian m ξ B) (huR : BoundedLipschitzRepresentative m u)
    (hvR : BoundedLipschitzRepresentative m v)
    {Cξ : ℝ} (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    2*(∫ x,ξ x*gamma m u v x ∂m) =
      (∫ x,u x*v x*B x ∂m)-(∫ x,A x*v x*ξ x ∂m)-(∫ x,u x*C x*ξ x ∂m) := by
  obtain ⟨u0,⟨L,hL⟩,⟨Cu,hCu⟩,hue⟩ := huR
  obtain ⟨v0,⟨M,hM⟩,⟨Cv,hCv⟩,hve⟩ := hvR
  have H := (hu.congr_ae hue.symm .rfl).mixed_pairing hfin hpar
    (hv.congr_ae hve.symm .rfl) hξ hL hM hCu hCv hξB
  have e1 : (∫ x,ξ x*gamma m u0 v0 x ∂m) = ∫ x,ξ x*gamma m u v x ∂m :=
    integral_congr_ae (.fun_mul .rfl (gamma_congr_ae hue hve))
  have e2 : (∫ x,u0 x*v0 x*B x ∂m) = ∫ x,u x*v x*B x ∂m :=
    integral_congr_ae ((hue.fun_mul hve).fun_mul .rfl)
  have e3 : (∫ x,A x*v0 x*ξ x ∂m) = ∫ x,A x*v x*ξ x ∂m :=
    integral_congr_ae ((EventuallyEq.fun_mul .rfl hve).fun_mul .rfl)
  have e4 : (∫ x,u0 x*C x*ξ x ∂m) = ∫ x,u x*C x*ξ x ∂m :=
    integral_congr_ae ((hue.fun_mul .rfl).fun_mul .rfl)
  rwa [e1,e2,e3,e4] at H

omit [SigmaFinite m] in
lemma IsLaplacian.square_gamma_pairing_ae (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ B : X → ℝ}
    (hu : IsLaplacian m u A) (hξ : IsLaplacian m ξ B)
    (huR : BoundedLipschitzRepresentative m u) {Cξ : ℝ}
    (hξB : ∀ᵐ x ∂m,|ξ x| ≤ Cξ) :
    (∫ x,ξ x*gamma m u u x ∂m) =
      (1/2)*(∫ x,(u x)^2*B x ∂m)-(∫ x,u x*A x*ξ x ∂m) := by
  have H := hu.mixed_pairing_ae hfin hpar hu hξ huR huR hξB
  have e1 : (∫ x,u x*u x*B x ∂m) = ∫ x,(u x)^2*B x ∂m := by simp only [pow_two]
  have e2 : (∫ x,A x*u x*ξ x ∂m) = ∫ x,u x*A x*ξ x ∂m := by congr 1; funext x; ring
  rw [e1,e2] at H
  linarith

end WeakHessian

end
end InlinedFile190

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TripleTimePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile186
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_bounded_triple (u v w : Lp ℝ 2 m) {B : ℝ}
    (hw : ∀ᵐ x ∂m,|w x| ≤ B) : Integrable (fun x => u x*v x*w x) m := by
  simpa only [Pi.mul_apply,mul_comm (w _)] using
    (Lp.memLp u |>.integrable_mul (Lp.memLp v)).bdd_mul (Lp.aestronglyMeasurable w)
      (by simpa only [Real.norm_eq_abs] using hw)

lemma hasDerivAt_integral_mul_mul {u v w : ℝ → Lp ℝ 2 m}
    {u' v' w' : Lp ℝ 2 m} {a : ℝ}
    (hu : HasDerivAt u u' a) (hv : HasDerivAt v v' a) (hw : HasDerivAt w w' a)
    (n : ℕ) (hub : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    (hvb : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|v t x| ≤ (n:ℝ))
    {B : ℝ} (hwb : ∀ᵐ x ∂m,|w a x| ≤ B) :
    HasDerivAt (fun t => ∫ x,u t x*v t x*w t x ∂m)
      ((∫ x,u' x*v a x*w a x ∂m)+(∫ x,u a x*v' x*w a x ∂m)+
        (∫ x,u a x*v a x*w' x ∂m)) a := by
  have huba := mem_of_mem_nhds hub
  have hvba := mem_of_mem_nhds hvb
  have hs : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|(u t+v t) x| ≤ ((2*n:ℕ):ℝ) := by
    filter_upwards [hub,hvb] with t ht hv
    filter_upwards [ht,hv,Lp.coeFn_add (u t) (v t)] with x hx hy he
    rw [he]
    push_cast
    exact (abs_add_le _ _).trans (by linarith)
  have hd := ((hasDerivAt_integral_square_mul (hu.add hv) hw (2*n) hs hwb).sub
    (hasDerivAt_integral_square_mul hu hw n hub hwb)).sub
      (hasDerivAt_integral_square_mul hv hw n hvb hwb)
  have hi (t : ℝ) (ht : ∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
      (hv : ∀ᵐ x ∂m,|v t x| ≤ (n:ℝ)) :
      (∫ x,((u t+v t) x)^2*w t x ∂m)-(∫ x,(u t x)^2*w t x ∂m)-
        (∫ x,(v t x)^2*w t x ∂m) = 2*(∫ x,u t x*v t x*w t x ∂m) := by
    have iu := (memLp_mul_bounded (Lp.memLp (u t)) (Lp.aestronglyMeasurable (u t)) ht).integrable_mul (Lp.memLp (w t))
    have iv := (memLp_mul_bounded (Lp.memLp (v t)) (Lp.aestronglyMeasurable (v t)) hv).integrable_mul (Lp.memLp (w t))
    have iuv := (memLp_mul_bounded (Lp.memLp (u t)) (Lp.aestronglyMeasurable (v t)) hv).integrable_mul (Lp.memLp (w t))
    change Integrable (fun x => u t x*u t x*w t x) m at iu
    change Integrable (fun x => v t x*v t x*w t x) m at iv
    change Integrable (fun x => u t x*v t x*w t x) m at iuv
    have he : (∫ x,((u t+v t) x)^2*w t x ∂m) =
      (∫ x,(u t x)^2*w t x ∂m)+2*(∫ x,u t x*v t x*w t x ∂m)+
        (∫ x,(v t x)^2*w t x ∂m) := by
      calc
        _ = ∫ x,((u t x)^2*w t x+2*(u t x*v t x*w t x))+(v t x)^2*w t x ∂m := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add (u t) (v t)] with x hx
          rw [hx]; simp only [Pi.add_apply]; ring
        _ = _ := by
          have iu' : Integrable (fun x => (u t x)^2*w t x) m := by simpa only [pow_two] using iu
          have iv' : Integrable (fun x => (v t x)^2*w t x) m := by simpa only [pow_two] using iv
          rw [integral_add (f := fun x => (u t x)^2*w t x+2*(u t x*v t x*w t x)) (iu'.add (iuv.const_mul 2)) iv',
            integral_add iu' (iuv.const_mul 2),integral_const_mul]
    linarith
  have heq : (fun t => (∫ x,((u t+v t) x)^2*w t x ∂m)-(∫ x,(u t x)^2*w t x ∂m)-
        (∫ x,(v t x)^2*w t x ∂m)) =ᶠ[𝓝 a]
      (fun t => 2*(∫ x,u t x*v t x*w t x ∂m)) := by
    filter_upwards [hub,hvb] with t ht hv
    exact hi t ht hv
  have hd' := (hd.congr_of_eventuallyEq heq.symm).div_const 2

  have hab : Integrable (fun x => u a x*v a x*w' x) m :=
    (memLp_mul_bounded (Lp.memLp (u a)) (Lp.aestronglyMeasurable (v a)) hvba).integrable_mul (Lp.memLp w')
  have hsq (p : Lp ℝ 2 m) (hp : ∀ᵐ x ∂m,|p x| ≤ (n:ℝ)) :
      Integrable (fun x => (p x)^2*w' x) m := by
    have H := (memLp_mul_bounded (Lp.memLp p) (Lp.aestronglyMeasurable p) hp).integrable_mul (Lp.memLp w')
    change Integrable (fun x => p x*p x*w' x) m at H
    simpa only [pow_two] using H
  have e1 : (∫ x,(u a+v a) x*(u'+v') x*w a x ∂m) =
      (∫ x,u a x*u' x*w a x ∂m)+(∫ x,u a x*v' x*w a x ∂m)+
      (∫ x,u' x*v a x*w a x ∂m)+(∫ x,v a x*v' x*w a x ∂m) := by
    calc
      _ = ∫ x,((u a x*u' x*w a x+u a x*v' x*w a x)+u' x*v a x*w a x)+v a x*v' x*w a x ∂m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (u a) (v a),Lp.coeFn_add u' v'] with x hx hy
        rw [hx,hy]; simp only [Pi.add_apply]; ring
      _ = _ := by
        have i1 := integral_bounded_triple (u a) u' (w a) hwb
        have i2 := integral_bounded_triple (u a) v' (w a) hwb
        have i3 := integral_bounded_triple u' (v a) (w a) hwb
        have i4 := integral_bounded_triple (v a) v' (w a) hwb
        rw [integral_add (f := fun x => (u a x*u' x*w a x+u a x*v' x*w a x)+u' x*v a x*w a x) ((i1.add i2).add i3) i4,
          integral_add (f := fun x => u a x*u' x*w a x+u a x*v' x*w a x) (i1.add i2) i3,integral_add i1 i2]
  have e2 : (∫ x,((u a+v a) x)^2*w' x ∂m) =
      (∫ x,(u a x)^2*w' x ∂m)+2*(∫ x,u a x*v a x*w' x ∂m)+
        (∫ x,(v a x)^2*w' x ∂m) := by
    calc
      _ = ∫ x,((u a x)^2*w' x+2*(u a x*v a x*w' x))+(v a x)^2*w' x ∂m := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (u a) (v a)] with x hx
        rw [hx]; simp only [Pi.add_apply]; ring
      _ = _ := by
        rw [integral_add (f := fun x => (u a x)^2*w' x+2*(u a x*v a x*w' x)) ((hsq _ huba).add (hab.const_mul 2)) (hsq _ hvba),
          integral_add (hsq _ huba) (hab.const_mul 2),integral_const_mul]
  simp only [Pi.add_apply] at hd'
  rw [e1,e2] at hd'
  convert! hd' using 1 <;> (first | (funext t; ring) | ring)
end WeakHessian

end
end InlinedFile186

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GammaTimeDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile191
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_triple_neg_left (u v w : Lp ℝ 2 m) :
    (∫ x,(-u) x*v x*w x ∂m) = -(∫ x,u x*v x*w x ∂m) := by
  calc
    _ = ∫ x,-(u x*v x*w x) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_neg u] with x hx
      rw [hx]; simp only [Pi.neg_apply]; ring
    _ = _ := integral_neg _

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_triple_neg_middle (u v w : Lp ℝ 2 m) :
    (∫ x,u x*(-v) x*w x ∂m) = -(∫ x,u x*v x*w x ∂m) := by
  calc
    _ = ∫ x,-(u x*v x*w x) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_neg v] with x hx
      rw [hx]; simp only [Pi.neg_apply]; ring
    _ = _ := integral_neg _

omit [SigmaFinite m] in
lemma hasDerivAt_gamma_interpolation (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m)
    {u A ξ B : ℝ → Lp ℝ 2 m} {C D : Lp ℝ 2 m} {a : ℝ}
    (hud : HasDerivAt u (-A a) a) (hAd : HasDerivAt A (-C) a)
    (hξd : HasDerivAt ξ (B a) a) (hBd : HasDerivAt B D a)
    (huG : ∀ᶠ t in 𝓝 a,IsLaplacian m (u t : X → ℝ) (A t))
    (hAG : IsLaplacian m (A a : X → ℝ) C)
    (hξG : ∀ᶠ t in 𝓝 a,IsLaplacian m (ξ t : X → ℝ) (B t))
    (hBG : IsLaplacian m (B a : X → ℝ) D)
    (huR : ∀ᶠ t in 𝓝 a,BoundedLipschitzRepresentative m (u t))
    (hAR : BoundedLipschitzRepresentative m (A a))
    (n : ℕ) (hub : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    (hAb : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|A t x| ≤ (n:ℝ))
    {Cξ CB : ℝ} (hξb : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|ξ t x| ≤ Cξ)
    (hBb : ∀ᵐ x ∂m,|B a x| ≤ CB) :
    HasDerivAt (fun t => ∫ x,ξ t x*gamma m (u t : X → ℝ) (u t) x ∂m)
      ((∫ x,B a x*gamma m (u a : X → ℝ) (u a) x ∂m)-
        2*(∫ x,ξ a x*gamma m (u a : X → ℝ) (A a) x ∂m)) a := by
  have huga := mem_of_mem_nhds huG
  have hξga := mem_of_mem_nhds hξG
  have hura := mem_of_mem_nhds huR
  have hξba := mem_of_mem_nhds hξb
  have hd1 := (hasDerivAt_integral_square_mul hud hBd n hub hBb).const_mul (1/2:ℝ)
  have hd2 := hasDerivAt_integral_mul_mul hud hAd hξd n hub hAb hξba
  have hd := hd1.sub hd2
  have heq : (fun t => ∫ x,ξ t x*gamma m (u t : X → ℝ) (u t) x ∂m) =ᶠ[𝓝 a]
      (fun t => (1/2)*(∫ x,(u t x)^2*B t x ∂m)-(∫ x,u t x*A t x*ξ t x ∂m)) := by
    filter_upwards [huG,hξG,huR,hξb] with t h1 h2 h3 h4
    exact h1.square_gamma_pairing_ae hfin hpar h2 h3 h4
  have H := hd.congr_of_eventuallyEq heq
  rw [integral_triple_neg_middle,integral_triple_neg_left,integral_triple_neg_middle] at H
  have e1 := huga.square_gamma_pairing_ae hfin hpar hBG hura hBb
  have e2 := huga.mixed_pairing_ae hfin hpar hAG hξga hura hAR hξba
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  rw [e1,e2]
  ring
end WeakHessian

end
end InlinedFile191

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile192
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma cheegerHeat_backwards_derivative (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {t T : ℝ} (ht : t < T) :
    HasDerivAt (fun s => cheegerHeat h (T-s) u) (-cheegerHeat h (T-t) A) t := by
  have H := (cheegerHeat_deriv_at_generator hfin h hu (sub_pos.mpr ht)).scomp_of_eq t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t)) rfl
  simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,id_eq,Pi.sub_apply] using H

lemma RCD.weighted_heat_interpolation_hasDerivAt {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {f Af AAf ξ Bξ BBξ : Lp ℝ 2 (exponentialMeasure m V)}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    (hBξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator Bξ BBξ)
    {Cf CAf CAAf Cξ CBξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ) (hCBξ : 0 ≤ CBξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m V,|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m V,|ξ x| ≤ Cξ)
    (hBξb : ∀ᵐ x ∂exponentialMeasure m V,|Bξ x| ≤ CBξ)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ x,cheegerHeat h s ξ x*
        gamma (exponentialMeasure m V) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
          ∂exponentialMeasure m V)
      ((∫ x,cheegerHeat h t Bξ x*
        gamma (exponentialMeasure m V) (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) f) x
          ∂exponentialMeasure m V)-
        2*(∫ x,cheegerHeat h t ξ x*
          gamma (exponentialMeasure m V) (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) Af) x
            ∂exponentialMeasure m V)) t := by
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hgen {u A : Lp ℝ 2 ν} (hu : Q.IsFormGenerator u A) (s : ℝ) :
      IsLaplacian ν (cheegerHeat h s u) (cheegerHeat h s A) :=
    (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr (Q.formGenerator_heat ν hu s)
  obtain ⟨n,hn⟩ := exists_nat_ge (max Cf CAf)
  have hn1 : Cf ≤ (n:ℝ) := (le_max_left _ _).trans hn
  have hn2 : CAf ≤ (n:ℝ) := (le_max_right _ _).trans hn
  apply hasDerivAt_gamma_interpolation (Cξ := Cξ) (CB := CBξ) hnfin hnpar
    (cheegerHeat_backwards_derivative hnfin h hf htT)
    (cheegerHeat_backwards_derivative hnfin h hAf htT)
    (cheegerHeat_deriv_at_generator hnfin h hξ ht)
    (cheegerHeat_deriv_at_generator hnfin h hBξ ht)
    (Eventually.of_forall fun s => hgen hf (T-s)) (hgen hAf (T-t))
    (Eventually.of_forall fun s => hgen hξ s) (hgen hBξ t)
    _ _ n _ _ _ (cheegerHeat_bounded h ht.le hCBξ Bξ hBξb)
  · filter_upwards [eventually_lt_nhds htT] with s hs
    exact hrcd.weighted_heat_boundedLipschitzRepresentative hN hfull hfin o hV hBV h hf hCf hCAf
      hfb hAfb (sub_nonneg.mpr hs.le)
  · exact hrcd.weighted_heat_boundedLipschitzRepresentative hN hfull hfin o hV hBV h hAf hCAf hCAAf
      hAfb hAAfb (sub_nonneg.mpr htT.le)
  · filter_upwards [eventually_lt_nhds htT] with s hs
    exact (cheegerHeat_bounded h (sub_nonneg.mpr hs.le) hCf f hfb).mono fun x hx => hx.trans hn1
  · filter_upwards [eventually_lt_nhds htT] with s hs
    exact (cheegerHeat_bounded h (sub_nonneg.mpr hs.le) hCAf Af hAfb).mono fun x hx => hx.trans hn2
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact cheegerHeat_bounded h hs.le hCξ ξ hξb
end WeakHessian

end
end InlinedFile192

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

section
omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma integral_mul_eq_inner {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x, f x*g x ∂m) = ⟪hg.toLp g,hf.toLp f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp only [hx,hy]
  rfl

end

end WeakHessian

end
end InlinedFile173

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatBE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile193
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_interpolation_BE {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af AAf ξ Bξ BBξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    (hBξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator Bξ BBξ)
    {Cf CAf CAAf Cξ CBξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ) (hCBξ : 0 ≤ CBξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hBξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Bξ x| ≤ CBξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) :
    2*(∫ x,(cheegerHeat h t ξ x*(K-a*G x))*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) f) x
        ∂exponentialMeasure m (fun x => a*F x)) ≤
      deriv (fun s => ∫ x,cheegerHeat h s ξ x*
        gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
          ∂exponentialMeasure m (fun x => a*F x)) t := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hd := hrcd.weighted_heat_interpolation_hasDerivAt hN hfull hfin o hV hVB h hf hAf hξ hBξ
    hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb ht htT
  rw [hd.deriv]
  have hgen {u A : Lp ℝ 2 ν} (hu : Q.IsFormGenerator u A) (s : ℝ) :
      IsLaplacian ν (cheegerHeat h s u) (cheegerHeat h s A) :=
    (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (Q.formGenerator_heat ν hu s)
  have hBE := hHess.rcd_weighted_BE hN hrcd hfull hfin o hF hFb hGb hGc ha
    (hgen hf (T-t)) (hgen hAf (T-t)).1 (hgen hξ t)
    (cheegerHeat_bounded h ht.le hCξ ξ hξb) (cheegerHeat_bounded h ht.le hCBξ Bξ hBξb)
    (cheegerHeat_nonneg h ht.le ξ hξ0)
  linarith only [hBE]
end WeakHessian

end
end InlinedFile193

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatVariableDissipation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile199
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_dissipation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af AAf ξ Bξ BBξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    (hBξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator Bξ BBξ)
    {Cf CAf CAAf Cξ CBξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ) (hCBξ : 0 ≤ CBξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hBξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Bξ x| ≤ CBξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    2*(∫ s in 0..T,∫ x,(cheegerHeat h s ξ x*(K-a*G x))*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m (fun x => a*F x)) ≤
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x))-
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T f) (cheegerHeat h T f) x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  let E := fun s => ∫ x,cheegerHeat h s ξ x*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  let Z := fun s => ∫ x,(cheegerHeat h s ξ x*(K-a*G x))*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  have hc : ContinuousOn E (Icc 0 T) :=
    hrcd.weighted_heat_gamma_continuousOn hN hfull hfin o hV hVB h hf hξ hCf hCAf hCξ hfb hAfb hξb T
  have hZ : ContinuousOn Z (Icc 0 T) := by
    apply hrcd.weighted_heat_curvature_continuousOn hN hfull hfin o hV hVB h ξ hf hCf hCAf hfb hAfb
      ((continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable) (B := |K|+|a| *CG) _ T
    exact ae_of_all _ fun x => (abs_sub _ _).trans (by dsimp only [Pi.mul_apply]; rw [abs_mul]; gcongr; exact hGb x)
  have hd : ∀ t ∈ Ioo 0 T,HasDerivWithinAt E (deriv E t) (Ioi t) t := by
    intro t ht
    exact (hrcd.weighted_heat_interpolation_hasDerivAt hN hfull hfin o hV hVB h hf hAf hξ hBξ
      hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb ht.1 ht.2).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hi : ∀ t ∈ Ioo 0 T,2*Z t ≤ deriv E t := fun t ht =>
    hHess.rcd_weighted_heat_interpolation_BE hN hrcd hfull hfin o hF hFb hGb hGc ha h
      hf hAf hξ hBξ hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb hξ0 ht.1 ht.2
  have H := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT hc hd
    ((hZ.const_mul 2).integrableOn_Icc) hi
  rw [intervalIntegral.integral_const_mul] at H
  simpa only [E,Z,sub_zero,sub_self,cheegerHeat_zero,one_apply_eq_self,ν,V] using H
end WeakHessian

end
end InlinedFile199

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_VariableDissipationTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_bounded_test {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af AAf ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    {Cf CAf CAAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    2*(∫ s in 0..T,∫ x,(cheegerHeat h s ξ x*(K-a*G x))*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m (fun x => a*F x)) ≤
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x))-
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T f) (cheegerHeat h T f) x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCξ ξ hξb)
  have hvs0 (n : ℕ) : ∀ᵐ x ∂ν,0 ≤ vs n x := by
    rw [he n]; exact cheeger_double_resolvent_nonneg h (hts n) ξ hξ0
  have hvs : Tendsto vs atTop (𝓝 ξ) := by
    have H := cheeger_double_resolvent_tendsto h hts ht0 ξ
    exact H.congr (fun n => (he n).symm)
  have hΓ (t : ℝ) (ht : 0 ≤ t) :
      MemLp (gamma ν (cheegerHeat h t f) (cheegerHeat h t f)) 2 ν :=
    hrcd.weighted_heat_gamma_memLp hN hfull hfin o hV hVB h hf hCf hCAf hfb hAfb ht
  have hΓ0 : MemLp (gamma ν f f) 2 ν := by
    simpa only [cheegerHeat_zero,one_apply_eq_self] using hΓ 0 le_rfl
  have hid (v : Lp ℝ 2 ν) {q : X → ℝ} (hq : MemLp q 2 ν) :
      (∫ x,v x*q x ∂ν) = ⟪hq.toLp q,v⟫_ℝ := by
    simpa only [Lp.toLp_coeFn] using integral_mul_eq_inner (Lp.memLp v) hq
  have hleft : Tendsto (fun n => ∫ x,vs n x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)
      atTop (𝓝 (∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)) := by
    simp only [hid _ (hΓ T hT)]
    exact (tendsto_const_nhds (x := (hΓ T hT).toLp _)).inner hvs
  have hright : Tendsto (fun n => ∫ x,cheegerHeat h T (vs n) x*gamma ν f f x ∂ν)
      atTop (𝓝 (∫ x,cheegerHeat h T ξ x*gamma ν f f x ∂ν)) := by
    simp only [hid _ hΓ0]
    simpa only [Function.comp_def] using (tendsto_const_nhds (x := hΓ0.toLp _)).inner
      ((cheegerHeat h T).continuous.tendsto ξ |>.comp hvs)
  let k := fun x => K-a*G x
  let B := |K|+|a| *CG
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hkm : AEStronglyMeasurable k ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hkb : ∀ᵐ x ∂ν, |k x| ≤ B := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by dsimp only [B]; rw [abs_mul]; gcongr; exact hGb x)
  let Z := fun (v : Lp ℝ 2 ν) s => ∫ x, (cheegerHeat h s v x*k x)*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  have hZ (v : Lp ℝ 2 ν) : ContinuousOn (Z v) (Icc 0 T) :=
    hrcd.weighted_heat_curvature_continuousOn hN hfull hfin o hV hVB h v hf hCf hCAf hfb hAfb hkm hkb T
  have hZlim (s : ℝ) (hs : s ∈ Icc 0 T) :
      Tendsto (fun n => Z (vs n) s) atTop (𝓝 (Z ξ s)) := by
    have hq := memLp_mul_bounded (hΓ (T-s) (sub_nonneg.mpr hs.2)) hkm hkb
    have H := (tendsto_const_nhds (x := hq.toLp _)).inner (𝕜 := ℝ)
      ((cheegerHeat h s).continuous.tendsto ξ |>.comp hvs)
    have hrepr (v : Lp ℝ 2 ν) : Z v s = ⟪hq.toLp _,cheegerHeat h s v⟫_ℝ := by
      rw [← hid _ hq]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; ring
    simpa only [hrepr,Function.comp_def] using H
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hfS : Sobolev ν (f : X → ℝ) :=
    (identified_sobolev_iff_energy hnfin hID).mpr hf.1
  have hZbound (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖Z (vs n) s‖ ≤ (Cξ*B)*(2*(cheegerEnergy ν (f : X → ℝ)).toReal) := by
    simpa only [Real.norm_eq_abs,Z] using abs_weighted_heat_gamma_le hnfin hID h hfS hCξ
      (hvb n) hkm hB hkb hs.1 (sub_nonneg.mpr hs.2)
  have htime : Tendsto (fun n => ∫ s in 0..T, Z (vs n) s) atTop (𝓝 (∫ s in 0..T, Z ξ s)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (Cξ*B)*(2*(cheegerEnergy ν (f : X → ℝ)).toReal))
    · exact Eventually.of_forall fun n => ((hZ (vs n)).mono (by
        rw [uIoc_of_le hT]; exact Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hZbound n s (by
        rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hZlim s (by rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
  apply le_of_tendsto_of_tendsto (htime.const_mul 2) (hright.sub hleft)
    (Eventually.of_forall fun n => ?_)
  exact hHess.rcd_weighted_heat_variable_dissipation hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hf hAf (hg n) (hAg n) hCf hCAf hCAAf hCξ (by positivity)
    hfb hAfb hAAfb (hvb n) (hAb n) (hvs0 n) hT
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EnergyGammaPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile208
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma energy_tendsto_weakGradient (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    {un : ℕ → X → ℝ} {u : X → ℝ}
    (hn : ∀ n,Sobolev m (un n)) (hu : Sobolev m u)
    (ht : Tendsto (fun n => (cheegerEnergy m (fun x => un n x-u x)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (hn n).2.2.toLp (weakGradient m (un n))) atTop
      (𝓝 (hu.2.2.toLp (weakGradient m u))) := by
  have hd (n : ℕ) := (hn n).sub hfin hu
  have he (n : ℕ) : ‖(hd n).2.2.toLp (weakGradient m (fun x => un n x-u x))‖^2 =
      2*(cheegerEnergy m (fun x => un n x-u x)).toReal := by
    rw [norm_toLp_sq_eq_integral,identified_cheegerEnergy_toReal hID (hd n)]
    ring
  have hs : Tendsto (fun n => ‖(hd n).2.2.toLp (weakGradient m (fun x => un n x-u x))‖^2)
      atTop (𝓝 0) := by simpa only [he,mul_zero] using ht.const_mul 2
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hnorm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hnorm
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub ((hn n).2.2.toLp (weakGradient m (un n)))
      (hu.2.2.toLp (weakGradient m u)),(hn n).2.2.coeFn_toLp,
    hu.2.2.coeFn_toLp,(hd n).2.2.coeFn_toLp,
    weakGradient_dist_le hfin (hn n).2.1 hu.2.1,
    weakGradient_nonneg (m := m) (fun x => un n x-u x)] with x hs hn' hu' hd hab hp
  rw [hs,Pi.sub_apply,hn',hu',hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
  exact hab

omit [ProperSpace X] [SigmaFinite m] in
lemma energy_tendsto_gamma_bounded_pairing (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    {un : ℕ → X → ℝ} {u : X → ℝ}
    (hn : ∀ n,Sobolev m (un n)) (hu : Sobolev m u)
    (ht : Tendsto (fun n => (cheegerEnergy m (fun x => un n x-u x)).toReal) atTop (𝓝 0))
    {ξ : X → ℝ} (hξ : AEStronglyMeasurable ξ m) {B : ℝ} (hξb : ∀ᵐ x ∂m,|ξ x| ≤ B) :
    Tendsto (fun n => ∫ x,ξ x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x,ξ x*gamma m u u x ∂m)) := by
  have hD := energy_tendsto_weakGradient hfin hID hn hu ht
  have hval := tendsto_integral_bounded_Lp_sq hξ hξb hD
  have hid (v : X → ℝ) (hv : MemLp (weakGradient m v) 2 m) :
      (∫ x,ξ x*gamma m v v x ∂m) = ∫ x,ξ x*(hv.toLp (weakGradient m v) x)^2 ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) v,hv.coeFn_toLp] with x hΓ hx
    rw [hΓ,hx]
  simpa only [hid _ hu.2.2,hid _ ((hn _).2.2)] using hval
end WeakHessian

end
end InlinedFile208

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_VariableEnergyClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma energy_tendsto_heat_gamma_bounded_pairing
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {fs : ℕ → Lp ℝ 2 m} {f : Lp ℝ 2 m}
    (hfs : ∀ n, Sobolev m (fs n : X → ℝ)) (hf : Sobolev m (f : X → ℝ))
    (hE : Tendsto (fun n => (cheegerEnergy m ((fs n-f : Lp ℝ 2 m) : X → ℝ)).toReal)
      atTop (𝓝 0)) {q : X → ℝ} (hqm : AEStronglyMeasurable q m)
    {B : ℝ} (hqb : ∀ᵐ x ∂m, |q x| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ x, q x*gamma m (cheegerHeat h t (fs n)) (cheegerHeat h t (fs n)) x ∂m)
      atTop (𝓝 (∫ x, q x*gamma m (cheegerHeat h t f) (cheegerHeat h t f) x ∂m)) := by
  let Q := cheeger_closedQuadraticEnergy h
  have hfd := (identified_sobolev_iff_energy hfin hID).mp hf
  have hfsd (n : ℕ) := (identified_sobolev_iff_energy hfin hID).mp (hfs n)
  have hft : Sobolev m (cheegerHeat h t f) :=
    (identified_sobolev_iff_energy hfin hID).mpr ((cheegerHeat_energy_le h ht f).trans_lt hfd)
  have hfst (n : ℕ) : Sobolev m (cheegerHeat h t (fs n)) :=
    (identified_sobolev_iff_energy hfin hID).mpr ((cheegerHeat_energy_le h ht (fs n)).trans_lt (hfsd n))
  have hEt : Tendsto (fun n => (cheegerEnergy m
      ((cheegerHeat h t (fs n)-cheegerHeat h t f : Lp ℝ 2 m) : X → ℝ)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hE
    rw [← map_sub]
    exact ENNReal.toReal_mono (Q.sub_lt_top (hfsd n) hfd).ne (cheegerHeat_energy_le h ht (fs n-f))
  apply energy_tendsto_gamma_bounded_pairing hfin hID hfst hft _ hqm hqb
  simpa only [cheegerEnergy_congr_ae (Lp.coeFn_sub _ _),Pi.sub_def] using hEt

omit [SigmaFinite m] in
lemma energy_tendsto_variable_heat_integral
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {fs : ℕ → Lp ℝ 2 m} {f ξ : Lp ℝ 2 m}
    (hfs : ∀ n, Sobolev m (fs n : X → ℝ)) (hf : Sobolev m (f : X → ℝ))
    (hE : Tendsto (fun n => (cheegerEnergy m ((fs n-f : Lp ℝ 2 m) : X → ℝ)).toReal)
      atTop (𝓝 0)) {M : ℝ} (hM : ∀ n, (cheegerEnergy m (fs n : X → ℝ)).toReal ≤ M)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m, |ξ x| ≤ Cξ)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m)
    {B : ℝ} (hB : 0 ≤ B) (hkb : ∀ᵐ x ∂m, |k x| ≤ B)
    {T : ℝ} (hT : 0 ≤ T)
    (hi : ∀ n, IntervalIntegrable
      (fun s => ∫ x, (cheegerHeat h s ξ x*k x)*
        gamma m (cheegerHeat h (T-s) (fs n)) (cheegerHeat h (T-s) (fs n)) x ∂m) volume 0 T) :
    IntervalIntegrable
      (fun s => ∫ x, (cheegerHeat h s ξ x*k x)*
        gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m) volume 0 T ∧
    Tendsto (fun n => ∫ s in 0..T, ∫ x, (cheegerHeat h s ξ x*k x)*
      gamma m (cheegerHeat h (T-s) (fs n)) (cheegerHeat h (T-s) (fs n)) x ∂m)
      atTop (𝓝 (∫ s in 0..T, ∫ x, (cheegerHeat h s ξ x*k x)*
        gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m)) := by
  let Z := fun (u : Lp ℝ 2 m) s => ∫ x, (cheegerHeat h s ξ x*k x)*
    gamma m (cheegerHeat h (T-s) u) (cheegerHeat h (T-s) u) x ∂m
  have hlim (s : ℝ) (hs : s ∈ Icc 0 T) : Tendsto (fun n => Z (fs n) s) atTop (𝓝 (Z f s)) := by
    apply energy_tendsto_heat_gamma_bounded_pairing hfin hID h hfs hf hE
      ((Lp.memLp _).aestronglyMeasurable.mul hkm) (B := Cξ*B) _ (sub_nonneg.mpr hs.2)
    filter_upwards [cheegerHeat_bounded h hs.1 hCξ ξ hξb,hkb] with x hξ hk
    rw [Pi.mul_apply,abs_mul]
    exact mul_le_mul hξ hk (abs_nonneg _) hCξ
  have hmeas (n : ℕ) : AEStronglyMeasurable (Z (fs n)) (volume.restrict (uIoc 0 T)) :=
    (intervalIntegrable_iff.mp (hi n)).1
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Z (fs n) s‖ ≤ (Cξ*B)*(2*M) := by
    rw [Real.norm_eq_abs]
    exact (abs_weighted_heat_gamma_le hfin hID h (hfs n) hCξ hξb hkm hB hkb
      hs.1 (sub_nonneg.mpr hs.2)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hM n]) (mul_nonneg hCξ hB))
  constructor
  · apply intervalIntegrable_iff.mpr
    have hzm : AEStronglyMeasurable (Z f) (volume.restrict (uIoc 0 T)) :=
      aestronglyMeasurable_of_tendsto_ae atTop hmeas ((ae_restrict_iff' measurableSet_uIoc).mpr
        (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)))
    have hc : IntervalIntegrable (fun _ : ℝ => (Cξ*B)*(2*(cheegerEnergy m (f : X → ℝ)).toReal)) volume 0 T := intervalIntegrable_const
    apply (intervalIntegrable_iff.mp hc).mono' hzm
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    exact ae_of_all _ fun s hs => by
      rw [uIoc_of_le hT] at hs
      simpa only [Z,Real.norm_eq_abs] using abs_weighted_heat_gamma_le hfin hID h hf hCξ hξb hkm hB hkb
        hs.1.le (sub_nonneg.mpr hs.2)
  · apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (Cξ*B)*(2*M))
    · exact Eventually.of_forall hmeas
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hbound n s (by
        rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_VariableDuhamelClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma ClosedQuadraticEnergy.graph_energy_limits {Q : E → ℝ≥0∞}
    (hQ : ClosedQuadraticEnergy Q) {us As : ℕ → E} {u A : E}
    (hs : ∀ n, hQ.IsFormGenerator (us n) (As n)) (hu : hQ.IsFormGenerator u A)
    (hus : Tendsto us atTop (𝓝 u)) (hAs : Tendsto As atTop (𝓝 A)) :
    Tendsto (fun n => (Q (us n-u)).toReal) atTop (𝓝 0) ∧
      ∃ M : ℝ, ∀ n, (Q (us n)).toReal ≤ M := by
  have hsub (n : ℕ) : (Q (us n-u)).toReal = -⟪As n-A,us n-u⟫_ℝ/2 := by
    linarith only [hQ.formGenerator_energy (hQ.formGenerator_sub (hs n) hu)]
  have he (n : ℕ) : (Q (us n)).toReal = -⟪As n,us n⟫_ℝ/2 := by
    linarith only [hQ.formGenerator_energy (hs n)]
  constructor
  · simp only [hsub]
    simpa only [sub_self,inner_zero_right,neg_zero,zero_div] using
      (((hAs.sub_const A).inner (𝕜 := ℝ) (hus.sub_const u)).neg.div_const 2)
  · have H : Tendsto (fun n => (Q (us n)).toReal) atTop (𝓝 (-⟪A,u⟫_ℝ/2)) := by
      simp only [he]
      exact (hAs.inner hus).neg.div_const 2
    obtain ⟨M,hM⟩ := H.bddAbove_range
    exact ⟨M,fun n => hM (mem_range_self n)⟩
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma heatVariableDissipation_of_energy_tendsto
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {fs : ℕ → Lp ℝ 2 m} {f ξ : Lp ℝ 2 m}
    (hfs : ∀ n, Sobolev m (fs n : X → ℝ)) (hf : Sobolev m (f : X → ℝ))
    (hE : Tendsto (fun n => (cheegerEnergy m ((fs n-f : Lp ℝ 2 m) : X → ℝ)).toReal)
      atTop (𝓝 0)) {M : ℝ} (hM : ∀ n, (cheegerEnergy m (fs n : X → ℝ)).toReal ≤ M)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m, |ξ x| ≤ Cξ)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m)
    {B : ℝ} (hB : 0 ≤ B) (hkb : ∀ᵐ x ∂m, |k x| ≤ B)
    {T : ℝ} (hT : 0 ≤ T) (hs : ∀ n, HeatVariableDissipation h k (fs n) ξ T) :
    HeatVariableDissipation h k f ξ T := by
  obtain ⟨hi,ht⟩ := energy_tendsto_variable_heat_integral hfin hID h hfs hf hE hM
    hCξ hξb hkm hB hkb hT (fun n => (hs n).1)
  have hleft := energy_tendsto_heat_gamma_bounded_pairing hfin hID h hfs hf hE
    (Lp.aestronglyMeasurable ξ) hξb hT
  have hright : Tendsto (fun n => ∫ x, cheegerHeat h T ξ x*gamma m (fs n) (fs n) x ∂m)
      atTop (𝓝 (∫ x, cheegerHeat h T ξ x*gamma m f f x ∂m)) := by
    apply energy_tendsto_gamma_bounded_pairing hfin hID hfs hf _ (Lp.aestronglyMeasurable _)
      (cheegerHeat_bounded h hT hCξ ξ hξb)
    simpa only [cheegerEnergy_congr_ae (Lp.coeFn_sub _ _),Pi.sub_def] using hE
  exact ⟨hi, le_of_tendsto_of_tendsto (ht.const_mul 2) (hright.sub hleft)
    (Eventually.of_forall fun n => (hs n).2)⟩
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_VariableDissipationGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_generator {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf Cξ : ℝ} (hCf : 0 ≤ Cf)
    (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    HeatVariableDissipation h (fun x => K-a*G x) f ξ T := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp (|a| *CF)).toNNReal) (D := (Real.exp (|a| *CF)).toNNReal) hm hν
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let R := fun n => (Q.scale (hts n)).resolventLinear
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCf f hfb)
  have hRgraph := cheeger_double_resolvent_graph_tendsto h hf hts ht0
  have hAs (n : ℕ) : As n = R n (R n Af) := by
    apply Q.formGenerator_unique (cheeger_domain_dense h) (hg n)
    rw [he n]
    exact hRgraph.1 n
  have hvs : Tendsto vs atTop (𝓝 f) := hRgraph.2.1.congr (fun n => (he n).symm)
  have hAslim : Tendsto As atTop (𝓝 Af) := hRgraph.2.2.congr (fun n => (hAs n).symm)
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hfS : Sobolev ν (f : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr hf.1
  have hvS (n : ℕ) : Sobolev ν (vs n : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr (hg n).1
  obtain ⟨hE,M,hM⟩ := Q.graph_energy_limits hg hf hvs hAslim
  have hkm : AEStronglyMeasurable (fun x => K-a*G x) ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hkb : ∀ᵐ x ∂ν, |K-a*G x| ≤ |K|+|a| *CG := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
  apply heatVariableDissipation_of_energy_tendsto hnfin hID h hvS hfS hE hM hCξ hξb hkm
    (by positivity : 0 ≤ |K|+|a| *CG) hkb hT
  intro n
  constructor
  · have hc := hrcd.weighted_heat_curvature_continuousOn hN hfull hfin o hV hVB h ξ
      (hg n) hCf (by positivity) (hvb n) (hAb n) hkm hkb T
    exact (hc.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  · exact hHess.rcd_weighted_heat_variable_bounded_test hN hrcd hfull hfin o hF hFb hGb hGc ha h
      (hg n) (hAg n) hCf (by positivity) (by positivity) hCξ
      (hvb n) (hAb n) (hAAb n) hξb hξ0 hT
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_BoundedGraphCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile206
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheeger_bounded_graph_core (h : QuadraticCheegerEnergy m)
    {f A : Lp ℝ 2 m} (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f A) :
    ∃ vs As : ℕ → Lp ℝ 2 m,
      (∀ n,(cheeger_closedQuadraticEnergy h).IsFormGenerator (vs n) (As n)) ∧
      (∀ n,∀ᵐ x ∂m,|vs n x| ≤ (n:ℝ)) ∧
      (∀ n,∀ᵐ x ∂m,|As n x| ≤ 2*(n:ℝ)) ∧
      Tendsto vs atTop (𝓝 f) ∧ Tendsto As atTop (𝓝 A) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := (Q.scale (show (0:ℝ)<1 from zero_lt_one)).resolventLinear
  let b := fun n => (realClip_lipschitz n).compLp (μ := m) (p := 2) (realClip_zero n) (f-A)
  let vs := fun n => R (b n)
  let As := fun n => vs n-b n
  have hb (n : ℕ) : ∀ᵐ x ∂m,|b n x| ≤ (n:ℝ) := by
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) (f-A)] with x hx
    rw [show b n x = realClip n ((f-A) x) from hx]
    exact realClip_abs_le n _
  have hvs (n : ℕ) : ∀ᵐ x ∂m,|vs n x| ≤ (n:ℝ) :=
    cheeger_scaled_resolvent_bounded h zero_lt_one (Nat.cast_nonneg n) (b n) (hb n)
  have hAs (n : ℕ) : ∀ᵐ x ∂m,|As n x| ≤ 2*(n:ℝ) := by
    filter_upwards [Lp.coeFn_sub (vs n) (b n),hvs n,hb n] with x he hv hb
    change |(vs n-b n) x| ≤ _
    rw [he,Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith)
  have hg (n : ℕ) : Q.IsFormGenerator (vs n) (As n) := by
    have H := (Q.scaled_resolvent_iff zero_lt_one (b n) (vs n)).mp rfl
    simpa only [inv_one,one_smul] using H
  have he : R (f-A) = f := by
    apply (Q.scaled_resolvent_iff zero_lt_one (f-A) f).mpr
    simpa only [sub_sub_cancel,inv_one,one_smul] using hf
  have hvlim : Tendsto vs atTop (𝓝 f) := by
    have H := R.continuous.tendsto (f-A) |>.comp (realClip_tendsto_Lp (f-A))
    simpa only [he,Function.comp_def] using H
  refine ⟨vs,As,hg,hvs,hAs,hvlim,?_⟩
  simpa only [sub_sub_cancel] using hvlim.sub (realClip_tendsto_Lp (f-A))
end WeakHessian

end
end InlinedFile206

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_VariableDissipationFullDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_full_generator {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    HeatVariableDissipation h (fun x => K-a*G x) f ξ T := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  obtain ⟨vs,As,hg,hvb,hAb,hvs,hAslim⟩ := cheeger_bounded_graph_core h hf
  have hfS : Sobolev ν (f : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr hf.1
  have hvS (n : ℕ) : Sobolev ν (vs n : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr (hg n).1
  obtain ⟨hE,M,hM⟩ := Q.graph_energy_limits hg hf hvs hAslim
  have hkm : AEStronglyMeasurable (fun x => K-a*G x) ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hkb : ∀ᵐ x ∂ν, |K-a*G x| ≤ |K|+|a| *CG := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
  apply heatVariableDissipation_of_energy_tendsto hnfin hID h hvS hfS hE hM hCξ hξb hkm
    (by positivity : 0 ≤ |K|+|a| *CG) hkb hT
  intro n
  exact hHess.rcd_weighted_heat_variable_generator hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) (Nat.cast_nonneg n) hCξ (hvb n) hξb hξ0 hT
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_VariableDissipationSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_sobolev {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    HeatVariableDissipation h (fun x => K-a*G x) f ξ T := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hfd : cheegerEnergy ν (f : X → ℝ) < ∞ := (identified_sobolev_iff_energy hnfin hID).mp hf
  let fd : Q.domain := ⟨f,hfd⟩
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let us := fun n => (Q.scale (hts n)).resolventLinear f
  let As := fun n => (ts n)⁻¹ • (us n-f)
  have hg (n : ℕ) : Q.IsFormGenerator (us n) (As n) := (Q.scaled_resolvent_iff (hts n) f _).mp rfl
  let ud : ℕ → Q.domain := fun n => ⟨us n,(hg n).1⟩
  have hb (n : ℕ) : Q.realEnergy (ud n) ≤ Q.realEnergy fd :=
    ENNReal.toReal_mono hfd.ne (Q.scaled_resolvent_energy_le (hts n) f)
  have he : Tendsto (fun n => Q.realEnergy (ud n-fd)) atTop (𝓝 0) :=
    Q.form_energy_sub_tendsto (cheeger_domain_dense h) ud fd
      (Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hts ht0 f)
      (Q.realEnergy_quadratic.nonneg fd) hb
      (Q.scaled_resolvent_energy_tendsto (cheeger_domain_dense h) hts ht0 fd)
  have hE : Tendsto (fun n => (cheegerEnergy ν ((us n-f : Lp ℝ 2 ν) : X → ℝ)).toReal) atTop (𝓝 0) := he
  have hus (n : ℕ) : Sobolev ν (us n : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr (hg n).1
  have hkm : AEStronglyMeasurable (fun x => K-a*G x) ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hkb : ∀ᵐ x ∂ν, |K-a*G x| ≤ |K|+|a| *CG := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
  apply heatVariableDissipation_of_energy_tendsto hnfin hID h hus hf hE hb hCξ hξb hkm
    (by positivity : 0 ≤ |K|+|a| *CG) hkb hT
  intro n
  exact hHess.rcd_weighted_heat_variable_full_generator hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) hCξ hξb hξ0 hT
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma heatBridgeError_const (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (c T s : ℝ) :
    heatBridgeError h f ξ (fun _ => c) T s = c*heatBridgeEnergy h f ξ T s := by
  dsimp [heatBridgeError,heatBridgeEnergy]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

lemma heatBridgeEnergy_zero (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T : ℝ) :
    heatBridgeEnergy h f ξ T 0 = ∫ x,ξ x*gamma m (cheegerHeat h T f) (cheegerHeat h T f) x ∂m := by
  simp [heatBridgeEnergy,cheegerHeat_zero]

lemma heatBridgeEnergy_end (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T : ℝ) :
    heatBridgeEnergy h f ξ T T = ∫ x,cheegerHeat h T ξ x*gamma m f f x ∂m := by
  simp [heatBridgeEnergy,cheegerHeat_zero]

variable [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma WeakHessianUpperBound.heatBridge_integrable {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable (heatBridgeEnergy h f ξ T) volume 0 T := by
  let C := CG+(|K|+1)/a
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hGH (x : X) : G x ≤ C := by
    have H := (le_abs_self (G x)).trans (hGb x)
    have H' : 0 ≤ (|K|+1)/a := by positivity
    dsimp [C]; linarith
  have hH := hHess.mono_bounded hfin hGc.aestronglyMeasurable aestronglyMeasurable_const hGb
    (fun _ : X => (abs_of_nonneg hC).le) hGH
  have HC := (hH.rcd_weighted_heat_variable_sobolev hN hrcd hfull hfin o hF hFb
    (fun _ : X => (abs_of_nonneg hC).le) continuous_const ha.le h hf hCξ hξb hξ0 hT).1
  have hk : K-a*C ≠ 0 := by
    have he : a*C = a*CG+(|K|+1) := by dsimp [C]; field_simp
    rw [he]
    have : 0 ≤ a*CG := mul_nonneg ha.le hCG
    linarith [le_abs_self K]
  change IntervalIntegrable (heatBridgeError h f ξ (fun _ => K-a*C) T) volume 0 T at HC
  simp only [funext (heatBridgeError_const h f ξ (K-a*C) T)] at HC
  have H := HC.const_mul (K-a*C)⁻¹
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  simp only [← mul_assoc,inv_mul_cancel₀ hk,one_mul]

omit [SigmaFinite m] in
lemma heatBridgeError_decompose
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m,|ξ x| ≤ Cξ)
    {J : X → ℝ} (hJm : AEStronglyMeasurable J m) {B : ℝ} (hJb : ∀ᵐ x ∂m,|J x| ≤ B)
    (κ a T : ℝ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    heatBridgeError h f ξ (fun x => κ-a*J x) T s =
      κ*heatBridgeEnergy h f ξ T s-a*heatBridgeError h f ξ J T s := by
  have hfs : Sobolev m (cheegerHeat h (T-s) f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h (sub_nonneg.mpr hs.2) f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  have hg := integrable_gamma hfin hfs hfs
  have hρb := cheegerHeat_bounded h hs.1 hCξ ξ hξb
  have hρm := (Lp.memLp (cheegerHeat h s ξ)).aestronglyMeasurable
  have hi : Integrable (fun x => cheegerHeat h s ξ x*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x) m :=
    hg.bdd_mul hρm (by simpa only [Real.norm_eq_abs] using hρb)
  have hji : Integrable (fun x => (cheegerHeat h s ξ x*J x)*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x) m := by
    apply hg.bdd_mul (hρm.mul hJm) (c := Cξ*max B 0)
    filter_upwards [hρb,hJb] with x hρ hJ
    change |cheegerHeat h s ξ x*J x| ≤ _
    rw [abs_mul]
    exact mul_le_mul hρ (hJ.trans (le_max_left _ _)) (abs_nonneg _) hCξ
  dsimp [heatBridgeError,heatBridgeEnergy]
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hi.const_mul κ) (hji.const_mul a)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DuhamelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set MeasureTheory
open scoped Topology

lemma duhamel_signed_error {E D : ℝ → ℝ} {T M κ a : ℝ}
    (hT : 0 ≤ T) (hM : 0 < M)
    (hEi : IntervalIntegrable E volume 0 T)
    (hlo : ∀ s ∈ Icc 0 T, E 0 ≤ M*E s)
    (hhi : ∀ s ∈ Icc 0 T, E s ≤ M*E T)
    (hduh : 2*(κ*(∫ s in 0..T,E s)-a*(∫ s in 0..T,D s)) ≤ E T-E 0) :
    (1+2*max κ 0*T/M)*E 0 ≤
      (1+2*max (-κ) 0*T*M)*E T+2*a*(∫ s in 0..T,D s) := by
  have hl : T*(E 0/M) ≤ ∫ s in 0..T,E s := by
    have H := intervalIntegral.integral_mono_on hT intervalIntegrable_const hEi
      (fun s hs => (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hlo s hs))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using H
  have hh : (∫ s in 0..T,E s) ≤ T*(M*E T) := by
    have H := intervalIntegral.integral_mono_on hT hEi intervalIntegrable_const hhi
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using H
  have hk : max κ 0-max (-κ) 0 = κ := by
    rcases le_total 0 κ with h|h
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
    · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]; ring
  have HL := mul_le_mul_of_nonneg_left hl (le_max_right κ 0)
  have HH := mul_le_mul_of_nonneg_left hh (le_max_right (-κ) 0)
  have key' : max κ 0*T/M*E 0-max (-κ) 0*T*M*E T ≤ κ*(∫ s in 0..T,E s) := by
    calc
      _ = max κ 0*(T*(E 0/M))-max (-κ) 0*(T*(M*E T)) := by ring
      _ ≤ max κ 0*(∫ s in 0..T,E s)-max (-κ) 0*(∫ s in 0..T,E s) := sub_le_sub HL HH
      _ = κ*(∫ s in 0..T,E s) := by rw [← sub_mul,hk]
  simp only [div_eq_mul_inv] at key' ⊢
  nlinarith only [hduh,key']

lemma duhamel_signed_error_ratio {E D : ℝ → ℝ} {T M κ a : ℝ}
    (hT : 0 ≤ T) (hM : 0 < M)
    (hEi : IntervalIntegrable E volume 0 T)
    (hlo : ∀ s ∈ Icc 0 T, E 0 ≤ M*E s)
    (hhi : ∀ s ∈ Icc 0 T, E s ≤ M*E T)
    (hduh : 2*(κ*(∫ s in 0..T,E s)-a*(∫ s in 0..T,D s)) ≤ E T-E 0) :
    ((1+2*max κ 0*T/M)/(1+2*max (-κ) 0*T*M))*E 0 ≤
      E T+(2*a/(1+2*max (-κ) 0*T*M))*(∫ s in 0..T,D s) := by
  have hp : 0 < 1+2*max (-κ) 0*T*M := by positivity
  have H := duhamel_signed_error hT hM hEi hlo hhi hduh
  have H' := div_le_div_of_nonneg_right H hp.le
  calc
    _ = ((1+2*max κ 0*T/M)*E 0)/(1+2*max (-κ) 0*T*M) := by ring
    _ ≤ ((1+2*max (-κ) 0*T*M)*E T+2*a*(∫ s in 0..T,D s))/(1+2*max (-κ) 0*T*M) := H'
    _ = _ := by rw [add_div,mul_div_cancel_left₀ _ hp.ne']; ring

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LocalizedGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.localized_heat_gradient_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 < a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    let M := Real.exp (2*(|K|+a*CG)*T)
    let κ := K-a*c
    let E := heatBridgeEnergy h f ξ T
    let D := heatBridgeError h f ξ (fun x => max (G x-c) 0) T
    IntervalIntegrable E volume 0 T ∧ IntervalIntegrable D volume 0 T ∧
      ((1+2*max κ 0*T/M)/(1+2*max (-κ) 0*T*M))*E 0 ≤
        E T+(2*a/(1+2*max (-κ) 0*T*M))*(∫ s in 0..T,D s) := by
  dsimp only
  let ν := exponentialMeasure m (fun x => a*F x)
  let J := fun x => max (G x-c) 0
  let κ := K-a*c
  let E := heatBridgeEnergy h f ξ T
  let D := heatBridgeError h f ξ J T
  let Z := heatBridgeError h f ξ (fun x => κ-a*J x) T
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hJc : Continuous J := (hGc.sub continuous_const).max continuous_const
  have hJb (x : X) : |J x| ≤ CG+|c| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [(abs_le.mp (hGb x)).2,neg_le_abs c]
    · positivity
  have hmaxb (x : X) : |max (G x) c| ≤ CG+|c| := abs_max_le_of_abs_le (hGb x)
  have hHmax := hHess.mono_bounded hfin hGc.aestronglyMeasurable
    (hGc.max continuous_const).aestronglyMeasurable hGb hmaxb (fun x => le_max_left (G x) c)
  have hki (x : X) : K-a*max (G x) c = κ-a*J x := by
    dsimp [κ,J]
    rcases le_total c (G x) with hc|hc
    · rw [max_eq_left hc,max_eq_left (sub_nonneg.mpr hc)]; ring
    · rw [max_eq_right hc,max_eq_right (sub_nonpos.mpr hc)]; ring
  have HZ := hHmax.rcd_weighted_heat_variable_sobolev hN hrcd hfull hfin o hF hFb hmaxb
    (hGc.max continuous_const) ha.le h hf hCξ hξb hξ0 hT
  simp_rw [hki] at HZ
  change IntervalIntegrable Z volume 0 T ∧ 2*(∫ s in 0..T,Z s) ≤ _ at HZ
  have hEi := hHess.heatBridge_integrable hN hrcd hfull hfin o hF hFb hGb hGc ha h hf hCξ hξb hξ0 hT
  change IntervalIntegrable E volume 0 T at hEi
  have hdecomp (s : ℝ) (hs : s ∈ Icc 0 T) : Z s = κ*E s-a*D s :=
    heatBridgeError_decompose hnfin hID h hf hCξ hξb hJc.aestronglyMeasurable
      (ae_of_all _ hJb) κ a T hs
  have hDi : IntervalIntegrable D volume 0 T := by
    have H := ((hEi.const_mul κ).sub HZ.1).const_mul a⁻¹
    apply (intervalIntegrable_congr ?_).mp H
    intro s hs
    rw [uIoc_of_le hT] at hs
    change a⁻¹*(κ*E s-Z s) = D s
    rw [hdecomp s ⟨hs.1.le,hs.2⟩]
    field_simp
    ring
  refine ⟨hEi,hDi,?_⟩
  have hint : (∫ s in 0..T,Z s) = κ*(∫ s in 0..T,E s)-a*(∫ s in 0..T,D s) := by
    calc
      _ = ∫ s in 0..T,κ*E s-a*D s := intervalIntegral.integral_congr (by
        rw [uIcc_of_le hT]; exact hdecomp)
      _ = _ := by rw [intervalIntegral.integral_sub (hEi.const_mul κ) (hDi.const_mul a),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hduh := HZ.2
  rw [hint,← heatBridgeEnergy_end h f ξ T,← heatBridgeEnergy_zero h f ξ T] at hduh
  apply duhamel_signed_error_ratio hT (Real.exp_pos _) hEi
    (fun s hs => (hHess.heatBridge_bounds hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hCξ hξb hξ0 hs).1)
    (fun s hs => (hHess.heatBridge_bounds hN hrcd hfull hfin o hF hFb hGb hGc ha.le h hf hCξ hξb hξ0 hs).2)
    hduh

end WeakHessian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient_oai.{u_1} := @OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient_oai.{u_1}
