-- Prove2me | solution 1 for OAI.WeakHessian.RCD.generator_entropy_subdifferential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:00:49.701659+00:00
-- url     : https://prove2.me/submissions/2cda7a29-5696-4341-ab3e-5a7e5265cd1f

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_compact_sobolev_entropy_subdifferential

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
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_QuadraticCostIncrement
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
namespace WeakHessianTransport
open Set Filter MeasureTheory CompactlySupported
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma isCompact_lipschitz_norm_ball (R : ℝ≥0) {M : ℝ} (_hM : 0 ≤ M) :
    IsCompact {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ M} := by
  let S := {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ M}
  have hS : IsClosed S :=
    ((isClosed_setOfPred_lipschitzWith R).preimage (continuous_pi fun x : X => continuous_eval_const x)).inter
      (isClosed_le continuous_norm continuous_const)
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  have hb : IsClosed (e '' S) := e.toHomeomorph.isClosedMap S hS
  have hc : IsCompact (e '' S) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (Icc (-M) M) isCompact_Icc (e '' S) hb
    · rintro f x ⟨φ,hφ,rfl⟩
      exact abs_le.mp ((φ.norm_coe_le_norm x).trans hφ.2)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (R:ℝ)*r)
        (by simpa only [mul_zero, id_eq] using
          (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (R:ℝ))
      intro x y f
      obtain ⟨φ,hφ,he⟩ := f.property
      have hed : (f.val : X → ℝ) = φ := by rw [← he]; rfl
      change dist (f.val x) (f.val y) ≤ (R:ℝ)*dist x y
      rw [congrFun hed x,congrFun hed y]
      exact hφ.1.dist_le_mul x y
  exact e.toHomeomorph.isCompact_image.mp hc

end WeakHessianTransport

end
end InlinedFile0

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
lemma BoundedTracks.integrable_length_sq {π : Measure (Curve X)} [IsFiniteMeasure π]
    (hb : BoundedTracks π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  apply (integrable_const ((2*R)^2)).mono'
    (((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).pow 2).aestronglyMeasurable
  filter_upwards [hb] with γ hγ
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mpr
  have H := dist_triangle (γ timeZero) o (γ timeOne)
  rw [dist_comm o] at H
  linarith [hγ timeZero,hγ timeOne]

end WeakHessian

end

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
lemma squareDensity_integral {n : Measure X} {w : X → ℝ} (hw : Measurable w) (f : X → ℝ) :
    (∫ x, f x ∂squareDensityMeasure n w) = ∫ x, w x^2*f x ∂n := by
  rw [squareDensityMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integrable {n : Measure X} {w f : X → ℝ} (hw : Measurable w) :
    Integrable f (squareDensityMeasure n w) ↔ Integrable (fun x => w x^2*f x) n := by
  rw [squareDensityMeasure,integrable_withDensity_iff_integrable_smul₀'
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_mass {n : Measure X} {w : X → ℝ} (hw : Measurable w)
    [IsProbabilityMeasure (squareDensityMeasure n w)] : (∫ x, w x^2 ∂n) = 1 := by
  have H := squareDensity_integral (n := n) hw (fun _ => (1:ℝ))
  simpa using H.symm

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
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_DensityConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile8
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma integral_sq_sub_le {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x, |f x^2-g x^2| ∂m) ≤ ‖hf.toLp f-hg.toLp g‖*‖hf.toLp f+hg.toLp g‖ := by
  have H := integral_mul_le_sqrt_integral_sq (hf.sub hg).norm (hf.add hg).norm
  simp only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,sq_abs] at H
  have hi : (∫ x,|f x^2-g x^2| ∂m) = ∫ x,|f x-g x| *|f x+g x| ∂m := by
    congr 1
    funext x
    rw [← abs_mul]
    congr 1
    ring
  rw [hi]
  have hs : (∫ x,(f x-g x)^2 ∂m) = ‖hf.toLp f-hg.toLp g‖^2 := by
    rw [← MemLp.toLp_sub hf hg]
    exact (norm_toLp_sq_eq_integral (hf.sub hg)).symm
  have ha : (∫ x,(f x+g x)^2 ∂m) = ‖hf.toLp f+hg.toLp g‖^2 := by
    rw [← MemLp.toLp_add hf hg]
    exact (norm_toLp_sq_eq_integral (hf.add hg)).symm
  simpa only [hs,ha,Real.sqrt_sq (norm_nonneg _)] using H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_L1_tendsto {ι : Type*} {l : Filter ι} {fs : ι → X → ℝ} {w : X → ℝ}
    (hfs : ∀ i, MemLp (fs i) 2 m) (hw : MemLp w 2 m)
    (hF : Tendsto (fun i => (hfs i).toLp (fs i)) l (𝓝 (hw.toLp w))) :
    Tendsto (fun i => ∫ x, |fs i x^2-w x^2| ∂m) l (𝓝 0) := by
  have H := ((hF.sub (tendsto_const_nhds (x := hw.toLp w))).norm).mul ((hF.add (tendsto_const_nhds (x := hw.toLp w))).norm)
  simp only [sub_self,norm_zero,zero_mul] at H
  exact squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) (fun i => integral_sq_sub_le (hfs i) hw) H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_pairing_bound {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m) {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m)
    {M : ℝ} (hM : ∀ᵐ x ∂m, ‖φ x‖ ≤ M) :
    |(∫ x,φ x ∂squareDensityMeasure m f)-(∫ x,φ x ∂squareDensityMeasure m g)| ≤
      M*(∫ x,|f x^2-g x^2| ∂m) := by
  rw [squareDensity_integral hf,squareDensity_integral hg]
  have hi : Integrable (fun x => f x^2) m := hf2.integrable_sq
  have hj : Integrable (fun x => g x^2) m := hg2.integrable_sq
  have hif : Integrable (fun x => f x^2*φ x) m := by simpa only [mul_comm] using hi.bdd_mul hφ hM
  have hig : Integrable (fun x => g x^2*φ x) m := by simpa only [mul_comm] using hj.bdd_mul hφ hM
  rw [← integral_sub hif hig,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x,‖f x^2*φ x-g x^2*φ x‖ ∂m := norm_integral_le_integral_norm _
    _ ≤ ∫ x,M*|f x^2-g x^2| ∂m := by
      apply integral_mono_ae (hif.sub hig).norm ((hi.sub hj).abs.const_mul M)
      filter_upwards [hM] with x hx
      simp only [Pi.sub_apply,← sub_mul,norm_mul,Real.norm_eq_abs] at *
      nlinarith [abs_nonneg (f x^2-g x^2)]
    _ = _ := integral_const_mul _ _

lemma squareDensity_tendsto_probability {fs : ℕ → X → ℝ} {w : X → ℝ}
    (hfm : ∀ n, Measurable (fs n)) (hwm : Measurable w)
    (hfs : ∀ n, MemLp (fs n) 2 m) (hw : MemLp w 2 m)
    (hP : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fs n)))
    (hW : IsProbabilityMeasure (squareDensityMeasure m w))
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.toLp w))) :
    Tendsto (β := ProbabilityMeasure X) (fun n => squareDensityProbability m (fs n) (hP n)) atTop
      (𝓝 (squareDensityProbability m w hW)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have H := (squareDensity_L1_tendsto hfs hw hF).const_mul ‖φ‖
  simp only [mul_zero] at H
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ H
  intro n
  exact squareDensity_pairing_bound (hfm n) hwm (hfs n) hw φ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => φ.norm_coe_le_norm x)
end WeakHessian

end
end InlinedFile8

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile9
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma LipschitzWith.integrable_supported_ball {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {μ : Measure X} [IsFiniteMeasure μ]
    (o : X) (R : ℝ≥0) (hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R) : Integrable φ μ := by
  apply Integrable.of_bound hφ.continuous.aestronglyMeasurable (‖φ o‖+(L:ℝ)*R)
  filter_upwards [hs] with x hx
  have H := hφ.dist_le_mul x o
  have hd : dist x o ≤ R := hx
  calc
    ‖φ x‖ ≤ ‖φ o‖+‖φ x-φ o‖ := by simpa [add_comm, norm_sub_rev] using norm_le_norm_add_norm_sub (φ o) (φ x)
    _ ≤ _ := by rw [← dist_eq_norm]; exact add_le_add le_rfl (H.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg))

end WeakHessian

end
end InlinedFile9

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
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_GammaLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile16
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma abs_integral_mul_le_L2_norm {a b : X → ℝ} (ha : MemLp a 2 m) (hb : MemLp b 2 m) :
    |∫ x,a x*b x ∂m| ≤ ‖ha.toLp a‖*‖hb.toLp b‖ := by
  have H : (∫ x,a x*b x ∂m) = ⟪ha.toLp a,hb.toLp b⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [H]
  exact abs_real_inner_le_norm _ _

end WeakHessian

end
end InlinedFile16

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NoncompactCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile36
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [TopologicalSpace.SeparableSpace X] in
lemma hopf_dual_le_planEnergy (μ ν : ProbabilityMeasure X)
    {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hi : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π)
    (h0 : interpolation π timeZero = (μ:Measure X))
    (h1 : interpolation π timeOne = (ν:Measure X)) (f : X →ᵇ ℝ) :
    (∫ x, WeakHessianTransport.hopfLax f 1 x ∂(μ:Measure X))-(∫ x,f x ∂(ν:Measure X)) ≤ planEnergy π/2 := by
  let Q := WeakHessianTransport.boundedHopfMap f 1
  have he : (Q:X → ℝ) = WeakHessianTransport.hopfLax f 1 :=
    funext (WeakHessianTransport.boundedHopfMap_apply_pos f (by norm_num))
  have iQ : Integrable (fun γ : Curve X => Q (γ timeZero)) π :=
    Integrable.of_bound (Q.continuous.comp (continuous_eval_const timeZero)).aestronglyMeasurable ‖Q‖
      (ae_of_all _ fun γ => Q.norm_coe_le_norm (γ timeZero))
  have iF : Integrable (fun γ : Curve X => f (γ timeOne)) π :=
    Integrable.of_bound (f.continuous.comp (continuous_eval_const timeOne)).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun γ => f.norm_coe_le_norm (γ timeOne))
  have H : (∫ γ,Q (γ timeZero)-f (γ timeOne) ∂π) ≤ planEnergy π/2 := by
    apply le_trans (integral_mono (iQ.sub iF) (hi.div_const 2) ?_)
    · exact le_of_eq (integral_div _ _)
    · intro γ
      rw [he]
      have h := WeakHessianTransport.hopfLax_le_objective
        (fun x => (WeakHessianTransport.boundedContinuous_bounds f x).1)
        (by norm_num : (0:ℝ)<1) (γ timeZero) (γ timeOne)
      simp only [WeakHessianTransport.hopfObjective,mul_one] at h
      dsimp only [Pi.sub_apply]
      linarith
  rw [integral_sub iQ iF] at H
  have eq0 : (∫ γ,Q (γ timeZero) ∂π) = ∫ x,Q x ∂(μ:Measure X) := by
    rw [← h0]
    exact (integral_map (continuous_eval_const timeZero).measurable.aemeasurable Q.continuous.aestronglyMeasurable).symm
  have eq1 : (∫ γ,f (γ timeOne) ∂π) = ∫ x,f x ∂(ν:Measure X) := by
    rw [← h1]
    exact (integral_map (continuous_eval_const timeOne).measurable.aemeasurable f.continuous.aestronglyMeasurable).symm
  rw [eq0,eq1] at H
  simpa only [he] using H

lemma exists_coupling_of_energy_limit (μ ν : ProbabilityMeasure X)
    (μs : ℕ → ProbabilityMeasure X) (hμs : Tendsto μs atTop (𝓝 μ))
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (hi : ∀ n, Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (ps n:Measure (Curve X)))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = (μs n:Measure X))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    {E : ℝ} (hE : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E)) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsCoupling q μ ν ∧ QuadraticTransportCost q ≤ ENNReal.ofReal E := by
  obtain ⟨q,hq,hq0,hq1,hcost⟩ := WeakHessianTransport.exists_proper_coupling_cost_of_hopf_bound
    (μ:Measure X) (ν:Measure X) E (by
      intro f hf
      have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμs (WeakHessianTransport.boundedHopfMap f 1)
      have he : (WeakHessianTransport.boundedHopfMap f 1:X → ℝ) = WeakHessianTransport.hopfLax f 1 :=
        funext (WeakHessianTransport.boundedHopfMap_apply_pos f (by norm_num))
      simp only [he] at H
      exact le_of_tendsto_of_tendsto' (H.sub_const _) (hE.div_const 2)
        (fun n => hopf_dual_le_planEnergy (μs n) ν (hi n) (h0 n) (h1 n) f))
  exact ⟨q,hq,⟨hq0,hq1⟩,hcost⟩

lemma planEnergy_le_coupling_of_restricted_contact
    {π : Measure (Curve X)} [IsProbabilityMeasure π] {q : Measure (X×X)}
    (hiq : QuadraticTransportCost q ≠ ∞)
    (μ ν : ProbabilityMeasure X) (hq : IsCoupling q μ ν)
    (h1 : interpolation π timeOne = (ν:Measure X))
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hiφπ : Integrable φ (interpolation π timeZero)) (hiφμ : Integrable φ (μ:Measure X))
    (hiψν : Integrable ψ (ν:Measure X))
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ x y, y ∈ S → φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    planEnergy π-(∫ p : X×X,dist p.1 p.2^2 ∂q) ≤
      2*((∫ x,φ x ∂interpolation π timeZero)-(∫ x,φ x ∂(μ:Measure X))) := by
  have iφπ := (integrable_map_measure hφ.aestronglyMeasurable (continuous_eval_const timeZero).measurable.aemeasurable).mp hiφπ
  have iψπ := (integrable_map_measure hψ.aestronglyMeasurable (continuous_eval_const timeOne).measurable.aemeasurable).mp (h1 ▸ hiψν)
  have iφq := (integrable_map_measure hφ.aestronglyMeasurable measurable_fst.aemeasurable).mp (hq.1 ▸ hiφμ)
  have iψq := (integrable_map_measure hψ.aestronglyMeasurable measurable_snd.aemeasurable).mp (hq.2 ▸ hiψν)
  simp only [Function.comp_def] at iφπ iψπ iφq iψq
  have hsq : ∀ᵐ p : X×X ∂q, p.2 ∈ S :=
    (ae_map_iff measurable_snd.aemeasurable hS).mp (hq.2 ▸ hs)
  have H : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂π) = planEnergy π/2 := by
    rw [integral_congr_ae hc]; exact integral_div _ _
  have J : (∫ p : X×X,φ p.1+ψ p.2 ∂q) ≤ (∫ p : X×X,dist p.1 p.2^2 ∂q)/2 := by
    apply (integral_mono_ae (iφq.add iψq) ((integrable_squared_distance_of_cost hiq).div_const 2)
      (hsq.mono fun p hp => hd p.1 p.2 hp)).trans
    exact le_of_eq (integral_div _ _)
  rw [integral_add iφπ iψπ,
    ← integral_map (continuous_eval_const timeZero).measurable.aemeasurable hφ.aestronglyMeasurable,
    ← integral_map (continuous_eval_const timeOne).measurable.aemeasurable hψ.aestronglyMeasurable] at H
  change (∫ x,φ x ∂interpolation π timeZero)+(∫ x,ψ x ∂interpolation π timeOne) = _ at H
  rw [h1] at H
  rw [integral_add iφq iψq,
    ← integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hψ.aestronglyMeasurable,hq.1,hq.2] at J
  linarith
end WeakHessian

end
end InlinedFile36

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_QuadraticPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile25
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma compactCTransform_attained {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (x : X) :
    ∃ y ∈ S, compactCTransform S ψ x = dist x y^2/2-ψ y ∧
      ∀ z ∈ S, compactCTransform S ψ x ≤ dist x z^2/2-ψ z := by
  obtain ⟨y,hy,hm⟩ := hS.exists_isMinOn hne (((continuous_const.dist continuous_id).pow 2).div_const 2 |>.continuousOn |>.sub hψ)
  have he : compactCTransform S ψ x = dist x y^2/2-ψ y := by
    apply IsLeast.csInf_eq
    exact ⟨mem_image_of_mem _ hy,by rintro _ ⟨z,hz,rfl⟩; exact hm hz⟩
  exact ⟨y,hy,he,fun z hz => he ▸ hm hz⟩

lemma compactCTransform_le {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (x : X) {y : X} (hy : y ∈ S) :
    compactCTransform S ψ x+ψ y ≤ dist x y^2/2 := by
  obtain ⟨z,hz,he,hm⟩ := compactCTransform_attained hS hne hψ x
  linarith [hm y hy]

lemma half_cost_difference_bound (o x z y : X) {R : ℝ} (hy : dist y o ≤ R) :
    |dist x y^2/2-dist z y^2/2| ≤
      ((dist x o+dist z o)/2+R)*dist x z := by
  have ha := abs_dist_sub_le x z y
  have hb : dist x y+dist z y ≤ dist x o+dist z o+2*R := by
    have hx := dist_triangle x o y
    have hz := dist_triangle z o y
    rw [dist_comm o y] at hx hz
    linarith
  have hfact : dist x y^2/2-dist z y^2/2 = (dist x y-dist z y)*(dist x y+dist z y)/2 := by ring
  rw [hfact,abs_div,abs_mul,abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  have H := mul_le_mul ha hb (add_nonneg dist_nonneg dist_nonneg) dist_nonneg
  nlinarith

lemma compactCTransform_difference_bound {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (o : X) {R : ℝ}
    (hs : S ⊆ Metric.closedBall o R) (x z : X) :
    |compactCTransform S ψ x-compactCTransform S ψ z| ≤
      ((dist x o+dist z o)/2+R)*dist x z := by
  have one (x z : X) : compactCTransform S ψ x-compactCTransform S ψ z ≤
      ((dist x o+dist z o)/2+R)*dist x z := by
    obtain ⟨y,hy,he,hm⟩ := compactCTransform_attained hS hne hψ z
    have H := compactCTransform_le hS hne hψ x hy
    have B := (le_abs_self (dist x y^2/2-dist z y^2/2)).trans (half_cost_difference_bound o x z y (hs hy))
    linarith
  apply abs_le.mpr
  constructor
  · have H := one z x
    rw [add_comm (dist z o),dist_comm z x] at H
    linarith
  · exact one x z

lemma compactCTransform_contact {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {φ ψ : X → ℝ} (hψ : ContinuousOn ψ S)
    (hdual : ∀ x y,φ x+ψ y ≤ dist x y^2/2) {x y : X} (hy : y ∈ S)
    (hc : φ x+ψ y = dist x y^2/2) : compactCTransform S ψ x = φ x := by
  obtain ⟨z,hz,he,hm⟩ := compactCTransform_attained hS hne hψ x
  have H := hdual x z
  have H' := compactCTransform_le hS hne hψ x hy
  linarith
end WeakHessian

end
end InlinedFile25

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_QuadraticGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile26
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma QuadraticLipschitzBound.lipschitzOn_ball {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 ≤ R) (a : X) (r : ℝ≥0) :
    LipschitzOnWith (NNReal.mk (dist a o+R+r) (by positivity)) f (Metric.closedBall a r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  apply (hf x y).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  have H := dist_triangle x a o
  have J := dist_triangle y a o
  change dist x a ≤ r at hx
  change dist y a ≤ r at hy
  change (dist x o+dist y o)/2+R ≤ dist a o+R+r
  linarith

lemma QuadraticLipschitzBound.continuous {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 ≤ R) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hf.lipschitzOn_ball hR x 1).continuousOn.continuousAt
    (Metric.closedBall_mem_nhds x (by norm_num))

lemma QuadraticLipschitzBound.deriv_comp_bound {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) (γ : Curve X) (t : ℝ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      ENNReal.ofReal (dist (evalReal γ t) o+R)*metricSpeed γ t := by
  let a := evalReal γ t
  have heps (ε : ℝ) (hε : 0 < ε) :
      ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
        ENNReal.ofReal (dist a o+R+ε)*metricSpeed γ t := by
    obtain ⟨g,hg,heg⟩ := (hf.lipschitzOn_ball hR.le a (NNReal.mk ε hε.le)).extend_real
    have H := deriv_comp_le_metricSpeed_all hg γ t
    have he : (fun s => f (evalReal γ s)) =ᶠ[𝓝 t] (fun s => g (evalReal γ s)) := by
      have ht : Tendsto (evalReal γ) (𝓝 t) (𝓝 a) := (continuous_evalReal.comp (continuous_const.prodMk continuous_id)).continuousAt
      filter_upwards [ht (Metric.closedBall_mem_nhds a hε)] with s hs
      exact heg hs
    rw [← he.deriv_eq] at H
    change ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      (↑(NNReal.mk (dist a o+R+ε) (by positivity)) : ℝ≥0∞)*metricSpeed γ t at H
    rw [← ENNReal.ofReal_eq_coe_nnreal] at H
    exact H
  have hp : ENNReal.ofReal (dist a o+R) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (dist a o+R+ε)*metricSpeed γ t)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (dist a o+R)*metricSpeed γ t)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inl hp)
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero,id_eq] using (tendsto_const_nhds (x := dist a o+R)).add (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (eventually_mem_nhdsWithin.mono fun ε hε => heps ε hε)

lemma QuadraticLipschitzBound.comp_ac {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 ≤ R) {γ : Curve X} (hγ : IsAC2 γ) :
    AbsolutelyContinuousOnInterval (fun s => f (evalReal γ s)) 0 1 := by
  obtain ⟨r,hr,hs⟩ := (isCompact_range γ.continuous).isBounded.subset_closedBall_lt 0 o
  apply ac_comp_lipschitzOn hγ.absolutelyContinuous (hf.lipschitzOn_ball hR o ⟨r,hr.le⟩)
  intro s _hs
  exact hs (mem_range_self (clampTime s))

lemma QuadraticLipschitzBound.endpoint_bound {o : X} {R : ℝ} {f : X → ℝ}
    (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) {γ : Curve X} (hγ : IsAC2 γ) :
    ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)| ≤
      ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (dist (evalReal γ t) o+R)*metricSpeed γ t := by
  have hac := hf.comp_ac hR.le hγ
  calc
    _ = ‖∫ t in Icc (0:ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
      rw [← ofReal_norm,Real.norm_eq_abs,integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one,hac.integral_deriv_eq_sub]
      simp [evalReal,clampTime,timeOne,timeZero]
      rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := lintegral_mono (fun t => by
      simpa only [← ofReal_norm,Real.norm_eq_abs] using hf.deriv_comp_bound hR γ t)

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma QuadraticLipschitzBound.upperGradient (hfin : FiniteOnBoundedSets m)
    {o : X} {R : ℝ} {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) :
    IsLocalWeakUpperGradient m f (fun x => dist x o+R) := by
  refine ⟨?_,ae_of_all _ fun x => by positivity,?_⟩
  · intro a r _hr
    let : IsFiniteMeasure (m.restrict (Metric.ball a r)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
    apply MemLp.of_bound (by fun_prop) (r+dist a o+R)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ dist x o+R)]
    have H := dist_triangle x a o
    change dist x a < r at hx
    linarith
  · intro π hπ _hb
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1] with γ hγ
    exact hf.endpoint_bound hR hγ

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma QuadraticLipschitzBound.localSobolev (hfin : FiniteOnBoundedSets m)
    {o : X} {R : ℝ} {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) :
    LocalSobolev m f := by
  refine ⟨?_,(hf.upperGradient hfin hR).exists_minimal (hf.continuous hR.le).aemeasurable hfin⟩
  intro a r hr
  obtain ⟨g,hg,he⟩ := (hf.lipschitzOn_ball hR.le a ⟨r,hr.le⟩).extend_real
  apply (memLp_congr_ae ?_).mp ((localSobolev_of_lipschitz hfin hg).1 a r hr)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (he (show dist x a ≤ r from le_of_lt hx)).symm

lemma QuadraticLipschitzBound.gradient_le (hfin : FiniteOnBoundedSets m)
    {o : X} {R : ℝ} {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hR : 0 < R) :
    ∀ᵐ x ∂m, weakGradient m f x ≤ dist x o+R :=
  (weakGradient_isMinimal (hf.localSobolev hfin hR).2).2 _ (hf.upperGradient hfin hR)

end WeakHessian

end
end InlinedFile26

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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

section

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma rootCutoff_lipschitz (o : X) (R : ℝ) : LipschitzWith 1 (rootCutoff o R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rootCutoff o R x) (rootCutoff o R y) ≤
        dist (R+2-dist x o) (R+2-dist y o) := by
      simpa only [NNReal.coe_one,one_mul,rootCutoff] using
        (rootClip_lipschitz 1).dist_le_mul (R+2-dist x o) (R+2-dist y o)
    _ = dist (dist x o) (dist y o) := dist_sub_left _ _ _
    _ ≤ 1*dist x y := by simpa using dist_dist_dist_le_left x y o

lemma rootCutoff_nonneg (o : X) (R : ℝ) (x : X) : 0 ≤ rootCutoff o R x := rootClip_nonneg _ _
lemma rootCutoff_le_one (o : X) (R : ℝ) (x : X) : rootCutoff o R x ≤ 1 := rootClip_le zero_le_one _
lemma rootCutoff_one {o : X} {R : ℝ} {x : X} (hx : x ∈ Metric.closedBall o R) :
    rootCutoff o R x = 1 := by
  have H : dist x o ≤ R := hx
  simp only [rootCutoff,rootClip,min_eq_left (by linarith : 1 ≤ R+2-dist x o),max_eq_right zero_le_one]
lemma rootCutoff_support (o : X) (R : ℝ) : tsupport (rootCutoff o R) ⊆ Metric.closedBall o (R+2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  have H : R+2 < dist x o := lt_of_not_ge hh
  have he : rootCutoff o R x = 0 := by
    apply max_eq_left
    exact (min_le_right _ _).trans (by linarith)
  exact hx he

end

end WeakHessian

end
end InlinedFile6

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile18
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma toLp_tendsto_of_domination {fs : ℕ → X → ℝ} {f D : X → ℝ}
    (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m) (hD : MemLp D 2 m)
    (hb : ∀ n, ∀ᵐ x ∂m, ‖fs n x‖ ≤ ‖D x‖)
    (hT : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f)) := by
  have hi : UnifIntegrable fs 2 m := by
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := hD.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    apply le_trans (eLpNorm_mono_ae ?_) (hd s hs hms)
    filter_upwards [hb n] with x hx
    by_cases h : x ∈ s
    · simpa only [indicator_of_mem h] using hx
    · simp only [indicator_of_notMem h,le_refl]
  have ht : UnifTight fs 2 m := by
    intro ε hε
    obtain ⟨s,hsm,hs,hd⟩ :=
      (unifTight_const (ι := ℕ) (by norm_num) hD).exists_measurableSet_indicator (ENNReal.coe_ne_zero.mpr hε.ne')
    refine ⟨s,hs.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono_ae ?_) (hd n)
    filter_upwards [hb n] with x hx
    by_cases h : x ∈ sᶜ
    · simpa only [indicator_of_mem h] using hx
    · simp only [indicator_of_notMem h,le_refl]
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hfs f hf).mpr
    (tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hfs n).aestronglyMeasurable) hf hi ht hT)

omit [CompleteSpace X] in
lemma CurvatureDimension.integral_gamma_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X)
    {fs : ℕ → X → ℝ} {f g : X → ℝ}
    (hfs : ∀ n, Sobolev m (fs n)) (hf : Sobolev m f) (hg : Sobolev m g)
    (hT : Tendsto (fun n => (hfs n).1.toLp (fs n)) atTop (𝓝 (hf.1.toLp f)))
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ n, ‖(hfs n).2.2.toLp (weakGradient m (fs n))‖ ≤ M) :
    Tendsto (fun n => ∫ x,gamma m (fs n) g x ∂m) atTop (𝓝 (∫ x,gamma m f g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy hq
  let mk (v : X → ℝ) (hv : Sobolev m v) : Q.domain := ⟨hv.1.toLp v,by
    change cheegerEnergy m (hv.1.toLp v : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o hv.1).mp hv⟩
  have he (v : X → ℝ) (hv : Sobolev m v) :
      Q.realEnergy (mk v hv) = ‖hv.2.2.toLp (weakGradient m v)‖^2/2 := by
    change (cheegerEnergy m (hv.1.toLp v : X → ℝ)).toReal = _
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq hv,
      norm_toLp_sq_eq_integral hv.2.2]
  have hbE (n : ℕ) : Q.realEnergy (mk (fs n) (hfs n)) ≤ M^2/2 := by
    rw [he (fs n) (hfs n)]
    gcongr
    exact hb n
  have hpair (v : X → ℝ) (hv : Sobolev m v) :
      (∫ x,gamma m v g x ∂m) = 2*Q.form (mk v hv) (mk g hg) := by
    rw [← hcd.global_integral_gamma_form hfin o hq]
    apply integral_congr_ae
    exact gamma_congr_ae hv.1.coeFn_toLp.symm hg.1.coeFn_toLp.symm
  simp_rw [hpair f hf,hpair _ (hfs _)]
  exact (Q.form_tendsto_of_bounded_energy (cheeger_domain_dense hq)
    (fun n => mk (fs n) (hfs n)) (mk f hf) (mk g hg) hT
    (div_nonneg (pow_nonneg hM 2) (by norm_num) : 0 ≤ M^2/2) hbE).const_mul 2
end WeakHessian

end
end InlinedFile18

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

lemma Sobolev.square_bounded (hfin : FiniteOnBoundedSets m) {u : X → ℝ}
    (hu : Sobolev m u) {B : ℝ} (hB : ∀ᵐ x ∂m, |u x| ≤ B) :
    Sobolev m (fun x => u x^2) := by
  have hsq : MemLp (fun x => u x^2) 2 m := by
    simpa only [pow_two] using memLp_mul_bounded hu.1 hu.1.aestronglyMeasurable hB
  have hc : ContDiff ℝ 1 (fun s : ℝ => s^2) := contDiff_id.pow 2
  have hd (s : ℝ) : deriv (fun t : ℝ => t^2) s = 2*s := by
    simp
  have hb : ∀ᵐ x ∂m, |deriv (fun s : ℝ => s^2) (u x)| ≤ 2*B := by
    filter_upwards [hB] with x hx
    rw [hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  apply Sobolev.of_upperGradient hfin hsq
    ((weakGradient_isMinimal hu.2.1.2).1.comp_contDiff hu.1.aemeasurable hc hb)
  have hm : AEStronglyMeasurable (fun x => |deriv (fun s : ℝ => s^2) (u x)|) m := by
    simp only [hd]
    exact continuous_abs.comp_aestronglyMeasurable (hu.1.aestronglyMeasurable.const_mul 2)
  simpa only [mul_comm] using memLp_mul_bounded hu.2.2 hm (by simpa only [abs_abs] using hb)

lemma gamma_square_bounded (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v : X → ℝ}
    (hu : Sobolev m u) (hv : LocalSobolev m v) {B : ℝ} (hB : ∀ᵐ x ∂m, |u x| ≤ B) :
    gamma m (fun x => u x^2) v =ᵐ[m] (fun x => 2*u x*gamma m u v x) := by
  have hd (s : ℝ) : deriv (fun t : ℝ => t^2) s = 2*s := by
    simp
  have hb : ∀ᵐ x ∂m, |deriv (fun s : ℝ => s^2) (u x)| ≤ 2*B := by
    filter_upwards [hB] with x hx
    rw [hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  simpa only [Function.comp_def,id_eq,hd] using gamma_comp_contDiff hfin hpar hu.2.1 hv
    (contDiff_id.pow 2) (hu.square_bounded hfin hB).2.1.1 hb

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
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_PotentialPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile19
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [ProperSpace X] in
lemma norm_gradient_le_supported_lipschitz (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hfS : Sobolev m f) {L : ℝ≥0} (hf : LipschitzWith L f)
    {Q : Set X} (hQ : MeasurableSet Q) (hs : tsupport f ⊆ Q)
    (hD : MemLp (Q.indicator (fun _ : X => (L:ℝ))) 2 m) :
    ‖hfS.2.2.toLp (weakGradient m f)‖ ≤ ‖hD.toLp (Q.indicator (fun _ : X => (L:ℝ)))‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hfS.2.2.coeFn_toLp,hD.coeFn_toLp,weakGradient_zero_off_support hfS.2.1,
    weakGradient_le_lipschitz hfin hf,weakGradient_nonneg (m := m) f,
    (ae_restrict_iff' hQ).mp (indicator_ae_eq_restrict (μ := m) (f := fun _ : X => (L:ℝ)) hQ)]
      with x he hd hz hl hn hi
  rw [he,hd,Real.norm_eq_abs,abs_of_nonneg hn]
  by_cases hx : x ∈ Q
  · simpa only [hi hx,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg] using hl
  · rw [hz (fun h => hx (hs h)),indicator_of_notMem hx,norm_zero]

omit [ProperSpace X] in
lemma integral_gamma_localization (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g v : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ x ∈ Q, f x = g x)
    (hs : ∀ᵐ x ∂m, x ∉ Q → v x = 0) :
    (∫ x,gamma m f v x ∂m) = ∫ x,gamma m g v x ∂m := by
  apply integral_congr_ae
  filter_upwards [gamma_locality_left hfin hf hg hv hQ (ae_of_all _ he),
    gamma_zero_off_set hfin hpar hv hf hQ hs,gamma_zero_off_set hfin hpar hv hg hQ hs,
    gamma_comm (m := m) f v,gamma_comm (m := m) g v] with x hl hz hy hc hd
  by_cases hx : x ∈ Q
  · exact hl hx
  · rw [hc,hd,hz hx,hy hx]

end WeakHessian

end
end InlinedFile19

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyPairingLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile20
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma entropy_pairing_twice (_ : FiniteOnBoundedSets m) {u φ : X → ℝ}
    (_ : LocalSobolev m u) (_ : LocalSobolev m φ) :
    (∫ x,2*u x*gamma m φ u x ∂m) = 2*(∫ x,u x*gamma m u φ x ∂m) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [gamma_comm (m := m) φ u] with x hx
  rw [hx]; ring

end WeakHessian

end
end InlinedFile20

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NormalizedRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile7
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_probability_of_norm {m : Measure X} {w : X → ℝ}
    (hw : MemLp w 2 m) (hnorm : ‖hw.toLp w‖ = 1) :
    IsProbabilityMeasure (squareDensityMeasure m w) := by
  constructor
  rw [squareDensityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mp hw) (ae_of_all _ fun x => sq_nonneg (w x)),
    ← norm_toLp_sq_eq_integral hw,hnorm,one_pow,ENNReal.ofReal_one]

end WeakHessian

end
end InlinedFile7

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile11
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] [SigmaFinite m] in
lemma squareDensity_ae_support {w : X → ℝ} (hw : Measurable w) {Q : Set X}
    (hzero : ∀ᵐ x ∂m, x ∉ Q → w x = 0) :
    ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Q := by
  apply (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mpr
  filter_upwards [hzero] with x hx hn
  by_contra h
  exact hn (by rw [hx h]; simp)
end WeakHessian

end
end InlinedFile11

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_SobolevFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile12
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma sqrt_gradient_energy_le_upper {v D : X → ℝ} (hv : Sobolev m v)
    (hD : IsLocalWeakUpperGradient m v D) (hD2 : MemLp D 2 m) :
    Real.sqrt (∫ x,(weakGradient m v x)^2 ∂m) ≤ ‖hD2.toLp D‖ := by
  have H : (∫ x,(weakGradient m v x)^2 ∂m) ≤ ∫ x,D x^2 ∂m := by
    apply integral_mono_ae ((memLp_two_iff_integrable_sq hv.2.2.aestronglyMeasurable).mp hv.2.2)
      ((memLp_two_iff_integrable_sq hD2.aestronglyMeasurable).mp hD2)
    filter_upwards [(weakGradient_isMinimal hv.2.1.2).2 D hD,weakGradient_nonneg (m := m) v] with x hx hn
    nlinarith
  rw [← norm_toLp_sq_eq_integral hD2] at H
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt H

end WeakHessian

end
end InlinedFile12

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_StrongRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile14
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.energy_tendsto_of_upper_bound
    {ι : Type*} {l : Filter ι} (us : ι → hQ.domain) (u : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    (bs : ι → ℝ) (hb : ∀ i, hQ.realEnergy (us i) ≤ bs i)
    (hbs : Tendsto bs l (𝓝 (hQ.realEnergy u))) :
    Tendsto (fun i => hQ.realEnergy (us i)) l (𝓝 (hQ.realEnergy u)) := by
  have he (v : hQ.domain) : ENNReal.ofReal (hQ.realEnergy v) = Q v :=
    ENNReal.ofReal_toReal v.property.ne
  have hbs' : Tendsto (fun i => ENNReal.ofReal (bs i)) l (𝓝 (Q u)) := by
    rw [← he u]
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp hbs
  have hQlim : Tendsto (fun i => Q (us i)) l (𝓝 (Q u)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact hu (hQ.lowerSemicontinuous u a ha)
    · intro b hb'
      filter_upwards [hbs'.eventually_lt_const hb'] with i hi
      rw [← he (us i)]
      exact (ENNReal.ofReal_le_ofReal (hb i)).trans_lt hi
  exact ENNReal.continuousAt_toReal u.property.ne |>.tendsto.comp hQlim
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.strong_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X)
    {w : X → ℝ} (hw : Sobolev m w)
    (fs Ds : ℕ → X → ℝ) (hfs : ∀ n, MemLp (fs n) 2 m) (hDs : ∀ n, MemLp (Ds n) 2 m)
    (hUG : ∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n))
    (hfT : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)))
    (hDT : Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w)))) :
    ∃ hs : ∀ n, Sobolev m (fun x => fs n x-w x),
      Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖)
        atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let hS (n : ℕ) := Sobolev.of_upperGradient hfin (hfs n) (hUG n) (hDs n)
  let Q := cheeger_closedQuadraticEnergy hq
  let u : Q.domain := ⟨hw.1.toLp w,by
    change cheegerEnergy m (hw.1.toLp w : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o hw.1).mp hw⟩
  let us (n : ℕ) : Q.domain := ⟨(hfs n).toLp (fs n),by
    change cheegerEnergy m ((hfs n).toLp (fs n) : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae (hfs n).coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o (hfs n)).mp (hS n)⟩
  have eu : Q.realEnergy u = ‖hw.2.2.toLp (weakGradient m w)‖^2/2 := by
    change (cheegerEnergy m (hw.1.toLp w : X → ℝ)).toReal = _
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq hw,
      norm_toLp_sq_eq_integral hw.2.2]
  let bs (n : ℕ) := ‖(hDs n).toLp (Ds n)‖^2/2
  have hbs : Tendsto bs atTop (𝓝 (Q.realEnergy u)) := by
    rw [eu]
    exact hDT.norm.pow 2 |>.div_const 2
  have hb (n : ℕ) : Q.realEnergy (us n) ≤ bs n := by
    change (cheegerEnergy m ((hfs n).toLp (fs n) : X → ℝ)).toReal ≤ _
    rw [cheegerEnergy_congr_ae (hfs n).coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq (hS n)]
    dsimp [bs]
    rw [norm_toLp_sq_eq_integral (hDs n)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply integral_mono_ae (hS n).2.2.integrable_sq (hDs n).integrable_sq
    filter_upwards [(weakGradient_isMinimal (hS n).2.1.2).2 _ (hUG n),
      weakGradient_nonneg (m := m) (fs n)] with x hx hn
    nlinarith
  obtain ⟨M,hM,hMb⟩ := (Metric.isBounded_range_of_tendsto bs hbs).exists_pos_norm_le
  have hbM (n : ℕ) : Q.realEnergy (us n) ≤ M :=
    (hb n).trans ((le_abs_self _).trans (hMb _ (mem_range_self n)))
  have hE := Q.energy_tendsto_of_upper_bound us u hfT bs hb hbs
  have hsub := Q.form_energy_sub_tendsto (cheeger_domain_dense hq) us u hfT hM.le hbM hE
  let hs (n : ℕ) := (hS n).sub hfin hw
  refine ⟨hs,?_⟩
  have he (n : ℕ) : ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖^2 =
      2*Q.realEnergy (us n-u) := by
    rw [norm_toLp_sq_eq_integral (hs n).2.2]
    have hae : ((us n-u : Q.domain):Lp ℝ 2 m) = (hs n).1.toLp (fun x => fs n x-w x) := by
      exact (MemLp.toLp_sub (hfs n) hw.1).symm
    change _ = 2*(cheegerEnergy m (((us n-u : Q.domain):Lp ℝ 2 m) : X → ℝ)).toReal
    rw [hae,cheegerEnergy_congr_ae (hs n).1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq (hs n)]
    ring
  have H : Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖^2)
      atTop (𝓝 0) := by simpa only [he,mul_zero] using hsub.const_mul 2
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using H.sqrt
end WeakHessian

end
end InlinedFile14

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_QuadraticContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile34
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma planEnergy_le_of_restricted_contact {π η : Measure (Curve X)}
    [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hiη : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) η)
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hiφπ : Integrable φ (interpolation π timeZero)) (hiφη : Integrable φ (interpolation η timeZero))
    (hiψπ : Integrable ψ (interpolation π timeOne))
    {S : Set X} (hs : ∀ᵐ γ ∂η, γ timeOne ∈ S)
    (hd : ∀ x y, y ∈ S → φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h1 : interpolation π timeOne = interpolation η timeOne) :
    planEnergy π-planEnergy η ≤
      2*((∫ x,φ x ∂interpolation π timeZero)-(∫ x,φ x ∂interpolation η timeZero)) := by
  have hmap (p : Measure (Curve X)) (s : Time) (f : X → ℝ) (hf : Continuous f) :
      (∫ γ,f (γ s) ∂p) = ∫ x,f x ∂interpolation p s :=
    (integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable).symm
  have ip := (integrable_map_measure hφ.aestronglyMeasurable (continuous_eval_const timeZero).measurable.aemeasurable).mp hiφπ
  have iq := (integrable_map_measure hφ.aestronglyMeasurable (continuous_eval_const timeZero).measurable.aemeasurable).mp hiφη
  have jp := (integrable_map_measure hψ.aestronglyMeasurable (continuous_eval_const timeOne).measurable.aemeasurable).mp hiψπ
  have jq := (integrable_map_measure hψ.aestronglyMeasurable (continuous_eval_const timeOne).measurable.aemeasurable).mp (h1 ▸ hiψπ)
  simp only [Function.comp_def] at ip iq jp jq
  have hC : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂π) = planEnergy π/2 := by
    rw [integral_congr_ae hc]
    exact integral_div _ _
  have hB : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂η) ≤ planEnergy η/2 := by
    apply le_trans (integral_mono_ae (iq.add jq) (hiη.div_const 2) (hs.mono fun γ hγ => hd _ _ hγ))
    exact le_of_eq (integral_div _ _)
  rw [integral_add ip jp,hmap π timeZero φ hφ,hmap π timeOne ψ hψ,h1] at hC
  rw [integral_add iq jq,hmap η timeZero φ hφ,hmap η timeOne ψ hψ] at hB
  linarith

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma entropy_pairing_congr_squareDensity (hfin : FiniteOnBoundedSets m)
    {w φ ψ : X → ℝ} (hw : LocalSobolev m w) (hwm : Measurable w)
    (hφ : LocalSobolev m φ) (hψ : LocalSobolev m ψ)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (he : φ =ᵐ[squareDensityMeasure m w] ψ) :
    (fun x => 2*w x*gamma m φ w x) =ᵐ[m] fun x => 2*w x*gamma m ψ w x := by
  have he' := (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mp he
  let S := {x | φ x = ψ x}
  have hS : MeasurableSet S := measurableSet_eq_fun hφm hψm
  have H := gamma_locality_left hfin hφ hψ hw hS (ae_of_all _ fun x hx => hx)
  filter_upwards [he',H] with x hx hg
  by_cases hz : w x = 0
  · simp [hz]
  have hn : ENNReal.ofReal (w x^2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero hz)
  rw [hg (hx hn)]

variable [ProperSpace X] [SigmaFinite m]

lemma RCD.compact_quadratic_entropy_subgradient {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R T : ℝ≥0) (hT : 0 < T)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      BoundedTracks (π:Measure (Curve X)) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∃ L : ℝ≥0, LipschitzWith L ψ) ∧
      (∀ x y, y ∈ Metric.closedBall o T → φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  have haμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (R:ℝ) ≤ (R+T:ℝ≥0))) hx
  have haν : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (T:ℝ) ≤ (R+T:ℝ≥0))) hx
  obtain ⟨π,f,g,hπ,hb,hgeo,ho,hf,hg,hd,hc,hent⟩ := hrcd.compact_sobolev_entropy_subdifferential
    hN hfin w hw hwm hB hwn hwB μ ν hμ o (R+T) (ae_iff.mp haμ) (ae_iff.mp haν) hCt hdν
  let S := Metric.closedBall o (T:ℝ)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hne : S.Nonempty := Metric.nonempty_closedBall.mpr T.coe_nonneg
  let f' := compactCTransform S g
  have hq : QuadraticLipschitzBound o T f' := compactCTransform_difference_bound hS hne hg.continuous.continuousOn o (Subset.refl S)
  have hq' : QuadraticLipschitzBound o T (fun x => f' x-f' o) := by
    intro x y
    simpa only [sub_sub_sub_cancel_right] using hq x y
  have hg' : LipschitzWith (2*(R+T+2)) (fun y => g y+f' o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul x y
  have hsπ : ∀ᵐ γ ∂(π:Measure (Curve X)), γ timeOne ∈ S := by
    apply (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable hS.measurableSet).mp
    change ∀ᵐ x ∂interpolation (π:Measure (Curve X)) timeOne, x ∈ S
    rw [ho.1.interpolation_endpoints.2]
    exact ae_iff.mpr hsν
  have heπ : ∀ᵐ γ ∂(π:Measure (Curve X)), f' (γ timeZero) = f (γ timeZero) := by
    filter_upwards [hsπ,hc] with γ hs hc
    exact compactCTransform_contact hS hne hg.continuous.continuousOn hd hs hc
  have heμ : f' =ᵐ[(μ:Measure X)] f := by
    rw [← ho.1.interpolation_endpoints.1]
    exact (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable
      (isClosed_eq (hq.continuous T.coe_nonneg) hf.continuous).measurableSet).mpr heπ
  have hepair := entropy_pairing_congr_squareDensity hfin hw.2.1 hwm
    (hq.localSobolev hfin hT) (localSobolev_of_lipschitz hfin hf)
    (hq.continuous T.coe_nonneg).measurable hf.continuous.measurable (hμ ▸ heμ)
  have hshift : (fun x => 2*w x*gamma m (fun y => f' y-f' o) w x) =ᵐ[m]
      fun x => 2*w x*gamma m f' w x := by
    exact (gamma_add_const_left hfin (hq.localSobolev hfin hT) hw.2.1 (-f' o)).mono fun x hx => by
      simp only [sub_eq_add_neg,hx]
  refine ⟨π,(fun x => f' x-f' o),(fun y => g y+f' o),hb,ho,hq',sub_self _,⟨_,hg'⟩,?_,?_,?_⟩
  · intro x y hy
    have H := compactCTransform_le hS hne hg.continuous.continuousOn x hy
    dsimp [f']
    linarith
  · filter_upwards [heπ,hc] with γ he hc
    rw [he]
    linarith
  · rw [integral_congr_ae hshift,integral_congr_ae hepair]
    exact hent
end WeakHessian

end
end InlinedFile34

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RadialRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile28
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_mul_tendsto {f : X → ℝ} (hf : MemLp f 2 m) (o : X) :
    Tendsto (fun n => (radial_mul_memLp hf o n).toLp (fun x => f x*radialCutoff o n x))
      atTop (𝓝 (hf.toLp f)) := by
  apply toLp_tendsto_of_domination (fun n => radial_mul_memLp hf o n) hf hf
  · intro n
    apply ae_of_all
    intro x
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by
      rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg o n x)]
      exact radialCutoff_le_one o n x)
  · exact ae_of_all _ fun x => by simpa only [mul_one] using (radialCutoff_tendsto o x).const_mul (f x)

omit [ProperSpace X] in
lemma radial_root_approximation (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) :
    ∃ Ds : ℕ → X → ℝ, ∃ hDs : ∀ n, MemLp (Ds n) 2 m,
      (∀ n, IsLocalWeakUpperGradient m (fun x => w x*radialCutoff o n x) (Ds n)) ∧
      Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
        (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  let D := weakGradient m w
  let c (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
  let Ds (n : ℕ) (x : X) := D x*radialCutoff o n x+c n*|w x|
  let hDs (n : ℕ) : MemLp (Ds n) 2 m := (radial_mul_memLp hw.2.2 o n).add (by
    simpa only [Real.norm_eq_abs] using hw.1.norm.const_mul (c n))
  refine ⟨Ds,hDs,?_,?_⟩
  · intro n
    have H := (weakGradient_isMinimal hw.2.1.2).1.mul_bounded
      (lipschitz_isLocalWeakUpperGradient hfin (radialCutoff_lipschitz o n)) hw.2.1.1
      (radialCutoff_lipschitz o n).continuous.measurable.aemeasurable
      (A := 1) (B := c n)
      (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
      (ae_of_all _ fun x => by simp only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; exact le_of_eq (abs_of_nonneg (by positivity)))
    simpa only [abs_of_nonneg (radialCutoff_nonneg o n _),NNReal.coe_inv,NNReal.coe_add,
      NNReal.coe_natCast,NNReal.coe_one,mul_comm,D,Ds,c] using H
  · have hc : Tendsto c atTop (𝓝 (0:ℝ)) := by
      simpa only [c,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hn : MemLp (fun x => |w x|) 2 m := by simpa only [Real.norm_eq_abs] using hw.1.norm
    have H := (radial_mul_tendsto hw.2.2 o).add (hc.smul (tendsto_const_nhds (x := hn.toLp (fun x => |w x|))))
    have he (n : ℕ) : (hDs n).toLp (Ds n) =
        (radial_mul_memLp hw.2.2 o n).toLp (fun x => D x*radialCutoff o n x)+c n • hn.toLp (fun x => |w x|) := by
      rw [← MemLp.toLp_const_smul,← MemLp.toLp_add]
      congr 1
    simp_rw [he]
    simpa only [zero_smul,add_zero] using H

lemma radial_root_strong {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (hq : QuadraticCheegerEnergy m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) :
    ∃ hs : ∀ n, Sobolev m (fun x => w x*radialCutoff o n x-w x),
      Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => w x*radialCutoff o n x-w x))‖)
        atTop (𝓝 0) := by
  obtain ⟨Ds,hDs,hUG,hDT⟩ := radial_root_approximation hfin hw o
  exact hcd.strong_root_approximation hfin hq o hw _ Ds (fun n => radial_mul_memLp hw.1 o n)
    hDs hUG (radial_mul_tendsto hw.1 o) hDT

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_weighted_root_tendsto {w W : X → ℝ} (hW : MemLp (fun x => w x*W x) 2 m) (o : X) :
    ∃ hs : ∀ n, MemLp (fun x => (w x*radialCutoff o n x-w x)*W x) 2 m,
      Tendsto (fun n => ‖(hs n).toLp (fun x => (w x*radialCutoff o n x-w x)*W x)‖)
        atTop (𝓝 0) := by
  have he (n : ℕ) : (fun x => (w x*radialCutoff o n x-w x)*W x) =
      fun x => w x*W x*radialCutoff o n x-w x*W x := by funext x; ring
  have hs (n : ℕ) : MemLp (fun x => (w x*radialCutoff o n x-w x)*W x) 2 m := by
    rw [he]; exact (radial_mul_memLp hW o n).sub hW
  refine ⟨hs,?_⟩
  have H := ((radial_mul_tendsto hW o).sub (tendsto_const_nhds (x := hW.toLp _))).norm
  have heq (n : ℕ) : (hs n).toLp (fun x => (w x*radialCutoff o n x-w x)*W x) =
      (radial_mul_memLp hW o n).toLp (fun x => w x*W x*radialCutoff o n x)-hW.toLp (fun x => w x*W x) := by
    rw [← MemLp.toLp_sub]
    congr 1
    exact he n
  simp_rw [heq]
  simpa only [sub_self,norm_zero] using H
end WeakHessian

end
end InlinedFile28

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NormalizedRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile29
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_probability_normalization {w : X → ℝ} (hw : MemLp w 2 m)
    (hwm : Measurable w) [IsProbabilityMeasure (squareDensityMeasure m w)] (o : X) :
    ∃ k : ℕ, ∃ c : ℕ → ℝ, (∀ n, 0 < c n ∧ c n ≤ 2) ∧ Tendsto c atTop (𝓝 1) ∧
      ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x))) := by
  have hnorm : ‖hw.toLp w‖ = 1 := by
    have H := norm_toLp_sq_eq_integral hw
    rw [squareDensity_mass hwm] at H
    nlinarith [norm_nonneg (hw.toLp w)]
  have hn : Tendsto (fun n => ‖(radial_mul_memLp hw o n).toLp (fun x => w x*radialCutoff o n x)‖)
      atTop (𝓝 (1:ℝ)) := by simpa only [hnorm] using (radial_mul_tendsto hw o).norm
  obtain ⟨k,hk⟩ := eventually_atTop.1 (hn.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)/2 < 1)))
  let c (n : ℕ) := ‖(radial_mul_memLp hw o (n+k)).toLp (fun x => w x*radialCutoff o (n+k) x)‖⁻¹
  have hpos (n : ℕ) : 0 < ‖(radial_mul_memLp hw o (n+k)).toLp (fun x => w x*radialCutoff o (n+k) x)‖ :=
    lt_trans (by norm_num) (hk _ (Nat.le_add_left k n))
  have hc (n : ℕ) : 0 < c n ∧ c n ≤ 2 := by
    refine ⟨inv_pos.mpr (hpos n),?_⟩
    exact (inv_le_comm₀ (hpos n) (by norm_num : (0:ℝ)<2)).mpr (by simpa using (hk _ (Nat.le_add_left k n)).le)
  refine ⟨k,c,hc,?_,?_⟩
  · simpa only [inv_one,Function.comp_apply,c] using (hn.comp (tendsto_add_atTop_nat k)).inv₀ one_ne_zero
  · intro n
    apply squareDensity_probability_of_norm ((radial_mul_memLp hw o (n+k)).const_mul (c n))
    have he : ((radial_mul_memLp hw o (n+k)).const_mul (c n)).toLp
        (fun x => c n*(w x*radialCutoff o (n+k) x)) =
        c n • (radial_mul_memLp hw o (n+k)).toLp (fun x => w x*radialCutoff o (n+k) x) :=
      (radial_mul_memLp hw o (n+k)).toLp_const_smul (c n)
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (hc n).1]
    exact inv_mul_cancel₀ (hpos n).ne'

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma normalized_radial_tendsto {f : X → ℝ} (hf : MemLp f 2 m) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => ((radial_mul_memLp hf o (n+k)).const_mul (c n)).toLp
      (fun x => c n*(f x*radialCutoff o (n+k) x))) atTop (𝓝 (hf.toLp f)) := by
  have H := hc.smul ((radial_mul_tendsto hf o).comp (tendsto_add_atTop_nat k))
  have he (n : ℕ) : ((radial_mul_memLp hf o (n+k)).const_mul (c n)).toLp
      (fun x => c n*(f x*radialCutoff o (n+k) x)) =
      c n • (radial_mul_memLp hf o (n+k)).toLp (fun x => f x*radialCutoff o (n+k) x) :=
    (radial_mul_memLp hf o (n+k)).toLp_const_smul (c n)
  simp_rw [he]
  simpa only [one_smul,Function.comp_apply] using H

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma normalized_radial_weighted_tendsto {w W : X → ℝ}
    (hW : MemLp (fun x => w x*W x) 2 m) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) :
    ∃ hs : ∀ n, MemLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) 2 m,
      Tendsto (fun n => ‖(hs n).toLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x)‖)
        atTop (𝓝 0) := by
  have he (n : ℕ) : (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) =
      fun x => c n*(w x*W x*radialCutoff o (n+k) x)-w x*W x := by funext x; ring
  have hs (n : ℕ) : MemLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) 2 m := by
    rw [he]; exact ((radial_mul_memLp hW o (n+k)).const_mul (c n)).sub hW
  refine ⟨hs,?_⟩
  have heq (n : ℕ) : (hs n).toLp (fun x => (c n*(w x*radialCutoff o (n+k) x)-w x)*W x) =
      ((radial_mul_memLp hW o (n+k)).const_mul (c n)).toLp
        (fun x => c n*(w x*W x*radialCutoff o (n+k) x))-hW.toLp (fun x => w x*W x) := by
    rw [← MemLp.toLp_sub]
    congr 1
    exact he n
  simp_rw [heq]
  simpa only [sub_self,norm_zero] using ((normalized_radial_tendsto hW o k hc).sub_const (hW.toLp _)).norm

lemma CurvatureDimension.normalized_radial_root_strong {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (hq : QuadraticCheegerEnergy m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hcn : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 1)) :
    ∃ hs : ∀ n, Sobolev m (fun x => c n*(w x*radialCutoff o (n+k) x)),
      Tendsto (fun n => ‖((hs n).sub hfin hw).2.2.toLp
        (weakGradient m (fun x => c n*(w x*radialCutoff o (n+k) x)-w x))‖) atTop (𝓝 0) := by
  obtain ⟨Ds,hDs,hUG,hDT⟩ := radial_root_approximation hfin hw o
  let fs (n : ℕ) (x : X) := c n*(w x*radialCutoff o (n+k) x)
  let Es (n : ℕ) (x : X) := c n*Ds (n+k) x
  let hfs (n : ℕ) : MemLp (fs n) 2 m := (radial_mul_memLp hw.1 o (n+k)).const_mul (c n)
  let hEs (n : ℕ) : MemLp (Es n) 2 m := (hDs (n+k)).const_mul (c n)
  have hEU (n : ℕ) : IsLocalWeakUpperGradient m (fs n) (Es n) := by
    simpa only [abs_of_nonneg (hcn n),fs,Es] using (hUG (n+k)).const_mul (c n)
  let hs (n : ℕ) := Sobolev.of_upperGradient hfin (hfs n) (hEU n) (hEs n)
  have hET : Tendsto (fun n => (hEs n).toLp (Es n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
    have H := hc.smul (hDT.comp (tendsto_add_atTop_nat k))
    have he (n : ℕ) : (hEs n).toLp (Es n) = c n • (hDs (n+k)).toLp (Ds (n+k)) :=
      (hDs (n+k)).toLp_const_smul (c n)
    simp_rw [he]
    simpa only [Function.comp_apply,one_smul] using H
  obtain ⟨hsub,hST⟩ := hcd.strong_root_approximation hfin hq o hw fs Es hfs hEs hEU
    (normalized_radial_tendsto hw.1 o k hc) hET
  exact ⟨hs,hST⟩
end WeakHessian

end
end InlinedFile29

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_QuadraticCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile33
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma QuadraticLipschitzBound.centered_bound {o : X} {R : ℝ} (hR : 0 ≤ R)
    {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hz : f o = 0) (x : X) :
    |f x| ≤ (dist x o+R)^2 := by
  have H := hf x o
  rw [hz,sub_zero,dist_self] at H
  apply H.trans
  calc
    ((dist x o+0)/2+R)*dist x o ≤ (dist x o+R)*dist x o := by
      nlinarith [sq_nonneg (dist x o)]
    _ ≤ (dist x o+R)*(dist x o+R) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR) (add_nonneg dist_nonneg hR)
    _ = (dist x o+R)^2 := by ring

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integrable_of_quadratic_bound {w W f : X → ℝ}
    (hwm : Measurable w) (hW : MemLp (fun x => w x*W x) 2 m)
    (hf : AEStronglyMeasurable f m) (hb : ∀ᵐ x ∂m, |f x| ≤ (W x)^2) :
    Integrable f (squareDensityMeasure m w) ∧ Integrable (fun x => w x^2*f x) m := by
  have hi := hW.integrable_sq
  have hj : Integrable (fun x => w x^2*f x) m := by
    apply hi.mono' (hwm.pow_const 2 |>.aestronglyMeasurable.mul hf)
    filter_upwards [hb] with x hx
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg (w x))]
  exact ⟨(squareDensity_integrable hwm).mpr hj,hj⟩

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_quadratic_pairing_bound {u v W f : X → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (huW : MemLp (fun x => u x*W x) 2 m) (hvW : MemLp (fun x => v x*W x) 2 m)
    (hf : AEStronglyMeasurable f m) (hb : ∀ᵐ x ∂m, |f x| ≤ (W x)^2) :
    |(∫ x,f x ∂squareDensityMeasure m u)-(∫ x,f x ∂squareDensityMeasure m v)| ≤
      ∫ x,|(u x*W x)^2-(v x*W x)^2| ∂m := by
  have hi := (squareDensity_integrable_of_quadratic_bound hu huW hf hb).2
  have hj := (squareDensity_integrable_of_quadratic_bound hv hvW hf hb).2
  rw [squareDensity_integral hu,squareDensity_integral hv,← integral_sub hi hj,← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hi.sub hj).norm (huW.integrable_sq.sub hvW.integrable_sq).abs
  filter_upwards [hb] with x hx
  have he : (u x*W x)^2-(v x*W x)^2 = (u x^2-v x^2)*W x^2 := by ring
  simp only [Pi.sub_apply]
  rw [← sub_mul,Real.norm_eq_abs,abs_mul,he,abs_mul,abs_of_nonneg (sq_nonneg (W x))]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

lemma quadratic_integral_tendsto {o : X} {R : ℝ} (hR : 0 ≤ R)
    {fs : ℕ → X → ℝ} {f w : X → ℝ}
    (hfs : ∀ n, QuadraticLipschitzBound o R (fs n)) (hf : QuadraticLipschitzBound o R f)
    (hz : ∀ n, fs n o = 0) (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hwm : Measurable w) (hwW : MemLp (fun x => w x*(dist x o+R)) 2 m) :
    Tendsto (fun n => ∫ x,fs n x ∂squareDensityMeasure m w) atTop
      (𝓝 (∫ x,f x ∂squareDensityMeasure m w)) := by
  simp_rw [squareDensity_integral hwm]
  have hmeas : ∀ index, AEStronglyMeasurable (fun point => w point^2*fs index point) m :=
    fun index => (hwm.pow_const 2).aestronglyMeasurable.mul
      ((hfs index).continuous hR).aestronglyMeasurable
  have hbound : ∀ index, ∀ᵐ point ∂m,
      ‖w point^2*fs index point‖ ≤ (w point*(dist point o+R))^2 := by
    intro index
    exact ae_of_all _ fun point => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hweighted := mul_le_mul_of_nonneg_left
        ((hfs index).centered_bound hR (hz index) point) (sq_nonneg (w point))
      nlinarith
  apply tendsto_integral_of_L1 (fun point => w point^2*f point)
    ((hwm.pow_const 2).aestronglyMeasurable.mul (hf.continuous hR).aestronglyMeasurable)
  · exact Eventually.of_forall fun index =>
      hwW.integrable_sq.mono' (hmeas index) (hbound index)
  · simpa only [ofReal_norm] using
      tendsto_lintegral_norm_of_dominated_convergence hmeas hwW.integrable_sq.2 hbound
        (ae_of_all _ fun point => (ht point).const_mul (w point^2))

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_weighted_density_tendsto {w W : X → ℝ}
    (hwW : MemLp (fun x => w x*W x) 2 m) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x,|((c n*(w x*radialCutoff o (n+k) x))*W x)^2-(w x*W x)^2| ∂m)
      atTop (𝓝 0) := by
  have H := squareDensity_L1_tendsto
    (fun n => (radial_mul_memLp hwW o (n+k)).const_mul (c n)) hwW
    (normalized_radial_tendsto hwW o k hc)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  congr 1
  funext x
  congr 1
  ring
end WeakHessian

end
end InlinedFile33

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_QuadraticCostLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile35
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma weighted_density_triangle {u v w W : X → ℝ}
    (hu : MemLp (fun x => u x*W x) 2 m) (hv : MemLp (fun x => v x*W x) 2 m)
    (hw : MemLp (fun x => w x*W x) 2 m) :
    (∫ x,|(u x*W x)^2-(v x*W x)^2| ∂m) ≤
      (∫ x,|(u x*W x)^2-(w x*W x)^2| ∂m)+(∫ x,|(v x*W x)^2-(w x*W x)^2| ∂m) := by
  have hiu : Integrable (fun x => |(u x*W x)^2-(w x*W x)^2|) m := (hu.integrable_sq.sub hw.integrable_sq).abs
  have hiv : Integrable (fun x => |(v x*W x)^2-(w x*W x)^2|) m := (hv.integrable_sq.sub hw.integrable_sq).abs
  rw [← integral_add hiu hiv]
  apply integral_mono (hu.integrable_sq.sub hv.integrable_sq).abs
    ((hu.integrable_sq.sub hw.integrable_sq).abs.add (hv.integrable_sq.sub hw.integrable_sq).abs)
  intro x
  change |(u x*W x)^2-(v x*W x)^2| ≤ |(u x*W x)^2-(w x*W x)^2|+|(v x*W x)^2-(w x*W x)^2|
  rw [abs_sub_comm ((v x*W x)^2) ((w x*W x)^2)]
  exact abs_sub_le _ _ _

lemma cost_difference_quadratic_contact {u v W φ ψ : X → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (huW : MemLp (fun x => u x*W x) 2 m) (hvW : MemLp (fun x => v x*W x) 2 m)
    {π η : Measure (Curve X)} [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hiη : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) η)
    (h0π : interpolation π timeZero = squareDensityMeasure m u)
    (h0η : interpolation η timeZero = squareDensityMeasure m v)
    (h1 : interpolation π timeOne = interpolation η timeOne)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hiψ : Integrable ψ (interpolation π timeOne))
    (hb : ∀ᵐ x ∂m, |φ x| ≤ W x^2)
    {S : Set X} (hs : ∀ᵐ γ ∂η, γ timeOne ∈ S)
    (hd : ∀ x y, y ∈ S → φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    planEnergy π-planEnergy η ≤ 2*(∫ x,|(u x*W x)^2-(v x*W x)^2| ∂m) := by
  have ip := (squareDensity_integrable_of_quadratic_bound hu huW hφ.aestronglyMeasurable hb).1
  have iq := (squareDensity_integrable_of_quadratic_bound hv hvW hφ.aestronglyMeasurable hb).1
  have H := planEnergy_le_of_restricted_contact hiη hφ hψ (h0π ▸ ip) (h0η ▸ iq) hiψ hs hd hc h1
  rw [h0π,h0η] at H
  have J := squareDensity_quadratic_pairing_bound hu hv huW hvW hφ.aestronglyMeasurable hb
  exact H.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans J) (by norm_num))

variable [SecondCountableTopology X]

omit [SecondCountableTopology X] in
lemma exists_energy_limit_of_quadratic_contacts
    {us : ℕ → X → ℝ} {w W : X → ℝ}
    (hum : ∀ n, Measurable (us n))
    (huW : ∀ n, MemLp (fun x => us n x*W x) 2 m)
    (hwW : MemLp (fun x => w x*W x) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) atTop (𝓝 0))
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (hi : ∀ n, Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (ps n:Measure (Curve X)))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = squareDensityMeasure m (us n))
    (h1 : ∀ i j, interpolation (ps i:Measure (Curve X)) timeOne = interpolation (ps j:Measure (Curve X)) timeOne)
    (φ ψ : ℕ → X → ℝ) (hφ : ∀ n, Continuous (φ n)) (hψ : ∀ n, Continuous (ψ n))
    (hiψ : ∀ n, Integrable (ψ n) (interpolation (ps n:Measure (Curve X)) timeOne))
    (hb : ∀ n, ∀ᵐ x ∂m, |φ n x| ≤ W x^2)
    {S : Set X} (hs : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeOne ∈ S)
    (hd : ∀ n x y, y ∈ S → φ n x+ψ n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)),
      φ n (γ timeZero)+ψ n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    ∃ E : ℝ, 0 ≤ E ∧ Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E) := by
  let e (n : ℕ) := ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m
  have hbnd (i j : ℕ) : |planEnergy (ps i:Measure (Curve X))-planEnergy (ps j:Measure (Curve X))| ≤ 2*(e i+e j) := by
    have aux (a b : ℕ) : planEnergy (ps a:Measure (Curve X))-planEnergy (ps b:Measure (Curve X)) ≤ 2*(e a+e b) :=
      (cost_difference_quadratic_contact (hum a) (hum b) (huW a) (huW b) (hi b) (h0 a) (h0 b)
        (h1 a b) (hφ a) (hψ a) (hiψ a) (hb a) (hs b) (hd a) (hc a)).trans
        (mul_le_mul_of_nonneg_left (weighted_density_triangle (huW a) (huW b) hwW) (by norm_num))
    exact abs_le.mpr ⟨by have H := aux j i; linarith,aux i j⟩
  have hC : CauchySeq (fun n => planEnergy (ps n:Measure (Curve X))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k,hk⟩ := eventually_atTop.1 (hTV.eventually (eventually_lt_nhds (show (0:ℝ)<ε/4 by positivity)))
    refine ⟨k,fun i hi j hj => ?_⟩
    rw [Real.dist_eq]
    exact (hbnd i j).trans_lt (by have H := hk i hi; have J := hk j hj; dsimp [e]; linarith)
  obtain ⟨E,hE⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨E,ge_of_tendsto' hE (fun n => planEnergy_nonneg _),hE⟩
end WeakHessian

end
end InlinedFile35

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NoncompactOptimal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile37
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma limit_energy_le_coupling_of_quadratic_contacts
    {us : ℕ → X → ℝ} {w W : X → ℝ}
    (hum : ∀ n, Measurable (us n)) (hwm : Measurable w)
    (huW : ∀ n, MemLp (fun x => us n x*W x) 2 m) (hwW : MemLp (fun x => w x*W x) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) atTop (𝓝 0))
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = squareDensityMeasure m (us n))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    (φ ψ : ℕ → X → ℝ) (hφ : ∀ n, Continuous (φ n)) (hψ : ∀ n, Continuous (ψ n))
    (hiψ : ∀ n, Integrable (ψ n) (ν:Measure X))
    (hb : ∀ n, ∀ᵐ x ∂m, |φ n x| ≤ W x^2)
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ n x y, y ∈ S → φ n x+ψ n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)),
      φ n (γ timeZero)+ψ n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    {E : ℝ} (hE : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E))
    {q : Measure (X×X)} (hq : IsCoupling q μ ν) : ENNReal.ofReal E ≤ QuadraticTransportCost q := by
  by_cases hqt : QuadraticTransportCost q = ∞
  · simp [hqt]
  have H (n : ℕ) : planEnergy (ps n:Measure (Curve X))-(∫ p : X×X,dist p.1 p.2^2 ∂q) ≤
      2*(∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) := by
    have ip := (squareDensity_integrable_of_quadratic_bound (hum n) (huW n) (hφ n).aestronglyMeasurable (hb n)).1
    have iq := (squareDensity_integrable_of_quadratic_bound hwm hwW (hφ n).aestronglyMeasurable (hb n)).1
    have I := planEnergy_le_coupling_of_restricted_contact hqt μ ν hq (h1 n)
      (hφ n) (hψ n) (h0 n ▸ ip) (hμ ▸ iq) (hiψ n) hS hs (hd n) (hc n)
    rw [h0 n,hμ] at I
    exact I.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (squareDensity_quadratic_pairing_bound (hum n) hwm (huW n) hwW (hφ n).aestronglyMeasurable (hb n))) (by norm_num))
  have I := le_of_tendsto_of_tendsto' (hE.sub_const (∫ p : X×X,dist p.1 p.2^2 ∂q)) (hTV.const_mul 2) H
  simp only [mul_zero] at I
  rw [quadraticTransportCost_eq_integral hqt]
  exact ENNReal.ofReal_le_ofReal (sub_nonpos.mp I)

lemma exists_noncompact_optimal_of_quadratic_contacts
    {us : ℕ → X → ℝ} {w W : X → ℝ}
    (hum : ∀ n, Measurable (us n)) (hwm : Measurable w)
    (huW : ∀ n, MemLp (fun x => us n x*W x) 2 m) (hwW : MemLp (fun x => w x*W x) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) atTop (𝓝 0))
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (μs : ℕ → ProbabilityMeasure X) (hμs : ∀ n, (μs n:Measure X) = squareDensityMeasure m (us n))
    (hμT : Tendsto μs atTop (𝓝 μ))
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (hi : ∀ n, Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (ps n:Measure (Curve X)))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = (μs n:Measure X))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    (φ ψ : ℕ → X → ℝ) (hφ : ∀ n, Continuous (φ n)) (hψ : ∀ n, Continuous (ψ n))
    (hiψ : ∀ n, Integrable (ψ n) (ν:Measure X))
    (hb : ∀ n, ∀ᵐ x ∂m, |φ n x| ≤ W x^2)
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ n x y, y ∈ S → φ n x+ψ n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)),
      φ n (γ timeZero)+ψ n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧
      QuadraticTransportCost q ≠ ∞ ∧
      Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (QuadraticTransportCost q).toReal) := by
  have h0' (n : ℕ) := (h0 n).trans (hμs n)
  have h1' (i j : ℕ) := (h1 i).trans (h1 j).symm
  have hiψ' (n : ℕ) : Integrable (ψ n) (interpolation (ps n:Measure (Curve X)) timeOne) := h1 n ▸ hiψ n
  have hs' (n : ℕ) : ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeOne ∈ S :=
    (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable hS).mp (by
      change ∀ᵐ y ∂interpolation (ps n:Measure (Curve X)) timeOne, y ∈ S
      rw [h1 n]; exact hs)
  obtain ⟨E,hEn,hE⟩ := exists_energy_limit_of_quadratic_contacts hum huW hwW hTV ps hi h0' h1' φ ψ hφ hψ hiψ' hb hs' hd hc
  obtain ⟨q,hqp,hq,hqc⟩ := exists_coupling_of_energy_limit μ ν μs hμT ps hi h0 h1 hE
  have hlower (q' : Measure (X×X)) (hq' : IsCoupling q' μ ν) : ENNReal.ofReal E ≤ QuadraticTransportCost q' :=
    limit_energy_le_coupling_of_quadratic_contacts hum hwm huW hwW hTV μ ν hμ ps h0' h1 φ ψ hφ hψ hiψ hb hS hs hd hc hE hq'
  have he : QuadraticTransportCost q = ENNReal.ofReal E := le_antisymm hqc (hlower q hq)
  refine ⟨q,hqp,⟨hq,fun q' hq' => hqc.trans (hlower q' hq')⟩,ne_top_of_le_ne_top ENNReal.ofReal_ne_top hqc,?_⟩
  simpa only [he,ENNReal.toReal_ofReal hEn] using hE
end WeakHessian

end
end InlinedFile37

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_QuadraticCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile40
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma exists_quadratic_locally_uniform_subsequence
    (o : X) (R : ℝ≥0) (fs : ℕ → X → ℝ)
    (hLip : ∀ n, QuadraticLipschitzBound o R (fs n))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |fs n o| ≤ B) :
    ∃ f : X → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧ QuadraticLipschitzBound o R f ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      ∀ k : ℕ, TendstoUniformlyOn (fun n => fs (s n)) f atTop
        (Metric.closedBall o (k:ℝ)) := by
  let Q (k : ℕ) := Metric.closedBall o (k:ℝ)
  let (k : ℕ) : CompactSpace (Q k) := isCompact_iff_compactSpace.mp (isCompact_closedBall o (k:ℝ))
  let vs (n k : ℕ) : C(Q k,ℝ) := ⟨fun x => fs n x,((hLip n).continuous R.coe_nonneg).comp continuous_subtype_val⟩
  let L (k : ℕ) : ℝ≥0 := k+R
  let M (k : ℕ) := B+(L k:ℝ)*k
  let S (k : ℕ) := {f : C(Q k,ℝ) | LipschitzWith (L k) f ∧ ‖f‖ ≤ M k}
  have hS (k : ℕ) : IsCompact (S k) :=
    WeakHessianTransport.isCompact_lipschitz_norm_ball (L k) (by dsimp [M]; positivity)
  have hvs (n k : ℕ) : vs n k ∈ S k := by
    refine ⟨?_,?_⟩
    · change LipschitzWith (L k) (fun x : Q k => fs n x)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have H := ((hLip n).lipschitzOn_ball R.coe_nonneg o (k:ℝ≥0)).dist_le_mul x x.property y y.property
      simpa only [dist_self,zero_add,add_zero,NNReal.coe_mk,NNReal.coe_add,NNReal.coe_natCast,L,add_comm,Subtype.dist_eq] using H
    · apply (ContinuousMap.norm_le _ (by dsimp [M]; positivity)).mpr
      intro x
      have hl := (hLip n).lipschitzOn_ball R.coe_nonneg o (k:ℝ≥0) |>.dist_le_mul x x.property o (by simp)
      have hl : dist (fs n x) (fs n o) ≤ (L k:ℝ)*dist (x:X) o := by
        simpa only [dist_self,zero_add,add_zero,NNReal.coe_mk,NNReal.coe_add,NNReal.coe_natCast,L,add_comm] using hl
      have hd : dist (x:X) o ≤ k := x.property
      have H : |fs n x| ≤ |fs n o|+|fs n x-fs n o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (fs n o) (fs n x)
      change ‖fs n x‖ ≤ _
      rw [Real.norm_eq_abs]
      exact H.trans (add_le_add (hb n) (by rw [← Real.dist_eq]; exact hl.trans (mul_le_mul_of_nonneg_left hd (L k).coe_nonneg)))
  obtain ⟨F,hF,s,hs,ht⟩ := (isCompact_pi_infinite hS).tendsto_subseq (fun n => hvs n)
  have hk (k : ℕ) : Tendsto (fun n => vs (s n) k) atTop (𝓝 (F k)) :=
    (continuous_apply k).tendsto F |>.comp ht
  have hxk (k : ℕ) (x : Q k) : Tendsto (fun n => fs (s n) x) atTop (𝓝 (F k x)) :=
    (continuous_eval_const x).tendsto (F k) |>.comp (hk k)
  have hex (x : X) : ∃ k : ℕ, x ∈ Q k := by
    obtain ⟨k,hk⟩ := exists_nat_ge (dist x o)
    exact ⟨k,hk⟩
  let k (x : X) := (hex x).choose
  let f (x : X) := F (k x) ⟨x,(hex x).choose_spec⟩
  have hp (x : X) : Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x)) := hxk (k x) _
  have he (j : ℕ) (x : Q j) : F j x = f x := tendsto_nhds_unique (hxk j x) (hp x)
  have hf : QuadraticLipschitzBound o R f := by
    intro x y
    exact le_of_tendsto_of_tendsto' ((hp x).sub (hp y) |>.abs) tendsto_const_nhds
      (fun n => hLip (s n) x y)
  refine ⟨f,s,hs,hf,hp,?_⟩
  intro j
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (hk j)) ε hε] with n hn x hx
  have H := ContinuousMap.dist_apply_le_dist (f := vs (s n) j) (g := F j) ⟨x,hx⟩
  change dist (fs (s n) x) (F j ⟨x,hx⟩) ≤ _ at H
  rw [he] at H
  simpa only [dist_comm] using H.trans_lt hn
end WeakHessian

end
end InlinedFile40

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

lemma weakGradient_zero_on_zero {u : X → ℝ} (hu : LocalSobolev m u)
    (hmu : Measurable u) : ∀ᵐ x ∂m, u x = 0 → weakGradient m u x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [weakGradient_locality hu hz (hmu (measurableSet_singleton (0:ℝ)))
    (ae_of_all _ fun x hx => hx),weakGradient_const (m := m) 0] with x h1 h2 hx
  exact (h1 hx).trans h2

end WeakHessian
end
end InlinedFile0

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
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherEpsilon
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
open scoped Topology ENNReal NNReal

lemma fisherEpsilon_pos (n : ℕ) : 0 < fisherEpsilon n := by unfold fisherEpsilon; positivity
lemma fisherEpsilon_tendsto : Tendsto fisherEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile45
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

lemma regularizedRoot_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedRoot a) ((2*Real.sqrt (max a (x+a)))⁻¹) x := by
  have hc : Continuous (fun s : ℝ => (2*Real.sqrt (max a (s+a)))⁻¹) :=
    (continuous_const.mul ((continuous_const.max (continuous_id.add continuous_const)).sqrt)).inv₀
      (fun s => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (ha.trans_le (le_max_left _ _)))))
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma regularizedRoot_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedRoot a) x = (2*Real.sqrt (max a (x+a)))⁻¹ :=
  (regularizedRoot_hasDeriv ha x).deriv

lemma regularizedRoot_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedRoot a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (regularizedRoot_hasDeriv ha x).differentiableAt,?_⟩
  rw [show deriv (regularizedRoot a) = (fun x => (2*Real.sqrt (max a (x+a)))⁻¹) from funext (regularizedRoot_deriv ha)]
  exact (continuous_const.mul ((continuous_const.max (continuous_id.add continuous_const)).sqrt)).inv₀
    (fun s => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (ha.trans_le (le_max_left _ _)))))

lemma regularizedRoot_zero (a : ℝ) : regularizedRoot a 0 = 0 := by simp [regularizedRoot]

lemma regularizedRoot_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedRoot a) x| ≤ (2*Real.sqrt a)⁻¹ := by
  rw [regularizedRoot_deriv ha,abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))]
  exact inv_anti₀ (mul_pos (by norm_num) (Real.sqrt_pos.2 ha))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_left _ _)) (by norm_num))

lemma regularizedRoot_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith (⟨(2*Real.sqrt a)⁻¹,by positivity⟩ : ℝ≥0) (regularizedRoot a) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (regularizedRoot_hasDeriv ha x).differentiableAt)
  intro x
  exact NNReal.coe_le_coe.mp (regularizedRoot_deriv_bound ha x)

lemma regularizedRoot_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedRoot a x = Real.sqrt (x+a)-Real.sqrt a := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 x) :
      HasDerivAt (fun t : ℝ => Real.sqrt (t+a)) ((2*Real.sqrt (max a (s+a)))⁻¹) s := by
    rw [max_eq_right (by linarith [hs.1] : a ≤ s+a),← one_div]
    simpa only [one_div,id_eq] using! ((hasDerivAt_id s).add_const a).sqrt
      (ne_of_gt (by linarith [hs.1] : 0 < s+a))
  have hc : Continuous (fun s : ℝ => (2*Real.sqrt (max a (s+a)))⁻¹) :=
    (continuous_const.mul ((continuous_const.max (continuous_id.add continuous_const)).sqrt)).inv₀
      (fun s => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 (ha.trans_le (le_max_left _ _)))))
  simpa only [regularizedRoot,zero_add] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le hx] using hs)) (hc.intervalIntegrable 0 x)

lemma regularizedRoot_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ regularizedRoot a x ∧ regularizedRoot a x ≤ Real.sqrt x := by
  rw [regularizedRoot_eq ha hx]
  constructor
  · exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  · have h : Real.sqrt (x+a) ≤ Real.sqrt x+Real.sqrt a := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      nlinarith [Real.sq_sqrt hx,Real.sq_sqrt ha.le,
        mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg a)]
    linarith

lemma regularizedRoot_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => regularizedRoot (fisherEpsilon n) x) atTop (𝓝 (Real.sqrt x)) := by
  simp_rw [regularizedRoot_eq (fisherEpsilon_pos _) hx]
  simpa only [Function.comp_def,add_zero,Real.sqrt_zero,sub_zero] using
    (Real.continuous_sqrt.tendsto (x+0) |>.comp (tendsto_const_nhds.add fisherEpsilon_tendsto)).sub
      (Real.continuous_sqrt.tendsto 0 |>.comp fisherEpsilon_tendsto)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.sqrt_of_fisher (hfin : FiniteOnBoundedSets m) {u : X → ℝ}
    (hu : Sobolev m u) (hmu : Measurable u) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    (hi : Integrable u m) (hI : Integrable (fisherDensity (m := m) u) m) :
    Sobolev m (fun x => Real.sqrt (u x)) := by
  let w (x : X) := Real.sqrt (u x)
  have hw : MemLp w 2 m := (memLp_two_iff_integrable_sq hmu.sqrt.aestronglyMeasurable).mpr
    (hi.congr (hun.mono fun x hx => (Real.sq_sqrt hx).symm))
  let fn (n : ℕ) (x : X) := regularizedRoot (fisherEpsilon n) (u x)
  have hfn (n : ℕ) : MemLp (fn n) 2 m :=
    (regularizedRoot_lipschitz (fisherEpsilon_pos n)).comp_memLp
      (regularizedRoot_zero _) hu.1
  have hT : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hw.toLp w)) := by
    apply toLp_tendsto_of_domination hfn hw hw
    · intro n
      filter_upwards [hun] with x hx
      simpa only [fn,w,Real.norm_eq_abs,abs_of_nonneg (regularizedRoot_bounds (fisherEpsilon_pos n) hx).1,
        abs_of_nonneg (Real.sqrt_nonneg _)] using (regularizedRoot_bounds (fisherEpsilon_pos n) hx).2
    · exact hun.mono fun x hx => regularizedRoot_tendsto hx
  let Dn (n : ℕ) (x : X) := |deriv (regularizedRoot (fisherEpsilon n)) (u x)| *weakGradient m u x
  have hDn (n : ℕ) : MemLp (Dn n) 2 m := by
    have hm : AEStronglyMeasurable (fun x => |deriv (regularizedRoot (fisherEpsilon n)) (u x)|) m :=
      ((regularizedRoot_contDiff (fisherEpsilon_pos n)).continuous_deriv le_rfl).measurable.comp hmu |>.abs |>.aestronglyMeasurable
    simpa only [Dn,mul_comm] using memLp_mul_bounded hu.2.2 hm
      (ae_of_all _ fun x => by simpa only [abs_abs] using regularizedRoot_deriv_bound (fisherEpsilon_pos n) (u x))
  have hUG (n : ℕ) : IsLocalWeakUpperGradient m (fn n) (Dn n) :=
    (weakGradient_isMinimal hu.2.1.2).1.comp_contDiff hu.1.aemeasurable
      (regularizedRoot_contDiff (fisherEpsilon_pos n))
        (ae_of_all _ fun x => regularizedRoot_deriv_bound (fisherEpsilon_pos n) (u x))
  have hsq (n : ℕ) : ∀ᵐ x ∂m, Dn n x^2 ≤ fisherDensity (m := m) u x := by
    filter_upwards [hun,weakGradient_zero_on_zero hu.2.1 hmu] with x hx hz
    dsimp only [Dn,fisherDensity]
    rcases hx.eq_or_lt with hx | hx
    · simp [hz hx.symm,hx.symm]
    · rw [regularizedRoot_deriv (fisherEpsilon_pos n),max_eq_right (by linarith : fisherEpsilon n ≤ u x+fisherEpsilon n)]
      have he : (2*Real.sqrt (u x+fisherEpsilon n))^2 = 4*(u x+fisherEpsilon n) := by
        rw [mul_pow,Real.sq_sqrt (by linarith [fisherEpsilon_pos n])]; ring
      rw [mul_pow,sq_abs,inv_pow,he,← div_eq_inv_mul]
      apply div_le_div_of_nonneg_left (sq_nonneg _) hx
      linarith [fisherEpsilon_pos n]
  have hB (n : ℕ) : ‖(hDn n).toLp (Dn n)‖ ≤ Real.sqrt (∫ x,fisherDensity (m := m) u x ∂m) := by
    have H := integral_mono_ae
      ((memLp_two_iff_integrable_sq (hDn n).aestronglyMeasurable).mp (hDn n)) hI (hsq n)
    rw [← norm_toLp_sq_eq_integral (hDn n)] at H
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt H
  obtain ⟨D,hD,hDB⟩ := exists_upperGradient_of_bounded_l2
    (fun n => (hUG n).congr_ae (hfn n).coeFn_toLp.symm (hDn n).coeFn_toLp.symm) hT hB
  exact Sobolev.of_upperGradient hfin hw
    (hD.congr_ae hw.coeFn_toLp Filter.EventuallyEq.rfl) (Lp.memLp D)
end WeakHessian

end
end InlinedFile45

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_QuadraticPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile31
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.quadratic_potential_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) (R : ℝ≥0)
    {T : ℝ≥0} (hTpos : 0 < T)
    {φs : ℕ → X → ℝ} {φ g : X → ℝ}
    (hφs : ∀ n, QuadraticLipschitzBound o T (φs n)) (hφ : QuadraticLipschitzBound o T φ)
    {B : ℝ} (_ : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hg : Sobolev m g) (hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → g x = 0) :
    Tendsto (fun n => ∫ x,gamma m (φs n) g x ∂m) atTop (𝓝 (∫ x,gamma m φ g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := Metric.closedBall o ((R:ℝ)+2)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  let L : ℝ≥0 := T+(R+2)
  obtain ⟨k,hk⟩ := exists_nat_ge (B+(L:ℝ)*(R:ℝ))
  let χ := rootCutoff o R
  let loc (v : X → ℝ) (x : X) := realClip k (v x)*χ x
  let C : ℝ≥0 := L*‖(1:ℝ)‖₊+‖(k:ℝ)‖₊*1
  have hχB (x : X) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (rootCutoff_nonneg o R x)]
    exact rootCutoff_le_one o R x
  have hlocal (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) : LipschitzOnWith L v Q := by
    have H := hv.lipschitzOn_ball T.coe_nonneg o (R+2)
    have hL : NNReal.mk (dist o o+(T:ℝ)+((R+2:ℝ≥0):ℝ)) (by positivity) = L := by
      apply NNReal.eq
      simp [L]
    rw [hL] at H
    simpa only [Q,NNReal.coe_add,NNReal.coe_ofNat] using H
  have hlip (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) : LipschitzWith C (loc v) := by
    obtain ⟨v',hv',hev'⟩ := (hlocal v hv).extend_real
    have hcl : LipschitzWith L (fun x => realClip k (v' x)) := by
      simpa only [one_mul,Function.comp_def] using (realClip_lipschitz k).comp hv'
    have H := lipschitz_mul_bounded hcl (rootCutoff_lipschitz o R) (fun x => realClip_abs_le k (v' x)) hχB
    have heq : loc v = (fun x => realClip k (v' x)*rootCutoff o R x) := by
      funext x
      by_cases hx : x ∈ Q
      · simp only [loc,χ,hev' hx]
      · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (rootCutoff_support o R hh))
        change realClip k (v x)*χ x = realClip k (v' x)*χ x
        rw [hz,mul_zero,mul_zero]
    rw [heq]
    exact H
  have hs (v : X → ℝ) : tsupport (loc v) ⊆ Q :=
    tsupport_mul_subset_right.trans (rootCutoff_support o R)
  have hc (v : X → ℝ) : HasCompactSupport (loc v) :=
    isCompact_closedBall o ((R:ℝ)+2) |>.of_isClosed_subset (isClosed_tsupport _) (hs v)
  have hS (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) : Sobolev m (loc v) :=
    sobolev_of_lipschitz_compactSupport hfin (hlip v hv) (hc v)
  have he (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) (hbv : |v o| ≤ B)
      (x : X) (hx : x ∈ Metric.closedBall o R) : loc v x = v x := by
    have hdist : dist x o ≤ R := hx
    have H : |v x| ≤ (k:ℝ) := by
      have ha : |v x| ≤ |v o|+|v x-v o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (v o) (v x)
      have hbnd := (hlocal v hv).dist_le_mul x (show x ∈ Q from le_trans hdist (by linarith)) o (by change dist o o ≤ (R:ℝ)+2; rw [dist_self]; positivity)
      rw [Real.dist_eq] at hbnd
      exact (ha.trans (add_le_add hbv (hbnd.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)))).trans hk
    simp only [loc,χ,rootCutoff_one hx,mul_one,realClip,
      min_eq_left (abs_le.mp H).2,max_eq_right (abs_le.mp H).1]
  let d := Q.indicator (fun _ : X => (k:ℝ))
  have hd : MemLp d 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hdom (v : X → ℝ) : ∀ᵐ x ∂m, ‖loc v x‖ ≤ ‖d x‖ := by
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Q
    · simp only [loc,d,indicator_of_mem hx,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      exact (mul_le_mul (realClip_abs_le k (v x)) (hχB x) (abs_nonneg _) (Nat.cast_nonneg k)).trans_eq (mul_one _)
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs v h)),norm_zero]
      exact norm_nonneg _
  have hLT : Tendsto (fun n => (hS (φs n) (hφs n)).1.toLp (loc (φs n))) atTop
      (𝓝 ((hS φ hφ).1.toLp (loc φ))) := by
    apply toLp_tendsto_of_domination (fun n => (hS (φs n) (hφs n)).1) (hS φ hφ).1 hd
      (fun n => hdom (φs n))
    exact ae_of_all _ fun x => ((realClip_lipschitz k).continuous.tendsto (φ x) |>.comp (hT x)).mul_const (χ x)
  let D := Q.indicator (fun _ : X => (C:ℝ))
  have hD : MemLp D 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hbD (n : ℕ) : ‖(hS (φs n) (hφs n)).2.2.toLp (weakGradient m (loc (φs n)))‖ ≤ ‖hD.toLp D‖ :=
    norm_gradient_le_supported_lipschitz hfin (hS (φs n) (hφs n)) (hlip _ (hφs n))
      measurableSet_closedBall (hs _) hD
  have H := hcd.integral_gamma_tendsto hfin hq o (fun n => hS _ (hφs n)) (hS φ hφ) hg hLT (norm_nonneg _) hbD
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hp (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) (hbv : |v o| ≤ B) :
      (∫ x,gamma m (loc v) g x ∂m) = ∫ x,gamma m v g x ∂m :=
    integral_gamma_localization hfin hpar (hS v hv).2.1 (hv.localSobolev hfin hTpos) hg.2.1
      measurableSet_closedBall (he v hv hbv) hgs
  simpa only [hp φ hφ hbφ,hp _ (hφs _) (hb _)] using H
end WeakHessian

end
end InlinedFile31

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedPairing2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile27
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma weighted_gamma_bound (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {a u φ W : X → ℝ}
    (ha : AEStronglyMeasurable a m) (hu : Sobolev m u) (hφ : LocalSobolev m φ)
    (hW : ∀ᵐ x ∂m, 0 ≤ W x) (hD : ∀ᵐ x ∂m, weakGradient m φ x ≤ W x)
    (hAW : MemLp (fun x => a x*W x) 2 m) :
    Integrable (fun x => a x*gamma m u φ x) m ∧
      |∫ x,a x*gamma m u φ x ∂m| ≤
        ‖hAW.toLp (fun x => a x*W x)‖*‖hu.2.2.toLp (weakGradient m u)‖ := by
  have hB : ∀ᵐ x ∂m, ‖a x*gamma m u φ x‖ ≤ ‖a x*W x‖*weakGradient m u x := by
    filter_upwards [abs_gamma_le hfin hpar hu.2.1 hφ,hW,hD,
      weakGradient_nonneg (m := m) u] with x hx hw hd hn
    have H := hx.trans (mul_le_mul_of_nonneg_left hd hn)
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left H (abs_nonneg (a x))
  have hi := hAW.norm.integrable_mul hu.2.2
  have hme : AEStronglyMeasurable (fun x => a x*gamma m u φ x) m :=
    ha.mul (gamma_aestronglyMeasurable hfin hu.2.1 hφ)
  have hi' := hi.mono' hme hB
  refine ⟨hi',?_⟩
  have H : |∫ x,a x*gamma m u φ x ∂m| ≤ ∫ x, ‖a x*W x‖*weakGradient m u x ∂m := by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hi'.norm hi hB)
  have J := abs_integral_mul_le_L2_norm hAW.norm hu.2.2
  have hn : ‖hAW.norm.toLp (fun x => ‖a x*W x‖)‖ = ‖hAW.toLp (fun x => a x*W x)‖ := by
    simp only [Lp.norm_toLp,eLpNorm_norm]
  rw [hn] at J
  exact H.trans ((le_abs_self _).trans J)

lemma weighted_gamma_root_difference (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v φ W : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) (hφ : LocalSobolev m φ)
    (hW : ∀ᵐ x ∂m, 0 ≤ W x) (hD : ∀ᵐ x ∂m, weakGradient m φ x ≤ W x)
    (huW : MemLp (fun x => u x*W x) 2 m) (hvW : MemLp (fun x => v x*W x) 2 m)
    (hdW : MemLp (fun x => (u x-v x)*W x) 2 m) :
    |(∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m)| ≤
      ‖hdW.toLp (fun x => (u x-v x)*W x)‖*‖hu.2.2.toLp (weakGradient m u)‖+
      ‖hvW.toLp (fun x => v x*W x)‖*‖(hu.sub hfin hv).2.2.toLp (weakGradient m (fun x => u x-v x))‖ := by
  let hsub := hu.sub hfin hv
  have h1 := weighted_gamma_bound hfin hpar hu.1.aestronglyMeasurable hu hφ hW hD huW
  have h2 := weighted_gamma_bound hfin hpar hv.1.aestronglyMeasurable hv hφ hW hD hvW
  have h3 := weighted_gamma_bound (a := fun x => u x-v x) hfin hpar
    (hu.1.aestronglyMeasurable.sub hv.1.aestronglyMeasurable) hu hφ hW hD hdW
  have h4 := weighted_gamma_bound hfin hpar hv.1.aestronglyMeasurable hsub hφ hW hD hvW
  have he : (∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m) =
      (∫ x,(u x-v x)*gamma m u φ x ∂m)+(∫ x,v x*gamma m (fun y => u y-v y) φ x ∂m) := by
    rw [← integral_sub h1.1 h2.1,← integral_add h3.1 h4.1]
    apply integral_congr_ae
    filter_upwards [gamma_sub_left hfin hpar hu.2.1 hv.2.1 hφ] with x hx
    rw [hx]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h3.2 h4.2)
end WeakHessian

end
end InlinedFile27

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_QuadraticEntropyPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile32
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

lemma tendsto_by_uniform_approximations {a : ℕ → ℝ} {A : ℝ}
    {b : ℕ → ℕ → ℝ} {B e : ℕ → ℝ}
    (hb : ∀ k, Tendsto (b k) atTop (𝓝 (B k))) (he : Tendsto e atTop (𝓝 0))
    (hab : ∀ k n, |a n-b k n| ≤ e k) (hAB : ∀ k, |A-B k| ≤ e k) :
    Tendsto a atTop (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k,hk⟩ := ((he.eventually (eventually_lt_nhds (show (0:ℝ) < ε/3 by positivity))).exists)
  filter_upwards [(Metric.tendsto_nhds.mp (hb k)) (ε/3) (by positivity)] with n hn
  rw [Real.dist_eq] at hn ⊢
  have H : |a n-A| ≤ |a n-b k n|+|b k n-B k|+|B k-A| := by
    have heq : a n-A = (a n-b k n)+(b k n-B k)+(B k-A) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_sub_comm (B k) A] at H
  linarith [hab k n,hAB k]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.quadratic_entropy_pairing_fixed {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) {T : ℝ≥0} (hTpos : 0 < T)
    {φs : ℕ → X → ℝ} {φ w : X → ℝ}
    (hφs : ∀ n, QuadraticLipschitzBound o T (φs n)) (hφ : QuadraticLipschitzBound o T φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hw : Sobolev m w) {A : ℝ} (hA : ∀ᵐ x ∂m, |w x| ≤ A)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m) :
    Tendsto (fun n => ∫ x,w x*gamma m w (φs n) x ∂m) atTop
      (𝓝 (∫ x,w x*gamma m w φ x ∂m)) := by
  have hp : (0:ℝ) < T := hTpos
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  let W (x : X) := dist x o+(T:ℝ)
  let v (k : ℕ) (x : X) := w x*radialCutoff o k x
  obtain ⟨D,hD,hUG,hDT⟩ := radial_root_approximation hfin hw o
  let hv (k : ℕ) : Sobolev m (v k) := Sobolev.of_upperGradient hfin (radial_mul_memLp hw.1 o k) (hUG k) (hD k)
  obtain ⟨hs,hsT⟩ := radial_root_strong hcd hfin hq hw o
  obtain ⟨hdW,hdWT⟩ := radial_weighted_root_tendsto hwW o
  have hvW (k : ℕ) : MemLp (fun x => v k x*W x) 2 m := by
    have he : (fun x => v k x*W x) = fun x => w x*W x*radialCutoff o k x := by funext x; dsimp [v]; ring
    rw [he]
    exact radial_mul_memLp hwW o k
  let e (k : ℕ) := ‖(hdW k).toLp (fun x => (v k x-w x)*W x)‖*‖(hD k).toLp (D k)‖+
    ‖hwW.toLp (fun x => w x*W x)‖*‖(hs k).2.2.toLp (weakGradient m (fun x => v k x-w x))‖
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,zero_add,e,v,W] using (hdWT.mul hDT.norm).add (hsT.const_mul ‖hwW.toLp (fun x => w x*W x)‖)
  have hnorm (k : ℕ) : ‖(hv k).2.2.toLp (weakGradient m (v k))‖ ≤ ‖(hD k).toLp (D k)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hv k).2.2.coeFn_toLp,(hD k).coeFn_toLp,
      (weakGradient_isMinimal (hv k).2.1.2).2 _ (hUG k),weakGradient_nonneg (m := m) (v k)] with x he hd hg hn
    rw [he,hd,Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs]
    exact hg.trans (le_abs_self _)
  have bound (k : ℕ) (f : X → ℝ) (hf : QuadraticLipschitzBound o T f) :
      |(∫ x,w x*gamma m w f x ∂m)-(∫ x,v k x*gamma m (v k) f x ∂m)| ≤ e k := by
    rw [abs_sub_comm]
    have H := weighted_gamma_root_difference hfin hpar (hv k) hw (hf.localSobolev hfin hp)
      (ae_of_all _ fun x => by positivity) (hf.gradient_le hfin hp) (hvW k) hwW (hdW k)
    exact H.trans (add_le_add (mul_le_mul_of_nonneg_left (hnorm k) (norm_nonneg _)) le_rfl)
  have hvA (k : ℕ) : ∀ᵐ x ∂m, |v k x| ≤ A := by
    filter_upwards [hA] with x hx
    dsimp [v]
    rw [abs_mul,abs_of_nonneg (radialCutoff_nonneg o k x)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_le_one o k x)).trans hx
  have fixed (k : ℕ) : Tendsto (fun n => ∫ x,v k x*gamma m (v k) (φs n) x ∂m) atTop
      (𝓝 (∫ x,v k x*gamma m (v k) φ x ∂m)) := by
    have hg := (hv k).square_bounded hfin (hvA k)
    have hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o ((k:ℝ)+1) → (v k x)^2 = 0 := by
      apply ae_of_all
      intro x hx
      have hz : radialCutoff o k x = 0 := by
        have hd : (k:ℝ)+1 ≤ dist x o := le_of_lt (lt_of_not_ge hx)
        unfold radialCutoff
        rw [max_eq_left]
        exact sub_nonpos.mpr ((le_div_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr (by simpa using hd))
      simp [v,hz]
    have H := hcd.quadratic_potential_pairing_tendsto hfin hq o ((k:ℝ≥0)+1)
      hTpos hφs hφ hB hb hbφ hT hg hgs
    have eqn (f : X → ℝ) (hf : QuadraticLipschitzBound o T f) :
        (∫ x,gamma m f (fun x => (v k x)^2) x ∂m) = 2*(∫ x,v k x*gamma m (v k) f x ∂m) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [gamma_comm (m := m) f (fun x => (v k x)^2),
        gamma_square_bounded hfin hpar (hv k) (hf.localSobolev hfin hp) (hvA k)] with x hc he
      rw [hc,he]
      ring
    have J := H.div_const 2
    simp only [eqn _ (hφs _),eqn φ hφ,mul_div_cancel_left₀ _ (two_ne_zero : (2:ℝ) ≠ 0)] at J
    exact J
  exact tendsto_by_uniform_approximations fixed he (fun k n => bound k (φs n) (hφs n)) (fun k => bound k φ hφ)

lemma CurvatureDimension.quadratic_entropy_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) {T : ℝ≥0} (hTpos : 0 < T)
    {φs : ℕ → X → ℝ} {φ w : X → ℝ}
    (hφs : ∀ n, QuadraticLipschitzBound o T (φs n)) (hφ : QuadraticLipschitzBound o T φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hw : Sobolev m w) {A : ℝ} (hA : ∀ᵐ x ∂m, |w x| ≤ A)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m)
    {vs : ℕ → X → ℝ} (hvs : ∀ n, Sobolev m (vs n))
    (hvsW : ∀ n, MemLp (fun x => vs n x*(dist x o+T)) 2 m)
    (hdW : ∀ n, MemLp (fun x => (vs n x-w x)*(dist x o+T)) 2 m)
    (hWT : Tendsto (fun n => ‖(hdW n).toLp (fun x => (vs n x-w x)*(dist x o+T))‖) atTop (𝓝 0))
    (hE : Tendsto (fun n => ‖((hvs n).sub hfin hw).2.2.toLp
      (weakGradient m (fun x => vs n x-w x))‖) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, ‖(hvs n).2.2.toLp (weakGradient m (vs n))‖ ≤ M) :
    Tendsto (fun n => ∫ x,2*vs n x*gamma m (φs n) (vs n) x ∂m) atTop
      (𝓝 (∫ x,2*w x*gamma m φ w x ∂m)) := by
  have hp : (0:ℝ) < T := hTpos
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hbt := (hWT.mul_const M).add (hE.const_mul ‖hwW.toLp (fun x => w x*(dist x o+T))‖)
  simp only [mul_zero,zero_mul,zero_add] at hbt
  have hd : Tendsto (fun n => (∫ x,vs n x*gamma m (vs n) (φs n) x ∂m)-
      (∫ x,w x*gamma m w (φs n) x ∂m)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hbt
    intro n
    rw [Real.norm_eq_abs]
    exact (weighted_gamma_root_difference hfin hpar (hvs n) hw ((hφs n).localSobolev hfin hp)
      (ae_of_all _ fun x => by positivity) ((hφs n).gradient_le hfin hp) (hvsW n) hwW (hdW n)).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)) le_rfl)
  have hf := hcd.quadratic_entropy_pairing_fixed hfin hq o hTpos hφs hφ hB hb hbφ hT hw hA hwW
  have H := (hd.add hf).const_mul 2
  simp only [zero_add,sub_add_cancel] at H
  simp_rw [entropy_pairing_twice hfin (hvs _).2.1 ((hφs _).localSobolev hfin hp),
    entropy_pairing_twice hfin hw.2.1 (hφ.localSobolev hfin hp)]
  exact H
end WeakHessian

end
end InlinedFile32

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RadialEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile30
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

lemma mul_log_product (a b : ℝ) :
    (a*b)*Real.log (a*b) = a*(b*Real.log b)+b*(a*Real.log a) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma entropy_integral_multipliers_tendsto {ρ : X → ℝ}
    (hρ : Integrable ρ m) (hE : Integrable (fun x => ρ x*Real.log (ρ x)) m)
    {a : ℕ → X → ℝ} (ha : ∀ n, AEStronglyMeasurable (a n) m)
    {A : ℝ} (_hA : 0 ≤ A) (haA : ∀ n, ∀ᵐ x ∂m, a n x ∈ Icc 0 A)
    (haT : ∀ᵐ x ∂m, Tendsto (fun n => a n x) atTop (𝓝 1)) :
    (∀ n, Integrable (fun x => (a n x*ρ x)*Real.log (a n x*ρ x)) m) ∧
    Tendsto (fun n => ∫ x,(a n x*ρ x)*Real.log (a n x*ρ x) ∂m) atTop
      (𝓝 (∫ x,ρ x*Real.log (ρ x) ∂m)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := A)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  let B (x : X) := A*|ρ x*Real.log (ρ x)|+C*|ρ x|
  have hBi : Integrable B m := hE.abs.const_mul A |>.add (hρ.abs.const_mul C)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => (a n x*ρ x)*Real.log (a n x*ρ x)) m :=
    Real.continuous_mul_log.comp_aestronglyMeasurable ((ha n).mul hρ.1)
  have hb (n : ℕ) : ∀ᵐ x ∂m, ‖(a n x*ρ x)*Real.log (a n x*ρ x)‖ ≤ B x := by
    filter_upwards [haA n] with x hx
    rw [mul_log_product,Real.norm_eq_abs]
    apply (abs_add_le _ _).trans
    dsimp [B]
    simp only [abs_mul,abs_of_nonneg hx.1]
    exact add_le_add (mul_le_mul_of_nonneg_right hx.2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (by simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx.1,mul_comm] using mul_le_mul_of_nonneg_left (hC _ hx) (abs_nonneg (ρ x)))
  refine ⟨fun n => hBi.mono' (hm n) (hb n),?_⟩
  apply tendsto_integral_of_dominated_convergence B hm hBi hb
  filter_upwards [haT] with x hx
  have ht : Tendsto (fun n => a n x*ρ x) atTop (𝓝 (ρ x)) := by simpa using hx.mul_const (ρ x)
  exact (Real.continuous_mul_log.tendsto (ρ x)).comp ht

lemma squareDensity_entropy_eq [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    entropyReal m (squareDensityMeasure m w) = ∫ x,w x^2*Real.log (w x^2) ∂m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [entropyReal_eq_integral_density hac]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma squareDensity_finiteEntropy_iff [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    [IsFiniteMeasure (squareDensityMeasure m w)] :
    FiniteEntropy m (squareDensityMeasure m w) ↔ Integrable (fun x => w x^2*Real.log (w x^2)) m := by
  have hac : squareDensityMeasure m w ≪ m := withDensity_absolutelyContinuous _ _
  rw [FiniteEntropy,and_iff_right hac,← integrable_rnDeriv_mul_log_iff hac]
  apply integrable_congr
  filter_upwards [Measure.rnDeriv_withDensity m (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)] with x hx
  simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]

variable [MetricSpace X] [BorelSpace X]

lemma normalized_radial_entropy_tendsto [SigmaFinite m] {w : X → ℝ}
    (hw : MemLp w 2 m) (hwm : Measurable w) [IsProbabilityMeasure (squareDensityMeasure m w)]
    (hE : FiniteEntropy m (squareDensityMeasure m w)) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 2) (hcT : Tendsto c atTop (𝓝 1))
    (hp : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)))) :
    (∀ n, FiniteEntropy m (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)))) ∧
    Tendsto (fun n => entropyReal m (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x))))
      atTop (𝓝 (entropyReal m (squareDensityMeasure m w))) := by
  let a (n : ℕ) (x : X) := (c n*radialCutoff o (n+k) x)^2
  have ha n : AEStronglyMeasurable (a n) m := by
    exact (((radialCutoff_lipschitz o (n+k)).continuous.const_mul (c n)).pow 2).aestronglyMeasurable
  have hA n : ∀ᵐ x ∂m, a n x ∈ Icc (0:ℝ) 4 := by
    apply ae_of_all
    intro x
    have hn : 0 ≤ c n*radialCutoff o (n+k) x := mul_nonneg (hc n).1 (radialCutoff_nonneg o (n+k) x)
    have hb : c n*radialCutoff o (n+k) x ≤ 2 :=
      (mul_le_of_le_one_right (hc n).1 (radialCutoff_le_one o (n+k) x)).trans (hc n).2
    exact ⟨sq_nonneg _,by dsimp [a]; nlinarith⟩
  have haT : ∀ᵐ x ∂m, Tendsto (fun n => a n x) atTop (𝓝 1) := ae_of_all _ fun x => by
    simpa only [one_mul,one_pow,a,Function.comp_apply] using (hcT.mul ((radialCutoff_tendsto o x).comp (tendsto_add_atTop_nat k))).pow 2
  have he (n : ℕ) (x : X) : (c n*(w x*radialCutoff o (n+k) x))^2 = a n x*w x^2 := by dsimp [a]; ring
  have H := entropy_integral_multipliers_tendsto hw.integrable_sq
    ((squareDensity_finiteEntropy_iff hwm).mp hE) ha (by norm_num : (0:ℝ) ≤ 4) hA haT
  have hm (n : ℕ) : Measurable (fun x => c n*(w x*radialCutoff o (n+k) x)) :=
    (hwm.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).const_mul _
  constructor
  · intro n
    let := hp n
    apply (squareDensity_finiteEntropy_iff (hm n)).mpr
    simpa only [he] using H.1 n
  · have eqn (n : ℕ) : entropyReal m (squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x))) =
        ∫ x,(a n x*w x^2)*Real.log (a n x*w x^2) ∂m := by
      let := hp n
      rw [squareDensity_entropy_eq (hm n)]
      simp only [he]
    simp_rw [eqn,squareDensity_entropy_eq hwm]
    exact H.2
end WeakHessian

end
end InlinedFile30

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile44
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.local_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A φ : X → ℝ}
    (hu : IsLaplacian m u A) (hφ : LocalSobolev m φ)
    (hAφ : Integrable (fun x => A x*φ x) m)
    (hγ : Integrable (gamma m u φ) m)
    (hDφ : Integrable (fun x => |φ x| *weakGradient m u x) m) :
    (∫ x,A x*φ x ∂m) = -(∫ x,gamma m u φ x ∂m) := by
  let : Nonempty X := ⟨o⟩
  have hχs (n : ℕ) := localSobolev_of_lipschitz hfin (radialCutoff_lipschitz o n)
  have hχB (n : ℕ) : ∀ᵐ x ∂m, |weakGradient m (radialCutoff o n) x| ≤ ((n:ℝ)+1)⁻¹ := by
    filter_upwards [weakGradient_nonneg (m := m) (radialCutoff o n),
      weakGradient_le_lipschitz hfin (radialCutoff_lipschitz o n)] with x hn hb
    rwa [abs_of_nonneg hn]
  have hcross (n : ℕ) : ∀ᵐ x ∂m, |φ x*gamma m u (radialCutoff o n) x| ≤
      ((n:ℝ)+1)⁻¹*(|φ x| *weakGradient m u x) := by
    filter_upwards [abs_gamma_lipschitz_le hfin hpar hu.1.2.1 (radialCutoff_lipschitz o n)] with x hx
    rw [abs_mul]
    simp only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hx
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans_eq (by ring)
  have hi (n : ℕ) : Integrable (fun x => φ x*gamma m u (radialCutoff o n) x) m :=
    (hDφ.const_mul _).mono' (hφ.1.aestronglyMeasurable.mul
      (gamma_aestronglyMeasurable hfin hu.1.2.1 (hχs n))) (hcross n)
  have he (n : ℕ) : (∫ x,A x*φ x*radialCutoff o n x ∂m) =
      -(∫ x,gamma m u φ x*radialCutoff o n x ∂m)-
      (∫ x,φ x*gamma m u (radialCutoff o n) x ∂m) := by
    have H := hu.2.2 (fun x => φ x*radialCutoff o n x)
      (hφ.mul_lipschitz_compactSupport hfin (radialCutoff_lipschitz o n) (radialCutoff_compact o n))
    have hp := gamma_mul_left hfin hpar hφ (hχs n) hu.1.2.1
      (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x) (hχB n)
    have hg : gamma m u (fun x => φ x*radialCutoff o n x) =ᵐ[m]
        (fun x => φ x*gamma m u (radialCutoff o n) x+radialCutoff o n x*gamma m u φ x) := by
      filter_upwards [hp,gamma_comm (m := m) u (fun x => φ x*radialCutoff o n x),
        gamma_comm (m := m) (radialCutoff o n) u,gamma_comm (m := m) φ u] with x h1 h2 h3 h4
      rw [h2,h1,h3,h4]
    have hg2 : Integrable (fun x => radialCutoff o n x*gamma m u φ x) m :=
      hγ.bdd_mul (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
    rw [integral_congr_ae hg,integral_add (hi n) hg2] at H
    simp_rw [mul_assoc,mul_comm (radialCutoff o n _)] at H ⊢
    linarith
  have hn (n : ℕ) : ‖∫ x,φ x*gamma m u (radialCutoff o n) x ∂m‖ ≤
      ((n:ℝ)+1)⁻¹*(∫ x,|φ x| *weakGradient m u x ∂m) := by
    simpa only [integral_const_mul] using norm_integral_le_of_norm_le (hDφ.const_mul ((n:ℝ)+1)⁻¹) (hcross n)
  have hc0 : Tendsto (fun n => ∫ x,φ x*gamma m u (radialCutoff o n) x ∂m) atTop (𝓝 0) := by
    apply squeeze_zero_norm hn
    simpa only [one_div,zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (∫ x,|φ x| *weakGradient m u x ∂m)
  have H := (integral_radialCutoff_tendsto o hγ).neg.sub hc0
  simp only [sub_zero] at H
  simp_rw [← he] at H
  exact tendsto_nhds_unique (integral_radialCutoff_tendsto o hAφ) H

lemma IsLaplacian.quadratic_weighted_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A : Lp ℝ 2 m}
    (hu : IsLaplacian m u A) {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {R : ℝ} (hR : 0 < R) {φ : X → ℝ} (hφ : QuadraticLipschitzBound o R φ)
    (hφW : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hDW : MemLp (fun x => (dist x o+R)*Real.exp (-V x)) 2 m) :
    (∫ x,A x*φ x ∂m) = -(∫ x,gamma m u φ x ∂m) := by
  have hD := hu.memLp_gradient_mul_exp hfin hpar hV hU hA
  have hφS := hφ.localSobolev hfin hR
  apply hu.local_pairing hfin hpar o hφS (weighted_pairing hA hφW).1
  · apply (weighted_pairing hD hDW).1.mono' (gamma_aestronglyMeasurable hfin hu.1.2.1 hφS)
    filter_upwards [abs_gamma_le hfin hpar hu.1.2.1 hφS,hφ.gradient_le hfin hR,
      weakGradient_nonneg (m := m) u] with x hx hy hn
    exact hx.trans (mul_le_mul_of_nonneg_left hy hn)
  · have ha : MemLp (fun x => |φ x| *Real.exp (-V x)) 2 m := by
      convert hφW.norm using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have H := (weighted_pairing hD ha).1
    simpa only [mul_comm] using H
end WeakHessian

end
end InlinedFile44

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_QuadraticVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile38
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma quadratic_integral_tendsto_measure {μ : Measure X} {o : X} {R : ℝ} (hR : 0 ≤ R)
    {fs : ℕ → X → ℝ} {f : X → ℝ}
    (hfs : ∀ n, QuadraticLipschitzBound o R (fs n)) (_hf : QuadraticLipschitzBound o R f)
    (hz : ∀ n, fs n o = 0) (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hW : Integrable (fun x => (dist x o+R)^2) μ) :
    Tendsto (fun n => ∫ x,fs n x ∂μ) atTop (𝓝 (∫ x,f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (dist x o+R)^2)
  · intro n; exact ((hfs n).continuous hR).aestronglyMeasurable
  · exact hW
  · intro n; exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hfs n).centered_bound hR (hz n) x
  · exact ae_of_all _ ht

lemma quadratic_moving_density_integral_tendsto {o : X} {R : ℝ} (hR : 0 ≤ R)
    {fs : ℕ → X → ℝ} {f w : X → ℝ} {us : ℕ → X → ℝ}
    (hfs : ∀ n, QuadraticLipschitzBound o R (fs n)) (hf : QuadraticLipschitzBound o R f)
    (hz : ∀ n, fs n o = 0) (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hwm : Measurable w) (hum : ∀ n, Measurable (us n))
    (hwW : MemLp (fun x => w x*(dist x o+R)) 2 m)
    (huW : ∀ n, MemLp (fun x => us n x*(dist x o+R)) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*(dist x o+R))^2-(w x*(dist x o+R))^2| ∂m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,fs n x ∂squareDensityMeasure m (us n)) atTop
      (𝓝 (∫ x,f x ∂squareDensityMeasure m w)) := by
  have hD : Tendsto (fun n => (∫ x,fs n x ∂squareDensityMeasure m (us n))-
      (∫ x,fs n x ∂squareDensityMeasure m w)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hTV
    intro n
    exact squareDensity_quadratic_pairing_bound (hum n) hwm (huW n) hwW
      ((hfs n).continuous hR).aestronglyMeasurable (ae_of_all _ fun x => (hfs n).centered_bound hR (hz n) x)
  have H := hD.add (quadratic_integral_tendsto hR hfs hf hz ht hwm hwW)
  simpa only [zero_add,sub_add_cancel] using H

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
lemma limit_quadratic_transport_support
    {us : ℕ → X → ℝ} {w : X → ℝ} (hum : ∀ n, Measurable (us n)) (hwm : Measurable w)
    (o : X) (R : ℝ≥0)
    (huW : ∀ n, MemLp (fun x => us n x*(dist x o+R)) 2 m)
    (hwW : MemLp (fun x => w x*(dist x o+R)) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*(dist x o+R))^2-(w x*(dist x o+R))^2| ∂m) atTop (𝓝 0))
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = squareDensityMeasure m (us n))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    (φs ψs : ℕ → X → ℝ) (φ : X → ℝ)
    (hφs : ∀ n, QuadraticLipschitzBound o R (φs n)) (hφ : QuadraticLipschitzBound o R φ)
    (hz : ∀ n, φs n o = 0) (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hψ : ∀ n, Continuous (ψs n)) (hiψ : ∀ n, Integrable (ψs n) (ν:Measure X))
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ n x y, y ∈ S → φs n x+ψs n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)), φs n (γ timeZero)+ψs n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    {E : ℝ} (hE : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E))
    (ξ : ProbabilityMeasure X) (hξW : Integrable (fun x => (dist x o+R)^2) (ξ:Measure X))
    {q : Measure (X×X)} (hq : IsCoupling q ξ ν) (hqt : QuadraticTransportCost q ≠ ∞) :
    E-(QuadraticTransportCost q).toReal ≤
      2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X))) := by
  have ip (n : ℕ) := (squareDensity_integrable_of_quadratic_bound (hum n) (huW n)
    ((hφs n).continuous R.coe_nonneg).aestronglyMeasurable (ae_of_all _ fun x => (hφs n).centered_bound R.coe_nonneg (hz n) x)).1
  have iq (n : ℕ) : Integrable (φs n) (ξ:Measure X) :=
    hξW.mono' ((hφs n).continuous R.coe_nonneg).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hφs n).centered_bound R.coe_nonneg (hz n) x)
  have hv := quadratic_moving_density_integral_tendsto R.coe_nonneg hφs hφ hz ht hwm hum hwW huW hTV
  have hx := quadratic_integral_tendsto_measure R.coe_nonneg hφs hφ hz ht hξW
  have heq : (QuadraticTransportCost q).toReal = ∫ p : X×X,dist p.1 p.2^2 ∂q := by
    rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [heq,hμ]
  apply le_of_tendsto_of_tendsto' (hE.sub_const _) ((hv.sub hx).const_mul 2)
  intro n
  simpa only [h0 n] using planEnergy_le_coupling_of_restricted_contact hqt ξ ν hq (h1 n)
    ((hφs n).continuous R.coe_nonneg) (hψ n) (h0 n ▸ ip n) (iq n) (hiψ n) hS hs (hd n) (hc n)
end WeakHessian

end
end InlinedFile38

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_RadialGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile39
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma normalized_radial_gradient_bounded (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hcn : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 1))
    (hs : ∀ n, Sobolev m (fun x => c n*(w x*radialCutoff o (n+k) x))) :
    ∃ M : ℝ, ∀ n, ‖(hs n).2.2.toLp (weakGradient m (fun x => c n*(w x*radialCutoff o (n+k) x)))‖ ≤ M := by
  obtain ⟨Ds,hDs,hUG,hDT⟩ := radial_root_approximation hfin hw o
  let Es (n : ℕ) (x : X) := c n*Ds (n+k) x
  let hEs (n : ℕ) : MemLp (Es n) 2 m := (hDs (n+k)).const_mul (c n)
  have hEU (n : ℕ) : IsLocalWeakUpperGradient m (fun x => c n*(w x*radialCutoff o (n+k) x)) (Es n) := by
    simpa only [abs_of_nonneg (hcn n),Es] using (hUG (n+k)).const_mul (c n)
  have hET : Tendsto (fun n => (hEs n).toLp (Es n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
    have H := hc.smul (hDT.comp (tendsto_add_atTop_nat k))
    have he (n : ℕ) : (hEs n).toLp (Es n) = c n • (hDs (n+k)).toLp (Ds (n+k)) :=
      (hDs (n+k)).toLp_const_smul (c n)
    simp_rw [he]
    simpa only [Function.comp_apply,one_smul] using H
  obtain ⟨M,_hM,hMb⟩ := (Metric.isBounded_range_of_tendsto (fun n => ‖(hEs n).toLp (Es n)‖) hET.norm).exists_pos_norm_le
  refine ⟨M,fun n => ?_⟩
  have H := sqrt_gradient_energy_le_upper (hs n) (hEU n) (hEs n)
  rw [← norm_toLp_sq_eq_integral (hs n).2.2,Real.sqrt_sq (norm_nonneg _)] at H
  exact H.trans (by simpa only [Real.norm_eq_abs,abs_norm] using hMb _ (mem_range_self n))
end WeakHessian

end
end InlinedFile39

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_NoncompactSubgradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile41
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m]

theorem RCD.noncompact_entropy_subdifferential {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (hEnt : FiniteEntropy m (μ:Measure X))
    (o : X) (T : ℝ≥0) (hT : 0 < T)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*(QuadraticTransportCost q).toReal ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw.1 hwm o
  let us (n : ℕ) (x : X) := c n*(w x*radialCutoff o (n+k) x)
  have hum (n : ℕ) : Measurable (us n) :=
    (hwm.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).const_mul _
  have hu2 (n : ℕ) : MemLp (us n) 2 m := (radial_mul_memLp hw.1 o (n+k)).const_mul (c n)
  have hcn (n : ℕ) : 0 ≤ c n := (hc n).1.le
  obtain ⟨hus,hstrong⟩ := hrcd.1.normalized_radial_root_strong hfin hrcd.2 hw o k hcn hcT
  have hus' (n : ℕ) : Sobolev m (us n) := hus n
  obtain ⟨M,hM⟩ := normalized_radial_gradient_bounded hfin hw o k hcn hcT hus
  have hU (n : ℕ) : ∀ᵐ x ∂m, 0 ≤ us n x ∧ us n x ≤ 2*B := by
    filter_upwards [hwn,hwB] with x hx hxb
    refine ⟨mul_nonneg (hcn n) (mul_nonneg hx (radialCutoff_nonneg o (n+k) x)),?_⟩
    have H : w x*radialCutoff o (n+k) x ≤ B := (mul_le_of_le_one_right hx (radialCutoff_le_one o (n+k) x)).trans hxb
    exact (mul_le_mul_of_nonneg_left H (hcn n)).trans (mul_le_mul_of_nonneg_right (hc n).2 hB)
  let μs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (us n) (hp n)
  have hμs (n : ℕ) : (μs n:Measure X) = squareDensityMeasure m (us n) := rfl
  let R (n : ℕ) : ℝ≥0 := (n+k:ℕ)+1
  have hsμ (n : ℕ) : (μs n:Measure X) (Metric.closedBall o (R n))ᶜ = 0 := by
    apply ae_iff.mp
    apply squareDensity_ae_support (hum n)
    apply ae_of_all
    intro x hx
    have hdn : ((n+k:ℕ):ℝ)+1 ≤ dist x o := by
      have H : ¬dist x o ≤ (R n:ℝ) := hx
      simpa only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using (not_le.mp H).le
    have hz : radialCutoff o (n+k) x = 0 := by
      unfold radialCutoff
      rw [max_eq_left]
      exact sub_nonpos.mpr ((le_div_iff₀ (by positivity : (0:ℝ)<((n+k:ℕ):ℝ)+1)).mpr (by simpa using hdn))
    simp only [us,hz,mul_zero]
  have hμT : Tendsto μs atTop (𝓝 μ) := by
    have H := squareDensity_tendsto_probability hum hwm hu2 hw.1 hp inferInstance (normalized_radial_tendsto hw.1 o k hcT)
    have he : squareDensityProbability m w inferInstance = μ := ProbabilityMeasure.toMeasure_injective hμ.symm
    simpa only [he] using H
  have heT := normalized_radial_entropy_tendsto hw.1 hwm (hμ ▸ hEnt) o k
    (fun n => ⟨hcn n,(hc n).2⟩) hcT hp
  have huW (n : ℕ) : MemLp (fun x => us n x*(dist x o+T)) 2 m := by
    convert ((radial_mul_memLp hwW o (n+k)).const_mul (c n)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x; dsimp [us]; ring
  obtain ⟨hdW,hWT⟩ := normalized_radial_weighted_tendsto hwW o k hcT
  have hTV := radial_weighted_density_tendsto hwW o k hcT
  have hex (n : ℕ) := hrcd.compact_quadratic_entropy_subgradient hN hfin (us n) (hus' n) (hum n)
    (by positivity : 0 ≤ 2*B) ((hU n).mono fun _ hx => hx.1) ((hU n).mono fun _ hx => hx.2)
    (μs n) ν (hμs n) o (R n) T hT (hsμ n) hsν hCt hdν
  choose ps fs gs hbps hops hfs hzero hgs hdual hcontact hent using hex
  have h0 (n : ℕ) := (hops n).1.interpolation_endpoints.1
  have h1 (n : ℕ) := (hops n).1.interpolation_endpoints.2
  have hcf (n : ℕ) := (hfs n).continuous T.coe_nonneg
  have hcg (n : ℕ) := (hgs n).choose_spec.continuous
  have hsb : ∀ᵐ y ∂(ν:Measure X), y ∈ Metric.closedBall o T := ae_iff.mpr hsν
  have hig (n : ℕ) : Integrable (gs n) (ν:Measure X) :=
    LipschitzWith.integrable_supported_ball (hgs n).choose_spec o T hsb
  have hfbd (n : ℕ) : ∀ᵐ x ∂m, |fs n x| ≤ (dist x o+T)^2 :=
    ae_of_all _ fun x => (hfs n).centered_bound T.coe_nonneg (hzero n) x
  obtain ⟨q,hqp,hqo,hqt,hcost⟩ := exists_noncompact_optimal_of_quadratic_contacts hum hwm huW hwW hTV
    μ ν hμ μs hμs hμT ps (fun n => (hbps n).integrable_length_sq) h0 h1 fs gs hcf hcg hig hfbd
    measurableSet_closedBall hsb hdual hcontact
  obtain ⟨φ,s,hs,hφ,hφT,hφU⟩ := exists_quadratic_locally_uniform_subsequence o T fs hfs (by norm_num : (0:ℝ) ≤ 0)
    (fun n => by simp only [hzero n,abs_zero,le_refl])
  have hφo : φ o = 0 := tendsto_nhds_unique (hφT o) (by simpa only [hzero] using (tendsto_const_nhds (x := (0:ℝ))))
  refine ⟨q,φ,hqp,hqo,hqt,hφ,hφo,?_,?_⟩
  · intro ξ hξ q' hq' hq't
    exact limit_quadratic_transport_support (fun n => hum (s n)) hwm o T (fun n => huW (s n)) hwW
      (hTV.comp hs.tendsto_atTop) μ ν hμ (fun n => ps (s n)) (fun n => (h0 (s n)).trans (hμs (s n)))
      (fun n => h1 (s n)) (fun n => fs (s n)) (fun n => gs (s n)) φ (fun n => hfs (s n)) hφ
      (fun n => hzero (s n)) hφT (fun n => hcg (s n)) (fun n => hig (s n)) measurableSet_closedBall hsb
      (fun n => hdual (s n)) (fun n => hcontact (s n)) (hcost.comp hs.tendsto_atTop) ξ hξ hq' hq't
  · have hpair := hrcd.1.quadratic_entropy_pairing_tendsto hfin hrcd.2 o hT
      (fun n => hfs (s n)) hφ (by norm_num : (0:ℝ) ≤ 0)
      (fun n => by simp only [hzero,abs_zero,le_refl]) (by simp only [hφo,abs_zero,le_refl]) hφT hw
      (hwn.and hwB |>.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2) hwW
      (fun n => hus' (s n)) (fun n => huW (s n)) (fun n => hdW (s n))
      (hWT.comp hs.tendsto_atTop) (hstrong.comp hs.tendsto_atTop) (fun n => hM (s n))
    have hEntT : Tendsto (fun n => entropyReal m (μs (s n):Measure X)) atTop (𝓝 (entropyReal m (μ:Measure X))) := by
      rw [hμ]
      exact heT.2.comp hs.tendsto_atTop
    exact le_of_tendsto_of_tendsto' ((hEntT.sub_const _).add ((hcost.comp hs.tendsto_atTop).const_mul (K/2)))
      hpair (fun n => hent (s n))
end WeakHessian

end
end InlinedFile41

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

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma QuadraticLipschitzBound.weighted_memLp (o : X) {T : ℝ} (hT : 0 ≤ T)
    {φ V : X → ℝ} (hφ : QuadraticLipschitzBound o T φ) (hzero : φ o = 0)
    (hV : Measurable V) (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    MemLp (fun x => φ x*Real.exp (-V x)) 2 m := by
  apply hW.mono ((hφ.continuous hT).aestronglyMeasurable.mul (hV.neg.exp.aestronglyMeasurable))
  apply ae_of_all
  intro x
  change |φ x*Real.exp (-V x)| ≤ |(dist x o+T)^2*Real.exp (-V x)|
  simp only [abs_mul,abs_of_nonneg (sq_nonneg (dist x o+T)),abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hφ.centered_bound hT hzero x) (Real.exp_pos _).le

variable [SigmaFinite m]

theorem RCD.generator_entropy_subdifferential_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (o : X) {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m, u x ≤ B)
    (hI : Integrable (fisherDensity (m := m) u) m)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hEnt : FiniteEntropy m (μ:Measure X))
    (T : ℝ≥0) (hT : 0 < T)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*(QuadraticTransportCost q).toReal ≤
        -(∫ x,A x*φ x ∂m) := by
  let w (x : X) := Real.sqrt (u x)
  have hum := (Lp.stronglyMeasurable u).measurable
  have hw := hu.1.sqrt_of_fisher hfin hum hun hi hI
  have hwm : Measurable w := hum.sqrt
  have hwn : ∀ᵐ x ∂m, 0 ≤ w x := ae_of_all _ fun x => Real.sqrt_nonneg _
  have hwB : ∀ᵐ x ∂m, w x ≤ Real.sqrt B :=
    huB.mono fun x hx => (Real.sqrt_le_sqrt_iff hB).mpr hx
  have hwW : MemLp (fun x => w x*(dist x o+T)) 2 m := by
    apply (memLp_two_iff_integrable_sq (hwm.aestronglyMeasurable.mul
      (continuous_id.dist continuous_const |>.add continuous_const).aestronglyMeasurable)).mpr
    exact (weighted_pairing hU hW).1.congr (hun.mono fun x hx => by
      change u x*(dist x o+T)^2 = (Real.sqrt (u x)*(dist x o+T))^2
      rw [mul_pow,Real.sq_sqrt hx])
  have hμw : (μ:Measure X) = squareDensityMeasure m w := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar,hent⟩ := hrcd.noncompact_entropy_subdifferential hN hfin
    w hw hwm (Real.sqrt_nonneg B) hwn hwB μ ν hμw hEnt o T hT hwW hsν hCt hdν
  refine ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar,?_⟩
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hV.continuous.measurable hW
  have hp := hu.quadratic_weighted_pairing hfin hpar o hV hU hA
    (show (0:ℝ)<T from hT) hφ hφW hD
  have hsq : (fun x => w x^2) =ᵐ[m] u := hun.mono fun x hx => Real.sq_sqrt hx
  have hg : gamma m u φ =ᵐ[m] (fun x => 2*w x*gamma m φ w x) := by
    filter_upwards [gamma_square_bounded hfin hpar hw (hφ.localSobolev hfin hT) (B := Real.sqrt B)
      (hwn.and hwB |>.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2),
      gamma_congr_ae hsq Filter.EventuallyEq.rfl,gamma_comm (m := m) w φ] with x h1 h2 h3
    rw [← h2,h1,h3]
  rw [integral_congr_ae hg] at hp
  linarith
end WeakHessian

end
end InlinedFile46

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.generator_entropy_subdifferential_oai.{u_1} := @OAI.WeakHessian.RCD.generator_entropy_subdifferential_oai.{u_1}
