-- Prove2me | solution 1 for OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:54:35.883982+00:00
-- url     : https://prove2.me/submissions/9956338c-0c35-4611-8538-bf78f810d6f5

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_generator_entropy_subdifferential

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CcConst
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
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]

lemma exists_marginal_majorant (h : C_c(X×Y,ℝ)) :
    ∃ fg : C_c(X,ℝ) × C_c(Y,ℝ), h ≤ marginalSum fg := by
  refine ⟨(ccConst X ‖h.toContinuousMap‖,0), ?_⟩
  intro p
  change h.toContinuousMap p ≤ ‖h.toContinuousMap‖ + 0
  simpa only [add_zero] using h.toContinuousMap.apply_le_norm p

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

lemma integral_marginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    ∫ p, marginalSum fg p ∂μ.prod ν = marginalIntegral μ ν fg := by
  rw [integral_prod _ (marginalSum fg).integrable]
  simp only [marginalSum_apply, marginalIntegral_apply]
  have H (x : X) : (∫ y, (fg.1 x + fg.2 y) ∂ν) = fg.1 x + ∫ y, fg.2 y ∂ν := by
    rw [integral_add (integrable_const _) fg.2.integrable]
    simp
  simp_rw [H]
  rw [integral_add fg.1.integrable (integrable_const _)]
  simp

lemma exists_measure_of_positive_functional
    (g : C_c(X,ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g) :
    ∃ q : Measure X, IsFiniteMeasure q ∧
      ∀ f : C_c(X,ℝ), (∫ x, f x ∂q) = g f := by
  let Λ : C_c(X,ℝ) →ₚ[ℝ] ℝ := { g with monotone' := hg }
  exact ⟨RealRMK.rieszMeasure Λ, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), RealRMK.integral_rieszMeasure Λ⟩

omit [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y] [BorelSpace X] [BorelSpace Y] in
lemma probability_of_first_marginal {μ : Measure X} [IsProbabilityMeasure μ]
    {q : Measure (X×Y)} (hfst : q.map Prod.fst = μ) : IsProbabilityMeasure q := by
  constructor
  have H := congrArg (fun η : Measure X => η univ) hfst
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    measure_univ] using H

lemma integral_marginalSum_of_marginals (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)}
    (hfst : q.map Prod.fst = μ) (hsnd : q.map Prod.snd = ν)
    (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg := by
  let _ := probability_of_first_marginal hfst
  have h0 : Integrable (fun p : X×Y => fg.1 p.1) q :=
    (fg.1.continuous.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun p : X×Y => fg.2 p.2) q :=
    (fg.2.continuous.comp continuous_snd).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ p, fg.1 p.1+fg.2 p.2 ∂q) = _
  rw [integral_add h0 h1]
  rw [← integral_map (μ := q) (f := fg.1) measurable_fst.aemeasurable (map_continuous fg.1).aestronglyMeasurable,
    ← integral_map (μ := q) (f := fg.2) measurable_snd.aemeasurable (map_continuous fg.2).aestronglyMeasurable,
    hfst, hsnd]
  rfl

lemma marginals_of_integral_identity (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)}
    [IsFiniteMeasure q]
    (hq : ∀ fg : C_c(X,ℝ) × C_c(Y,ℝ),
      (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg) :
    q.map Prod.fst = μ ∧ q.map Prod.snd = ν := by
  constructor
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable]
    simpa only [marginalSum_apply, marginalIntegral_apply,
      CompactlySupportedContinuousMap.zero_apply, add_zero, integral_zero] using hq (f,0)
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_snd.aemeasurable (map_continuous f).aestronglyMeasurable]
    simpa only [marginalSum_apply, marginalIntegral_apply,
      CompactlySupportedContinuousMap.zero_apply, zero_add, integral_zero] using hq (0,f)

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_QuadraticCost
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
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

local instance ccPosSMulMono : PosSMulMono ℝ C_c(X×Y,ℝ) where
  smul_le_smul_of_nonneg_left r hr f g hfg := by
    intro p
    exact mul_le_mul_of_nonneg_left (hfg p) hr

lemma compact_kantorovich_duality (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (cost : C_c(X×Y,ℝ)) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×Y), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, cost p ∂q) ≤ ∫ p, cost p ∂q') ∧
      ∀ ε : ℝ, 0 < ε → ∃ fg : C_c(X,ℝ) × C_c(Y,ℝ),
        marginalSum fg ≤ cost ∧
        (∫ p, cost p ∂q) < marginalIntegral μ ν fg + ε := by
  let T : (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] C_c(X×Y,ℝ) := marginalSum
  let c := marginalIntegral μ ν
  let l := (integralPositiveLinearMap (μ.prod ν)).toLinearMap
  have hl : Monotone l := (integralPositiveLinearMap (μ.prod ν)).monotone
  have hcomp : ∀ fg, l (T fg) = c fg := integral_marginalSum μ ν
  have hmajor : ∀ h, ∃ fg, h ≤ T fg := exists_marginal_majorant
  obtain ⟨g,hgpos,hgmarg,hgcost⟩ := exists_envelope_support T c l hl hcomp hmajor (-cost)
  obtain ⟨q,hqfinite,hq⟩ := exists_measure_of_positive_functional g hgpos
  let _ := hqfinite
  have hqsum (fg) : (∫ p, marginalSum fg p ∂q) = marginalIntegral μ ν fg :=
    (hq (T fg)).trans (hgmarg fg)
  obtain ⟨hq0,hq1⟩ := marginals_of_integral_identity μ ν hqsum
  have hcq : (∫ p, cost p ∂q) = - upperEnvelope T c (-cost) := by
    have H := (hq (-cost)).trans hgcost
    change (∫ p, -cost p ∂q) = upperEnvelope T c (-cost) at H
    rw [integral_neg] at H
    linarith
  refine ⟨q, probability_of_first_marginal hq0, hq0, hq1, ?_, ?_⟩
  · intro q' hq'0 hq'1
    let _ := probability_of_first_marginal hq'0
    let l' := (integralPositiveLinearMap q').toLinearMap
    have hl' : Monotone l' := (integralPositiveLinearMap q').monotone
    have hcomp' : ∀ fg, l' (T fg) = c fg := integral_marginalSum_of_marginals μ ν hq'0 hq'1
    have H := lower_le_envelope T c l' hl' hcomp' hmajor (-cost)
    change (∫ p, -cost p ∂q') ≤ upperEnvelope T c (-cost) at H
    rw [integral_neg] at H
    rw [hcq]
    linarith
  · intro ε hε
    obtain ⟨fg,hfg,hfgc⟩ := envelope_lt T c hmajor
      (x := -cost) (r := upperEnvelope T c (-cost)+ε) (by linarith)
    refine ⟨-fg, ?_, ?_⟩
    · change T (-fg) ≤ cost
      rw [map_neg]
      simpa only [neg_neg] using neg_le_neg hfg
    · change (∫ p, cost p ∂q) < c (-fg)+ε
      rw [hcq, map_neg]
      linarith

end WeakHessianTransport

open Set Filter
open scoped Topology ENNReal NNReal


open Set

end

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

omit [CompactSpace X] in
lemma quadratic_cost_increment {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R) (x z y : X) :
    dist z y^2/2-dist x y^2/2 ≤ (R:ℝ)*dist z x := by
  have h1 := dist_triangle z x y
  have h2 := hR z y
  have h3 := hR x y
  have h4 := dist_nonneg (x := z) (y := y)
  have h5 := dist_nonneg (x := x) (y := y)
  have h6 := dist_nonneg (x := z) (y := x)
  have H : (dist z y-dist x y)*(dist z y+dist x y) ≤ dist z x*(2*(R:ℝ)) := by
    calc
      _ ≤ dist z x*(dist z y+dist x y) := by gcongr; linarith
      _ ≤ dist z x*(2*(R:ℝ)) := by gcongr; linarith
  nlinarith

lemma hopfLax_lipschitz_diameter {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R)
    {f : X → ℝ} {B : ℝ} (hf : Continuous f) (hB : ∀ x, B ≤ f x) :
    LipschitzWith R (hopfLax f 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro z x
  have H (z x : X) : hopfLax f 1 z-hopfLax f 1 x ≤ (R:ℝ)*dist z x := by
    obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hB (by norm_num : (0:ℝ)<1) x
    have hz := hopfLax_le_objective hB (by norm_num : (0:ℝ)<1) z y
    have hi := quadratic_cost_increment hR x z y
    rw [← hy]
    dsimp [hopfObjective] at *
    linarith
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by have HH := H x z; rw [dist_comm x z] at HH; linarith, H z x⟩

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

variable [MeasurableSpace X] [BorelSpace X]
lemma potential_integral_lipschitz (μ : Measure X) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (fun f : C(X,ℝ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hf : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g μ := g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [NNReal.coe_one,one_mul,dist_eq_norm,← integral_sub hf hg]
  calc
    _ ≤ ∫ x, ‖f x-g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, dist f g ∂μ := integral_mono (hf.sub hg).norm (integrable_const _) (fun x => by
      simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist x (f := f) (g := g))
    _ = dist f g := by simp

lemma bounded_dual_improvement {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R)
    (o : X) (a b : C_c(X,ℝ)) (hab : marginalSum (a,b) ≤ quadraticCost 1) :
    ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      ‖φ‖ ≤ (R:ℝ)^2 ∧ ‖ψ‖ ≤ (R:ℝ)^2 ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        (∫ x, a x ∂μ)+(∫ y, b y ∂ν) ≤ (∫ x, φ x ∂μ)+(∫ y, ψ y ∂ν) := by
  have hb : ∀ y, -‖b.toContinuousMap‖ ≤ -b y := fun y => by
    have H := b.toContinuousMap.norm_coe_le_norm y
    exact neg_le_neg (le_abs_self _ |>.trans H)
  let v := hopfLax (fun y => -b y) 1
  have hvL : LipschitzWith R v := hopfLax_lipschitz_diameter hR b.continuous.neg hb
  let φ : C(X,ℝ) := ⟨fun x => v x-v o,hvL.continuous.sub continuous_const⟩
  have hφL : LipschitzWith R φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (v x-v o) (v y-v o) ≤ (R:ℝ)*dist x y
    simpa only [dist_sub_right] using hvL.dist_le_mul x y
  have hφabs (x : X) : |φ x| ≤ (R:ℝ)^2 := by
    have H := hvL.dist_le_mul x o
    change |v x-v o| ≤ _
    rw [Real.dist_eq] at H
    exact H.trans (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hR x o) R.coe_nonneg)
  have hφnorm : ‖φ‖ ≤ (R:ℝ)^2 := (ContinuousMap.norm_le φ (sq_nonneg _)).mpr hφabs
  have hφlower : ∀ x, -(R:ℝ)^2 ≤ -φ x := fun x => neg_le_neg (le_abs_self _ |>.trans (hφabs x))
  let w := hopfLax (fun x => -φ x) 1
  have hwL : LipschitzWith R w := hopfLax_lipschitz_diameter hR φ.continuous.neg hφlower
  let ψ : C(X,ℝ) := ⟨w,hwL.continuous⟩
  have hψabs (y : X) : |ψ y| ≤ (R:ℝ)^2 := by
    apply abs_le.mpr
    constructor
    · exact lower_le_hopfLax hφlower (by norm_num : (0:ℝ)<1) y
    · have H := hopfLax_le_objective hφlower (by norm_num : (0:ℝ)<1) y o
      have HR := hR y o
      change hopfLax _ _ _ ≤ _
      have hφo : φ o = 0 := sub_self _
      dsimp only [hopfObjective] at H
      rw [hφo] at H
      nlinarith [sq_le_sq₀ dist_nonneg R.coe_nonneg |>.mpr HR,sq_nonneg (R:ℝ)]
  refine ⟨φ,ψ,hφL,hwL,hφnorm,(ContinuousMap.norm_le ψ (sq_nonneg _)).mpr hψabs,?_,?_⟩
  · intro x y
    have H := hopfLax_le_objective hφlower (by norm_num : (0:ℝ)<1) y x
    change φ x+w y ≤ _
    dsimp [w,hopfObjective] at *
    rw [dist_comm y x] at H
    linarith
  · intro μ ν _ _
    have haφ (x : X) : a x ≤ φ x+v o := by
      suffices a x ≤ v x by dsimp [φ]; linarith
      apply le_csInf ⟨hopfObjective (fun y => -b y) 1 x x,mem_range_self x⟩
      rintro r ⟨y,rfl⟩
      have H := hab (x,y)
      change a x+b y ≤ dist x y^2/(2*1) at H
      dsimp [hopfObjective]
      linarith
    have hbψ (y : X) : b y ≤ ψ y-v o := by
      suffices b y+v o ≤ w y by change b y ≤ w y-v o; linarith
      apply le_csInf ⟨hopfObjective (fun x => -φ x) 1 y y,mem_range_self y⟩
      rintro r ⟨x,rfl⟩
      have H := hopfLax_le_objective hb (by norm_num : (0:ℝ)<1) x y
      change v x ≤ -b y+dist x y^2/(2*1) at H
      dsimp [hopfObjective,φ]
      rw [dist_comm y x]
      linarith
    have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hψi : Integrable ψ ν := ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have H := integral_mono a.integrable (hφi.add (integrable_const _)) haφ
    have I := integral_mono b.integrable (hψi.sub (integrable_const _)) hbψ
    change (∫ x,a x ∂μ) ≤ ∫ x,φ x+v o ∂μ at H
    change (∫ x,b x ∂ν) ≤ ∫ x,ψ x-v o ∂ν at I
    rw [integral_add hφi (integrable_const _),integral_const] at H
    rw [integral_sub hψi (integrable_const _),integral_const] at I
    simp only [probReal_univ,one_smul] at H I
    linarith

lemma compact_kantorovich_potentials (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {R : ℝ≥0}
    (hR : ∀ x y : X, dist x y ≤ R) (o : X) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×X), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, quadraticCost 1 p ∂q) ≤ ∫ p, quadraticCost 1 p ∂q') ∧
      ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
        (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
        ∀ᵐ p ∂q, φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  obtain ⟨q,hqp,hq0,hq1,hqmin,hqdual⟩ := compact_kantorovich_duality μ ν (quadraticCost 1)
  let _ := hqp
  let K := {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ (R:ℝ)^2}
  let A := {p : C(X,ℝ)×C(X,ℝ) | ∀ x y, p.1 x+p.2 y ≤ dist x y^2/2}
  let S := (K×ˢK) ∩ A
  have hK : IsCompact K := isCompact_lipschitz_norm_ball R (sq_nonneg _)
  have hA : IsClosed A := by
    simp only [A,ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_le ((continuous_eval_const x).comp continuous_fst |>.add
      ((continuous_eval_const y).comp continuous_snd)) continuous_const
  have hS : IsCompact S := (hK.prod hK).inter_right hA
  have happrox (ε : ℝ) (hε : 0 < ε) : ∃ p ∈ S,
      (∫ z,quadraticCost 1 z ∂q) < (∫ x,p.1 x ∂μ)+(∫ y,p.2 y ∂ν)+ε := by
    obtain ⟨⟨a,b⟩,hab,hεab⟩ := hqdual ε hε
    obtain ⟨φ,ψ,hφL,hψL,hφB,hψB,hφψ,hI⟩ := bounded_dual_improvement hR o a b hab
    refine ⟨(φ,ψ),⟨⟨⟨hφL,hφB⟩,⟨hψL,hψB⟩⟩,hφψ⟩,?_⟩
    change (∫ z,quadraticCost 1 z ∂q) < (∫ x,φ x ∂μ)+(∫ y,ψ y ∂ν)+ε
    change (∫ z,quadraticCost 1 z ∂q) < (∫ x,a x ∂μ)+(∫ y,b y ∂ν)+ε at hεab
    have HH := hI μ ν
    linarith
  have hSne : S.Nonempty := by obtain ⟨p,hp,_⟩ := happrox 1 (by norm_num); exact ⟨p,hp⟩
  let I : C(X,ℝ)×C(X,ℝ) → ℝ := fun p => (∫ x,p.1 x ∂μ)+(∫ y,p.2 y ∂ν)
  have hI : Continuous I := ((potential_integral_lipschitz μ).continuous.comp continuous_fst).add
    ((potential_integral_lipschitz ν).continuous.comp continuous_snd)
  obtain ⟨p,hp,hmax⟩ := hS.exists_isMaxOn hSne hI.continuousOn
  have hge : (∫ z,quadraticCost 1 z ∂q) ≤ I p := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨r,hr,hir⟩ := happrox ε hε
    have HH := hmax hr
    change (∫ x,r.1 x ∂μ)+(∫ y,r.2 y ∂ν) ≤ I p at HH
    linarith
  let φ : C_c(X,ℝ) := ⟨p.1,HasCompactSupport.of_compactSpace _⟩
  let ψ : C_c(X,ℝ) := ⟨p.2,HasCompactSupport.of_compactSpace _⟩
  have hsum : (∫ z,marginalSum (φ,ψ) z ∂q) = I p :=
    integral_marginalSum_of_marginals μ ν hq0 hq1 (φ,ψ)
  have hle : marginalSum (φ,ψ) ≤ quadraticCost 1 := by
    intro z
    simpa only [marginalSum_apply,quadraticCost_apply,mul_one,φ,ψ,CompactlySupportedContinuousMap.coe_mk] using hp.2 z.1 z.2
  have heq : ∀ᵐ z ∂q,marginalSum (φ,ψ) z = quadraticCost 1 z := by
    apply (integral_eq_iff_of_ae_le (marginalSum (φ,ψ)).integrable (quadraticCost 1).integrable
      (ae_of_all _ hle)).mp
    apply le_antisymm (integral_mono (marginalSum (φ,ψ)).integrable (quadraticCost 1).integrable hle)
    rw [hsum]
    exact hge
  refine ⟨q,hqp,hq0,hq1,hqmin,p.1,p.2,hp.1.1.1,hp.1.2.1,hp.2,?_⟩
  simpa only [marginalSum_apply,quadraticCost_apply,mul_one,φ,ψ,CompactlySupportedContinuousMap.coe_mk] using heq

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

noncomputable section
noncomputable section
namespace WeakHessianTransport
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma lowerLipExtension_bdd {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (x : X) :
    BddAbove (range (fun z : S => f z - D * dist x z)) := by
  obtain ⟨o⟩ := ‹Nonempty S›
  refine ⟨f o+D*dist x o,?_⟩
  rintro r ⟨z,rfl⟩
  have H := hf.le_add_mul z o
  have J := mul_le_mul_of_nonneg_left (dist_triangle_left (z:X) (o:X) x) D.coe_nonneg
  change f z ≤ f o+D*dist (z:X) (o:X) at H
  nlinarith

lemma lowerLipExtension_eq {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (x : S) : lowerLipExtension S f D x = f x := by
  apply le_antisymm
  · apply ciSup_le
    intro z
    have H := hf.le_add_mul z x
    change f z ≤ f x+D*dist (z:X) (x:X) at H
    rw [dist_comm] at H
    linarith
  · have H := le_ciSup (lowerLipExtension_bdd hf (x:X)) x
    simpa only [dist_self,mul_zero,sub_zero,lowerLipExtension] using H

lemma lowerLipExtension_lipschitz {S : Set X} [Nonempty S] {f : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) : LipschitzWith D (lowerLipExtension S f D) := by
  apply LipschitzWith.of_le_add_mul D
  intro x y
  apply ciSup_le
  intro z
  have H := le_ciSup (lowerLipExtension_bdd hf y) z
  change f z-D*dist y z ≤ lowerLipExtension S f D y at H
  have J := mul_le_mul_of_nonneg_left (dist_triangle y x (z:X)) D.coe_nonneg
  rw [dist_comm y x] at J
  linarith

lemma quadratic_cost_two_point_lower {D : ℝ≥0} {z w x y : X}
    (hD : dist z w ≤ D) :
    dist z w^2/2-D*(dist x z+dist y w) ≤ dist x y^2/2 := by
  have hr : 0 ≤ dist x z+dist y w := by positivity
  have ha : dist z w ≤ dist x z+dist y w+dist x y := by
    have H := dist_triangle z x w
    have J := dist_triangle x y w
    rw [dist_comm z x] at H
    linarith
  by_cases h : dist x y ≤ dist z w
  · have H : dist z w^2-dist x y^2 ≤ (dist x z+dist y w)*(2*D) := by
      calc
        _ = (dist z w-dist x y)*(dist z w+dist x y) := by ring
        _ ≤ (dist x z+dist y w)*(dist z w+dist x y) := by gcongr; linarith
        _ ≤ (dist x z+dist y w)*(2*D) := by gcongr; linarith
    nlinarith
  · have H := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (le_of_not_ge h)
    nlinarith [mul_nonneg D.coe_nonneg hr]

lemma lowerLipExtension_dual {S : Set X} [Nonempty S] {f g : S → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (hg : LipschitzWith D g)
    (hD : ∀ z w : S, dist (z:X) (w:X) ≤ D)
    (hdual : ∀ z w : S, f z+g w ≤ dist (z:X) (w:X)^2/2) (x y : X) :
    lowerLipExtension S f D x+lowerLipExtension S g D y ≤ dist x y^2/2 := by
  rw [← le_sub_iff_add_le]
  apply (ciSup_le_iff (lowerLipExtension_bdd hf x)).mpr
  intro z
  rw [le_sub_iff_add_le,add_comm,← le_sub_iff_add_le]
  apply (ciSup_le_iff (lowerLipExtension_bdd hg y)).mpr
  intro w
  have H := quadratic_cost_two_point_lower (hD z w) (x := x) (y := y)
  have J := hdual z w
  linarith

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
open WeakHessian

lemma quadraticTransportCost_map_subtype {S : Set X} (hS : MeasurableSet S)
    (q : Measure (S×S)) :
    QuadraticTransportCost (q.map (Prod.map Subtype.val Subtype.val)) =
      QuadraticTransportCost q := by
  unfold QuadraticTransportCost
  rw [lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2)
    ((MeasurableEmbedding.subtype_coe hS).prodMap
      (MeasurableEmbedding.subtype_coe hS)).measurable]
  rfl

lemma compact_quadraticCost_eq [CompactSpace X] (q : Measure (X×X))
    [IsFiniteMeasure q] :
    QuadraticTransportCost q = ENNReal.ofReal (2*(∫ p,quadraticCost 1 p ∂q)) := by
  have hi : Integrable (fun p : X×X => dist p.1 p.2^2) q :=
    ((continuous_fst.dist continuous_snd).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : (∫ p : X×X, dist p.1 p.2^2 ∂q) = 2*(∫ p,quadraticCost 1 p ∂q) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by simp only [quadraticCost_apply]; ring)
  rw [← heq,ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p => sq_nonneg _))]
  apply lintegral_congr
  intro p
  rw [edist_dist,ENNReal.ofReal_pow dist_nonneg]

lemma compact_kantorovich_potentials_of_optimal [CompactSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : Measure (X×X)} (hq : IsOptimalCoupling q μ ν)
    {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R) (o : X) :
    ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ p ∂q, φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  have hqp : IsProbabilityMeasure q := by
    constructor
    have H := congrArg (fun μ => μ Set.univ) hq.1.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using H
  let := hqp
  obtain ⟨q',hqp',hq0',hq1',hqmin',φ,ψ,hφ,hψ,hdual,hcontact⟩ :=
    compact_kantorovich_potentials μ ν hR o
  let := hqp'
  have H := hq.2 q' ⟨hq0',hq1'⟩
  rw [compact_quadraticCost_eq,compact_quadraticCost_eq] at H
  have hcost : (∫ p,quadraticCost 1 p ∂q) ≤ ∫ p,quadraticCost 1 p ∂q' := by
    have hn : 0 ≤ 2*(∫ p,quadraticCost 1 p ∂q') := by
      apply mul_nonneg (by norm_num)
      apply integral_nonneg
      intro p
      simp only [quadraticCost_apply]
      positivity
    have he := (ENNReal.ofReal_le_ofReal_iff hn).mp H
    linarith
  have hm (r : Measure (X×X)) [IsProbabilityMeasure r]
      (hr0 : r.map Prod.fst = μ) (hr1 : r.map Prod.snd = ν) :
      (∫ p,φ p.1+ψ p.2 ∂r) = (∫ x,φ x ∂μ)+(∫ y,ψ y ∂ν) := by
    rw [integral_add,← integral_map measurable_fst.aemeasurable φ.continuous.aestronglyMeasurable,
      ← integral_map measurable_snd.aemeasurable ψ.continuous.aestronglyMeasurable,hr0,hr1]
    · exact (φ.continuous.comp continuous_fst).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact (ψ.continuous.comp continuous_snd).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun p : X×X => φ p.1+ψ p.2) q :=
    ((φ.continuous.comp continuous_fst).add (ψ.continuous.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨φ,ψ,hφ,hψ,hdual,?_⟩
  have heq : (∫ p,φ p.1+ψ p.2 ∂q) = (∫ p,quadraticCost 1 p ∂q) := by
    apply le_antisymm
    · apply integral_mono hi (quadraticCost 1).integrable
      intro p
      simpa only [quadraticCost_apply,mul_one] using hdual p.1 p.2
    · calc
        _ ≤ ∫ p,quadraticCost 1 p ∂q' := hcost
        _ = ∫ p,φ p.1+ψ p.2 ∂q' := by
          apply integral_congr_ae
          filter_upwards [hcontact] with p hp
          simpa only [quadraticCost_apply,mul_one] using hp.symm
        _ = _ := by rw [hm q' hq0' hq1',hm q hq.1.1 hq.1.2]
  have H := (integral_eq_iff_of_ae_le hi (quadraticCost 1).integrable
    (ae_of_all _ (fun p => by simpa only [quadraticCost_apply,mul_one] using hdual p.1 p.2))).mp heq
  filter_upwards [H] with p hp
  simpa only [quadraticCost_apply,mul_one] using hp

lemma bounded_support_kantorovich_potentials
    {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ y ∂ν, y ∈ S)
    {q : Measure (X×X)} (hq : IsOptimalCoupling q μ ν)
    {R : ℝ≥0} (hR : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R) :
    ∃ φ ψ : X → ℝ, LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ p ∂q,φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : Nonempty S := hne.to_subtype
  have he := MeasurableEmbedding.subtype_coe hS.measurableSet
  have hep := he.prodMap he
  let μs : Measure S := μ.comap Subtype.val
  let νs : Measure S := ν.comap Subtype.val
  have hμr : ∀ᵐ x ∂μ,x ∈ range (Subtype.val : S → X) := by simpa using hμ
  have hνr : ∀ᵐ x ∂ν,x ∈ range (Subtype.val : S → X) := by simpa using hν
  let : IsProbabilityMeasure μs := he.isProbabilityMeasure_comap hμr
  let : IsProbabilityMeasure νs := he.isProbabilityMeasure_comap hνr
  have hμs : μs.map Subtype.val = μ := by
    rw [he.map_comap,Measure.restrict_eq_self_of_ae_mem hμr]
  have hνs : νs.map Subtype.val = ν := by
    rw [he.map_comap,Measure.restrict_eq_self_of_ae_mem hνr]
  have hqr : ∀ᵐ p ∂q,p ∈ range (Prod.map (Subtype.val : S → X) (Subtype.val : S → X)) := by
    have H : ∀ᵐ p ∂q,p.1 ∈ S := by
      apply (ae_map_iff measurable_fst.aemeasurable hS.measurableSet).mp
      rwa [hq.1.1]
    have J : ∀ᵐ p ∂q,p.2 ∈ S := by
      apply (ae_map_iff measurable_snd.aemeasurable hS.measurableSet).mp
      rwa [hq.1.2]
    filter_upwards [H,J] with p hp0 hp1
    exact ⟨(⟨p.1,hp0⟩,⟨p.2,hp1⟩),rfl⟩
  let qs : Measure (S×S) := q.comap (Prod.map Subtype.val Subtype.val)
  have hqs : qs.map (Prod.map Subtype.val Subtype.val) = q := by
    rw [hep.map_comap,Measure.restrict_eq_self_of_ae_mem hqr]
  have hqs0 : qs.map Prod.fst = μs := by
    apply he.map_injective
    rw [Measure.map_map he.measurable measurable_fst,hμs,← hq.1.1,← hqs,
      Measure.map_map measurable_fst hep.measurable]
    rfl
  have hqs1 : qs.map Prod.snd = νs := by
    apply he.map_injective
    rw [Measure.map_map he.measurable measurable_snd,hνs,← hq.1.2,← hqs,
      Measure.map_map measurable_snd hep.measurable]
    rfl
  have hqsopt : IsOptimalCoupling qs μs νs := by
    refine ⟨⟨hqs0,hqs1⟩,?_⟩
    intro r hr
    have hr' : IsCoupling (r.map (Prod.map Subtype.val Subtype.val)) μ ν := by
      constructor
      · rw [Measure.map_map measurable_fst hep.measurable,← hμs,← hr.1,
          Measure.map_map he.measurable measurable_fst]
        rfl
      · rw [Measure.map_map measurable_snd hep.measurable,← hνs,← hr.2,
          Measure.map_map he.measurable measurable_snd]
        rfl
    have H := hq.2 _ hr'
    rw [← hqs,quadraticTransportCost_map_subtype hS.measurableSet,
      quadraticTransportCost_map_subtype hS.measurableSet] at H
    exact H
  obtain ⟨f,g,hf,hg,hdual,hcontact⟩ := compact_kantorovich_potentials_of_optimal μs νs hqsopt
    (fun x y => hR x x.property y y.property) (Classical.arbitrary S)
  let φ := lowerLipExtension S f R
  let ψ := lowerLipExtension S g R
  refine ⟨φ,ψ,lowerLipExtension_lipschitz hf,lowerLipExtension_lipschitz hg,
    lowerLipExtension_dual hf hg (fun x y => hR x x.property y y.property) hdual,?_⟩
  rw [← hqs]
  apply (ae_map_iff hep.measurable.aemeasurable ?_).mpr
  · filter_upwards [hcontact] with p hp
    simpa only [Prod.map_fst,Prod.map_snd,φ,ψ,lowerLipExtension_eq hf,
      lowerLipExtension_eq hg,Subtype.dist_eq] using hp
  · exact (isClosed_eq
      (((lowerLipExtension_lipschitz hf).continuous.comp continuous_fst).add
        ((lowerLipExtension_lipschitz hg).continuous.comp continuous_snd))
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet

end WeakHessianTransport

end
end
end
end InlinedFile1

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
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_LipschitzDerivQuadraticRemainder
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
open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

lemma lipschitzOn_deriv_quadratic_remainder {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
    (hψ : LipschitzOnWith L ψ s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    |φ b - φ a - ψ a*(b-a)| ≤ (L:ℝ)*|b-a|^2 := by
  have hseg := hs.segment_subset ha hb
  have H := (convex_segment a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => φ x - φ a - ψ a*(x-a))
    (f' := fun x => ψ x-ψ a) (C := (L:ℝ)*|b-a|)
    (fun x hx => by
      convert ((hφ x (hseg hx)).sub_const (φ a)).sub
        (((hasDerivAt_id x).sub_const a).const_mul (ψ a)) |>.hasDerivWithinAt using 1 <;>
        first | rfl | simp)
    (fun x hx => by
      calc
        ‖ψ x - ψ a‖ ≤ (L:ℝ)*‖x-a‖ := hψ.norm_sub_le (hseg hx) ha
        _ ≤ (L:ℝ)*|b-a| := mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hx) L.coe_nonneg)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using H

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma hasFDerivWithinAt_integral_lipschitzOn {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
    (hψ : LipschitzOnWith L ψ s) {S : Set (Lp ℝ 2 m)}
    (hS : ∀ v ∈ S, ∀ᵐ x ∂m, v x ∈ s)
    (hi : ∀ v ∈ S, Integrable (fun x => φ (v x)) m)
    {u : Lp ℝ 2 m} (hu : u ∈ S) (hwu : MemLp (fun x => ψ (u x)) 2 m) :
    HasFDerivWithinAt (fun v : Lp ℝ 2 m => ∫ x, φ (v x) ∂m)
      (innerSL ℝ (hwu.toLp (fun x => ψ (u x)))) S u := by
  let w : Lp ℝ 2 m := hwu.toLp (fun x => ψ (u x))
  have hw : (w : X → ℝ) =ᵐ[m] fun x => ψ (u x) := MemLp.coeFn_toLp _
  have herr (v : Lp ℝ 2 m) (hv : v ∈ S) :
      |(∫ x, φ (v x) ∂m) - (∫ x, φ (u x) ∂m) - ⟪w,v-u⟫_ℝ| ≤ (L:ℝ)*‖v-u‖^2 := by
    have hvv : Integrable (fun x => (v-u) x*(v-u) x) m :=
      (Lp.memLp (v-u)).integrable_mul (Lp.memLp (v-u))
    have hn : (∫ x, (v-u) x*(v-u) x ∂m) = ‖v-u‖^2 := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial] using real_inner_self_eq_norm_sq (v-u)
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_sub (hi v hv) (hi u hu)]
    have hii : Integrable (fun x => φ (v x) - φ (u x)) m := (hi v hv).sub (hi u hu)
    rw [← integral_sub hii (show Integrable (fun x => (v-u) x*w x) m from
      (Lp.memLp (v-u)).integrable_mul (Lp.memLp w))]
    calc
      |∫ x, φ (v x) - φ (u x) - (v-u) x * w x ∂m| ≤
          ∫ x, (L:ℝ)*((v-u) x*(v-u) x) ∂m := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le (hvv.const_mul (L:ℝ))
        filter_upwards [hw,Lp.coeFn_sub v u,hS v hv,hS u hu] with x hx ha hvs hus
        rw [hx,ha]
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        have H := lipschitzOn_deriv_quadratic_remainder hs hφ hψ hus hvs
        rw [sq_abs] at H
        simpa only [pow_two,mul_comm] using H
      _ = (L:ℝ)*‖v-u‖^2 := by rw [integral_const_mul,hn]
  have h0 : Tendsto (fun v : Lp ℝ 2 m => v-u) (𝓝[S] u) (𝓝 0) := by
    simpa only [sub_self,id_eq] using ((tendsto_id : Tendsto (fun v : Lp ℝ 2 m => v) (𝓝 u) (𝓝 u)).mono_left nhdsWithin_le_nhds).sub_const u
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply (IsBigO.of_bound (L:ℝ) ?_).trans_isLittleO
    ((isLittleO_norm_pow_id (show 1 < (2:ℕ) by norm_num)).comp_tendsto h0)
  filter_upwards [eventually_mem_nhdsWithin] with v hv
  change ‖(∫ x, φ (v x) ∂m) - (∫ x, φ (u x) ∂m) - ⟪w,v-u⟫_ℝ‖ ≤ (L:ℝ)*‖‖v-u‖^2‖
  simpa only [Real.norm_eq_abs, norm_pow, norm_norm, abs_of_nonneg (norm_nonneg _)] using herr v hv

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma hasFDerivAt_integral_quadratic {φ ψ : ℝ → ℝ} {L : ℝ≥0}
    (hφ : ∀ x, HasDerivAt φ (ψ x) x) (hψ : LipschitzWith L ψ)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, φ (v x) ∂m)
      (innerSL ℝ ((hψ.comp_memLp hψ0 (Lp.memLp u)).toLp (ψ ∘ u))) u := by
  have hi (v : Lp ℝ 2 m) : Integrable (fun x => φ (v x)) m := by
    apply ((Lp.memLp v).integrable_sq.const_mul (L:ℝ)).mono'
      ((show Continuous φ from continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
    apply Eventually.of_forall
    intro x
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun x _ => hφ x) hψ.lipschitzOnWith (a := 0) (b := v x) (mem_univ _) (mem_univ _)
    simpa only [hφ0,hψ0,sub_zero,zero_mul,Real.norm_eq_abs,sq_abs] using H
  apply hasFDerivWithinAt_univ.mp
  exact hasFDerivWithinAt_integral_lipschitzOn convex_univ (fun x _ => hφ x) hψ.lipschitzOnWith
    (fun v _ => Eventually.of_forall fun x => mem_univ (v x)) (fun v _ => hi v)
    (mem_univ u) (hψ.comp_memLp hψ0 (Lp.memLp u))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_TruncatedLog
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
open scoped Topology NNReal

lemma truncatedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (truncatedLog a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (truncatedLog_hasDeriv ha x).differentiableAt,?_⟩
  rw [show deriv (truncatedLog a) = (fun x => (max a x)⁻¹) from funext (truncatedLog_deriv ha)]
  exact (continuous_const.max continuous_id).inv₀ (fun s => ne_of_gt (ha.trans_le (le_max_left _ _)))

lemma truncatedLog_eq {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    truncatedLog a x = Real.log x := by
  have H : (∫ s in a..x, (max a s)⁻¹) = Real.log x-Real.log a := by
    calc
      (∫ s in a..x, (max a s)⁻¹) = ∫ s in a..x, s⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hax] at hs
        exact congrArg Inv.inv (max_eq_right hs.1)
      _ = Real.log x-Real.log a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro s hs
          rw [uIcc_of_le hax] at hs
          exact Real.hasDerivAt_log (ne_of_gt (ha.trans_le hs.1))
        · exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt (ha.trans_le hs.1))).intervalIntegrable_of_Icc hax
  dsimp only [truncatedLog]
  rw [H]
  ring

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

lemma regularizedEntropy_zero (a : ℝ) : regularizedEntropy a 0 = 0 := by
  simp [regularizedEntropy]
lemma regularizedLog_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (regularizedLog a) :=
  ((truncatedLog_contDiff ha).comp (contDiff_id.add contDiff_const)).sub contDiff_const
lemma regularizedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedLog a) ((max a (x+a))⁻¹) x := by
  simpa only [regularizedLog,Function.comp_def,mul_one] using!
    ((truncatedLog_hasDeriv ha (x+a)).comp x ((hasDerivAt_id x).add_const a)).sub_const (Real.log a)
lemma regularizedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (regularizedLog a) x = (max a (x+a))⁻¹ := (regularizedLog_hasDeriv ha x).deriv
lemma regularizedLog_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedLog a x = Real.log (x+a)-Real.log a := by
  rw [regularizedLog,truncatedLog_eq ha (by linarith)]
lemma regularizedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (regularizedLog a) x| ≤ a⁻¹ := by
  rw [regularizedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a (x+a))))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma regularizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (regularizedEntropy a) (regularizedLog a x) x := by
  have hc := (regularizedLog_contDiff ha).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma regularizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-(Real.log a+1)*x := by
  let F : ℝ → ℝ := fun y => (y+a)*Real.log (y+a)-(Real.log a+1)*y
  have hF (y : ℝ) (hy : y ∈ uIcc 0 x) : HasDerivAt F (regularizedLog a y) y := by
    rw [uIcc_of_le hx] at hy
    have hypos : 0 < y+a := by linarith [hy.1]
    have H := ((Real.hasDerivAt_mul_log hypos.ne').comp y ((hasDerivAt_id y).add_const a)).sub
      ((hasDerivAt_id y).const_mul (Real.log a+1))
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    rw [regularizedLog_eq ha hy.1]
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((regularizedLog_contDiff ha).continuous.intervalIntegrable 0 x)
  change regularizedEntropy a x = F x-F 0 at H
  rw [H]
  dsimp [F]
  ring_nf

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma regularizedEntropy_hasFDeriv {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    HasFDerivAt (fun v : Lp ℝ 2 m => ∫ x, regularizedEntropy a (v x) ∂m)
      (innerSL ℝ ((regularizedLog_memLp ha u).toLp (fun x => regularizedLog a (u x)))) u :=
  hasFDerivAt_integral_quadratic (regularizedEntropy_hasDeriv ha) (regularizedLog_lipschitz ha)
    (regularizedEntropy_zero a) (regularizedLog_zero a) u

end WeakHessian

end
end InlinedFile0

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

end WeakHessian

end
end InlinedFile26

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

end WeakHessian

end
end InlinedFile18

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
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CompContDiffLipschitz
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
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.comp_contDiff_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hLip : LipschitzWith L φ) (hzero : φ 0 = 0) :
    Sobolev m (φ ∘ f) := by
  have hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ (L:ℝ) :=
    ae_of_all _ (fun x => norm_deriv_le_of_lipschitz hLip)
  have hmeas : AEStronglyMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf.1.aemeasurable).abs.aestronglyMeasurable
  apply Sobolev.of_upperGradient hfinite (hLip.comp_memLp hzero hf.1)
    ((weakGradient_isMinimal hf.2.1.2).1.comp_contDiff hf.1.aemeasurable hφ hB)
  simpa only [mul_comm] using memLp_mul_bounded hf.2.2 hmeas (by simpa only [abs_abs] using hB)

lemma IsLaplacian.regularizedLog_identity (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {a : ℝ} (ha : 0 < a) :
    (∫ x, A x * regularizedLog a (u x) ∂m) =
      -(∫ x, (weakGradient m u x)^2 / (u x+a) ∂m) := by
  have hv := hu.1.comp_contDiff_lipschitz hfinite (regularizedLog_contDiff ha)
    (regularizedLog_lipschitz ha) (regularizedLog_zero a)
  have hgamma := gamma_comp_contDiff hfinite hpar hu.1.2.1 hu.1.2.1
    (regularizedLog_contDiff ha) hv.2.1.1 (ae_of_all _ (fun x => regularizedLog_deriv_bound ha (u x)))
  have heq : (∫ x, gamma m u (regularizedLog a ∘ u) x ∂m) =
      (∫ x, (weakGradient m u x)^2/(u x+a) ∂m) := by
    apply integral_congr_ae
    filter_upwards [gamma_comm (m := m) u (regularizedLog a ∘ u), hgamma,
      gamma_self (m := m) u,hun] with x hc hg hs hx
    rw [hc,hg,hs,regularizedLog_deriv ha,max_eq_right (by linarith : a ≤ u x+a)]
    exact inv_mul_eq_div _ _
  have H := hu.2.2 (regularizedLog a ∘ u) hv
  rw [heq] at H
  simp only [Function.comp_apply] at H
  linarith

variable [ProperSpace X]

lemma CurvatureDimension.cheegerHeat_regularizedEntropy_deriv {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => ∫ x, regularizedEntropy a (cheegerHeat h s u x) ∂m)
      (-(∫ x, (weakGradient m (cheegerHeat h t u) x)^2 / (cheegerHeat h t u x+a) ∂m))
      (Ici t) t := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, hfinite _ Metric.isBounded_ball⟩⟩
  have htime := (cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu ht
  change HasDerivWithinAt (fun s : ℝ => cheegerHeat h s u) (cheegerHeat h t A) (Ici t) t at htime
  have HE := (regularizedEntropy_hasFDeriv ha (cheegerHeat h t u)).comp_hasDerivWithinAt t htime
  have hL := hcd.global_isLaplacian_of_formGenerator hfinite o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hid := hL.regularizedLog_identity hfinite (hcd.global_localGradientParallelogram hfinite o h)
    (cheegerHeat_nonneg h ht u hun) ha
  have hip : (innerSL ℝ ((regularizedLog_memLp ha (cheegerHeat h t u)).toLp
      (fun x => regularizedLog a (cheegerHeat h t u x)))) (cheegerHeat h t A) =
      -(∫ x, (weakGradient m (cheegerHeat h t u) x)^2 / (cheegerHeat h t u x+a) ∂m) := by
    change ⟪((regularizedLog_memLp ha (cheegerHeat h t u)).toLp
      (fun x => regularizedLog a (cheegerHeat h t u x))), (cheegerHeat h t A)⟫_ℝ = _
    rw [L2.inner_def]
    convert hid using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [(regularizedLog_memLp ha (cheegerHeat h t u)).coeFn_toLp] with x hx
    simpa only [RCLike.inner_apply, conj_trivial] using congrArg (fun z : ℝ => cheegerHeat h t A x*z) hx
  simpa only [Function.comp_def,hip] using! HE

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RegularizedEntropyIntegrable
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
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma regularizedEntropy_integrable {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    Integrable (fun x => regularizedEntropy a (u x)) m := by
  apply ((Lp.memLp u).integrable_sq.const_mul a⁻¹).mono'
    ((show Continuous (regularizedEntropy a) from continuous_iff_continuousAt.mpr
      (fun y => (regularizedEntropy_hasDeriv ha y).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun y _ => regularizedEntropy_hasDeriv ha y) (regularizedLog_lipschitz ha).lipschitzOnWith
      (a := 0) (b := u x) (mem_univ _) (mem_univ _)
    simpa only [regularizedEntropy_zero,regularizedLog_zero,zero_mul,sub_zero,Real.norm_eq_abs,sq_abs,NNReal.coe_mk] using! H

lemma CurvatureDimension.cheegerHeat_regularizedFisher_continuousOn {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => ∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) (Ici 0) := by
  let logLp : Lp ℝ 2 m → Lp ℝ 2 m := (regularizedLog_lipschitz ha).compLp (regularizedLog_zero a)
  have hc : ContinuousOn (fun t => -⟪logLp (cheegerHeat h t u),cheegerHeat h t A⟫_ℝ) (Ici 0) :=
    (((regularizedLog_lipschitz ha).continuous_compLp (regularizedLog_zero a)).comp_continuousOn
      (cheegerHeat_continuousOn hfin h u)).inner (cheegerHeat_continuousOn hfin h A) |>.neg
  apply hc.congr
  intro t ht
  have hL := hcd.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hid := hL.regularizedLog_identity hfin (hcd.global_localGradientParallelogram hfin o h)
    (cheegerHeat_nonneg h ht u hun) ha
  dsimp only
  rw [L2.inner_def]
  have heq : (∫ x,inner (𝕜 := ℝ) (logLp (cheegerHeat h t u) x) (cheegerHeat h t A x) ∂m) =
      ∫ x,cheegerHeat h t A x*regularizedLog a (cheegerHeat h t u x) ∂m := by
    apply integral_congr_ae
    filter_upwards [(regularizedLog_lipschitz ha).coeFn_compLp (regularizedLog_zero a) (cheegerHeat h t u)] with x hx
    simp only [logLp,Function.comp_apply] at hx ⊢
    rw [hx]
    simp only [RCLike.inner_apply,conj_trivial]
  rw [heq,hid,neg_neg]

lemma CurvatureDimension.cheegerHeat_regularizedEntropy_FTC {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) =
      (∫ x,regularizedEntropy a (u x) ∂m)-(∫ x,regularizedEntropy a (cheegerHeat h b u x) ∂m) := by
  have hc : Continuous (fun v : Lp ℝ 2 m => ∫ x,regularizedEntropy a (v x) ∂m) :=
    continuous_iff_continuousAt.mpr fun v => (regularizedEntropy_hasFDeriv ha v).continuousAt
  have ht := hc.comp_continuousOn (cheegerHeat_continuousOn hfin h u)
  have hI := (hcd.cheegerHeat_regularizedFisher_continuousOn hfin o h hu hun ha).mono
    (Icc_subset_Ici_self : Icc (0:ℝ) b ⊆ Ici 0)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb (ht.mono Icc_subset_Ici_self)
    (fun t ht => (hcd.cheegerHeat_regularizedEntropy_deriv hfin o h hu hun ha ht.1.le).mono Ioi_subset_Ici_self)
    (hI.intervalIntegrable_of_Icc hb).neg
  rw [intervalIntegral.integral_neg] at H
  simpa only [Function.comp_apply,cheegerHeat_zero,one_apply_eq_self,neg_sub] using (neg_eq_iff_eq_neg.mp H)
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RenormalizedEntropy
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
open scoped Topology

lemma renormalizedEntropy_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    renormalizedEntropy a x = (x+a)*Real.log (x+a)-a*Real.log a-x := by
  rw [renormalizedEntropy,regularizedEntropy_eq ha hx]
  ring

lemma renormalizedEntropy_lower {a x w : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hw : 0 < w) :
    x*Real.log w-w ≤ renormalizedEntropy a x := by
  by_cases hz : x = 0
  · simp only [hz,renormalizedEntropy,regularizedEntropy_zero,mul_zero,zero_add,zero_mul,zero_sub]
    linarith
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have H := Real.log_le_sub_one_of_pos (div_pos hw hxp)
  rw [Real.log_div hw.ne' hxp.ne'] at H
  have HH := mul_le_mul_of_nonneg_left H hx
  have hdiv : x*(w/x-1)=w-x := by field_simp
  rw [hdiv] at HH
  have hxlog := mul_le_mul_of_nonneg_left (Real.log_le_log hxp (le_add_of_nonneg_right ha.le)) hx
  have halog := mul_le_mul_of_nonneg_left (Real.log_le_log ha (le_add_of_nonneg_left hx)) ha.le
  rw [renormalizedEntropy_eq ha hx]
  nlinarith

lemma renormalizedEntropy_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (renormalizedEntropy a) (regularizedLog a x+Real.log a) x := by
  simpa only [renormalizedEntropy,Pi.add_apply,id_eq,mul_one] using! (regularizedEntropy_hasDeriv ha x).add
    ((hasDerivAt_id x).const_mul (Real.log a))

lemma renormalizedEntropy_upper {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    renormalizedEntropy a x ≤ x^2/2 := by
  let F (y : ℝ) := renormalizedEntropy a y-y^2/2
  have hd (y : ℝ) : HasDerivAt F (regularizedLog a y+Real.log a-y) y := by
    convert! (renormalizedEntropy_hasDeriv ha y).sub (((hasDerivAt_id y).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (simp only [id_eq]; ring)
  have H : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Ici 0)
      rw [regularizedLog_eq ha hy0]
      have HH := Real.log_le_sub_one_of_pos (by linarith : 0 < y+a)
      linarith
  have HH := H (show (0:ℝ) ∈ Ici 0 from (by simp)) hx hx
  have hF0 : F 0 = 0 := by simp [F,renormalizedEntropy,regularizedEntropy_zero]
  rw [hF0] at HH
  dsimp [F] at HH
  linarith
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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma renormalizedEntropy_integrable {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) (hi : Integrable u m) :
    Integrable (fun x => renormalizedEntropy a (u x)) m :=
  (regularizedEntropy_integrable ha u).add (hi.const_mul (Real.log a))

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_renormalizedEntropy {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) (hi : Integrable u m) :
    (∫ x,renormalizedEntropy a (u x) ∂m) =
      (∫ x,regularizedEntropy a (u x) ∂m)+Real.log a*(∫ x,u x ∂m) := by
  exact (integral_add (regularizedEntropy_integrable ha u) (hi.const_mul (Real.log a))).trans
    (congrArg (fun z => (∫ x,regularizedEntropy a (u x) ∂m)+z) (integral_const_mul _ _))

lemma CurvatureDimension.cheegerHeat_renormalizedEntropy_FTC {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) =
      (∫ x,renormalizedEntropy a (u x) ∂m)-(∫ x,renormalizedEntropy a (cheegerHeat h b u x) ∂m) := by
  have hmass := hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi hb
  rw [integral_renormalizedEntropy ha u hi,integral_renormalizedEntropy ha _ hmass.1,hmass.2]
  simpa only [add_sub_add_right_eq_sub] using hcd.cheegerHeat_regularizedEntropy_FTC hfin o h hu hun ha hb

lemma CurvatureDimension.cheegerHeat_regularizedFisher_action_bound {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) ≤
      ‖u‖^2/2+
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*b)*
        ‖hD.toLp (fun x => V x*Real.exp (-V x))‖+(∫ x,Real.exp (-V x) ∂m) := by
  have ht := (hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi hb).1
  have hUt := (hcd.cheegerHeat_weighted hfin o h u hV hU hb).1
  have hpair := weighted_pairing hUt hD
  have hE0 : (∫ x,renormalizedEntropy a (u x) ∂m) ≤ ‖u‖^2/2 := by
    have H := integral_mono_ae (renormalizedEntropy_integrable ha u hi)
      ((Lp.memLp u).integrable_sq.div_const 2) (hun.mono fun x hx => renormalizedEntropy_upper ha ha1 hx)
    rw [integral_div] at H
    have he : (∫ x,u x^2 ∂m) = ‖u‖^2 := by
      simpa only [L2.inner_def,RCLike.inner_apply,conj_trivial,pow_two] using real_inner_self_eq_norm_sq u
    rwa [he] at H
  have hEt : -(∫ x,cheegerHeat h b u x*V x ∂m)-(∫ x,Real.exp (-V x) ∂m) ≤
      (∫ x,renormalizedEntropy a (cheegerHeat h b u x) ∂m) := by
    have H := integral_mono_ae (hpair.1.neg.sub hw) (renormalizedEntropy_integrable ha _ ht) (by
      filter_upwards [cheegerHeat_nonneg h hb u hun] with x hx
      have H := renormalizedEntropy_lower ha hx (Real.exp_pos (-V x))
      simpa only [Real.log_exp,mul_neg,Pi.sub_apply,Pi.neg_apply] using! H)
    change (∫ x,-(cheegerHeat h b u x*V x)-Real.exp (-V x) ∂m) ≤ _ at H
    have he : (∫ x,-(cheegerHeat h b u x*V x)-Real.exp (-V x) ∂m) =
        -(∫ x,cheegerHeat h b u x*V x ∂m)-(∫ x,Real.exp (-V x) ∂m) := by
      calc
        _ = (∫ x,-(cheegerHeat h b u x*V x) ∂m)-(∫ x,Real.exp (-V x) ∂m) :=
          integral_sub (by simpa only [Pi.neg_apply] using! hpair.1.neg) hw
        _ = _ := by rw [integral_neg]
    rw [he] at H
    exact H
  have hm := (le_abs_self (∫ x,cheegerHeat h b u x*V x ∂m)).trans hpair.2
  have hB := hcd.cheegerHeat_weighted_norm hfin o h u hV hU hb
  have hm' := hm.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [hcd.cheegerHeat_renormalizedEntropy_FTC hN hfull hfin o h hu hun hi ha hb]
  linarith
end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

lemma fisherEpsilon_pos (n : ℕ) : 0 < fisherEpsilon n := by unfold fisherEpsilon; positivity
lemma fisherEpsilon_le_one (n : ℕ) : fisherEpsilon n ≤ 1 := by
  unfold fisherEpsilon
  exact (div_le_one (by positivity)).mpr (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
lemma fisherEpsilon_antitone : Antitone fisherEpsilon := by
  intro n k hnk
  unfold fisherEpsilon
  gcongr
lemma fisherEpsilon_tendsto : Tendsto fisherEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma regularizedFisher_mono {v g : ℝ} (hv : 0 ≤ v) :
    Monotone (fun n => g^2/(v+fisherEpsilon n)) := by
  intro n k hnk
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [fisherEpsilon_pos k])
  have H := fisherEpsilon_antitone hnk
  linarith

lemma regularizedFisher_tendsto {v g : ℝ} (hv : 0 ≤ v) (hz : v = 0 → g = 0) :
    Tendsto (fun n => g^2/(v+fisherEpsilon n)) atTop (𝓝 (g^2/v)) := by
  rcases hv.eq_or_lt with hv | hv
  · simp only [hv.symm,hz hv.symm,zero_pow (by decide : 2 ≠ 0),zero_div]
    exact tendsto_const_nhds
  · simpa only [add_zero,Pi.div_apply] using! tendsto_const_nhds.div
      (tendsto_const_nhds.add fisherEpsilon_tendsto) (by simpa using hv.ne')

lemma ofReal_fisher_eq_iSup {v g : ℝ} (hv : 0 ≤ v) (hz : v = 0 → g = 0) :
    ENNReal.ofReal (g^2/v) = ⨆ n,ENNReal.ofReal (g^2/(v+fisherEpsilon n)) :=
  tendsto_nhds_unique (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (regularizedFisher_tendsto hv hz))
    (tendsto_atTop_iSup (fun _ _ hij => ENNReal.ofReal_le_ofReal (regularizedFisher_mono hv hij)))

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
lemma integrable_regularizedFisher {u g : X → ℝ} (hu : AEStronglyMeasurable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hg : MemLp g 2 m) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x => g x^2/(u x+a)) m := by
  apply (hg.integrable_sq.div_const a).mono' ((hg.aestronglyMeasurable.pow 2).div₀ (hu.add_const a))
  filter_upwards [hun] with x hx
  simp only [Pi.div_apply,Pi.pow_apply]
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
  exact div_le_div_of_nonneg_left (sq_nonneg _) ha (by linarith)

lemma lintegral_fisher_eq_iSup {u g : X → ℝ} (hu : AEStronglyMeasurable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hg : MemLp g 2 m)
    (hz : ∀ᵐ x ∂m,u x = 0 → g x = 0) :
    (∫⁻ x,ENNReal.ofReal (g x^2/u x) ∂m) =
      ⨆ n,ENNReal.ofReal (∫ x,g x^2/(u x+fisherEpsilon n) ∂m) := by
  have he : (fun x => ENNReal.ofReal (g x^2/u x)) =ᵐ[m]
      fun x => ⨆ n,ENNReal.ofReal (g x^2/(u x+fisherEpsilon n)) := by
    filter_upwards [hun,hz] with x hx hz
    exact ofReal_fisher_eq_iSup hx hz
  rw [lintegral_congr_ae he,lintegral_iSup']
  · congr 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_regularizedFisher hu hun hg (fisherEpsilon_pos n))
      (hun.mono fun x hx => div_nonneg (sq_nonneg _) (by linarith [fisherEpsilon_pos n]))).symm
  · exact fun n => ((hg.aestronglyMeasurable.pow 2).div₀ (hu.add_const (fisherEpsilon n))).aemeasurable.ennreal_ofReal
  · filter_upwards [hun] with x hx
    exact fun _ _ hij => ENNReal.ofReal_le_ofReal (regularizedFisher_mono hx hij)

lemma fisher_action_of_regularization {T : Type*} [MeasurableSpace T] {ν : Measure T}
    {u g : T → X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ᵐ t ∂ν,AEStronglyMeasurable (u t) m)
    (hun : ∀ᵐ t ∂ν,∀ᵐ x ∂m,0 ≤ u t x)
    (hg : ∀ᵐ t ∂ν,MemLp (g t) 2 m)
    (hz : ∀ᵐ t ∂ν,∀ᵐ x ∂m,u t x = 0 → g t x = 0)
    (hR : ∀ n,Integrable (fun t => ∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m) ν)
    (hB : ∀ n,(∫ t,∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m ∂ν) ≤ C) :
    (∀ᵐ t ∂ν,Integrable (fun x => g t x^2/u t x) m) ∧
      Integrable (fun t => ∫ x,g t x^2/u t x ∂m) ν ∧
      (∫ t,∫ x,g t x^2/u t x ∂m ∂ν) ≤ C := by
  let R : ℕ → T → ℝ := fun n t => ∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m
  let I : T → ℝ≥0∞ := fun t => ∫⁻ x,ENNReal.ofReal (g t x^2/u t x) ∂m
  have he : I =ᵐ[ν] fun t => ⨆ n,ENNReal.ofReal (R n t) := by
    filter_upwards [hu,hun,hg,hz] with t hu hn hg hz
    exact lintegral_fisher_eq_iSup hu hn hg hz
  have hmono : ∀ᵐ t ∂ν,Monotone (fun n => ENNReal.ofReal (R n t)) := by
    filter_upwards [hu,hun,hg] with t hu hn hg
    intro n k hnk
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono_ae (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos n))
      (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos k))
      (hn.mono fun x hx => regularizedFisher_mono hx hnk)
  have hIm : AEMeasurable I ν :=
    (AEMeasurable.iSup (fun n => (hR n).1.aemeasurable.ennreal_ofReal)).congr he.symm
  have hIb : (∫⁻ t,I t ∂ν) ≤ ENNReal.ofReal C := by
    rw [lintegral_congr_ae he,lintegral_iSup' (fun n => (hR n).1.aemeasurable.ennreal_ofReal) hmono]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hR n)]
    · exact ENNReal.ofReal_le_ofReal (hB n)
    · filter_upwards [hun] with t hn
      exact integral_nonneg_of_ae (hn.mono fun x hx => div_nonneg (sq_nonneg _) (by linarith [fisherEpsilon_pos n]))
  have hIf : (∫⁻ t,I t ∂ν) ≠ ∞ := ne_of_lt (hIb.trans_lt ENNReal.ofReal_lt_top)
  have hIa : ∀ᵐ t ∂ν,I t < ∞ := ae_lt_top' hIm hIf
  have hsp : ∀ᵐ t ∂ν,Integrable (fun x => g t x^2/u t x) m := by
    filter_upwards [hu,hun,hg,hIa] with t hu hn hg hf
    apply (lintegral_ofReal_ne_top_iff_integrable ((hg.aestronglyMeasurable.pow 2).div₀ hu)
      (hn.mono fun x hx => div_nonneg (sq_nonneg _) hx)).mp
    exact hf.ne
  have htr : (fun t => (I t).toReal) =ᵐ[ν] fun t => ∫ x,g t x^2/u t x ∂m := by
    filter_upwards [hsp,hun] with t hi hn
    rw [show I t = ENNReal.ofReal (∫ x,g t x^2/u t x ∂m) from
      (ofReal_integral_eq_lintegral_ofReal hi (hn.mono fun x hx => div_nonneg (sq_nonneg _) hx)).symm,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae (hn.mono fun x hx => div_nonneg (sq_nonneg _) hx))]
  refine ⟨hsp,(integrable_toReal_of_lintegral_ne_top hIm hIf).congr htr,?_⟩
  rw [← integral_congr_ae htr,integral_toReal hIm hIa]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hIb).trans_eq (ENNReal.toReal_ofReal hC)
lemma integral_regularizedFisher_tendsto {u g : X → ℝ} (hu : AEStronglyMeasurable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hg : MemLp g 2 m)
    (hz : ∀ᵐ x ∂m,u x = 0 → g x = 0) (hI : Integrable (fun x => g x^2/u x) m) :
    Tendsto (fun n => ∫ x,g x^2/(u x+fisherEpsilon n) ∂m) atTop (𝓝 (∫ x,g x^2/u x ∂m)) :=
  integral_tendsto_of_tendsto_of_monotone
    (fun n => integrable_regularizedFisher hu hun hg (fisherEpsilon_pos n)) hI
    (hun.mono fun x hx => regularizedFisher_mono hx)
    (by filter_upwards [hun,hz] with x hx hz; exact regularizedFisher_tendsto hx hz)

lemma integral_regularizedFisher_action_tendsto {T : Type*} [MeasurableSpace T] {ν : Measure T}
    {u g : T → X → ℝ}
    (hu : ∀ᵐ t ∂ν,AEStronglyMeasurable (u t) m)
    (hun : ∀ᵐ t ∂ν,∀ᵐ x ∂m,0 ≤ u t x)
    (hg : ∀ᵐ t ∂ν,MemLp (g t) 2 m)
    (hz : ∀ᵐ t ∂ν,∀ᵐ x ∂m,u t x = 0 → g t x = 0)
    (hR : ∀ n,Integrable (fun t => ∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m) ν)
    (hI : ∀ᵐ t ∂ν,Integrable (fun x => g t x^2/u t x) m)
    (hIt : Integrable (fun t => ∫ x,g t x^2/u t x ∂m) ν) :
    Tendsto (fun n => ∫ t,∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m ∂ν) atTop
      (𝓝 (∫ t,∫ x,g t x^2/u t x ∂m ∂ν)) := by
  apply integral_tendsto_of_tendsto_of_monotone hR hIt
  · filter_upwards [hu,hun,hg] with t hu hn hg
    intro n k hnk
    exact integral_mono_ae (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos n))
      (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos k))
      (hn.mono fun x hx => regularizedFisher_mono hx hnk)
  · filter_upwards [hu,hun,hg,hz,hI] with t ht hn hg hz hi
    exact integral_regularizedFisher_tendsto ht hn hg hz hi
end WeakHessian

end
end InlinedFile0

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

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

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

end WeakHessian

end
end InlinedFile30

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ReducedEntropy
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

lemma renormalizedEntropy_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => renormalizedEntropy (fisherEpsilon n) x) atTop (𝓝 (reducedEntropy x)) := by
  have h1 := Real.continuous_mul_log.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := x)).add fisherEpsilon_tendsto)
  have h2 := Real.continuous_mul_log.continuousAt.tendsto.comp fisherEpsilon_tendsto
  convert! (h1.sub h2).sub_const x using 1
  · ext n
    exact renormalizedEntropy_eq (fisherEpsilon_pos n) hx
  · simp only [reducedEntropy,add_zero,zero_mul,sub_zero]

lemma renormalizedEntropy_abs_bound {a x V : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    |renormalizedEntropy a x| ≤ x^2/2+|x*V|+Real.exp (-V) := by
  have hl := renormalizedEntropy_lower ha hx (Real.exp_pos (-V))
  rw [Real.log_exp,mul_neg] at hl
  have hu := renormalizedEntropy_upper ha ha1 hx
  exact abs_le.mpr ⟨by linarith [le_abs_self (x*V),sq_nonneg x],
    by linarith [abs_nonneg (x*V),Real.exp_pos (-V)]⟩

lemma reducedEntropy_abs_bound {x V : ℝ} (hx : 0 ≤ x) :
    |reducedEntropy x| ≤ x^2/2+|x*V|+Real.exp (-V) :=
  le_of_tendsto ((renormalizedEntropy_tendsto hx).abs)
    (Eventually.of_forall (fun n => renormalizedEntropy_abs_bound (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx))

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_reducedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Integrable (fun x => reducedEntropy (u x)) m := by
  apply (((hu.integrable_sq.div_const 2).add hUV.norm).add hV).mono'
    ((Real.continuous_mul_log.sub continuous_id).comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards [hun] with x hx
  simpa only [Real.norm_eq_abs,Pi.add_apply,reducedEntropy,Pi.sub_apply,id_eq] using! reducedEntropy_abs_bound (V := V x) hx

lemma tendsto_integral_renormalizedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => ∫ x,renormalizedEntropy (fisherEpsilon n) (u x) ∂m) atTop
      (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => u x^2/2+‖u x*V x‖+Real.exp (-V x))
  · intro n
    exact (continuous_iff_continuousAt.mpr fun y =>
      (renormalizedEntropy_hasDeriv (fisherEpsilon_pos n) y).continuousAt).comp_aestronglyMeasurable hu.aestronglyMeasurable
  · exact ((hu.integrable_sq.div_const 2).add hUV.norm).add hV
  · intro n
    filter_upwards [hun] with x hx
    simpa only [Real.norm_eq_abs] using renormalizedEntropy_abs_bound (V := V x)
      (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx
  · exact hun.mono (fun x hx => renormalizedEntropy_tendsto hx)
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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatFisherFinite
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
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology InnerProductSpace NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_fisher_finite_action {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {b : ℝ} (hb : 0 ≤ b) :
    (∀ᵐ t ∂volume.restrict (Icc 0 b),Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m) ∧
    IntervalIntegrable (fun t => ∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) volume 0 b ∧
    (∫ t in 0..b,∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) ≤
      ‖u‖^2/2+‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*b)*
        ‖hD.toLp (fun x => V x*Real.exp (-V x))‖+(∫ x,Real.exp (-V x) ∂m) := by
  have ht : ∀ᵐ t ∂volume.restrict (Icc 0 b),t ∈ Icc 0 b := ae_restrict_mem measurableSet_Icc
  have hL (t : ℝ) := hcd.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hack := fisher_action_of_regularization (u := fun t => cheegerHeat h t u)
    (g := fun t => weakGradient m (cheegerHeat h t u))
    (ν := volume.restrict (Icc 0 b))
    (C := ‖u‖^2/2+‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*b)*
        ‖hD.toLp (fun x => V x*Real.exp (-V x))‖+(∫ x,Real.exp (-V x) ∂m))
    (by have hw0 : 0 ≤ ∫ x,Real.exp (-V x) ∂m := integral_nonneg (fun x => (Real.exp_pos (-V x)).le)
        positivity)
    (ae_of_all _ fun t => Lp.aestronglyMeasurable _)
    (ht.mono fun t ht => cheegerHeat_nonneg h ht.1 u hun)
    (ae_of_all _ fun t => (hL t).1.2.2)
    (ae_of_all _ fun t => weakGradient_zero_on_zero (hL t).1.2.1 (Lp.stronglyMeasurable _).measurable)
    (fun n => ((hcd.cheegerHeat_regularizedFisher_continuousOn hfin o h hu hun
      (fisherEpsilon_pos n)).mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc)
    (fun n => by
      have H := hcd.cheegerHeat_regularizedFisher_action_bound hN hfull hfin o h hu hun hi hV hU hD hw
        (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hb
      rwa [intervalIntegral.integral_of_le hb,← integral_Icc_eq_integral_Ioc] at H)
  refine ⟨hack.1,(intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr hack.2.1,?_⟩
  rw [intervalIntegral.integral_of_le hb,← integral_Icc_eq_integral_Ioc]
  exact hack.2.2

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatEntropyDissipation
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
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology InnerProductSpace NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_entropy_dissipation {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {b : ℝ} (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) =
      (∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m) := by
  have ht : ∀ᵐ t ∂volume.restrict (Icc 0 b),t ∈ Icc 0 b := ae_restrict_mem measurableSet_Icc
  have hL (t : ℝ) := hcd.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hI := hcd.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb
  have hFI := integral_regularizedFisher_action_tendsto (u := fun t => cheegerHeat h t u)
    (g := fun t => weakGradient m (cheegerHeat h t u)) (ν := volume.restrict (Icc 0 b))
    (ae_of_all _ fun t => Lp.aestronglyMeasurable _)
    (ht.mono fun t ht => cheegerHeat_nonneg h ht.1 u hun)
    (ae_of_all _ fun t => (hL t).1.2.2)
    (ae_of_all _ fun t => weakGradient_zero_on_zero (hL t).1.2.1 (Lp.stronglyMeasurable _).measurable)
    (fun n => ((hcd.cheegerHeat_regularizedFisher_continuousOn hfin o h hu hun
      (fisherEpsilon_pos n)).mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc)
    hI.1 ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mp hI.2.1)
  have hUt := (hcd.cheegerHeat_weighted hfin o h u hV hU hb).1
  have he0 := tendsto_integral_renormalizedEntropy (Lp.memLp u) hun (weighted_pairing hU hD).1 hw
  have het := tendsto_integral_renormalizedEntropy (Lp.memLp (cheegerHeat h b u))
    (cheegerHeat_nonneg h hb u hun) (weighted_pairing hUt hD).1 hw
  have heq (n : ℕ) :
      (∫ t in Icc 0 b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+fisherEpsilon n) ∂m) =
        (∫ x,renormalizedEntropy (fisherEpsilon n) (u x) ∂m)-
        (∫ x,renormalizedEntropy (fisherEpsilon n) (cheegerHeat h b u x) ∂m) := by
    have H := hcd.cheegerHeat_renormalizedEntropy_FTC hN hfull hfin o h hu hun hi (fisherEpsilon_pos n) hb
    rwa [intervalIntegral.integral_of_le hb,← integral_Icc_eq_integral_Ioc] at H
  have he : (∫ t in Icc 0 b,∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m) =
      (∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m) :=
    tendsto_nhds_unique (hFI.congr heq) (he0.sub het)
  rwa [intervalIntegral.integral_of_le hb,← integral_Icc_eq_integral_Ioc]

end WeakHessian

end
end InlinedFile0

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

lemma QuadraticLipschitzBound.cut_memLp (hfin : FiniteOnBoundedSets m) (o : X)
    {T : ℝ} (hT : 0 < T) {φ : X → ℝ} (hφ : QuadraticLipschitzBound o T φ) (n : ℕ) :
    MemLp (fun x => φ x*radialCutoff o n x) 2 m := by
  let : Nonempty X := ⟨o⟩
  exact ((hφ.localSobolev hfin hT).mul_lipschitz_compactSupport hfin
    (radialCutoff_lipschitz o n) (radialCutoff_compact o n)).1

end WeakHessian

end
end InlinedFile46

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_GeneralCostSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile47
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.compact_quadratic_cost_support {K N : ℝ}
    (hcd : CurvatureDimension m K N) (μ ν : ProbabilityMeasure X)
    (hm : (μ:Measure X) ≪ m) (hn : (ν:Measure X) ≪ m)
    (o : X) (R T : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      BoundedTracks (π:Measure (Curve X)) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∃ L : ℝ≥0, LipschitzWith L ψ) ∧
      (∀ x y, y ∈ Metric.closedBall o T → φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) := by
  have hm2 := hasSecondMoment_of_ae_dist_le o R (ae_iff.mpr hsμ)
  have hn2 := hasSecondMoment_of_ae_dist_le o T (ae_iff.mpr hsν)
  obtain ⟨p,hp,hgeo,ho,_⟩ := hcd μ ν inferInstance inferInstance hm2 hn2 hm hn
  let π : ProbabilityMeasure (Curve X) := ⟨p,hp⟩
  have haμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (R:ℝ) ≤ (R+T:ℝ≥0))) hx
  have haν : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (T:ℝ) ≤ (R+T:ℝ≥0))) hx
  have hb : BoundedTracks p := by
    refine ⟨o,3*((R+T:ℝ≥0):ℝ)+1,by positivity,?_⟩
    have H := optimalPlan_supported_tube π hgeo ho.1 (ae_iff.mp haμ) (ae_iff.mp haν)
    filter_upwards [ae_iff.mpr H] with γ hγ
    intro t
    exact (boundedEndpointTube_range hγ t).trans (by linarith)
  obtain ⟨f,g,hf,hg,hd,hc⟩ := bounded_support_kantorovich_potentials
    (isCompact_closedBall o ((R+T:ℝ≥0):ℝ)) (Metric.nonempty_closedBall.mpr (R+T).coe_nonneg)
    (μ:Measure X) (ν:Measure X) haμ haν ho
    (R := 2*(R+T)) (by
      intro x hx y hy
      have H := dist_triangle x o y
      rw [dist_comm o y] at H
      change dist x o ≤ (R+T:ℝ≥0) at hx
      change dist y o ≤ (R+T:ℝ≥0) at hy
      exact H.trans (by exact_mod_cast (by linarith : dist x o+dist y o ≤ 2*((R+T:ℝ≥0):ℝ))))
  have hcp : ∀ᵐ γ ∂p, f (γ timeZero)+g (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2 :=
    ae_of_ae_map ((continuous_eval_const timeZero).measurable.prodMk
      (continuous_eval_const timeOne).measurable).aemeasurable hc
  let S := Metric.closedBall o (T:ℝ)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hne : S.Nonempty := Metric.nonempty_closedBall.mpr T.coe_nonneg
  let f' := compactCTransform S g
  have hq : QuadraticLipschitzBound o T f' := compactCTransform_difference_bound hS hne hg.continuous.continuousOn o (Subset.refl S)
  have hq' : QuadraticLipschitzBound o T (fun x => f' x-f' o) := by
    intro x y
    simpa only [sub_sub_sub_cancel_right] using hq x y
  have hg' : LipschitzWith (2*(R+T)) (fun y => g y+f' o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul x y
  have hsπ : ∀ᵐ γ ∂p, γ timeOne ∈ S := by
    apply (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable hS.measurableSet).mp
    change ∀ᵐ x ∂interpolation p timeOne, x ∈ S
    rw [ho.1.interpolation_endpoints.2]
    exact ae_iff.mpr hsν
  refine ⟨π,(fun x => f' x-f' o),(fun y => g y+f' o),hb,ho,hq',sub_self _,⟨_,hg'⟩,?_,?_⟩
  · intro x y hy
    have H := compactCTransform_le hS hne hg.continuous.continuousOn x hy
    dsimp [f']
    linarith
  · filter_upwards [hsπ,hcp] with γ hs hc
    have he := compactCTransform_contact hS hne hg.continuous.continuousOn hd hs hc
    change f' (γ timeZero)-f' o+(g (γ timeOne)+f' o) = _
    change f' (γ timeZero) = _ at he
    rw [he]
    linarith

theorem CurvatureDimension.noncompact_cost_support [SigmaFinite m] {K N : ℝ}
    (hcd : CurvatureDimension m K N)
    (w : X → ℝ) (hw : MemLp w 2 m) (hwm : Measurable w)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (hn : (ν:Measure X) ≪ m) (o : X) (T : ℝ≥0)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw hwm o
  let us (n : ℕ) (x : X) := c n*(w x*radialCutoff o (n+k) x)
  have hum (n : ℕ) : Measurable (us n) :=
    (hwm.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).const_mul _
  have hu2 (n : ℕ) : MemLp (us n) 2 m := (radial_mul_memLp hw o (n+k)).const_mul (c n)
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
    have H := squareDensity_tendsto_probability hum hwm hu2 hw hp inferInstance (normalized_radial_tendsto hw o k hcT)
    have he : squareDensityProbability m w inferInstance = μ := ProbabilityMeasure.toMeasure_injective hμ.symm
    simpa only [he] using H
  have huW (n : ℕ) : MemLp (fun x => us n x*(dist x o+T)) 2 m := by
    convert ((radial_mul_memLp hwW o (n+k)).const_mul (c n)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x; dsimp [us]; ring
  have hTV := radial_weighted_density_tendsto hwW o k hcT
  have hex (n : ℕ) := hcd.compact_quadratic_cost_support (μs n) ν
    (withDensity_absolutelyContinuous _ _) hn o (R n) T (hsμ n) hsν
  choose ps fs gs hbps hops hfs hzero hgs hdual hcontact using hex
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
  refine ⟨q,φ,hqp,hqo,hqt,hφ,hφo,?_⟩
  intro ξ hξ q' hq' hq't
  exact limit_quadratic_transport_support (fun n => hum (s n)) hwm o T (fun n => huW (s n)) hwW
    (hTV.comp hs.tendsto_atTop) μ ν hμ (fun n => ps (s n)) (fun n => (h0 (s n)).trans (hμs (s n)))
    (fun n => h1 (s n)) (fun n => fs (s n)) (fun n => gs (s n)) φ (fun n => hfs (s n)) hφ
    (fun n => hzero (s n)) hφT (fun n => hcg (s n)) (fun n => hig (s n)) measurableSet_closedBall hsb
    (fun n => hdual (s n)) (fun n => hcontact (s n)) (hcost.comp hs.tendsto_atTop) ξ hξ hq' hq't
end WeakHessian

end
end InlinedFile47

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

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_sqrt_memLp (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) :
    MemLp (fun x => Real.sqrt (u x)) 2 m := by
  apply (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable u |>.measurable.sqrt.aestronglyMeasurable)).mpr
  exact hi.congr (hun.mono fun x hx => (Real.sq_sqrt hx).symm)

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_sqrt_weighted (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {W V : X → ℝ} (hWm : AEStronglyMeasurable W m)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => W x^2*Real.exp (-V x)) 2 m) :
    MemLp (fun x => Real.sqrt (u x)*W x) 2 m := by
  apply (memLp_two_iff_integrable_sq ((Lp.stronglyMeasurable u |>.measurable.sqrt.aestronglyMeasurable).mul hWm)).mpr
  exact (weighted_pairing hU hW).1.congr (hun.mono fun x hx => by simp only [Pi.mul_apply,mul_pow,Real.sq_sqrt hx])

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma densityMeasure_finiteEntropy [SigmaFinite m] (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    [IsFiniteMeasure (densityMeasure m u)] {V : X → ℝ}
    (hUV : Integrable (fun x => u x*V x) m) (hV : Integrable (fun x => Real.exp (-V x)) m) :
    FiniteEntropy m (densityMeasure m u) := by
  have he := densityMeasure_eq_square_sqrt u hun
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_finiteEntropy_iff (Lp.stronglyMeasurable u |>.measurable.sqrt)]
  have H := (integrable_reducedEntropy (Lp.memLp u) hun hUV hV).add hi
  apply H.congr
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,Pi.add_apply,reducedEntropy]
  ring

variable [SigmaFinite m]

lemma CurvatureDimension.density_cost_support {K N : ℝ} (hcd : CurvatureDimension m K N)
    (o : X) (T : ℝ≥0) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hn : (ν:Measure X) ≪ m) (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {V : X → ℝ} (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) := by
  exact hcd.noncompact_cost_support _ (densityMeasure_sqrt_memLp u hun hi)
    (Lp.stronglyMeasurable u |>.measurable.sqrt) μ ν (hμ.trans (densityMeasure_eq_square_sqrt u hun)) hn o T
    (densityMeasure_sqrt_weighted u hun (by fun_prop) hU hW) hsν

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
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile42
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma radial_tail_norm_tendsto {f : X → ℝ} (hf : MemLp f 2 m) (o : X) :
    Tendsto (fun n => ‖(radial_tail_memLp hf o n).toLp
      (fun x => f x*(1-radialCutoff o n x))‖) atTop (𝓝 0) := by
  have H := ((tendsto_const_nhds (x := hf.toLp f)).sub (radial_mul_tendsto hf o)).norm
  have he (n : ℕ) : (radial_tail_memLp hf o n).toLp (fun x => f x*(1-radialCutoff o n x)) =
      hf.toLp f-(radial_mul_memLp hf o n).toLp (fun x => f x*radialCutoff o n x) := by
    rw [← MemLp.toLp_sub]
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring
  simpa only [he,sub_self,norm_zero] using H

lemma weighted_pairing_cutoff_error {V f φ : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m) (o : X) (n : ℕ) :
    ‖(∫ x,f x*φ x ∂m)-(∫ x,f x*φ x*radialCutoff o n x ∂m)‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*
      ‖(radial_tail_memLp hφ o n).toLp (fun x => (φ x*Real.exp (-V x))*(1-radialCutoff o n x))‖ := by
  have hi := (weighted_pairing hf hφ).1
  have hic := hi.mul_bdd (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
  rw [← integral_sub hi hic]
  have hc : MemLp (fun x => (φ x*(1-radialCutoff o n x))*Real.exp (-V x)) 2 m := by
    convert radial_tail_memLp hφ o n using 1
    all_goals try with_reducible_and_instances rfl
    funext x; ring
  convert (weighted_pairing hf hc).2 using 1
  · congr 2; funext x; ring
  · congr 2
    apply Lp.ext
    filter_upwards [hc.coeFn_toLp,(radial_tail_memLp hφ o n).coeFn_toLp] with x hx hy
    rw [hx,hy]; ring

omit [MetricSpace X] [BorelSpace X] in
lemma integral_mul_eq_inner_toLp (f : Lp ℝ 2 m) {φ : X → ℝ} (hφ : MemLp φ 2 m) :
    (∫ x,f x*φ x ∂m) = ⟪hφ.toLp φ,f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial]

lemma weighted_pairing_tendsto {ι : Type*} {l : Filter ι}
    {V φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m) (o : X)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {fs : ι → Lp ℝ 2 m} {f : Lp ℝ 2 m} (hlim : Tendsto fs l (𝓝 f))
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hfs : ∀ i, MemLp (fun x => fs i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l, ‖(hfs i).toLp (fun x => fs i x*Real.exp (V x))‖ ≤ B) :
    Tendsto (fun i => ∫ x,fs i x*φ x ∂m) l (𝓝 (∫ x,f x*φ x ∂m)) := by
  let D := ‖hf.toLp (fun x => f x*Real.exp (V x))‖
  have htail : Tendsto (fun n => (B+D)*‖(radial_tail_memLp hφ o n).toLp
      (fun x => (φ x*Real.exp (-V x))*(1-radialCutoff o n x))‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (radial_tail_norm_tendsto hφ o).const_mul (B+D)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n,hn⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hc : Tendsto (fun i => ∫ x,fs i x*φ x*radialCutoff o n x ∂m) l
      (𝓝 (∫ x,f x*φ x*radialCutoff o n x ∂m)) := by
    simp_rw [mul_assoc,integral_mul_eq_inner_toLp _ (hcut n)]
    exact (innerSL ℝ ((hcut n).toLp _)).continuous.continuousAt.tendsto.comp hlim
  filter_upwards [hB,(Metric.tendsto_nhds.mp hc) (ε/2) (half_pos hε)] with i hi hic
  have he1 := (weighted_pairing_cutoff_error (hfs i) hφ o n).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have he2 := weighted_pairing_cutoff_error hf hφ o n
  have ht1 := dist_triangle (∫ x,fs i x*φ x ∂m)
    (∫ x,fs i x*φ x*radialCutoff o n x ∂m) (∫ x,f x*φ x ∂m)
  have ht2 := dist_triangle (∫ x,fs i x*φ x*radialCutoff o n x ∂m)
    (∫ x,f x*φ x*radialCutoff o n x ∂m) (∫ x,f x*φ x ∂m)
  simp only [dist_eq_norm] at ht1 ht2 hic ⊢
  rw [norm_sub_rev (∫ x,f x*φ x*radialCutoff o n x ∂m)] at ht2
  dsimp only [D] at hn
  nlinarith

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma CurvatureDimension.cheegerHeat_weighted_pairing_continuous {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m) :
    Continuous (fun t : ℝ => ∫ x,cheegerHeat h (max t 0) u x*φ x ∂m) := by
  have hc : Continuous (fun t : ℝ => cheegerHeat h (max t 0) u) :=
    (cheegerHeat_continuousOn hfin h u).comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t 0)
  apply continuous_iff_continuousAt.mpr
  intro t
  apply weighted_pairing_tendsto hφ o hcut hc.continuousAt
    (hcd.cheegerHeat_weighted hfin o h u hV hU (le_max_right t 0)).1
    (fun s => (hcd.cheegerHeat_weighted hfin o h u hV hU (le_max_right s 0)).1)
  filter_upwards [((continuous_id.max continuous_const : Continuous (fun s : ℝ => max s 0)).continuousAt.eventually_lt_const
    (lt_add_one (max t 0)))] with s hs
  exact (hcd.cheegerHeat_weighted_norm hfin o h u hV hU (le_max_right s 0)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.le (sq_nonneg _))) (norm_nonneg _))
end WeakHessian

end
end InlinedFile42

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatFTC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile43
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_weighted_FTC {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, ∫ x,cheegerHeat h s A x*φ x ∂m) =
      (∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
  let fn (n : ℕ) (s : ℝ) := ∫ x,cheegerHeat h s A x*φ x*radialCutoff o n x ∂m
  have he (n : ℕ) (s : ℝ) : fn n s = ⟪(hcut n).toLp _,cheegerHeat h s A⟫_ℝ := by
    simp only [fn,mul_assoc,integral_mul_eq_inner_toLp _ (hcut n)]
  have hc (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    change ContinuousOn (fun s => fn n s) (Ici 0)
    simp_rw [he]
    exact (innerSL ℝ ((hcut n).toLp _)).continuous.comp_continuousOn (cheegerHeat_continuousOn hfin h A)
  have hn (n : ℕ) : MemLp (fun x => (φ x*radialCutoff o n x)*Real.exp (-V x)) 2 m := by
    convert radial_mul_memLp hφ o n using 1
    all_goals try with_reducible_and_instances rfl
    funext x; ring
  have hnn (n : ℕ) : ‖(hn n).toLp _‖ ≤ ‖hφ.toLp _‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hn n).coeFn_toLp,hφ.coeFn_toLp] with x hx hy
    rw [hx,hy]
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg (φ x)) (radialCutoff_le_one o n x)) (abs_nonneg _)
  let M := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ M*‖hφ.toLp _‖ := by
    have H := weighted_pairing (hcd.cheegerHeat_weighted hfin o h A hV hA hs.1).1 (hn n)
    simp only [← mul_assoc] at H
    exact H.2.trans (mul_le_mul
      ((hcd.cheegerHeat_weighted_norm hfin o h A hV hA hs.1).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))) (norm_nonneg _)))
      (hnn n) (norm_nonneg _) (by dsimp [M]; positivity))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop
      (𝓝 (∫ x,cheegerHeat h s A x*φ x ∂m)) :=
    integral_radialCutoff_tendsto o (weighted_pairing (hcd.cheegerHeat_weighted hfin o h A hV hA hs).1 hφ).1
  have htime : Tendsto (fun n => ∫ s in 0..t,fn n s) atTop
      (𝓝 (∫ s in 0..t,∫ x,cheegerHeat h s A x*φ x ∂m)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M*‖hφ.toLp _‖)
    · exact Eventually.of_forall fun n => ((hc n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by
        rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hb n s (by
        rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le)
  have hFTC (n : ℕ) : (∫ s in 0..t,fn n s) =
      (∫ x,cheegerHeat h t u x*φ x*radialCutoff o n x ∂m)-(∫ x,u x*φ x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ ((hcut n).toLp _)
    have hai : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t :=
      ((cheegerHeat_continuousOn hfin h A).mono (show uIcc (0:ℝ) t ⊆ Ici 0 by
        rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfin h hu ht)
    rw [← T.intervalIntegral_comp_comm hai,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_mul_eq_inner_toLp _ (hcut n),← mul_assoc,fn] using H
  have hs := (integral_radialCutoff_tendsto o
    (weighted_pairing (hcd.cheegerHeat_weighted hfin o h u hV hU ht).1 hφ).1).sub
    (integral_radialCutoff_tendsto o (weighted_pairing hU hφ).1)
  simp_rw [hFTC] at htime
  exact tendsto_nhds_unique htime hs

lemma CurvatureDimension.cheegerHeat_weighted_deriv {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x,cheegerHeat h s u x*φ x ∂m)
      (∫ x,cheegerHeat h t A x*φ x ∂m) t := by
  let g (s : ℝ) := ∫ x,cheegerHeat h (max s 0) A x*φ x ∂m
  have hc : Continuous g := hcd.cheegerHeat_weighted_pairing_continuous hfin o h A hV hA hφ hcut
  have he (r : ℝ) (hr : 0 ≤ r) : (∫ s in 0..r,g s) =
      (∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
    rw [← hcd.cheegerHeat_weighted_FTC hfin o h hu hV hU hA hφ hcut hr]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr] at hs
    simp only [g,max_eq_left hs.1]
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const (∫ x,u x*φ x ∂m)
  have H : HasDerivAt (fun r => (∫ s in 0..r,g s)+(∫ x,u x*φ x ∂m))
      (∫ x,cheegerHeat h t A x*φ x ∂m) t := by
    simpa only [g,max_eq_left ht.le] using hd
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  rw [he r hr.le]
  ring
end WeakHessian

end
end InlinedFile43

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile50
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_deriv {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {t d : ℝ} (ht : 0 < t)
    (hI : Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m)
    (hd : HasDerivAt (fun s => quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)) d t) :
    d/2+K/2*quadraticWassersteinSq (μ t:Measure X) (ν:Measure X) ≤
      entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X) := by
  have hn (s : ℝ) (hs : 0 ≤ s) := cheegerHeat_nonneg h hs u hun
  have hi' (s : ℝ) (hs : 0 ≤ s) := (cheegerHeat_integrable hfin o h u hi hs).1
  have hwU (s : ℝ) (hs : 0 ≤ s) := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU hs).1
  have hwA := (hrcd.1.cheegerHeat_weighted hfin o h A hV hA ht.le).1
  have hB' (s : ℝ) (hs : 0 ≤ s) : ∀ᵐ x ∂m,cheegerHeat h s u x ≤ B :=
    (cheegerHeat_bounded h hs hB u ((hun.and huB).mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2)).mono
      fun x hx => (le_abs_self _).trans hx
  have hL := hrcd.1.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hEnt : FiniteEntropy m (μ t:Measure X) := by
    have he := hμ t ht.le
    let : IsFiniteMeasure (densityMeasure m (cheegerHeat h t u)) := he ▸ inferInstance
    rw [he]
    exact densityMeasure_finiteEntropy _ (hn t ht.le) (hi' t ht.le) (weighted_pairing (hwU t ht.le) hD).1 hw
  obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar,hent⟩ := hrcd.generator_entropy_subdifferential hN hfin o hL
    (hn t ht.le) (hi' t ht.le) hB (hB' t ht.le) hI (μ t) ν (hμ t ht.le) hEnt T hT hV
    (hwU t ht.le) hwA hW hW1 hsν hCt hdν
  have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hV.continuous.measurable hW
  have hp := hrcd.1.cheegerHeat_weighted_deriv hfin o h hu hV hU hA hφW
    (hφ.cut_memLp hfin o hT) ht
  have hmin : IsLocalMin (fun s => quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)-
      2*(∫ x,cheegerHeat h s u x*φ x ∂m)) t := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hnν : (ν:Measure X) ≪ m := Measure.absolutelyContinuous_of_le_smul hdν
    obtain ⟨q',ψ,hq'p,hq'o,hq't,_⟩ := hrcd.1.density_cost_support o T (cheegerHeat h s u)
      (hn s hs.le) (hi' s hs.le) (μ s) ν (hμ s hs.le) hnν hsν (hwU s hs.le) hW
    have hSW : Integrable (fun x => (dist x o+T)^2) (μ s:Measure X) := by
      rw [hμ s hs.le]
      exact densityMeasure_quadratic_integrable o T _ (hn s hs.le) (hwU s hs.le) hW
    have H := hvar (μ s) hSW q' hq'o.1 hq't
    rw [← hqo.quadraticWassersteinSq_eq,← hq'o.quadraticWassersteinSq_eq,
      hμ t ht.le,hμ s hs.le,integral_densityMeasure m _ (hn t ht.le),integral_densityMeasure m _ (hn s hs.le)] at H
    rw [← hμ t ht.le,← hμ s hs.le] at H
    change quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)-2*(∫ x,cheegerHeat h t u x*φ x ∂m) ≤ _
    linarith
  have H := hmin.hasDerivAt_eq_zero (hd.sub (hp.const_mul 2))
  rw [← hqo.quadraticWassersteinSq_eq] at hent
  linarith
end WeakHessian

end
end InlinedFile50

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile49
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_weighted_pairing_lipschitz {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {b s t : ℝ} (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) :
    |(∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,cheegerHeat h s u x*φ x ∂m)| ≤
      (‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hφ.toLp _‖)*|t-s| := by
  let g (s : ℝ) := ∫ x,cheegerHeat h (max s 0) A x*φ x ∂m
  have hc : Continuous g := hcd.cheegerHeat_weighted_pairing_continuous hfin o h A hV hA hφ hcut
  have he (r : ℝ) (hr : 0 ≤ r) : (∫ z in 0..r,g z) =
      (∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
    rw [← hcd.cheegerHeat_weighted_FTC hfin o h hu hV hU hA hφ hcut hr]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hr] at hz
    simp only [g,max_eq_left hz.1]
  have hst := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 s) (hc.intervalIntegrable (μ := volume) s t)
  rw [he s hs.1,he t ht.1] at hst
  have he' : (∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,cheegerHeat h s u x*φ x ∂m) = ∫ z in s..t,g z := by linarith
  rw [he',← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro z hz
  have hz' : z ∈ Icc 0 b := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hz)
  simp only [g,max_eq_left hz'.1]
  exact (weighted_pairing (hcd.cheegerHeat_weighted hfin o h A hV hA hz'.1).1 hφ).2.trans
    (mul_le_mul_of_nonneg_right
      ((hcd.cheegerHeat_weighted_norm hfin o h A hV hA hz'.1).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz'.2 (sq_nonneg _))) (norm_nonneg _)))
      (norm_nonneg _))

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma QuadraticLipschitzBound.weighted_norm_le (o : X) {T : ℝ} (hT : 0 ≤ T)
    {φ V : X → ℝ} (hφ : QuadraticLipschitzBound o T φ) (hzero : φ o = 0)
    (hφW : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    ‖hφW.toLp _‖ ≤ ‖hW.toLp _‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hφW.coeFn_toLp,hW.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (dist x o+T)),abs_of_pos (Real.exp_pos (-V x))]
  exact mul_le_mul_of_nonneg_right (hφ.centered_bound hT hzero x) (Real.exp_pos _).le

variable [SigmaFinite m]

lemma CurvatureDimension.cheegerHeat_cost_lipschitz {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (hn : (ν:Measure X) ≪ m) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    {b s t : ℝ} (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) :
    |quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)-quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)| ≤
      (2*‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|t-s| := by
  have hw (r : ℝ) (hr : 0 ≤ r) := (hcd.cheegerHeat_weighted hfin o h u hV hU hr).1
  have hnU (r : ℝ) (hr : 0 ≤ r) := cheegerHeat_nonneg h hr u hun
  have hiU (r : ℝ) (hr : 0 ≤ r) := (cheegerHeat_integrable hfin o h u hi hr).1
  have hex (r : ℝ) (hr : 0 ≤ r) := hcd.density_cost_support o T (cheegerHeat h r u)
    (hnU r hr) (hiU r hr) (μ r) ν (hμ r hr) hn hsν (hw r hr) hW
  have one (r v : ℝ) (hr : r ∈ Icc 0 b) (hv : v ∈ Icc 0 b) :
      quadraticWassersteinSq (μ r:Measure X) (ν:Measure X)-quadraticWassersteinSq (μ v:Measure X) (ν:Measure X) ≤
        (2*‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|r-v| := by
    obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar⟩ := hex r hr.1
    obtain ⟨q',ψ,hq'p,hq'o,hq't,_⟩ := hex v hv.1
    have hvW : Integrable (fun x => (dist x o+T)^2) (μ v:Measure X) := by
      rw [hμ v hv.1]
      exact densityMeasure_quadratic_integrable o T _ (hnU v hv.1) (hw v hv.1) hW
    have H := hvar (μ v) hvW q' hq'o.1 hq't
    rw [← hqo.quadraticWassersteinSq_eq,← hq'o.quadraticWassersteinSq_eq,
      hμ r hr.1,hμ v hv.1,integral_densityMeasure m _ (hnU r hr.1),integral_densityMeasure m _ (hnU v hv.1)] at H
    rw [← hμ r hr.1,← hμ v hv.1] at H
    have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hV.continuous.measurable hW
    have H' := hcd.cheegerHeat_weighted_pairing_lipschitz hfin o h hu hV hU hA hφW
      (hφ.cut_memLp hfin o hT) hv hr
    have Hnorm := hφ.weighted_norm_le o T.coe_nonneg hφ0 hφW hW
    have H'' : |(∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,cheegerHeat h v u x*φ x ∂m)| ≤
        (‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|r-v| :=
      H'.trans (by gcongr)
    calc
      _ ≤ 2*((∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,cheegerHeat h v u x*φ x ∂m)) := H
      _ ≤ 2*((‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|r-v|) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans H'') (by norm_num)
      _ = _ := by ring
  apply abs_le.mpr
  exact ⟨by have H := one s t hs ht; rw [abs_sub_comm s t] at H; linarith,one t s ht hs⟩
end WeakHessian

end
end InlinedFile49

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEVI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile51
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma entropyReal_eq_reducedDensity (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hi : Integrable u m) (hr : Integrable (fun x => reducedEntropy (u x)) m)
    (μ : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u) :
    entropyReal m (μ:Measure X) = (∫ x,reducedEntropy (u x) ∂m)+1 := by
  have hmass : (∫ x,u x ∂m) = 1 := by
    have H := integral_densityMeasure m u hun (fun _ => (1:ℝ))
    rw [← hμ] at H
    simpa using H.symm
  have he := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_entropy_eq (Lp.stronglyMeasurable u |>.measurable.sqrt),← hmass,← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,reducedEntropy,sub_add_cancel]

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_entropy_continuousOn {K N : ℝ}
    (hN : 1 < N) (hcd : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    {b : ℝ} (hb : 0 ≤ b) : ContinuousOn (fun t => entropyReal m (μ t:Measure X)) (Icc 0 b) := by
  have hI := hcd.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb
  have hac := hI.2.1.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hc : ContinuousOn (fun t => (∫ x,reducedEntropy (u x) ∂m)+1-
      ∫ r in 0..t,∫ x,fisherDensity (m := m) (cheegerHeat h r u) x ∂m) (Icc 0 b) := by
    apply ContinuousOn.sub continuousOn_const
    simpa only [uIcc_of_le hb] using hac.continuousOn
  apply hc.congr
  intro t ht
  dsimp only
  rw [hcd.cheegerHeat_entropy_dissipation hN hfull hfin o h hu hun hi hV hU hD hw ht.1,
    entropyReal_eq_reducedDensity _ (cheegerHeat_nonneg h ht.1 u hun)
      (cheegerHeat_integrable hfin o h u hi ht.1).1
      (integrable_reducedEntropy (Lp.memLp _) (cheegerHeat_nonneg h ht.1 u hun)
        (weighted_pairing (hcd.cheegerHeat_weighted hfin o h u hV hU ht.1).1 hD).1 hw) (μ t) (hμ t ht.1)]
  ring

lemma CurvatureDimension.cheegerHeat_cost_ac {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (hn : (ν:Measure X) ≪ m) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (fun t => quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)) 0 b := by
  let C : ℝ≥0 := ⟨2*‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖,by positivity⟩
  have hl : LipschitzOnWith C (fun t => quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)) (Icc 0 b) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    convert! hcd.cheegerHeat_cost_lipschitz hfin o h hu hun hi hV hU hA μ hμ ν hn T hT hsν hW ht hs using 1
    all_goals try with_reducible_and_instances rfl
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hb] using hl

lemma RCD.cheegerHeat_comparison_ae {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ t ∂volume.restrict (Icc 0 b),
      deriv (fun s => quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)) t/2+
        K/2*quadraticWassersteinSq (μ t:Measure X) (ν:Measure X) ≤
          entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X) := by
  have hac := hrcd.1.cheegerHeat_cost_ac hfin o h hu hun hi hV hU hA μ hμ ν
    (Measure.absolutelyContinuous_of_le_smul hdν) T hT hsν hW hb
  have hI := hrcd.1.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb
  filter_upwards [ae_restrict_mem measurableSet_Icc,hI.1,
    ae_restrict_of_ae hac.ae_differentiableAt,ae_restrict_of_ae (show ∀ᵐ t ∂(volume:Measure ℝ), t ≠ 0 by simp [ae_iff])] with t ht hIt hdt ht0
  exact hrcd.cheegerHeat_comparison_deriv hN hfin o h hu hun hi hB huB hV hU hA hD hw μ hμ
    ν T hT hsν hCt hdν hW hW1 (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hIt
    (hdt (by simpa only [uIcc_of_le hb] using ht)).hasDerivAt
end WeakHessian

end
end InlinedFile51

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_IntegratedEVI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile52
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

lemma integrated_exponential_evi_of_ae {E H : ℝ → ℝ} {K b : ℝ} (hb : 0 ≤ b)
    (hE : AbsolutelyContinuousOnInterval E 0 b) (hH : ContinuousOn H (Icc 0 b))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 b), deriv E t/2+K/2*E t ≤ H t) :
    (Real.exp (K*b)*E b-E 0)/2 ≤ ∫ t in 0..b,Real.exp (K*t)*H t := by
  have hG : AbsolutelyContinuousOnInterval (fun t : ℝ => Real.exp (K*t)) 0 b :=
    (by fun_prop : ContDiffOn ℝ 1 (fun t : ℝ => Real.exp (K*t)) (uIcc 0 b)).absolutelyContinuousOnInterval
  have hF := hG.fun_mul hE
  have hHi : IntervalIntegrable (fun t => Real.exp (K*t)*H t) volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hb] using (show ContinuousOn (fun t : ℝ => Real.exp (K*t)) (Icc 0 b) by fun_prop).fun_mul hH
  have ha : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      deriv (fun s => Real.exp (K*s)*E s) t/2 ≤ Real.exp (K*t)*H t := by
    filter_upwards [hbound,ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hE.ae_differentiableAt]
      with t ht htb hdt
    have hd := (((hasDerivAt_id t).const_mul K).exp).mul (hdt (by simpa only [uIcc_of_le hb] using htb)).hasDerivAt
    have hd' : HasDerivAt (fun s => Real.exp (K*s)*E s)
        (Real.exp (K*t)*K*E t+Real.exp (K*t)*deriv E t) t := by
      convert! hd using 1
      all_goals try with_reducible_and_instances rfl
      simp
    rw [hd'.deriv]
    have H := mul_le_mul_of_nonneg_left ht (Real.exp_pos (K*t)).le
    nlinarith
  have H := intervalIntegral.integral_mono_ae_restrict hb (hF.intervalIntegrable_deriv.div_const 2) hHi ha
  rw [intervalIntegral.integral_div,hF.integral_deriv_eq_sub] at H
  simpa only [mul_zero,Real.exp_zero,one_mul] using H

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_integrated_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  exact integrated_exponential_evi_of_ae hb
    (hrcd.1.cheegerHeat_cost_ac hfin o h hu hun hi hV hU hA μ hμ ν
      (Measure.absolutelyContinuous_of_le_smul hdν) T hT hsν hW hb)
    (continuousOn_const.sub (hrcd.1.cheegerHeat_entropy_continuousOn hN hfull hfin o h hu hun hi hV hU hD hw μ hμ hb))
    (hrcd.cheegerHeat_comparison_ae hN hfull hfin o h hu hun hi hB huB hV hU hA hD hw μ hμ ν T hT
      hsν hCt hdν hW hW1 hb)
end WeakHessian

end
end InlinedFile52

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated_oai.{u_1} := @OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated_oai.{u_1}
