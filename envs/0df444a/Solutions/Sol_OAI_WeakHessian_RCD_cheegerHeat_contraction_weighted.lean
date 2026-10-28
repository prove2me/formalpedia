-- Prove2me | solution 1 for OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:57:16.531491+00:00
-- url     : https://prove2.me/submissions/7f4f2f18-6fde-4c80-82fd-4cf5f17bafc0

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_cheegerHeat_comparison_weighted

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
lemma regularizedLog_eq {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    regularizedLog a x = Real.log (x+a)-Real.log a := by
  rw [regularizedLog,truncatedLog_eq ha (by linarith)]

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

lemma cheegerHeat_add (h : QuadraticCheegerEnergy m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    cheegerHeat h (t+s) = cheegerHeat h t * cheegerHeat h s := realHeat_add m _ ht hs

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

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

lemma fisherEpsilon_pos (n : ℕ) : 0 < fisherEpsilon n := by unfold fisherEpsilon; positivity
lemma fisherEpsilon_le_one (n : ℕ) : fisherEpsilon n ≤ 1 := by
  unfold fisherEpsilon
  exact (div_le_one (by positivity)).mpr (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
lemma fisherEpsilon_tendsto : Tendsto fisherEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end WeakHessian

end
end InlinedFile0

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

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma IsCoupling.swap {q : Measure (X×X)} {μ ν : Measure X} (hq : IsCoupling q μ ν) :
    IsCoupling (q.map Prod.swap) ν μ := by
  constructor
  · rw [Measure.map_map measurable_fst measurable_swap]; exact hq.2
  · rw [Measure.map_map measurable_snd measurable_swap]; exact hq.1

omit [ProperSpace X] in
lemma quadraticTransportCost_swap (q : Measure (X×X)) :
    QuadraticTransportCost (q.map Prod.swap) = QuadraticTransportCost q := by
  rw [QuadraticTransportCost,lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2) measurable_swap]
  simp only [Prod.swap,edist_comm,QuadraticTransportCost]

omit [ProperSpace X] in
lemma quadraticWassersteinSq_comm (μ ν : Measure X) : quadraticWassersteinSq μ ν = quadraticWassersteinSq ν μ := by
  unfold quadraticWassersteinSq
  congr 1
  apply le_antisymm
  · apply le_iInf; intro q; apply le_iInf; intro hq
    exact (iInf_le_of_le (q.map Prod.swap) (iInf_le _ hq.swap)).trans_eq (quadraticTransportCost_swap q)
  · apply le_iInf; intro q; apply le_iInf; intro hq
    exact (iInf_le_of_le (q.map Prod.swap) (iInf_le _ hq.swap)).trans_eq (quadraticTransportCost_swap q)

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma quadraticWassersteinSq_le_cost {μ ν : Measure X} {q : Measure (X×X)}
    (hq : IsCoupling q μ ν) (hqt : QuadraticTransportCost q ≠ ∞) :
    quadraticWassersteinSq μ ν ≤ (QuadraticTransportCost q).toReal :=
  ENNReal.toReal_mono hqt (iInf_le_of_le q (iInf_le _ hq))

lemma sqrt_integral_sq_eq_norm_toLp {A : Type*} [MeasurableSpace A] {q : Measure A} {f : A → ℝ}
    (hf : MemLp f 2 q) : Real.sqrt (∫ x,f x^2 ∂q) = ‖hf.toLp f‖ := by
  rw [← norm_toLp_sq_eq_integral hf,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

lemma integral_sq_triangle {A : Type*} [MeasurableSpace A] {q : Measure A} {f g k : A → ℝ}
    (hf : MemLp f 2 q) (hg : MemLp g 2 q) (hkm : AEStronglyMeasurable k q)
    (hk : ∀ᵐ x ∂q,|k x| ≤ |f x+g x|) :
    MemLp k 2 q ∧ Real.sqrt (∫ x,k x^2 ∂q) ≤ Real.sqrt (∫ x,f x^2 ∂q)+Real.sqrt (∫ x,g x^2 ∂q) := by
  have hK : MemLp k 2 q := (hf.add hg).mono hkm hk
  refine ⟨hK,?_⟩
  rw [sqrt_integral_sq_eq_norm_toLp hK,sqrt_integral_sq_eq_norm_toLp hf,sqrt_integral_sq_eq_norm_toLp hg]
  apply (show ‖hK.toLp k‖ ≤ ‖hf.toLp f+hg.toLp g‖ from ?_).trans (norm_add_le _ _)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hK.coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,Lp.coeFn_add (hf.toLp f) (hg.toLp g),hk] with x hx hy hz ha hk
  simpa only [hx,ha,Pi.add_apply,hy,hz,Real.norm_eq_abs] using hk

omit [ProperSpace X] in
lemma exists_coupling_triangle (μ ν ξ : ProbabilityMeasure X)
    {q r : Measure (X×X)} [IsProbabilityMeasure q] [IsProbabilityMeasure r]
    (hq : IsCoupling q μ ν) (hr : IsCoupling r ν ξ)
    (hqt : QuadraticTransportCost q ≠ ∞) (hrt : QuadraticTransportCost r ≠ ∞) :
    ∃ s : Measure (X×X), IsCoupling s μ ξ ∧ QuadraticTransportCost s ≠ ∞ ∧
      Real.sqrt (QuadraticTransportCost s).toReal ≤
        Real.sqrt (QuadraticTransportCost q).toReal+Real.sqrt (QuadraticTransportCost r).toReal := by
  let : Nonempty X := (μ:Measure X).nonempty_of_neZero
  obtain ⟨p,hp,hp0,hp1,hjoin⟩ := exists_fiber_gluing_supported q r Prod.snd Prod.fst
    measurable_snd measurable_fst (hq.2.trans hr.1.symm)
  let := hp
  let F : (X×X)×(X×X) → X×X := fun p => (p.1.1,p.2.2)
  have hFm : Measurable F := (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hsq : IsCoupling (p.map F) μ ξ := by
    constructor
    · rw [Measure.map_map measurable_fst hFm]
      change p.map (Prod.fst ∘ Prod.fst) = _
      rw [← Measure.map_map measurable_fst measurable_fst,hp0,hq.1]
    · rw [Measure.map_map measurable_snd hFm]
      change p.map (Prod.snd ∘ Prod.snd) = _
      rw [← Measure.map_map measurable_snd measurable_snd,hp1,hr.2]
  have hq2 : MemLp (fun z : X×X => dist z.1 z.2) 2 q :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hqt)
  have hr2 : MemLp (fun z : X×X => dist z.1 z.2) 2 r :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (integrable_squared_distance_of_cost hrt)
  have hqP := hq2.comp_measurePreserving (show MeasurePreserving Prod.fst p q from ⟨measurable_fst,hp0⟩)
  have hrP := hr2.comp_measurePreserving (show MeasurePreserving Prod.snd p r from ⟨measurable_snd,hp1⟩)
  have hK := integral_sq_triangle hqP hrP (show AEStronglyMeasurable (fun z => dist z.1.1 z.2.2) p from by fun_prop) (by
    filter_upwards [hjoin] with z hz
    simp only [Function.comp_def,abs_of_nonneg dist_nonneg,abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
    rw [← hz]
    exact dist_triangle z.1.1 z.1.2 z.2.2)
  have hki : Integrable (fun z => dist z.1.1 z.2.2^2) p := (memLp_two_iff_integrable_sq (by fun_prop)).mp hK.1
  have hsi : Integrable (fun z : X×X => dist z.1 z.2^2) (p.map F) :=
    (integrable_map_measure ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable hFm.aemeasurable).mpr hki
  have hst := cost_ne_top_iff_integrable_sq.mpr hsi
  refine ⟨p.map F,hsq,hst,?_⟩
  rw [quadraticTransportCost_eq_integral hst,quadraticTransportCost_eq_integral hqt,quadraticTransportCost_eq_integral hrt]
  simp only [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [integral_map hFm.aemeasurable ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable]
  have hqeq : (∫ z, (dist z.1 z.2)^2 ∂q) = ∫ z : (X×X)×(X×X),dist z.1.1 z.1.2^2 ∂p := by
    rw [← hp0,integral_map measurable_fst.aemeasurable (by fun_prop)]
  have hreq : (∫ z, (dist z.1 z.2)^2 ∂r) = ∫ z : (X×X)×(X×X),dist z.2.1 z.2.2^2 ∂p := by
    rw [← hp1,integral_map measurable_snd.aemeasurable (by fun_prop)]
  rw [hqeq,hreq]
  exact hK.2

lemma quadraticWassersteinSq_triangle (μ ν ξ : ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    (hξ : Integrable (fun x => dist x o^2) (ξ:Measure X)) :
    Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ξ:Measure X)) ≤
      Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))+
        Real.sqrt (quadraticWassersteinSq (ν:Measure X) (ξ:Measure X)) := by
  obtain ⟨q,hqp,hq,hqt⟩ := exists_optimal_coupling_of_moments μ ν o hμ hν
  obtain ⟨r,hrp,hr,hrt⟩ := exists_optimal_coupling_of_moments ν ξ o hν hξ
  let := hqp; let := hrp
  obtain ⟨s,hs,hst,H⟩ := exists_coupling_triangle μ ν ξ hq.1 hr.1 hqt hrt
  rw [hq.quadraticWassersteinSq_eq,hr.quadraticWassersteinSq_eq]
  exact (Real.sqrt_le_sqrt (quadraticWassersteinSq_le_cost hs hst)).trans H
end WeakHessian

end
end InlinedFile58

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_CostTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile63
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadraticWassersteinSq_tendsto_zero_of_tests {ι : Type*} {l : Filter ι}
    (μ : ProbabilityMeasure X) (μs : ι → ProbabilityMeasure X) (ξ : ℕ → ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hμs : ∀ i,Integrable (fun x => dist x o^2) (μs i:Measure X))
    (hξ : ∀ n,Integrable (fun x => dist x o^2) (ξ n:Measure X))
    (hT : Tendsto (fun n => quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X)) atTop (𝓝 0))
    (hTs : ∀ n,Tendsto (fun i => quadraticWassersteinSq (μs i:Measure X) (ξ n:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X)))) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) l (𝓝 0) := by
  have hS : Tendsto (fun n => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hT.sqrt
  have hS' : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (μs i:Measure X))) l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n,hn⟩ := (hS.eventually_lt_const (by linarith : (0:ℝ)<ε/4)).exists
    have H := (hTs n).sqrt.eventually_lt_const (show Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ξ n:Measure X)) < ε/2 by linarith)
    filter_upwards [H] with i hi
    have ht := quadraticWassersteinSq_triangle μ (ξ n) (μs i) o hμ (hξ n) (hμs i)
    rw [quadraticWassersteinSq_comm (ξ n:Measure X) (μs i:Measure X)] at ht
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (Real.sqrt_nonneg _)] using (show Real.sqrt (quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) < ε by linarith)
  have H := hS'.pow 2
  have hn (p q : Measure X) : 0 ≤ quadraticWassersteinSq p q := ENNReal.toReal_nonneg
  simpa only [Real.sq_sqrt (hn _ _),zero_pow (by norm_num : (2:ℕ) ≠ 0)] using H

lemma quadraticWassersteinSq_tendsto_pair {ι : Type*} {l : Filter ι}
    (μ ν : ProbabilityMeasure X) (μs νs : ι → ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    (hμs : ∀ i,Integrable (fun x => dist x o^2) (μs i:Measure X))
    (hνs : ∀ i,Integrable (fun x => dist x o^2) (νs i:Measure X))
    (hTμ : Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) l (𝓝 0))
    (hTν : Tendsto (fun i => quadraticWassersteinSq (ν:Measure X) (νs i:Measure X)) l (𝓝 0)) :
    Tendsto (fun i => quadraticWassersteinSq (μs i:Measure X) (νs i:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))) := by
  have hS : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (μs i:Measure X))+
      Real.sqrt (quadraticWassersteinSq (ν:Measure X) (νs i:Measure X))) l (𝓝 0) := by
    simpa only [Real.sqrt_zero,add_zero] using hTμ.sqrt.add hTν.sqrt
  have hpair : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μs i:Measure X) (νs i:Measure X))) l
      (𝓝 (Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X)))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hS.eventually_lt_const hε] with i hi
    have h1 := quadraticWassersteinSq_triangle (μs i) μ (νs i) o (hμs i) hμ (hνs i)
    have h2 := quadraticWassersteinSq_triangle μ ν (νs i) o hμ hν (hνs i)
    have h3 := quadraticWassersteinSq_triangle μ (μs i) ν o hμ (hμs i) hν
    have h4 := quadraticWassersteinSq_triangle (μs i) (νs i) ν o (hμs i) (hνs i) hν
    rw [quadraticWassersteinSq_comm (μs i:Measure X) (μ:Measure X)] at h1
    rw [quadraticWassersteinSq_comm (νs i:Measure X) (ν:Measure X)] at h4
    rw [Real.dist_eq]
    apply lt_of_le_of_lt _ hi
    apply abs_le.mpr
    constructor <;> linarith
  have H := hpair.pow 2
  have hn (p q : Measure X) : 0 ≤ quadraticWassersteinSq p q := ENNReal.toReal_nonneg
  simpa only [Real.sq_sqrt (hn _ _)] using H
end WeakHessian

end
end InlinedFile63

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_LogAddTwoSqrt
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

lemma log_one_add_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1+x) ≤ 2*Real.sqrt x := by
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have H := Real.add_one_le_exp (Real.sqrt x)
  have hp := Real.exp_pos (Real.sqrt x)
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  rw [show 2*Real.sqrt x = Real.sqrt x+Real.sqrt x by ring,Real.exp_add]
  nlinarith [sq_nonneg (Real.exp (Real.sqrt x)-(Real.sqrt x+1))]

lemma renormalizedEntropy_error {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    |renormalizedEntropy a x-reducedEntropy x| ≤ 4*Real.sqrt a*Real.sqrt x := by
  by_cases hz : x = 0
  · simp [hz,renormalizedEntropy,regularizedEntropy_zero,reducedEntropy]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have he : renormalizedEntropy a x-reducedEntropy x =
      x*Real.log (1+a/x)+a*Real.log (1+x/a) := by
    rw [renormalizedEntropy_eq ha hx,reducedEntropy,
      show 1+a/x = (x+a)/x by field_simp,
      show 1+x/a = (x+a)/a by field_simp; ring,
      Real.log_div (by positivity) hxp.ne',Real.log_div (by positivity) ha.ne']
    ring
  have hp : 0 ≤ x*Real.log (1+a/x)+a*Real.log (1+x/a) :=
    add_nonneg (mul_nonneg hx (Real.log_nonneg (by linarith [div_nonneg ha.le hx])))
      (mul_nonneg ha.le (Real.log_nonneg (by linarith [div_nonneg hx ha.le])))
  rw [he,abs_of_nonneg hp]
  have H1 := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt (div_nonneg ha.le hx)) hx
  have H2 := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt (div_nonneg hx ha.le)) ha.le
  have h1 : x*Real.sqrt (a/x) = Real.sqrt a*Real.sqrt x := by
    rw [Real.sqrt_div ha.le,← mul_div_assoc]
    apply (div_eq_iff (Real.sqrt_ne_zero'.mpr hxp)).mpr
    rw [mul_assoc,Real.mul_self_sqrt hx,mul_comm]
  have h2 : a*Real.sqrt (x/a) = Real.sqrt a*Real.sqrt x := by
    rw [Real.sqrt_div hx,← mul_div_assoc]
    apply (div_eq_iff (Real.sqrt_ne_zero'.mpr ha)).mpr
    calc
      a*Real.sqrt x = (Real.sqrt a*Real.sqrt a)*Real.sqrt x := by rw [Real.mul_self_sqrt ha.le]
      _ = _ := by ring
  nlinarith
end WeakHessian
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_reducedEntropy_of_sqrt (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hs : Integrable (fun x => Real.sqrt (u x)) m) :
    Integrable (fun x => reducedEntropy (u x)) m := by
  apply ((regularizedEntropy_integrable (a := 1) zero_lt_one u).norm.add (hs.const_mul 4)).mono'
    ((Real.continuous_mul_log.sub continuous_id).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  filter_upwards [hun] with x hx
  have H := renormalizedEntropy_error (a := 1) zero_lt_one hx
  simp only [Real.sqrt_one,mul_one,renormalizedEntropy,Real.log_one,zero_mul,add_zero] at H
  have H' := abs_sub_comm (regularizedEntropy 1 (u x)) (reducedEntropy (u x))
  simp only [Real.norm_eq_abs,Pi.add_apply]
  calc
    |reducedEntropy (u x)| ≤ |reducedEntropy (u x)-regularizedEntropy 1 (u x)|+
        |regularizedEntropy 1 (u x)| := by simpa only [sub_zero] using abs_sub_le (reducedEntropy (u x)) (regularizedEntropy 1 (u x)) 0
    _ ≤ _ := by rw [← H']; linarith

lemma integral_renormalizedEntropy_error {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    (hs : Integrable (fun x => Real.sqrt (u x)) m) :
    |(∫ x,renormalizedEntropy a (u x) ∂m)-(∫ x,reducedEntropy (u x) ∂m)| ≤
      4*Real.sqrt a*(∫ x,Real.sqrt (u x) ∂m) := by
  rw [← integral_sub (renormalizedEntropy_integrable ha u hi) (integrable_reducedEntropy_of_sqrt u hun hs)]
  calc
    _ ≤ ∫ x,|renormalizedEntropy a (u x)-reducedEntropy (u x)| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ x,4*Real.sqrt a*Real.sqrt (u x) ∂m := by
      apply integral_mono_ae
        ((renormalizedEntropy_integrable ha u hi).sub (integrable_reducedEntropy_of_sqrt u hun hs)).abs
        (hs.const_mul _)
      exact hun.mono (fun x hx => renormalizedEntropy_error ha hx)
    _ = _ := integral_const_mul _ _

lemma tendsto_integral_renormalizedEntropy_Lp {a : ℝ} (ha : 0 < a)
    {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m} (hu : Tendsto us atTop (𝓝 u))
    (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hm : ∀ n,(∫ x,us n x ∂m) = ∫ x,u x ∂m) :
    Tendsto (fun n => ∫ x,renormalizedEntropy a (us n x) ∂m) atTop
      (𝓝 (∫ x,renormalizedEntropy a (u x) ∂m)) := by
  have H := ((regularizedEntropy_hasFDeriv ha u).continuousAt.tendsto.comp hu).add_const
    (Real.log a*(∫ x,u x ∂m))
  have he (v : Lp ℝ 2 m) (hv : Integrable v m) :
      (∫ x,renormalizedEntropy a (v x) ∂m) =
        (∫ x,regularizedEntropy a (v x) ∂m)+Real.log a*(∫ x,v x ∂m) := by
    simp only [renormalizedEntropy]
    rw [integral_add (regularizedEntropy_integrable ha v) (hv.const_mul _),integral_const_mul]
  simpa only [he u hi,he _ (his _),hm,Function.comp_apply] using H

lemma tendsto_integral_reducedEntropy_of_sqrt_bound
    {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m} (hu : Tendsto us atTop (𝓝 u))
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hns : ∀ n,∀ᵐ x ∂m,0 ≤ us n x)
    (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hm : ∀ n,(∫ x,us n x ∂m) = ∫ x,u x ∂m)
    (hs : Integrable (fun x => Real.sqrt (u x)) m)
    (hss : ∀ n,Integrable (fun x => Real.sqrt (us n x)) m)
    {C : ℝ} (hsC : (∫ x,Real.sqrt (u x) ∂m) ≤ C)
    (hssC : ∀ n,(∫ x,Real.sqrt (us n x) ∂m) ≤ C) :
    Tendsto (fun n => ∫ x,reducedEntropy (us n x) ∂m) atTop
      (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  have hlim : Tendsto (fun k => 4*Real.sqrt (fisherEpsilon k)*C) atTop (𝓝 0) := by
    simpa using ((fisherEpsilon_tendsto.sqrt.const_mul 4).mul_const C)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,hk⟩ := (hlim.eventually_lt_const (by linarith : 0 < ε/3)).exists
  have H := tendsto_integral_renormalizedEntropy_Lp (fisherEpsilon_pos k) hu hi his hm
  obtain ⟨n,hn⟩ := Metric.tendsto_atTop.mp H (ε/3) (by linarith)
  refine ⟨n,fun j hj => ?_⟩
  have he0 := (integral_renormalizedEntropy_error (fisherEpsilon_pos k) u hun hi hs).trans
    (mul_le_mul_of_nonneg_left hsC (by positivity))
  have hej := (integral_renormalizedEntropy_error (fisherEpsilon_pos k) (us j) (hns j) (his j) (hss j)).trans
    (mul_le_mul_of_nonneg_left (hssC j) (by positivity))
  have hh := hn j hj
  rw [Real.dist_eq] at hh ⊢
  have he := abs_sub_le (∫ x,reducedEntropy (us j x) ∂m)
    (∫ x,renormalizedEntropy (fisherEpsilon k) (us j x) ∂m)
    (∫ x,reducedEntropy (u x) ∂m)
  have he' := abs_sub_le (∫ x,renormalizedEntropy (fisherEpsilon k) (us j x) ∂m)
    (∫ x,renormalizedEntropy (fisherEpsilon k) (u x) ∂m)
    (∫ x,reducedEntropy (u x) ∂m)
  rw [abs_sub_comm (∫ x,renormalizedEntropy (fisherEpsilon k) (us j x) ∂m)] at hej
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SqrtWeighted
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

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma sqrt_le_weighted {u V : ℝ} (hu : 0 ≤ u) :
    Real.sqrt u ≤ (u*Real.exp (V/2)+Real.exp (-(V/2)))/2 := by
  have hd := Real.exp_pos (-(V/2))
  have heer : (u*Real.exp (V/2))*Real.exp (-(V/2)) = u := by
    rw [mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  apply (mul_le_mul_iff_left₀ hd).mp
  nlinarith [sq_nonneg (Real.sqrt u-Real.exp (-(V/2))),Real.sq_sqrt hu]

lemma integrable_sqrt_weighted {u V : X → ℝ}
    (hu : AEStronglyMeasurable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hw : Integrable (fun x => Real.exp (-(V x/2))) m) :
    Integrable (fun x => Real.sqrt (u x)) m ∧
      (∫ x,Real.sqrt (u x) ∂m) ≤
        (‖hU.toLp (fun x => u x*Real.exp (V x))‖*‖hD.toLp (fun x => Real.exp (-(V x/2)))‖+
          ∫ x,Real.exp (-(V x/2)) ∂m)/2 := by
  have hg : MemLp (fun x => Real.exp (V x/2)*Real.exp (-V x)) 2 m := by
    have he : (fun x => Real.exp (V x/2)*Real.exp (-V x)) = (fun x => Real.exp (-(V x/2))) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [he]
  have H := weighted_pairing hU hg
  have hnorm : ‖hg.toLp (fun x => Real.exp (V x/2)*Real.exp (-V x))‖ =
      ‖hD.toLp (fun x => Real.exp (-(V x/2)))‖ := by
    congr 1
    apply Lp.ext
    filter_upwards [hg.coeFn_toLp,hD.coeFn_toLp] with x hx hy
    rw [hx,hy,← Real.exp_add]
    congr 1
    ring
  rw [hnorm] at H
  have hi : Integrable (fun x => Real.sqrt (u x)) m := by
    apply ((H.1.add hw).div_const 2).mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hu)
    filter_upwards [hun] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Pi.add_apply] using! sqrt_le_weighted (V := V x) hx
  refine ⟨hi,?_⟩
  calc
    (∫ x,Real.sqrt (u x) ∂m) ≤ ∫ x,(u x*Real.exp (V x/2)+Real.exp (-(V x/2)))/2 ∂m :=
      integral_mono_ae hi ((H.1.add hw).div_const 2) (hun.mono fun x hx => sqrt_le_weighted hx)
    _ = ((∫ x,u x*Real.exp (V x/2) ∂m)+(∫ x,Real.exp (-(V x/2)) ∂m))/2 := by
      rw [integral_div,integral_add H.1 hw]
    _ ≤ _ := by
      have HH := (le_abs_self (∫ x,u x*Real.exp (V x/2) ∂m)).trans H.2
      linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile55
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_reducedEntropy_tendsto_weighted {V : X → ℝ}
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hlim : Tendsto us atTop (𝓝 u)) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hns : ∀ n,∀ᵐ x ∂m,0 ≤ us n x) (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hm : ∀ n,(∫ x,us n x ∂m) = ∫ x,u x ∂m)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hUs : ∀ n,MemLp (fun x => us n x*Real.exp (V x)) 2 m)
    {C : ℝ} (hC : ‖hU.toLp _‖ ≤ C) (hCs : ∀ n,‖(hUs n).toLp _‖ ≤ C) :
    Tendsto (fun n => ∫ x,reducedEntropy (us n x) ∂m) atTop (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  have hroot := integrable_sqrt_weighted (Lp.aestronglyMeasurable u) hun hU hhalf hhalfi
  have hroots (n : ℕ) := integrable_sqrt_weighted (Lp.aestronglyMeasurable (us n)) (hns n) (hUs n) hhalf hhalfi
  apply tendsto_integral_reducedEntropy_of_sqrt_bound hlim hun hns hi his hm hroot.1 (fun n => (hroots n).1)
    (C := (C*‖hhalf.toLp _‖+(∫ x,Real.exp (-(V x/2)) ∂m))/2)
  · exact hroot.2.trans (by gcongr)
  · intro n
    exact (hroots n).2.trans (by gcongr; exact hCs n)
end WeakHessian

end
end InlinedFile55

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

end WeakHessian

end
end InlinedFile42

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

end WeakHessian

end
end InlinedFile51

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatEntropyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile66
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_entropy_continuousOn_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hN : 1 < N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (μ : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    {b : ℝ} : ContinuousOn (fun t => entropyReal m (μ t:Measure X)) (Icc 0 b) := by
  have hUt (t : ℝ) (ht : 0 ≤ t) := (hcd.cheegerHeat_weighted hfin o h u hV hU ht).1
  have hn (t : ℝ) (ht : 0 ≤ t) := cheegerHeat_nonneg h ht u hun
  have hit (t : ℝ) (ht : 0 ≤ t) := (cheegerHeat_integrable hfin o h u hi ht).1
  have he (t : ℝ) (ht : 0 ≤ t) : entropyReal m (μ t:Measure X) = (∫ x,reducedEntropy (cheegerHeat h t u x) ∂m)+1 :=
    entropyReal_eq_reducedDensity _ (hn t ht) (hit t ht)
      (integrable_reducedEntropy (Lp.memLp _) (hn t ht) (weighted_pairing (hUt t ht) hD).1 hw) (μ t) (hμ t ht)
  have hc : Continuous (fun t : Icc (0:ℝ) b => cheegerHeat h t u) :=
    continuousOn_iff_continuous_domRestrict.mp ((cheegerHeat_continuousOn hfin h u).mono Icc_subset_Ici_self)
  have hnorm (t : Icc (0:ℝ) b) : ‖(hUt t t.property.1).toLp _‖ ≤ ‖hU.toLp _‖*Real.exp ((L:ℝ)^2*b) :=
    (hcd.cheegerHeat_weighted_norm hfin o h u hV hU t.property.1).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 (sq_nonneg _))) (norm_nonneg _))
  rw [continuousOn_iff_continuous_domRestrict,continuous_iff_seqContinuous]
  intro ts t hts
  change Tendsto (fun n => entropyReal m (μ (ts n):Measure X)) atTop (𝓝 (entropyReal m (μ t:Measure X)))
  simp_rw [he _ (ts _).property.1,he _ t.property.1]
  apply Tendsto.add_const
  exact integral_reducedEntropy_tendsto_weighted hhalf hhalfi ((hc.tendsto t).comp hts)
    (hn t t.property.1) (fun n => hn (ts n) (ts n).property.1)
    (hit t t.property.1) (fun n => hit (ts n) (ts n).property.1)
    (fun n => by rw [(hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi (ts n).property.1).2,
      (hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi t.property.1).2])
    (hUt t t.property.1) (fun n => hUt (ts n) (ts n).property.1) (hnorm t) (fun n => hnorm (ts n))
end WeakHessian

end
end InlinedFile66

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ReweightCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile61
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadraticWassersteinSq_reweight_bound (μ ν : ProbabilityMeasure X) (ρ : Measure X)
    [IsFiniteMeasure ρ] {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hdec : (μ:Measure X) = a • (ν:Measure X)+ρ) (o : X)
    (hρ : Integrable (fun x => dist x o^2) ρ)
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X)) :
    quadraticWassersteinSq (μ:Measure X) (ν:Measure X) ≤
      2*((∫ x,dist x o^2 ∂ρ)+(ρ univ).toReal*(∫ x,dist x o^2 ∂(ν:Measure X))) := by
  let d : X → X×X := fun x => (x,x)
  have hd : Measurable d := measurable_id.prodMk measurable_id
  let q : Measure (X×X) := (a • (ν:Measure X)).map d+ρ.prod (ν:Measure X)
  have hmass : a+ρ univ = 1 := by
    have H := congrArg (fun μ : Measure X => μ univ) hdec
    simpa only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using H.symm
  have hc : IsCoupling q μ ν := by
    constructor
    · dsimp [q]
      rw [Measure.map_add _ _ measurable_fst,Measure.map_map measurable_fst hd]
      simpa only [d,Function.comp_def,Measure.map_id',Measure.map_fst_prod,measure_univ,one_smul] using hdec.symm
    · dsimp [q]
      rw [Measure.map_add _ _ measurable_snd,Measure.map_map measurable_snd hd]
      simp only [d,Function.comp_def,Measure.map_id',Measure.map_snd_prod,← add_smul,hmass,one_smul]
  have hdiag : Integrable (fun p : X×X => dist p.1 p.2^2) ((a • (ν:Measure X)).map d) := by
    apply (integrable_map_measure ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable hd.aemeasurable).mpr
    apply Integrable.smul_measure ?_ ha
    simp [Function.comp_def,d]
  have hbound : Integrable (fun p : X×X => 2*(dist p.1 o^2+dist p.2 o^2)) (ρ.prod (ν:Measure X)) :=
    ((hρ.comp_fst (ν:Measure X)).add (hν.comp_snd ρ)).const_mul 2
  have hle (p : X×X) : dist p.1 p.2^2 ≤ 2*(dist p.1 o^2+dist p.2 o^2) := by
    have H := dist_triangle p.1 o p.2
    rw [dist_comm o p.2] at H
    nlinarith [dist_nonneg (x := p.1) (y := p.2),sq_nonneg (dist p.1 o-dist p.2 o)]
  have hprod : Integrable (fun p : X×X => dist p.1 p.2^2) (ρ.prod (ν:Measure X)) :=
    hbound.mono' ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (dist p.1 p.2))] using hle p)
  have hqi : Integrable (fun p : X×X => dist p.1 p.2^2) q := hdiag.add_measure hprod
  have hqt := cost_ne_top_iff_integrable_sq.mpr hqi
  apply (quadraticWassersteinSq_le_cost hc hqt).trans
  rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  change (∫ p,dist p.1 p.2^2 ∂((a • (ν:Measure X)).map d+ρ.prod (ν:Measure X))) ≤ _
  rw [integral_add_measure hdiag hprod,integral_map hd.aemeasurable ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable]
  simp only [d,dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),integral_zero,zero_add]
  apply (integral_mono hprod hbound hle).trans_eq
  rw [integral_const_mul,integral_add (hρ.comp_fst (ν:Measure X)) (hν.comp_snd ρ)]
  congr 1
  have h1 : (∫ p : X×X,dist p.1 o^2 ∂ρ.prod (ν:Measure X)) = ∫ x,dist x o^2 ∂ρ := by
    simpa using (integral_prod_mul (fun x => dist x o^2) (fun _ : X => (1:ℝ)) (μ := ρ) (ν := (ν:Measure X)))
  have h2 : (∫ p : X×X,dist p.2 o^2 ∂ρ.prod (ν:Measure X)) = (ρ univ).toReal*(∫ x,dist x o^2 ∂(ν:Measure X)) := by
    simpa [measureReal_def] using (integral_prod_mul (fun _ : X => (1:ℝ)) (fun x => dist x o^2) (μ := ρ) (ν := (ν:Measure X)))
  rw [h1,h2]

lemma quadraticWassersteinSq_reweight_tendsto {ι : Type*} {l : Filter ι}
    (μ : ProbabilityMeasure X) (ν : ι → ProbabilityMeasure X) (ρ : ι → Measure X)
    [∀ i, IsFiniteMeasure (ρ i)] (a : ι → ℝ≥0∞) (hat : ∀ i,a i ≠ ∞)
    (hdec : ∀ i,(μ:Measure X) = a i • (ν i:Measure X)+ρ i) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : ∀ i,Integrable (fun x => dist x o^2) (ν i:Measure X))
    (ha : Tendsto (fun i => (a i).toReal) l (𝓝 1))
    (hM : Tendsto (fun i => ∫ x,dist x o^2 ∂(ν i:Measure X)) l (𝓝 (∫ x,dist x o^2 ∂(μ:Measure X)))) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (ν i:Measure X)) l (𝓝 0) := by
  have hρle (i) : ρ i ≤ (μ:Measure X) := by
    rw [hdec i]
    exact Measure.le_add_left le_rfl
  have hρ (i) : Integrable (fun x => dist x o^2) (ρ i) := hμ.mono_measure (hρle i)
  have hmass (i) : (a i).toReal+(ρ i univ).toReal = 1 := by
    have H := congrArg (fun μ : Measure X => μ univ) (hdec i)
    have H' : a i+ρ i univ = 1 := by
      simpa only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using H.symm
    have H'' := congrArg ENNReal.toReal H'
    simpa only [ENNReal.toReal_add (hat i) (measure_ne_top _ _),ENNReal.toReal_one] using H''
  have hmoment (i) : (∫ x,dist x o^2 ∂(μ:Measure X)) =
      (a i).toReal*(∫ x,dist x o^2 ∂(ν i:Measure X))+(∫ x,dist x o^2 ∂ρ i) := by
    conv_lhs => rw [hdec i]
    rw [integral_add_measure ((hν i).smul_measure (hat i)) (hρ i),integral_smul_measure,smul_eq_mul]
  have hR : Tendsto (fun i => (ρ i univ).toReal) l (𝓝 0) := by
    have H := (show Tendsto (fun _ : ι => (1:ℝ)) l (𝓝 1) from tendsto_const_nhds).sub ha
    simp only [sub_self] at H
    exact H.congr (fun i => by linarith [hmass i])
  have hRM : Tendsto (fun i => ∫ x,dist x o^2 ∂ρ i) l (𝓝 0) := by
    have H := (show Tendsto (fun _ : ι => ∫ x,dist x o^2 ∂(μ:Measure X)) l (𝓝 (∫ x,dist x o^2 ∂(μ:Measure X))) from tendsto_const_nhds).sub (ha.mul hM)
    simp only [one_mul,sub_self] at H
    exact H.congr (fun i => by linarith [hmoment i])
  have hB := (hRM.add (hR.mul hM)).const_mul 2
  simp only [zero_mul,zero_add,mul_zero] at hB
  apply squeeze_zero (fun i => ENNReal.toReal_nonneg) (fun i => ?_) hB
  exact quadraticWassersteinSq_reweight_bound μ (ν i) (ρ i) (hat i) (hdec i) o (hρ i) (hν i)

lemma quadraticWassersteinSq_tendsto_of_cost_zero {ι : Type*} {l : Filter ι}
    (μ ν : ProbabilityMeasure X) (νs : ι → ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    (hνs : ∀ i,Integrable (fun x => dist x o^2) (νs i:Measure X))
    (hT : Tendsto (fun i => quadraticWassersteinSq (ν:Measure X) (νs i:Measure X)) l (𝓝 0)) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (νs i:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))) := by
  have hS : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (ν:Measure X) (νs i:Measure X))) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hT.sqrt
  have hSQ : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (νs i:Measure X))) l
      (𝓝 (Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X)))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hS.eventually_lt_const hε] with i hi
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ⟨?_,?_⟩) hi
    · have H := quadraticWassersteinSq_triangle μ (νs i) ν o hμ (hνs i) hν
      rw [quadraticWassersteinSq_comm (νs i:Measure X) (ν:Measure X)] at H
      linarith
    · have H := quadraticWassersteinSq_triangle μ ν (νs i) o hμ hν (hνs i)
      linarith
  have H := hSQ.pow 2
  have hn (p q : Measure X) : 0 ≤ quadraticWassersteinSq p q := ENNReal.toReal_nonneg
  simpa only [Real.sq_sqrt (hn _ _)] using H
end WeakHessian

end
end InlinedFile61

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RadialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile62
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_const_mul {w : X → ℝ} (hw : Measurable w) (c : ℝ) :
    squareDensityMeasure m (fun x => c*w x) = ENNReal.ofReal (c^2) • squareDensityMeasure m w := by
  unfold squareDensityMeasure
  rw [← withDensity_smul _ (hw.pow_const 2 |>.ennreal_ofReal)]
  congr 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_radial_le {w : X → ℝ} (o : X) (n : ℕ) :
    squareDensityMeasure m (fun x => w x*radialCutoff o n x) ≤ squareDensityMeasure m w := by
  apply withDensity_mono
  exact ae_of_all _ fun x => by
    apply ENNReal.ofReal_le_ofReal
    have h1 := radialCutoff_nonneg o n x
    have h2 := radialCutoff_le_one o n x
    have hc : radialCutoff o n x^2 ≤ 1 := by nlinarith
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (sq_nonneg (w x))

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_normalized_radial_support [SigmaFinite m] {w : X → ℝ} (hw : Measurable w)
    (o : X) (n : ℕ) (c : ℝ) :
    (squareDensityMeasure m (fun x => c*(w x*radialCutoff o n x)))
      (Metric.closedBall o ((n:ℝ)+1))ᶜ = 0 := by
  apply ae_iff.mp
  apply squareDensity_ae_support ((hw.mul (radialCutoff_lipschitz o n).continuous.measurable).const_mul c)
  exact ae_of_all _ fun x hx => by
    have hdn : (n:ℝ)+1 ≤ dist x o := (not_le.mp hx).le
    have hz : radialCutoff o n x = 0 := by
      unfold radialCutoff
      rw [max_eq_left]
      exact sub_nonpos.mpr ((le_div_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr (by simpa using hdn))
    change c*(w x*radialCutoff o n x)=0
    simp only [hz,mul_zero]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma squareDensity_normalized_radial_le {w : X → ℝ} (hw : Measurable w)
    (o : X) (n : ℕ) {c : ℝ} (hc : |c| ≤ 2) :
    squareDensityMeasure m (fun x => c*(w x*radialCutoff o n x)) ≤
      (4:ℝ≥0∞) • squareDensityMeasure m w := by
  rw [squareDensity_const_mul (w := fun x => w x*radialCutoff o n x) (hw.mul (radialCutoff_lipschitz o n).continuous.measurable) c]
  apply (_root_.smul_le_smul_left _ (squareDensity_radial_le (m := m) (w := w) o n)).trans
  apply IsOrderedSMul.smul_le_smul_right
  have hs : c^2 ≤ 4 := by nlinarith [sq_abs c,abs_nonneg c]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

omit [ProperSpace X] in
lemma radial_secondMoment_tendsto {w : X → ℝ} (hw : Measurable w) (o : X) (k : ℕ)
    (hM : Integrable (fun x => dist x o^2) (squareDensityMeasure m w)) :
    Tendsto (fun n : ℕ => ∫ x,dist x o^2 ∂squareDensityMeasure m (fun x => w x*radialCutoff o (n+k) x))
      atTop (𝓝 (∫ x,dist x o^2 ∂squareDensityMeasure m w)) := by
  have he (n : ℕ) : (∫ x,dist x o^2 ∂squareDensityMeasure m (fun x => w x*radialCutoff o (n+k) x)) =
      ∫ x,(w x*radialCutoff o (n+k) x)^2*dist x o^2 ∂m :=
    squareDensity_integral (hw.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable) (fun x => dist x o^2)
  simp only [he,squareDensity_integral hw]
  have hi := (squareDensity_integrable hw).mp hM
  apply tendsto_integral_of_dominated_convergence (fun x => w x^2*dist x o^2)
    (fun n => (((hw.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).pow_const 2).mul
      ((measurable_id.dist measurable_const).pow_const 2)).aestronglyMeasurable) hi
  · intro n
    exact ae_of_all _ fun x => by
      change ‖(w x*radialCutoff o (n+k) x)^2*dist x o^2‖ ≤ w x^2*dist x o^2
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),mul_pow]
      have h1 := radialCutoff_nonneg o (n+k) x
      have h2 := radialCutoff_le_one o (n+k) x
      have hc : radialCutoff o (n+k) x^2 ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (w x)) (sq_nonneg (dist x o)),
        mul_le_mul_of_nonneg_left hc (mul_nonneg (sq_nonneg (w x)) (sq_nonneg (dist x o)))]
  · exact ae_of_all _ fun x => by
      have H := ((((radialCutoff_tendsto o x).comp (tendsto_add_atTop_nat k)).const_mul (w x)).pow 2).mul_const (dist x o^2)
      simpa only [mul_one,Function.comp_apply,Pi.mul_apply,id_eq] using H

lemma normalized_radial_cost_tendsto {w : X → ℝ} (hw : Measurable w)
    (μ : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (k : ℕ) {c : ℕ → ℝ} (hc : ∀ n,0 < c n) (hcT : Tendsto c atTop (𝓝 1))
    (ν : ℕ → ProbabilityMeasure X)
    (hν : ∀ n,(ν n:Measure X) = squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)))
    (hM : Integrable (fun x => dist x o^2) (μ:Measure X)) :
    (∀ n,Integrable (fun x => dist x o^2) (ν n:Measure X)) ∧
    Tendsto (fun n => quadraticWassersteinSq (μ:Measure X) (ν n:Measure X)) atTop (𝓝 0) := by
  let σ (n : ℕ) : Measure X := squareDensityMeasure m (fun x => w x*radialCutoff o (n+k) x)
  have hσ (n) : σ n ≤ (μ:Measure X) := by rw [hμ]; exact squareDensity_radial_le o (n+k)
  let (n : ℕ) : IsFiniteMeasure (σ n) := isFiniteMeasure_of_le (μ:Measure X) (hσ n)
  have he (n) : (ν n:Measure X) = ENNReal.ofReal (c n^2) • σ n := by
    rw [hν n]; exact squareDensity_const_mul (hw.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable) (c n)
  have hi (n) : Integrable (fun x => dist x o^2) (ν n:Measure X) := by
    rw [he n]; exact (hM.mono_measure (hσ n)).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hi,?_⟩
  let ρ (n : ℕ) : Measure X := (μ:Measure X)-σ n
  let (n : ℕ) : IsFiniteMeasure (ρ n) := isFiniteMeasure_of_le (μ:Measure X) Measure.sub_le
  let a (n : ℕ) : ℝ≥0∞ := (ENNReal.ofReal (c n^2))⁻¹
  have hc0 (n) : ENNReal.ofReal (c n^2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (hc n))
  have hae (n) : a n • (ν n:Measure X) = σ n := by
    rw [he n,smul_smul]
    simp only [a,ENNReal.inv_mul_cancel (hc0 n) ENNReal.ofReal_ne_top,one_smul]
  apply quadraticWassersteinSq_reweight_tendsto μ ν ρ a
    (fun n => ENNReal.inv_ne_top.mpr (hc0 n)) (fun n => ?_) o hM hi
  · have H := (hcT.pow 2).inv₀ (by norm_num : (1:ℝ)^2 ≠ 0)
    simpa only [a,ENNReal.toReal_inv,ENNReal.toReal_ofReal (sq_nonneg _),one_pow,inv_one] using H
  · have HT := radial_secondMoment_tendsto hw o k (hμ ▸ hM)
    have H := (hcT.pow 2).mul HT
    have eqn (n) : (∫ x,dist x o^2 ∂(ν n:Measure X)) = c n^2*(∫ x,dist x o^2 ∂σ n) := by
      rw [he n,integral_smul_measure,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
    simp_rw [eqn]
    simpa only [hμ,one_pow,one_mul,σ] using H
  · rw [hae n]
    exact (add_comm (σ n) (ρ n)).trans (Measure.sub_add_cancel_of_le (hσ n)) |>.symm
end WeakHessian

end
end InlinedFile62

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile53
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma weighted_absolute_tendsto {ι : Type*} {l : Filter ι} {V W : X → ℝ}
    (hW : MemLp (fun x => W x*Real.exp (-V x)) 2 m) (o : X)
    (hcut : ∀ n,MemLp (fun x => W x*radialCutoff o n x) 2 m)
    {fs : ι → Lp ℝ 2 m} {f : Lp ℝ 2 m} (hlim : Tendsto fs l (𝓝 f))
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hfs : ∀ i,MemLp (fun x => fs i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l,‖(hfs i).toLp _‖ ≤ B) :
    Tendsto (fun i => ∫ x,|fs i x-f x| *W x ∂m) l (𝓝 0) := by
  let gs (i : ι) : Lp ℝ 2 m := (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).compLp norm_zero (fs i-f)
  have he (i : ι) : gs i =ᵐ[m] fun x => |fs i x-f x| := by
    filter_upwards [(lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).coeFn_compLp norm_zero (fs i-f),Lp.coeFn_sub (fs i) f] with x hx hy
    simpa only [gs,Function.comp_apply,hy,Pi.sub_apply,Real.norm_eq_abs] using hx
  have hg : Tendsto gs l (𝓝 (0:Lp ℝ 2 m)) := by
    have H := ((lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).continuous_compLp (p := (2:ℝ≥0∞)) (μ := m) norm_zero).continuousAt.tendsto.comp (hlim.sub (tendsto_const_nhds (x := f)))
    simpa only [gs,Function.comp_def,sub_self,LipschitzWith.compLp_zero] using H
  have hgw (i : ι) : MemLp (fun x => gs i x*Real.exp (V x)) 2 m := by
    apply MemLp.ae_eq (hf_Lp := ((hfs i).sub hf).norm)
    filter_upwards [he i] with x hx
    simp only [Pi.sub_apply,Real.norm_eq_abs,hx]
    rw [← sub_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hn (i : ι) : ‖(hgw i).toLp _‖ ≤ ‖(hfs i).toLp _‖+‖hf.toLp _‖ := by
    have hid : ‖(hgw i).toLp _‖ ≤ ‖(hfs i).toLp _-hf.toLp _‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hgw i).coeFn_toLp,(hfs i).coeFn_toLp,hf.coeFn_toLp,he i,Lp.coeFn_sub ((hfs i).toLp _) (hf.toLp _)] with x ha hb hc hd he'
      simp only [ha,he',Pi.sub_apply,hb,hc,hd,Real.norm_eq_abs,← sub_mul,abs_mul,abs_abs,abs_of_pos (Real.exp_pos _),le_refl]
    exact hid.trans (norm_sub_le _ _)
  have hz : MemLp (fun x => (0:Lp ℝ 2 m) x*Real.exp (V x)) 2 m := by
    exact MemLp.ae_eq (hf_Lp := MemLp.zero) (by filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx; simp only [Pi.zero_apply,hx,zero_mul])
  have H := weighted_pairing_tendsto hW o hcut hg hz hgw (B := B+‖hf.toLp _‖)
    (hB.mono fun i hi => (hn i).trans (add_le_add hi le_rfl))
  have hzi : (∫ x,(0:Lp ℝ 2 m) x*W x ∂m) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
    simp only [hx,Pi.zero_apply,zero_mul]
  rw [hzi] at H
  exact H.congr (fun i => integral_congr_ae ((he i).mono fun x hx => by rw [hx]))
end WeakHessian

end
end InlinedFile53

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CostContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile54
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma weighted_abs_sub_memLp {u v V : X → ℝ}
    (hu : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hv : MemLp (fun x => v x*Real.exp (V x)) 2 m) :
    MemLp (fun x => |u x-v x| * Real.exp (V x)) 2 m := by
  apply MemLp.ae_eq (hf_Lp := (hu.sub hv).norm)
  exact ae_of_all _ fun x => by
    simp only [Pi.sub_apply,Real.norm_eq_abs,← sub_mul,abs_mul,abs_of_pos (Real.exp_pos _)]

lemma CurvatureDimension.cost_variation_density {K N : ℝ} (hcd : CurvatureDimension m K N)
    (o : X) (T : ℝ≥0) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hui : Integrable u m) (hvi : Integrable v m)
    (μ ξ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hξ : (ξ:Measure X) = densityMeasure m v)
    (hn : (ν:Measure X) ≪ m) (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {V : X → ℝ} (hVm : Measurable V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    |quadraticWassersteinSq (μ:Measure X) (ν:Measure X)-quadraticWassersteinSq (ξ:Measure X) (ν:Measure X)| ≤
      2*(∫ x,|u x-v x| * (dist x o+T)^2 ∂m) := by
  have one (u v : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
      (hui : Integrable u m) (hvi : Integrable v m)
      (μ ξ : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
      (hξ : (ξ:Measure X) = densityMeasure m v)
      (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
      (hV : MemLp (fun x => v x*Real.exp (V x)) 2 m) :
      quadraticWassersteinSq (μ:Measure X) (ν:Measure X)-quadraticWassersteinSq (ξ:Measure X) (ν:Measure X) ≤
        2*(∫ x,|u x-v x| * (dist x o+T)^2 ∂m) := by
    obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar⟩ := hcd.density_cost_support o T u hun hui μ ν hμ hn hsν hU hW
    obtain ⟨q',ψ,hq'p,hq'o,hq't,_⟩ := hcd.density_cost_support o T v hvn hvi ξ ν hξ hn hsν hV hW
    have hvW : Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) := by
      rw [hξ]; exact densityMeasure_quadratic_integrable o T v hvn hV hW
    have H := hvar ξ hvW q' hq'o.1 hq't
    rw [← hqo.quadraticWassersteinSq_eq,← hq'o.quadraticWassersteinSq_eq,hμ,hξ,
      integral_densityMeasure m _ hun,integral_densityMeasure m _ hvn] at H
    rw [← hμ,← hξ] at H
    have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hVm hW
    have hprod := (weighted_pairing (weighted_abs_sub_memLp hU hV) hW).1
    have hiu := (weighted_pairing hU hφW).1
    have hiv := (weighted_pairing hV hφW).1
    have H' : (∫ x,u x*φ x ∂m)-(∫ x,v x*φ x ∂m) ≤
        ∫ x,|u x-v x| * (dist x o+T)^2 ∂m := by
      rw [← integral_sub hiu hiv]
      apply integral_mono_ae (hiu.sub hiv) hprod
      exact ae_of_all _ fun x => by
        simp only [Pi.sub_apply,← sub_mul]
        calc
          _ ≤ |(u x-v x)*φ x| := le_abs_self _
          _ = |u x-v x| * |φ x| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hφ.centered_bound T.coe_nonneg hφ0 x) (abs_nonneg _)
    exact H.trans (mul_le_mul_of_nonneg_left H' (by norm_num))
  apply abs_le.mpr
  refine ⟨?_,one u v hun hvn hui hvi μ ξ hμ hξ hU hV⟩
  have H := one v u hvn hun hvi hui ξ μ hξ hμ hV hU
  simp_rw [abs_sub_comm (v _) (u _)] at H
  linarith

lemma CurvatureDimension.cost_tendsto_density {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) (T : ℝ≥0)
    {ι : Type*} {l : Filter ι} {us : ι → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hlim : Tendsto us l (𝓝 u)) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (husn : ∀ i,∀ᵐ x ∂m,0 ≤ us i x) (hui : Integrable u m) (husi : ∀ i,Integrable (us i) m)
    (μ : ProbabilityMeasure X) (μs : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hμ : (μ:Measure X) = densityMeasure m u) (hμs : ∀ i,(μs i:Measure X) = densityMeasure m (us i))
    (hn : (ν:Measure X) ≪ m) (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {V : X → ℝ} (hVm : Measurable V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hUs : ∀ i,MemLp (fun x => us i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l,‖(hUs i).toLp _‖ ≤ B)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    Tendsto (fun i => quadraticWassersteinSq (μs i:Measure X) (ν:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfin _ Metric.isBounded_ball⟩⟩
  have hcut (n : ℕ) : MemLp (fun x => (dist x o+T)^2*radialCutoff o n x) 2 m :=
    ((by fun_prop : Continuous (fun x => (dist x o+T)^2)).mul (radialCutoff_lipschitz o n).continuous).memLp_of_hasCompactSupport
      ((radialCutoff_compact o n).mul_left)
  have H : Tendsto (fun i => 2*(∫ x,|us i x-u x| * (dist x o+T)^2 ∂m)) l (𝓝 0) := by
    simpa only [mul_zero] using (weighted_absolute_tendsto hW o hcut hlim hU hUs hB).const_mul 2
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [H.eventually_lt_const hε] with i hi
  simp only [dist_eq_norm,Real.norm_eq_abs]
  exact (hcd.cost_variation_density o T (us i) u (husn i) hun (husi i) hui (μs i) μ ν (hμs i) hμ hn hsν
    hVm (hUs i) hU hW).trans_lt hi
end WeakHessian

end
end InlinedFile54

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TargetEVI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile68
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma intervalIntegral_exp_entropy_tendsto {K b : ℝ} (hb : 0 ≤ b) {E : ℝ → ℝ}
    (hE : ContinuousOn E (Icc 0 b)) {ι : Type*} {l : Filter ι} {c : ι → ℝ} {c0 : ℝ}
    (hc : Tendsto c l (𝓝 c0)) :
    Tendsto (fun i => ∫ t in 0..b,Real.exp (K*t)*(c i-E t)) l
      (𝓝 (∫ t in 0..b,Real.exp (K*t)*(c0-E t))) := by
  have heI : IntervalIntegrable (fun t : ℝ => Real.exp (K*t)) volume 0 b := (by fun_prop : Continuous (fun t : ℝ => Real.exp (K*t))).intervalIntegrable _ _
  have hEI : IntervalIntegrable (fun t : ℝ => Real.exp (K*t)*E t) volume 0 b :=
    ((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (K*t)) (Icc 0 b)).mul hE).intervalIntegrable_of_Icc hb
  have heq (z : ℝ) : (∫ t in 0..b,Real.exp (K*t)*(z-E t)) =
      z*(∫ t in 0..b,Real.exp (K*t))-(∫ t in 0..b,Real.exp (K*t)*E t) := by
    have hf : (fun t : ℝ => Real.exp (K*t)*(z-E t)) = fun t => z*Real.exp (K*t)-Real.exp (K*t)*E t := by funext t; ring
    rw [hf,intervalIntegral.integral_sub (heI.const_mul z) hEI,intervalIntegral.integral_const_mul]
  simp_rw [heq]
  exact (hc.mul_const _).sub_const _

lemma RCD.cheegerHeat_comparison_weighted_target {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,|u x| ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (w : X → ℝ) (hw : MemLp w 2 m) (hwm : Measurable w)
    (hν : (ν:Measure X) = squareDensityMeasure m w)
    (hνE : FiniteEntropy m (ν:Measure X))
    (hνM : Integrable (fun x => dist x o^2) (ν:Measure X))
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  have hUt (t : ℝ) (ht : 0 ≤ t) := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ht).1
  have hμM (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => dist x o^2) (μ t:Measure X) := by
    rw [hμ t ht]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 (cheegerHeat h t u)
      (cheegerHeat_nonneg h ht u hun) (hUt t ht) (hW 0).1
  have hEc := hrcd.1.cheegerHeat_entropy_continuousOn_weighted hN hfull hfin o h u hun
    (integrable_of_integral_eq_one hmass) hV hU hD hdecayi hhalf hhalfi μ hμ (b := b)
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hν ▸ inferInstance
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw hwm o
  let νs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (fun x => c n*(w x*radialCutoff o (n+k) x)) (hp n)
  have hνs (n : ℕ) : (νs n:Measure X) = squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)) := rfl
  have hMC := normalized_radial_cost_tendsto hwm ν hν o k (fun n => (hc n).1) hcT νs hνs hνM
  have hET := normalized_radial_entropy_tendsto hw hwm (hν ▸ hνE) o k
    (fun n => ⟨(hc n).1.le,(hc n).2⟩) hcT hp
  have hET' : Tendsto (fun n => entropyReal m (νs n:Measure X)) atTop (𝓝 (entropyReal m (ν:Measure X))) := by
    simpa only [hνs,hν] using hET.2
  have hcost (t : ℝ) (ht : 0 ≤ t) := quadraticWassersteinSq_tendsto_of_cost_zero (μ t) ν νs o (hμM t ht) hνM hMC.1 hMC.2
  have hleft := (((hcost b hb).const_mul (Real.exp (K*b))).sub (hcost 0 le_rfl)).div_const 2
  have hright := intervalIntegral_exp_entropy_tendsto hb hEc (K := K) hET'
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  let T : ℝ≥0 := (n+k:ℕ)+1
  have hT : 0 < T := by dsimp [T]; positivity
  have hsν : (νs n:Measure X) (Metric.closedBall o T)ᶜ = 0 := by
    rw [hνs n]
    simpa only [T,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using squareDensity_normalized_radial_support hwm o (n+k) (c n)
  have hd : (νs n:Measure X) ≤ ((4:ℝ≥0∞)*C) • m := by
    rw [hνs n]
    apply (squareDensity_normalized_radial_le hwm o (n+k) (by rw [abs_of_pos (hc n).1]; exact (hc n).2)).trans
    rw [← hν,← smul_smul]
    exact _root_.smul_le_smul_left _ hdν
  exact hrcd.cheegerHeat_comparison_weighted hN hfull hfin o h u hun hmass hB huB hV hU
    hdecay hD hdecayi hhalf hhalfi μ hμ (νs n) T hT hsν
    (ENNReal.mul_ne_top (by norm_num) hCt) hd (hW T).1 (hW T).2 hb
end WeakHessian

end
end InlinedFile68

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

lemma RCD.cheegerHeat_comparison_shift {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hU' : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ (a+b):Measure X) (ν c:Measure X)-
      quadraticWassersteinSq (μ a:Measure X) (ν c:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν c:Measure X)-entropyReal m (μ (a+t):Measure X)) := by
  have hui := integrable_of_integral_eq_one hum
  have hvi := integrable_of_integral_eq_one hvm
  have hua := cheegerHeat_nonneg h ha u hun
  have hvc := cheegerHeat_nonneg h hc v hvn
  have hvcI := (cheegerHeat_integrable hfin o h v hvi hc).1
  have hUa := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ha).1
  have hUc := (hrcd.1.cheegerHeat_weighted hfin o h v hV hU' hc).1
  have hum' : ∫ x,cheegerHeat h a u x ∂m = 1 :=
    (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hui ha).2.trans hum
  have hμ' (t : ℝ) (ht : 0 ≤ t) :
      (μ (a+t):Measure X) = densityMeasure m (cheegerHeat h t (cheegerHeat h a u)) := by
    rw [hμ _ (add_nonneg ha ht),add_comm a t,cheegerHeat_add h ht ha]
    rfl
  let : IsProbabilityMeasure (densityMeasure m (cheegerHeat h c v)) := hν c hc ▸ inferInstance
  have hνE : FiniteEntropy m (ν c:Measure X) := by
    rw [hν c hc]
    exact densityMeasure_finiteEntropy _ hvc hvcI (weighted_pairing hUc hD).1 hdecayi
  have hνM : Integrable (fun x => dist x o^2) (ν c:Measure X) := by
    rw [hν c hc]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _ hvc hUc (hW 0).1
  have hdν : (ν c:Measure X) ≤ ENNReal.ofReal C • m := by
    rw [hν c hc]
    exact densityMeasure_le_const ((cheegerHeat_bounded h hc hC v hvC).mono fun _ hx => (le_abs_self _).trans hx)
  have H := hrcd.cheegerHeat_comparison_weighted_target hN hfull hfin o h (cheegerHeat h a u)
    hua hum' hB (cheegerHeat_bounded h ha hB u huB) hV hUa hdecay hD hdecayi hhalf hhalfi hW
    (fun t => μ (a+t)) hμ' (ν c) (fun x => Real.sqrt (cheegerHeat h c v x))
    (densityMeasure_sqrt_memLp _ hvc hvcI) (Lp.stronglyMeasurable _ |>.measurable.sqrt)
    ((hν c hc).trans (densityMeasure_eq_square_sqrt _ hvc)) hνE hνM ENNReal.ofReal_ne_top hdν hb
  simpa only [add_zero] using H
end WeakHessian

end
end InlinedFile69

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatCostTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile70
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma CurvatureDimension.cost_zero_tendsto_density {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (o : X)
    {ι : Type*} {l : Filter ι} {us : ι → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hlim : Tendsto us l (𝓝 u)) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (husn : ∀ i,∀ᵐ x ∂m,0 ≤ us i x) (hui : Integrable u m) (husi : ∀ i,Integrable (us i) m)
    (μ : ProbabilityMeasure X) (μs : ι → ProbabilityMeasure X)
    (hμ : (μ:Measure X) = densityMeasure m u) (hμs : ∀ i,(μs i:Measure X) = densityMeasure m (us i))
    {V : X → ℝ} (hVm : Measurable V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hUs : ∀ i,MemLp (fun x => us i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l,‖(hUs i).toLp _‖ ≤ B)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) l (𝓝 0) := by
  let w : X → ℝ := fun x => Real.sqrt (u x)
  have hw : MemLp w 2 m := densityMeasure_sqrt_memLp u hun hui
  have hwm : Measurable w := Lp.stronglyMeasurable u |>.measurable.sqrt
  have hroot : (μ:Measure X) = squareDensityMeasure m w := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hroot ▸ inferInstance
  have hM : Integrable (fun x => dist x o^2) (μ:Measure X) := by
    rw [hμ]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 u hun hU (hW 0)
  have hMs (i) : Integrable (fun x => dist x o^2) (μs i:Measure X) := by
    rw [hμs i]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 (us i) (husn i) (hUs i) (hW 0)
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw hwm o
  let ξ (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (fun x => c n*(w x*radialCutoff o (n+k) x)) (hp n)
  have hξ (n : ℕ) : (ξ n:Measure X) = squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)) := rfl
  have hMC := normalized_radial_cost_tendsto hwm μ hroot o k (fun n => (hc n).1) hcT ξ hξ hM
  apply quadraticWassersteinSq_tendsto_zero_of_tests μ μs ξ o hM hMs hMC.1 hMC.2
  intro n
  let T : ℝ≥0 := (n+k:ℕ)+1
  have hsξ : (ξ n:Measure X) (Metric.closedBall o T)ᶜ = 0 := by
    rw [hξ n]
    simpa only [T,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using squareDensity_normalized_radial_support hwm o (n+k) (c n)
  have hξm : (ξ n:Measure X) ≪ m := withDensity_absolutelyContinuous _ _
  exact hcd.cost_tendsto_density hfin o T hlim hun husn hui husi μ μs (ξ n) hμ hμs hξm hsξ hVm hU hUs hB (hW T)

lemma CurvatureDimension.cheegerHeat_cost_zero_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hui : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : ∀ T : ℝ≥0,MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    {ι : Type*} {l : Filter ι} {ts : ι → ℝ} {t : ℝ}
    (hts : ∀ i,0 ≤ ts i) (ht : 0 ≤ t) (hT : Tendsto ts l (𝓝 t)) :
    Tendsto (fun i => quadraticWassersteinSq (μ t:Measure X) (μ (ts i):Measure X)) l (𝓝 0) := by
  have hUt (s : ℝ) (hs : 0 ≤ s) := (hcd.cheegerHeat_weighted hfin o h u hV hU hs).1
  have hlim : Tendsto (fun i => cheegerHeat h (ts i) u) l (𝓝 (cheegerHeat h t u)) :=
    (cheegerHeat_continuousOn hfin h u t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hT,Eventually.of_forall hts⟩)
  apply hcd.cost_zero_tendsto_density hfin o hlim (cheegerHeat_nonneg h ht u hun)
    (fun i => cheegerHeat_nonneg h (hts i) u hun) (cheegerHeat_integrable hfin o h u hui ht).1
    (fun i => (cheegerHeat_integrable hfin o h u hui (hts i)).1) (μ t) (fun i => μ (ts i))
    (hμ t ht) (fun i => hμ (ts i) (hts i)) hV.continuous.measurable (hUt t ht)
    (fun i => hUt (ts i) (hts i)) (B := ‖hU.toLp _‖*Real.exp ((L:ℝ)^2*(t+1))) _ hW
  filter_upwards [hT.eventually_le_const (by linarith : t < t+1)] with i hi
  exact (hcd.cheegerHeat_weighted_norm hfin o h u hV hU (hts i)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi (sq_nonneg _))) (norm_nonneg _))
end WeakHessian

end
end InlinedFile70

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EVICalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile71
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma exp_integral_average_tendsto {E : ℝ → ℝ} (hE : Continuous E) (K x : ℝ) :
    Tendsto (fun h : ℝ => (∫ s in 0..h,Real.exp (K*s)*E (x+s))/h)
      (𝓝[>] 0) (𝓝 (E x)) := by
  have hc : Continuous (fun s : ℝ => Real.exp (K*s)*E (x+s)) := by fun_prop
  have H := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,smul_eq_mul,div_eq_mul_inv,
    mul_zero,Real.exp_zero,one_mul,mul_one,add_zero,mul_comm] using H

lemma exp_entropy_average_identity {E : ℝ → ℝ} (hE : Continuous E) (K x z h : ℝ) :
    (∫ s in 0..h,Real.exp (K*s)*(z-E (x+s)))/h =
      z*((∫ s in 0..h,Real.exp (K*s))/h)-(∫ s in 0..h,Real.exp (K*s)*E (x+s))/h := by
  have hf : (fun s : ℝ => Real.exp (K*s)*(z-E (x+s))) =
      fun s => z*Real.exp (K*s)-Real.exp (K*s)*E (x+s) := by funext s; ring
  rw [hf,intervalIntegral.integral_sub ((by fun_prop : Continuous (fun s : ℝ => Real.exp (K*s))).intervalIntegrable _ _ |>.const_mul z)
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (K*s)*E (x+s))).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  ring

lemma evi_error_ratio_tendsto {E F : ℝ → ℝ} (hE : Continuous E) (hF : Continuous F) (K x : ℝ) :
    Tendsto (fun h : ℝ => 2*Real.exp (2*K*x)*
      (Real.exp (K*h)*((∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))/h)+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))/h)) (𝓝[>] 0) (𝓝 0) := by
  have hA : Tendsto (fun h : ℝ => (∫ s in 0..h,Real.exp (K*s))/h) (𝓝[>] 0) (𝓝 1) := by
    simpa only [mul_one] using exp_integral_average_tendsto (E := fun _ => (1:ℝ)) continuous_const K x
  have hFt : Tendsto (fun h : ℝ => F (x+h)) (𝓝[>] 0) (𝓝 (F x)) := by
    simpa only [add_zero] using ((by fun_prop : Continuous (fun h : ℝ => F (x+h))).tendsto 0).mono_left nhdsWithin_le_nhds
  have hExp : Tendsto (fun h : ℝ => Real.exp (K*h)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [mul_zero,Real.exp_zero] using ((by fun_prop : Continuous (fun h : ℝ => Real.exp (K*h))).tendsto 0).mono_left nhdsWithin_le_nhds
  simp_rw [exp_entropy_average_identity hE,exp_entropy_average_identity hF]
  have H := ((hExp.mul ((hFt.mul hA).sub (exp_integral_average_tendsto hE K x))).add
    ((hA.const_mul (E x)).sub (exp_integral_average_tendsto hF K x))).const_mul (2*Real.exp (2*K*x))
  simpa only [mul_one,one_mul,sub_add_sub_cancel,sub_self,mul_zero] using H

lemma evi_rectangle {D : ℝ → ℝ → ℝ} {E F : ℝ → ℝ} {K x h : ℝ}
    (h1 : (Real.exp (K*h)*D (x+h) (x+h)-D x (x+h))/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))
    (h2 : (Real.exp (K*h)*D x (x+h)-D x x)/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s))) (hh : 0 < h) :
    (Real.exp (2*K*(x+h))*D (x+h) (x+h)-Real.exp (2*K*x)*D x x)/h ≤
      2*Real.exp (2*K*x)*(Real.exp (K*h)*((∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))/h)+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))/h) := by
  have he : Real.exp (2*K*(x+h)) = Real.exp (2*K*x)*(Real.exp (K*h)*Real.exp (K*h)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [he]
  have H := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (K*h)).le
  have H' : (Real.exp (K*h)*Real.exp (K*h))*D (x+h) (x+h)-D x x ≤
      2*(Real.exp (K*h)*(∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))) := by nlinarith
  have H'' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left H' (Real.exp_pos (2*K*x)).le) hh.le
  calc
    _ = Real.exp (2*K*x)*((Real.exp (K*h)*Real.exp (K*h))*D (x+h) (x+h)-D x x)/h := by ring
    _ ≤ Real.exp (2*K*x)*(2*(Real.exp (K*h)*(∫ s in 0..h,Real.exp (K*s)*(F (x+h)-E (x+s)))+
        (∫ s in 0..h,Real.exp (K*s)*(E x-F (x+s)))))/h := H''
    _ = _ := by ring
end WeakHessian

end
end InlinedFile71

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_EVIContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile72
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma evi_doubling_contraction {D : ℝ → ℝ → ℝ} {E F : ℝ → ℝ} {K b : ℝ}
    (hE : Continuous E) (hF : Continuous F) (hb : 0 ≤ b)
    (hDc : ContinuousOn (fun t => D t t) (Icc 0 b))
    (h1 : ∀ x h r : ℝ,0 ≤ x → 0 ≤ h → 0 ≤ r →
      (Real.exp (K*h)*D (x+h) r-D x r)/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(F r-E (x+s)))
    (h2 : ∀ x h r : ℝ,0 ≤ x → 0 ≤ h → 0 ≤ r →
      (Real.exp (K*h)*D r (x+h)-D r x)/2 ≤
      ∫ s in 0..h,Real.exp (K*s)*(E r-F (x+s))) :
    Real.exp (2*K*b)*D b b ≤ D 0 0 := by
  let g : ℝ → ℝ := fun t => Real.exp (2*K*t)*D t t
  have hgc : ContinuousOn g (Icc 0 b) := (by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (2*K*t)) (Icc 0 b)).mul hDc
  apply image_le_of_liminf_slope_right_le_deriv_boundary (f := g) (B := fun _ => D 0 0) (B' := fun _ => 0) hgc
    (by simp [g]) continuousOn_const (fun x _ => (hasDerivAt_const x (D 0 0)).hasDerivWithinAt) _ ⟨hb,le_rfl⟩
  intro x hx r hr
  have hsub : Tendsto (fun z : ℝ => z-x) (𝓝[>] x) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using ((by fun_prop : Continuous (fun z : ℝ => z-x)).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (show x < z from hz)
  have hR := (evi_error_ratio_tendsto hE hF K x).comp hsub
  apply Filter.Eventually.frequently
  filter_upwards [hR.eventually_lt_const hr,self_mem_nhdsWithin] with z hz hxz
  have hh : 0 < z-x := sub_pos.mpr hxz
  have H := evi_rectangle (h1 x (z-x) (x+(z-x)) hx.1 hh.le (add_nonneg hx.1 hh.le))
    (h2 x (z-x) x hx.1 hh.le hx.1) hh
  rw [slope_def_field]
  have Hg : (g z-g x)/(z-x) ≤ 2*Real.exp (2*K*x)*
      (Real.exp (K*(z-x))*((∫ s in 0..z-x,Real.exp (K*s)*(F (x+(z-x))-E (x+s)))/(z-x))+
        (∫ s in 0..z-x,Real.exp (K*s)*(E x-F (x+s)))/(z-x)) := by
    simpa only [g,add_sub_cancel] using H
  exact Hg.trans_lt hz
end WeakHessian

end
end InlinedFile72

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile73
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

lemma continuous_max_zero_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ∀ b : ℝ, ContinuousOn f (Icc 0 b)) : Continuous (fun t => f (max t 0)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : Continuous (fun t : ℝ => max t 0) := by fun_prop
  have ht : Tendsto (fun t : ℝ => max t 0) (𝓝 x) (𝓝 (max x 0)) := hc.tendsto x
  apply (hf (max x 0+1) (max x 0) ⟨le_max_right _ _,by linarith⟩).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨ht,?_⟩
  filter_upwards [ht.eventually_le_const (by linarith : max x 0 < max x 0+1)] with y hy
  exact ⟨le_max_right _ _,hy⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_contraction_weighted_oai {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hU' : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (2*K*b)*quadraticWassersteinSq (μ b:Measure X) (ν b:Measure X) ≤
      quadraticWassersteinSq (μ 0:Measure X) (ν 0:Measure X) := by
  have hui := integrable_of_integral_eq_one hum
  have hvi := integrable_of_integral_eq_one hvm
  have hE := continuous_max_zero_of_continuousOn_Icc (fun b =>
    hrcd.1.cheegerHeat_entropy_continuousOn_weighted hN hfull hfin o h u hun hui hV hU hD hdecayi hhalf hhalfi μ hμ (b := b))
  have hF := continuous_max_zero_of_continuousOn_Icc (fun b =>
    hrcd.1.cheegerHeat_entropy_continuousOn_weighted hN hfull hfin o h v hvn hvi hV hU' hD hdecayi hhalf hhalfi ν hν (b := b))
  have hM (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => dist x o^2) (μ t:Measure X) := by
    rw [hμ t ht]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _
      (cheegerHeat_nonneg h ht u hun) (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ht).1 (hW 0).1
  have hM' (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => dist x o^2) (ν t:Measure X) := by
    rw [hν t ht]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _
      (cheegerHeat_nonneg h ht v hvn) (hrcd.1.cheegerHeat_weighted hfin o h v hV hU' ht).1 (hW 0).1
  have hDc : ContinuousOn (fun t => quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X)) (Icc 0 b) := by
    rw [continuousOn_iff_continuous_domRestrict,continuous_iff_seqContinuous]
    intro ts t ht
    have hT : Tendsto (fun n => (ts n:ℝ)) atTop (𝓝 (t:ℝ)) := (continuous_subtype_val.tendsto t).comp ht
    exact quadraticWassersteinSq_tendsto_pair (μ t) (ν t) (fun n => μ (ts n)) (fun n => ν (ts n)) o
      (hM t t.property.1) (hM' t t.property.1) (fun n => hM (ts n) (ts n).property.1) (fun n => hM' (ts n) (ts n).property.1)
      (hrcd.1.cheegerHeat_cost_zero_tendsto hfin o h u hun hui hV hU (fun T => (hW T).1) μ hμ
        (fun n => (ts n).property.1) t.property.1 hT)
      (hrcd.1.cheegerHeat_cost_zero_tendsto hfin o h v hvn hvi hV hU' (fun T => (hW T).1) ν hν
        (fun n => (ts n).property.1) t.property.1 hT)
  apply evi_doubling_contraction (D := fun s t => quadraticWassersteinSq (μ s:Measure X) (ν t:Measure X)) (K := K) hE hF hb hDc
  · intro x s r hx hs hr
    have H := hrcd.cheegerHeat_comparison_shift hN hfull hfin o h u v hun hvn hum hvm hB hC huB hvC
      hV hU hU' hdecay hD hdecayi hhalf hhalfi hW μ ν hμ hν hx hs hr
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht0 : 0 ≤ t := (uIcc_of_le hs ▸ ht).1
    rw [max_eq_left hr,max_eq_left (add_nonneg hx ht0)]
  · intro x s r hx hs hr
    have H := hrcd.cheegerHeat_comparison_shift hN hfull hfin o h v u hvn hun hvm hum hC hB hvC huB
      hV hU' hU hdecay hD hdecayi hhalf hhalfi hW ν μ hν hμ hx hs hr
    simp_rw [quadraticWassersteinSq_comm (ν _:Measure X) (μ _:Measure X)] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht0 : 0 ≤ t := (uIcc_of_le hs ▸ ht).1
    rw [max_eq_left hr,max_eq_left (add_nonneg hx ht0)]
end WeakHessian

end
end InlinedFile73

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted_oai.{u_1} := @OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted_oai.{u_1}
