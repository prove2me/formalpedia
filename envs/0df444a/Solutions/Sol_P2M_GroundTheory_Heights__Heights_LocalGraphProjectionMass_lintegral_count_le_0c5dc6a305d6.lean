-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphProjectionMass_lintegral_count_le_0c5dc6a305d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:03.234288+00:00
-- url     : https://prove2.me/submissions/2d1729df-7303-4f4b-a7b7-a33e94abc363

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphProjectionMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphProjectionMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphProjectionMass
theorem _root_.solution (U : Matrix (Fin n) (Fin n) ℂ)
    (c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hc : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (c i) z = ∑ j, U i j * z j)
    {d : ℕ} (I : Finset (Fin n)) (hI : I.card = d) (A : Set (EuclideanSpace ℂ (Fin n))) :
    ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) ≤
      (⨆ y : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ A ∧ rowsProj U (I.orderEmbOfFin hI) z = y}.encard : ℕ∞) : ℝ≥0∞)) *
        μH[((2 * d : ℕ) : ℝ)] (rowsProj U (I.orderEmbOfFin hI) '' A) := by
  set e := I.orderIsoOfFin hI
  set s : Fin d → Fin n := ⇑(I.orderEmbOfFin hI) with hs
  let φ : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.toEquiv.symm
  have hφ : ∀ x k, φ x k = x (e k) := fun x k => rfl
  have hrow : ∀ z k, rowsProj U s z k = inner ℂ (c (e k)) z := by
    intro z k
    rw [hc]
    simp [rowsProj, Matrix.mulVec, dotProduct, s, e, Finset.coe_orderIsoOfFin_apply]
  have hiff : ∀ x z, frameProj c I z = WithLp.ofLp x ↔ rowsProj U s z = φ x := by
    intro x z
    constructor
    · intro h
      ext k
      rw [hrow, hφ]
      exact congrFun h (e k)
    · intro h
      funext i
      have := congrArg (fun y : EuclideanSpace ℂ (Fin d) => y (e.symm i)) h
      simp only [hrow, hφ, OrderIso.apply_symm_apply] at this
      exact this
  set T := rowsProj U s '' A
  set N := ⨆ y : EuclideanSpace ℂ (Fin d), (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)
  have hle : ∀ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ≤
      (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x := by
    intro x
    have hset : {z ∈ A | frameProj c I z = WithLp.ofLp x} = {z | z ∈ A ∧ rowsProj U s z = φ x} := by
      ext z
      exact and_congr Iff.rfl (hiff x z)
    by_cases hx : φ x ∈ T
    · rw [Set.indicator_of_mem (show x ∈ φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T from
        subset_toMeasurable _ T hx)]
      simp only [frameFibreCount]
      rw [hset]
      exact le_iSup (fun y => (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)) (φ x)
    · have h0 : {z ∈ A | frameProj c I z = WithLp.ofLp x} = ∅ := by
        rw [hset]
        exact Set.eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz.1, hz.2⟩
      simp only [frameFibreCount]
      rw [h0]
      simp
  calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        lintegral_mono hle
    _ = N * μH[((2 * d : ℕ) : ℝ)] (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T) :=
        lintegral_indicator_const ((measurableSet_toMeasurable _ _).preimage φ.continuous.measurable) _
    _ = N * μH[((2 * d : ℕ) : ℝ)] T := by
        rw [φ.isometry.hausdorffMeasure_preimage (Or.inr φ.surjective), φ.surjective.range_eq,
          Set.inter_univ, measure_toMeasurable]
end GroundTheory.Heights₂.Heights.LocalGraphProjectionMass
