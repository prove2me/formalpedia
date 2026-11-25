-- Prove2me | solution 1 for UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:39.173557+00:00
-- url     : https://prove2.me/submissions/8cad570c-ba93-4776-9a87-2f434788bfb4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapInvolutionEqSelf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MeasurableMatrixInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionMapCompactFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Theorems.Thm_UpperTheory_involution_map_compact_finite
import Theorems.Thm_UpperTheory_map_involution_eq_self
import Theorems.Thm_UpperTheory_measurable_matrix_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace UpperTheory.Reformulated.B.BlochKatoDuality
theorem _root_.solution :
    Formalism.FourierDecayAlt.B2.HaarInvFromUnique := by
  intro huniq k r U μ hU hμ
  have hm : Measurable (invM : Mt k r → Mt k r) := UpperTheory.measurable_matrix_inv _
  have hUc : IsClosed (X := Mt k r) U := hU.closed
  have hmem : ∀ x : Mt k r, x ∈ U → invM x ∈ U := fun x hx => hU.inv_mem x hx
  have hinv : ∀ x : Mt k r, x ∈ U → invM (invM x) = x := fun x hx =>
    Matrix.nonsing_inv_nonsing_inv (Matrix.of x) (hU.unit x hx)
  have hae : ∀ᵐ x ∂μ, (x : Mt k r) ∈ U := hμ.conc
  have hcont : ContinuousOn (invM : Mt k r → Mt k r) U := by
    intro x hx
    obtain ⟨u, hu⟩ := hU.unit x hx
    have h1 : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      have h2 := NormedRing.inverse_continuousAt u
      rw [hu] at h2
      exact h2
    exact (continuousAt_matrix_inv (Matrix.of x : Mat k r) h1).continuousWithinAt
  have hfin := UpperTheory.involution_map_compact_finite (Mt k r) μ U invM hm hUc hcont hmem hinv hμ.conc hμ.finite_compact
  have hconc : (μ.map invM) (Uᶜ : Set (Mat k r)) = 0 := by
    have h : ∀ᵐ x ∂(μ.map invM), (x : Mt k r) ∈ U :=
      (ae_map_iff hm.aemeasurable hUc.measurableSet).2 (hae.mono hmem)
    exact h
  have hleft : ∀ a ∈ U, (μ.map invM).map (lmulM a) = μ.map invM := by
    intro a ha
    have hl : Measurable (lmulM a : Mt k r → Mt k r) :=
      Continuous.measurable (α := Mt k r) (γ := Mt k r)
        (Continuous.matrix_mul (continuous_const (y := a)) (continuous_id (X := Mat k r)))
    have hr : Measurable (rmulF a⁻¹ : Mt k r → Mt k r) :=
      Continuous.measurable (α := Mt k r) (γ := Mt k r)
        (Continuous.matrix_mul (continuous_id (X := Mat k r)) (continuous_const (y := a⁻¹)))
    have he : (lmulM a ∘ invM : Mt k r → Mt k r) = invM ∘ rmulF a⁻¹ := by
      funext x
      change a * (Matrix.of x : Mat k r)⁻¹ = (Matrix.of x * a⁻¹ : Mat k r)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a (hU.unit a ha)]
    rw [Measure.map_map hl hm, he, ← Measure.map_map hm hr, hμ.right _ (hU.inv_mem a ha)]
  obtain ⟨c, hc⟩ := huniq k r U μ (μ.map invM) hU hμ hconc hleft hfin
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  exact UpperTheory.map_involution_eq_self (Mt k r) μ invM c hm (hae.mono hinv) hc
end UpperTheory.Reformulated.B.BlochKatoDuality
