-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:42.215774+00:00
-- url     : https://prove2.me/submissions/fbc5264c-720e-4bfe-bbd4-05c7380fb278

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLog_le_a8984c2e2088
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurableSet_coneBall_4b3833b98430

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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeLogBound
theorem _root_.solution (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ConeLogBound.Statement := by
  intro n e δ h W f u hW hf hδ hu
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n))
  set c := (μ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
  have hmass := hMass n e δ h W f hW hf hδ
  have hfin := hFin n e h W f hW hf
  have hS := measurableSet_coneBall h W
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℂ (Fin n) => Real.log (h.norm u)) (coneBall h W) μ :=
    integrableOn_const hfin.ne
  have hae : (fun y => fsLog h u (h.pointOf y)) ≤ᵐ[μ.restrict (coneBall h W)]
      fun _ => Real.log (h.norm u) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hS]
    have hnull := hNull n e h W f u hW hf hu
    refine measure_mono_null (fun y hy => ?_) hnull
    have hy' : ¬(y ∈ coneBall h W → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u)) := hy
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hy' fun h' => absurd h' hc
    · show ∑ j, u j * h.pointOf y j = 0
      by_contra hne
      exact hy' fun _ => fsLog_le h hne
  have hle := setIntegral_mono_ae_restrict (hInt n e h W f u hW hf hu) hconst hae
  rw [setIntegral_const, smul_eq_mul] at hle
  unfold coneIntegral at hmass ⊢
  change (∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂μ) / c ≤ δ * Real.log (h.norm u)
  change (∫ y in coneBall h W, (1 : ℝ) ∂μ) / c = δ at hmass
  rw [setIntegral_const, smul_eq_mul, mul_one] at hmass
  rcases (le_or_gt c 0) with hc | hc
  · have hc0 : c = 0 := le_antisymm hc ENNReal.toReal_nonneg
    rw [hc0, div_zero] at hmass ⊢
    rw [← hmass]
    simp
  · rw [div_le_iff₀ hc]
    calc _ ≤ μ.real (coneBall h W) * Real.log (h.norm u) := hle
      _ = δ * Real.log (h.norm u) * c := by
        rw [← hmass]
        field_simp
end ConeLogBound
end GroundTheory.Heights₂.Heights
