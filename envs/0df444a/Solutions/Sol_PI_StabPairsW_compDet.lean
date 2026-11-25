-- Prove2me | solution 1 for PI.StabPairsW.compDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:27.378808+00:00
-- url     : https://prove2.me/submissions/9e962d41-6fd0-4a4c-8abf-4057d0234b69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Theorems.Thm_PI_StabPairsW_det_UT
import Theorems.Thm_PI_StabPairsW_det_Zhat_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution : CompDet := by
  intro k r z z' γ hs hp p hpS q hqS
  obtain ⟨hp1, hp2, hpe⟩ := hpS
  obtain ⟨hq1, hq2, hqe⟩ := hqS
  have hZu : IsUnit (Zhat k r z z' γ) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_Zhat_ne z z' hs γ hp))
  have hU : ∀ {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}, u ∈ UTset (r + 1) → IsUnit u :=
    fun hu => (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_UT hu]; exact isUnit_one)
  have hUH : ∀ {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}, u ∈ UTset (r + 1) → IsUnit uᴴ :=
    fun hu => (Matrix.isUnit_iff_isUnit_det _).2
      (by rw [Matrix.det_conjTranspose, det_UT hu, star_one]; exact isUnit_one)
  constructor
  · intro h1
    have e : (p.1ᴴ * Zhat k r z z' γ) * p.2 = (p.1ᴴ * Zhat k r z z' γ) * q.2 := by
      rw [hpe, h1, hqe]
    exact Prod.ext h1 (((hUH hp1).mul hZu).mul_left_cancel e)
  · intro h2
    have e : p.1ᴴ * (Zhat k r z z' γ * p.2) = q.1ᴴ * (Zhat k r z z' γ * p.2) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpe, h2, hqe]
    have h1 := (hZu.mul (hU hp2)).mul_right_cancel e
    exact Prod.ext (Matrix.conjTranspose_inj.1 h1) h2
end PI.StabPairsW
