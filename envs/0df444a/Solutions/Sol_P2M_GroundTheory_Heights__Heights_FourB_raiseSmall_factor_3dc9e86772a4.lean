-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_raiseSmall_factor_3dc9e86772a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:48.945656+00:00
-- url     : https://prove2.me/submissions/dd3429a1-7415-4a8b-b28d-35d7fb3d5448

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PDegreeRatio
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {f : ℕ} (N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ)
    (hx : ∀ τ (i l : Fin N), i < l → x τ l < x τ i) (τ : Fin f) (i l : Fin N) :
    (if i < l then raiseSmall N j' δ x τ i - raiseSmall N j' δ x τ l else 1) =
      (if i < l then x τ i - x τ l else 1) *
        (if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1) := by
  by_cases hil : i < l
  · have hpos : 0 < x τ i - x τ l := sub_pos.mpr (hx τ i l hil)
    have hlt : i.val < l.val := hil
    simp only [if_pos hil, raiseSmall]
    by_cases hA : Across N j' i l
    · obtain ⟨h1, h2⟩ := hA
      have hi : ¬ N - j' ≤ i.val := by omega
      rw [if_neg hi, if_pos h2, if_pos (show Across N j' i l from ⟨h1, h2⟩)]
      field_simp
      ring
    · rw [if_neg hA, mul_one]
      simp only [Across, not_and, not_le] at hA
      by_cases hi : N - j' ≤ i.val
      · rw [if_pos hi, if_pos (show N - j' ≤ l.val by omega)]; ring
      · have hl := hA (by omega)
        rw [if_neg hi, if_neg (show ¬ N - j' ≤ l.val by omega)]
  · have hA : ¬ Across N j' i l := by
      rintro ⟨h1, h2⟩
      exact hil (Fin.lt_def.mpr (by omega))
    simp [hil, hA]
end GroundTheory.Heights₂.Heights.FourB
