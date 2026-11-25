-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_L1_g__eq_e1cebfa140ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:01.873835+00:00
-- url     : https://prove2.me/submissions/d2801c86-cc2a-490d-98aa-538fd48dd45e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_G_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sixVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring
end ReciprocityTheory.ChartRestriction.L1
