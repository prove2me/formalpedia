-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_L1_g__eq_e5b5a7aa6c51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:26.600677+00:00
-- url     : https://prove2.me/submissions/efbd6773-24f4-4fce-b652-fb6037f15deb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_G_eq

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
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring
end ReciprocityTheory.ChartRestriction.L1
