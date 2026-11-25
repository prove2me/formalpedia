-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.inv_apply_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:43.012312+00:00
-- url     : https://prove2.me/submissions/694c5819-608d-47fb-996d-e4d14a5a8920

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
import Theorems.Thm_PositivityTheory_ThKH_Iwas_inv_eq_of_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]
namespace PositivityTheory.ThKH.Iwas
theorem _root_.solution (hc : ∀ x, c (c x) = x) {M N : Matrix (β ⊕ β) (β ⊕ β) L} (h : Iso c (Wm L β) (Wm L β) M)
    (hN : M * N = 1) (i j : β ⊕ β) : N i j = c (M j.swap i.swap) := by
  rw [inv_eq_of_iso hc h hN]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Wm, cT, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end PositivityTheory.ThKH.Iwas
