-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.inv_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:50.721866+00:00
-- url     : https://prove2.me/submissions/c4753d4f-8df0-407c-91cd-55a46773345e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
import Theorems.Thm_PositivityTheory_ThKH_Iwas_iso_iff_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Wm_mul_self


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
    (hN : M * N = 1) : N = Wm L β * cT c M * Wm L β := by
  have h1 := (iso_iff_cT hc M).1 h
  have h2 : Wm L β * cT c M * Wm L β * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c M), h1, Wm_mul_self]
  calc N = (Wm L β * cT c M * Wm L β * M) * N := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc _ M, hN, Matrix.mul_one]
end PositivityTheory.ThKH.Iwas
