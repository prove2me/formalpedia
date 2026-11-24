-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.iso_iff_cT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:52.071036+00:00
-- url     : https://prove2.me/submissions/2f66327c-ca49-4f97-b74c-430acdec1c3a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
import Theorems.Thm_PositivityTheory_ThKH_Iwas_Wm_map

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
theorem _root_.solution (hc : ∀ x, c (c x) = x) (M : Matrix (β ⊕ β) (β ⊕ β) L) :
    Iso c (Wm L β) (Wm L β) M ↔ cT c M * Wm L β * M = Wm L β := by
  have hcc : ∀ N : Matrix (β ⊕ β) (β ⊕ β) L, (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  constructor
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, Wm_map, hcc] at this
    exact this
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, Wm_map] at this
    rw [cT, transpose_map, hcc] at this
    exact this
end PositivityTheory.ThKH.Iwas
