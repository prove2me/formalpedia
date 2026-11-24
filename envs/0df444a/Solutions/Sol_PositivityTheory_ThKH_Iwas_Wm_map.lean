-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.Wm_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:50.943156+00:00
-- url     : https://prove2.me/submissions/ce095957-cdb6-450b-a627-f7ce1c28ad55

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc

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
namespace PositivityTheory.ThKH.Iwas
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (β : Type) [DecidableEq β] :
    (Wm A β).map f = Wm B β := by
  ext (i | i) (j | j) <;> simp [Wm, Matrix.one_apply, apply_ite f]
end PositivityTheory.ThKH.Iwas
