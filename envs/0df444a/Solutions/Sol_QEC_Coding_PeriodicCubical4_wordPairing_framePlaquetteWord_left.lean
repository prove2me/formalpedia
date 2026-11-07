-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.wordPairing_framePlaquetteWord_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:27:47.803711+00:00
-- url     : https://prove2.me/submissions/fafb4ad9-3aea-4a31-bd54-9abcbf245891

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_framePlaquetteWord
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (p : Plane) (x y : Word (ZMod 2) (Plaquette L)) :
    wordPairing (framePlaquetteWord p x) y =
      wordPairing x (framePlaquetteWord p y) := by
  calc
    wordPairing (framePlaquetteWord p x) y =
        wordPairing (framePlaquetteWord p x)
          (framePlaquetteWord p (framePlaquetteWord p y)) := by
      congr 1
      exact (wordReindex (plaquetteEquiv p)).symm_apply_apply y |>.symm
    _ = wordPairing x (framePlaquetteWord p y) :=
      wordPairing_framePlaquetteWord p x (framePlaquetteWord p y)
end QEC.Coding.PeriodicCubical4
