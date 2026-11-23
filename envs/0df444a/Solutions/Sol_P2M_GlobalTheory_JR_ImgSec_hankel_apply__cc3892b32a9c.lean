-- Prove2me | solution 1 for P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:56.001744+00:00
-- url     : https://prove2.me/submissions/42911e48-e761-4eb5-bc12-c84ce13dcd20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_mom_sec_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
variable {k : Type} [CommRing k] {r : ℕ}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution (a : Inv r k) (i j : Fin r) : hankel a i j = (a.2.1 ᵥ* (companion a.1 ^ (i : ℕ))) j :=
  mom_sec_add a i j
end GlobalTheory.JR.ImgSec
