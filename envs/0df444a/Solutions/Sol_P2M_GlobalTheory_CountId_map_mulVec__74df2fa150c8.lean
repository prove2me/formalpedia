-- Prove2me | solution 1 for P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:57.030819+00:00
-- url     : https://prove2.me/submissions/32198d4e-e9b3-43e4-a768-1623f1d41a99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']
namespace GlobalTheory.CountId
theorem _root_.solution (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (fun i => φ ((A *ᵥ v) i)) = A.map φ *ᵥ fun i => φ (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
end GlobalTheory.CountId
