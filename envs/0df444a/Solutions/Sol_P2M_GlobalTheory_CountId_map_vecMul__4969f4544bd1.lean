-- Prove2me | solution 1 for P2M_GlobalTheory_CountId_map_vecMul__4969f4544bd1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:11.901968+00:00
-- url     : https://prove2.me/submissions/19435892-82fd-4c83-9d8b-6a48548c3b3c

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
    (fun i => φ ((v ᵥ* A) i)) = (fun i => φ (v i)) ᵥ* A.map φ := by
  funext i
  simp [Matrix.vecMul, dotProduct, map_sum, map_mul]
end GlobalTheory.CountId
