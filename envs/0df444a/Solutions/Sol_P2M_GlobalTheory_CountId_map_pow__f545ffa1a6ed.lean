-- Prove2me | solution 1 for P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:40.204907+00:00
-- url     : https://prove2.me/submissions/07bf15bb-337d-4ee3-ad99-8ecc092daa9f

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
theorem _root_.solution (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (i : ℕ) :
    (A ^ i).map φ = (A.map φ) ^ i := by
  induction i with
  | zero => simp [Matrix.map_one]
  | succ m ih => rw [pow_succ, pow_succ, Matrix.map_mul, ih]
end GlobalTheory.CountId
