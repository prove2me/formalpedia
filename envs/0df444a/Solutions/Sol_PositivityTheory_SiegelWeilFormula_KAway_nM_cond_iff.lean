-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.nM_cond_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:22:55.194298+00:00
-- url     : https://prove2.me/submissions/0a5bb04b-59e0-4399-ab5f-0dabf9e8d209

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem _root_.solution (t : Matrix (Fin n) (Fin n) R) :
    (nM t)ᵀ * jF n ε * (nM t).map c = jF n ε ↔ tᵀ + (ε : R) • t.map c = 0 := by
  simp only [nM, jF, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj]
  simp [Matrix.map_one c (map_zero c) (map_one c), add_comm]
end PositivityTheory.SiegelWeilFormula.KAway
