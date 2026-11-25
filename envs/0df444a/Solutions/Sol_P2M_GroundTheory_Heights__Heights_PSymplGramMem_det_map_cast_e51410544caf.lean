-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplGramMem_det_map_cast_e51410544caf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:00.515066+00:00
-- url     : https://prove2.me/submissions/6271a602-73e1-4c47-80d2-1b0d74c6ed96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplGramMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.PSymplGramMem
namespace GroundTheory.Heights₂.Heights.PSymplGramMem
theorem _root_.solution {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by
  have h := SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))
  simpa using h
end GroundTheory.Heights₂.Heights.PSymplGramMem
