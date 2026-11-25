-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplOrbit_smul_symplCons_a513fc6e72e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:10.720047+00:00
-- url     : https://prove2.me/submissions/bc393e0f-123a-4d65-9451-b7413560ee83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOrbit

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
open GroundTheory.Heights₂.Heights.PSymplOrbit
namespace GroundTheory.Heights₂.Heights.PSymplOrbit
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (m p q : R) (w : Fin n ⊕ Fin n → R) :
    m • symplCons p q w = symplCons (m * p) (m * q) (m • w) := by
  funext x
  rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons]
end GroundTheory.Heights₂.Heights.PSymplOrbit
