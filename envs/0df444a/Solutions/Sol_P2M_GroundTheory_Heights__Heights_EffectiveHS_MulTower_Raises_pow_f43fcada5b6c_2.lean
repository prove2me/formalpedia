-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:50.794582+00:00
-- url     : https://prove2.me/submissions/fa5d8541-6729-47f4-8311-549cd60f1b00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_one_b487892ad098

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)
namespace GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
namespace Raises
theorem _root_.solution {τ : MulTower R A} {k : ℕ} {x : A} (hx : τ.Raises k x) (n : ℕ) :
    τ.Raises (k * n) (x ^ n) := by
  induction n with
  | zero => simpa using τ.raises_one
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact ih.mul hx
end Raises
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
