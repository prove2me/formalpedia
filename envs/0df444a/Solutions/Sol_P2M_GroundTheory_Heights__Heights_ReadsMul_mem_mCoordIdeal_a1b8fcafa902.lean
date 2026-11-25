-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReadsMul_mem_mCoordIdeal_a1b8fcafa902
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:49.431819+00:00
-- url     : https://prove2.me/submissions/ef3f76dd-507b-4e5c-ab21-44a995ca1eca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReadsMul_mConeMap_of_homog_9cd01bc91e23

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ReadsMul
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ReadsMul
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) (h0 : aeval y g = 0) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_homog y hg, h0, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.ReadsMul
