-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_2ebb31936f55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:50.87355+00:00
-- url     : https://prove2.me/submissions/86d62b56-1953-47bb-a9d5-d0078ad1cf43

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
theorem _root_.solution {ι : Type*} (t : Finset ι) (k : ι → ℕ) (x : ι → A)
    (h : ∀ i ∈ t, τ.Raises (k i) (x i)) : τ.Raises (∑ i ∈ t, k i) (∏ i ∈ t, x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using τ.raises_one
  | insert a t ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a t)).mul (ih fun i hi => h i (mem_insert_of_mem hi))
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
