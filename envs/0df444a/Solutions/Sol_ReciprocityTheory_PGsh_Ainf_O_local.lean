-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.O_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:02.168034+00:00
-- url     : https://prove2.me/submissions/aa95bcde-2108-4105-8346-07dd034482ae

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O :=
    ⟨⟨(0 : O), (1 : O), fun h => by
      have h2 := congrArg (algebraMap O C) h
      simp at h2⟩⟩
  have hu : ∀ y : O, v (algebraMap O C y) = 1 → IsUnit y := fun y hy =>
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by
      rw [h0, map_zero] at hy
      exact zero_ne_one hy) hy
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases (hv.map_le_one x).lt_or_eq with hlt | heq
  · right
    apply hu
    rw [map_sub, map_one]
    exact Valuation.map_one_sub_of_lt v hlt
  · left
    exact hu x heq
end ReciprocityTheory.PGsh.Ainf
