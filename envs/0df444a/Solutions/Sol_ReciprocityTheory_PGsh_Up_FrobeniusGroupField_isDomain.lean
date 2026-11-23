-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:03.612185+00:00
-- url     : https://prove2.me/submissions/991f502d-4deb-4066-8702-a8822fa654e1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) : IsDomain R := by
  have : Nontrivial R := ⟨0, 1, fun h => by
    have := congrArg (fun r => v (algebraMap R C r)) h
    simp at this⟩
  exact hv.hom_inj.isDomain (algebraMap R C)
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
