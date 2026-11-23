-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.isLocal_of_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:13.569847+00:00
-- url     : https://prove2.me/submissions/4c135907-55a6-4d00-a55f-722d57ddb718

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) : IsLocalRing R := by
  have hne : Nontrivial R := ⟨⟨0, 1, fun h => by
    have := congrArg (fun x => v (algebraMap R C x)) h
    simp at this⟩⟩
  refine @IsLocalRing.of_nonunits_add R _ hne ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one] at ha hb ⊢
  have ha' : v (algebraMap R C a) < 1 := lt_of_le_of_ne (hv.map_le_one a) ha
  have hb' : v (algebraMap R C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) hb
  rw [map_add]
  exact ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt ha' hb'))
end ReciprocityTheory.PGsh.Up
