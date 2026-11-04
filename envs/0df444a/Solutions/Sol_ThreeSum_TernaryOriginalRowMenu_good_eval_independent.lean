-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.good_eval_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:57.431964+00:00
-- url     : https://prove2.me/submissions/f85cc4ea-b5cd-4fdc-99d9-0829af9af76a

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
namespace ThreeSum.TernaryOriginalRowMenu
theorem _root_.solution {Λ t : ℕ} (v : Fin t → Fin Λ → K)
    (x : E) (hx : x ∉ badSeeds (E := E) v) :
    LinearIndependent K (fun i => evalVector Λ x (v i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_cases hz : c = 0
  · simp [hz]
  · exfalso
    apply hx
    apply mem_biUnion.mpr
    refine ⟨c, mem_erase.mpr ⟨hz,mem_univ _⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have hh : evalVector Λ x (∑ j, c j • v j) = 0 := by
      simpa only [map_sum, map_smul] using hc
    change (Polynomial.aeval x) (combination (E := E) v c) = 0 at hh
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hh
end ThreeSum.TernaryOriginalRowMenu
