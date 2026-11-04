-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.combination_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:02.075004+00:00
-- url     : https://prove2.me/submissions/28cb5bfd-ebb9-4257-a74f-fb98b9db64a1

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_vectorPoly_injective

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
    (hv : LinearIndependent K v) (c : Fin t → K) (hc : c ≠ 0) :
    combination (E := E) v c ≠ 0 := by
  intro hz
  have he : (∑ i, c i • v i) = 0 :=
    vectorPoly_injective Λ (hz.trans (map_zero (vectorPoly Λ)).symm)
  apply hc
  funext i
  exact Fintype.linearIndependent_iff.mp hv c he i
end ThreeSum.TernaryOriginalRowMenu
