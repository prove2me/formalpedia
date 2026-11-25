-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:32:08.954934+00:00
-- url     : https://prove2.me/submissions/2ccd9f63-5908-4c5f-8010-3e0f74c4ef1b

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_degreeOfFamily_eq_degreeOfFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v : Fin r → V} (hv : IsFrame K E v) : deg h E = degreeOfFamily h E v := by
  have hex : ∃ p : (Σ r : ℕ, Fin r → V), IsFrame K E p.2 := ⟨⟨r, v⟩, hv⟩
  unfold deg
  rw [dif_pos hex]
  exact degreeOfFamily_eq_degreeOfFamily h hE hex.choose_spec hv
end ReciprocityTheory.GeometryOfNumbersTheory
