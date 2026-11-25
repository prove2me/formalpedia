-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.isAdicComplete_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:06:07.294903+00:00
-- url     : https://prove2.me/submissions/e354679b-f08e-4c9c-b8ea-d4fc4a7cb516

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_isPrecomplete_of_basis
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_span_p_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (S : Type) [CommRing S] [Algebra ℤ_[p] S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] S) : IsAdicComplete (Ideal.span {(p : S)}) S := by
  have : Module.Finite ℤ_[p] S := Module.Finite.of_basis b
  have hH : IsHausdorff (maximalIdeal ℤ_[p]) S := inferInstance
  have hP : IsPrecomplete (maximalIdeal ℤ_[p]) S := isPrecomplete_of_basis b
  rw [← span_p_eq S]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
