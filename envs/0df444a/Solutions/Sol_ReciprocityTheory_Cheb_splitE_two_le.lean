-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:37.425663+00:00
-- url     : https://prove2.me/submissions/1f6f7a18-459d-4a7b-aad9-9a02feb1c5d5

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_H_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : 2 ≤ Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) := by
  have h0 : 0 < Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) := Module.finrank_pos
  have h1 : Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)) ≠ 1 := by
    intro h
    rw [IntermediateField.finrank_eq_one_iff] at h
    apply splitE_H_ne_top hirr χ hχ
    rw [← IntermediateField.fixingSubgroup_fixedField (splitEH hirr χ), h,
      IntermediateField.fixingSubgroup_bot]
  omega
end ReciprocityTheory.Cheb
