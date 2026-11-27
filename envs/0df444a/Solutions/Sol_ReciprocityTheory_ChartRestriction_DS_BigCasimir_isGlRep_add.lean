-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.isGlRep_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:19.696999+00:00
-- url     : https://prove2.me/submissions/191d9936-e086-4d61-9f36-5214e5c5f986

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution {A B : Fin n → Fin n → Module.End ℂ X} (hA : IsGlRep A) (hB : IsGlRep B)
    (hAB : ∀ a b c d, A a b * B c d = B c d * A a b) : IsGlRep (A + B) := by
  intro a b c d
  simp only [Pi.add_apply]
  have h1 := hA a b c d
  have h2 := hB a b c d
  have h3 := hAB a b c d
  have h4 := hAB c d a b
  have : (A a b + B a b) * (A c d + B c d) - (A c d + B c d) * (A a b + B a b) =
      (A a b * A c d - A c d * A a b) + (B a b * B c d - B c d * B a b) := by
    simp only [add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [this, h1, h2]
  split_ifs <;> (try simp only [sub_zero, zero_sub, add_zero]) <;> abel
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
