-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CycleSectionChow_proof_79f707d56c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:50.119515+00:00
-- url     : https://prove2.me/submissions/47396fca-667e-4d5b-9183-8b2ff63e9788

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleSectionChow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowFormCycle_zero_one_4cd37bc8ca85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowFormCycle_C_mul_f39b13a892e3

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CycleSectionChow
theorem _root_.solution (h1 : ChowFormSection.Statement) (h2 : ChowFormCycleAdd.Statement)
    (h3 : ChowFormCycleSmul.Statement) : CycleSectionChow.Statement := by
  intro n e Z f u hprime hf hadm
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  have hW : ∀ W ∈ Z.support, IsChowFormCycle (divCycle W u) e (specFirst (g W) u) :=
    fun W hW' => h1 ℂ n e W (g W) u (hprime W hW') (hg W hW') (hadm W hW')
  have key : ∀ s ⊆ Z.support, IsChowFormCycle (∑ W ∈ s, Z W • divCycle W u) e
      (∏ W ∈ s, specFirst (g W) u ^ Z W) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using (isChowFormCycle_zero_one : IsChowFormCycle (0 : ProjCycle ℂ n) e 1)
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact h2 ℂ n e _ _ _ _ (h3 ℂ n e (Z a) _ _ (hW a (hs (Finset.mem_insert_self a s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  have hspec : specFirst (C c * ∏ W ∈ Z.support, g W ^ Z W) u =
      C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  rw [hspec]
  exact (key Z.support subset_rfl).C_mul hc
end CycleSectionChow
end GroundTheory.Heights₂.Heights
