-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.coherent_top_initialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:35:15.179998+00:00
-- url     : https://prove2.me/submissions/7e745c01-1c68-4f2f-9241-81916d955800

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_self
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_perturbTop_preimage


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    ∃ u : (SuffixData S n).family.Cochain1 (TopIndex n),
      (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val ∧
      (SuffixData S n).family.coboundary1 (TopIndex n) (u+e) = (perturbTop S n sigma e).val ∧
      descentWord S n (TopIndex n) u (TopIndex n) (Nat.le_refl _) +
        descentWord S n (TopIndex n) (u+e) (TopIndex n) (Nat.le_refl _) = e := by
  obtain ⟨u,hu,hue⟩ := perturbTop_preimage S n sigma e
  refine ⟨u,hu,hue,?_⟩
  rw [descentWord_self,descentWord_self,← add_assoc,word_add_self,zero_add]
end QEC.Coding.BDL26HistoryErrorTelescoping
