-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionDegreeSum_proof_a7a878d0e31c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:50.775443+00:00
-- url     : https://prove2.me/submissions/a1e31c0a-db32-4980-8270-9fc0cad4fe94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionDegreeSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionDegreeSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4


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
namespace GroundTheory.Heights₂.Heights
namespace SectionDegreeSum
theorem _root_.solution (h : ChowFormSection.Statement) : SectionDegreeSum.Statement := by
  intro F _ _ n e δ I f u hI hf hδ hu
  obtain ⟨c, hc, g, hg, heq⟩ := h F n (e + 1) I f u hI hf hu
  have hδs : IsMultiHomog δ (specFirst f u) := hδ.specFirst u
  rw [heq] at hδs
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hδs hne
  exact ⟨g, δW, fun W hW => ⟨isProjPrime_of_mem_support_divCycle hI u hW, hg W hW, hδW W hW⟩,
    hsum.symm⟩
end SectionDegreeSum
end GroundTheory.Heights₂.Heights
