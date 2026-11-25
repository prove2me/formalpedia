-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_biUnion_39b419609317
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:34.127037+00:00
-- url     : https://prove2.me/submissions/8a2a44cd-16b9-4a80-94af-f6e9056616e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_empty_e8cbdc6b748b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_union_47b1eb91459a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.QuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.QuasiFiniteSheets
theorem _root_.solution (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ)
    (hsh : ∀ Q ∈ F, ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (ComplexSets.zeroSet Q) A c)
    (hpair : ∀ Q ∈ F, ∀ Q' ∈ F, Q ≠ Q' → ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
      ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (⋃ Q ∈ F, ComplexSets.zeroSet Q) A c := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simpa using hasSheetsOff_empty A⟩
  | insert Q F hQ ih =>
    obtain ⟨c₀, hc₀, h₀⟩ := ih (fun Q' h => hsh Q' (Finset.mem_insert_of_mem h))
      (fun Q' h Q'' h' hne => hpair Q' (Finset.mem_insert_of_mem h) Q'' (Finset.mem_insert_of_mem h') hne)
    obtain ⟨c, hc, h⟩ := hsh Q (Finset.mem_insert_self _ _)
    have hp : ∀ Q' ∈ F, ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
        ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0 :=
      fun Q' hQ' => hpair Q (Finset.mem_insert_self _ _) Q' (Finset.mem_insert_of_mem hQ')
        (by rintro rfl; exact hQ hQ')
    choose! e he0 he using hp
    refine ⟨c * c₀ * ∏ Q' ∈ F, e Q', mul_ne_zero (mul_ne_zero hc hc₀) (Finset.prod_ne_zero_iff.mpr he0), ?_⟩
    rw [Finset.set_biUnion_insert]
    refine hasSheetsOff_union h h₀ ?_
    rintro x ⟨hxQ, hxF⟩
    obtain ⟨Q', hQ', hx'⟩ := Set.mem_iUnion₂.mp hxF
    rw [map_prod]
    exact Finset.prod_eq_zero hQ' (he Q' hQ' x ⟨hxQ, hx'⟩)
end GroundTheory.Heights₂.Heights.QuasiFiniteSheets
