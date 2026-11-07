-- Prove2me | solution 1 for QEC.Coding.ReedMuller.evaluationLinearMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:20:23.7132+00:00
-- url     : https://prove2.me/submissions/89eebdd8-ff70-46e4-9f57-22d4f72db6d6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace ReedMuller
open scoped BigOperators
private theorem monomialValue_supportPoint {m r : Nat}
    (monomial : SquarefreeMonomial m r) (support : Finset (Fin m)) :
    monomialValue monomial (supportPoint support) =
      if monomial.1 ⊆ support then 1 else 0 := by
  classical
  by_cases hsubset : monomial.1 ⊆ support
  · rw [if_pos hsubset]
    unfold monomialValue
    apply Finset.prod_eq_one
    intro coordinate hcoordinate
    simp [supportPoint, hsubset hcoordinate]
  · rw [if_neg hsubset]
    obtain ⟨coordinate, hcoordinate, hmissing⟩ :
        ∃ coordinate ∈ monomial.1, coordinate ∉ support := by
      simpa only [Finset.not_subset] using hsubset
    unfold monomialValue
    exact Finset.prod_eq_zero hcoordinate (by simp [supportPoint, hmissing])
end ReedMuller
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution (m r : Nat) :
    Function.Injective (evaluationLinearMap m r) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro polynomial hzero
  funext target
  have hcoeff :
      ∀ card : Nat, ∀ monomial : SquarefreeMonomial m r,
        monomial.1.card = card → polynomial monomial = 0 := by
    intro card
    induction card using Nat.strong_induction_on with
    | h card ih =>
        intro monomial hcard
        have happly := congrFun hzero (supportPoint monomial.1)
        rw [evaluationLinearMap_apply] at happly
        have hsingle :
            (∑ other,
              polynomial other * monomialValue other (supportPoint monomial.1)) =
              polynomial monomial := by
          rw [Fintype.sum_eq_single monomial]
          · rw [monomialValue_supportPoint]
            simp
          · intro other hne
            by_cases hsubset : other.1 ⊆ monomial.1
            · have hsupportNe : other.1 ≠ monomial.1 := by
                intro heq
                exact hne (Subtype.ext heq)
              have hstrict : other.1 ⊂ monomial.1 :=
                (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hsupportNe⟩
              have hcardLt : other.1.card < monomial.1.card :=
                Finset.card_lt_card hstrict
              have hother : polynomial other = 0 :=
                ih other.1.card (by simpa [hcard] using hcardLt) other rfl
              simp [monomialValue_supportPoint, hsubset, hother]
            · simp [monomialValue_supportPoint, hsubset]
        rw [hsingle] at happly
        simpa using happly
  exact hcoeff target.1.card target rfl
end QEC.Coding.ReedMuller
