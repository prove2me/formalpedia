-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.puncturedReedSolomonCode_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:13.218596+00:00
-- url     : https://prove2.me/submissions/59352af4-7b2a-4cb3-9790-e3e67a366a38

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dimension
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace KT19ReedSolomon
open scoped BigOperators
private theorem restrictKept_injective_on_reedSolomonCode
    (p l k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hlength : l ≤ p - k) :
    Function.Injective
      ((restrictKept p k).domRestrict (reedSolomonCode p l).carrier) := by
  intro left right heq
  rcases (mem_reedSolomonCode p l left.1).1 left.2 with ⟨leftPolynomial, hleft⟩
  rcases (mem_reedSolomonCode p l right.1).1 right.2 with ⟨rightPolynomial, hright⟩
  have hpolynomials : leftPolynomial = rightPolynomial := by
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (keptPunctureLocations p k)
    · exact (Polynomial.mem_degreeLT.mp leftPolynomial.2).trans_le
        (by simpa [keptPunctureLocations_card p k hkp] using hlength)
    · exact (Polynomial.mem_degreeLT.mp rightPolynomial.2).trans_le
        (by simpa [keptPunctureLocations_card p k hkp] using hlength)
    · intro point hpoint
      have hpoint' := congrFun heq ⟨point, hpoint⟩
      calc
        leftPolynomial.1.eval point = left.1 point := by
          exact congrFun hleft point
        _ = right.1 point := by
          change left.1 point = right.1 point at hpoint'
          exact hpoint'
        _ = rightPolynomial.1.eval point := by
          exact (congrFun hright point).symm
  apply Subtype.ext
  calc
    left.1 = evaluationLinearMap p l leftPolynomial := hleft.symm
    _ = evaluationLinearMap p l rightPolynomial :=
      congrArg (evaluationLinearMap p l) hpolynomials
    _ = right.1 := hright
end KT19ReedSolomon
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (hlength : l ≤ p - k) :
    Dimension (puncturedReedSolomonCode p l k) = l := by
  change Module.finrank (ZMod p)
    ((reedSolomonCode p l).carrier.map (restrictKept p k)) = l
  rw [← LinearMap.range_domRestrict]
  rw [LinearMap.finrank_range_of_inj
    (restrictKept_injective_on_reedSolomonCode p l k hkp hlength)]
  exact reedSolomonCode_dimension p l (Nat.le_trans hlength (Nat.sub_le _ _))
end QEC.Coding.KT19ReedSolomon
