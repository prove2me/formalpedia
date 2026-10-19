-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.matching_block_six_leaves_of_coefficientTranscendenceDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/9cef78e7-eeaa-4624-a064-f4b79853ae37

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_blockLeaves_pos_of_eval_eq_permanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_rational_skeleton_trdeg
import Theorems.Thm_PermanentFormulaLowerBound_Formula_yLeafCount_rename_matchingVariableEquiv
import Theorems.Thm_PermanentFormulaLowerBound_Formula_eval_rename_eq_matchingMarkedPermanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_valid_rename
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_yLeafCount_rename_matchingVariableEquiv
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_eval_rename_eq_matchingMarkedPermanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_blockLeaves_pos_of_eval_eq_permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution
    {n m : ℕ} {Y : Type*} [Fintype Y] [Nonempty Y]
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : Valid f)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (htd : ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d)) :
    m * m ≤ 6 * blockLeaves (matchingMarkedFinset d) f := by
  classical
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  have hymem : d y ∈ matchingMarkedFinset d :=
    (mem_matchingMarkedFinset d (d y)).2 ⟨y, rfl⟩
  have hpos : 0 < blockLeaves (matchingMarkedFinset d) f :=
    blockLeaves_pos_of_eval_eq_permanent f hf
      (matchingMarkedFinset d) (d y).1 (d y).2 hymem
  let g : RationalFormula (Y ⊕ matchingOutside d) ℂ :=
    rename (matchingVariableEquiv d).symm f
  have hmarked : 0 < yLeafCount g := by
    simpa [g, yLeafCount_rename_matchingVariableEquiv] using hpos
  have hvalid' : Valid g :=
    valid_rename (matchingVariableEquiv d).symm hvalid
  have houtput : eval g =
      algebraMap (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d) :=
    eval_rename_eq_matchingMarkedPermanent d f hf
  have hupper := rational_skeleton_trdeg g hvalid' hmarked
    (matchingMarkedPermanent d) houtput
  dsimp [g] at hupper
  rw [yLeafCount_rename_matchingVariableEquiv d f] at hupper
  have hcard :
      ((m * m : ℕ) : Cardinal) ≤
        ((6 * blockLeaves (matchingMarkedFinset d) f - 3 : ℕ) : Cardinal) :=
    htd.trans hupper
  have hnat :
      m * m ≤ 6 * blockLeaves (matchingMarkedFinset d) f - 3 := by
    exact_mod_cast hcard
  omega
end PermanentFormulaLowerBound.RationalFormula
