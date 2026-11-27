-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Tree_premises_satisfiable__242a85f84517
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:07.629615+00:00
-- url     : https://prove2.me/submissions/0a894610-4d8d-4eef-971a-e8179a6417aa

import Mathlib
import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_HarderNarasimhan_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_ExistsCoordBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KernelExtensionOfKoszulLoweringImageLeviWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ProjKillsLiPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_OfListTakeOfFn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_RegularSequencePowerExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MiracleFlatOfRegSeqDepth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_ExistsIsRegularOfListEqMaximalIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MulXProjQExact
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_EagonNorthcottExactOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_AugmentationDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionLowersSecondDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZeroOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_BasisZeroEqSingle
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StBaseOf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Theorems.Thm_Formalism_L2_Indef_Tree_reduced_forms_neg_four
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Complex
universe u
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open scoped InnerProductSpace
namespace Formalism.L2.Indef.Tree
theorem _root_.solution :
    (7 % 16 = 7 ∧ Squarefree 7) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, |(Polynomial.X : Polynomial ℝ).eval x| ≤ 1) ∧
    0 < Complex.I.im ∧ 0 < (Complex.I / 1).im ∧ (reducedForms (-4)).Nonempty ∧
    RingTheory.Sequence.IsWeaklyRegular ℤ (List.ofFn (fun _ : Fin 1 => (2 : ℤ))) ∧
    RingTheory.Sequence.IsRegular ℤ ([] : List ℤ) ∧
    (∀ z : Fin 1 → ℂ_[2], (∀ i, ‖z i‖ < 1) →
      Summable (fun α : Fin 1 →₀ ℕ => (0 : ℂ_[2]) * ∏ i, z i ^ α i) ∧
      ‖∑' α : Fin 1 →₀ ℕ, (0 : ℂ_[2]) * ∏ i, z i ^ α i‖ ≤ 1) := by
  refine ⟨⟨by norm_num, (by norm_num : Nat.Prime 7).prime.squarefree⟩,
    fun x hx => by simp only [Polynomial.eval_X]; rw [abs_le]; constructor <;> linarith [hx.1, hx.2],
    by simp, by simp, by rw [reduced_forms_neg_four]; simp, ?_, ⟨RingTheory.Sequence.IsWeaklyRegular.nil ℤ ℤ, by simp⟩, ?_⟩
  · simp only [List.ofFn_succ, List.ofFn_zero]
    rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b h
    simp only [smul_eq_mul] at h
    omega
  · intro z _
    simp
end Formalism.L2.Indef.Tree
