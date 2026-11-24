-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.exists_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:46.936987+00:00
-- url     : https://prove2.me/submissions/eafc5a92-63be-4ad4-8d13-3071ab35ae76

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {Φ : Matrix A D k → ℂ}
    (hΦ : Φ ∈ SB _) : ∃ U : Subgroup (GL D k), IsOpen (U : Set (GL D k)) ∧ ∀ u ∈ U, ∀ X, Φ (X * u.val) = Φ X := by
  obtain ⟨hl, hc⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hK : IsCompact (tsupport Φ) := hc
  let U : Subgroup (GL D k) :=
    { carrier := {u | ∀ X, Φ (X * u.val) = Φ X}
      one_mem' := fun X => by rw [Units.val_one, Matrix.mul_one]
      mul_mem' := fun {u v} hu hv X => by rw [Units.val_mul, ← Matrix.mul_assoc, hv, hu]
      inv_mem' := fun {u} hu X => by
        rw [← hu (X * (u⁻¹).val), Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] }
  have hev : ∀ᶠ u in nhds (1 : GL D k), ∀ X ∈ tsupport Φ, Φ (X * u.val) = Φ X := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have h1 : IsLocallyConstant fun z : GL D k × Matrix A D k => Φ (z.2 * z.1.val) :=
      hl.comp_continuous (continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst))
    have h2 : IsLocallyConstant fun z : GL D k × Matrix A D k => Φ z.2 :=
      hl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x)] with z e1 e2
    rw [e1, e2, Units.val_one, Matrix.mul_one]
  have hinv : Filter.Tendsto (fun u : GL D k => u⁻¹) (nhds 1) (nhds 1) := by
    have := (continuous_inv (G := GL D k)).tendsto 1
    rwa [inv_one] at this
  have hU : (U : Set (GL D k)) ∈ nhds (1 : GL D k) := by
    filter_upwards [hev, hinv.eventually hev] with u hu hu' X
    by_cases hx : X ∈ tsupport Φ
    · exact hu X hx
    by_cases hxu : X * u.val ∈ tsupport Φ
    · have := hu' _ hxu
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]
  exact ⟨U, U.isOpen_of_mem_nhds hU, fun u hu => hu⟩
end PositivityTheory.ThK.SplitLoc.Unr
