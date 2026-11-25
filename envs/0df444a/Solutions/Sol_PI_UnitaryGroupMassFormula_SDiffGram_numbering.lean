-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SDiffGram.numbering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:53.313206+00:00
-- url     : https://prove2.me/submissions/282bbb10-f2ab-4545-9c18-4b711b489bb2

import Definitions.Def_Formalism_PeriodIntegrals_SDiffGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_SDiffGramMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SDiffGram
open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_X simeq_ren ren_be)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub)
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.SDiffGram
theorem _root_.solution (ι ι' : Type) [Fintype ι] [Fintype ι'] :
    ∃ (E : ι ⊕ ι' ≃ Fin (Fintype.card ι + Fintype.card ι')) (eι : ι ≃ Fin (Fintype.card ι))
      (eι' : ι' ≃ Fin (Fintype.card ι')),
      (∀ i i', E (Sum.inl i) < E (Sum.inl i') ↔ eι i < eι i') ∧
      (∀ g g', E (Sum.inr g) < E (Sum.inr g') ↔ eι' g < eι' g') ∧
      (∀ i g, E (Sum.inl i) < E (Sum.inr g)) ∧ (∀ g i, ¬ E (Sum.inr g) < E (Sum.inl i)) := by
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eι' : ι' ≃ Fin (Fintype.card ι') := Fintype.equivFin ι'
  have hlr : ∀ i g, (Equiv.sumCongr eι eι').trans finSumFinEquiv (Sum.inl i) <
      (Equiv.sumCongr eι eι').trans finSumFinEquiv (Sum.inr g) := by
    intro i g
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd,
      Fin.val_natAdd]
    have := (eι i).isLt
    omega
  refine ⟨(Equiv.sumCongr eι eι').trans finSumFinEquiv, eι, eι', ?_, ?_, hlr,
    fun g i h => lt_asymm h (hlr i g)⟩
  · intro i i'
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
    rw [Fin.lt_def, Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd]
  · intro g g'
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
    rw [Fin.lt_def, Fin.lt_def, Fin.val_natAdd, Fin.val_natAdd]
    omega
end PI.UnitaryGroupMassFormula.SDiffGram
