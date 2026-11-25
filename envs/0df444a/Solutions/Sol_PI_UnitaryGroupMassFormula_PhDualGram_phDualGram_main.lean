-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.phDualGram_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:29.659881+00:00
-- url     : https://prove2.me/submissions/416a7a03-5587-45d1-990d-dbd511d0d23d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_PhDualGramMain
import Theorems.Thm_PI_FglPhSplit_Wk_compositionalInverseSymm
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_gramRhs_dual
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_PhOn
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution : PhDualGram := by
  intro p _ l ex ph S hD hG κ ι _ _ b b' hb hb' hI
  obtain ⟨hex0, hinv, hph0⟩ := hD
  obtain ⟨hl0, hinvl⟩ := PI.FglPhSplit.Wk.compositionalInverseSymm ℂ_[p] l ex hex0 hinv
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : ι ⊕ ι ≃ Fin (Fintype.card ι + Fintype.card ι) :=
    (Equiv.sumCongr eι eι).trans finSumFinEquiv
  have hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e') := by
    intro e e'
    simp only [E, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd,
      Fin.val_natAdd]
    have := (eι e).isLt
    omega
  have hS : ∀ j i, Sum.elim b b' (E.symm j) i ∈ S := by
    intro j i
    rcases E.symm j with e | e
    exacts [hb e i, hb' e i]
  have h := simeq_ren (p := p) E.symm (hG κ _ (fun j => Sum.elim b b' (E.symm j)) hS)
  rw [ren_PhOn hex0 hl0 E (Sum.elim b b'), gramRhs_dual hex0 hph0 hl0 hinvl b b' hI E hE,
    map_sum] at h
  refine (congrArg (Simeq _) ?_).mp h
  unfold beSum
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ren_be hex0 hl0 _ (constantCoeff_X _) (constantCoeff_X _)]
  simp only [Xv, ren_X, Equiv.symm_apply_apply]
end PI.UnitaryGroupMassFormula.PhDualGram
