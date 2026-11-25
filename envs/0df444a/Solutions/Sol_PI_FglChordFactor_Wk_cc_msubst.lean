-- Prove2me | solution 1 for PI.FglChordFactor.Wk.cc_msubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:20.220186+00:00
-- url     : https://prove2.me/submissions/9f1c9c75-8c49-46f7-b8cb-d14f06c3a970

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst


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
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {φ : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hφ : MvPowerSeries.HasSubst φ)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst φ H) = MvPowerSeries.constantCoeff H := by
  rw [MvPowerSeries.constantCoeff_subst hφ, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => φ s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      simp [hφ0, zero_pow hs]
    rw [h0, smul_zero]
end PI.FglChordFactor.Wk
