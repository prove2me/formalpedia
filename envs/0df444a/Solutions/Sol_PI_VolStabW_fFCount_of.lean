-- Prove2me | solution 1 for PI.VolStabW.fFCount_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:34.836979+00:00
-- url     : https://prove2.me/submissions/d006ad9f-be09-43d9-ac72-ac6012c2d425

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_ratio_bound
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_split_ratio
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_inert_ratio
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_split_delta
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_inert_delta
import Theorems.Thm_PI_VolStabW_FiniteFieldCounting_card_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos (α := k)
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by positivity
  rcases hσ.2 with ⟨hK, hdeg, hne⟩ | ⟨e, he⟩
  · letI : Field K := hK.toField
    rw [hI k K σ hσ.1 hdeg hne h2 M a (by omega) J hJ hJd T hT hTd,
      FiniteFieldCounting.inert_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.inert_delta M a ha _ hq1)
  · have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have hd : e J.det = (J.map e).det := (e : K →+* k × k).map_det J
      rw [← hd]
      exact hJd.map e
    have hTd' : IsUnit (T.map e).det := by
      have hd : e T.det = (T.map e).det := (e : K →+* k × k).map_det T
      rw [← hd]
      exact hTd.map e
    rw [FiniteFieldCounting.card_transport σ e he J T, hS k M a (by omega) _ hJ' hJd' _ hT' hTd',
      FiniteFieldCounting.split_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.split_delta M a ha _ hq1)
end PI.VolStabW
