-- Prove2me | solution 1 for PI.VolStabS.fFCount_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:42.977091+00:00
-- url     : https://prove2.me/submissions/a3379964-5cef-4704-956e-e2e5af92426f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_ratio_bound
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_split_ratio
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_inert_ratio
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_split_delta
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_inert_delta
import Theorems.Thm_PI_VolStabS_FiniteFieldCounting_card_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
namespace PI.VolStabS
theorem _root_.solution (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by linarith
  have haM : a ≤ M := by omega
  rcases hσ.2 with ⟨hF, hrank, hne⟩ | ⟨e, he⟩
  · letI : Field K := hF.toField
    have hc := hI k K σ hσ.1 hrank hne h2 M a haM J hJ hJd T hT hTd
    rw [hc, FiniteFieldCounting.inert_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun j => FiniteFieldCounting.inert_delta M a ha _ hq1 j)
  · have hc := FiniteFieldCounting.card_transport σ e he J T
    have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have h := hJd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hTd' : IsUnit (T.map e).det := by
      have h := hTd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hs : (Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} : ℝ) =
        (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
          (Nat.card k : ℝ) ^ (a * (M - a)) := hS k M a haM (J.map e) hJ' hJd' (T.map e) hT' hTd'
    rw [hc, hs, FiniteFieldCounting.split_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun i => FiniteFieldCounting.split_delta M a ha _ hq1 i)
end PI.VolStabS
