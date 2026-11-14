-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_likelihood_mean_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:12.147212+00:00
-- url     : https://prove2.me/submissions/4f79f3b4-336e-4692-9130-3c4da8b36150
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_small
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ (s*η^2/96)*n := by
  have hε : 0 < η^2/96 := by positivity
  obtain ⟨s,hs,hs1,N,hN⟩ := overlap_likelihood_small m hm d hd t ht hC1 (η^2/96) hε
  refine ⟨s,hs,hs1,max N 1,?_⟩
  intro n hn heven
  have hn0 : (0:ℝ) < n := by
    have h : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast h
  have hh := hN n (le_trans (le_max_left _ _) hn) heven
  have hh' : plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) / n ≤ η^2/96*s := by
    simpa [div_eq_mul_inv,mul_comm] using hh
  have h := (div_le_iff₀ hn0).mp hh'
  nlinarith
