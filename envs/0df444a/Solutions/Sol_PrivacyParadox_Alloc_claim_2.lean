-- Prove2me | solution 1 for PrivacyParadox.Alloc.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:38:02.70533+00:00
-- url     : https://prove2.me/submissions/b3722e44-743c-4c3c-a2c1-a8fc5d29aa83

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

open PrivacyParadox.Alloc in
theorem solution (P : Prog) (hP : P.Standing) (m : ℕ) (hm1 : 1 ≤ m) (hmK : m < P.K) :
    P.Q (m + 1) 1 = P.Q m (P.phi m / P.phi (m + 1)) ∧
      P.R (m + 1) 1 = P.R m (P.phi m / P.phi (m + 1)) := by
  obtain ⟨_, hpos, _⟩ := hP
  have hφm : 0 < P.phi m := (hpos m (Finset.mem_Icc.mpr ⟨hm1, hmK.le⟩)).2
  have hφ1 : 0 < P.phi (m + 1) := (hpos (m + 1) (Finset.mem_Icc.mpr ⟨by omega, hmK⟩)).2
  have hsplit : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.Icc (m + 1) P.K, f k =
      f (m + 1) + ∑ k ∈ Finset.Icc (m + 1 + 1) P.K, f k := by
    intro f
    have hI : Finset.Icc (m + 1) P.K = insert (m + 1) (Finset.Icc (m + 1 + 1) P.K) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_insert (by simp)]
  constructor
  · unfold Prog.Q
    rw [Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega), hsplit]
    have hz : P.phi m / (P.phi m / P.phi (m + 1)) = P.phi (m + 1) := by
      field_simp
    rw [hz, div_one]
    have hs : Real.sqrt (P.phi (m + 1)) * Real.sqrt (P.phi (m + 1)) = P.phi (m + 1) :=
      Real.mul_self_sqrt hφ1.le
    linear_combination (-(P.pr (m + 1))) * hs
  · unfold Prog.R
    rw [Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega), hsplit]
    have hz : P.phi m / P.phi (m + 1) / P.phi m = 1 / P.phi (m + 1) := by
      field_simp
    rw [hz]
    have h1 : 1 / P.phi (m + 1) * (P.pr (m + 1) * P.phi (m + 1)) = P.pr (m + 1) := by
      field_simp
    linear_combination 2 * P.gam * h1
