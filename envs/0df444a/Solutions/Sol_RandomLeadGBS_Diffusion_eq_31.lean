-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:21:20.826207+00:00
-- url     : https://prove2.me/submissions/3d6d5165-e66f-473d-b2a2-1e25633180d9

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_eq_14
import Theorems.Thm_RandomLeadGBS_Diffusion_eq_19
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_4

open RandomLeadGBS.Diffusion

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ (p : State → ℝ) (q : ℤ → ℝ),
      IsStationary P r p → IsArtStationary P r q →
      Summable (fun j : ℤ => q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ)) ∧
      Summable (fun s : State => p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ)) ∧
      ∑' j : ℤ, q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ) -
        ∑' s : State, p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ) ≤ C := by
  obtain ⟨C, hC, r₀, h4⟩ := lemma_4 P hP hx
  refine ⟨C, hC, max r₀ 1, fun r hr p q hp hq => ?_⟩
  have hr0 : r ≥ r₀ := le_trans (le_max_left _ _) hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hr)
  have hβ : 0 < P.β := hP.1
  obtain ⟨hsD, _hsDt, hDle, hDtC⟩ := h4 r hr0 p hp
  obtain ⟨hsZ, hZ⟩ := eq_14 P hP hx r hrpos p hp
  obtain ⟨hsZh, hZh⟩ := eq_19 P hP hx r hrpos q hq
  -- the artificial in-transit level is the integer ceiling of the truncated target
  have hart : (fun j : ℤ => q j * ((⌈truncTarget P r j⌉ : ℤ) : ℝ)) =
      fun j => q j * (artZ P r j : ℝ) := by
    funext j
    have h0 : 0 ≤ truncTarget P r j := le_max_right _ _
    simp only [artZ]
    rw [← Int.natCast_ceil_eq_ceil h0, Int.cast_natCast]
  -- for the GBS chain, ⌈T⌉ = Z − D
  have hgbs : (fun s : State => p s * ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ)) =
      fun s => p s * (s.2 : ℝ) - p s * gapD P r s := by
    funext s; simp only [gapD]; ring
  rw [hart, hgbs]
  refine ⟨hsZh, hsZ.sub hsD, ?_⟩
  rw [Summable.tsum_sub hsZ hsD]
  have e1 : ∑' j : ℤ, q j * (artZ P r j : ℝ) = r / P.β := by
    field_simp; linarith [hZh]
  have e2 : ∑' s : State, p s * (s.2 : ℝ) = r / P.β := by
    field_simp; linarith [hZ]
  rw [e1, e2]
  linarith
