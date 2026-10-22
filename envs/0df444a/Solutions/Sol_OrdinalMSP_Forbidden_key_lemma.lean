-- Prove2me | solution 1 for OrdinalMSP.Forbidden.key_lemma
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:57:24.314404+00:00
-- url     : https://prove2.me/submissions/d3981d89-0237-433a-8f9a-61d52d15f82d

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting
import Theorems.Thm_OrdinalMSP_Forbidden_eq_5
import Theorems.Thm_OrdinalMSP_Forbidden_game_bound
import Theorems.Thm_OrdinalMSP_Forbidden_integral_eval
import Theorems.Thm_OrdinalMSP_Forbidden_optimal_p

open OrdinalMSP.Forbidden

theorem solution {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (k : ℕ) (hk : 1 ≤ k)
    (ALG : ArrivalOrder R → ℕ → Finset R) (hALG : HasForbiddenSets M k ALG) :
    IsProbCompetitive M ALG (pK k) (alphaK k) := by
  intro r hr
  set g : ℝ → ℝ := fun p => if k = 1 then -p * Real.log p else (p - p ^ k) / ((k : ℝ) - 1)
    with hgdef
  obtain ⟨⟨hp0, hp1⟩, hgp, -⟩ := optimal_p k hk g (fun p => rfl)
  have hn : 1 ≤ Fintype.card R := Fintype.card_pos_iff.mpr ⟨r⟩
  have hint : (∫ τ in (pK k)..1, (pK k / τ) ^ k) = g (pK k) := by
    obtain ⟨h1, h2⟩ := integral_eval (pK k) hp0 hp1
    by_cases hk1 : k = 1
    · subst hk1; simp only [hgdef, if_true]; exact h1
    · have : 2 ≤ k := by omega
      simp only [hgdef, if_neg hk1]; exact h2 k this
  have hgame := game_bound (Fintype.card R) k hn hk (pK k) hp0 hp1
  have h5 := eq_5 M hE k ALG hALG (pK k) hp0.le hp1 r hr
  rw [← hgp, ← hint]
  exact hgame.trans h5
