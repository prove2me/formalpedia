-- Prove2me | solution 1 for RandomSizeStable.Stability.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T17:00:52.917323+00:00
-- url     : https://prove2.me/submissions/4c1d92db-7d40-47f3-b359-b788ded49bf5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_VotingRule
import Theorems.Thm_RandomSizeStable_Stability_theorem_3
import Theorems.Thm_RandomSizeStable_Stability_lemma_5
import Theorems.Thm_RandomSizeStable_Stability_rank_cut_certificate_dStar

section
set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable

open RandomSizeStable.Stability in
/-- Theorem 1, pp.4 and 15: one ranking-only rule family, chosen before all
profiles and all hidden consistent pseudometrics. Zero optimum is retained. -/
theorem chk_theorem_1 :
    ∃ R : VotingRule,
      (213609 / 100000 : ℝ) < (21361 / 10000 : ℝ) ∧
      ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (E : Election (Fin n) (Fin m)),
        HasDistortionAtMost E (R n m hn hm E).val (213609 / 100000) := by
  classical
  have hex := (RandomSizeStable.Stability.theorem_3 dStar).1
  let hex' : ∀ (n m : ℕ), 0 < n → 0 < m → Election (Fin n) (Fin m) →
      {P : Fin m → ℝ // P ∈ stdSimplex ℝ (Fin m)} := by
    intro n m hn hm E
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact ⟨Classical.choose (hex (Fin n) (Fin m) E),
      (Classical.choose_spec (hex (Fin n) (Fin m) E)).1⟩
  refine ⟨hex', by norm_num, ?_⟩
  intro n m hn hm E
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨b, lam, lo, hi, nu, tau, hC, hb, hphi, hlam, hlam0, hlam1, hJ, hcover, hsupport,
    hmass, htau, htau0, hcut⟩ := RandomSizeStable.Stability.rank_cut_certificate_dStar
  have h5 := (RandomSizeStable.Stability.lemma_5 dStar (113609 / 200000) b hC hb hphi lam hlam
    hlam0 hlam1 lo hi hJ hcover nu hsupport hmass tau htau htau0 hcut (Fin n) (Fin m) E).1
  have hst := Classical.choose_spec (hex (Fin n) (Fin m) E)
  have := h5 _ hst
  have e : (1 + 2 * (113609 / 200000 : ℝ)) = 213609 / 100000 := by norm_num
  rw [e] at this
  exact this

end RandomSizeStable

end

theorem solution : type_of% @RandomSizeStable.chk_theorem_1 := @RandomSizeStable.chk_theorem_1
