-- Prove2me | solution 1 for PPSLattice.corollary_4_30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sora
-- created : 2026-11-15T07:41:27.077739+00:00
-- url     : https://prove2.me/submissions/d03b4e46-659c-4d77-a3e5-0b3f387ec510
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PPSLattice_lwe_regime_implies_owf
import Theorems.Thm_PPSLattice_construction46_finite_coin_realization
import Theorems.Thm_PPSLattice_homomorphic_evaluation
import Theorems.Thm_PPSLattice_claim_4_11
import Theorems.Thm_PPSLattice_theorem_4_3
import Theorems.Thm_PPSLattice_theorem_4_5
import Theorems.Thm_PPSLattice_theorem_4_13
import Theorems.Thm_PPSLattice_theorem_4_26

open QAlgorithms.Complexity PPSLattice
set_option autoImplicit false

private theorem negligible_of_le_add {f g h : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : NoisyOWMPC.Negligible g)
    (hh : NoisyOWMPC.Negligible h) (hbound : ∀ n, f n ≤ g n + h n) :
    NoisyOWMPC.Negligible f := by
  refine ⟨hf, ?_⟩
  intro c hc
  obtain ⟨ng, hng⟩ := hg.2 (c + 1) (by linarith)
  obtain ⟨nh, hnh⟩ := hh.2 (c + 1) (by linarith)
  refine ⟨max 2 (max ng nh), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hng' : ng ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnh' : nh ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpow : (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(c + 1)) * n := by
    calc
      (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(c + 1) + 1) := by congr 1; ring
      _ = (n : ℝ) ^ (-(c + 1)) * (n : ℝ) ^ (1 : ℝ) := Real.rpow_add hnpos _ _
      _ = _ := by rw [Real.rpow_one]
  have hp : 0 ≤ (n : ℝ) ^ (-(c + 1)) := Real.rpow_nonneg (le_of_lt hnpos) _
  calc
    f n ≤ g n + h n := hbound n
    _ ≤ (n : ℝ) ^ (-(c + 1)) + (n : ℝ) ^ (-(c + 1)) :=
      add_le_add (hng n hng') (hnh n hnh')
    _ ≤ (n : ℝ) ^ (-c) := by rw [hrpow]; nlinarith

private theorem game_security_transfer (payload : Bool) (E I : PPS)
    (hI : ∀ A : RestrictedDec.Adversary, A.Valid →
      NoisyOWMPC.Negligible (fun lam ↦ |((ppsGame payload I A lam) true).toReal - 1 / 2|))
    (hsim : ∀ A : RestrictedDec.Adversary, A.Valid →
      ∃ B : RestrictedDec.Adversary, B.Valid ∧
        NoisyOWMPC.Negligible (fun lam ↦
          |((ppsGame payload E A lam) true).toReal -
            ((ppsGame payload I B lam) true).toReal|)) :
    ∀ A : RestrictedDec.Adversary, A.Valid →
      NoisyOWMPC.Negligible (fun lam ↦ |((ppsGame payload E A lam) true).toReal - 1 / 2|) := by
  intro A hA
  obtain ⟨B, hB, hgap⟩ := hsim A hA
  apply negligible_of_le_add (fun _ ↦ abs_nonneg _) hgap (hI B hB)
  intro lam
  exact abs_sub_le _ _ _

theorem solution (ε : ℝ) (q χ : ℕ → ℕ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hreg : LWERegime ε q χ) (hLWE : LWEHard q χ) :
    ∃ E : PPS, E.Efficient ∧ E.Correct ∧ E.FullyCompact ∧ E.ModeInd ∧ E.PayloadHiding ∧
      E.PkUniform := by
  have hOWF := lwe_regime_implies_owf ε q χ hε hε2 hreg hLWE
  obtain ⟨H, c, hHe, hH⟩ := homomorphic_evaluation
  obtain ⟨K, sC, _, hK, _⟩ := claim_4_11
  obtain ⟨F, hFe, hF, _⟩ := theorem_4_3 hOWF
  obtain ⟨G, hGe, hG, _⟩ := theorem_4_5 hOWF
  obtain ⟨P, E, hP, hPLWE, hEe, hEc, hEcompact, hEu, hsim⟩ :=
    construction46_finite_coin_realization ε q χ hε hε2 hreg hLWE
      H c hHe hH K sC hK F hFe hF G hGe hG
  have hmode := theorem_4_13 H c hHe hH P hP K sC hK F hFe hF G hGe hG hPLWE
  have hpayload := theorem_4_26 H c hHe hH P hP K sC hK F hFe hF G hGe hG hPLWE
  exact ⟨E, hEe, hEc, hEcompact,
    game_security_transfer false E _ hmode (hsim false),
    game_security_transfer true E _ hpayload (hsim true), hEu⟩
