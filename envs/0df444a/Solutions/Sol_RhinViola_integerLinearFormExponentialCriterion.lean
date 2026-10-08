-- Prove2me | solution 1 for RhinViola.integerLinearFormExponentialCriterion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:22:55.698393+00:00
-- url     : https://prove2.me/submissions/d0cc4efb-6394-4321-b83e-94ed2639a394

import Theorems.Thm_RhinViola_existsExponentSlack
import Theorems.Thm_RhinViola_ceilLogIndexBounds
import Theorems.Thm_RhinViola_ceilLogIndexEventuallyGe
import Theorems.Thm_RhinViola_coefficientNonzeroOfSmallLinearForm
import Theorems.Thm_RhinViola_selectedIndexErrorLowerBound
import Theorems.Thm_RhinViola_ceilIndexPowerLowerBound
import Theorems.Thm_RhinViola_eventuallyAbsorbPositiveConstant
import Mathlib.Tactic

theorem solution
    (α σ ρ ε : ℝ) (a b : ℕ → ℤ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hbounds : ∀ δ : ℝ, 0 < δ → δ < σ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        let f : ℝ := (a n : ℝ) - (b n : ℝ) * α
        f ≠ 0 ∧
        Real.exp (-((σ + δ) * (n : ℝ))) ≤ |f| ∧
        |f| ≤ Real.exp (-((σ - δ) * (n : ℝ))) ∧
        |(b n : ℝ)| ≤ Real.exp ((ρ + δ) * (n : ℝ))) :
    ∃ Q : ℕ, ∀ p : ℤ, ∀ q : ℕ, Q ≤ q → 0 < q →
      (q : ℝ) ^ (-(1 + ρ / σ + ε)) <
        |α - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨δ, hδ, hδσ, hslack⟩ :=
    RhinViola.existsExponentSlack σ ρ ε hσ hρ hε
  let u : ℝ := σ - δ
  let v : ℝ := σ + δ
  let w : ℝ := ρ + δ
  let c : ℝ := v + w
  let E : ℝ := c / u
  let T : ℝ := 1 + ρ / σ + ε
  have hu : 0 < u := by
    dsimp [u]
    exact sub_pos.mpr hδσ
  have hc : 0 < c := by
    dsimp [c, v, w]
    nlinarith
  have hET : E < T := by
    dsimp [E, T, c, v, w, u]
    convert hslack using 1 <;> ring
  obtain ⟨N, hN⟩ := hbounds δ hδ hδσ
  obtain ⟨Qidx, hQidx⟩ :=
    RhinViola.ceilLogIndexEventuallyGe u (max N 1) hu
  let C : ℝ := Real.exp (-c) * (2 : ℝ) ^ (-E)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨Qabs, hQabs⟩ :=
    RhinViola.eventuallyAbsorbPositiveConstant C E T hC hET
  refine ⟨max Qidx Qabs, ?_⟩
  intro p q hQq hq
  have hQidxq : Qidx ≤ q :=
    le_trans (Nat.le_max_left Qidx Qabs) hQq
  have hQabsq : Qabs ≤ q :=
    le_trans (Nat.le_max_right Qidx Qabs) hQq
  let n : ℕ := ⌈Real.log (2 * (q : ℝ)) / u⌉₊
  have hmaxN : max N 1 ≤ n := by
    dsimp [n]
    exact hQidx q hQidxq hq
  have hNn : N ≤ n :=
    le_trans (Nat.le_max_left N 1) hmaxN
  have hone : 1 ≤ n :=
    le_trans (Nat.le_max_right N 1) hmaxN
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one hone
  let f : ℝ := (a n : ℝ) - (b n : ℝ) * α
  have hbds := hN n hNn
  change f ≠ 0 ∧
      Real.exp (-(v * (n : ℝ))) ≤ |f| ∧
      |f| ≤ Real.exp (-(u * (n : ℝ))) ∧
      |(b n : ℝ)| ≤ Real.exp (w * (n : ℝ)) at hbds
  rcases hbds with ⟨hfnz, hflow, hfup, hbup⟩
  have hceil := RhinViola.ceilLogIndexBounds u q hu hq
  change Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ) ∧
      (n : ℝ) < Real.log (2 * (q : ℝ)) / u + 1 at hceil
  rcases hceil with ⟨hnlower, hnupper⟩
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hnpos
  have hneg : -(u * (n : ℝ)) < 0 := by
    exact neg_lt_zero.mpr (mul_pos hu hnR)
  have hexplt : Real.exp (-(u * (n : ℝ))) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hneg
  have hfsmall : |f| < 1 :=
    lt_of_le_of_lt hfup hexplt
  have hf_eq : f = (a n : ℝ) - (b n : ℝ) * α := rfl
  have hbne : b n ≠ 0 :=
    RhinViola.coefficientNonzeroOfSmallLinearForm
      α f (a n) (b n) hf_eq hfnz hfsmall
  have herr :
      Real.exp (-(c * (n : ℝ))) ≤
        |α - (p : ℝ) / (q : ℝ)| := by
    dsimp [c]
    exact RhinViola.selectedIndexErrorLowerBound
      α f u v w (a n) (b n) p q n
      hq hbne hu hf_eq hnlower hfup hflow hbup
  have hpower :
      C * (q : ℝ) ^ (-E) <
        Real.exp (-(c * (n : ℝ))) := by
    have hpower_raw := RhinViola.ceilIndexPowerLowerBound
      u c q n hu hc hq hnupper
    simpa [C, E, mul_assoc] using hpower_raw
  have habsorb :
      (q : ℝ) ^ (-T) < C * (q : ℝ) ^ (-E) :=
    hQabs q hQabsq hq
  have hfinal :
      (q : ℝ) ^ (-T) <
        |α - (p : ℝ) / (q : ℝ)| :=
    lt_of_lt_of_le (lt_trans habsorb hpower) herr
  simpa [T] using hfinal
