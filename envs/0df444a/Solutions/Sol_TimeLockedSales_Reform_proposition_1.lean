-- Prove2me | solution 1 for TimeLockedSales.Reform.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:46:45.717579+00:00
-- url     : https://prove2.me/submissions/a25a76c7-4131-4f14-abb6-38b875f71499

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

open TimeLockedSales.Reform in
theorem solution (P : Params) (hS : P.Standing)
    {M : Type} [Fintype M] (σ : InfoPolicy M) (t : ℕ) (ht : t < P.T) (m : M)
    (hm : 0 < msgProb P σ t m) :
    vStar P < P.p ∧ P.p < vStarStar P ∧
    (vStarStar P ≤ msgPosterior P σ t m →
      ∀ s : Bool, buysAt P σ t (law P σ t) s m) ∧
    (vStar P ≤ msgPosterior P σ t m →
      msgPosterior P σ t m < vStarStar P →
      ∀ s : Bool, (buysAt P σ t (law P σ t) s m ↔ s = true)) ∧
    (msgPosterior P σ t m < vStar P →
      ∀ s : Bool, ¬ buysAt P σ t (law P σ t) s m) := by
  obtain ⟨hp0, hp1, hq0, hq1, _, _⟩ := hS
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ h, law P σ t true h * σ.σ t h m := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ h, law P σ t false h * σ.σ t h m := ⟨_, rfl⟩
  have hmp : msgProb P σ t m = A + B := by
    unfold msgProb; rw [Fintype.sum_bool, hA, hB]
  have hAB : 0 < A + B := hmp ▸ hm
  have hpost : msgPosterior P σ t m = A / (A + B) := by
    unfold msgPosterior; rw [hmp, hA]
  have hsum : ∀ v s, ∑ h, law P σ t v h * σ.σ t h m * sigLik P v s =
      (∑ h, law P σ t v h * σ.σ t h m) * sigLik P v s := fun v s => (Finset.sum_mul _ _ _).symm
  have hbuy : ∀ s, buysAt P σ t (law P σ t) s m ↔
      P.p * (A * sigLik P true s + B * sigLik P false s) ≤ A * sigLik P true s := by
    intro s
    unfold buysAt
    rw [Fintype.sum_bool]
    simp only [hsum]
    rw [← hA, ← hB]
  have hTT : sigLik P true true = P.q := by simp [sigLik]
  have hFT : sigLik P false true = 1 - P.q := by simp [sigLik]
  have hTF : sigLik P true false = 1 - P.q := by simp [sigLik]
  have hFF : sigLik P false false = P.q := by simp [sigLik]
  set π := msgPosterior P σ t m with hπ
  have hD1 : 0 < P.p * (1 - P.q) + (1 - P.p) * P.q := by nlinarith
  have hD2 : 0 < P.p * P.q + (1 - P.p) * (1 - P.q) := by nlinarith
  have hbT : buysAt P σ t (law P σ t) true m ↔ vStar P ≤ π := by
    rw [hbuy, hTT, hFT, hpost]
    unfold vStar
    rw [div_le_div_iff₀ hD1 hAB]
    constructor <;> intro h <;> nlinarith
  have hbF : buysAt P σ t (law P σ t) false m ↔ vStarStar P ≤ π := by
    rw [hbuy, hTF, hFF, hpost]
    unfold vStarStar
    rw [div_le_div_iff₀ hD2 hAB]
    constructor <;> intro h <;> nlinarith
  have h1 : vStar P < P.p := by
    unfold vStar
    rw [div_lt_iff₀ hD1]
    nlinarith [mul_pos hp0 (by linarith : (0:ℝ) < 1 - P.p)]
  have h2 : P.p < vStarStar P := by
    unfold vStarStar
    rw [lt_div_iff₀ hD2]
    nlinarith [mul_pos hp0 (by linarith : (0:ℝ) < 1 - P.p)]
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro hv s
    cases s
    · exact hbF.mpr hv
    · exact hbT.mpr (by linarith)
  · intro hv1 hv2 s
    cases s
    · simp only [Bool.false_eq_true, iff_false]
      intro hb
      have := hbF.mp hb
      linarith
    · simp only [iff_true]
      exact hbT.mpr hv1
  · intro hv s
    cases s
    · intro hb
      have := hbF.mp hb
      linarith
    · intro hb
      have := hbT.mp hb
      linarith
