-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P07.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:24:50.816451+00:00
-- url     : https://prove2.me/submissions/4b22fa0d-2fef-41e1-925e-1aebb82209cf

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07
noncomputable section

open Filter

open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P07

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

theorem g58b_diag {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (rho : TC.State b) :
    (∀ k, 0 ≤ (inner ℂ (b k) (rho.val.val (b k))).re) ∧
    Summable (fun k => (inner ℂ (b k) (rho.val.val (b k))).re) ∧
    ∑' k, (inner ℂ (b k) (rho.val.val (b k))).re = 1 := by
  obtain ⟨⟨_, hpos⟩, htr⟩ := rho.property
  have hs : Summable (fun k => inner ℂ (b k) (rho.val.val (b k))) := by
    by_contra h
    have := tsum_eq_zero_of_not_summable h
    unfold QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace at htr
    rw [this] at htr; exact zero_ne_one htr
  refine ⟨fun k => hpos _, hs.mapL Complex.reCLM, ?_⟩
  have := Complex.re_tsum hs
  unfold QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace at htr
  rw [← this, htr]; simp

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (rho : TC.State b) (E : ℝ) (m : ℕ) (hm : 0 < m)
    (henergy : TC.spectralEnergy b S.levels rho ≤ ENNReal.ofReal E)
    (hbudget : groundEnergy S ≤ E) :
    ((S.levels m : ℝ) - groundEnergy S) * truncationTail b rho m ≤
        E - groundEnergy S ∧
    (0 < (S.levels m : ℝ) - groundEnergy S →
      truncationTail b rho m ≤
        (E - groundEnergy S) / ((S.levels m : ℝ) - groundEnergy S)) := by
  set p : ℕ → ℝ := fun k => (inner ℂ (b k) (rho.val.val (b k))).re with hpdef
  obtain ⟨hp0, hps, hp1⟩ := g58b_diag b rho
  have hE0 : 0 ≤ groundEnergy S := by unfold groundEnergy; exact NNReal.coe_nonneg _
  have hEnn : 0 ≤ E := hE0.trans hbudget
  -- energy series
  set q : ℕ → ℝ≥0 := fun k => S.levels k * (p k).toNNReal with hq
  have hqe : TC.spectralEnergy b S.levels rho = ∑' k, (q k : ℝ≥0∞) := by
    unfold TC.spectralEnergy
    rfl
  have hqfin : ∑' k, (q k : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hqe ▸ henergy)
  have hqs : Summable q := ENNReal.tsum_coe_ne_top_iff_summable.mp hqfin
  have hqr : Summable (fun k => (q k : ℝ)) := NNReal.summable_coe.mpr hqs
  have hqval : ∀ k, (q k : ℝ) = (S.levels k : ℝ) * p k := by
    intro k; simp only [q, NNReal.coe_mul, p, Real.coe_toNNReal _ (hp0 k)]
  have hqle : ∑' k, (q k : ℝ) ≤ E := by
    have h1 : ENNReal.ofReal (∑' k, (q k : ℝ)) ≤ ENNReal.ofReal E := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => NNReal.coe_nonneg _) hqr]
      simpa [ENNReal.ofReal_coe_nnreal, ← hqe] using henergy
    exact (ENNReal.ofReal_le_ofReal_iff hEnn).mp h1
  have hlev : ∀ k, groundEnergy S ≤ S.levels k := by
    intro k; unfold groundEnergy; exact_mod_cast S.ordered (Nat.zero_le k)
  have main : ((S.levels m : ℝ) - groundEnergy S) * truncationTail b rho m ≤
      E - groundEnergy S := by
    unfold truncationTail
    rw [← tsum_mul_left]
    have hsum2 : Summable (fun k => ((S.levels k : ℝ) - groundEnergy S) * p k) := by
      have := hqr.sub (hps.mul_left (groundEnergy S))
      refine this.congr (fun k => ?_)
      rw [hqval]; ring
    calc ∑' k, ((S.levels m : ℝ) - groundEnergy S) *
            (if m ≤ k then (inner ℂ (b k) (rho.val.val (b k))).re else 0)
        ≤ ∑' k, ((S.levels k : ℝ) - groundEnergy S) * p k := by
          refine Summable.tsum_le_tsum (fun k => ?_) ?_ hsum2
          · by_cases hk : m ≤ k
            · simp only [hk, if_true]
              have : (S.levels m : ℝ) ≤ S.levels k := by exact_mod_cast S.ordered hk
              exact mul_le_mul_of_nonneg_right (by linarith) (hp0 k)
            · simp only [hk, if_false, mul_zero]
              exact mul_nonneg (by linarith [hlev k]) (hp0 k)
          · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hps.mul_left
              ((S.levels m : ℝ) - groundEnergy S))
            · split_ifs
              · exact mul_nonneg (by linarith [hlev m]) (hp0 k)
              · simp
            · split_ifs
              · exact le_rfl
              · simp only [mul_zero]; exact mul_nonneg (by linarith [hlev m]) (hp0 k)
      _ = ∑' k, (q k : ℝ) - groundEnergy S * ∑' k, p k := by
          rw [← tsum_mul_left, ← Summable.tsum_sub hqr (hps.mul_left _)]
          congr 1; funext k; rw [hqval]; ring
      _ ≤ E - groundEnergy S := by rw [hp1]; linarith
  refine ⟨main, fun hpos => ?_⟩
  rw [le_div_iff₀ hpos]; linarith [main]
