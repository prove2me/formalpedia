-- Prove2me | solution 1 for SennottDP.ContinuousTime.avgCost_le_of_ineq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:15:12.379988+00:00
-- url     : https://prove2.me/submissions/468ceb73-c52a-40b8-88bd-0e0c94ba7f4c

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory

namespace SennottDP.ContinuousTime.ACI

/-- The mean of the exponential distribution. -/
theorem aci_exp_mean {ν : ℝ} (hν : 0 < ν) :
    ∫⁻ s, ENNReal.ofReal s ∂(expMeasure ν) = ENNReal.ofReal (1 / ν) := by
  unfold expMeasure gammaMeasure
  have hmeas : Measurable (gammaPDF 1 ν) := ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 ν)
  have hmeas2 : Measurable (gammaPDF 2 ν) := ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 2 ν)
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas ENNReal.measurable_ofReal]
  have h : ∀ s, (gammaPDF 1 ν * fun s => ENNReal.ofReal s) s =
      ENNReal.ofReal (1 / ν) * gammaPDF 2 ν s := by
    intro s
    simp only [Pi.mul_apply, gammaPDF, gammaPDFReal]
    by_cases hs : 0 ≤ s
    · rw [if_pos hs, if_pos hs]
      rw [show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero,
        Real.rpow_one, Real.rpow_one, Real.rpow_two, Real.Gamma_one, Real.Gamma_two]
      have he := Real.exp_pos (-(ν * s))
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    · rw [if_neg hs, if_neg hs]; simp
  simp_rw [h]
  rw [lintegral_const_mul _ hmeas2,
    lintegral_gammaPDF_eq_one (by norm_num) hν, mul_one]

variable {S Act : Type} [Countable S]

/-- History-free expected sum for a stationary policy. -/
noncomputable def aciE (Ψ : CTMDC S Act) (e : S → Act) (f : S → Act → ℝ → ℝ≥0∞) :
    ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | n + 1, i => ∫⁻ s, (f i (e i) s + ∑' j, Ψ.P i (e i) j * aciE Ψ e f n j) ∂(expMeasure (Ψ.ν i (e i)))

theorem aci_hist (Ψ : CTMDC S Act) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (f : S → Act → ℝ → ℝ≥0∞) :
    ∀ n k sa t i, CTMDC.expectedSum (Ψ.ofStationary e he) f n k sa t i = aciE Ψ e f n i := by
  intro n
  induction n with
  | zero => intro k sa t i; rfl
  | succ n ih =>
    intro k sa t i
    simp only [CTMDC.expectedSum, ih]
    rw [Finset.sum_eq_single (e i)]
    · simp [CTMDC.ofStationary, aciE]
    · intro a _ ha
      simp [CTMDC.ofStationary, ha]
    · intro h; exact absurd (he i) h

theorem aci_lint (ν : ℝ) (hν : 0 < ν) (A c K : ℝ≥0∞) :
    ∫⁻ s, (A + c * ENNReal.ofReal s + K) ∂(expMeasure ν) = A + c * ENNReal.ofReal (1 / ν) + K := by
  have := isProbabilityMeasure_expMeasure hν
  rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
    lintegral_const_mul _ ENNReal.measurable_ofReal, aci_exp_mean hν]
  simp [lintegral_const, measure_univ]

theorem aci_cost_succ (Ψ : CTMDC S Act) (e : S → Act) (i : S) (hν : 0 < Ψ.ν i (e i)) (n : ℕ) :
    aciE Ψ e Ψ.periodCost (n + 1) i = ENNReal.ofReal (Ψ.G i (e i)) +
      ENNReal.ofReal (Ψ.g i (e i)) * ENNReal.ofReal (Ψ.meanSojourn i (e i)) +
      ∑' j, Ψ.P i (e i) j * aciE Ψ e Ψ.periodCost n j := by
  simp only [aciE, CTMDC.periodCost]
  rw [aci_lint _ hν]
  rfl

theorem aci_time_succ (Ψ : CTMDC S Act) (e : S → Act) (i : S) (hν : 0 < Ψ.ν i (e i)) (n : ℕ) :
    aciE Ψ e (fun _ _ s => ENNReal.ofReal s) (n + 1) i = ENNReal.ofReal (Ψ.meanSojourn i (e i)) +
      ∑' j, Ψ.P i (e i) j * aciE Ψ e (fun _ _ s => ENNReal.ofReal s) n j := by
  simp only [aciE]
  have := aci_lint _ hν 0 1 (∑' j, Ψ.P i (e i) j * aciE Ψ e (fun _ _ s => ENNReal.ofReal s) n j)
  simp only [zero_add, one_mul] at this
  rw [this]
  rfl

end SennottDP.ContinuousTime.ACI

open SennottDP.ContinuousTime SennottDP.ContinuousTime.ACI in
theorem solution {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (Z : ℝ) (z : S → ℝ) (hz : BddBelow (Set.range z)) (h1015 : Ψ.Ineq1015 e Z z) :
    ∀ i, ((Ψ.avgCost (Ψ.ofStationary e he) i : ℝ≥0∞) : EReal) ≤ (Z : EReal) := by
  obtain ⟨-, hpos, hPsum, -⟩ := hΨ
  obtain ⟨htau, ⟨ε0, hε0, hlow⟩, hup⟩ := hCTB
  obtain ⟨m, hm⟩ := hz
  have hmz : ∀ j, m ≤ z j := fun j => hm ⟨j, rfl⟩
  set Cn : ℕ → S → ℝ≥0∞ := aciE Ψ e Ψ.periodCost with hCn
  set Tn : ℕ → S → ℝ≥0∞ := aciE Ψ e (fun _ _ s => ENNReal.ofReal s) with hTn
  have hν : ∀ i, 0 < Ψ.ν i (e i) := fun i => (hpos i (e i) (he i)).2.2
  have hτ : ∀ i, Ψ.meanSojourn i (e i) = 1 / Ψ.ν i (e i) := fun i => rfl
  have hτpos : ∀ i, 0 < Ψ.meanSojourn i (e i) := fun i => by rw [hτ]; exact one_div_pos.mpr (hν i)
  have hτlow : ∀ i, tau + ε0 ≤ Ψ.meanSojourn i (e i) := fun i => hlow i (e i) (he i)
  have hτup : ∀ i, Ψ.meanSojourn i (e i) ≤ B := fun i => hup i (e i) (he i)
  have hPfin : ∀ i j, Ψ.P i (e i) j ≠ ⊤ := fun i j =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((hPsum i (e i) (he i)) ▸ ENNReal.le_tsum j)
  set p : S → S → ℝ := fun i j => (Ψ.P i (e i) j).toReal with hp
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => ENNReal.toReal_nonneg
  have hpsum : ∀ i, ∑' j, p i j = 1 := fun i => by
    rw [hp, ← ENNReal.tsum_toReal_eq (hPfin i), hPsum i (e i) (he i), ENNReal.toReal_one]
  have hpsm : ∀ i, Summable (p i) := fun i =>
    ENNReal.summable_toReal (by rw [hPsum i (e i) (he i)]; exact ENNReal.one_ne_top)
  -- the main induction
  have claim : ∀ n : ℕ, ∀ i, Cn n i ≠ ⊤ ∧ Tn n i ≠ ⊤ ∧ (Tn n i).toReal ≤ n * B ∧
      n * (tau + ε0) ≤ (Tn n i).toReal ∧ (Cn n i).toReal - Z * (Tn n i).toReal ≤ z i - m := by
    intro n
    induction n with
    | zero =>
      intro i
      have hC0 : Cn 0 i = 0 := rfl
      have hT0 : Tn 0 i = 0 := rfl
      simp only [hC0, hT0, ENNReal.toReal_zero, Nat.cast_zero, zero_mul, mul_zero, sub_zero]
      exact ⟨ENNReal.zero_ne_top, ENNReal.zero_ne_top, le_rfl, le_rfl, by linarith [hmz i]⟩
    | succ n ih =>
      intro i
      have hBi : 0 ≤ B := le_trans (hτpos i).le (hτup i)
      have hTj0 : ∀ j, 0 ≤ (Tn n j).toReal := fun j => ENNReal.toReal_nonneg
      -- time
      have hTterm : ∀ j, Ψ.P i (e i) j * Tn n j = ENNReal.ofReal (p i j * (Tn n j).toReal) := by
        intro j
        rw [ENNReal.ofReal_mul (hp0 i j), ENNReal.ofReal_toReal (hPfin i j),
          ENNReal.ofReal_toReal (ih j).2.1]
      have hTsm : Summable (fun j => p i j * (Tn n j).toReal) :=
        Summable.of_nonneg_of_le (fun j => mul_nonneg (hp0 i j) (hTj0 j))
          (fun j => mul_le_mul_of_nonneg_left (ih j).2.2.1 (hp0 i j)) ((hpsm i).mul_right _)
      have hTsum : ∑' j, Ψ.P i (e i) j * Tn n j = ENNReal.ofReal (∑' j, p i j * (Tn n j).toReal) := by
        rw [tsum_congr hTterm, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hp0 i j) (hTj0 j)) hTsm]
      have hTs0 : 0 ≤ ∑' j, p i j * (Tn n j).toReal := tsum_nonneg fun j => mul_nonneg (hp0 i j) (hTj0 j)
      have hTsucc : Tn (n + 1) i = ENNReal.ofReal (Ψ.meanSojourn i (e i) + ∑' j, p i j * (Tn n j).toReal) := by
        rw [hTn, aci_time_succ Ψ e i (hν i) n, ← hTn, hTsum,
          ENNReal.ofReal_add (hτpos i).le hTs0]
      have hTup : ∑' j, p i j * (Tn n j).toReal ≤ n * B := by
        calc ∑' j, p i j * (Tn n j).toReal ≤ ∑' j, p i j * (n * B) :=
              Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (ih j).2.2.1 (hp0 i j)) hTsm
                ((hpsm i).mul_right _)
          _ = n * B := by rw [tsum_mul_right, hpsum i, one_mul]
      have hTlo : n * (tau + ε0) ≤ ∑' j, p i j * (Tn n j).toReal := by
        calc (n : ℝ) * (tau + ε0) = ∑' j, p i j * (n * (tau + ε0)) := by rw [tsum_mul_right, hpsum i, one_mul]
          _ ≤ ∑' j, p i j * (Tn n j).toReal :=
              Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (ih j).2.2.2.1 (hp0 i j))
                ((hpsm i).mul_right _) hTsm
      -- cost
      have hCj : ∀ j, (Cn n j).toReal ≤ z j - m + |Z| * (n * B) := by
        intro j
        have h1 := (ih j).2.2.2.2
        have h2 : Z * (Tn n j).toReal ≤ |Z| * (n * B) := by
          refine (le_abs_self _).trans ?_
          rw [abs_mul, abs_of_nonneg (hTj0 j)]
          exact mul_le_mul_of_nonneg_left (ih j).2.2.1 (abs_nonneg _)
        linarith
      have hCterm : ∀ j, Ψ.P i (e i) j * Cn n j = ENNReal.ofReal (p i j * (Cn n j).toReal) := by
        intro j
        rw [ENNReal.ofReal_mul (hp0 i j), ENNReal.ofReal_toReal (hPfin i j),
          ENNReal.ofReal_toReal (ih j).1]
      have hzsm : Summable (fun j => p i j * z j) := (h1015 i).1
      have hCsm : Summable (fun j => p i j * (Cn n j).toReal) := by
        refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hp0 i j) ENNReal.toReal_nonneg)
          (fun j => mul_le_mul_of_nonneg_left (hCj j) (hp0 i j)) ?_
        have : (fun j => p i j * (z j - m + |Z| * (n * B))) =
            fun j => p i j * z j + p i j * (|Z| * (n * B) - m) := funext fun j => by ring
        rw [this]
        exact hzsm.add ((hpsm i).mul_right _)
      have hCs0 : 0 ≤ ∑' j, p i j * (Cn n j).toReal :=
        tsum_nonneg fun j => mul_nonneg (hp0 i j) ENNReal.toReal_nonneg
      have hCsum : ∑' j, Ψ.P i (e i) j * Cn n j = ENNReal.ofReal (∑' j, p i j * (Cn n j).toReal) := by
        rw [tsum_congr hCterm, ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (hp0 i j) ENNReal.toReal_nonneg) hCsm]
      obtain ⟨hG0, hg0, -⟩ := hpos i (e i) (he i)
      have hCsucc : Cn (n + 1) i = ENNReal.ofReal (Ψ.G i (e i) + Ψ.g i (e i) * Ψ.meanSojourn i (e i) +
          ∑' j, p i j * (Cn n j).toReal) := by
        rw [hCn, aci_cost_succ Ψ e i (hν i) n, ← hCn, hCsum, ← ENNReal.ofReal_mul hg0,
          ← ENNReal.ofReal_add hG0 (mul_nonneg hg0 (hτpos i).le),
          ← ENNReal.ofReal_add (add_nonneg hG0 (mul_nonneg hg0 (hτpos i).le)) hCs0]
      refine ⟨by rw [hCsucc]; exact ENNReal.ofReal_ne_top, by rw [hTsucc]; exact ENNReal.ofReal_ne_top,
        ?_, ?_, ?_⟩
      · rw [hTsucc, ENNReal.toReal_ofReal (add_nonneg (hτpos i).le hTs0)]
        push_cast
        linarith [hτup i]
      · rw [hTsucc, ENNReal.toReal_ofReal (add_nonneg (hτpos i).le hTs0)]
        push_cast
        linarith [hτlow i]
      · rw [hCsucc, hTsucc, ENNReal.toReal_ofReal (add_nonneg (hτpos i).le hTs0),
          ENNReal.toReal_ofReal (add_nonneg (add_nonneg hG0 (mul_nonneg hg0 (hτpos i).le)) hCs0)]
        have hkey : ∑' j, p i j * (Cn n j).toReal - Z * ∑' j, p i j * (Tn n j).toReal ≤
            ∑' j, p i j * z j - m := by
          rw [← tsum_mul_left, ← Summable.tsum_sub hCsm (hTsm.mul_left Z)]
          calc ∑' j, (p i j * (Cn n j).toReal - Z * (p i j * (Tn n j).toReal))
              ≤ ∑' j, (p i j * z j - p i j * m) := by
                refine Summable.tsum_le_tsum (fun j => ?_) (hCsm.sub (hTsm.mul_left Z))
                  (hzsm.sub ((hpsm i).mul_right m))
                have := (ih j).2.2.2.2
                have h3 : p i j * ((Cn n j).toReal - Z * (Tn n j).toReal) ≤ p i j * (z j - m) :=
                  mul_le_mul_of_nonneg_left this (hp0 i j)
                linarith
            _ = ∑' j, p i j * z j - m := by
                rw [Summable.tsum_sub hzsm ((hpsm i).mul_right m), tsum_mul_right, hpsum i, one_mul]
        have h15 := (h1015 i).2
        linarith
  -- conclusion
  intro i
  have hC : ∀ n, CTMDC.expCostN (Ψ.ofStationary e he) n i = Cn n i := fun n =>
    aci_hist Ψ e he _ n 0 Fin.elim0 Fin.elim0 i
  have hT : ∀ n, CTMDC.expTimeN (Ψ.ofStationary e he) n i = Tn n i := fun n =>
    aci_hist Ψ e he _ n 0 Fin.elim0 Fin.elim0 i
  have htε : 0 < tau + ε0 := by linarith
  rcases lt_or_ge Z 0 with hZ | hZ
  · exfalso
    obtain ⟨N, hN⟩ := exists_nat_gt ((z i - m) / ((tau + ε0) * (-Z)))
    obtain ⟨-, -, -, hlo, hcl⟩ := claim N i
    have hC0 : 0 ≤ (Cn N i).toReal := ENNReal.toReal_nonneg
    have hpos' : 0 < (tau + ε0) * (-Z) := mul_pos htε (by linarith)
    rw [div_lt_iff₀ hpos'] at hN
    nlinarith
  · have hlim : CTMDC.avgCost (Ψ.ofStationary e he) i ≤ ENNReal.ofReal Z := by
      refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
      unfold CTMDC.avgCost
      simp only [hC, hT]
      obtain ⟨N, hN⟩ := exists_nat_gt ((z i - m) / ((tau + ε0) * δ))
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [eventually_ge_atTop (N + 1)] with n hn
      obtain ⟨hCf, hTf, -, hlo, hcl⟩ := claim n i
      have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
      have hδ' : (0 : ℝ) < δ := hδ
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hnpos : (0 : ℝ) < n := by linarith
      have hTpos : 0 < (Tn n i).toReal := lt_of_lt_of_le (mul_pos hnpos htε) hlo
      have hbig : z i - m ≤ δ * (Tn n i).toReal := by
        rw [div_lt_iff₀ (mul_pos htε hδ')] at hN
        have h1 : δ * (n * (tau + ε0)) ≤ δ * (Tn n i).toReal := mul_le_mul_of_nonneg_left hlo hδ'.le
        have h2 : (N : ℝ) * ((tau + ε0) * δ) ≤ n * ((tau + ε0) * δ) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_pos htε hδ').le
        nlinarith
      refine ENNReal.div_le_of_le_mul ?_
      rw [← ENNReal.ofReal_toReal hCf, ← ENNReal.ofReal_toReal hTf,
        show (δ : ℝ≥0∞) = ENNReal.ofReal δ from (ENNReal.ofReal_coe_nnreal).symm,
        ← ENNReal.ofReal_add hZ hδ'.le, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    have := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hlim
    rw [EReal.coe_ennreal_ofReal, max_eq_left hZ] at this
    exact this


