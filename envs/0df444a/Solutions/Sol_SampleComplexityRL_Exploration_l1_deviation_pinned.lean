-- Prove2me | solution 1 for SampleComplexityRL.Exploration.l1_deviation_pinned
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:04:23.057677+00:00
-- url     : https://prove2.me/submissions/7526ea05-7d43-4e6e-bf9d-df0f7224d185

import Mathlib
import Definitions.Def_SampleComplexityRL_Exploration_Empirical

set_option autoImplicit false
open MeasureTheory ProbabilityTheory SampleComplexityRL.Exploration

namespace SCRL1

noncomputable def ind {N : ℕ} (B : Finset (Fin N)) (x : Fin N) : ℝ := if x ∈ B then 1 else 0

theorem mean_ind {N : ℕ} (μ : Measure (Fin N)) [IsProbabilityMeasure μ] (B : Finset (Fin N)) :
    ∫ x, ind B x ∂μ = ∑ i ∈ B, (μ {i}).toReal := by
  rw [integral_fintype Integrable.of_finite]
  simp only [ind, smul_eq_mul, mul_ite, mul_one, mul_zero, Measure.real]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem emp_sum {N m : ℕ} (hm : 0 < m) (ω : Fin m → Fin N) (B : Finset (Fin N)) :
    ∑ i ∈ B, empiricalDist ω i = (∑ j, ind B (ω j)) / m := by
  unfold empiricalDist
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.card_filter, ind]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq]

theorem emp_sum_univ {N m : ℕ} (hm : 0 < m) (ω : Fin m → Fin N) :
    ∑ i, empiricalDist ω i = 1 := by
  rw [emp_sum hm ω Finset.univ]
  have : ∀ j, ind (Finset.univ : Finset (Fin N)) (ω j) = 1 := by intro j; simp [ind]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem pm_mean {N m : ℕ} (μ : Measure (Fin N)) [IsProbabilityMeasure μ] (B : Finset (Fin N))
    (j : Fin m) :
    ∫ ω, ind B (ω j) ∂(Measure.pi fun _ : Fin m => μ) = ∑ i ∈ B, (μ {i}).toReal := by
  rw [← mean_ind μ B]
  have h := (measurePreserving_eval (fun _ : Fin m => μ) j).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (measurable_pi_apply j).aemeasurable]
  exact (measurable_of_finite _).aestronglyMeasurable

theorem hoeffding_subset {N m : ℕ} (μ : Measure (Fin N)) [IsProbabilityMeasure μ]
    (B : Finset (Fin N)) (hm : 0 < m) (ε : ℝ) (hε0 : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m => μ).real
      {ω | (m : ℝ) * ε / 2 ≤ ∑ j, (ind B (ω j) - ∑ i ∈ B, (μ {i}).toReal)}
      ≤ Real.exp (-((m : ℝ) * ε ^ 2 / 2)) := by
  set pB := ∑ i ∈ B, (μ {i}).toReal with hpB
  have hind : iIndepFun (fun (j : Fin m) (ω : Fin m → Fin N) => ind B (ω j) - pB)
      (Measure.pi fun _ : Fin m => μ) :=
    iIndepFun_pi (μ := fun _ : Fin m => μ) (X := fun _ x => ind B x - pB)
      (fun _ => (measurable_of_finite _).aemeasurable)
  have hsub : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω : Fin m → Fin N => ind B (ω j) - pB)
        ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (Measure.pi fun _ : Fin m => μ) := by
    intro j _
    have := hasSubgaussianMGF_of_mem_Icc (μ := Measure.pi fun _ : Fin m => μ)
      (X := fun ω : Fin m → Fin N => ind B (ω j)) (a := 0) (b := 1)
      ((measurable_of_finite _).aemeasurable)
      (ae_of_all _ (fun ω => by unfold ind; split_ifs <;> simp))
    rw [pm_mean μ B j] at this
    exact this
  have hε : 0 ≤ (m : ℝ) * ε / 2 := by positivity
  have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (c := fun _ => (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) hsub hε
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  convert this using 2
  push_cast
  simp
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp


theorem sum_mu_one {N : ℕ} (μ : Measure (Fin N)) [IsProbabilityMeasure μ] :
    ∑ i, (μ {i}).toReal = 1 := by
  have h := mean_ind μ Finset.univ
  have e : ∀ x : Fin N, ind (Finset.univ : Finset (Fin N)) x = 1 := by intro x; simp [ind]
  simp only [e] at h
  rw [integral_const] at h
  simpa using h.symm

theorem bad_subset {N m : ℕ} (μ : Measure (Fin N)) [IsProbabilityMeasure μ] (hm : 0 < m)
    (ε : ℝ) (ω : Fin m → Fin N) (hbad : ε < ∑ i, |empiricalDist ω i - (μ {i}).toReal|) :
    ∃ B : Finset (Fin N), (m : ℝ) * ε / 2 ≤
      ∑ j, (ind B (ω j) - ∑ i ∈ B, (μ {i}).toReal) := by
  classical
  set d : Fin N → ℝ := fun i => empiricalDist ω i - (μ {i}).toReal with hd
  have hsum0 : ∑ i, d i = 0 := by
    simp only [hd, Finset.sum_sub_distrib, emp_sum_univ hm ω, sum_mu_one]; norm_num
  refine ⟨Finset.univ.filter (fun i => 0 < d i), ?_⟩
  set B := Finset.univ.filter (fun i => 0 < d i) with hB
  have habs : ∑ i, |d i| = 2 * ∑ i ∈ B, d i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < d i)]
    have h1 : ∑ i ∈ B, |d i| = ∑ i ∈ B, d i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hB, Finset.mem_filter] at hi
      exact abs_of_pos hi.2
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < d i), |d i|
        = - ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < d i), d i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      exact abs_of_nonpos (not_lt.mp hi.2)
    have h3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < d i) d
    rw [h1, h2]
    linarith
  have hc : ∑ j, (ind B (ω j) - ∑ i ∈ B, (μ {i}).toReal) = (m : ℝ) * ∑ i ∈ B, d i := by
    have h1 : ∑ i ∈ B, d i = (∑ j, ind B (ω j)) / m - ∑ i ∈ B, (μ {i}).toReal := by
      simp only [hd, Finset.sum_sub_distrib, emp_sum hm ω B]
    rw [h1, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [hc]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have : ε / 2 ≤ ∑ i ∈ B, d i := by
    have : ε < 2 * ∑ i ∈ B, d i := by rw [← habs]; exact hbad
    linarith
  calc (m : ℝ) * ε / 2 = (m : ℝ) * (ε / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hm0.le

theorem numeric (N m : ℕ) (hN : 0 < N) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 8 * (N : ℝ) / ε ^ 2 * Real.log (2 * N / δ) ≤ m) :
    (2 : ℝ) ^ N * Real.exp (-((m : ℝ) * ε ^ 2 / 2)) < δ := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hq : (1 : ℝ) < 2 * N / δ := by
    rw [lt_div_iff₀ hδ0]; linarith
  have hL : 0 < Real.log (2 * N / δ) := Real.log_pos hq
  set L := Real.log (2 * N / δ) with hLdef
  have h1 : 4 * (N : ℝ) * L ≤ (m : ℝ) * ε ^ 2 / 2 := by
    have : 8 * (N : ℝ) / ε ^ 2 * L * ε ^ 2 ≤ m * ε ^ 2 :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    have e : 8 * (N : ℝ) / ε ^ 2 * L * ε ^ 2 = 8 * N * L := by field_simp
    rw [e] at this
    linarith
  set u := δ / (2 * N) with hu
  have hu0 : 0 < u := by positivity
  have huhalf : u ≤ δ / 2 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hexp : Real.exp (-L) = u := by
    rw [Real.exp_neg, hLdef, Real.exp_log (by positivity), hu]
    field_simp
  have h2 : Real.exp (-((m : ℝ) * ε ^ 2 / 2)) ≤ u ^ (4 * N) := by
    calc Real.exp (-((m : ℝ) * ε ^ 2 / 2)) ≤ Real.exp (-(4 * (N : ℝ) * L)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = u ^ (4 * N) := by
          rw [← hexp, ← Real.exp_nat_mul]
          congr 1
          push_cast; ring
  have h3 : (2 : ℝ) ^ N * u ^ (4 * N) = (2 * u ^ 4) ^ N := by
    rw [mul_pow, ← pow_mul]
  have hu1 : u ≤ 1 / 2 := by linarith
  have h4 : 2 * u ^ 4 ≤ 1 := by
    have : u ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ hu0.le hu1 4
    nlinarith
  have h5 : (2 * u ^ 4) ^ N ≤ 2 * u ^ 4 :=
    pow_le_of_le_one (by positivity) h4 (by omega)
  have h6 : 2 * u ^ 4 < δ := by
    have : u ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hu0.le hu1 3
    have : 2 * u ^ 4 = u * (2 * u ^ 3) := by ring
    nlinarith
  calc (2 : ℝ) ^ N * Real.exp (-((m : ℝ) * ε ^ 2 / 2))
      ≤ (2 : ℝ) ^ N * u ^ (4 * N) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * u ^ 4) ^ N := h3
    _ ≤ 2 * u ^ 4 := h5
    _ < δ := h6

end SCRL1

theorem solution (N m : ℕ) (hN : 0 < N) (μ : Measure (Fin N))
    [IsProbabilityMeasure μ] (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 8 * (N : ℝ) / ε ^ 2 * Real.log (2 * N / δ) ≤ m) :
    ENNReal.ofReal (1 - δ) <
      (Measure.pi fun _ : Fin m => μ)
        {ω | ∑ i, |empiricalDist ω i - (μ {i}).toReal| ≤ ε} := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : (1 : ℝ) < 2 * N / δ := by
    rw [lt_div_iff₀ hδ0]; linarith
  have hL : 0 < Real.log (2 * N / δ) := Real.log_pos hq
  have hmr : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmr
  set Pm := Measure.pi fun _ : Fin m => μ with hPm
  set target : Set (Fin m → Fin N) := {ω | ∑ i, |empiricalDist ω i - (μ {i}).toReal| ≤ ε} with htg
  have htm : MeasurableSet target := (Set.toFinite _).measurableSet
  have hcompl : targetᶜ ⊆ ⋃ B : Finset (Fin N), {ω : Fin m → Fin N | (m : ℝ) * ε / 2 ≤
      ∑ j, (SCRL1.ind B (ω j) - ∑ i ∈ B, (μ {i}).toReal)} := by
    intro ω hω
    simp only [htg, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    obtain ⟨B, hB⟩ := SCRL1.bad_subset μ hm0 ε ω hω
    exact Set.mem_iUnion.mpr ⟨B, hB⟩
  have hbad : Pm.real targetᶜ < δ := by
    calc Pm.real targetᶜ ≤ Pm.real (⋃ B : Finset (Fin N), {ω : Fin m → Fin N | (m : ℝ) * ε / 2 ≤
          ∑ j, (SCRL1.ind B (ω j) - ∑ i ∈ B, (μ {i}).toReal)}) :=
          measureReal_mono hcompl
      _ ≤ ∑ B : Finset (Fin N), Pm.real {ω : Fin m → Fin N | (m : ℝ) * ε / 2 ≤
          ∑ j, (SCRL1.ind B (ω j) - ∑ i ∈ B, (μ {i}).toReal)} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ B : Finset (Fin N), Real.exp (-((m : ℝ) * ε ^ 2 / 2)) :=
          Finset.sum_le_sum (fun B _ => SCRL1.hoeffding_subset μ B hm0 ε hε.le)
      _ = (2 : ℝ) ^ N * Real.exp (-((m : ℝ) * ε ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]; push_cast; ring
      _ < δ := SCRL1.numeric N m hN ε δ hε hδ0 hδ1 hm
  have hreal : 1 - δ < Pm.real target := by
    have := probReal_compl_eq_one_sub htm (μ := Pm)
    linarith
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)]
  exact hreal
