-- Prove2me | solution 1 for ServiceParts.Shortfall.repair_count_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:17:14.810983+00:00
-- url     : https://prove2.me/submissions/55acd6b2-99c4-4f8d-a3a7-ac212af94274

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_RepairStock

set_option autoImplicit false

open MeasureTheory

namespace P2M293b

lemma binom_sum_one (p : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  exact Eq.trans (Finset.sum_congr rfl (fun k _ => by ring)) h

end P2M293b

open MeasureTheory ServiceParts.Shortfall in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (lamI lam mu : ℝ) (hlamI : 0 < lamI) (hlamI_le : lamI ≤ lam)
    (hstable : lam < mu) (N Ni : Ω → ℕ) (hN_meas : Measurable N) (hNi_meas : Measurable Ni)
    (hN : ∀ j : ℕ, (P {ω | N ω = j}).toReal = (1 - lam / mu) * (lam / mu) ^ j)
    (hthin : ∀ j k : ℕ, k ≤ j →
      (P {ω | N ω = j ∧ Ni ω = k}).toReal =
        (P {ω | N ω = j}).toReal *
          ((j.choose k : ℝ) * (lamI / lam) ^ k * (1 - lamI / lam) ^ (j - k))) :
    ∀ j : ℕ, (P {ω | Ni ω = j}).toReal = geomPMF (repairEta lamI lam mu) j := by
  intro j
  have hlam : 0 < lam := lt_of_lt_of_le hlamI hlamI_le
  have hmu : 0 < mu := by linarith
  have hmeasT : ∀ n k : ℕ, MeasurableSet {ω | N ω = n ∧ Ni ω = k} := fun n k =>
    (hN_meas (measurableSet_singleton n)).inter (hNi_meas (measurableSet_singleton k))
  -- mass above the diagonal vanishes
  have hzero : ∀ n k : ℕ, n < k → P {ω | N ω = n ∧ Ni ω = k} = 0 := by
    intro n k hnk
    have hAmeas : MeasurableSet {ω | N ω = n ∧ Ni ω ≤ n} :=
      (hN_meas (measurableSet_singleton n)).inter (hNi_meas measurableSet_Iic)
    have hBmeas : MeasurableSet {ω | N ω = n ∧ n < Ni ω} :=
      (hN_meas (measurableSet_singleton n)).inter (hNi_meas measurableSet_Ioi)
    have hAB : {ω | N ω = n} = {ω | N ω = n ∧ Ni ω ≤ n} ∪ {ω | N ω = n ∧ n < Ni ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro h
        rcases le_or_gt (Ni ω) n with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | h)
        · exact h.1
        · exact h.1
    have hdisj : Disjoint {ω | N ω = n ∧ Ni ω ≤ n} {ω | N ω = n ∧ n < Ni ω} :=
      Set.disjoint_left.2 (fun ω h1 h2 => by
        simp only [Set.mem_setOf_eq] at h1 h2
        omega)
    have hA : (P {ω | N ω = n ∧ Ni ω ≤ n}).toReal = (P {ω | N ω = n}).toReal := by
      have hU : {ω | N ω = n ∧ Ni ω ≤ n} =
          ⋃ k ∈ Finset.range (n + 1), {ω | N ω = n ∧ Ni ω = k} := by
        ext ω
        rw [Set.mem_iUnion₂]
        constructor
        · intro h
          obtain ⟨h1, h2⟩ := h
          exact ⟨Ni ω, Finset.mem_range.2 (Nat.lt_succ_of_le h2), h1, rfl⟩
        · rintro ⟨k, hk, h1, h2⟩
          refine ⟨h1, ?_⟩
          have hk' := Finset.mem_range.1 hk
          show Ni ω ≤ n
          rw [h2]; omega
      have hpd : Set.PairwiseDisjoint (↑(Finset.range (n + 1)))
          (fun k : ℕ => {ω | N ω = n ∧ Ni ω = k}) :=
        fun a _ b _ hab => Set.disjoint_left.2 (fun ω h1 h2 => hab (h1.2.symm.trans h2.2))
      rw [hU, measure_biUnion_finset hpd (fun k _ => hmeasT n k),
        ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)]
      rw [Finset.sum_congr rfl (fun k hk => hthin n k (by
        simp only [Finset.mem_range] at hk; omega)), ← Finset.mul_sum, P2M293b.binom_sum_one, mul_one]
    have hsum : P {ω | N ω = n} = P {ω | N ω = n ∧ Ni ω ≤ n} + P {ω | N ω = n ∧ n < Ni ω} := by
      rw [hAB]; exact measure_union hdisj hBmeas
    have hsumR := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hA] at hsumR
    have hB0 : (P {ω | N ω = n ∧ n < Ni ω}).toReal = 0 := by linarith
    have hB : P {ω | N ω = n ∧ n < Ni ω} = 0 :=
      (ENNReal.toReal_eq_zero_iff _).1 hB0 |>.resolve_right (measure_ne_top _ _)
    refine measure_mono_null (fun ω h => ?_) hB
    obtain ⟨h1, h2⟩ := h
    show N ω = n ∧ n < Ni ω
    exact ⟨h1, by rw [h2]; exact hnk⟩
  -- countable additivity over the value of N
  have hU : {ω | Ni ω = j} = ⋃ n : ℕ, {ω | N ω = n ∧ Ni ω = j} := by
    ext ω; simp
  have hPj : (P {ω | Ni ω = j}).toReal = ∑' n : ℕ, (P {ω | N ω = n ∧ Ni ω = j}).toReal := by
    rw [hU, measure_iUnion (fun a b hab => Set.disjoint_left.2
        (fun ω h1 h2 => hab (h1.1.symm.trans h2.1))) (fun n => hmeasT n j),
      ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  -- the negative binomial series
  set f : ℕ → ℝ := fun n => (P {ω | N ω = n ∧ Ni ω = j}).toReal with hf
  have hr : lam / mu * (1 - lamI / lam) = (lam - lamI) / mu := by
    field_simp
  have hr0 : 0 ≤ lam / mu * (1 - lamI / lam) := by
    rw [hr]; exact div_nonneg (by linarith) hmu.le
  have hr1 : lam / mu * (1 - lamI / lam) < 1 := by
    rw [hr, div_lt_one hmu]; linarith
  have hgeo := (hasSum_choose_mul_geometric_of_norm_lt_one j (r := lam / mu * (1 - lamI / lam))
    (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left
      ((1 - lam / mu) * (lam / mu * (lamI / lam)) ^ j)
  have hshift : HasSum (fun m => f (m + j))
      ((1 - lam / mu) * (lam / mu * (lamI / lam)) ^ j *
        (1 / (1 - lam / mu * (1 - lamI / lam)) ^ (j + 1))) := by
    have hfun : (fun m => f (m + j)) = fun i =>
        (1 - lam / mu) * (lam / mu * (lamI / lam)) ^ j *
          (((i + j).choose j : ℝ) * (lam / mu * (1 - lamI / lam)) ^ i) := by
      funext m
      simp only [hf]
      rw [hthin (m + j) j (by omega), hN, Nat.add_sub_cancel]
      rw [mul_pow, mul_pow, pow_add]
      ring
    rw [hfun]; exact hgeo
  have hfull := (hasSum_nat_add_iff j).1 hshift
  have hfin : ∑ i ∈ Finset.range j, f i = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      simp only [Finset.mem_range] at hi
      simp only [hf, hzero i j hi, ENNReal.toReal_zero])
  rw [hfin, add_zero] at hfull
  rw [hPj, hfull.tsum_eq]
  -- algebra
  unfold geomPMF repairEta
  have hD : 0 < mu - lam + lamI := by linarith
  have e1 : lam / mu * (lamI / lam) = lamI / mu := by field_simp
  have e2 : 1 - lam / mu * (1 - lamI / lam) = (mu - lam + lamI) / mu := by field_simp; ring
  have e3 : 1 - lam / mu = (mu - lam) / mu := by field_simp
  have e4 : 1 - lamI / (mu - lam + lamI) = (mu - lam) / (mu - lam + lamI) := by
    field_simp; ring
  rw [e1, e2, e3, e4, div_pow, div_pow, div_pow]
  field_simp
  ring
