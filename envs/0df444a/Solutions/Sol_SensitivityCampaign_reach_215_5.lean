-- Prove2me | solution 5 for SensitivityCampaign.reach_215
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T07:56:43.866079+00:00
-- url     : https://prove2.me/submissions/1199b6c8-445f-4ecb-9618-3199c5a1f9f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityCampaign_endpoint22_exact_profile_rate
import Theorems.Thm_SensitivityGraphLocal_exists_215_success
import Theorems.Thm_SensitivityGraphLocal_succeeds_eq
import Theorems.Thm_SensitivityGraphCheck_search_iff_word
import Theorems.Thm_SensitivityVariableWord_certificate_iff_word
import Theorems.Thm_SensitivityProfileCycle_finite_seeds
import Theorems.Thm_SensitivityCampaign_finite_certificate_rational

open OAI.Paper320

/-- A fixed overhead in the sensitivity bound costs no exponent, even
when the two integer growth rates meet exactly. -/
private theorem endpoint_of_geometric_seeds (C R G p q : ℕ)
    (hR : 1 < R) (hG : 1 < G) (hq : 0 < q) (hRG : R ^ p ≤ G ^ q)
    (seeds : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ C * R ^ m ∧ G ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent ((p : ℝ) / q) := by
  intro ε hε S hS
  let a : ℝ := (p : ℝ) / q
  obtain ⟨j, hj⟩ := exists_nat_gt (a / ε)
  let k : ℕ := j + 1
  let d : ℕ := C.log2 + 1
  have hk : 0 < k := Nat.succ_pos _
  have hd : 0 < d := Nat.succ_pos _
  have hC : C ≤ R ^ d := (Nat.lt_log2_self (n := C)).le.trans
    (Nat.pow_le_pow_left hR d)
  obtain ⟨n, f, hs, hb⟩ := seeds (k * d)
  have hs' : sensitivity f ≤ R ^ ((k + 1) * d) := calc
    sensitivity f ≤ C * R ^ (k * d) := hs
    _ ≤ R ^ d * R ^ (k * d) := Nat.mul_le_mul_right _ hC
    _ = R ^ ((k + 1) * d) := by
      rw [← Nat.pow_add]
      exact congrArg (R ^ ·) ((Nat.add_comm d (k * d)).trans (by
        rw [Nat.add_mul k 1 d, Nat.one_mul]))
  have hbudget : (R ^ ((k + 1) * d)) ^ (p * k) ≤
      (G ^ (k * d)) ^ (q * (k + 1)) := calc
    _ = (R ^ p) ^ (k * ((k + 1) * d)) := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      congr 1 <;> ac_rfl
    _ ≤ (G ^ q) ^ (k * ((k + 1) * d)) := Nat.pow_le_pow_left hRG _
    _ = _ := by
      rw [← Nat.pow_mul, ← Nat.pow_mul]
      congr 1 <;> ac_rfl
  have hscore := SensitivityCampaign.finite_certificate_rational f (fun _ => false)
    (R ^ ((k + 1) * d)) (G ^ (k * d)) (p * k) (q * (k + 1))
    (one_lt_pow₀ hR (by positivity)) (one_lt_pow₀ hG (by positivity))
    (by positivity) hs' hb hbudget
  have hδ : 0 < ε - a / ((k : ℝ) + 1) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity)).mpr
    calc
      a < (j : ℝ) * ε := (div_lt_iff₀ hε).mp hj
      _ ≤ ε * ((k : ℝ) + 1) := by
        rw [mul_comm ε]
        apply mul_le_mul_of_nonneg_right _ hε.le
        dsimp [k]
        push_cast
        linarith
  have hresult := hscore (ε - a / ((k : ℝ) + 1)) hδ S hS
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hden : (k : ℝ) + 1 ≠ 0 := by positivity
  have hexp : ((p * k : ℕ) : ℝ) / ((q * (k + 1) : ℕ) : ℝ) -
      (ε - a / ((k : ℝ) + 1)) = a - ε := by
    dsimp [a]
    push_cast
    field_simp [hq', hden] <;> ring
  rw [hexp] at hresult
  exact hresult

private theorem reaches_from_graph_witness : SensitivityCampaign.AchievesExponent (2.15 : ℝ) := by
  obtain ⟨D, n, depth, hlocal⟩ := SensitivityGraphLocal.exists_215_success
  rw [SensitivityGraphLocal.succeeds_eq] at hlocal
  have hword := SensitivityGraphCheck.search_iff_word.mp ⟨D, n, depth, hlocal⟩
  obtain ⟨c, hR, hcross⟩ := SensitivityVariableWord.certificate_iff_word.mpr hword
  obtain ⟨C, _, hseeds⟩ := SensitivityProfileCycle.finite_seeds c
  have hG : 1 < c.vertices ^ c.period :=
    one_lt_pow₀ c.vertices_gt_one c.period_pos.ne'
  have hend := endpoint_of_geometric_seeds C c.radius (c.vertices ^ c.period)
    43 20 hR hG (by decide) hcross.le hseeds
  simpa only [Nat.cast_ofNat, show (43 : ℝ) / 20 = 2.15 by norm_num] using hend

/-- The verified four-stage family covers every loss greater than the remaining
gap. A successful finite graph supplies the endpoint at every smaller loss. -/
theorem solution : SensitivityCampaign.AchievesExponent (2.15 : ℝ) := by
  intro ε hε S hS
  let L : ℝ := Real.log ((5591 : ℝ) ^ 4) /
    Real.log ((3487007904161347435 : ℝ) / 344500417784)
  by_cases h : 2.15 - ε < L
  · have known : SensitivityCampaign.AchievesExponent L :=
      SensitivityCampaign.endpoint22_exact_profile_rate
    obtain ⟨n, f, hsize, hscore⟩ :=
      known (L - (2.15 - ε)) (sub_pos.mpr h) S hS
    rw [show L - (L - (2.15 - ε)) = 2.15 - ε by ring] at hscore
    exact ⟨n, f, hsize, hscore⟩
  · exact reaches_from_graph_witness ε hε S hS
