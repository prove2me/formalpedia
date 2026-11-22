-- Prove2me | solution 1 for ReadTwiceCount.density_budget
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:37:37.111813+00:00
-- url     : https://prove2.me/submissions/28db86f3-c3bb-421b-ad24-e425c332c392

import Mathlib

theorem solution {ι : Type*} (E act : Finset ι) (hact : act ⊆ E) (a q : ℝ) (s k : ℕ)
    (D r ai : ι → ℝ) (si : ι → ℕ) (ha : 0 < a) (hs : 1 ≤ s) (hq : 1 ≤ q) (hk : 2 ≤ k)
    (hD : ∀ i ∈ E, 0 ≤ D i) (hbudget : ∑ i ∈ E, Real.sqrt (D i) ≤ 1)
    (hpos : ∀ i ∈ act, 0 < D i) (hsi : ∀ i ∈ act, si i + 1 ≤ s)
    (hr : ∀ i ∈ act, Real.sqrt (D i) ≤ r i ∧ r i ≤ q * Real.sqrt (D i))
    (hai : ∀ i ∈ act, ai i = a * s / (r i * ((si i : ℝ) + 1))) :
    (∀ i ∈ act, a / (q * Real.sqrt (D i)) ≤ ai i) ∧
      ∑ i ∈ act, (ai i)⁻¹ ^ k ≤ a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) ∧
      a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) ≤
        a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k ∧
      a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k ≤ a⁻¹ ^ k * q ^ k := by
  classical
  have hqpos : 0 < q := by linarith
  have hsq : 0 ≤ ∑ i ∈ E, Real.sqrt (D i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg (D i)
  have hconst_nonneg : 0 ≤ a⁻¹ ^ k * q ^ k := by positivity
  -- the key identity (√D)^k = D^(k/2)
  have hsqrtpow : ∀ i ∈ act, (Real.sqrt (D i)) ^ k = D i ^ ((k : ℝ) / 2) := by
    intro i hi
    have hDi : 0 ≤ D i := le_of_lt (hpos i hi)
    calc (Real.sqrt (D i)) ^ k = (D i ^ (1 / 2 : ℝ)) ^ (k : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
      _ = D i ^ ((1 / 2 : ℝ) * (k : ℝ)) := (Real.rpow_mul hDi (1 / 2) (k : ℝ)).symm
      _ = D i ^ ((k : ℝ) / 2) := by congr 1; ring
  -- first clause
  have hfirst : ∀ i ∈ act, a / (q * Real.sqrt (D i)) ≤ ai i := by
    intro i hi
    have hDi : 0 < D i := hpos i hi
    have hsqrtpos : 0 < Real.sqrt (D i) := Real.sqrt_pos.mpr hDi
    have hrpos : 0 < r i := lt_of_lt_of_le hsqrtpos (hr i hi).1
    have hsi1pos : (0 : ℝ) < (si i : ℝ) + 1 := by positivity
    have hsi1le : ((si i : ℝ) + 1) ≤ (s : ℝ) := by exact_mod_cast hsi i hi
    have hprod : r i * ((si i : ℝ) + 1) ≤ q * Real.sqrt (D i) * s := by
      have hA : r i * ((si i : ℝ) + 1) ≤ (q * Real.sqrt (D i)) * ((si i : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (hr i hi).2 (le_of_lt hsi1pos)
      have hB : (q * Real.sqrt (D i)) * ((si i : ℝ) + 1) ≤ (q * Real.sqrt (D i)) * s :=
        mul_le_mul_of_nonneg_left hsi1le (by positivity)
      exact hA.trans hB
    rw [hai i hi,
      div_le_div_iff₀ (by positivity : (0 : ℝ) < q * Real.sqrt (D i))
        (by positivity : (0 : ℝ) < r i * ((si i : ℝ) + 1))]
    calc a * (r i * ((si i : ℝ) + 1)) ≤ a * (q * Real.sqrt (D i) * s) :=
          mul_le_mul_of_nonneg_left hprod ha.le
      _ = a * s * (q * Real.sqrt (D i)) := by ring
  -- second clause
  have hterm : ∀ i ∈ act, (ai i)⁻¹ ^ k ≤ a⁻¹ ^ k * q ^ k * D i ^ ((k : ℝ) / 2) := by
    intro i hi
    have hDi : 0 < D i := hpos i hi
    have hsqrtpos : 0 < Real.sqrt (D i) := Real.sqrt_pos.mpr hDi
    have hbase_pos : 0 < a / (q * Real.sqrt (D i)) := by positivity
    have hai_pos : 0 < ai i := lt_of_lt_of_le hbase_pos (hfirst i hi)
    have hinv : (ai i)⁻¹ ≤ (a / (q * Real.sqrt (D i)))⁻¹ :=
      (inv_le_inv₀ hai_pos hbase_pos).mpr (hfirst i hi)
    have hpow : (ai i)⁻¹ ^ k ≤ ((a / (q * Real.sqrt (D i)))⁻¹) ^ k :=
      pow_le_pow_left₀ (inv_nonneg.mpr hai_pos.le) hinv k
    calc (ai i)⁻¹ ^ k
        ≤ ((a / (q * Real.sqrt (D i)))⁻¹) ^ k := hpow
      _ = (q * Real.sqrt (D i) / a) ^ k := by rw [inv_div]
      _ = (q * Real.sqrt (D i)) ^ k / a ^ k := by rw [div_pow]
      _ = q ^ k * (Real.sqrt (D i)) ^ k / a ^ k := by rw [mul_pow]
      _ = q ^ k * D i ^ ((k : ℝ) / 2) / a ^ k := by rw [hsqrtpow i hi]
      _ = a⁻¹ ^ k * q ^ k * D i ^ ((k : ℝ) / 2) := by
          rw [inv_pow, div_eq_mul_inv]
          ring
  have hsum2 : ∑ i ∈ act, (ai i)⁻¹ ^ k ≤
      a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) := by
    calc ∑ i ∈ act, (ai i)⁻¹ ^ k
        ≤ ∑ i ∈ act, a⁻¹ ^ k * q ^ k * D i ^ ((k : ℝ) / 2) := Finset.sum_le_sum hterm
      _ = a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) := by
          rw [Finset.mul_sum]
  -- power superadditivity on finsets
  have hsum_pow_le : ∀ (u : Finset ι) (f : ι → ℝ), (∀ i ∈ u, 0 ≤ f i) →
      ∑ i ∈ u, f i ^ k ≤ (∑ i ∈ u, f i) ^ k := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro f _
        rw [Finset.sum_empty, Finset.sum_empty, zero_pow (by omega : k ≠ 0)]
    | insert x u hx ih =>
        intro f hf
        rw [Finset.sum_insert hx, Finset.sum_insert hx]
        have hfx : 0 ≤ f x := hf x (Finset.mem_insert_self x u)
        have hfu : ∀ i ∈ u, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
        have ih' := ih f hfu
        have h := pow_add_pow_le hfx (Finset.sum_nonneg hfu) (by omega : k ≠ 0)
        linarith
  -- third clause
  have hthird_sum : ∑ i ∈ act, D i ^ ((k : ℝ) / 2) ≤
      (∑ i ∈ E, Real.sqrt (D i)) ^ k := by
    calc ∑ i ∈ act, D i ^ ((k : ℝ) / 2)
        = ∑ i ∈ act, (Real.sqrt (D i)) ^ k := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hsqrtpow i hi).symm
      _ ≤ (∑ i ∈ act, Real.sqrt (D i)) ^ k :=
            hsum_pow_le act (fun i => Real.sqrt (D i)) (fun i _ => Real.sqrt_nonneg (D i))
      _ ≤ (∑ i ∈ E, Real.sqrt (D i)) ^ k := by
            apply pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg (D i)) _ k
            exact Finset.sum_le_sum_of_subset_of_nonneg hact
              (fun i _ _ => Real.sqrt_nonneg (D i))
  have hthird : a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) ≤
      a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k :=
    mul_le_mul_of_nonneg_left hthird_sum hconst_nonneg
  -- fourth clause
  have hSk_le_one : (∑ i ∈ E, Real.sqrt (D i)) ^ k ≤ 1 :=
    pow_le_one₀ hsq hbudget
  have hfourth : a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k ≤ a⁻¹ ^ k * q ^ k := by
    calc a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k
        ≤ a⁻¹ ^ k * q ^ k * 1 := mul_le_mul_of_nonneg_left hSk_le_one hconst_nonneg
      _ = a⁻¹ ^ k * q ^ k := by ring
  exact ⟨hfirst, hsum2, hthird, hfourth⟩

