-- Prove2me | solution 1 for TeschlODE.IntervalMaps.shift_exists_dense_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:21:08.983427+00:00
-- url     : https://prove2.me/submissions/048221a2-d574-4e22-be66-1a3805f470b5

import Mathlib
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

set_option autoImplicit false

namespace PF892F823

lemma shift_iterate_apply {N : ℕ} (m : ℕ) (x : ℕ → Fin N) (n : ℕ) :
    (TeschlODE.Shared.shift (N := N))^[m] x n = x (n + m) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih]
    show x (n + m + 1) = x (n + (m + 1))
    rw [Nat.add_assoc]

lemma close_of_agree (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ p x : ℕ → Fin N, (∀ n < K, p n = x n) →
      TeschlODE.Shared.symDist N p x < ε := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, ((1 : ℝ) / 2) ^ K0 < ε / (2 * N) :=
    exists_pow_lt_of_lt_one (div_pos hε (by positivity)) (by norm_num)
  refine ⟨K0 + 1, ?_⟩
  intro p x hpx
  set K := K0 + 1 with hKdef
  unfold TeschlODE.Shared.symDist
  set f : ℕ → ℝ := fun n => |(((p n : ℕ) : ℝ)) - ((x n : ℕ) : ℝ)| / (N : ℝ) ^ n with hf
  have hbound : ∀ n, f n ≤ N * ((1 : ℝ) / 2) ^ n := by
    intro n
    have h1 : |(((p n : ℕ) : ℝ)) - ((x n : ℕ) : ℝ)| ≤ N := by
      have a1 : ((p n : ℕ) : ℝ) < N := by exact_mod_cast (p n).isLt
      have a2 : ((x n : ℕ) : ℝ) < N := by exact_mod_cast (x n).isLt
      have b1 : (0 : ℝ) ≤ ((p n : ℕ) : ℝ) := Nat.cast_nonneg _
      have b2 : (0 : ℝ) ≤ ((x n : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_sub_le_iff]; constructor <;> linarith
    have h2 : (2 : ℝ) ^ n ≤ (N : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) hNr n
    have h2p : (0 : ℝ) < 2 ^ n := by positivity
    rw [hf]
    simp only
    rw [div_pow, one_pow, ← div_eq_mul_one_div]
    calc |(((p n : ℕ) : ℝ)) - ((x n : ℕ) : ℝ)| / (N : ℝ) ^ n
        ≤ (N : ℝ) / (N : ℝ) ^ n := by
          apply div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (N : ℝ) / 2 ^ n := by
          apply div_le_div_of_nonneg_left hNpos.le h2p h2
  have hnonneg : ∀ n, 0 ≤ f n := fun n => by rw [hf]; positivity
  have hgs : Summable (fun n : ℕ => (N : ℝ) * ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_two.mul_left _
  have hfs : Summable f := Summable.of_nonneg_of_le hnonneg hbound hgs
  have hzero : ∀ n < K, f n = 0 := by
    intro n hn
    rw [hf]
    simp only
    rw [hpx n hn, sub_self, abs_zero, zero_div]
  have hsplit := hfs.sum_add_tsum_nat_add K
  have hsum0 : ∑ i ∈ Finset.range K, f i = 0 :=
    Finset.sum_eq_zero (fun i hi => hzero i (Finset.mem_range.1 hi))
  rw [hsum0, zero_add] at hsplit
  rw [← hsplit]
  have htail : ∀ i, f (i + K) ≤ (N * ((1 : ℝ) / 2) ^ K) * ((1 : ℝ) / 2) ^ i := by
    intro i
    calc f (i + K) ≤ N * ((1 : ℝ) / 2) ^ (i + K) := hbound _
      _ = (N * ((1 : ℝ) / 2) ^ K) * ((1 : ℝ) / 2) ^ i := by rw [pow_add]; ring
  have hts : Summable (fun i => f (i + K)) := (summable_nat_add_iff K).2 hfs
  have hgs2 : Summable (fun i : ℕ => (N * ((1 : ℝ) / 2) ^ K) * ((1 : ℝ) / 2) ^ i) :=
    summable_geometric_two.mul_left _
  have hle := Summable.tsum_le_tsum htail hts hgs2
  rw [tsum_mul_left, tsum_geometric_two] at hle
  have hKlt : ((1 : ℝ) / 2) ^ K ≤ ((1 : ℝ) / 2) ^ K0 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : ((1 : ℝ) / 2) ^ K * (2 * N) < ε := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)).1 (lt_of_le_of_lt hKlt hK0)
    exact this
  calc ∑' i, f (i + K) ≤ N * ((1 : ℝ) / 2) ^ K * 2 := hle
    _ = ((1 : ℝ) / 2) ^ K * (2 * N) := by ring
    _ < ε := h3

/-- The dense-orbit point: block `j` = positions `[2^j, 2^(j+1))` holds the list `E j`. -/
noncomputable def orbitPt {N : ℕ} (d : Fin N) (E : ℕ → List (Fin N)) (n : ℕ) : Fin N :=
  ((E (Nat.log 2 n))[n - 2 ^ (Nat.log 2 n)]?).getD d

lemma orbitPt_block {N : ℕ} (d : Fin N) (E : ℕ → List (Fin N)) (j i : ℕ) (hi : i < 2 ^ j) :
    orbitPt d E (i + 2 ^ j) = ((E j)[i]?).getD d := by
  have hlog : Nat.log 2 (i + 2 ^ j) = j := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]; omega
  unfold orbitPt
  rw [hlog, Nat.add_sub_cancel]

lemma main (N : ℕ) (hN : 2 ≤ N) :
    ∃ x : ℕ → Fin N, ∀ y : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, TeschlODE.Shared.symDist N y ((TeschlODE.Shared.shift (N := N))^[k] x) < ε := by
  obtain ⟨e, he⟩ := exists_surjective_nat (List (Fin N))
  let d : Fin N := ⟨0, by omega⟩
  let E : ℕ → List (Fin N) := fun j => e (Nat.unpair j).1
  refine ⟨orbitPt d E, ?_⟩
  intro y ε hε
  obtain ⟨K, hK⟩ := close_of_agree N hN ε hε
  obtain ⟨m, hm⟩ := he (List.ofFn (fun i : Fin K => y i))
  let j := Nat.pair m K
  have hEj : E j = List.ofFn (fun i : Fin K => y i) := by
    show e (Nat.unpair (Nat.pair m K)).1 = _
    rw [Nat.unpair_pair]; exact hm
  have hjK : K ≤ j := Nat.right_le_pair m K
  have hK2 : K < 2 ^ j := lt_of_le_of_lt hjK (Nat.lt_two_pow_self)
  refine ⟨2 ^ j, hK y _ ?_⟩
  intro n hn
  rw [shift_iterate_apply, orbitPt_block d E j n (by omega), hEj, List.getElem?_ofFn]
  simp [hn]

end PF892F823

theorem solution (N : ℕ) (hN : 2 ≤ N) :
    ∃ x : ℕ → Fin N, ∀ y : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, TeschlODE.Shared.symDist N y ((TeschlODE.Shared.shift (N := N))^[k] x) < ε := by
  exact PF892F823.main N hN
