-- Prove2me | solution 1 for TeschlODE.Horseshoe.shift_periodicPts_countable_dense
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:03:21.492211+00:00
-- url     : https://prove2.me/submissions/c5042ece-94ab-4434-80b1-31eab713e9d1

import Mathlib
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

set_option autoImplicit false

namespace EC92F229

lemma shift_iterate_apply {N : ℕ} (m : ℕ) (x : ℕ → Fin N) (n : ℕ) :
    (TeschlODE.Shared.shift (N := N))^[m] x n = x (n + m) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih]
    show x (n + m + 1) = x (n + (m + 1))
    rw [Nat.add_assoc]

lemma periodic_mod {N : ℕ} (x : ℕ → Fin N) (m : ℕ) (h : ∀ n, x (n + m) = x n) (n : ℕ) :
    x n = x (n % m) := by
  have key : ∀ k r, x (r + m * k) = x r := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
      intro r
      rw [Nat.mul_succ, ← Nat.add_assoc, h, ih]
  conv_lhs => rw [← Nat.mod_add_div n m]
  exact key _ _

lemma countable_part (N : ℕ) :
    (Function.periodicPts (TeschlODE.Shared.shift (N := N))).Countable := by
  have hsub : Function.periodicPts (TeschlODE.Shared.shift (N := N)) ⊆
      ⋃ k : ℕ, Set.range (fun f : Fin (k + 1) → Fin N =>
        fun n => f ⟨n % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩) := by
    intro x hx
    obtain ⟨m, hm, hper⟩ := hx
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h : ∀ n, x (n + (k + 1)) = x n := by
      intro n
      have := congrFun hper.eq n
      rw [shift_iterate_apply] at this
      exact this
    refine Set.mem_iUnion.2 ⟨k, fun i => x i, ?_⟩
    funext n
    exact (periodic_mod x (k + 1) h n).symm
  refine Set.Countable.mono hsub ?_
  exact Set.countable_iUnion (fun k => Set.countable_range _)

lemma dense_part (N : ℕ) (hN : 2 ≤ N) (x : ℕ → Fin N) (ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ Function.periodicPts (TeschlODE.Shared.shift (N := N)),
      TeschlODE.Shared.symDist N p x < ε := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, ((1 : ℝ) / 2) ^ K0 < ε / (2 * N) :=
    exists_pow_lt_of_lt_one (div_pos hε (by positivity)) (by norm_num)
  set K := K0 + 1 with hKdef
  have hKpos : 0 < K := Nat.succ_pos K0
  let p : ℕ → Fin N := fun n => x (n % K)
  refine ⟨p, ⟨K, hKpos, ?_⟩, ?_⟩
  · show (TeschlODE.Shared.shift (N := N))^[K] p = p
    funext n
    rw [shift_iterate_apply]
    show x ((n + K) % K) = x (n % K)
    rw [Nat.add_mod_right]
  · unfold TeschlODE.Shared.symDist
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
      have : p n = x n := by
        show x (n % K) = x n
        rw [Nat.mod_eq_of_lt hn]
      rw [this, sub_self, abs_zero, zero_div]
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

end EC92F229

theorem solution (N : ℕ) (hN : 2 ≤ N) :
    (Function.periodicPts (TeschlODE.Shared.shift (N := N))).Countable ∧
      ∀ x : ℕ → Fin N, ∀ ε : ℝ, 0 < ε →
        ∃ p ∈ Function.periodicPts (TeschlODE.Shared.shift (N := N)), TeschlODE.Shared.symDist N p x < ε := by
  exact ⟨EC92F229.countable_part N, fun x ε hε => EC92F229.dense_part N hN x ε hε⟩
