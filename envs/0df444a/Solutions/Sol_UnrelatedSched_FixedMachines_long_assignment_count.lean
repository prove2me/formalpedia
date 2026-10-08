-- Prove2me | solution 1 for UnrelatedSched.FixedMachines.long_assignment_count
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:30:48.74014+00:00
-- url     : https://prove2.me/submissions/4ba8122a-d440-405a-84a4-7263cfbde497

import Mathlib
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
open scoped BigOperators
open UnrelatedSched.FixedMachines

private lemma machine_bound {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ)
    (L : Fin n → Option (Fin m)) (hL : IsAdmissible P ε d L) (i : Fin m) :
    ((Finset.univ.filter (fun j => L j = some i)).card : ℝ) < 1 / ε := by
  classical
  let J := Finset.univ.filter (fun j => L j = some i)
  have hload := hL.2 i
  change ∑ j ∈ J, (P i j : ℝ) ≤ (d : ℝ) at hload
  by_cases hJ : J.Nonempty
  · have hs : ∑ j ∈ J, ε * (d : ℝ) < ∑ j ∈ J, (P i j : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hJ
      intro j hj
      exact hL.1 j i (Finset.mem_filter.mp hj).2
    have hd : 0 < (d : ℝ) := by
      obtain ⟨j, hj⟩ := hJ
      have hp : 0 < (P i j : ℝ) := by exact_mod_cast hP i j
      have hle : (P i j : ℝ) ≤ ∑ j ∈ J, (P i j : ℝ) :=
        Finset.single_le_sum (fun j _ => Nat.cast_nonneg _) hj
      linarith
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    apply (lt_div_iff₀ hε).mpr
    nlinarith
  · have hz : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    change (J.card : ℝ) < 1 / ε
    simp [hz, hε]

private def slots {n K : ℕ} (J : Finset (Fin n)) : Fin K → Option (Fin n) :=
  fun k => (J.sort (· ≤ ·))[k.val]?

private lemma slots_injective {n K : ℕ} :
    Function.Injective (fun J : {J : Finset (Fin n) // J.card ≤ K} => slots (K := K) J.val) := by
  intro J H he
  change slots (K := K) J.val = slots (K := K) H.val at he
  apply Subtype.ext
  apply Finset.ext
  intro j
  have hm (J : {J : Finset (Fin n) // J.card ≤ K}) :
      j ∈ J.val ↔ ∃ k : Fin K, slots (K := K) J.val k = some j := by
    rw [← Finset.mem_sort (· ≤ ·)]
    constructor
    · intro hj
      obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hj
      refine ⟨⟨k, lt_of_lt_of_le (by simpa using hk) J.property⟩, ?_⟩
      change (J.val.sort (· ≤ ·))[k]? = some j
      rw [List.getElem?_eq_getElem hk, he]
    · rintro ⟨k, hk⟩
      exact List.mem_of_getElem? hk
  rw [hm J, hm H]
  change (∃ k, slots (K := K) J.val k = some j) ↔ _
  rw [he]

#print axioms machine_bound

theorem solution {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ L, IsAdmissible P ε d L →
      ∀ i, ((Finset.univ.filter (fun j => L j = some i)).card : ℝ) < 1 / ε) ∧
    (({L : Fin n → Option (Fin m) | IsAdmissible P ε d L}.ncard : ℕ) : ℝ) <
      ((n : ℝ) + 1) ^ ((m : ℝ) / ε) := by
  classical
  have hb := machine_bound P hP ε hε d
  refine ⟨hb, ?_⟩
  let K := ⌈1 / ε⌉₊ - 1
  have hceil : 0 < ⌈1 / ε⌉₊ := Nat.ceil_pos.mpr (one_div_pos.mpr hε)
  have hK : (K : ℝ) < 1 / ε := Nat.lt_ceil.mp (by dsimp [K]; omega)
  have hbK (L : Fin n → Option (Fin m)) (hL : IsAdmissible P ε d L) (i : Fin m) :
      (Finset.univ.filter (fun j => L j = some i)).card ≤ K := by
    have hh := Nat.lt_ceil.mpr (hb L hL i)
    dsimp [K]; omega
  let enc : {L : Fin n → Option (Fin m) // IsAdmissible P ε d L} →
      (Fin m → Fin K → Option (Fin n)) := fun L i =>
        slots (Finset.univ.filter (fun j => L.val j = some i))
  have hinj : Function.Injective enc := by
    intro L H he
    apply Subtype.ext
    funext j
    have hf (i : Fin m) :
        Finset.univ.filter (fun j => L.val j = some i) =
        Finset.univ.filter (fun j => H.val j = some i) := by
      exact congrArg Subtype.val (slots_injective (n := n) (K := K)
        (a₁ := ⟨_, hbK L.val L.property i⟩) (a₂ := ⟨_, hbK H.val H.property i⟩)
        (congrFun he i))
    have hs (i : Fin m) : L.val j = some i ↔ H.val j = some i := by
      have := Finset.ext_iff.mp (hf i) j
      simpa using this
    cases hLj : L.val j with
    | some i => exact (hs i).mp hLj |>.symm
    | none =>
      cases hHj : H.val j with
      | none => rfl
      | some i => have := (hs i).mpr hHj; simp [hLj] at this
  have hc : {L : Fin n → Option (Fin m) | IsAdmissible P ε d L}.ncard ≤
      (n + 1) ^ (K * m) := by
    have hh := Fintype.card_le_of_injective enc hinj
    rw [← Set.fintypeCard_eq_ncard]
    have heq : Fintype.card ↥{L : Fin n → Option (Fin m) | IsAdmissible P ε d L} =
        Fintype.card {L : Fin n → Option (Fin m) // IsAdmissible P ε d L} :=
      Fintype.card_congr (Equiv.refl _)
    rw [heq]
    simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, pow_mul] using hh
  have hcr : (({L : Fin n → Option (Fin m) | IsAdmissible P ε d L}.ncard : ℕ) : ℝ) ≤
      ((n : ℝ) + 1) ^ (K * m) := by exact_mod_cast hc
  apply lt_of_le_of_lt hcr
  rw [← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · have hmr : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    push_cast
    have := mul_lt_mul_of_pos_right hK hmr
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

#print axioms solution
