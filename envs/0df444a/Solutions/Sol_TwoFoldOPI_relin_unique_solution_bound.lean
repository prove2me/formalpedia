-- Prove2me | solution 1 for TwoFoldOPI.relin_unique_solution_bound
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T20:02:29.664211+00:00
-- url     : https://prove2.me/submissions/affc24cf-4883-417f-a88e-027d58fd9d4c

import Mathlib
import Definitions.Def_TwoFoldOPI_schurFailureSum

open TwoFoldOPI

theorem solution {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (D : Submodule K (Fin m → K)) (c : Fin m → K) (hc : c ∈ D) :
    (Nat.card {c' : Fin m → K // (∀ i, c' i ≠ c i) ∧
        ∃ v ∈ D, ∃ w ∈ schurSquare D, v ≠ c ∧ w - (c + c') * v + c * c' = 0} : ℝ) ≤
      schurFailureSum D * ((Fintype.card K : ℝ) - 1) ^ m := by
  classical
  have hK1 : 1 ≤ Fintype.card K := Fintype.card_pos
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := by
    have := Fintype.one_lt_card (α := K)
    rw [hq]; exact_mod_cast this
  have hq0 : (0 : ℝ) < q - 1 := by linarith
  have hqcast : ((Fintype.card K - 1 : ℕ) : ℝ) = q - 1 := by
    rw [Nat.cast_sub hK1]; simp [hq]
  -- the bad set, as a finset
  set bad := Finset.univ.filter (fun c' : Fin m → K => (∀ i, c' i ≠ c i) ∧
      ∃ v ∈ D, ∃ w ∈ schurSquare D, v ≠ c ∧ w - (c + c') * v + c * c' = 0) with hbad
  have hcardbad : Nat.card {c' : Fin m → K // (∀ i, c' i ≠ c i) ∧
        ∃ v ∈ D, ∃ w ∈ schurSquare D, v ≠ c ∧ w - (c + c') * v + c * c' = 0} = bad.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcardbad]
  -- the union-bound index sets
  set Dnz := Finset.univ.filter (fun d : Fin m → K => d ∈ D ∧ d ≠ 0) with hDnz
  let Sh : (Fin m → K) → Finset (Fin m → K) := fun dv =>
    Finset.univ.filter (fun dw => dw ∈ shorten (schurSquare D) (zeroSet dv))
  let S : (Fin m → K) → (Fin m → K) → Finset (Fin m → K) := fun dv dw =>
    Finset.univ.filter (fun c' => (∀ i, c' i ≠ c i) ∧ ∀ i, dw i = (c i + c' i) * dv i)
  -- Step 1: every bad `c'` is explained by a pair `(Δv, Δw)`
  have hcc : c * c ∈ schurSquare D := Submodule.subset_span ⟨c, hc, c, hc, rfl⟩
  have hsub : bad ⊆ Dnz.biUnion (fun dv => (Sh dv).biUnion (fun dw => S dv dw)) := by
    intro c' hc'
    rw [hbad, Finset.mem_filter] at hc'
    obtain ⟨-, hne, v, hv, w, hw, hvc, heq⟩ := hc'
    have hid : w - c * c = (c + c') * (v - c) := by
      have : w = (c + c') * v - c * c' := by
        rw [← sub_eq_zero]; rw [← heq]; ring
      rw [this]; ring
    simp only [Finset.mem_biUnion]
    refine ⟨v - c, ?_, w - c * c, ?_, ?_⟩
    · rw [hDnz, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, D.sub_mem hv hc, sub_ne_zero.mpr hvc⟩
    · simp only [Sh, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(schurSquare D).sub_mem hw hcc, ?_⟩
      intro i hi
      simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have := congrFun hid i
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply] at this hi ⊢
      rw [this, hi, mul_zero]
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hne, fun i => ?_⟩
      have := congrFun hid i
      simpa only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply] using this
  -- Step 2: each `S Δv Δw` has at most `(q-1)^(m - wt Δv)` elements
  have hS : ∀ dv dw, (S dv dw).card ≤ (Fintype.card K - 1) ^ (m - hammingNorm dv) := by
    intro dv dw
    let T : Fin m → Finset K := fun i =>
      if dv i = 0 then Finset.univ.erase (c i) else {dw i / dv i - c i}
    have hST : S dv dw ⊆ Fintype.piFinset T := by
      intro c' hc'
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      rw [Fintype.mem_piFinset]
      intro i
      by_cases h0 : dv i = 0
      · simp only [T, h0, if_true, Finset.mem_erase, Finset.mem_univ, and_true]
        exact hc'.1 i
      · simp only [T, h0, if_false, Finset.mem_singleton]
        rw [hc'.2 i]
        field_simp
        ring
    have hcardT : ∀ i, (T i).card = if dv i = 0 then Fintype.card K - 1 else 1 := by
      intro i
      by_cases h0 : dv i = 0
      · simp [T, h0, Finset.card_erase_of_mem]
      · simp [T, h0]
    calc (S dv dw).card ≤ (Fintype.piFinset T).card := Finset.card_le_card hST
      _ = ∏ i, (T i).card := Fintype.card_piFinset T
      _ = ∏ i, (if dv i = 0 then Fintype.card K - 1 else 1) := by
          apply Finset.prod_congr rfl; intro i _; exact hcardT i
      _ = (Fintype.card K - 1) ^ (Finset.univ.filter (fun i => dv i = 0)).card := by
          rw [Finset.prod_ite]; simp
      _ = (Fintype.card K - 1) ^ (m - hammingNorm dv) := by
          congr 1
          have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
            (fun i => dv i = 0)
          simp only [Finset.card_univ, Fintype.card_fin] at h
          have hw : hammingNorm dv = (Finset.univ.filter (fun i => ¬ dv i = 0)).card := rfl
          omega
  -- Step 3: the number of `Δw` is `q^{dim}`
  have hSh : ∀ dv, ((Sh dv).card : ℝ) =
      q ^ Module.finrank K (shorten (schurSquare D) (zeroSet dv)) := by
    intro dv
    have h1 : (Sh dv).card = Fintype.card (shorten (schurSquare D) (zeroSet dv)) := by
      simp only [Sh]; rw [Fintype.card_subtype]
    rw [h1, Module.card_eq_pow_finrank (K := K)]
    push_cast; rfl
  -- Step 4: put together
  have hnat : bad.card ≤ ∑ dv ∈ Dnz, ∑ dw ∈ Sh dv, (S dv dw).card := by
    calc bad.card ≤ (Dnz.biUnion (fun dv => (Sh dv).biUnion (fun dw => S dv dw))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ dv ∈ Dnz, ((Sh dv).biUnion (fun dw => S dv dw)).card := Finset.card_biUnion_le
      _ ≤ ∑ dv ∈ Dnz, ∑ dw ∈ Sh dv, (S dv dw).card := by
          apply Finset.sum_le_sum; intro dv _; exact Finset.card_biUnion_le
  have hE : schurFailureSum D = ∑ dv ∈ Dnz,
      q ^ Module.finrank K (shorten (schurSquare D) (zeroSet dv)) / (q - 1) ^ hammingNorm dv := by
    unfold schurFailureSum
    rw [hDnz, hq]
  calc (bad.card : ℝ) ≤ ((∑ dv ∈ Dnz, ∑ dw ∈ Sh dv, (S dv dw).card : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = ∑ dv ∈ Dnz, ∑ dw ∈ Sh dv, ((S dv dw).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ dv ∈ Dnz, ∑ dw ∈ Sh dv, (q - 1) ^ (m - hammingNorm dv) := by
        apply Finset.sum_le_sum; intro dv _
        apply Finset.sum_le_sum; intro dw _
        have := hS dv dw
        rw [← hqcast]
        exact_mod_cast this
    _ = ∑ dv ∈ Dnz, q ^ Module.finrank K (shorten (schurSquare D) (zeroSet dv)) *
          (q - 1) ^ (m - hammingNorm dv) := by
        apply Finset.sum_congr rfl; intro dv _
        rw [Finset.sum_const, nsmul_eq_mul, hSh]
    _ = ∑ dv ∈ Dnz, q ^ Module.finrank K (shorten (schurSquare D) (zeroSet dv)) /
          (q - 1) ^ hammingNorm dv * (q - 1) ^ m := by
        apply Finset.sum_congr rfl; intro dv _
        have hle : hammingNorm dv ≤ m := by
          have := hammingNorm_le_card_fintype (x := dv)
          simpa using this
        have hpos : (0 : ℝ) < (q - 1) ^ hammingNorm dv := pow_pos hq0 _
        rw [div_mul_eq_mul_div, mul_div_assoc]
        congr 1
        rw [eq_div_iff hpos.ne', ← pow_add, Nat.sub_add_cancel hle]
    _ = schurFailureSum D * (q - 1) ^ m := by
        rw [hE, Finset.sum_mul]
