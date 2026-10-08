-- Prove2me | solution 1 for SkutellaCQP.MaxSNP.lemma_7_1_b
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:21:08.721818+00:00
-- url     : https://prove2.me/submissions/726279e7-9beb-486e-a25f-9a88fb891abb

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

open SkutellaCQP.MaxSNP Finset

private lemma schedule_bound {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (S : Sched n m) (hS : Feasible I S) :
    (4 * n + 4 * m : ℝ) - VAL S ≤ satCount I (SAT S) := by
  classical
  let v : Fin m → Fin n := fun c => (S.mach (.inr c)).1
  have hv (x : Fin n) : 0 ≤ S.start (.inl x) := hS.2.1 (.inl x)
  have hc (c : Fin m) : 3 ≤ S.start (.inr c) := hS.2.1 (.inr c)
  have hm (c : Fin m) (h : ¬ Satisfies (SAT S) (I.clause c)) :
      S.mach (.inl (v c)) = S.mach (.inr c) := by
    apply Prod.ext
    · exact hS.1 (.inl (v c))
    · have he := hS.1 (.inr c)
      change ((S.mach (.inr c)).1, !(S.mach (.inr c)).2) ∈ I.clause c at he
      have hh : (S.mach (.inl (v c))).2 ≠ !(S.mach (.inr c)).2 := by
        intro hb
        exact h ⟨_, he, hb⟩
      cases h₁ : (S.mach (.inl (v c))).2 <;>
        cases h₂ : (S.mach (.inr c)).2 <;> simp_all
  have per (c : Fin m) :
      4 - (if Satisfies (SAT S) (I.clause c) then (1 : ℝ) else 0) ≤
        S.start (.inr c) + S.start (.inl (v c)) / 3 := by
    split_ifs with h
    · linarith [hv (v c), hc c]
    · have hn := hS.2.2 (.inl (v c)) (.inr c) (by simp) (hm c h)
      change S.start (.inl (v c)) + 4 ≤ S.start (.inr c) ∨
        S.start (.inr c) + 0 ≤ S.start (.inl (v c)) at hn
      rcases hn with hn | hn <;> linarith [hv (v c), hc c]
  have count (x : Fin n) : (univ.filter fun c => v c = x).card ≤ 3 := by
    calc
      (univ.filter fun c => v c = x).card ≤
          ∑ c, ((I.clause c).filter fun ℓ => ℓ.1 = x).card := by
        have he : (∑ c : Fin m, if v c = x then (1 : ℕ) else 0) =
            (univ.filter fun c => v c = x).card := by simp
        rw [← he]
        apply sum_le_sum
        intro c _
        split_ifs with h
        · apply Finset.one_le_card.mpr
          refine ⟨((S.mach (.inr c)).1, !(S.mach (.inr c)).2), ?_⟩
          exact mem_filter.mpr ⟨hS.1 (.inr c), h⟩
        · exact Nat.zero_le _
      _ ≤ 3 := hI.2.1 x
  have charge : (∑ c, S.start (.inl (v c)) / 3) ≤ ∑ x, S.start (.inl x) := by
    calc
      (∑ c, S.start (.inl (v c)) / 3) =
          ∑ x, ∑ c ∈ univ.filter (fun c => v c = x), S.start (.inl x) / 3 := by
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro c _
        simp
      _ = ∑ x, ((univ.filter fun c => v c = x).card : ℝ) * (S.start (.inl x) / 3) := by
        simp
      _ ≤ ∑ x, S.start (.inl x) := by
        apply sum_le_sum
        intro x _
        have hcount : ((univ.filter fun c => v c = x).card : ℝ) ≤ 3 := by
          exact_mod_cast count x
        nlinarith [hv x]
  have hh := sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin m))) => per c)
  have hs : (∑ c : Fin m, if Satisfies (SAT S) (I.clause c) then (1 : ℝ) else 0) =
      satCount I (SAT S) := by
    simp [satCount, sum_filter]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  rw [hs] at hh
  have hval : VAL S = (∑ x : Fin n, S.start (.inl x)) + 4 * n +
      ∑ c : Fin m, S.start (.inr c) := by
    simp [VAL, Fintype.sum_sum_type, ptime, sum_add_distrib]
    ring
  rw [hval]
  linarith

private lemma assignment_schedule {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (t : Fin n → Bool) : ∃ S : Sched n m, Feasible I S ∧
      VAL S = (4 * n + 4 * m : ℝ) - satCount I t := by
  classical
  have choices (c : Fin m) : ∃ ℓ ∈ I.clause c,
      Satisfies t (I.clause c) → t ℓ.1 = ℓ.2 := by
    by_cases h : Satisfies t (I.clause c)
    · obtain ⟨ℓ, hℓ, ht⟩ := h
      exact ⟨ℓ, hℓ, fun _ => ht⟩
    · obtain ⟨ℓ, hℓ⟩ := one_le_card.mp (hI.1 c).1
      exact ⟨ℓ, hℓ, fun hh => (h hh).elim⟩
  choose ℓ hℓ ht using choices
  let S : Sched n m := {
    mach := Sum.elim (fun x => (x, t x)) (fun c => ((ℓ c).1, !(ℓ c).2))
    start := Sum.elim (fun _ => 0) (fun c => if Satisfies t (I.clause c) then 3 else 4) }
  have nonoverlap (x : Fin n) (c : Fin m) (he : S.mach (.inl x) = S.mach (.inr c)) :
      S.start (.inl x) + ptime (Sum.inl x : Job n m) ≤ S.start (.inr c) := by
    have hx : x = (ℓ c).1 := congrArg Prod.fst he
    have hb : t x = !(ℓ c).2 := congrArg Prod.snd he
    have hn : ¬ Satisfies t (I.clause c) := by
      intro h
      have hh := ht c h
      rw [← hx, hb] at hh
      cases (ℓ c).2 <;> simp_all
    simp [S, ptime, hn]
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro j
    cases j with
    | inl x => rfl
    | inr c => simpa [Eligible, S] using hℓ c
  · intro j
    cases j <;> simp [S, rel] <;> split_ifs <;> norm_num
  · intro j k hjk he
    cases j with
    | inl x =>
      cases k with
      | inl y =>
        have := congrArg Prod.fst he
        simp only [S, Sum.elim_inl] at this
        exact (hjk (by simpa [this])).elim
      | inr c => exact Or.inl (nonoverlap x c he)
    | inr c =>
      cases k with
      | inl x => exact Or.inr (nonoverlap x c he.symm)
      | inr d =>
        change S.start (.inr c) + 0 ≤ S.start (.inr d) ∨
          S.start (.inr d) + 0 ≤ S.start (.inr c)
        simpa using le_total (S.start (.inr c)) (S.start (.inr d))
  · have hs : (∑ c : Fin m, if Satisfies t (I.clause c) then (1 : ℝ) else 0) =
        satCount I t := by simp [satCount, sum_filter]
    have he (c : Fin m) : (if Satisfies t (I.clause c) then (3 : ℝ) else 4) =
        4 - (if Satisfies t (I.clause c) then 1 else 0) := by split_ifs <;> norm_num
    simp only [VAL, Fintype.sum_sum_type, S, Sum.elim_inl, Sum.elim_inr, ptime,
      zero_add, add_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [he]
    rw [sum_sub_distrib, hs]
    simp
    ring

theorem solution {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    ∃ S₀ : Sched n m, Feasible I S₀ ∧ VAL S₀ = (4 * n + 4 * m : ℝ) - optSat I ∧
      ∀ S, Feasible I S → VAL S₀ ≤ VAL S := by
  classical
  obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup (s := (univ : Finset (Fin n → Bool)))
    (f := satCount I) (by simp)
  change optSat I = satCount I t at he
  obtain ⟨S₀, hS₀, hv⟩ := assignment_schedule I hI t
  rw [← he] at hv
  refine ⟨S₀, hS₀, hv, ?_⟩
  intro S hS
  have hb := schedule_bound I hI S hS
  have hc : satCount I (SAT S) ≤ optSat I := le_sup (mem_univ _)
  have hc' : (satCount I (SAT S) : ℝ) ≤ optSat I := by exact_mod_cast hc
  linarith

#print axioms solution
