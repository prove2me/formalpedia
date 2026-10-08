-- Prove2me | solution 1 for SkutellaCQP.MaxSNP.l_condition_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:21:09.673998+00:00
-- url     : https://prove2.me/submissions/d65a504d-3461-42fd-983f-2e40d99e90c7

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

open SkutellaCQP.MaxSNP Finset

private theorem half_bound {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    (m : ℝ) / 2 ≤ optSat I ∧ n ≤ 3 * m := by
  classical
  have hcover : (univ : Finset (Fin m)) ⊆
      (univ.filter fun c => Satisfies (fun _ => true) (I.clause c)) ∪
      (univ.filter fun c => Satisfies (fun _ => false) (I.clause c)) := by
    intro c hc
    have hne : (I.clause c).Nonempty := card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hI.1 c).1)
    obtain ⟨⟨x, b⟩, hb⟩ := hne
    cases b
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, ⟨(x, false), hb, rfl⟩⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _, ⟨(x, true), hb, rfl⟩⟩))
  have hc : m ≤ satCount I (fun _ => true) + satCount I (fun _ => false) := by
    simpa [satCount] using (card_le_card hcover).trans (card_union_le _ _)
  have ht : satCount I (fun _ => true) ≤ optSat I := le_sup (mem_univ _)
  have hf : satCount I (fun _ => false) ≤ optSat I := le_sup (mem_univ _)
  constructor
  · have hn : m ≤ 2 * optSat I := by omega
    have hr : (m : ℝ) ≤ 2 * (optSat I : ℝ) := by exact_mod_cast hn
    linarith
  · have hvars : (univ : Finset (Fin n)) ⊆ univ.biUnion (fun c => (I.clause c).image Prod.fst) := by
      intro x hx
      obtain ⟨c, b, hb⟩ := hI.2.2 x
      exact mem_biUnion.mpr ⟨c, mem_univ _, mem_image.mpr ⟨(x,b), hb, rfl⟩⟩
    calc
      n = (univ : Finset (Fin n)).card := by simp
      _ ≤ (univ.biUnion fun c => (I.clause c).image Prod.fst).card := card_le_card hvars
      _ ≤ ∑ c, ((I.clause c).image Prod.fst).card := card_biUnion_le
      _ ≤ ∑ c, (I.clause c).card := sum_le_sum (fun c _ => card_image_le)
      _ ≤ ∑ _c : Fin m, 3 := sum_le_sum (fun c _ => (hI.1 c).2)
      _ = 3 * m := by simp [Nat.mul_comm]


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

theorem solution {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (S₀ : Sched n m) (hS₀ : Feasible I S₀) (hopt : ∀ S, Feasible I S → VAL S₀ ≤ VAL S) :
    VAL S₀ ≤ 12 * m + 4 * m ∧ (12 * m + 4 * m : ℝ) ≤ 32 * optSat I := by
  obtain ⟨S, hS, hv⟩ := assignment_schedule I hI (fun _ => true)
  have ho := hopt S hS
  obtain ⟨hh, hn⟩ := half_bound I hI
  have hn' : (n : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hn
  have hz : (0 : ℝ) ≤ satCount I (fun _ => true) := Nat.cast_nonneg _
  constructor <;> linarith

#print axioms solution
