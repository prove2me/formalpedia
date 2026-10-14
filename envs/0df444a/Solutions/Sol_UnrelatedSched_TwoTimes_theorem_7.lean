-- Prove2me | solution 1 for UnrelatedSched.TwoTimes.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:53:58.148951+00:00
-- url     : https://prove2.me/submissions/03673943-af57-4631-8f8f-a5114ed2bf5b

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling


namespace UnrelatedSched.TwoTimes

lemma ts_load_nat {m N : ℕ} (t : Fin m → Fin N → ℕ) (σ : Fin N → Fin m) (i : Fin m) :
    load (fun i j => (t i j : ℝ)) σ i
      = ((∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j : ℕ) : ℝ) := by
  unfold load; push_cast; rfl

lemma ts_load_le {m N : ℕ} (t : Fin m → Fin N → ℕ) (σ : Fin N → Fin m) (B : ℕ)
    (h : makespan (fun i j => (t i j : ℝ)) σ ≤ (B : ℝ)) (i : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j ≤ B := by
  have h1 : load (fun i j => (t i j : ℝ)) σ i ≤ makespan (fun i j => (t i j : ℝ)) σ :=
    le_ciSup (f := fun i => load (fun i j => (t i j : ℝ)) σ i) (Set.finite_range _).bddAbove i
  rw [ts_load_nat] at h1
  exact_mod_cast h1.trans h

lemma ts_makespan_le {m N : ℕ} (t : Fin m → Fin N → ℕ) (σ : Fin N → Fin m) (B : ℕ)
    (h : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j ≤ B) :
    makespan (fun i j => (t i j : ℝ)) σ ≤ (B : ℝ) := by
  unfold makespan
  apply Real.iSup_le _ (Nat.cast_nonneg _)
  intro i
  rw [ts_load_nat]
  exact_mod_cast h i

lemma ts_tight {m N : ℕ} (t : Fin m → Fin N → ℕ) (l : Fin N → ℕ) (σ : Fin N → Fin m) (B : ℕ)
    (hl : ∀ i j, l j ≤ t i j) (hsum : m * B ≤ ∑ j, l j)
    (hle : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j ≤ B) :
    (∀ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j = B) ∧
      ∀ j, t (σ j) j = l j := by
  have hfib : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j = ∑ j, t (σ j) j := by
    rw [← Finset.sum_fiberwise Finset.univ σ (fun j => t (σ j) j)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
    rw [(Finset.mem_filter.1 hj).2]
  have h1 : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j ≤ ∑ _i : Fin m, B :=
    Finset.sum_le_sum (fun i _ => hle i)
  have h2 : ∑ j, l j ≤ ∑ j, t (σ j) j := Finset.sum_le_sum (fun j _ => hl _ j)
  have h3 : ∑ _i : Fin m, B = m * B := by simp
  have heq : ∑ j, l j = ∑ j, t (σ j) j := by
    apply le_antisymm h2
    rw [← hfib]; omega
  have heq2 : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j = ∑ _i : Fin m, B := by
    apply le_antisymm h1
    omega
  refine ⟨fun i => ?_, fun j => ?_⟩
  · exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 heq2 i (Finset.mem_univ _)
  · exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hl _ j)).1 heq j (Finset.mem_univ _)).symm

lemma ts_split {m A B : ℕ} (T : Fin (A + B) → ℕ) (σ : Fin (A + B) → Fin m) (i : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => σ j = i), T j =
      ∑ e ∈ Finset.univ.filter (fun e : Fin A => σ (Fin.castAdd B e) = i), T (Fin.castAdd B e) +
      ∑ k ∈ Finset.univ.filter (fun k : Fin B => σ (Fin.natAdd A k) = i), T (Fin.natAdd A k) := by
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter, Finset.sum_filter]

lemma ts_nt {p q a b : ℕ} (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime p q)
    (h : a * p + b * q = p * q) : (a = q ∧ b = 0) ∨ (a = 0 ∧ b = p) := by
  have h1 : p ∣ b * q := by
    have : p ∣ a * p + b * q := h ▸ dvd_mul_right p q
    exact (Nat.dvd_add_right (dvd_mul_left p a)).1 this
  have h2 : q ∣ a * p := by
    have : q ∣ a * p + b * q := h ▸ dvd_mul_left q p
    exact (Nat.dvd_add_left (dvd_mul_left q b)).1 this
  obtain ⟨b', hb'⟩ := hcop.dvd_of_dvd_mul_right h1
  obtain ⟨a', ha'⟩ := hcop.symm.dvd_of_dvd_mul_right h2
  subst hb' ha'
  have : p * q * (a' + b') = p * q * 1 := by
    calc p * q * (a' + b') = q * a' * p + p * b' * q := by ring
      _ = p * q * 1 := by rw [h, mul_one]
  have h3 : a' + b' = 1 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp hq) this
  rcases Nat.eq_zero_or_pos a' with h0 | h0
  · right; subst h0; simp at h3; subst h3; simp
  · left; have : b' = 0 := by omega
    subst this; have : a' = 1 := by omega
    subst this; simp

lemma ts_dummy {m n : ℕ} (F' : Finset (Fin m)) (hF : F'.card = n) (r N : ℕ)
    (hN : N ≤ r * (m - n)) :
    ∃ d : Fin N → Fin m, (∀ k, d k ∉ F') ∧
      ∀ i, (Finset.univ.filter (fun k => d k = i)).card ≤ r := by
  classical
  have hc : Fintype.card {i // i ∉ F'} = m - n := by
    rw [Fintype.card_subtype_compl]; simp [hF]
  let e : Fin (m - n) ≃ {i // i ∉ F'} := (Fintype.equivFinOfCardEq hc).symm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain rfl : N = 0 := by simpa using hN
    exact ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun i => by simp⟩
  · have hlt : ∀ k : Fin N, k.1 / r < m - n := fun k =>
      (Nat.div_lt_iff_lt_mul hr).2 (by rw [mul_comm]; exact lt_of_lt_of_le k.2 hN)
    refine ⟨fun k => (e ⟨k.1 / r, hlt k⟩).1, fun k => (e _).2, fun i => ?_⟩
    calc (Finset.univ.filter (fun k : Fin N => (e ⟨k.1 / r, hlt k⟩).1 = i)).card
        ≤ (Finset.univ : Finset (Fin r)).card := by
          apply Finset.card_le_card_of_injOn (fun k => (⟨k.1 % r, Nat.mod_lt _ hr⟩ : Fin r))
          · intro k _; simp
          · intro k1 hk1 k2 hk2 hk
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk1 hk2
            have h12 : e ⟨k1.1 / r, hlt k1⟩ = e ⟨k2.1 / r, hlt k2⟩ :=
              Subtype.ext (hk1.trans hk2.symm)
            have h3 := Fin.mk.inj_iff.1 (e.injective h12)
            have h4 : k1.1 % r = k2.1 % r := by simpa using hk
            apply Fin.ext
            rw [← Nat.div_add_mod k1.1 r, ← Nat.div_add_mod k2.1 r, h3, h4]
      _ = r := by simp

lemma ts_lower (p q n m : ℕ) (hpq : p < q) (S : Fin m → Finset (Fin (q * n)))
    (hm : 0 < p) :
    ∀ (i : Fin m) (j : Fin (q * n + p * (m - n))),
      (if (j : ℕ) < q * n then p else q) ≤ twoTimes p q n S i j := by
  intro i j
  refine Fin.addCases (fun u => ?_) (fun k => ?_) j
  · have h1 := twoTimes_elem p q n S i u
    have h2 : ((Fin.castAdd (p * (m - n)) u : Fin (q * n + p * (m - n))) : ℕ) < q * n := by
      simpa using u.2
    have h3 : twoTimes p q n S i (Fin.castAdd (p * (m - n)) u) = _ := h1
    rw [if_pos h2, h3]
    split_ifs <;> omega
  · have h1 := twoTimes_dummy p q n S i k
    have h2 : ¬ ((Fin.natAdd (q * n) k : Fin (q * n + p * (m - n))) : ℕ) < q * n := by
      simp
    have h3 : twoTimes p q n S i (Fin.natAdd (q * n) k) = _ := h1
    rw [if_neg h2, h3]

theorem no_idle_core {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (σ : Fin (q * n + p * (m - n)) → Fin m)
    (hσ : makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) :
    (∀ i : Fin m, load (fun i j => (twoTimes p q n S i j : ℝ)) σ i = (p * q : ℝ)) ∧
      (∀ u : Fin (q * n), u ∈ S (σ (elemJob p q n m u))) ∧
      (∀ i : Fin m,
        ((Finset.univ.filter (fun u => σ (elemJob p q n m u) = i)).card = q ∧
            ∀ k : Fin (p * (m - n)), σ (dummyJob p q n m k) ≠ i) ∨
          ((∀ u : Fin (q * n), σ (elemJob p q n m u) ≠ i) ∧
            (Finset.univ.filter (fun k => σ (dummyJob p q n m k) = i)).card = p)) := by
  have hq : 0 < q := hp.trans hpq
  have hB : makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ ((p * q : ℕ) : ℝ) := by
    push_cast; exact hσ
  have hle := ts_load_le (twoTimes p q n S) σ (p * q) hB
  have hsum : m * (p * q) ≤ ∑ j : Fin (q * n + p * (m - n)), (if (j : ℕ) < q * n then p else q) := by
    rw [Fin.sum_univ_add]
    have e1 : ∀ u : Fin (q * n), (if ((Fin.castAdd (p * (m - n)) u : Fin (q * n + p * (m - n))) : ℕ) < q * n then p else q) = p := by
      intro u; simp
    have e2 : ∀ k : Fin (p * (m - n)), (if ((Fin.natAdd (q * n) k : Fin (q * n + p * (m - n))) : ℕ) < q * n then p else q) = q := by
      intro k; simp
    simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rcases le_or_gt n m with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [Nat.add_sub_cancel_left]
      nlinarith
    · have : m - n = 0 := by omega
      rw [this]
      have : m + 1 ≤ n := h
      nlinarith [Nat.mul_pos hp hq]
  obtain ⟨hload, htight⟩ := ts_tight (twoTimes p q n S) _ σ (p * q) (ts_lower p q n m hpq S hp) hsum hle
  have hel : ∀ u : Fin (q * n), twoTimes p q n S (σ (elemJob p q n m u)) (elemJob p q n m u) = p := by
    intro u
    have := htight (elemJob p q n m u)
    rw [this]
    have h2 : ((elemJob p q n m u : Fin (q * n + p * (m - n))) : ℕ) < q * n := by
      simp [elemJob]
    simp [h2]
  refine ⟨fun i => ?_, fun u => ?_, fun i => ?_⟩
  · refine (ts_load_nat (twoTimes p q n S) σ i).trans ?_
    rw [hload i]; push_cast; rfl
  · have := hel u
    rw [twoTimes_elem] at this
    by_contra h
    rw [if_neg h] at this
    omega
  · have h := hload i
    rw [ts_split] at h
    have hA : ∑ e ∈ Finset.univ.filter (fun e : Fin (q * n) => σ (Fin.castAdd (p * (m - n)) e) = i),
        twoTimes p q n S i (Fin.castAdd (p * (m - n)) e)
        = (Finset.univ.filter (fun u => σ (elemJob p q n m u) = i)).card * p := by
      apply Finset.sum_const_nat
      intro u hu
      have hu' := (Finset.mem_filter.1 hu).2
      have := hel u
      rw [show elemJob p q n m u = Fin.castAdd (p * (m - n)) u from rfl, hu'] at this
      exact this
    have hD : ∑ k ∈ Finset.univ.filter (fun k : Fin (p * (m - n)) => σ (Fin.natAdd (q * n) k) = i),
        twoTimes p q n S i (Fin.natAdd (q * n) k)
        = (Finset.univ.filter (fun k => σ (dummyJob p q n m k) = i)).card * q := by
      apply Finset.sum_const_nat
      intro k _
      exact twoTimes_dummy p q n S i k
    rw [hA, hD] at h
    rcases ts_nt hp hq hcop h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨h1, fun k hk => ?_⟩
      have : k ∈ Finset.univ.filter (fun k => σ (dummyJob p q n m k) = i) := by simp [hk]
      rw [Finset.card_eq_zero.1 h2] at this
      simp at this
    · right
      refine ⟨fun u hu => ?_, h2⟩
      have : u ∈ Finset.univ.filter (fun u => σ (elemJob p q n m u) = i) := by simp [hu]
      rw [Finset.card_eq_zero.1 h1] at this
      simp at this


theorem matching_core (p q : ℕ) {m n : ℕ} (S : Fin m → Finset (Fin (q * n)))
    (hS : ∀ i, (S i).card = q) (F' : Finset (Fin m)) (hF' : IsQMatching S F') :
    ∃ σ : Fin (q * n + p * (m - n)) → Fin m,
      makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ) := by
  obtain ⟨hcard, hcov⟩ := hF'
  have h : ∀ u : Fin (q * n), ∃ i ∈ F', u ∈ S i := by
    intro u
    have : u ∈ F'.biUnion S := by rw [hcov]; exact Finset.mem_univ u
    simpa [Finset.mem_biUnion] using this
  choose g hgF hgS using h
  obtain ⟨d, hdF, hdc⟩ := ts_dummy F' hcard p (p * (m - n)) le_rfl
  refine ⟨Fin.append g d, ?_⟩
  have key := ts_makespan_le (twoTimes p q n S) (Fin.append g d) (p * q) ?_
  · push_cast at key; exact key
  intro i
  rw [ts_split]
  simp only [Fin.append_left, Fin.append_right]
  have hD : ∑ k ∈ Finset.univ.filter (fun k : Fin (p * (m - n)) => d k = i),
      twoTimes p q n S i (Fin.natAdd (q * n) k)
      = (Finset.univ.filter (fun k : Fin (p * (m - n)) => d k = i)).card * q := by
    apply Finset.sum_const_nat
    intro k _
    exact twoTimes_dummy p q n S i k
  have hA : ∑ e ∈ Finset.univ.filter (fun e : Fin (q * n) => g e = i),
      twoTimes p q n S i (Fin.castAdd (p * (m - n)) e)
      = (Finset.univ.filter (fun e : Fin (q * n) => g e = i)).card * p := by
    apply Finset.sum_const_nat
    intro u hu
    have hu' := (Finset.mem_filter.1 hu).2
    have h1 := twoTimes_elem p q n S i u
    have h2 : u ∈ S i := hu' ▸ hgS u
    rw [if_pos h2] at h1
    exact h1
  rw [hA, hD]
  by_cases hi : i ∈ F'
  · have h0 : (Finset.univ.filter (fun k : Fin (p * (m - n)) => d k = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro k hk
      exact hdF k ((Finset.mem_filter.1 hk).2 ▸ hi)
    have h1 : (Finset.univ.filter (fun e : Fin (q * n) => g e = i)).card ≤ q := by
      refine le_trans (Finset.card_le_card (t := S i) ?_) (hS i).le
      intro u hu
      have hu' := (Finset.mem_filter.1 hu).2
      exact hu' ▸ hgS u
    rw [h0]
    calc _ ≤ q * p + 0 * q := by simpa using Nat.mul_le_mul_right p h1
      _ = p * q := by ring
  · have h0 : (Finset.univ.filter (fun e : Fin (q * n) => g e = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro u hu
      exact hi ((Finset.mem_filter.1 hu).2 ▸ hgF u)
    rw [h0]
    calc 0 * p + (Finset.univ.filter (fun k : Fin (p * (m - n)) => d k = i)).card * q
        ≤ 0 * p + p * q := by simpa using Nat.mul_le_mul_right q (hdc i)
      _ = p * q := by ring

theorem theorem_7_core {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (hS : ∀ i, (S i).card = q) :
    (∀ i j, twoTimes p q n S i j = p ∨ twoTimes p q n S i j = q) ∧
      ((∃ σ : Fin (q * n + p * (m - n)) → Fin m,
          makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) ↔
        ∃ F' : Finset (Fin m), IsQMatching S F') := by
  have hq : 0 < q := hp.trans hpq
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun u => ?_) (fun k => ?_) j
    · have h1 := twoTimes_elem p q n S i u
      have h3 : twoTimes p q n S i (Fin.castAdd (p * (m - n)) u) = _ := h1
      rw [h3]; split_ifs <;> simp
    · have h1 := twoTimes_dummy p q n S i k
      have h3 : twoTimes p q n S i (Fin.natAdd (q * n) k) = _ := h1
      rw [h3]; simp
  · rintro ⟨σ, hσ⟩
    obtain ⟨h1, h2, h3⟩ := no_idle_core hp hpq hcop S σ hσ
    classical
    refine ⟨Finset.univ.filter (fun i => ∃ u, σ (elemJob p q n m u) = i), ?_, ?_⟩
    · set F' := Finset.univ.filter (fun i => ∃ u, σ (elemJob p q n m u) = i) with hF'
      have hfib : ∀ i, (Finset.univ.filter (fun u => σ (elemJob p q n m u) = i)).card
          = if i ∈ F' then q else 0 := by
        intro i
        by_cases hi : i ∈ F'
        · rw [if_pos hi]
          rcases h3 i with ⟨hc, _⟩ | ⟨hno, _⟩
          · exact hc
          · exfalso
            obtain ⟨u, hu⟩ := (Finset.mem_filter.1 hi).2
            exact hno u hu
        · rw [if_neg hi, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro u hu
          exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, u, (Finset.mem_filter.1 hu).2⟩)
      have htot := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin (q * n)))) (t := (Finset.univ : Finset (Fin m)))
        (f := fun u => σ (elemJob p q n m u)) (fun _ _ => Finset.mem_univ _)
      simp only [hfib, Finset.card_univ, Fintype.card_fin] at htot
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul] at htot
      exact Nat.eq_of_mul_eq_mul_right hq (by rw [← htot]; ring)
    · rw [Finset.eq_univ_iff_forall]
      intro u
      rw [Finset.mem_biUnion]
      exact ⟨σ (elemJob p q n m u), Finset.mem_filter.2 ⟨Finset.mem_univ _, u, rfl⟩, h2 u⟩
  · rintro ⟨F', hF'⟩
    exact matching_core p q S hS F' hF'

end UnrelatedSched.TwoTimes

open UnrelatedSched.TwoTimes


theorem solution {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (hS : ∀ i, (S i).card = q) :
    (∀ i j, twoTimes p q n S i j = p ∨ twoTimes p q n S i j = q) ∧
      ((∃ σ : Fin (q * n + p * (m - n)) → Fin m,
          makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) ↔
        ∃ F' : Finset (Fin m), IsQMatching S F') := by
  exact theorem_7_core hp hpq hcop S hS
