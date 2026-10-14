-- Prove2me | solution 1 for UnrelatedSched.TwoTimes.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:55:44.977447+00:00
-- url     : https://prove2.me/submissions/ea93d1ec-fdc5-4c6d-a09d-7ef93b011c3d

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem4Instance

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


lemma t4_elem {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (e : Fin (3 * n)) :
    thm4Times T i (Fin.castAdd (m - n) e)
      = if tripleCoord (T i) (finProdFinEquiv.symm e).1 = (finProdFinEquiv.symm e).2 then 1 else 3 := by
  simp [thm4Times]

lemma t4_dummy {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (k : Fin (m - n)) :
    thm4Times T i (Fin.natAdd (3 * n) k) = 3 := by
  simp [thm4Times]

lemma t4_lower {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    ∀ (i : Fin m) (j : Fin (3 * n + (m - n))),
      (if (j : ℕ) < 3 * n then 1 else 3) ≤ thm4Times T i j := by
  intro i j
  refine Fin.addCases (fun u => ?_) (fun k => ?_) j
  · have h2 : ((Fin.castAdd (m - n) u : Fin (3 * n + (m - n))) : ℕ) < 3 * n := by simp
    rw [if_pos h2, t4_elem]
    split_ifs <;> omega
  · have h2 : ¬ ((Fin.natAdd (3 * n) k : Fin (3 * n + (m - n))) : ℕ) < 3 * n := by simp
    rw [if_neg h2, t4_dummy]

theorem t4_fwd {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (σ : Fin (3 * n + (m - n)) → Fin m)
    (hσ : makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ 3) :
    ∃ F' : Finset (Fin m), IsThreeDimMatching T F' := by
  classical
  have hB : makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ ((3 : ℕ) : ℝ) := by
    push_cast; exact hσ
  have hle := ts_load_le (thm4Times T) σ 3 hB
  have hsum : m * 3 ≤ ∑ j : Fin (3 * n + (m - n)), (if (j : ℕ) < 3 * n then 1 else 3) := by
    rw [Fin.sum_univ_add]
    have e1 : ∀ u : Fin (3 * n), (if ((Fin.castAdd (m - n) u : Fin (3 * n + (m - n))) : ℕ) < 3 * n then 1 else 3) = 1 := by
      intro u; simp
    have e2 : ∀ k : Fin (m - n), (if ((Fin.natAdd (3 * n) k : Fin (3 * n + (m - n))) : ℕ) < 3 * n then 1 else 3) = 3 := by
      intro k; simp
    simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  obtain ⟨hload, htight⟩ := ts_tight (thm4Times T) _ σ 3 (t4_lower T) hsum hle
  have hel : ∀ e : Fin (3 * n),
      tripleCoord (T (σ (Fin.castAdd (m - n) e))) (finProdFinEquiv.symm e).1
        = (finProdFinEquiv.symm e).2 := by
    intro e
    have h1 := htight (Fin.castAdd (m - n) e)
    have h2 : ((Fin.castAdd (m - n) e : Fin (3 * n + (m - n))) : ℕ) < 3 * n := by simp
    rw [if_pos h2, t4_elem] at h1
    by_contra h
    rw [if_neg h] at h1
    omega
  set F' := Finset.univ.filter (fun i => ∃ e : Fin (3 * n), σ (Fin.castAdd (m - n) e) = i) with hF'
  have hfib : ∀ i, (Finset.univ.filter (fun e : Fin (3 * n) => σ (Fin.castAdd (m - n) e) = i)).card
      = if i ∈ F' then 3 else 0 := by
    intro i
    have h := hload i
    rw [ts_split] at h
    have hA : ∑ e ∈ Finset.univ.filter (fun e : Fin (3 * n) => σ (Fin.castAdd (m - n) e) = i),
        thm4Times T i (Fin.castAdd (m - n) e)
        = (Finset.univ.filter (fun e : Fin (3 * n) => σ (Fin.castAdd (m - n) e) = i)).card * 1 := by
      apply Finset.sum_const_nat
      intro u hu
      have hu' := (Finset.mem_filter.1 hu).2
      rw [t4_elem, if_pos (hu' ▸ hel u)]
    have hD : ∑ k ∈ Finset.univ.filter (fun k : Fin (m - n) => σ (Fin.natAdd (3 * n) k) = i),
        thm4Times T i (Fin.natAdd (3 * n) k)
        = (Finset.univ.filter (fun k : Fin (m - n) => σ (Fin.natAdd (3 * n) k) = i)).card * 3 := by
      apply Finset.sum_const_nat
      intro k _
      exact t4_dummy T i k
    rw [hA, hD] at h
    by_cases hi : i ∈ F'
    · rw [if_pos hi]
      obtain ⟨e, he⟩ := (Finset.mem_filter.1 hi).2
      have : 0 < (Finset.univ.filter (fun e : Fin (3 * n) => σ (Fin.castAdd (m - n) e) = i)).card :=
        Finset.card_pos.2 ⟨e, by simp [he]⟩
      omega
    · rw [if_neg hi, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro u hu
      exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, u, (Finset.mem_filter.1 hu).2⟩)
  have hcardF : F'.card = n := by
    have htot := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin (3 * n)))) (t := (Finset.univ : Finset (Fin m)))
      (f := fun u => σ (Fin.castAdd (m - n) u)) (fun _ _ => Finset.mem_univ _)
    simp only [hfib, Finset.card_univ, Fintype.card_fin] at htot
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul] at htot
    omega
  have hcov : ∀ c : Fin 3, ∀ x : Fin n, ∃ i ∈ F', tripleCoord (T i) c = x := by
    intro c x
    refine ⟨σ (Fin.castAdd (m - n) (finProdFinEquiv (c, x))),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, _, rfl⟩, ?_⟩
    have := hel (finProdFinEquiv (c, x))
    simpa using this
  refine ⟨F', hcardF, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi, h⟩ := hcov 0 j
    exact ⟨i, hi, by simpa [tripleCoord] using h⟩
  · intro j
    obtain ⟨i, hi, h⟩ := hcov 1 j
    exact ⟨i, hi, by simpa [tripleCoord] using h⟩
  · intro j
    obtain ⟨i, hi, h⟩ := hcov 2 j
    exact ⟨i, hi, by simpa [tripleCoord] using h⟩

theorem t4_bwd {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (F' : Finset (Fin m))
    (hF : IsThreeDimMatching T F') :
    ∃ σ : Fin (3 * n + (m - n)) → Fin m,
      makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ 3 := by
  obtain ⟨hcard, h0, h1, h2⟩ := hF
  have hcov : ∀ c : Fin 3, ∀ x : Fin n, ∃ i ∈ F', tripleCoord (T i) c = x := by
    intro c x
    fin_cases c
    · obtain ⟨i, hi, h⟩ := h0 x; exact ⟨i, hi, by simpa [tripleCoord] using h⟩
    · obtain ⟨i, hi, h⟩ := h1 x; exact ⟨i, hi, by simpa [tripleCoord] using h⟩
    · obtain ⟨i, hi, h⟩ := h2 x; exact ⟨i, hi, by simpa [tripleCoord] using h⟩
  choose G hGF hGc using hcov
  obtain ⟨d, hdF, hdc⟩ := ts_dummy F' hcard 1 (m - n) (by simp)
  let g : Fin (3 * n) → Fin m := fun e => G (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2
  refine ⟨Fin.append g d, ?_⟩
  have key := ts_makespan_le (thm4Times T) (Fin.append g d) 3 ?_
  · push_cast at key; exact key
  intro i
  rw [ts_split]
  simp only [Fin.append_left, Fin.append_right]
  have hD : ∑ k ∈ Finset.univ.filter (fun k : Fin (m - n) => d k = i),
      thm4Times T i (Fin.natAdd (3 * n) k)
      = (Finset.univ.filter (fun k : Fin (m - n) => d k = i)).card * 3 := by
    apply Finset.sum_const_nat
    intro k _
    exact t4_dummy T i k
  have hA : ∑ e ∈ Finset.univ.filter (fun e : Fin (3 * n) => g e = i),
      thm4Times T i (Fin.castAdd (m - n) e)
      = (Finset.univ.filter (fun e : Fin (3 * n) => g e = i)).card * 1 := by
    apply Finset.sum_const_nat
    intro u hu
    have hu' := (Finset.mem_filter.1 hu).2
    rw [t4_elem, if_pos]
    have := hGc (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2
    rw [← hu']; exact this
  rw [hA, hD]
  by_cases hi : i ∈ F'
  · have h0 : (Finset.univ.filter (fun k : Fin (m - n) => d k = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro k hk
      exact hdF k ((Finset.mem_filter.1 hk).2 ▸ hi)
    have h1 : (Finset.univ.filter (fun e : Fin (3 * n) => g e = i)).card ≤ 3 := by
      calc _ ≤ (Finset.univ : Finset (Fin 3)).card := by
            apply Finset.card_le_card_of_injOn (fun e => (finProdFinEquiv.symm e).1)
            · intro e _; simp
            · intro e1 he1 e2 he2 hk
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he1 he2
              have c1 := hGc (finProdFinEquiv.symm e1).1 (finProdFinEquiv.symm e1).2
              have c2 := hGc (finProdFinEquiv.symm e2).1 (finProdFinEquiv.symm e2).2
              have hk' : (finProdFinEquiv.symm e1).1 = (finProdFinEquiv.symm e2).1 := hk
              have : (finProdFinEquiv.symm e1).2 = (finProdFinEquiv.symm e2).2 := by
                rw [← c1, ← c2]
                have e1' : G (finProdFinEquiv.symm e1).1 (finProdFinEquiv.symm e1).2 = i := he1
                have e2' : G (finProdFinEquiv.symm e2).1 (finProdFinEquiv.symm e2).2 = i := he2
                rw [e1', hk', e2']
              exact finProdFinEquiv.symm.injective (Prod.ext hk' this)
        _ = 3 := by simp
    rw [h0]; omega
  · have h0 : (Finset.univ.filter (fun e : Fin (3 * n) => g e = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro u hu
      exact hi ((Finset.mem_filter.1 hu).2 ▸ hGF _ _)
    have := hdc i
    rw [h0]; omega

theorem theorem_4_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (3 * n + (m - n)) → Fin m,
        makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ 3) ↔
      ∃ F' : Finset (Fin m), IsThreeDimMatching T F' := by
  constructor
  · rintro ⟨σ, hσ⟩; exact t4_fwd T σ hσ
  · rintro ⟨F', hF'⟩; exact t4_bwd T F' hF'

end UnrelatedSched.TwoTimes

open UnrelatedSched.TwoTimes


theorem solution {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (3 * n + (m - n)) → Fin m,
        makespan (fun i j => (thm4Times T i j : ℝ)) σ ≤ 3) ↔
      ∃ F' : Finset (Fin m), IsThreeDimMatching T F' := by
  exact theorem_4_core T
