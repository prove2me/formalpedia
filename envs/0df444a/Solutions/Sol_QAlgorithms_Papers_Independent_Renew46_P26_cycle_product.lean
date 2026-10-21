-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.cycle_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:46:57.597451+00:00
-- url     : https://prove2.me/submissions/7c29fa68-14d4-4845-8315-077b8748b5f7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

open Equiv
def g64m_P {k : ℕ} (m : ℕ) (g : Perm (Fin k)) : Prop :=
  (∀ x : Fin k, m < x.val → g x = x) ∧ ∀ x y : Fin k, x.val ≤ m → y.val ≤ m → ∃ r : ℕ, (g ^ r) x = y

lemma g64m_pow_succ {α : Type*} (f : Perm α) (s : ℕ) (x : α) : (f ^ (s + 1)) x = f ((f ^ s) x) := by
  rw [pow_succ', Perm.mul_apply]

lemma g64m_sym {k : ℕ} (f : Perm (Fin k)) (x y : Fin k) (r : ℕ) (h : (f ^ r) x = y) :
    ∃ s : ℕ, (f ^ s) y = x := by
  refine ⟨orderOf f * r - r, ?_⟩
  have h1 : 0 < orderOf f := orderOf_pos f
  have h2 : orderOf f * r - r + r = orderOf f * r := by
    have : r ≤ orderOf f * r := Nat.le_mul_of_pos_left r h1
    omega
  rw [← h, ← Perm.mul_apply, ← pow_add, h2, pow_mul, pow_orderOf_eq_one, one_pow, Perm.one_apply]

lemma g64m_agree {α : Type*} (f f' : Perm α) (x : α) (r : ℕ)
    (h : ∀ s < r, f' ((f ^ s) x) = f ((f ^ s) x)) : ∀ s ≤ r, (f' ^ s) x = (f ^ s) x := by
  intro s hs
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [g64m_pow_succ, g64m_pow_succ, ih (by omega), h s (by omega)]

lemma g64m_pres {k : ℕ} (m : ℕ) (g : Perm (Fin k)) (hg : ∀ x : Fin k, m < x.val → g x = x)
    (a : Fin k) (ha : a.val ≤ m) : ∀ s : ℕ, ((g ^ s) a).val ≤ m := by
  intro s
  induction s with
  | zero => simpa using ha
  | succ s ih =>
    rw [g64m_pow_succ]
    by_contra hc
    rw [not_le] at hc
    have := hg _ hc
    have h2 := g.injective this
    rw [h2] at hc
    omega

lemma g64m_trans {α : Type*} (f : Perm α) (x y z : α) (a b : ℕ) (h1 : (f ^ a) x = y)
    (h2 : (f ^ b) y = z) : (f ^ (b + a)) x = z := by
  rw [pow_add, Perm.mul_apply, h1, h2]

lemma g64m_stepA {k m : ℕ} (hM : m + 1 < k) (g : Perm (Fin k)) (hg : g64m_P m g)
    (j : Fin k) (hj : j.val ≤ m) : g64m_P (m + 1) (g * swap j ⟨m + 1, hM⟩) := by
  set M : Fin k := ⟨m + 1, hM⟩ with hMdef
  set h := g * swap j M with hh
  have hjM : j ≠ M := by intro e; rw [e] at hj; simp [hMdef] at hj
  have hgM : g M = M := hg.1 M (by simp [hMdef])
  have hhj : h j = M := by simp [hh, hgM]
  -- every x ≤ m reaches M under h
  have reachM : ∀ x : Fin k, x.val ≤ m + 1 → ∃ r, (h ^ r) x = M := by
    intro x hx
    by_cases hxM : x = M
    · exact ⟨0, by simp [hxM]⟩
    have hx' : x.val ≤ m := by
      have : x.val ≠ m + 1 := fun e => hxM (Fin.ext (by simp [hMdef, e]))
      omega
    have hex : ∃ r, (g ^ r) x = j := hg.2 x j hx' hj
    classical
    let r := Nat.find hex
    have hr : (g ^ r) x = j := Nat.find_spec hex
    have hmin : ∀ s < r, (g ^ s) x ≠ j := fun s hs => Nat.find_min hex hs
    have hag := g64m_agree g h x r (fun s hs => by
      have h1 := hmin s hs
      have h2 : (g ^ s) x ≠ M := by
        intro e
        have := g64m_pres m g hg.1 x hx' s
        rw [e] at this; simp [hMdef] at this
      simp [hh, swap_apply_of_ne_of_ne h1 h2]) r le_rfl
    refine ⟨r + 1, ?_⟩
    rw [g64m_pow_succ, hag, hr, hhj]
  refine ⟨fun x hx => ?_, fun x y hx hy => ?_⟩
  · have h1 : x ≠ j := fun e => by rw [e] at hx; omega
    have h2 : x ≠ M := fun e => by rw [e] at hx; simp [hMdef] at hx
    simp [hh, swap_apply_of_ne_of_ne h1 h2, hg.1 x (by omega)]
  · obtain ⟨a, ha⟩ := reachM x hx
    obtain ⟨b0, hb0⟩ := reachM y hy
    obtain ⟨b, hb⟩ := g64m_sym h y M b0 hb0
    exact ⟨b + a, g64m_trans h x M y a b ha hb⟩

lemma g64m_stepB {k m : ℕ} (hM : m + 1 < k) (h : Perm (Fin k)) (hh : g64m_P (m + 1) h) :
    (h⁻¹ ⟨m + 1, hM⟩).val ≤ m ∧
      g64m_P m (h * swap (h⁻¹ ⟨m + 1, hM⟩) ⟨m + 1, hM⟩) := by
  set M : Fin k := ⟨m + 1, hM⟩ with hMdef
  set j := h⁻¹ M with hjdef
  have hhj : h j = M := by simp [hjdef]
  have h0 : (⟨0, by omega⟩ : Fin k) ≠ M := by intro e; simp [hMdef] at e
  have hMmoves : h M ≠ M := by
    intro e
    obtain ⟨r, hr⟩ := hh.2 M ⟨0, by omega⟩ (by simp [hMdef]) (by simp)
    have : ∀ s : ℕ, (h ^ s) M = M := by
      intro s; induction s with
      | zero => rfl
      | succ s ih => rw [g64m_pow_succ, ih, e]
    rw [this] at hr; exact h0 hr.symm
  have hjM : j ≠ M := by intro e; rw [e] at hhj; exact hMmoves hhj
  have hjle : j.val ≤ m := by
    by_contra hc; rw [not_le] at hc
    have hc' : m + 1 < j.val := by
      have : j.val ≠ m + 1 := fun e => hjM (Fin.ext (by simp [hMdef, e]))
      omega
    have := hh.1 j hc'
    rw [this] at hhj; exact hjM hhj
  refine ⟨hjle, ?_⟩
  set g := h * swap j M with hg
  have hgj : g j = h M := by simp [hg]
  -- every x ≤ m reaches j under g
  have reachj : ∀ x : Fin k, x.val ≤ m → ∃ r, (g ^ r) x = j := by
    intro x hx
    have hex : ∃ r, (h ^ r) x = j := hh.2 x j (by omega) (by omega)
    classical
    let r := Nat.find hex
    have hr : (h ^ r) x = j := Nat.find_spec hex
    have hmin : ∀ s < r, (h ^ s) x ≠ j := fun s hs => Nat.find_min hex hs
    have hag := g64m_agree h g x r (fun s hs => by
      have h1 := hmin s hs
      have h2 : (h ^ s) x ≠ M := by
        intro e
        cases s with
        | zero =>
          simp at e; rw [e] at hx; simp [hMdef] at hx
        | succ s =>
          rw [g64m_pow_succ] at e
          have : (h ^ s) x = j := by rw [hjdef, ← e]; simp
          exact hmin s (by omega) this
      simp [hg, swap_apply_of_ne_of_ne h1 h2]) r le_rfl
    exact ⟨r, by rw [hag, hr]⟩
  refine ⟨fun x hx => ?_, fun x y hx hy => ?_⟩
  · by_cases hxM : x = M
    · rw [hxM]; simp [hg, hhj]
    · have h1 : x ≠ j := fun e => by rw [e] at hx; omega
      have hx2 : m + 1 < x.val := by
        have : x.val ≠ m + 1 := fun e => hxM (Fin.ext (by simp [hMdef, e]))
        omega
      simp [hg, swap_apply_of_ne_of_ne h1 hxM, hh.1 x hx2]
  · obtain ⟨a, ha⟩ := reachj x hx
    obtain ⟨b0, hb0⟩ := reachj y hy
    obtain ⟨b, hb⟩ := g64m_sym g y j b0 hb0
    exact ⟨b + a, g64m_trans g x j y a b ha hb⟩

lemma g64m_base {k : ℕ} (g : Perm (Fin k)) : g64m_P 0 g ↔ g = 1 := by
  constructor
  · rintro ⟨h1, _⟩
    ext x
    by_cases hx : 0 < x.val
    · simp [h1 x hx]
    · have hx0 : x.val = 0 := by omega
      by_contra hc
      have hne : 0 < (g x).val := by
        rcases Nat.eq_zero_or_pos (g x).val with e | e
        · exact absurd (by simp [e, hx0]) hc
        · exact e
      have := h1 (g x) hne
      have := g.injective this
      rw [this] at hne; omega
  · rintro rfl
    refine ⟨fun x _ => rfl, fun x y hx hy => ⟨0, ?_⟩⟩
    exact Fin.ext (by simp; omega)

lemma g64m_main {k : ℕ} : ∀ (m : ℕ) (hm : m + 1 ≤ k),
    (List.ofFn (fun i : Fin m => yjm (⟨i.val + 1, by omega⟩ : Fin k))).prod =
      ∑ g ∈ Finset.univ.filter (fun g : Perm (Fin k) => g64m_P m g),
        MonoidAlgebra.single g (1 : ℂ) := by
  intro m
  induction m with
  | zero =>
    intro hm
    have : Finset.univ.filter (fun g : Perm (Fin k) => g64m_P 0 g) = {1} := by
      ext g; simp [g64m_base]
    rw [this, Finset.sum_singleton]
    simp [MonoidAlgebra.one_def]
  | succ m ih =>
    intro hm
    rw [List.ofFn_succ', List.prod_concat]
    have ih' := ih (by omega)
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih']
    set M : Fin k := ⟨m + 1, by omega⟩ with hMdef
    have hy : yjm M = ∑ j ∈ Finset.univ.filter (fun j : Fin k => j < M),
        MonoidAlgebra.single (swap j M) (1 : ℂ) := rfl
    rw [hy, Finset.sum_mul_sum]
    simp only [MonoidAlgebra.single_mul_single, one_mul]
    rw [← Finset.sum_product']
    have hM : m + 1 < k := by omega
    refine Finset.sum_nbij' (fun p => p.1 * swap p.2 M) (fun h => (h * swap (h⁻¹ M) M, h⁻¹ M))
      ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨g, j⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact g64m_stepA hM g hp.1 j (by have := hp.2; rw [Fin.lt_def] at this; simp [hMdef] at this; omega)
    · intro h hh
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      have := g64m_stepB hM h hh
      refine ⟨this.2, ?_⟩
      rw [Fin.lt_def]; simp only [hMdef]; omega
    · rintro ⟨g, j⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hgM : g M = M := hp.1.1 M (by simp [hMdef])
      have hinv : (g * swap j M)⁻¹ M = j := by
        rw [mul_inv_rev, swap_inv, Perm.mul_apply]
        have : g⁻¹ M = M := by rw [Perm.inv_eq_iff_eq, hgM]
        rw [this, swap_apply_right]
      simp only [hinv, mul_assoc, swap_mul_self, mul_one]
    · intro h _
      simp only [mul_assoc, swap_mul_self, mul_one]

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (List.ofFn (fun i : Fin (k - 1) => yjm (⟨i.val + 1, by omega⟩ : Fin k))).prod =
      ∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin k) => IsFullCycle g),
        MonoidAlgebra.single g (1 : ℂ) := by
  rw [g64m_main (k - 1) (by omega)]
  congr 1
  apply Finset.filter_congr
  intro g _
  constructor
  · intro h i j
    exact h.2 i j (by omega) (by omega)
  · intro h
    exact ⟨fun x hx => by omega, fun x y _ _ => h x y⟩
