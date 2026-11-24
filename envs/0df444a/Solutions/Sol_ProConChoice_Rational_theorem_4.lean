-- Prove2me | solution 1 for ProConChoice.Rational.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:58:44.560863+00:00
-- url     : https://prove2.me/submissions/3a6fd5cb-482c-4f30-996b-1fa13dac2007

import Mathlib

set_option autoImplicit false

private lemma step_term (a b t s : ℝ) (hst : s < t) (ha : a ≤ t) (hb : b ≤ t)
    (ha' : a ≠ t → a ≤ s) (hb' : b ≠ t → b ≤ s) :
    max ((if a = t then s else a) - (if b = t then s else b)) 0
      + (if a = t then (if b ≠ t then t - s else 0) else 0) ≤ max (a - b) 0 := by
  by_cases h1 : a = t <;> by_cases h2 : b = t
  · subst h1; simp [h2]
  · have := hb' h2
    simp only [h1, h2, if_true, if_false, ne_eq, not_false_eq_true]
    rw [max_def, max_def]; split_ifs <;> linarith
  · have := ha' h1
    simp only [h1, h2, if_true, if_false]
    rw [max_def, max_def]; split_ifs <;> linarith
  · simp [h1, h2]

private lemma const_case {m n : ℕ} (r : Fin m → ℝ) (c : Fin n → ℝ) (hsum : ∑ i, r i = ∑ j, c j)
    (t : ℝ) (u : Fin m → ℝ) (w : Fin n → ℝ) (hu : ∀ i, u i = t) (hw : ∀ j, w j = t) :
    ∑ i, u i * r i - ∑ j, w j * c j ≤ ∑ i, ∑ j, max (u i - w j) 0 := by
  simp only [hu, hw, sub_self, max_self, Finset.sum_const_zero, ← Finset.mul_sum, hsum]
  simp

private lemma key {m n : ℕ} (r : Fin m → ℝ) (c : Fin n → ℝ) (hsum : ∑ i, r i = ∑ j, c j)
    (hcut : ∀ I : Finset (Fin m), ∀ J : Finset (Fin n),
        ∑ i ∈ I, r i - ∑ j ∈ Jᶜ, c j ≤ (I.card : ℝ) * J.card) :
    ∀ (N : ℕ) (u : Fin m → ℝ) (w : Fin n → ℝ),
      (Finset.univ.image u ∪ Finset.univ.image w).card ≤ N →
      ∑ i, u i * r i - ∑ j, w j * c j ≤ ∑ i, ∑ j, max (u i - w j) 0 := by
  intro N
  induction N with
  | zero =>
    intro u w hN
    have hV := Finset.card_eq_zero.mp (Nat.le_zero.mp hN)
    refine const_case r c hsum 0 u w (fun i => ?_) (fun j => ?_)
    · have : u i ∈ Finset.univ.image u ∪ Finset.univ.image w :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ i))
      rw [hV] at this; simp at this
    · have : w j ∈ Finset.univ.image u ∪ Finset.univ.image w :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem w (Finset.mem_univ j))
      rw [hV] at this; simp at this
  | succ N ih =>
    intro u w hN
    set V := Finset.univ.image u ∪ Finset.univ.image w with hVdef
    have memu : ∀ i, u i ∈ V := fun i =>
      Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ i))
    have memw : ∀ j, w j ∈ V := fun j =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem w (Finset.mem_univ j))
    rcases V.eq_empty_or_nonempty with hV | hV
    · refine const_case r c hsum 0 u w (fun i => ?_) (fun j => ?_)
      · have := memu i; rw [hV] at this; simp at this
      · have := memw j; rw [hV] at this; simp at this
    set t := V.max' hV with ht
    have htV : t ∈ V := V.max'_mem hV
    have hut : ∀ i, u i ≤ t := fun i => V.le_max' _ (memu i)
    have hwt : ∀ j, w j ≤ t := fun j => V.le_max' _ (memw j)
    rcases (V.erase t).eq_empty_or_nonempty with hE | hE
    · have hall : ∀ x ∈ V, x = t := fun x hx => by
        by_contra hne
        have : x ∈ V.erase t := Finset.mem_erase.mpr ⟨hne, hx⟩
        rw [hE] at this; simp at this
      exact const_case r c hsum t u w (fun i => hall _ (memu i)) (fun j => hall _ (memw j))
    set s := (V.erase t).max' hE with hs
    have hsV : s ∈ V.erase t := Finset.max'_mem _ _
    have hst : s < t := lt_of_le_of_ne (V.le_max' s (Finset.mem_of_mem_erase hsV))
      (Finset.ne_of_mem_erase hsV)
    have hus : ∀ i, u i ≠ t → u i ≤ s := fun i h =>
      (V.erase t).le_max' _ (Finset.mem_erase.mpr ⟨h, memu i⟩)
    have hws : ∀ j, w j ≠ t → w j ≤ s := fun j h =>
      (V.erase t).le_max' _ (Finset.mem_erase.mpr ⟨h, memw j⟩)
    set u' : Fin m → ℝ := fun i => if u i = t then s else u i with hu'
    set w' : Fin n → ℝ := fun j => if w j = t then s else w j with hw'
    have hcard : (Finset.univ.image u' ∪ Finset.univ.image w').card ≤ N := by
      have hsub : Finset.univ.image u' ∪ Finset.univ.image w' ⊆ V.erase t := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
          by_cases h : u k = t
          · simp only [u', h, if_true]; exact hsV
          · simp only [u', h, if_false]; exact Finset.mem_erase.mpr ⟨h, memu k⟩
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
          by_cases h : w k = t
          · simp only [w', h, if_true]; exact hsV
          · simp only [w', h, if_false]; exact Finset.mem_erase.mpr ⟨h, memw k⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem htV] at this
      omega
    have IH := ih u' w' hcard
    set S := Finset.univ.filter (fun i => u i = t) with hS
    set Jc := Finset.univ.filter (fun j => w j ≠ t) with hJc
    have hc := hcut S Jc
    have hJcc : Jcᶜ = Finset.univ.filter (fun j => w j = t) := by
      ext j; simp [Jc]
    have e1 : ∑ i, u i * r i = ∑ i, u' i * r i + (t - s) * ∑ i ∈ S, r i := by
      rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : u i = t
      · simp only [u', h, if_true]; ring
      · simp only [u', h, if_false]; ring
    have e2 : ∑ j, w j * c j = ∑ j, w' j * c j + (t - s) * ∑ j ∈ Jcᶜ, c j := by
      rw [hJcc, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : w j = t
      · simp only [w', h, if_true]; ring
      · simp only [w', h, if_false]; ring
    have e3 : ∑ i, ∑ j, max (u' i - w' j) 0 + (t - s) * ((S.card : ℝ) * Jc.card)
        ≤ ∑ i, ∑ j, max (u i - w j) 0 := by
      have hcnt : (t - s) * ((S.card : ℝ) * Jc.card) = ∑ i ∈ S, ∑ j ∈ Jc, (t - s) := by
        simp [Finset.sum_const]; ring
      rw [hcnt]
      calc ∑ i, ∑ j, max (u' i - w' j) 0 + ∑ i ∈ S, ∑ j ∈ Jc, (t - s)
          = ∑ i, ∑ j, (max (u' i - w' j) 0
              + (if u i = t then (if w j ≠ t then t - s else 0) else 0)) := by
            rw [Finset.sum_filter, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_add_distrib]
            by_cases h : u i = t
            · simp only [h, if_true, Jc, Finset.sum_filter]
            · simp only [h, if_false, Finset.sum_const_zero]
        _ ≤ ∑ i, ∑ j, max (u i - w j) 0 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              step_term (u i) (w j) t s hst (hut i) (hwt j) (hus i) (hws j)
    have hmul := mul_le_mul_of_nonneg_left hc (le_of_lt (sub_pos.mpr hst))
    rw [mul_sub] at hmul
    linarith

theorem solution (m n : ℕ) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ i, r i = ∑ j, c j) :
    (∃ A : Matrix (Fin m) (Fin n) ℝ,
        (∀ i, ∑ j, A i j = r i) ∧ (∀ j, ∑ i, A i j = c j) ∧ (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)) ↔
    (∀ I : Finset (Fin m), ∀ J : Finset (Fin n),
        ∑ i ∈ I, r i - ∑ j ∈ Jᶜ, c j ≤ (I.card : ℝ) * J.card) := by
  constructor
  · rintro ⟨A, hrow, hcol, hA⟩ I J
    have h1 : ∑ i ∈ I, r i = ∑ i ∈ I, ∑ j ∈ J, A i j + ∑ i ∈ I, ∑ j ∈ Jᶜ, A i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_add_sum_compl, hrow]
    have h2 : ∑ i ∈ I, ∑ j ∈ J, A i j ≤ (I.card : ℝ) * J.card := by
      calc ∑ i ∈ I, ∑ j ∈ J, A i j ≤ ∑ i ∈ I, ∑ j ∈ J, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hA i j).2
        _ = _ := by simp
    have h3 : ∑ i ∈ I, ∑ j ∈ Jᶜ, A i j ≤ ∑ j ∈ Jᶜ, c j := by
      rw [show (∑ i ∈ I, ∑ j ∈ Jᶜ, A i j) = ∑ j ∈ Jᶜ, ∑ i ∈ I, A i j from Finset.sum_comm]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← hcol j]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => (hA i j).1
    linarith
  · intro hcut
    by_contra hne
    let L : (Fin m → Fin n → ℝ) →ₗ[ℝ] (Fin m ⊕ Fin n → ℝ) :=
      { toFun := fun A k => Sum.elim (fun i => ∑ j, A i j) (fun j => ∑ i, A i j) k
        map_add' := by
          intro A B; funext k; cases k <;> simp [Finset.sum_add_distrib]
        map_smul' := by
          intro a A; funext k; cases k <;> simp [Finset.mul_sum] }
    let B : Set (Fin m → Fin n → ℝ) := Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (0:ℝ) 1
    have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    have hBv : Convex ℝ B := convex_pi fun _ _ => convex_pi fun _ _ => convex_Icc 0 1
    have hPc : IsClosed (L '' B) := (hBc.image L.continuous_of_finiteDimensional).isClosed
    have hPv : Convex ℝ (L '' B) := hBv.linear_image L
    have hx : Sum.elim r c ∉ L '' B := by
      rintro ⟨A, hA, hLA⟩
      apply hne
      refine ⟨A, fun i => ?_, fun j => ?_, fun i j => ?_⟩
      · have := congrFun hLA (Sum.inl i); simpa [L] using this
      · have := congrFun hLA (Sum.inr j); simpa [L] using this
      · exact hA i (Set.mem_univ _) j (Set.mem_univ _)
    obtain ⟨f, u0, hfB, hfx⟩ := geometric_hahn_banach_closed_point hPv hPc hx
    set e : Fin m ⊕ Fin n → ℝ := fun k => f (fun l => if k = l then 1 else 0) with he
    have hf : ∀ y, f y = ∑ k, y k * e k := fun y => by
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin m ⊕ Fin n → ℝ) →ₗ[ℝ] ℝ) y
      simpa [smul_eq_mul] using this
    set α : Fin m → ℝ := fun i => e (Sum.inl i) with hα
    set β : Fin n → ℝ := fun j => e (Sum.inr j) with hβ
    set A : Fin m → Fin n → ℝ := fun i j => if 0 < α i + β j then 1 else 0 with hAdef
    have hAB : A ∈ B := by
      intro i _ j _
      simp only [A]
      split_ifs <;> simp
    have h1 := hfB (L A) ⟨A, hAB, rfl⟩
    rw [hf, Fintype.sum_sum_type] at h1 hfx
    have hLA : ∑ i, (∑ j, A i j) * α i + ∑ j, (∑ i, A i j) * β j
        = ∑ i, ∑ j, max (α i - -β j) 0 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm (f := fun j i => A i j * β j), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [A, sub_neg_eq_add]
      split_ifs with h
      · rw [max_eq_left h.le]; ring
      · rw [max_eq_right (not_lt.mp h)]; ring
    have hk := key r c hsum hcut _ α (fun j => -β j) le_rfl
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr] at h1 hfx
    have hk' : ∑ i, α i * r i + ∑ j, β j * c j ≤ ∑ i, ∑ j, max (α i - -β j) 0 := by
      have : ∑ j, -β j * c j = -∑ j, β j * c j := by
        rw [← Finset.sum_neg_distrib]; simp
      linarith
    have h1' : ∑ i, (∑ j, A i j) * α i + ∑ j, (∑ i, A i j) * β j < u0 := h1
    have hfx' : u0 < ∑ i, r i * α i + ∑ j, c j * β j := hfx
    simp only [mul_comm (r _), mul_comm (c _)] at hfx'
    linarith
