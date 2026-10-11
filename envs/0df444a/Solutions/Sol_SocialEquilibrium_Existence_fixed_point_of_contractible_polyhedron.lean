-- Prove2me | solution 1 for SocialEquilibrium.Existence.fixed_point_of_contractible_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T11:50:32.986728+00:00
-- url     : https://prove2.me/submissions/845c0eab-4bb7-4170-84e4-467f1db64733

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_graph

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace BrouwerLib

open Finset

/-! ## Parity of an involution -/

/-- An involution on a finite set has as many fixed points as the set has elements, mod 2. -/
theorem card_zmod_two_eq_card_fixed {α : Type u} [DecidableEq α] (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) :
    ((s.card : ℕ) : ZMod 2) = ((s.filter (fun a => g a = a)).card : ZMod 2) := by
  have h1 : ∑ a ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => g a) ?_ ?_ ?_ ?_
    · intro a _; decide
    · intro a ha _; exact (Finset.mem_filter.mp ha).2
    · intro a ha
      obtain ⟨has, hne⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨hmem a has, ?_⟩
      rw [hinv a has]; exact fun h => hne h.symm
    · intro a ha; exact hinv a (Finset.mem_filter.mp ha).1
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun a => g a = a)
  rw [← h2]
  push_cast
  have h3 : (((s.filter (fun a => ¬ g a = a)).card : ℕ) : ZMod 2)
      = ∑ a ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) := by simp
  rw [h3, h1, add_zero]

/-! ## Kuhn simplices -/

/-- Vertex `j` of the Kuhn simplex with base `v` and rank permutation `r`: coordinate `i` is
incremented at step `r i`, so vertex `j` is `v + ∑_{r i < j} e_i`. -/
def kvert {n : ℕ} (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)) (j : ℕ) : Fin n → ℕ :=
  fun i => v i + if ((r i : Fin n) : ℕ) < j then 1 else 0

/-- Door condition: the facet opposite vertex `k` carries every label `1, …, n`. -/
def Door {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (v : Fin n → ℕ) (r : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) : Prop :=
  ∀ c, 1 ≤ c → c ≤ n → ∃ j : Fin (n + 1), j ≠ k ∧ ℓ (kvert v r j) = c

/-- A completely labelled Kuhn simplex: its `n + 1` vertices carry all labels `0, …, n`. -/
def FullyLabelled {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ c, c ≤ n → ∃ j : Fin (n + 1), ℓ (kvert v r j) = c

/-- The base points of the Kuhn simplices of the grid `{0, …, p}^n`. -/
def kgrid (n p : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ : Fin n => Finset.range p

theorem mem_kgrid {n p : ℕ} (v : Fin n → ℕ) : v ∈ kgrid n p ↔ ∀ i, v i < p := by
  simp [kgrid, Fintype.mem_piFinset]

/-- On a door, the labels of the other `n` vertices are exactly `1, …, n`. -/
theorem door_image {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) :
    ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))) = Finset.Icc 1 n := by
  apply Finset.eq_of_superset_of_card_ge
  · intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hc
    obtain ⟨j, hjk, hj⟩ := hd c h1 h2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, hj⟩
  · calc ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))).card
        ≤ (Finset.univ.erase k).card := Finset.card_image_le
      _ = n := by simp
      _ = (Finset.Icc 1 n).card := by simp

theorem door_label_pos {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) (j : Fin (n + 1)) (hj : j ≠ k) :
    1 ≤ ℓ (kvert v r j) := by
  have hmem : ℓ (kvert v r j) ∈
      ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, rfl⟩
  rw [door_image hd] at hmem
  exact (Finset.mem_Icc.mp hmem).1

theorem door_inj {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) (j₁ j₂ : Fin (n + 1)) (h₁ : j₁ ≠ k) (h₂ : j₂ ≠ k)
    (h : ℓ (kvert v r j₁) = ℓ (kvert v r j₂)) : j₁ = j₂ := by
  have hinj : Set.InjOn (fun j : Fin (n + 1) => ℓ (kvert v r j)) (Finset.univ.erase k : Finset _) := by
    rw [← Finset.card_image_iff, door_image hd]
    simp
  exact hinj (by simpa using h₁) (by simpa using h₂) h

/-! ## Counting doors -/

section Counting

open scoped Classical

/-- The Kuhn simplices of the grid `{0, …, p}^n`, as (base, rank permutation). -/
noncomputable def ksimp (n p : ℕ) : Finset ((Fin n → ℕ) × Equiv.Perm (Fin n)) :=
  kgrid n p ×ˢ Finset.univ

/-- Pairs (simplex, vertex index) whose opposite facet is a door. -/
noncomputable def kdoors (n p : ℕ) (ℓ : (Fin n → ℕ) → ℕ) :
    Finset (((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) :=
  (ksimp n p ×ˢ Finset.univ).filter (fun x => Door ℓ x.1.1 x.1.2 x.2)

/-- The completely labelled Kuhn simplices. -/
noncomputable def kfull (n p : ℕ) (ℓ : (Fin n → ℕ) → ℕ) :
    Finset ((Fin n → ℕ) × Equiv.Perm (Fin n)) :=
  (ksimp n p).filter (fun σ => FullyLabelled ℓ σ.1 σ.2)

/-- Door-to-door inside a simplex: move to the other vertex carrying the same label. -/
noncomputable def gA {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) :
    ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1) :=
  if h : ∃ j : Fin (n + 1), j ≠ x.2 ∧ ℓ (kvert x.1.1 x.1.2 j) = ℓ (kvert x.1.1 x.1.2 x.2) ∧
      ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0 then (x.1, h.choose) else x

theorem gA_of_zero {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1))
    (h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0) : gA ℓ x = x := by
  unfold gA
  rw [dif_neg]
  rintro ⟨j, -, -, h⟩
  exact h h0

theorem gA_spec {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1))
    (hx : Door ℓ x.1.1 x.1.2 x.2) (hne : ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0) :
    (gA ℓ x).1 = x.1 ∧ (gA ℓ x).2 ≠ x.2 ∧
      ℓ (kvert x.1.1 x.1.2 (gA ℓ x).2) = ℓ (kvert x.1.1 x.1.2 x.2) := by
  have hex : ∃ j : Fin (n + 1), j ≠ x.2 ∧ ℓ (kvert x.1.1 x.1.2 j) = ℓ (kvert x.1.1 x.1.2 x.2) ∧
      ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0 := by
    obtain ⟨j, hj, hj'⟩ := hx _ (Nat.one_le_iff_ne_zero.mpr hne) (hle _)
    exact ⟨j, hj, hj', hne⟩
  unfold gA
  rw [dif_pos hex]
  exact ⟨rfl, hex.choose_spec.1, hex.choose_spec.2.1⟩

theorem gA_mem {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ x ∈ kdoors n p ℓ := by
  by_cases h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0
  · rw [gA_of_zero ℓ x h0]; exact hx
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨e1, e2, e3⟩ := gA_spec ℓ hle x hd h0
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rw [e1]; exact (Finset.mem_product.mp hxs).1
  · rw [e1]
    intro c hc1 hc2
    obtain ⟨j, hjk, hj⟩ := hd c hc1 hc2
    by_cases hj2 : j = (gA ℓ x).2
    · refine ⟨x.2, fun h => e2 h.symm, ?_⟩
      rw [← e3, ← hj2]; exact hj
    · exact ⟨j, hj2, hj⟩

theorem gA_inv {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ (gA ℓ x) = x := by
  by_cases h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0
  · rw [gA_of_zero ℓ x h0, gA_of_zero ℓ x h0]
  obtain ⟨-, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨e1, e2, e3⟩ := gA_spec ℓ hle x hd h0
  have hy := gA_mem ℓ hle x hx
  obtain ⟨-, hdy⟩ := Finset.mem_filter.mp hy
  have h0y : ℓ (kvert (gA ℓ x).1.1 (gA ℓ x).1.2 (gA ℓ x).2) ≠ 0 := by
    rw [e1, e3]; exact h0
  obtain ⟨f1, f2, f3⟩ := gA_spec ℓ hle (gA ℓ x) hdy h0y
  rw [e1] at hdy f3
  have key : (gA ℓ (gA ℓ x)).2 = x.2 := by
    apply door_inj hdy _ _ f2 (fun h => e2 h.symm)
    rw [f3]; exact e3
  exact Prod.ext (by rw [f1, e1]) key

theorem gA_fixed_iff {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ x = x ↔ ℓ (kvert x.1.1 x.1.2 x.2) = 0 := by
  constructor
  · intro h
    by_contra h0
    obtain ⟨-, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, e2, -⟩ := gA_spec ℓ hle x hd h0
    exact e2 (by rw [h])
  · exact gA_of_zero ℓ x

/-- Step A: the number of doors has the parity of the number of completely labelled simplices. -/
theorem stepA {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n) :
    (((kdoors n p ℓ).card : ℕ) : ZMod 2) = ((kfull n p ℓ).card : ZMod 2) := by
  rw [card_zmod_two_eq_card_fixed (kdoors n p ℓ) (gA ℓ) (gA_mem ℓ hle) (gA_inv ℓ hle)]
  congr 1
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx1
    have h0 := (gA_fixed_iff ℓ hle x hx1).mp hx2
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hxs).1, ?_⟩
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · exact ⟨x.2, h0⟩
    · obtain ⟨j, -, hj⟩ := hd c hc0 hc
      exact ⟨j, hj⟩
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨-, hdx⟩ := Finset.mem_filter.mp hx1
    have h0y := (gA_fixed_iff ℓ hle y hy1).mp hy2
    refine Prod.ext hxy ?_
    by_contra hne
    have := door_label_pos hdx y.2 (fun h => hne h.symm)
    rw [hxy, h0y] at this
    exact absurd this (by norm_num)
  · intro σ hσ
    obtain ⟨hσs, hfl⟩ := Finset.mem_filter.mp hσ
    obtain ⟨k, hk⟩ := hfl 0 (Nat.zero_le _)
    have hmem : (σ, k) ∈ kdoors n p ℓ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hσs, Finset.mem_univ _⟩, ?_⟩
      intro c hc1 hc2
      obtain ⟨j, hj⟩ := hfl c hc2
      refine ⟨j, ?_, hj⟩
      rintro rfl
      omega
    exact ⟨(σ, k), Finset.mem_filter.mpr ⟨hmem, gA_of_zero ℓ _ hk⟩, rfl⟩

/-! ## Door-to-door across facets -/

theorem door_transfer {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v v' : Fin n → ℕ}
    {r r' : Equiv.Perm (Fin n)} {k k' : Fin (n + 1)} (φ : Fin (n + 1) → Fin (n + 1))
    (hφ : ∀ j, j ≠ k → φ j ≠ k' ∧ kvert v' r' (φ j) = kvert v r j) (hd : Door ℓ v r k) :
    Door ℓ v' r' k' := by
  intro c h1 h2
  obtain ⟨j, hj, hjc⟩ := hd c h1 h2
  obtain ⟨ha, hb⟩ := hφ j hj
  exact ⟨φ j, ha, by rw [hb]; exact hjc⟩

theorem finRotate_symm_zero (m : ℕ) : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]


theorem val_ne_zero_of_ne {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) : (a : ℕ) ≠ 0 :=
  fun h' => h (Fin.ext (by rw [h', Fin.val_zero]))

theorem val_ne_of_ne_last {n : ℕ} {a : Fin (n + 1)} (h : a ≠ Fin.last n) : (a : ℕ) ≠ n :=
  fun h' => h (Fin.ext (by rw [h', Fin.val_last]))

theorem last_ne_zero' (m : ℕ) : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

theorem kvert_move_zero {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j ≤ m) :
    kvert (Function.update v (r.symm 0) (v (r.symm 0) + 1)) (r.trans (finRotate (m + 1)).symm) j
      = kvert v r (j + 1) := by
  funext i
  unfold kvert
  by_cases hi : i = r.symm 0
  · subst hi
    simp only [Function.update_self, Equiv.trans_apply, Equiv.apply_symm_apply,
      finRotate_symm_zero, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · rw [Function.update_of_ne hi, Equiv.trans_apply]
    have hr : r i ≠ 0 := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    rw [coe_finRotate_symm_of_ne_zero hr]
    have : ((r i : Fin (m + 1)) : ℕ) ≠ 0 := val_ne_zero_of_ne hr
    split_ifs <;> omega

theorem kvert_move_last {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j ≤ m) (hv : 0 < v (r.symm (Fin.last m))) :
    kvert (Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1))
      (r.trans (finRotate (m + 1))) (j + 1) = kvert v r j := by
  funext i
  unfold kvert
  by_cases hi : i = r.symm (Fin.last m)
  · subst hi
    simp only [Function.update_self, Equiv.trans_apply, Equiv.apply_symm_apply,
      finRotate_last, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · rw [Function.update_of_ne hi, Equiv.trans_apply]
    have hr : r i ≠ Fin.last m := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    rw [coe_finRotate_of_ne_last hr]
    split_ifs <;> omega

theorem kvert_swap {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (m + 1)) (j : ℕ) (hj : j ≠ (k : ℕ)) :
    kvert v (r.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))) j = kvert v r j := by
  funext i
  unfold kvert
  rw [Equiv.trans_apply]
  have h1 : ((k.pred hk0 : Fin (m + 1)) : ℕ) = k - 1 := Fin.val_pred k hk0
  have h2 : ((k.castPred hkl : Fin (m + 1)) : ℕ) = k := Fin.coe_castPred k hkl
  have hkpos : (k : ℕ) ≠ 0 := val_ne_zero_of_ne hk0
  rcases eq_or_ne (r i) (k.pred hk0) with ha | ha
  · rw [ha, Equiv.swap_apply_left, h1, h2]
    split_ifs <;> omega
  · rcases eq_or_ne (r i) (k.castPred hkl) with hb | hb
    · rw [hb, Equiv.swap_apply_right, h1, h2]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Door-to-door across a facet of a Kuhn simplex (dimension `m + 1`). -/
noncomputable def gB {m : ℕ} (p : ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2)) :
    ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2) :=
  if hk0 : x.2 = 0 then
    (if x.1.1 (x.1.2.symm 0) + 1 < p then
      ((Function.update x.1.1 (x.1.2.symm 0) (x.1.1 (x.1.2.symm 0) + 1),
        x.1.2.trans (finRotate (m + 1)).symm), Fin.last (m + 1))
    else x)
  else if hkl : x.2 = Fin.last (m + 1) then
    (if 0 < x.1.1 (x.1.2.symm (Fin.last m)) then
      ((Function.update x.1.1 (x.1.2.symm (Fin.last m)) (x.1.1 (x.1.2.symm (Fin.last m)) - 1),
        x.1.2.trans (finRotate (m + 1))), 0)
    else x)
  else ((x.1.1, x.1.2.trans (Equiv.swap (x.2.pred hk0) (x.2.castPred hkl))), x.2)

theorem gB_zero_move {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : v (r.symm 0) + 1 < p) :
    gB p ((v, r), 0) = ((Function.update v (r.symm 0) (v (r.symm 0) + 1),
        r.trans (finRotate (m + 1)).symm), Fin.last (m + 1)) := by
  simp [gB, h]

theorem gB_zero_stay {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : ¬ v (r.symm 0) + 1 < p) : gB p ((v, r), 0) = ((v, r), 0) := by
  simp [gB, h]

theorem gB_last_move {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : 0 < v (r.symm (Fin.last m))) :
    gB p ((v, r), Fin.last (m + 1)) =
      ((Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1),
        r.trans (finRotate (m + 1))), 0) := by
  simp [gB, h, last_ne_zero' m]

theorem gB_last_stay {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : ¬ 0 < v (r.symm (Fin.last m))) :
    gB p ((v, r), Fin.last (m + 1)) = ((v, r), Fin.last (m + 1)) := by
  simp [gB, h, last_ne_zero' m]

theorem gB_mid {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (m + 1)) :
    gB p ((v, r), k) = ((v, r.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))), k) := by
  simp [gB, hk0, hkl]

theorem gB_mem {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) : gB p x ∈ kdoors (m + 1) p ℓ := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  simp only at hd
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
        intro i
        simp only [Function.update_apply]
        split_ifs with hi
        · exact h
        · exact hv i
      · refine door_transfer (fun j => ⟨(j : ℕ) - 1, by omega⟩) ?_ hd
        intro j hj
        have hj0 : (j : ℕ) ≠ 0 := val_ne_zero_of_ne hj
        have hjlt := j.isLt
        refine ⟨?_, ?_⟩
        · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
          omega
        · have := kvert_move_zero v r ((j : ℕ) - 1) (by omega)
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)] at this
          exact this
    · rw [gB_zero_stay v r h]; exact hx
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
            ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
          intro i
          simp only [Function.update_apply]
          split_ifs with hi
          · have := hv (r.symm (Fin.last m)); omega
          · exact hv i
        · refine door_transfer (fun j => ⟨min ((j : ℕ) + 1) (m + 1), by omega⟩) ?_ hd
          intro j hj
          have hjl : (j : ℕ) ≠ m + 1 := val_ne_of_ne_last hj
          have hjlt := j.isLt
          refine ⟨?_, ?_⟩
          · simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
            omega
          · have := kvert_move_last v r (j : ℕ) (by omega) h
            have e : min ((j : ℕ) + 1) (m + 1) = (j : ℕ) + 1 := by omega
            dsimp only
            rw [e]
            exact this
      · rw [gB_last_stay v r h]; exact hx
    · rw [gB_mid v r k hk0 hkl]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(mem_kgrid _).mpr hv, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · refine door_transfer id ?_ hd
        intro j hj
        exact ⟨hj, kvert_swap v r k hk0 hkl j (fun h => hj (Fin.ext h))⟩

theorem gB_inv {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) : gB p (gB p x) = x := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h]
      have e1 : (r.trans (finRotate (m + 1)).symm).symm (Fin.last m) = r.symm 0 := by
        rw [Equiv.symm_trans_apply, Equiv.symm_symm, finRotate_last]
      have h' : 0 < Function.update v (r.symm 0) (v (r.symm 0) + 1)
          ((r.trans (finRotate (m + 1)).symm).symm (Fin.last m)) := by
        rw [e1, Function.update_self]; omega
      rw [gB_last_move _ _ h']
      refine Prod.ext (Prod.ext ?_ ?_) rfl
      · simp only [e1, Function.update_self, Function.update_idem, Nat.add_sub_cancel,
          Function.update_eq_self]
      · exact Equiv.ext fun i => by simp
    · rw [gB_zero_stay v r h, gB_zero_stay v r h]
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h]
        have e1 : (r.trans (finRotate (m + 1))).symm 0 = r.symm (Fin.last m) := by
          rw [Equiv.symm_trans_apply, finRotate_symm_zero]
        have h' : Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1)
            ((r.trans (finRotate (m + 1))).symm 0) + 1 < p := by
          rw [e1, Function.update_self]; have := hv (r.symm (Fin.last m)); omega
        rw [gB_zero_move _ _ h']
        refine Prod.ext (Prod.ext ?_ ?_) rfl
        · simp only [e1, Function.update_self, Function.update_idem, Nat.sub_add_cancel h,
            Function.update_eq_self]
        · exact Equiv.ext fun i => by simp
      · rw [gB_last_stay v r h, gB_last_stay v r h]
    · rw [gB_mid v r k hk0 hkl, gB_mid v _ k hk0 hkl]
      refine Prod.ext (Prod.ext rfl ?_) rfl
      exact Equiv.ext fun i => by simp [Equiv.swap_apply_self]

theorem gB_fixed_facts {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (h0 : ∀ x (i : Fin (m + 1)), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin (m + 1)), x i = p → (i : ℕ) + 1 ≤ ℓ x)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) (hfix : gB p x = x) :
    x.2 = 0 ∧ x.1.1 0 = p - 1 ∧ x.1.2 0 = 0 := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  simp only at hd ⊢
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h] at hfix
      simp [Fin.ext_iff] at hfix
    · have hvp0 := hv (r.symm 0)
      have hvp : v (r.symm 0) = p - 1 := by omega
      obtain ⟨j, hj, hjl⟩ := hd 1 le_rfl (by omega)
      have hj0 : (j : ℕ) ≠ 0 := val_ne_zero_of_ne hj
      have hcoord : kvert v r j (r.symm 0) = p := by
        simp only [kvert, Equiv.apply_symm_apply, Fin.val_zero]
        rw [if_pos (by omega)]
        omega
      have hle := hP _ _ hcoord
      rw [hjl] at hle
      have hi0 : r.symm 0 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      refine ⟨rfl, ?_, ?_⟩
      · rw [← hi0]; exact hvp
      · exact ((Equiv.symm_apply_eq r).mp hi0).symm
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h] at hfix
        exact absurd (congrArg Prod.snd hfix).symm (last_ne_zero' m)
      · exfalso
        have hv0 : v (r.symm (Fin.last m)) = 0 := by omega
        have hilt := (r.symm (Fin.last m)).isLt
        obtain ⟨j, hj, hjl⟩ := hd ((r.symm (Fin.last m) : ℕ) + 1) (by omega) (by omega)
        have hjm : (j : ℕ) ≤ m := by
          have := j.isLt
          have : (j : ℕ) ≠ m + 1 := val_ne_of_ne_last hj
          omega
        have hcoord : kvert v r j (r.symm (Fin.last m)) = 0 := by
          simp only [kvert, Equiv.apply_symm_apply, Fin.val_last]
          rw [if_neg (by omega)]
          omega
        exact h0 _ _ hcoord hjl
    · rw [gB_mid v r k hk0 hkl] at hfix
      exfalso
      have h2 := congrArg (fun y => y.1.2 (r.symm (k.pred hk0))) hfix
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left] at h2
      have h3 := congrArg Fin.val h2
      rw [Fin.coe_castPred, Fin.val_pred] at h3
      have hkpos : (k : ℕ) ≠ 0 := val_ne_zero_of_ne hk0
      omega

theorem kvert_face {m : ℕ} (p : ℕ) (hp : 0 < p) (v : Fin m → ℕ) (r : Equiv.Perm (Fin m))
    (j : ℕ) :
    kvert (Fin.cons (p - 1) v : Fin (m + 1) → ℕ) (Equiv.Perm.decomposeFin.symm (0, r)) (j + 1)
      = (Fin.cons p (kvert v r j) : Fin (m + 1) → ℕ) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [kvert, Fin.cons_zero, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero]
    rw [if_pos (by omega)]
    omega
  | succ i =>
    simp only [kvert, Fin.cons_succ, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
      Equiv.refl_apply, Fin.val_succ]
    split_ifs <;> omega

theorem face_door_iff {m p : ℕ} (hp : 0 < p) (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (hP0 : ∀ y : Fin m → ℕ, 1 ≤ ℓ (Fin.cons p y)) (v : Fin m → ℕ) (r : Equiv.Perm (Fin m)) :
    Door ℓ (Fin.cons (p - 1) v) (Equiv.Perm.decomposeFin.symm (0, r)) 0 ↔
      FullyLabelled (fun y => ℓ (Fin.cons p y) - 1) v r := by
  constructor
  · intro hd c hc
    obtain ⟨j, hj, hjc⟩ := hd (c + 1) (by omega) (by omega)
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    refine ⟨j', ?_⟩
    rw [Fin.val_succ, kvert_face p hp] at hjc
    simp only
    omega
  · intro hfl c hc1 hc2
    obtain ⟨j', hj'⟩ := hfl (c - 1) (by omega)
    refine ⟨j'.succ, Fin.succ_ne_zero _, ?_⟩
    rw [Fin.val_succ, kvert_face p hp]
    have := hP0 (kvert v r j')
    simp only at hj'
    omega

theorem perm_decompose_of_zero {m : ℕ} (r : Equiv.Perm (Fin (m + 1))) (hr : r 0 = 0) :
    Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin r).2) = r := by
  obtain ⟨a, e, hae⟩ : ∃ a e, Equiv.Perm.decomposeFin r = (a, e) := ⟨_, _, rfl⟩
  have hr' : r = Equiv.Perm.decomposeFin.symm (a, e) := by rw [← hae, Equiv.symm_apply_apply]
  have ha : a = 0 := by
    have := Equiv.Perm.decomposeFin_symm_apply_zero a e
    rw [← hr', hr] at this
    exact this.symm
  rw [hae, ha, ← ha, ← hr']

theorem fixed_eq_face {m p : ℕ}
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (e0 : x.2 = 0) (ev : x.1.1 0 = p - 1) (er : x.1.2 0 = 0) :
    ((Fin.cons (p - 1) (Fin.tail x.1.1),
      Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin x.1.2).2)), 0) = x := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  simp only at e0 ev er ⊢
  rw [perm_decompose_of_zero r er, e0, ← ev, Fin.cons_self_tail]

/-- Step B: the number of doors has the parity of the number of completely labelled simplices
of the face `x₀ = p`, with the induced labelling. -/
theorem stepB {m p : ℕ} (hp : 0 < p) (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (h0 : ∀ x (i : Fin (m + 1)), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin (m + 1)), x i = p → (i : ℕ) + 1 ≤ ℓ x) :
    (((kdoors (m + 1) p ℓ).card : ℕ) : ZMod 2) =
      ((kfull m p (fun y => ℓ (Fin.cons p y) - 1)).card : ZMod 2) := by
  have hP0 : ∀ y : Fin m → ℕ, 1 ≤ ℓ (Fin.cons p y) := fun y => by
    simpa using hP (Fin.cons p y) 0 (by simp)
  rw [card_zmod_two_eq_card_fixed (kdoors (m + 1) p ℓ) (gB p) (gB_mem ℓ) (gB_inv ℓ)]
  congr 1
  apply Finset.card_nbij' (fun x => (Fin.tail x.1.1, (Equiv.Perm.decomposeFin x.1.2).2))
    (fun σ => ((Fin.cons (p - 1) σ.1, Equiv.Perm.decomposeFin.symm (0, σ.2)), 0))
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨e0, ev, er⟩ := gB_fixed_facts ℓ h0 hP x hx1 hx2
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx1
    have hv : ∀ i, x.1.1 i < p :=
      (mem_kgrid _).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
    have hd' : Door ℓ (Fin.cons (p - 1) (Fin.tail x.1.1))
        (Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin x.1.2).2)) 0 := by
      have h := fixed_eq_face x e0 ev er
      rw [← h] at hd
      exact hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_kgrid _).mpr (fun i => hv i.succ), Finset.mem_univ _⟩, ?_⟩
    exact (face_door_iff hp ℓ hP0 _ _).mp hd'
  · intro σ hσ
    rw [Finset.mem_coe] at hσ ⊢
    obtain ⟨hσs, hfl⟩ := Finset.mem_filter.mp hσ
    have hv : ∀ i, σ.1 i < p := (mem_kgrid _).mp (Finset.mem_product.mp hσs).1
    have hmem : ((Fin.cons (p - 1) σ.1, Equiv.Perm.decomposeFin.symm (0, σ.2)), 0)
        ∈ kdoors (m + 1) p ℓ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩,
        (face_door_iff hp ℓ hP0 _ _).mpr hfl⟩
      intro i
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; omega
      | succ i => simp only [Fin.cons_succ]; exact hv i
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    have hR : (Equiv.Perm.decomposeFin.symm (0, σ.2)).symm 0 = 0 := by
      rw [Equiv.symm_apply_eq, Equiv.Perm.decomposeFin_symm_apply_zero]
    apply gB_zero_stay
    rw [hR, Fin.cons_zero]
    omega
  · intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨e0, ev, er⟩ := gB_fixed_facts ℓ h0 hP x hx1 hx2
    exact fixed_eq_face x e0 ev er
  · intro σ _
    simp

/-- The number of completely labelled Kuhn simplices is odd (induction on the dimension). -/
theorem kfull_card_odd (n : ℕ) : ∀ (p : ℕ), 0 < p → ∀ (ℓ : (Fin n → ℕ) → ℕ), (∀ y, ℓ y ≤ n) →
    (∀ x (i : Fin n), x i = 0 → ℓ x ≠ (i : ℕ) + 1) →
    (∀ x (i : Fin n), x i = p → (i : ℕ) + 1 ≤ ℓ x) → Odd (kfull n p ℓ).card := by
  induction n with
  | zero =>
    intro p hp ℓ hle h0 hP
    have hfull : kfull 0 p ℓ = ksimp 0 p := by
      apply Finset.filter_true_of_mem
      intro σ _ c hc
      refine ⟨0, ?_⟩
      have := hle (kvert σ.1 σ.2 0)
      simp only [Fin.val_zero]
      omega
    rw [hfull]
    have hc : (ksimp 0 p).card = 1 := by
      simp [ksimp, kgrid]
    rw [hc]
    exact odd_one
  | succ m ih =>
    intro p hp ℓ hle h0 hP
    have hA := stepA (p := p) ℓ hle
    have hB := stepB hp ℓ h0 hP
    have hodd := ih p hp (fun y => ℓ (Fin.cons p y) - 1)
      (fun y => by
        show ℓ (Fin.cons p y) - 1 ≤ m
        have := hle (Fin.cons p y)
        omega)
      (fun y i hy => by
        show ℓ (Fin.cons p y) - 1 ≠ (i : ℕ) + 1
        have h1 := h0 (Fin.cons p y) i.succ (by simpa using hy)
        have h2 := hP (Fin.cons p y) 0 (by simp)
        simp only [Fin.val_succ, Fin.val_zero] at h1 h2
        omega)
      (fun y i hy => by
        show (i : ℕ) + 1 ≤ ℓ (Fin.cons p y) - 1
        have h1 := hP (Fin.cons p y) i.succ (by simpa using hy)
        simp only [Fin.val_succ] at h1
        omega)
    rw [← ZMod.natCast_eq_one_iff_odd] at hodd ⊢
    rw [← hA, hB, hodd]

end Counting

/-- **Sperner's lemma** on Kuhn's triangulation of the cube `[0, p]^n`.

Label the lattice points `x : Fin n → ℕ` by `ℓ x ∈ {0, …, n}` such that a point with `x i = 0`
never carries label `i + 1`, and a point with `x i = p` carries a label `≥ i + 1`. Then some
Kuhn simplex (base `v` with `v i < p`, vertices `kvert v r j`, `j = 0, …, n`) is completely
labelled. (In fact their number is odd: `kfull_card_odd`.) -/
theorem sperner_kuhn (n p : ℕ) (hp : 0 < p) (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (h0 : ∀ x (i : Fin n), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin n), x i = p → (i : ℕ) + 1 ≤ ℓ x) :
    ∃ (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)), (∀ i, v i < p) ∧ FullyLabelled ℓ v r := by
  classical
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp (kfull_card_odd n p hp ℓ hle h0 hP).pos
  obtain ⟨hs, hfl⟩ := Finset.mem_filter.mp hσ
  exact ⟨σ.1, σ.2, (mem_kgrid _).mp (Finset.mem_product.mp hs).1, hfl⟩

/-! ## Brouwer's fixed point theorem on the unit cube -/

section BrouwerCube

open Filter Topology

theorem mem_cube_iff {N : ℕ} (x : Fin N → ℝ) :
    x ∈ Set.Icc (0 : Fin N → ℝ) 1 ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The point of the unit cube represented by the lattice point `x` of `{0, …, p}^N`
(coordinates clamped at `p`). -/
noncomputable def cubePt {N : ℕ} (p : ℕ) (x : Fin N → ℕ) : Fin N → ℝ :=
  fun i => ((min (x i) p : ℕ) : ℝ) / p

theorem cubePt_mem {N p : ℕ} (hp : 0 < p) (x : Fin N → ℕ) :
    cubePt p x ∈ Set.Icc (0 : Fin N → ℝ) 1 := by
  rw [mem_cube_iff]
  intro i
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨by unfold cubePt; positivity, ?_⟩
  unfold cubePt
  rw [div_le_one hp']
  exact_mod_cast min_le_right _ _

open scoped Classical in
/-- Kuhn's labelling for a self-map `f` of the cube: `0` if no coordinate is pushed down,
otherwise `1 +` the largest coordinate `i` with `x i ≠ 0` and `f x i ≤ x i`. -/
noncomputable def cubeLabel {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ) :
    ℕ :=
  (Finset.univ.filter (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i)).sup
    (fun i => (i : ℕ) + 1)

theorem cubeLabel_le {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ) :
    cubeLabel f p x ≤ N := by
  unfold cubeLabel
  apply Finset.sup_le
  intro i _
  exact i.isLt

theorem cubeLabel_mem {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ)
    (i : Fin N) (h : cubeLabel f p x = (i : ℕ) + 1) :
    cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i := by
  classical
  unfold cubeLabel at h
  set s := Finset.univ.filter
    (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) with hs
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty] at h
    exact absurd h (by simp)
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup s hne (fun i : Fin N => (i : ℕ) + 1)
    rw [hjeq] at h
    have hji : j = i := Fin.ext (by have h' : (j : ℕ) + 1 = (i : ℕ) + 1 := h; omega)
    subst hji
    exact (Finset.mem_filter.mp hj).2

theorem cubeLabel_zero {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (p : ℕ) (hp : 0 < p) (x : Fin N → ℕ)
    (h : cubeLabel f p x = 0) (i : Fin N) : cubePt p x i ≤ f (cubePt p x) i := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hfx := (mem_cube_iff _).mp (hmap (cubePt_mem hp x)) i
  have hmem : i ∈ Finset.univ.filter
      (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hlt.le⟩
    intro h0
    rw [h0] at hlt
    linarith [hfx.1]
  have := Finset.le_sup (f := fun i : Fin N => (i : ℕ) + 1) hmem
  unfold cubeLabel at h
  omega

theorem cubeLabel_h0 {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ)
    (i : Fin N) (hx : x i = 0) : cubeLabel f p x ≠ (i : ℕ) + 1 := by
  intro h
  have := (cubeLabel_mem f p x i h).1
  apply this
  simp [cubePt, hx]

theorem cubeLabel_hP {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (p : ℕ) (hp : 0 < p) (x : Fin N → ℕ)
    (i : Fin N) (hx : x i = p) : (i : ℕ) + 1 ≤ cubeLabel f p x := by
  classical
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hpt : cubePt p x i = 1 := by
    simp only [cubePt, hx, min_self]
    exact div_self hp'.ne'
  have hfx := (mem_cube_iff _).mp (hmap (cubePt_mem hp x)) i
  have hmem : i ∈ Finset.univ.filter
      (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hpt]; exact one_ne_zero
    · rw [hpt]; exact hfx.2
  have := Finset.le_sup (f := fun i : Fin N => (i : ℕ) + 1) hmem
  unfold cubeLabel
  exact this

theorem dist_cubePt_kvert_le {N p : ℕ} (hp : 0 < p) (v : Fin N → ℕ) (hv : ∀ i, v i < p)
    (r : Equiv.Perm (Fin N)) (j : ℕ) :
    dist (cubePt p (kvert v r j)) (cubePt p v) ≤ 1 / (p : ℝ) := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have h1 : min (kvert v r j i) p = kvert v r j i :=
    min_eq_left (by unfold kvert; have := hv i; split_ifs <;> omega)
  have h2 : min (v i) p = v i := min_eq_left (hv i).le
  simp only [cubePt, h1, h2, Real.dist_eq]
  unfold kvert
  split_ifs
  · push_cast
    rw [show ((v i : ℝ) + 1) / p - v i / p = 1 / p by ring, abs_of_pos (by positivity)]
  · simp only [add_zero, sub_self, abs_zero]
    positivity

/-- Approximate fixed points from Sperner's lemma: at mesh `1 / (k + 1)` there is a base point
`b`, a nearby point `a` pushed up in every coordinate, and for each coordinate `i` a nearby
point `c i` pushed down in coordinate `i`. -/
theorem cube_approx {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (k : ℕ) :
    ∃ (b a : Fin N → ℝ) (c : Fin N → Fin N → ℝ),
      b ∈ Set.Icc (0 : Fin N → ℝ) 1 ∧ a ∈ Set.Icc (0 : Fin N → ℝ) 1 ∧
      (∀ i, c i ∈ Set.Icc (0 : Fin N → ℝ) 1) ∧
      dist a b ≤ 1 / ((k : ℝ) + 1) ∧ (∀ i, dist (c i) b ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ i, a i ≤ f a i) ∧ (∀ i, f (c i) i ≤ c i i) := by
  have hp : 0 < k + 1 := Nat.succ_pos k
  obtain ⟨v, r, hv, hfl⟩ := sperner_kuhn N (k + 1) hp (cubeLabel f (k + 1))
    (cubeLabel_le f (k + 1)) (fun x i hx => cubeLabel_h0 f (k + 1) x i hx)
    (fun x i hx => cubeLabel_hP f hmap (k + 1) hp x i hx)
  obtain ⟨j0, hj0⟩ := hfl 0 (Nat.zero_le _)
  have hJ : ∀ i : Fin N, ∃ j : Fin (N + 1), cubeLabel f (k + 1) (kvert v r j) = (i : ℕ) + 1 :=
    fun i => hfl _ (by omega)
  choose J hJ using hJ
  have hk : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  refine ⟨cubePt (k + 1) v, cubePt (k + 1) (kvert v r j0),
    fun i => cubePt (k + 1) (kvert v r (J i)),
    cubePt_mem hp v, cubePt_mem hp _, fun i => cubePt_mem hp _, ?_, ?_, ?_, ?_⟩
  · rw [← hk]; exact dist_cubePt_kvert_le hp v hv r _
  · intro i; rw [← hk]; exact dist_cubePt_kvert_le hp v hv r _
  · exact cubeLabel_zero f hmap (k + 1) hp _ hj0
  · intro i
    exact (cubeLabel_mem f (k + 1) _ i (hJ i)).2

/-- **Brouwer's fixed point theorem** on the unit cube `[0, 1]^N`, for `f` continuous on the
cube and mapping it into itself. -/
theorem brouwer_cube_Icc {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hf : ContinuousOn f (Set.Icc 0 1)) (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : Fin N → ℝ) 1, f x = x := by
  choose b a c hb ha hc hab hcb ha' hc' using cube_approx f hmap
  obtain ⟨x, hx, φ, hφ, hlim⟩ :=
    (isCompact_Icc (a := (0 : Fin N → ℝ)) (b := 1)).tendsto_subseq hb
  refine ⟨x, hx, ?_⟩
  have hε : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlimA : Tendsto (fun k => a (φ k)) atTop (𝓝 x) := by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hε
    rw [dist_comm]
    exact hab (φ k)
  have hlimC : ∀ i, Tendsto (fun k => c (φ k) i) atTop (𝓝 x) := fun i => by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hε
    rw [dist_comm]
    exact hcb (φ k) i
  have hfx : ∀ u : ℕ → Fin N → ℝ, (∀ k, u k ∈ Set.Icc (0 : Fin N → ℝ) 1) →
      Tendsto u atTop (𝓝 x) → Tendsto (fun k => f (u k)) atTop (𝓝 (f x)) := fun u hu hlu =>
    (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlu, Filter.Eventually.of_forall hu⟩)
  funext i
  apply le_antisymm
  · have h1 := ((continuous_apply i).tendsto (f x)).comp
      (hfx (fun k => c (φ k) i) (fun k => hc (φ k) i) (hlimC i))
    have h2 := ((continuous_apply i).tendsto x).comp (hlimC i)
    exact le_of_tendsto_of_tendsto' h1 h2 (fun k => hc' (φ k) i)
  · have h1 := ((continuous_apply i).tendsto (f x)).comp
      (hfx (fun k => a (φ k)) (fun k => ha (φ k)) hlimA)
    have h2 := ((continuous_apply i).tendsto x).comp hlimA
    exact le_of_tendsto_of_tendsto' h2 h1 (fun k => ha' (φ k) i)

/-- **Brouwer's fixed point theorem** on the unit cube, coordinate form, for `f` continuous on
the cube. -/
theorem brouwer_cube_continuousOn (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hf : ContinuousOn f {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1})
    (hmap : ∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) :
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x := by
  have hset : {x : Fin N → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} = Set.Icc 0 1 :=
    Set.ext fun x => (mem_cube_iff x).symm
  rw [hset] at hf
  obtain ⟨x, hx, hfx⟩ := brouwer_cube_Icc f hf
    (fun x hx => (mem_cube_iff _).mpr (hmap x ((mem_cube_iff x).mp hx)))
  exact ⟨x, (mem_cube_iff x).mp hx, hfx⟩

/-- **Brouwer's fixed point theorem** on the unit cube: a continuous `f : ℝ^N → ℝ^N` mapping
the cube `{x | ∀ i, 0 ≤ x i ≤ 1}` into itself has a fixed point in the cube. -/
theorem brouwer_cube (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ)) (hf : Continuous f)
    (hmap : ∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) :
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x :=
  brouwer_cube_continuousOn N f hf.continuousOn hmap

end BrouwerCube

end BrouwerLib


namespace FPCP

open SocialEquilibrium.Existence Set Metric unitInterval

/-! ## Part 0: contractibility transfer and the fixed-point property -/

theorem isContractible_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (e : A ≃ₜ B) (hA : IsContractible A) : IsContractible B := by
  obtain ⟨z₀, H, h0, h1⟩ := hA
  exact ⟨e z₀, (e : C(A, B)).comp (H.comp ((ContinuousMap.id I).prodMap (e.symm : C(B, A)))),
    fun z => by simp [h0], fun z => by simp [h1]⟩

/-- The fixed-point property for closed-graph, contractible-valued correspondences. -/
def EMProp (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ φ : X → Set X, IsSemicontinuous φ → (∀ x, IsContractible (φ x)) → ∃ x, x ∈ φ x

theorem EMProp.of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (hY : EMProp Y) : EMProp X := by
  intro φ hφ hc
  have hG : IsSemicontinuous (fun y => h '' φ (h.symm y)) := by
    have : graph (fun y => h '' φ (h.symm y)) =
        (fun p : Y × Y => (h.symm p.1, h.symm p.2)) ⁻¹' graph φ := by
      ext p
      simp only [graph, mem_setOf_eq, mem_preimage]
      constructor
      · rintro ⟨x, hx, hxp⟩
        rw [← hxp]; simpa using hx
      · intro hp
        exact ⟨h.symm p.2, hp, by simp⟩
    unfold IsSemicontinuous
    rw [this]
    exact hφ.preimage (by fun_prop)
  have hC : ∀ y, IsContractible (h '' φ (h.symm y)) := fun y =>
    isContractible_of_homeomorph (h.image (φ (h.symm y))) (hc _)
  obtain ⟨y, hy⟩ := hY (fun y => h '' φ (h.symm y)) hG hC
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, by simpa using hx⟩

/-! ## Part 1: neighbourhood-null-homotopic sets -/

/-- Small neighbourhoods of `A` are null-homotopic inside a given neighbourhood. -/
def NullNbhd {Y : Type*} [PseudoMetricSpace Y] (A : Set Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ G : C(I × Y, Y), (∀ y, G (0, y) = y) ∧ (∃ c, ∀ y, G (1, y) = c) ∧
    ∀ t y, y ∈ thickening δ A → G (t, y) ∈ thickening ε A

theorem nullNbhd_of_contractible {m : ℕ} (A : Set (Fin m → ℝ)) (hA : IsCompact A)
    (hc : IsContractible A) : NullNbhd A := by
  classical
  obtain ⟨z₀, H, h0, h1⟩ := hc
  intro ε hε
  have h10 : (1 : I) ≠ 0 := fun h => by simpa using congrArg Subtype.val h
  set F : Set (I × (Fin m → ℝ)) := ({0} ×ˢ univ) ∪ (univ ×ˢ A) ∪ ({1} ×ˢ univ) with hFdef
  have hF : IsClosed F :=
    ((isClosed_singleton.prod isClosed_univ).union (isClosed_univ.prod hA.isClosed)).union
      (isClosed_singleton.prod isClosed_univ)
  let G0 : I × (Fin m → ℝ) → (Fin m → ℝ) := fun p =>
    if p.1 = 0 then p.2 else if p.1 = 1 then (z₀ : Fin m → ℝ) else
      if h : p.2 ∈ A then ((H (p.1, ⟨p.2, h⟩) : A) : Fin m → ℝ) else 0
  have hGA : ∀ t (a : A), G0 (t, a) = ((H (t, a) : A) : Fin m → ℝ) := by
    intro t a
    by_cases ht0 : t = 0
    · subst ht0; simp [G0, h0]
    · by_cases ht1 : t = 1
      · subst ht1; simp [G0, h1]
      · simp [G0, ht0, ht1]
  have hG0 : ContinuousOn G0 F := by
    refine ContinuousOn.union_of_isClosed (ContinuousOn.union_of_isClosed ?_ ?_ ?_ ?_) ?_ ?_ ?_
    · refine continuous_snd.continuousOn.congr fun p hp => ?_
      obtain ⟨hp1, -⟩ := hp
      simp only [mem_singleton_iff] at hp1
      simp [G0, hp1]
    · rw [continuousOn_iff_continuous_restrict]
      have hc : Continuous (fun p : ↥(univ ×ˢ A) =>
          ((H (p.1.1, ⟨p.1.2, p.2.2⟩) : A) : Fin m → ℝ)) := by
        fun_prop
      refine hc.congr fun p => ?_
      obtain ⟨⟨t, y⟩, -, hy⟩ := p
      simp only [restrict_apply]
      exact (hGA t ⟨y, hy⟩).symm
    · exact isClosed_singleton.prod isClosed_univ
    · exact isClosed_univ.prod hA.isClosed
    · refine (continuousOn_const (c := (z₀ : Fin m → ℝ))).congr fun p hp => ?_
      obtain ⟨hp1, -⟩ := hp
      simp only [mem_singleton_iff] at hp1
      show G0 p = (z₀ : Fin m → ℝ)
      simp [G0, hp1, h10]
    · exact (isClosed_singleton.prod isClosed_univ).union (isClosed_univ.prod hA.isClosed)
    · exact isClosed_singleton.prod isClosed_univ
  let f : C(F, Fin m → ℝ) := ⟨F.restrict G0, continuousOn_iff_continuous_restrict.1 hG0⟩
  obtain ⟨G, hG⟩ := f.exists_restrict_eq hF
  have hGF : ∀ p (hp : p ∈ F), G p = G0 p := fun p hp => DFunLike.congr_fun hG ⟨p, hp⟩
  have hGt : ∀ t (a : A), G (t, a) ∈ A := by
    intro t a
    rw [hGF _ (Or.inl (Or.inr ⟨mem_univ _, a.2⟩)), hGA]
    exact (H _).2
  have hO : (univ : Set I) ×ˢ A ⊆ G ⁻¹' thickening ε A := by
    rintro ⟨t, a⟩ ⟨-, ha⟩
    exact self_subset_thickening hε _ (hGt t ⟨a, ha⟩)
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_univ.prod hA).exists_thickening_subset_open
    (isOpen_thickening.preimage G.continuous) hO
  refine ⟨δ, hδ, G, fun y => ?_, ⟨z₀, fun y => ?_⟩, fun t y hy => ?_⟩
  · rw [hGF _ (Or.inl (Or.inl ⟨mem_singleton _, mem_univ _⟩))]
    simp [G0]
  · rw [hGF _ (Or.inr ⟨mem_singleton _, mem_univ _⟩)]
    simp [G0, h10]
  · obtain ⟨a, ha, hya⟩ := mem_thickening_iff.1 hy
    refine hδO (mem_thickening_iff.2 ⟨(t, a), ⟨mem_univ _, ha⟩, ?_⟩)
    rw [Prod.dist_eq, dist_self]
    simpa using hya

theorem usc_of_closed_graph {X Y : Type*} [MetricSpace X] [MetricSpace Y] (K : Set X) (L : Set Y)
    (hK : IsCompact K) (hL : IsCompact L) (Ψ : X → Set Y)
    (hΓ : IsClosed {p : X × Y | p.1 ∈ K ∧ p.2 ∈ Ψ p.1}) (hsub : ∀ x ∈ K, Ψ x ⊆ L) :
    ∀ x ∈ K, ∀ η > 0, ∃ ρ > 0, ∀ x' ∈ K, dist x' x < ρ → Ψ x' ⊆ thickening η (Ψ x) := by
  intro x hx η hη
  set Γ := {p : X × Y | p.1 ∈ K ∧ p.2 ∈ Ψ p.1} with hΓdef
  have hΓc : IsCompact Γ :=
    (hK.prod hL).of_isClosed_subset hΓ (fun p hp => ⟨hp.1, hsub _ hp.1 hp.2⟩)
  set C := Γ ∩ (univ ×ˢ (thickening η (Ψ x))ᶜ) with hCdef
  have hCc : IsCompact C :=
    hΓc.inter_right (isClosed_univ.prod isOpen_thickening.isClosed_compl)
  have hP : IsClosed (Prod.fst '' C) := (hCc.image continuous_fst).isClosed
  have hxP : x ∉ Prod.fst '' C := by
    rintro ⟨p, ⟨⟨-, hy⟩, -, hy'⟩, hpx⟩
    rw [hpx] at hy
    exact hy' (self_subset_thickening hη _ hy)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hP.isOpen_compl x hxP
  refine ⟨ρ, hρ, fun x' hx' hd y hy => ?_⟩
  by_contra hyn
  exact hball (mem_ball.2 hd) ⟨(x', y), ⟨⟨hx', hy⟩, mem_univ _, hyn⟩, rfl⟩

/-! ## Part 2: extension over the skeleta of a simplex -/

section SXwrap
open Filter Topology
/-- Support of a weight vector. -/
noncomputable def supp {J : Type*} [Fintype J] (l : J → ℝ) : Finset J := by
  classical exact Finset.univ.filter (fun j => l j ≠ 0)

theorem mem_supp {J : Type*} [Fintype J] (l : J → ℝ) (j : J) : j ∈ supp l ↔ l j ≠ 0 := by
  classical
  simp [supp]

section SX

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Closed face of the standard simplex spanned by `S`. -/
def face (S : Finset J) : Set (J → ℝ) := stdSimplex ℝ J ∩ {l | ∀ j, j ∉ S → l j = 0}

/-- Points of the simplex whose support has at most `k` elements. -/
def lev (k : ℕ) : Set (J → ℝ) := {l | l ∈ stdSimplex ℝ J ∧ (supp l).card ≤ k}

theorem isClosed_face (S : Finset J) : IsClosed (face S) :=
  by
    have : {l : J → ℝ | ∀ j, j ∉ S → l j = 0} = ⋂ j, ⋂ (_ : j ∉ S), {l | l j = 0} := by
      ext l; simp
    unfold face
    rw [this]
    exact (isClosed_stdSimplex ℝ J).inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply j) continuous_const)

theorem mem_face_iff (S : Finset J) (l : J → ℝ) :
    l ∈ face S ↔ l ∈ stdSimplex ℝ J ∧ supp l ⊆ S := by
  simp only [face, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨h, h0⟩
    refine ⟨h, fun j hj => ?_⟩
    by_contra hjS
    exact (mem_supp l j).1 hj (h0 j hjS)
  · rintro ⟨h, hs⟩
    refine ⟨h, fun j hjS => ?_⟩
    by_contra hj
    exact hjS (hs ((mem_supp l j).2 hj))

theorem lev_eq (k : ℕ) : lev k = ⋃ S : {S : Finset J // S.card ≤ k}, face (S : Finset J) := by
  ext l
  simp only [lev, mem_setOf_eq, mem_iUnion, mem_face_iff, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨h, hk⟩
    exact ⟨supp l, hk, h, subset_rfl⟩
  · rintro ⟨S, hS, h, hsub⟩
    exact ⟨h, (Finset.card_le_card hsub).trans hS⟩

theorem isClosed_lev (k : ℕ) : IsClosed (lev (J := J) k) := by
  rw [lev_eq]
  exact isClosed_iUnion_of_finite fun S => isClosed_face _

theorem isCompact_lev (k : ℕ) : IsCompact (lev (J := J) k) :=
  (isCompact_stdSimplex ℝ J).of_isClosed_subset (isClosed_lev k) (fun _ hl => hl.1)

theorem supp_nonempty {l : J → ℝ} (hl : l ∈ stdSimplex ℝ J) : (supp l).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have h0 : ∀ j, l j = 0 := fun j => by
    by_contra hj
    have := (mem_supp l j).2 hj
    rw [h] at this
    simp at this
  have := hl.2
  simp [h0] at this

theorem continuousOn_lev {Y : Type*} [TopologicalSpace Y] (g : (J → ℝ) → Y) (k : ℕ)
    (h : ∀ S : Finset J, S.card ≤ k → ContinuousOn g (face S)) : ContinuousOn g (lev k) := by
  rw [lev_eq]
  exact (locallyFinite_of_finite _).continuousOn_iUnion (fun S => isClosed_face _)
    (fun S => h S.1 S.2)

/-- Minimum of the coordinates in `S`. -/
noncomputable def mn (S : Finset J) (l : J → ℝ) : ℝ := if h : S.Nonempty then S.inf' h l else 0

/-- Radial parameter: `0` at the barycentre of the face, `1` on its boundary. -/
noncomputable def sr (S : Finset J) (l : J → ℝ) : ℝ := 1 - S.card * mn S l

/-- Radial projection to the boundary of the face. -/
noncomputable def mu (S : Finset J) (l : J → ℝ) : J → ℝ :=
  fun j => if j ∈ S then (l j - mn S l) / sr S l else 0

/-- Homotopy time. -/
noncomputable def tau (S : Finset J) (l : J → ℝ) : I := projIcc 0 1 zero_le_one (1 - sr S l)

theorem continuous_mn (S : Finset J) : Continuous (mn S) := by
  by_cases h : S.Nonempty
  · have : mn S = fun l => S.inf' h (fun i => l i) := by
      funext l; simp [mn, h]
    rw [this]
    exact continuous_iff_continuousAt.2 fun x =>
      ContinuousAt.finset_inf'_apply h (fun i _ => (continuous_apply i).continuousAt)
  · have : mn S = fun _ => 0 := by funext l; simp [mn, h]
    rw [this]; exact continuous_const

theorem continuous_sr (S : Finset J) : Continuous (sr S) :=
  continuous_const.sub (continuous_const.mul (continuous_mn S))

theorem continuous_tau (S : Finset J) : Continuous (tau S) :=
  continuous_projIcc.comp (continuous_const.sub (continuous_sr S))

theorem sum_face {S : Finset J} {l : J → ℝ} (hl : l ∈ face S) : ∑ j ∈ S, l j = 1 := by
  have h1 := hl.1.2
  rw [← h1]
  refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hl.2 j hj

theorem mn_nonneg {S : Finset J} {l : J → ℝ} (hl : l ∈ face S) : 0 ≤ mn S l := by
  unfold mn
  split_ifs with h
  · exact Finset.le_inf' h _ fun j _ => hl.1.1 j
  · exact le_rfl

theorem mn_le {S : Finset J} {l : J → ℝ} {j : J} (hj : j ∈ S) : mn S l ≤ l j := by
  unfold mn
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

theorem card_mul_mn_le {S : Finset J} {l : J → ℝ} (hl : l ∈ face S) : S.card * mn S l ≤ 1 := by
  rw [← sum_face hl]
  have : ∑ _j ∈ S, mn S l ≤ ∑ j ∈ S, l j := Finset.sum_le_sum fun j hj => mn_le hj
  simpa using this

theorem sr_nonneg {S : Finset J} {l : J → ℝ} (hl : l ∈ face S) : 0 ≤ sr S l := by
  unfold sr; linarith [card_mul_mn_le hl]

theorem sr_le_one {S : Finset J} {l : J → ℝ} (hl : l ∈ face S) : sr S l ≤ 1 := by
  unfold sr
  have := mn_nonneg hl
  have : (0 : ℝ) ≤ S.card * mn S l := mul_nonneg (Nat.cast_nonneg _) this
  linarith

/-- On a proper sub-face the radial data is trivial. -/
theorem mn_eq_zero_of_ssubset {S : Finset J} {l : J → ℝ} (hl : l ∈ face S)
    (hs : supp l ⊂ S) : mn S l = 0 := by
  obtain ⟨j, hjS, hj⟩ := Finset.exists_of_ssubset hs
  have hl0 : l j = 0 := by
    by_contra h
    exact hj ((mem_supp l j).2 h)
  exact le_antisymm (hl0 ▸ mn_le hjS) (mn_nonneg hl)

theorem mu_eq_self_of_ssubset {S : Finset J} {l : J → ℝ} (hl : l ∈ face S)
    (hs : supp l ⊂ S) : mu S l = l := by
  have hm := mn_eq_zero_of_ssubset hl hs
  have hsr : sr S l = 1 := by simp [sr, hm]
  funext j
  simp only [mu, hm, hsr, sub_zero, div_one]
  split_ifs with hj
  · rfl
  · exact (hl.2 j hj).symm

theorem tau_eq_zero_of_ssubset {S : Finset J} {l : J → ℝ} (hl : l ∈ face S)
    (hs : supp l ⊂ S) : tau S l = 0 := by
  have hm := mn_eq_zero_of_ssubset hl hs
  have hsr : sr S l = 1 := by simp [sr, hm]
  simp only [tau, hsr, sub_self]
  exact projIcc_left _

theorem tau_eq_one_of_sr_eq_zero {S : Finset J} {l : J → ℝ} (h : sr S l = 0) : tau S l = 1 := by
  simp only [tau, h, sub_zero]
  exact projIcc_right _

/-- For `sr > 0`, the radial projection lands in a proper sub-face. -/
theorem mu_mem {S : Finset J} {l : J → ℝ} (hl : l ∈ face S) (hs : 0 < sr S l) :
    mu S l ∈ face S ∧ supp (mu S l) ⊂ S := by
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := sum_face hl
    simp [h] at this
  have hmf : mu S l ∈ face S := by
    refine ⟨⟨fun j => ?_, ?_⟩, fun j hj => ?_⟩
    · simp only [mu]
      split_ifs with hj
      · exact div_nonneg (sub_nonneg.2 (mn_le hj)) hs.le
      · exact le_rfl
    · have : ∑ j, mu S l j = ∑ j ∈ S, (l j - mn S l) / sr S l := by
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        · exact Finset.sum_congr rfl fun j hj => by simp [mu, hj]
        · intro j _ hj; simp [mu, hj]
      rw [this, ← Finset.sum_div, Finset.sum_sub_distrib, sum_face hl]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [div_eq_one_iff_eq hs.ne']
      rfl
    · simp [mu, hj]
  refine ⟨hmf, ?_⟩
  refine Finset.ssubset_iff_subset_ne.2 ⟨((mem_face_iff _ _).1 hmf).2, fun heq => ?_⟩
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hSne l
  have hmj : mu S l j = 0 := by
    simp only [mu, hj, if_true]
    have : mn S l = l j := by simp [mn, hSne, hjeq]
    rw [this, sub_self, zero_div]
  have : j ∈ supp (mu S l) := by rw [heq]; exact hj
  exact (mem_supp _ _).1 this hmj

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y]

/-- The skeleton-by-skeleton extension: `gseq n` is defined on supports of size `≤ n + 1`. -/
noncomputable def gseq (v : J → Y) (Gm : Finset J → C(I × Y, Y)) : ℕ → (J → ℝ) → Y
  | 0 => fun l => if h : (supp l).Nonempty then v h.choose else Classical.arbitrary Y
  | n + 1 => fun l => if (supp l).card ≤ n + 1 then gseq v Gm n l else
      Gm (supp l) (tau (supp l) l, gseq v Gm n (mu (supp l) l))

theorem supp_eq_singleton {l : J → ℝ} (hl : l ∈ stdSimplex ℝ J) (h1 : (supp l).card ≤ 1) :
    supp l = {(supp_nonempty hl).choose} := by
  have hne := supp_nonempty hl
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hne.choose_spec, fun j hj => ?_⟩
  exact Finset.card_le_one.1 h1 _ hj _ hne.choose_spec

theorem gseq_spec (U U' : Finset J → Set Y) (v : J → Y) (hv : ∀ j, v j ∈ U {j})
    (Gm : Finset J → C(I × Y, Y)) (hG0 : ∀ S y, 2 ≤ S.card → Gm S (0, y) = y)
    (hG1 : ∀ S, 2 ≤ S.card → ∃ c, ∀ y, Gm S (1, y) = c)
    (hGU : ∀ S, 2 ≤ S.card → ∀ t y, y ∈ U' S → Gm S (t, y) ∈ U S)
    (h2 : ∀ S T : Finset J, T ⊂ S → T.Nonempty → U T ⊆ U' S) :
    ∀ n, ContinuousOn (gseq v Gm n) (lev (n + 1)) ∧
      ∀ l ∈ lev (n + 1), gseq v Gm n l ∈ U (supp l) := by
  intro n
  induction n with
  | zero =>
    refine ⟨continuousOn_lev _ _ fun S hS => ?_, fun l hl => ?_⟩
    · rcases S.eq_empty_or_nonempty with hS0 | ⟨j, hjS⟩
      · intro l hl
        have hl' := (mem_face_iff _ _).1 hl
        obtain ⟨i, hi⟩ := supp_nonempty hl'.1
        have := hl'.2 hi
        rw [hS0] at this
        simp at this
      have hj : S ⊆ {j} := fun i hi => Finset.mem_singleton.2 (Finset.card_le_one.1 hS i hi j hjS)
      refine (continuousOn_const (c := v j)).congr fun l hl => ?_
      have hl' := (mem_face_iff _ _).1 hl
      have hs := supp_eq_singleton hl'.1 ((Finset.card_le_card (hl'.2.trans hj)).trans
        (by simp))
      have hne := supp_nonempty hl'.1
      have hc : hne.choose = j := by
        have := hl'.2.trans hj (hne.choose_spec)
        simpa using this
      simp only [gseq, dif_pos hne, hc]
    · have hne := supp_nonempty hl.1
      rw [supp_eq_singleton hl.1 hl.2]
      simp only [gseq, dif_pos hne]
      exact hv _
  | succ n ih =>
    obtain ⟨ihc, ihU⟩ := ih
    -- behaviour on a top face
    have htop : ∀ S : Finset J, S.card = n + 2 → ∀ l ∈ face S,
        gseq v Gm (n + 1) l = Gm S (tau S l, gseq v Gm n (mu S l)) := by
      intro S hS l hl
      have hsub := ((mem_face_iff _ _).1 hl).2
      by_cases heq : supp l = S
      · subst heq
        simp [gseq, hS]
      · have hss : supp l ⊂ S := Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩
        have hc : (supp l).card ≤ n + 1 := by
          have := Finset.card_lt_card hss; omega
        simp only [gseq, if_pos hc]
        rw [tau_eq_zero_of_ssubset hl hss, mu_eq_self_of_ssubset hl hss, hG0 S _ (by omega)]
    refine ⟨continuousOn_lev _ _ fun S hS => ?_, fun l hl => ?_⟩
    · rcases Nat.lt_or_ge S.card (n + 2) with hlt | hge
      · -- lower face: agrees with the previous stage
        refine (ihc.mono fun l hl => ?_).congr fun l hl => ?_
        · have hl' := (mem_face_iff _ _).1 hl
          exact ⟨hl'.1, (Finset.card_le_card hl'.2).trans (by omega)⟩
        · have hl' := (mem_face_iff _ _).1 hl
          have hc : (supp l).card ≤ n + 1 := (Finset.card_le_card hl'.2).trans (by omega)
          simp [gseq, hc]
      · have hS2 : S.card = n + 2 := le_antisymm hS hge
        have hS2' : 2 ≤ S.card := by omega
        obtain ⟨c, hc⟩ := hG1 S hS2'
        refine ContinuousOn.congr ?_ (htop S hS2)
        intro l0 hl0
        by_cases hs0 : sr S l0 = 0
        · -- the barycentre: use the tube lemma
          have hval : Gm S (tau S l0, gseq v Gm n (mu S l0)) = c := by
            rw [tau_eq_one_of_sr_eq_zero hs0, hc]
          rw [ContinuousWithinAt, hval]
          rw [(nhds_basis_opens c).tendsto_right_iff]
          rintro W ⟨hcW, hWo⟩
          have hKc : IsCompact (gseq v Gm n '' lev (n + 1)) := (isCompact_lev _).image_of_continuousOn ihc
          have hsub : ({1} : Set I) ×ˢ (gseq v Gm n '' lev (n + 1)) ⊆ Gm S ⁻¹' W := by
            rintro ⟨t, y⟩ ⟨ht, -⟩
            simp only [mem_singleton_iff] at ht
            subst ht
            simp [hc, hcW]
          obtain ⟨u, w, hu, hw, h1u, hKw, huw⟩ :=
            generalized_tube_lemma isCompact_singleton hKc (hWo.preimage (Gm S).continuous) hsub
          have hτ : ∀ᶠ l in 𝓝 l0, tau S l ∈ u := by
            have : tau S l0 ∈ u := by rw [tau_eq_one_of_sr_eq_zero hs0]; exact h1u rfl
            exact (continuous_tau S).continuousAt.preimage_mem_nhds (hu.mem_nhds this)
          filter_upwards [nhdsWithin_le_nhds hτ, self_mem_nhdsWithin] with l hlu hlS
          rcases (sr_nonneg hlS).eq_or_lt with h0 | hpos
          · show Gm S (tau S l, gseq v Gm n (mu S l)) ∈ W
            rw [tau_eq_one_of_sr_eq_zero h0.symm, hc]; exact hcW
          · obtain ⟨hmf, hms⟩ := mu_mem hlS hpos
            have hmlev : mu S l ∈ lev (n + 1) :=
              ⟨hmf.1, by have := Finset.card_lt_card hms; omega⟩
            exact huw ⟨hlu, hKw ⟨_, hmlev, rfl⟩⟩
        · -- away from the barycentre: composition of continuous maps
          have hpos : 0 < sr S l0 := lt_of_le_of_ne (sr_nonneg hl0) (Ne.symm hs0)
          have hmuc : ContinuousAt (mu S) l0 := by
            refine continuousAt_pi.2 fun j => ?_
            simp only [mu]
            split_ifs
            · exact ((continuous_apply j).continuousAt.sub (continuous_mn S).continuousAt).div
                (continuous_sr S).continuousAt hpos.ne'
            · exact continuousAt_const
          have hopen : {l | 0 < sr S l} ∈ 𝓝 l0 :=
            (isOpen_lt continuous_const (continuous_sr S)).mem_nhds hpos
          have hmaps : MapsTo (mu S) (face S ∩ {l | 0 < sr S l}) (lev (n + 1)) := by
            rintro l ⟨hlS, hlp⟩
            obtain ⟨hmf, hms⟩ := mu_mem hlS hlp
            exact ⟨hmf.1, by have := Finset.card_lt_card hms; omega⟩
          have hgm : ContinuousWithinAt (fun l => gseq v Gm n (mu S l))
              (face S ∩ {l | 0 < sr S l}) l0 :=
            (ihc _ (hmaps ⟨hl0, hpos⟩)).comp hmuc.continuousWithinAt hmaps
          rw [← continuousWithinAt_inter hopen]
          exact (Gm S).continuous.continuousAt.comp_continuousWithinAt
            (((continuous_tau S).continuousAt.continuousWithinAt).prodMk hgm)
    · -- membership
      by_cases hc : (supp l).card ≤ n + 1
      · have : gseq v Gm (n + 1) l = gseq v Gm n l := by simp [gseq, hc]
        rw [this]; exact ihU l ⟨hl.1, hc⟩
      · have hS2 : (supp l).card = n + 2 := by have := hl.2; omega
        have hlS : l ∈ face (supp l) := (mem_face_iff _ _).2 ⟨hl.1, subset_rfl⟩
        rw [htop _ hS2 l hlS]
        rcases (sr_nonneg hlS).eq_or_lt with h0 | hpos
        · -- barycentre: the constant `c` lies in `U`
          obtain ⟨c, hcc⟩ := hG1 (supp l) (by omega)
          rw [tau_eq_one_of_sr_eq_zero h0.symm, hcc]
          obtain ⟨j, hj⟩ := supp_nonempty hl.1
          have hjs : ({j} : Finset J) ⊂ supp l := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.singleton_subset_iff.2 hj, fun h => ?_⟩
            rw [← h] at hS2; simp at hS2
          have := hGU _ (by omega) 1 (v j) (h2 _ _ hjs (Finset.singleton_nonempty j) (hv j))
          rwa [hcc] at this
        · obtain ⟨hmf, hms⟩ := mu_mem hlS hpos
          have hmlev : mu (supp l) l ∈ lev (n + 1) :=
            ⟨hmf.1, by have := Finset.card_lt_card hms; omega⟩
          refine hGU _ (by omega) _ _ (h2 _ _ hms (supp_nonempty hmf.1) (ihU _ hmlev))

theorem simplex_extension (U U' : Finset J → Set Y) (h1 : ∀ j, (U {j}).Nonempty)
    (h2 : ∀ S T : Finset J, T ⊂ S → T.Nonempty → U T ⊆ U' S)
    (h3 : ∀ S : Finset J, 2 ≤ S.card → ∃ G : C(I × Y, Y), (∀ y, G (0, y) = y) ∧
      (∃ c, ∀ y, G (1, y) = c) ∧ ∀ t y, y ∈ U' S → G (t, y) ∈ U S) :
    ∃ g : (J → ℝ) → Y, ContinuousOn g (stdSimplex ℝ J) ∧
      ∀ l ∈ stdSimplex ℝ J, g l ∈ U (supp l) := by
  classical
  let v : J → Y := fun j => (h1 j).some
  let Gm : Finset J → C(I × Y, Y) := fun S =>
    if h : 2 ≤ S.card then (h3 S h).choose else ContinuousMap.snd
  have hGm : ∀ S (h : 2 ≤ S.card), Gm S = (h3 S h).choose := fun S h => by simp [Gm, h]
  obtain ⟨hc, hU⟩ := gseq_spec U U' v (fun j => (h1 j).some_mem) Gm
    (fun S y h => by rw [hGm S h]; exact (h3 S h).choose_spec.1 y)
    (fun S h => by rw [hGm S h]; exact (h3 S h).choose_spec.2.1)
    (fun S h => by rw [hGm S h]; exact (h3 S h).choose_spec.2.2) h2 (Fintype.card J)
  have hsub : stdSimplex ℝ J ⊆ lev (Fintype.card J + 1) := fun l hl =>
    ⟨hl, (Finset.card_le_univ _).trans (Nat.le_succ _)⟩
  exact ⟨_, hc.mono hsub, fun l hl => hU l (hsub hl)⟩

end SX
end SXwrap

/-- A ramp `0 → 1`. -/
noncomputable def ramp (s : ℝ) : ℝ := max 0 (min 1 s)

/-- The hat function `max 0 (1 - |u|)`, written as a difference of ramps. -/
noncomputable def hat (u : ℝ) : ℝ := ramp (u + 1) - ramp u

theorem continuous_ramp : Continuous ramp := continuous_const.max (continuous_const.min continuous_id)

theorem continuous_hat : Continuous hat :=
  (continuous_ramp.comp (continuous_id.add continuous_const)).sub continuous_ramp

theorem ramp_mono : Monotone ramp := fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

theorem hat_nonneg (u : ℝ) : 0 ≤ hat u := sub_nonneg.2 (ramp_mono (by linarith))

theorem ramp_of_nonpos {s : ℝ} (h : s ≤ 0) : ramp s = 0 := by
  unfold ramp; rw [min_eq_right (by linarith), max_eq_left h]

theorem ramp_of_one_le {s : ℝ} (h : 1 ≤ s) : ramp s = 1 := by
  unfold ramp; rw [min_eq_left h, max_eq_right zero_le_one]

theorem abs_lt_of_hat_ne_zero {u : ℝ} (h : hat u ≠ 0) : |u| < 1 := by
  by_contra h'
  push Not at h'
  apply h
  rcases le_abs'.1 h' with h1 | h1
  · simp only [hat, ramp_of_nonpos (show u + 1 ≤ 0 by linarith), ramp_of_nonpos (show u ≤ 0 by linarith),
      sub_self]
  · simp only [hat, ramp_of_one_le (show 1 ≤ u + 1 by linarith), ramp_of_one_le h1, sub_self]

theorem sum_hat (p : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ p) :
    ∑ a : Fin (p + 1), hat (t - ((a : ℕ) : ℝ)) = 1 := by
  have e : ∀ a : ℕ, hat (t - (a : ℝ)) =
      ramp (t + 1 - (a : ℝ)) - ramp (t + 1 - ((a + 1 : ℕ) : ℝ)) := by
    intro a
    simp only [hat]
    congr 2 <;> push_cast <;> ring
  rw [Fin.sum_univ_eq_sum_range (fun a => hat (t - (a : ℝ))) (p + 1),
    Finset.sum_congr rfl (fun a _ => e a),
    Finset.sum_range_sub' (fun a : ℕ => ramp (t + 1 - (a : ℝ)))]
  simp only [Nat.cast_zero, sub_zero]
  rw [ramp_of_one_le (by linarith), ramp_of_nonpos (by push_cast; linarith)]
  norm_num

theorem card_hat_support (p : ℕ) (t : ℝ) :
    (Finset.univ.filter (fun a : Fin (p + 1) => |t - ((a : ℕ) : ℝ)| < 1)).card ≤ 2 := by
  set k := ⌊t⌋
  calc _ ≤ ({k, k + 1} : Finset ℤ).card := by
        refine Finset.card_le_card_of_injOn (fun a : Fin (p + 1) => ((a : ℕ) : ℤ)) ?_ ?_
        · intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at ha
          have h1 := abs_lt.1 ha
          have hk1 := Int.floor_le t
          have hk2 := Int.lt_floor_add_one t
          have ha1 : k - 1 < ((a : ℕ) : ℤ) := by
            have : ((k - 1 : ℤ) : ℝ) < (((a : ℕ) : ℤ) : ℝ) := by push_cast; linarith
            exact_mod_cast this
          have ha2 : ((a : ℕ) : ℤ) < k + 2 := by
            have : (((a : ℕ) : ℤ) : ℝ) < ((k + 2 : ℤ) : ℝ) := by push_cast; linarith
            exact_mod_cast this
          simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
          omega
        · intro a _ b _ hab
          simp only at hab
          exact Fin.ext (by exact_mod_cast hab)
    _ ≤ 2 := Finset.card_le_two

theorem cube_partition (N : ℕ) : ∀ r > 0, ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
    (lam : (Fin N → ℝ) → J → ℝ) (c : J → (Fin N → ℝ)), ContinuousOn lam (Icc 0 1) ∧
    (∀ x ∈ Icc (0 : Fin N → ℝ) 1, lam x ∈ stdSimplex ℝ J) ∧
    (∀ x ∈ Icc (0 : Fin N → ℝ) 1, (supp (lam x)).card ≤ 2 ^ N) ∧
    ∀ x ∈ Icc (0 : Fin N → ℝ) 1, ∀ j, lam x j ≠ 0 → dist x (c j) < r := by
  intro r hr
  obtain ⟨p, hp⟩ := exists_nat_gt (1 / r)
  have hp0 : (0 : ℝ) < p := lt_trans (by positivity) hp
  have hpinv : 1 / (p : ℝ) < r := by
    rw [div_lt_iff₀ hp0]
    rw [div_lt_iff₀ hr] at hp
    linarith
  refine ⟨Fin N → Fin (p + 1), inferInstance, inferInstance,
    fun x j => ∏ i, hat (p * x i - ((j i : ℕ) : ℝ)), fun j i => ((j i : ℕ) : ℝ) / p,
    ?_, ?_, ?_, ?_⟩
  · refine Continuous.continuousOn (continuous_pi fun j => continuous_finset_prod _ fun i _ => ?_)
    exact continuous_hat.comp ((continuous_const.mul (continuous_apply i)).sub continuous_const)
  · intro x hx
    refine ⟨fun j => Finset.prod_nonneg fun i _ => hat_nonneg _, ?_⟩
    rw [← Fintype.prod_sum (fun i (a : Fin (p + 1)) => hat (p * x i - ((a : ℕ) : ℝ)))]
    refine Finset.prod_eq_one fun i _ => sum_hat p _ ?_ ?_
    · exact mul_nonneg hp0.le (hx.1 i)
    · have := hx.2 i
      have h0 := hx.1 i
      simp only [Pi.one_apply] at this
      nlinarith
  · intro x _
    have hsub : supp (fun j : Fin N → Fin (p + 1) => ∏ i, hat (p * x i - ((j i : ℕ) : ℝ))) ⊆
        Fintype.piFinset (fun i => Finset.univ.filter
          (fun a : Fin (p + 1) => |p * x i - ((a : ℕ) : ℝ)| < 1)) := by
      intro j hj
      rw [mem_supp] at hj
      rw [Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact abs_lt_of_hat_ne_zero ((Finset.prod_ne_zero_iff.1 hj) i (Finset.mem_univ _))
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset]
    calc ∏ i, _ ≤ ∏ _i : Fin N, 2 :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _) fun i _ => card_hat_support p _
      _ = 2 ^ N := by simp
  · intro x _ j hj
    rw [dist_pi_lt_iff hr]
    intro i
    have h := abs_lt_of_hat_ne_zero ((Finset.prod_ne_zero_iff.1 hj) i (Finset.mem_univ _))
    rw [Real.dist_eq]
    have e : (p : ℝ) * x i - ((j i : ℕ) : ℝ) = p * (x i - ((j i : ℕ) : ℝ) / p) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hp0] at h
    have : |x i - ((j i : ℕ) : ℝ) / p| < 1 / p := by
      rw [lt_div_iff₀ hp0]; linarith
    linarith

theorem exists_pos_le_finset {α : Type*} (W : Finset α) (f : α → ℝ) (hf : ∀ w ∈ W, 0 < f w) :
    ∃ c > 0, ∀ w ∈ W, c ≤ f w := by
  classical
  revert hf
  refine Finset.induction_on W (fun _ => ⟨1, one_pos, by simp⟩) ?_
  intro a W _ ih hf
  obtain ⟨c, hc, hcW⟩ := ih (fun w hw => hf w (Finset.mem_insert_of_mem hw))
  refine ⟨min c (f a), lt_min hc (hf a (Finset.mem_insert_self a W)), fun w hw => ?_⟩
  rcases Finset.mem_insert.1 hw with rfl | hw
  · exact min_le_right _ _
  · exact (min_le_left _ _).trans (hcW w hw)

theorem level_step {X : Type*} [MetricSpace X] {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (K : Set X) (hK : IsCompact K) (Ψ : X → Set Y)
    (hNN : ∀ x ∈ K, NullNbhd (Ψ x))
    (husc : ∀ x ∈ K, ∀ η > 0, ∃ ρ > 0, ∀ x' ∈ K, dist x' x < ρ → Ψ x' ⊆ thickening η (Ψ x))
    (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    ∃ (W : Finset X) (ρ δ : X → ℝ) (ε' r' : ℝ), 0 < ε' ∧ ε' ≤ ε ∧ 0 < r' ∧ r' ≤ r ∧
      (∀ w ∈ W, w ∈ K) ∧ (∀ x ∈ K, ∃ w ∈ W, dist x w < ρ w / 4) ∧
      (∀ w ∈ W, ρ w ≤ r ∧ 4 * r' ≤ ρ w ∧ 2 * ε' ≤ δ w) ∧
      (∀ w ∈ W, ∀ x' ∈ K, dist x' w < ρ w → Ψ x' ⊆ thickening (δ w / 2) (Ψ w)) ∧
      (∀ w ∈ W, ∃ G : C(I × Y, Y), (∀ y, G (0, y) = y) ∧ (∃ c, ∀ y, G (1, y) = c) ∧
        ∀ t y, y ∈ thickening (δ w) (Ψ w) → G (t, y) ∈ thickening ε (Ψ w)) := by
  classical
  have hx : ∀ x : X, ∃ δ : ℝ, ∃ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ ρ ≤ r ∧ (x ∈ K →
      (∃ G : C(I × Y, Y), (∀ y, G (0, y) = y) ∧ (∃ c, ∀ y, G (1, y) = c) ∧
        ∀ t y, y ∈ thickening δ (Ψ x) → G (t, y) ∈ thickening ε (Ψ x)) ∧
      ∀ x' ∈ K, dist x' x < ρ → Ψ x' ⊆ thickening (δ / 2) (Ψ x)) := by
    intro x
    by_cases hxK : x ∈ K
    · obtain ⟨δ, hδ, G, hG0, hG1, hGt⟩ := hNN x hxK ε hε
      obtain ⟨ρ, hρ, hρu⟩ := husc x hxK (δ / 2) (by positivity)
      exact ⟨δ, min ρ r, hδ, lt_min hρ hr, min_le_right _ _, fun _ =>
        ⟨⟨G, hG0, hG1, hGt⟩, fun x' hx' hd => hρu x' hx' (lt_of_lt_of_le hd (min_le_left _ _))⟩⟩
    · exact ⟨1, r, one_pos, hr, le_rfl, fun h => absurd h hxK⟩
  choose δ ρ hδ hρ hρr hdata using hx
  obtain ⟨W, hWK, hcov⟩ := hK.elim_nhds_subcover (fun x => ball x (ρ x / 4))
    (fun x _ => ball_mem_nhds x (by have := hρ x; positivity))
  obtain ⟨c1, hc1, hc1W⟩ := exists_pos_le_finset W (fun w => δ w / 2)
    (fun w _ => by have := hδ w; positivity)
  obtain ⟨c2, hc2, hc2W⟩ := exists_pos_le_finset W (fun w => ρ w / 4)
    (fun w _ => by have := hρ w; positivity)
  refine ⟨W, ρ, δ, min ε c1, min r c2, lt_min hε hc1, min_le_left _ _, lt_min hr hc2,
    min_le_left _ _, hWK, fun x hx => ?_, fun w hw => ⟨hρr w, ?_, ?_⟩,
    fun w hw => (hdata w (hWK w hw)).2, fun w hw => (hdata w (hWK w hw)).1⟩
  · have := hcov hx
    simp only [mem_iUnion, mem_ball, exists_prop] at this
    obtain ⟨w, hw, hd⟩ := this
    exact ⟨w, hw, hd⟩
  · have h : c2 ≤ ρ w / 4 := hc2W w hw
    have := min_le_right r c2
    linarith
  · have h : c1 ≤ δ w / 2 := hc1W w hw
    have := min_le_right ε c1
    linarith

theorem approx {X : Type*} [MetricSpace X] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K : Set X) (hK : IsCompact K) (Ψ : X → Set Y) (hne : ∀ x ∈ K, (Ψ x).Nonempty)
    (hNN : ∀ x ∈ K, NullNbhd (Ψ x))
    (husc : ∀ x ∈ K, ∀ η > 0, ∃ ρ > 0, ∀ x' ∈ K, dist x' x < ρ → Ψ x' ⊆ thickening η (Ψ x))
    (D : ℕ) (hpart : ∀ r > 0, ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (lam : X → J → ℝ)
      (c : J → X), ContinuousOn lam K ∧ (∀ x ∈ K, lam x ∈ stdSimplex ℝ J) ∧
      (∀ x ∈ K, (supp (lam x)).card ≤ D) ∧ ∀ x ∈ K, ∀ j, lam x j ≠ 0 → dist x (c j) < r) :
    ∀ ε > 0, ∃ f : X → Y, ContinuousOn f K ∧
      ∀ x ∈ K, ∃ x' ∈ K, dist x x' < ε ∧ ∃ y ∈ Ψ x', dist (f x) y < ε := by
  classical
  intro ε hε
  rcases K.eq_empty_or_nonempty with hK0 | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => 0, by simp [hK0], fun x hx => by simp [hK0] at hx⟩
  have LS := fun (p : {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2}) =>
    level_step K hK Ψ hNN husc p.1.1 p.1.2 p.2.1 p.2.2
  choose W ρ δ ε' r' hε'0 hε'le hr'0 hr'le hWK hcov hprop husc' hG using LS
  let step : {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2} → {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2} :=
    fun p => ⟨(ε' p, r' p), hε'0 p, hr'0 p⟩
  let p0 : {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2} := ⟨(ε / 2, ε / 2), by positivity, by positivity⟩
  let sq : ℕ → {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2} := fun d => step^[d] p0
  have hsq : ∀ d, sq (d + 1) = step (sq d) := fun d => Function.iterate_succ_apply' step d p0
  have heps_succ : ∀ d, (sq (d + 1)).1.1 = ε' (sq d) := fun d => by rw [hsq]
  have hrad_succ : ∀ d, (sq (d + 1)).1.2 = r' (sq d) := fun d => by rw [hsq]
  have heps_anti : Antitone (fun d => (sq d).1.1) := antitone_nat_of_succ_le fun d => by
    show (sq (d + 1)).1.1 ≤ (sq d).1.1
    rw [heps_succ]; exact hε'le _
  have hrad_anti : Antitone (fun d => (sq d).1.2) := antitone_nat_of_succ_le fun d => by
    show (sq (d + 1)).1.2 ≤ (sq d).1.2
    rw [hrad_succ]; exact hr'le _
  have heps0 : (sq 0).1.1 = ε / 2 := rfl
  have hrad0 : (sq 0).1.2 = ε / 2 := rfl
  have hepspos : ∀ d, 0 < (sq d).1.1 := fun d => (sq d).2.1
  have hradpos : ∀ d, 0 < (sq d).1.2 := fun d => (sq d).2.2
  obtain ⟨J, _, _, lam, c, hlc, hls, hlD, hld⟩ := hpart ((sq D).1.2 / 2) (by
    have := hradpos D; positivity)
  let Nv : Finset J → Prop := fun S => S.Nonempty ∧ ∃ x ∈ K, ∀ j ∈ S, lam x j ≠ 0
  have hanc : ∀ S : Finset J, ∃ xr : X, ∃ w : X, Nv S → xr ∈ K ∧ (∀ j ∈ S, lam xr j ≠ 0) ∧
      w ∈ W (sq (D - S.card)) ∧ dist xr w < ρ (sq (D - S.card)) w / 4 := by
    intro S
    by_cases h : Nv S
    · obtain ⟨-, x, hx, hxj⟩ := h
      obtain ⟨w, hw, hd⟩ := hcov _ x hx
      exact ⟨x, w, fun _ => ⟨hx, hxj, hw, hd⟩⟩
    · exact ⟨x₀, x₀, fun h' => absurd h' h⟩
  choose xr wa hxw using hanc
  have hcardD : ∀ S, Nv S → S.card ≤ D := by
    intro S hS
    obtain ⟨hxS, hxSj, -, -⟩ := hxw S hS
    refine le_trans (Finset.card_le_card fun j hj => ?_) (hlD _ hxS)
    exact (mem_supp _ _).2 (hxSj j hj)
  let U : Finset J → Set Y := fun S =>
    if Nv S then thickening (sq (D - S.card)).1.1 (Ψ (wa S)) else univ
  let U' : Finset J → Set Y := fun S =>
    if Nv S then thickening (δ (sq (D - S.card)) (wa S)) (Ψ (wa S)) else univ
  have h1 : ∀ j, (U {j}).Nonempty := by
    intro j
    by_cases h : Nv {j}
    · have hwK := hWK _ _ (hxw _ h).2.2.1
      simp only [U, if_pos h]
      exact (hne _ hwK).mono (self_subset_thickening (hepspos _) _)
    · simp only [U, if_neg h]
      exact univ_nonempty
  have h3 : ∀ S : Finset J, 2 ≤ S.card → ∃ G : C(I × Y, Y), (∀ y, G (0, y) = y) ∧
      (∃ c, ∀ y, G (1, y) = c) ∧ ∀ t y, y ∈ U' S → G (t, y) ∈ U S := by
    intro S _
    by_cases h : Nv S
    · obtain ⟨G, hG0, hG1, hGt⟩ := hG (sq (D - S.card)) (wa S) (hxw S h).2.2.1
      refine ⟨G, hG0, hG1, fun t y hy => ?_⟩
      simp only [U, U', if_pos h] at hy ⊢
      exact hGt t y hy
    · refine ⟨⟨fun p => (1 - (p.1 : ℝ)) • p.2, by fun_prop⟩, fun y => by simp, ⟨0, fun y => by simp⟩,
        fun t y _ => ?_⟩
      simp only [U, if_neg h]
      exact mem_univ _
  have h2 : ∀ S T : Finset J, T ⊂ S → T.Nonempty → U T ⊆ U' S := by
    intro S T hTS hTne y hy
    by_cases hS : Nv S
    swap
    · simp only [U', if_neg hS]; exact mem_univ _
    have hT : Nv T := ⟨hTne, xr S, (hxw S hS).1, fun j hj => (hxw S hS).2.1 j (hTS.subset hj)⟩
    simp only [U, U', if_pos hS, if_pos hT] at hy ⊢
    have hcS := hcardD S hS
    have hcTS : T.card < S.card := Finset.card_lt_card hTS
    have hS1 : 1 ≤ S.card := hS.1.card_pos
    obtain ⟨hxS, hxSj, hwS, hdS⟩ := hxw S hS
    obtain ⟨hxT, hxTj, hwT, hdT⟩ := hxw T hT
    obtain ⟨hρS, h4S, h2S⟩ := hprop _ _ hwS
    obtain ⟨hρT, -, -⟩ := hprop _ _ hwT
    have hradT : (sq (D - T.card)).1.2 ≤ (sq (D - S.card + 1)).1.2 := hrad_anti (by omega)
    have hradD : (sq D).1.2 ≤ (sq (D - S.card + 1)).1.2 := hrad_anti (by omega)
    rw [hrad_succ] at hradT hradD
    obtain ⟨j, hj⟩ := hTne
    have hj1 := hld _ hxT j (hxTj j hj)
    have hj2 := hld _ hxS j (hxSj j (hTS.subset hj))
    have hdist : dist (wa T) (wa S) < ρ (sq (D - S.card)) (wa S) := by
      have t1 := dist_triangle4 (wa T) (xr T) (c j) (wa S)
      have t2 := dist_triangle (c j) (xr S) (wa S)
      rw [dist_comm (wa T) (xr T)] at t1
      rw [dist_comm (c j) (xr S)] at t2
      have e1 : ρ (sq (D - T.card)) (wa T) ≤ ρ (sq (D - S.card)) (wa S) / 4 := by linarith
      have e2 : (sq D).1.2 ≤ ρ (sq (D - S.card)) (wa S) / 4 := by linarith
      have e3 : dist (xr T) (wa T) < ρ (sq (D - S.card)) (wa S) / 16 := by linarith
      have e4 : dist (xr T) (c j) < ρ (sq (D - S.card)) (wa S) / 8 := by linarith
      have e5 : dist (xr S) (c j) < ρ (sq (D - S.card)) (wa S) / 8 := by linarith
      have e6 : 0 < ρ (sq (D - S.card)) (wa S) := by
        have := dist_nonneg (x := xr S) (y := wa S); linarith
      linarith
    have hΨ := husc' _ _ hwS (wa T) (hWK _ _ hwT) hdist
    have heT : (sq (D - T.card)).1.1 ≤ δ (sq (D - S.card)) (wa S) / 2 := by
      have := heps_anti (show D - S.card + 1 ≤ D - T.card by omega)
      simp only at this
      rw [heps_succ] at this
      linarith
    have := thickening_subset_of_subset (sq (D - T.card)).1.1 hΨ hy
    have := thickening_thickening_subset _ _ _ this
    exact thickening_mono (by linarith) _ this
  obtain ⟨g, hgc, hgU⟩ := simplex_extension U U' h1 h2 h3
  refine ⟨fun x => g (lam x), hgc.comp hlc (fun x hx => hls x hx), fun x hx => ?_⟩
  have hS : Nv (supp (lam x)) :=
    ⟨supp_nonempty (hls x hx), x, hx, fun j hj => (mem_supp _ _).1 hj⟩
  have hmem := hgU (lam x) (hls x hx)
  simp only [U, if_pos hS] at hmem
  obtain ⟨y, hy, hdy⟩ := mem_thickening_iff.1 hmem
  obtain ⟨hxS, hxSj, hwS, hdS⟩ := hxw _ hS
  obtain ⟨hρS, -, -⟩ := hprop _ _ hwS
  have hrD : (sq D).1.2 ≤ ε / 2 := hrad0 ▸ hrad_anti (Nat.zero_le D)
  have hrS : (sq (D - (supp (lam x)).card)).1.2 ≤ ε / 2 := hrad0 ▸ hrad_anti (Nat.zero_le _)
  have heS : (sq (D - (supp (lam x)).card)).1.1 ≤ ε / 2 := heps0 ▸ heps_anti (Nat.zero_le _)
  obtain ⟨j, hj⟩ := supp_nonempty (hls x hx)
  have hj1 := hld _ hx j ((mem_supp _ _).1 hj)
  have hj2 := hld _ hxS j (hxSj j hj)
  refine ⟨wa _, hWK _ _ hwS, ?_, y, hy, by linarith⟩
  have t1 := dist_triangle4 x (c j) (xr (supp (lam x))) (wa (supp (lam x)))
  rw [dist_comm (c j)] at t1
  linarith

/-! ## Part 3: Eilenberg–Montgomery on the cube -/

theorem clamp_dist {N : ℕ} (a y : Fin N → ℝ) (hy : y ∈ Icc (0 : Fin N → ℝ) 1) :
    dist (fun i => max 0 (min 1 (a i))) y ≤ dist a y := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  have h0 : 0 ≤ y i := hy.1 i
  have h1 : y i ≤ 1 := hy.2 i
  refine le_trans ?_ (dist_le_pi_dist a y i)
  rw [Real.dist_eq, Real.dist_eq]
  have e : max 0 (min 1 (y i)) = y i := by
    rw [min_eq_right h1, max_eq_right h0]
  calc |max 0 (min 1 (a i)) - y i|
      = |max (min 1 (a i)) 0 - max (min 1 (y i)) 0| := by
        rw [max_comm 0 (min 1 (a i)), max_comm (min 1 (y i)) 0, e]
    _ ≤ |min 1 (a i) - min 1 (y i)| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |a i - y i| := abs_min_sub_min_le_max _ _ _ _
    _ = |a i - y i| := by simp

theorem em_cube (N : ℕ) (Ψ : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hΓ : IsClosed {p : (Fin N → ℝ) × (Fin N → ℝ) | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Ψ p.1})
    (hsub : ∀ x ∈ Icc (0 : Fin N → ℝ) 1, Ψ x ⊆ Icc 0 1)
    (hne : ∀ x ∈ Icc (0 : Fin N → ℝ) 1, (Ψ x).Nonempty)
    (hc : ∀ x ∈ Icc (0 : Fin N → ℝ) 1, IsContractible (Ψ x)) :
    ∃ x ∈ Icc (0 : Fin N → ℝ) 1, x ∈ Ψ x := by
  set K : Set (Fin N → ℝ) := Icc 0 1 with hKdef
  have hK : IsCompact K := isCompact_Icc
  set Γ := {p : (Fin N → ℝ) × (Fin N → ℝ) | p.1 ∈ K ∧ p.2 ∈ Ψ p.1} with hΓdef
  have hΓK : Γ ⊆ K ×ˢ K := fun p hp => ⟨hp.1, hsub _ hp.1 hp.2⟩
  have hΓc : IsCompact Γ := (hK.prod hK).of_isClosed_subset hΓ hΓK
  have hval : ∀ x ∈ K, IsCompact (Ψ x) := by
    intro x hx
    have : Ψ x = (fun y => (x, y)) ⁻¹' Γ := by
      ext y; simp [hΓdef, hx]
    refine hK.of_isClosed_subset ?_ (hsub x hx)
    rw [this]; exact hΓ.preimage (by fun_prop)
  by_contra hno
  push Not at hno
  have hO : Γ ⊆ {p | p.1 ≠ p.2} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_setOf_eq]
    rintro rfl
    exact hno x hx hy
  obtain ⟨η, hη, hηO⟩ :=
    hΓc.exists_thickening_subset_open (isOpen_ne_fun continuous_fst continuous_snd) hO
  have husc := usc_of_closed_graph K K hK hK Ψ hΓ hsub
  have hNN : ∀ x ∈ K, NullNbhd (Ψ x) := fun x hx =>
    nullNbhd_of_contractible _ (hval x hx) (hc x hx)
  obtain ⟨f, hf, hfa⟩ := approx K hK Ψ hne hNN husc (2 ^ N) (cube_partition N) η hη
  set f' : (Fin N → ℝ) → (Fin N → ℝ) := fun x i => max 0 (min 1 (f x i)) with hf'
  have hf'c : ContinuousOn f' K := by
    refine continuousOn_pi.2 fun i => ?_
    have hcl : Continuous (fun t : ℝ => max 0 (min 1 t)) :=
      continuous_const.max (continuous_const.min continuous_id)
    exact hcl.comp_continuousOn ((continuous_apply i).comp_continuousOn hf)
  have hf'K : MapsTo f' K K := by
    intro x _
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)
  obtain ⟨x, hxK, hfx⟩ := BrouwerLib.brouwer_cube_Icc f' hf'c hf'K
  obtain ⟨x', hx'K, hxx', y, hy, hfy⟩ := hfa x hxK
  have hyK : y ∈ K := hsub x' hx'K hy
  have hdist : dist (f' x) y ≤ dist (f x) y := clamp_dist (f x) y hyK
  have hmem : (x, x) ∈ thickening η Γ := by
    rw [mem_thickening_iff]
    refine ⟨(x', y), ⟨hx'K, hy⟩, ?_⟩
    rw [Prod.dist_eq]
    refine max_lt hxx' ?_
    calc dist x y = dist (f' x) y := by rw [hfx]
      _ ≤ dist (f x) y := hdist
      _ < η := hfy
  exact hηO hmem rfl

/-! ## Part 4: retracts -/

theorem emprop_of_retract_cube (m : ℕ) (Q : Set (Fin m → ℝ)) (hQK : Q ⊆ Icc 0 1)
    (hQ : IsClosed Q) (R : (Fin m → ℝ) → (Fin m → ℝ)) (hR : Continuous R)
    (hRQ : ∀ x, R x ∈ Q) (hRid : ∀ q ∈ Q, R q = q) : EMProp Q := by
  intro φ hφ hc
  set Ψ : (Fin m → ℝ) → Set (Fin m → ℝ) := fun x => Subtype.val '' φ ⟨R x, hRQ x⟩ with hΨ
  have hΓ : IsClosed {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Ψ p.1} := by
    have hF : Continuous (fun p : (Fin m → ℝ) × Q => ((⟨R p.1, hRQ p.1⟩ : Q), p.2)) := by
      fun_prop
    have hC : IsClosed ((fun p : (Fin m → ℝ) × Q => ((⟨R p.1, hRQ p.1⟩ : Q), p.2)) ⁻¹' graph φ) :=
      hφ.preimage hF
    have hE : Topology.IsClosedEmbedding (Prod.map (id : (Fin m → ℝ) → (Fin m → ℝ))
        (Subtype.val : Q → Fin m → ℝ)) :=
      Topology.IsClosedEmbedding.id.prodMap hQ.isClosedEmbedding_subtypeVal
    have hI := hE.isClosedMap _ hC
    have hset : {p : (Fin m → ℝ) × (Fin m → ℝ) | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Ψ p.1} =
        (Icc 0 1 ×ˢ univ) ∩ (Prod.map id Subtype.val ''
          ((fun p : (Fin m → ℝ) × Q => ((⟨R p.1, hRQ p.1⟩ : Q), p.2)) ⁻¹' graph φ)) := by
      ext ⟨x, y⟩
      simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_image,
        mem_preimage, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq, hΨ, graph]
      constructor
      · rintro ⟨hx, q, hq, rfl⟩
        exact ⟨hx, x, q, hq, rfl, rfl⟩
      · rintro ⟨hx, a, q, hq, rfl, rfl⟩
        exact ⟨hx, q, hq, rfl⟩
    rw [hset]
    exact (isClosed_Icc.prod isClosed_univ).inter hI
  have hsub : ∀ x ∈ Icc (0 : Fin m → ℝ) 1, Ψ x ⊆ Icc 0 1 := by
    intro x _
    rintro _ ⟨q, _, rfl⟩
    exact hQK q.2
  have hne : ∀ x ∈ Icc (0 : Fin m → ℝ) 1, (Ψ x).Nonempty := by
    intro x _
    obtain ⟨z, _⟩ := hc ⟨R x, hRQ x⟩
    exact ⟨_, z.1, z.2, rfl⟩
  have hcc : ∀ x ∈ Icc (0 : Fin m → ℝ) 1, IsContractible (Ψ x) := by
    intro x _
    exact isContractible_of_homeomorph
      (Topology.IsEmbedding.subtypeVal.homeomorphImage (φ ⟨R x, hRQ x⟩)) (hc _)
  obtain ⟨x, -, hx⟩ := em_cube m Ψ hΓ hsub hne hcc
  obtain ⟨q, hq, hqx⟩ := hx
  have hxQ : x ∈ Q := hqx ▸ q.2
  have hRx : (⟨R x, hRQ x⟩ : Q) = ⟨x, hxQ⟩ := Subtype.ext (hRid x hxQ)
  refine ⟨⟨x, hxQ⟩, ?_⟩
  have hq' : q = ⟨x, hxQ⟩ := Subtype.ext hqx
  have h' := hq
  rw [hq', hRx] at h'
  exact h'

theorem emprop_of_retract_euclid (m : ℕ) (Q : Set (EuclideanSpace ℝ (Fin m))) (hQ : IsCompact Q)
    (R : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hR : Continuous R)
    (hRQ : ∀ x, R x ∈ Q) (hRid : ∀ q ∈ Q, R q = q) : EMProp Q := by
  set L := EuclideanSpace.equiv (Fin m) ℝ with hL
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn (f := fun x => L x) L.continuous.continuousOn
  set M' : ℝ := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set c : ℝ := 1 / (2 * M') with hc
  have hc0 : c ≠ 0 := by positivity
  let A : EuclideanSpace ℝ (Fin m) ≃ₜ (Fin m → ℝ) :=
    L.toHomeomorph.trans ((Homeomorph.smulOfNeZero c hc0).trans
      (Homeomorph.addRight (fun _ => (1 / 2 : ℝ))))
  have hA : ∀ x, A x = c • L x + (fun _ => (1 / 2 : ℝ)) := fun x => rfl
  have hAK : A '' Q ⊆ Icc 0 1 := by
    rintro _ ⟨q, hq, rfl⟩
    have hb : ∀ i, |L q i| ≤ M' := fun i =>
      ((norm_le_pi_norm (L q) i).trans (hM q hq)).trans (le_max_left _ _)
    rw [hA]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 (hb i)).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hc]
      rw [div_mul_eq_mul_div, one_mul]
      have : -1 / 2 ≤ L q i / (2 * M') := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    · have := (abs_le.1 (hb i)).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hc]
      rw [div_mul_eq_mul_div, one_mul]
      have : L q i / (2 * M') ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  have hE := emprop_of_retract_cube m (A '' Q) hAK (hQ.image A.continuous).isClosed
    (fun y => A (R (A.symm y))) (by fun_prop) (fun y => ⟨_, hRQ _, rfl⟩)
    (by rintro _ ⟨q, hq, rfl⟩; simp [hRid q hq])
  exact EMProp.of_homeomorph (A.image Q) hE

/-- `A` is a neighbourhood retract. -/
def IsNR {E : Type*} [TopologicalSpace E] (A : Set E) : Prop :=
  ∃ U, IsOpen U ∧ A ⊆ U ∧ ∃ r : E → E, ContinuousOn r U ∧ MapsTo r U A ∧ ∀ a ∈ A, r a = a

theorem isNR_empty {E : Type*} [TopologicalSpace E] : IsNR (∅ : Set E) :=
  ⟨∅, isOpen_empty, subset_rfl, id, continuousOn_empty _, fun _ hx => hx, fun _ _ => rfl⟩

/-- Nearest-point retraction onto a complete convex set. -/
theorem convex_retract {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Set F) (hne : K.Nonempty) (hK : IsComplete K) (hc : Convex ℝ K) :
    ∃ P : F → F, Continuous P ∧ (∀ x, P x ∈ K) ∧ ∀ a ∈ K, P a = a := by
  have h := exists_norm_eq_iInf_of_complete_convex hne hK hc
  choose P hPK hPn using h
  have hchar : ∀ u, ∀ w ∈ K, inner ℝ (u - P u) (w - P u) ≤ 0 := fun u =>
    (norm_eq_iInf_iff_real_inner_le_zero hc (hPK u)).1 (hPn u)
  have hfix : ∀ a ∈ K, P a = a := by
    intro a ha
    have h1 := hchar a a ha
    rw [real_inner_self_eq_norm_sq] at h1
    have h2 : ‖a - P a‖ = 0 := by nlinarith [norm_nonneg (a - P a)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h2)).symm
  have hlip : LipschitzWith 1 P := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simp only [NNReal.coe_one, one_mul]
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := hchar u (P v) (hPK v)
    have h2 := hchar v (P u) (hPK u)
    have key : ‖P u - P v‖ ^ 2 ≤ inner ℝ (u - v) (P u - P v) := by
      have e : inner ℝ (u - v) (P u - P v) - ‖P u - P v‖ ^ 2 =
          - inner ℝ (u - P u) (P v - P u) - inner ℝ (v - P v) (P u - P v) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      linarith
    have hcs := real_inner_le_norm (u - v) (P u - P v)
    by_cases hz : ‖P u - P v‖ = 0
    · rw [hz]; exact norm_nonneg _
    · have hpos : 0 < ‖P u - P v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  exact ⟨P, hlip.continuous, hPK, hfix⟩

theorem isNR_convex {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {C : Set F}
    (hc : Convex ℝ C) (hC : IsCompact C) : IsNR C := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact isNR_empty
  · obtain ⟨P, hP, hPK, hPid⟩ := convex_retract C hne hC.isComplete hc
    exact ⟨univ, isOpen_univ, subset_univ _, P, hP.continuousOn, fun x _ => hPK x, hPid⟩

/-- Maps from closed sets into a neighbourhood retract extend to a neighbourhood. -/
theorem isNR_extend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} (hA : IsNR A) {F : Set E} (hF : IsClosed F) (f : E → E) (hf : ContinuousOn f F)
    (hfA : MapsTo f F A) :
    ∃ V, IsOpen V ∧ F ⊆ V ∧ ∃ f' : E → E, ContinuousOn f' V ∧ MapsTo f' V A ∧
      ∀ x ∈ F, f' x = f x := by
  obtain ⟨U, hU, hAU, r, hr, hrA, hrid⟩ := hA
  let f0 : C(F, E) := ⟨F.restrict f, continuousOn_iff_continuous_restrict.1 hf⟩
  obtain ⟨g, hg⟩ := f0.exists_restrict_eq hF
  have hgF : ∀ x (hx : x ∈ F), g x = f x := fun x hx => DFunLike.congr_fun hg ⟨x, hx⟩
  refine ⟨g ⁻¹' U, hU.preimage g.continuous, fun x hx => ?_, r ∘ g,
    hr.comp g.continuous.continuousOn (fun x hx => hx), fun x hx => hrA hx, fun x hx => ?_⟩
  · show g x ∈ U
    rw [hgF x hx]; exact hAU (hfA hx)
  · show r (g x) = f x
    rw [hgF x hx]; exact hrid _ (hfA hx)

/-- Borsuk's union theorem for compact neighbourhood retracts. -/
theorem isNR_union {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} (hAc : IsCompact A) (hBc : IsCompact B) (hA : IsNR A) (hB : IsNR B)
    (hD : IsNR (A ∩ B)) : IsNR (A ∪ B) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · simpa using hB
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simpa using hA
  have hAcl := hAc.isClosed
  have hBcl := hBc.isClosed
  obtain ⟨UD, hUD, hDU, rD, hrD, hrDD, hrDid⟩ := hD
  obtain ⟨ε, hε, hεU⟩ := (hAc.inter_right hBcl).exists_cthickening_subset_open hUD hDU
  set N := cthickening ε (A ∩ B) with hNdef
  have hNc : IsClosed N := isClosed_cthickening
  have hDint : A ∩ B ⊆ interior N :=
    (self_subset_thickening hε _).trans
      (interior_maximal (thickening_subset_cthickening ε _) isOpen_thickening)
  set a : E → ℝ := fun x => infDist x A with hadef
  set b : E → ℝ := fun x => infDist x B with hbdef
  have ha : Continuous a := continuous_infDist_pt A
  have hb : Continuous b := continuous_infDist_pt B
  set T := {x | a x = b x} with hTdef
  have hTc : IsClosed T := isClosed_eq ha hb
  have hTA : ∀ x ∈ A, x ∈ T → x ∈ B := by
    intro x hx hT
    have : b x = 0 := by
      have h' : a x = b x := hT
      rw [← h']; exact infDist_zero_of_mem hx
    exact (hBcl.mem_iff_infDist_zero hBne).2 this
  have hTB : ∀ x ∈ B, x ∈ T → x ∈ A := by
    intro x hx hT
    have : a x = 0 := by
      have h' : a x = b x := hT
      rw [h']; exact infDist_zero_of_mem hx
    exact (hAcl.mem_iff_infDist_zero hAne).2 this
  have hside : ∀ (P : Set E), IsClosed P → IsNR P → A ∩ B ⊆ P →
      (∀ x ∈ P, x ∈ T → x ∈ A ∩ B) → ∃ V, IsOpen V ∧ (P ∪ (T ∩ N)) ⊆ V ∧ ∃ e : E → E,
        ContinuousOn e V ∧ MapsTo e V P ∧ (∀ x ∈ P, e x = x) ∧ ∀ x ∈ T ∩ N, e x = rD x := by
    intro P hPc hPnr hDP hPT
    let h : E → E := fun x => if x ∈ P then x else rD x
    have hcont : ContinuousOn h (P ∪ (T ∩ N)) := by
      refine ContinuousOn.union_of_isClosed ?_ ?_ hPc (hTc.inter hNc)
      · exact continuousOn_id.congr fun x hx => by simp [h, hx]
      · refine (hrD.mono fun x hx => hεU hx.2).congr fun x hx => ?_
        by_cases hxP : x ∈ P
        · simp only [h, hxP, if_true]; exact (hrDid x (hPT x hxP hx.1)).symm
        · simp [h, hxP]
    have hmaps : MapsTo h (P ∪ (T ∩ N)) P := by
      intro x hx
      by_cases hxP : x ∈ P
      · simp [h, hxP]
      · simp only [h, hxP, if_false]
        rcases hx with hx | hx
        · exact absurd hx hxP
        · exact hDP (hrDD (hεU hx.2))
    obtain ⟨V, hV, hFV, e, he, heP, heq⟩ :=
      isNR_extend hPnr (hPc.union (hTc.inter hNc)) h hcont hmaps
    refine ⟨V, hV, hFV, e, he, heP, fun x hx => ?_, fun x hx => ?_⟩
    · rw [heq x (Or.inl hx)]; simp [h, hx]
    · rw [heq x (Or.inr hx)]
      by_cases hxP : x ∈ P
      · simp only [h, hxP, if_true]; exact (hrDid x (hPT x hxP hx.1)).symm
      · simp [h, hxP]
  obtain ⟨VA, hVA, hFA, eA, heA, heAA, heAid, heAD⟩ :=
    hside A hAcl hA inter_subset_left (fun x hx hT => ⟨hx, hTA x hx hT⟩)
  obtain ⟨VB, hVB, hFB, eB, heB, heBB, heBid, heBD⟩ :=
    hside B hBcl hB inter_subset_right (fun x hx hT => ⟨hTB x hx hT, hx⟩)
  set O := (VA ∪ {x | b x < a x}) ∩ (VB ∪ {x | a x < b x}) ∩ (T \ interior N)ᶜ with hOdef
  have hO : IsOpen O :=
    ((hVA.union (isOpen_lt hb ha)).inter (hVB.union (isOpen_lt ha hb))).inter
      (hTc.sdiff isOpen_interior).isOpen_compl
  have hcompl : ({x | a x ≤ b x} : Set E)ᶜ = {x | b x < a x} := by
    ext x; simp [not_le]
  refine ⟨O, hO, ?_, Set.piecewise {x | a x ≤ b x} eA eB, ?_, ?_, ?_⟩
  · intro x hx
    have hT' : x ∉ T \ interior N := by
      rintro ⟨hT, hN⟩
      rcases hx with hx | hx
      · exact hN (hDint ⟨hx, hTA x hx hT⟩)
      · exact hN (hDint ⟨hTB x hx hT, hx⟩)
    refine ⟨⟨?_, ?_⟩, hT'⟩
    · by_cases hxA : x ∈ A
      · exact Or.inl (hFA (Or.inl hxA))
      · right
        rcases hx with hx | hx
        · exact absurd hx hxA
        · show b x < a x
          have hb0 : b x = 0 := infDist_zero_of_mem hx
          rw [hb0]
          exact (hAcl.notMem_iff_infDist_pos hAne).1 hxA
    · by_cases hxB : x ∈ B
      · exact Or.inl (hFB (Or.inl hxB))
      · right
        rcases hx with hx | hx
        · show a x < b x
          have ha0 : a x = 0 := infDist_zero_of_mem hx
          rw [ha0]
          exact (hBcl.notMem_iff_infDist_pos hBne).1 hxB
        · exact absurd hx hxB
  · refine ContinuousOn.piecewise ?_ ?_ ?_
    · rintro x ⟨hxO, hxfr⟩
      have hxT : x ∈ T := frontier_le_subset_eq ha hb hxfr
      have hxN : x ∈ N := by
        by_contra hn
        exact hxO.2 ⟨hxT, fun h' => hn (interior_subset h')⟩
      rw [heAD x ⟨hxT, hxN⟩, heBD x ⟨hxT, hxN⟩]
    · refine heA.mono ?_
      rintro x ⟨hxO, hxc⟩
      rw [closure_le_eq ha hb] at hxc
      rcases hxO.1.1 with h | h
      · exact h
      · exact absurd (show a x ≤ b x from hxc) (not_le.2 h)
    · refine heB.mono ?_
      rintro x ⟨hxO, hxc⟩
      rw [hcompl] at hxc
      have hle : b x ≤ a x := closure_lt_subset_le hb ha hxc
      rcases hxO.1.2 with h | h
      · exact h
      · exact absurd h (not_lt.2 hle)
  · intro x hx
    by_cases h : a x ≤ b x
    · rw [Set.piecewise_eq_of_mem {x | a x ≤ b x} eA eB (show x ∈ {x | a x ≤ b x} from h)]
      exact Or.inl (heAA (by
        rcases hx.1.1 with h' | h'
        · exact h'
        · exact absurd h (not_le.2 h')))
    · rw [Set.piecewise_eq_of_notMem {x | a x ≤ b x} eA eB (show x ∉ {x | a x ≤ b x} from h)]
      exact Or.inr (heBB (by
        rcases hx.1.2 with h' | h'
        · exact h'
        · exact absurd h' (not_lt.2 (le_of_lt (not_le.1 h)))))
  · intro x hx
    by_cases hxA : x ∈ A
    · have h : a x ≤ b x := by
        rw [show a x = 0 from infDist_zero_of_mem hxA]; exact infDist_nonneg
      rw [Set.piecewise_eq_of_mem {x | a x ≤ b x} eA eB (show x ∈ {x | a x ≤ b x} from h)]
      exact heAid x hxA
    · have hxB : x ∈ B := hx.resolve_left hxA
      have h : ¬ a x ≤ b x := by
        rw [show b x = 0 from infDist_zero_of_mem hxB, not_le]
        exact (hAcl.notMem_iff_infDist_pos hAne).1 hxA
      rw [Set.piecewise_eq_of_notMem {x | a x ≤ b x} eA eB (show x ∉ {x | a x ≤ b x} from h)]
      exact heBid x hxB

theorem isNR_finite_union {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : ∀ n : ℕ, ∀ S : Finset (Set E), S.card ≤ n →
      (∀ C ∈ S, Convex ℝ C ∧ IsCompact C) → IsNR (⋃ C ∈ S, C) := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hS)]
    simpa using (isNR_empty : IsNR (∅ : Set E))
  | succ n ih =>
    intro S hS hSc
    rcases S.eq_empty_or_nonempty with rfl | ⟨C, hC⟩
    · exact ih ∅ (by simp) (by simp)
    have hS' : (S.erase C).card ≤ n := by rw [Finset.card_erase_of_mem hC]; omega
    have hS'c : ∀ C' ∈ S.erase C, Convex ℝ C' ∧ IsCompact C' := fun C' h =>
      hSc C' (Finset.mem_of_mem_erase h)
    have hunion : (⋃ C' ∈ S, C') = C ∪ ⋃ C' ∈ S.erase C, C' := by
      ext x
      simp only [mem_iUnion, mem_union, Finset.mem_erase, exists_prop]
      constructor
      · rintro ⟨C', hC', hx⟩
        by_cases h : C' = C
        · left; rw [← h]; exact hx
        · right; exact ⟨C', ⟨h, hC'⟩, hx⟩
      · rintro (hx | ⟨C', ⟨_, hC'⟩, hx⟩)
        · exact ⟨C, hC, hx⟩
        · exact ⟨C', hC', hx⟩
    have hinter : C ∩ (⋃ C' ∈ S.erase C, C') =
        ⋃ C'' ∈ (S.erase C).image (fun C' => C ∩ C'), C'' := by
      ext x
      simp only [mem_inter_iff, mem_iUnion, exists_prop, Finset.mem_image]
      constructor
      · rintro ⟨hxC, C', hC', hx⟩
        exact ⟨C ∩ C', ⟨C', hC', rfl⟩, hxC, hx⟩
      · rintro ⟨_, ⟨C', hC', rfl⟩, hxC, hx⟩
        exact ⟨hxC, C', hC', hx⟩
    rw [hunion]
    refine isNR_union (hSc C hC).2 ((S.erase C).isCompact_biUnion fun C' h => (hS'c C' h).2)
      (isNR_convex (hSc C hC).1 (hSc C hC).2) (ih _ hS' hS'c) ?_
    rw [hinter]
    refine ih _ (Finset.card_image_le.trans hS') ?_
    intro C'' hC''
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.1 hC''
    exact ⟨(hSc C hC).1.inter (hS'c C' hC').1, (hSc C hC).2.inter_right (hS'c C' hC').2.isClosed⟩

theorem enr_of_geom {m : ℕ} (Q : Set (EuclideanSpace ℝ (Fin m))) (hQ : IsGeometricPolyhedron Q) :
    ∃ U, IsOpen U ∧ Q ⊆ U ∧ ∃ r : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContinuousOn r U ∧ MapsTo r U Q ∧ ∀ q ∈ Q, r q = q := by
  obtain ⟨S, hS, rfl⟩ := hQ
  exact isNR_finite_union S.card S le_rfl fun C hC => by
    obtain ⟨s, -, rfl⟩ := hS C hC
    exact ⟨convex_convexHull ℝ _, Set.Finite.isCompact_convexHull (𝕜 := ℝ) s.finite_toSet⟩

theorem retract_of_enr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (Q : Set V)
    (hQ : IsCompact Q) (hc : IsContractible Q) (U : Set V) (hU : IsOpen U) (hQU : Q ⊆ U)
    (r : V → V) (hr : ContinuousOn r U) (hrQ : MapsTo r U Q) (hrid : ∀ q ∈ Q, r q = q) :
    ∃ R : V → V, Continuous R ∧ (∀ x, R x ∈ Q) ∧ ∀ q ∈ Q, R q = q := by
  classical
  obtain ⟨z₀, H, h0, h1⟩ := hc
  obtain ⟨ε, hε, hεU⟩ := hQ.exists_cthickening_subset_open hU hQU
  have hQne : Q.Nonempty := ⟨z₀.1, z₀.2⟩
  let r' : V → Q := fun x => if h : x ∈ U then ⟨r x, hrQ h⟩ else z₀
  have hr' : ContinuousOn r' U := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine hr.congr fun x hx => ?_
    simp [r', hx]
  let τ : V → I := fun x => Set.projIcc 0 1 zero_le_one (infDist x Q / ε)
  have hτ : Continuous τ := continuous_projIcc.comp ((continuous_infDist_pt Q).div_const ε)
  have hle : {x | infDist x Q ≤ ε} ⊆ U := by
    intro x hx
    obtain ⟨q, hq, hdq⟩ := hQ.exists_infDist_eq_dist hQne x
    exact hεU (mem_cthickening_of_dist_le x q ε Q hq (hdq ▸ hx))
  refine ⟨fun x => if infDist x Q ≤ ε then ((H (τ x, r' x) : Q) : V) else (z₀ : V), ?_, ?_, ?_⟩
  · refine continuous_if_le (continuous_infDist_pt Q) continuous_const ?_ continuousOn_const ?_
    · have : ContinuousOn (fun x => (τ x, r' x)) {x | infDist x Q ≤ ε} :=
        hτ.continuousOn.prodMk (hr'.mono hle)
      exact continuous_subtype_val.comp_continuousOn (H.continuous.comp_continuousOn this)
    · intro x hx
      have : τ x = 1 := by
        simp only [τ, hx, div_self hε.ne']
        exact Set.projIcc_right _
      simp [this, h1]
  · intro x
    dsimp only
    split_ifs
    · exact (H _).2
    · exact z₀.2
  · intro q hq
    have hd : infDist q Q = 0 := infDist_zero_of_mem hq
    have hτq : τ q = 0 := by
      simp only [τ, hd, zero_div]
      exact Set.projIcc_left _
    have hrq : r' q = ⟨q, hq⟩ := by
      simp [r', hQU hq, hrid q hq]
    simp [hd, hε.le, hτq, hrq, h0]

theorem isCompact_of_geom {m : ℕ} (Q : Set (EuclideanSpace ℝ (Fin m)))
    (hQ : IsGeometricPolyhedron Q) : IsCompact Q := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine S.isCompact_biUnion fun C hC => ?_
  obtain ⟨s, -, rfl⟩ := hS C hC
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) s.finite_toSet

theorem emprop_of_geom {m : ℕ} (Q : Set (EuclideanSpace ℝ (Fin m)))
    (hQ : IsGeometricPolyhedron Q) (hc : IsContractible Q) : EMProp Q := by
  have hQc := isCompact_of_geom Q hQ
  obtain ⟨U, hU, hQU, r, hr, hrQ, hrid⟩ := enr_of_geom Q hQ
  obtain ⟨R, hR, hRQ, hRid⟩ := retract_of_enr Q hQc hc U hU hQU r hr hrQ hrid
  exact emprop_of_retract_euclid m Q hQc R hR hRQ hRid

theorem main {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : Set E)
    (hZ : IsPolyhedron Z) (hZc : IsContractible Z) : EMProp Z := by
  obtain ⟨m, Q, hQ, ⟨e⟩⟩ := hZ
  exact EMProp.of_homeomorph e (emprop_of_geom Q hQ (isContractible_of_homeomorph e hZc))

end FPCP

open SocialEquilibrium.Existence in
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZ : IsPolyhedron Z) (hZc : IsContractible Z)
    (φ : Z → Set Z) (hφ : IsSemicontinuous φ) (hφc : ∀ z, IsContractible (φ z)) :
    ∃ z, z ∈ φ z := by
  exact FPCP.main Z hZ hZc φ hφ hφc
