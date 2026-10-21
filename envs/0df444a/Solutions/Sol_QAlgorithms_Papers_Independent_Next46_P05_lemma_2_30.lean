-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P05.lemma_2_30
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:29:18.008661+00:00
-- url     : https://prove2.me/submissions/23fea0dc-8d21-486d-aaf6-c3a936767bbe

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P05
open QAlgorithms.Papers.Independent.Next46.P05

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Frontier30.P26
  (bracketSpan innerWord Invariant ClosedCone GeneratingInvariantCone CompactlyEmbedded)

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedSpace


section G62E
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem g62e_B (J : EuclideanJordan V) (x z y : V) :
    J.product z (J.product (J.product x x) y) + (2:ℝ) • J.product x (J.product (J.product x z) y)
      = (2:ℝ) • J.product (J.product x z) (J.product x y)
        + J.product (J.product x x) (J.product z y) := by
  have h1 := J.jordan (x + z) y
  have h2 := J.jordan (x - z) y
  have h3 := J.jordan z y
  have h4 := J.jordan x y
  have hc := J.comm z x
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hc] at h1 h2
  linear_combination (norm := module) (1/2 : ℝ) • h1 - (1/2 : ℝ) • h2 - h3

theorem g62e_cubic (J : EuclideanJordan V) (e : V) (he : J.product e e = e) (z : V) :
    (2:ℝ) • J.product e (J.product e (J.product e z)) - (3:ℝ) • J.product e (J.product e z)
      + J.product e z = 0 := by
  have h := g62e_B J e z e
  simp only [he, J.comm z e, J.comm (J.product e z) e] at h
  linear_combination (norm := module) h

theorem g62e_sq_zero (J : EuclideanJordan V) (e a : V) (he : J.product e e = e)
    (ha : J.product e a = 0) : J.product e (J.product a a) = 0 := by
  have h := g62e_B J e a a
  simp only [he, ha, map_zero, LinearMap.zero_apply, smul_zero, add_zero, zero_add] at h
  exact h.symm

theorem g62e_nonneg (J : EuclideanJordan V) (u : V) : 0 ≤ J.scalar u u := by
  by_cases h : u = 0
  · simp [h]
  · exact (J.scalar_pos u h).le

theorem g62e_pos (J : EuclideanJordan V) (e : V) (he : J.product e e = e) (x : V) :
    0 ≤ J.scalar x (J.product e x) ∧
      (J.scalar x (J.product e x) = 0 → J.product e x = 0) := by
  set x1 := J.product e x with hx1
  set x2 := J.product e x1 with hx2
  set x3 := J.product e x2 with hx3
  set x4 := J.product e x3 with hx4
  have c1 : (2:ℝ) • x3 - (3:ℝ) • x2 + x1 = 0 := g62e_cubic J e he x
  have c2 : (2:ℝ) • x4 - (3:ℝ) • x3 + x2 = 0 := g62e_cubic J e he x1
  have k1 : J.scalar x ((2:ℝ) • x3 - (3:ℝ) • x2 + x1) = 0 := by rw [c1]; simp
  have k2 : J.scalar x ((2:ℝ) • x4 - (3:ℝ) • x3 + x2) = 0 := by rw [c2]; simp
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at k1 k2
  have e22 : J.scalar x2 x2 = J.scalar x x4 :=
    (J.scalar_assoc e x1 x2).trans (J.scalar_assoc e x x3)
  have e21 : J.scalar x2 x1 = J.scalar x x3 :=
    (J.scalar_assoc e x1 x1).trans (J.scalar_assoc e x x2)
  have e12 : J.scalar x1 x2 = J.scalar x x3 := (J.scalar_symm _ _).trans e21
  have e11 : J.scalar x1 x1 = J.scalar x x2 := J.scalar_assoc e x x1
  set u := (2:ℝ) • x2 - x1 with hu
  set v := (4:ℝ) • x1 - (4:ℝ) • x2 with hv
  have hid : J.scalar x x1 = J.scalar u u + (1/2) * J.scalar v v := by
    simp only [hu, hv, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, e22, e21, e12, e11]
    linarith
  have hu0 := g62e_nonneg J u
  have hv0 := g62e_nonneg J v
  refine ⟨by rw [hid]; positivity, fun h0 => ?_⟩
  have huu : J.scalar u u = 0 := by linarith
  have hvv : J.scalar v v = 0 := by linarith
  have hu' : u = 0 := by
    by_contra hne; have := J.scalar_pos u hne; linarith
  have hv' : v = 0 := by
    by_contra hne; have := J.scalar_pos v hne; linarith
  have : x1 = u + (1/2:ℝ) • v := by simp only [hu, hv]; module
  rw [this, hu', hv']; simp

theorem g62e_orth (J : EuclideanJordan V) (e u v : V) (α β : ℝ)
    (hu : J.product e u = α • u) (hv : J.product e v = β • v) (hne : α ≠ β) :
    J.scalar u v = 0 := by
  have h := J.scalar_assoc e u v
  rw [hu, hv, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h
  have : (α - β) * J.scalar u v = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hne
  · exact h1

end G62E

section JordanStatements

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Lemma 2.30, PDF p. 14. Both halves survive at the endpoint indices. -/
theorem solution (J : EuclideanJordan V) {r : ℕ} (c : Fin r → V)
    (hf : JordanFrame J c) (y : V) (hy : y ∈ squares J)
    (lam : Fin r → ℝ) (off : Fin r → Fin r → V)
    (hp : ∀ i j, i < j → off i j ∈ peirce J (c i) (1 / 2) ⊓ peirce J (c j) (1 / 2))
    (hd : y = (∑ i, lam i • c i) + ∑ i, ∑ j, if i < j then off i j else 0)
    (i : Fin r) (hz : lam i = 0) :
    (∀ l : Fin r, l < i → off l i = 0) ∧ (∀ j : Fin r, i < j → off i j = 0) := by
  obtain ⟨hprim, horth, hsum, -⟩ := hf
  have hidem : ∀ m, J.product (c m) (c m) = c m := fun m => (hprim m).2.2.1
  have hL : ∀ z, ∑ m, J.product (c m) z = z := by
    intro z
    have := J.unit_mul z
    rw [← hsum, map_sum, LinearMap.sum_apply] at this
    exact this
  have hEc : ∀ m j, J.product (c m) (c j) = (if m = j then (1:ℝ) else 0) • c j := by
    intro m j
    split_ifs with h
    · subst h; simp [hidem]
    · simp [horth m j h]
  have hEo : ∀ j k, j < k → ∀ m, J.product (c m) (off j k) =
      (if m = j ∨ m = k then (1/2:ℝ) else 0) • off j k := by
    intro j k hjk m
    have hpj : J.product (c j) (off j k) = (1/2:ℝ) • off j k :=
      Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 (hp j k hjk)).1
    have hpk : J.product (c k) (off j k) = (1/2:ℝ) • off j k :=
      Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 (hp j k hjk)).2
    by_cases hm : m = j ∨ m = k
    · rw [if_pos hm]
      rcases hm with rfl | rfl
      · exact hpj
      · exact hpk
    · rw [if_neg hm, zero_smul]
      push_neg at hm
      set z := off j k
      have hjk' : j ≠ k := ne_of_lt hjk
      let g : Fin r → ℝ := fun m => J.scalar z (J.product (c m) z)
      have hg0 : ∀ m, 0 ≤ g m := fun m => (g62e_pos J (c m) (hidem m) z).1
      have hgs : ∑ m, g m = J.scalar z z := by
        simp only [g, ← map_sum, hL]
      have hgj : g j = (1/2) * J.scalar z z := by simp [g, hpj]
      have hgk : g k = (1/2) * J.scalar z z := by simp [g, hpk]
      have hsub : ({m, j, k} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hg0 x)
      rw [Finset.sum_insert (by simp [hm.1, hm.2]), Finset.sum_insert (by simp [hjk']),
        Finset.sum_singleton, hgs, hgj, hgk] at hle
      have : g m = 0 := le_antisymm (by linarith) (hg0 m)
      exact (g62e_pos J (c m) (hidem m) z).2 this
  -- S y (c i) = 0
  have hyc : J.scalar y (c i) = 0 := by
    rw [hd]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    have hci : J.product (c i) (c i) = (1:ℝ) • c i := by rw [hidem, one_smul]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro j _
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with hjk
      · refine g62e_orth J (c i) _ _ _ 1 (hEo j k hjk i) hci ?_
        split_ifs <;> norm_num
      · simp
    · intro j _
      by_cases hji : j = i
      · subst hji; simp [hz]
      · rw [g62e_orth J (c i) _ _ 0 1 (by rw [hEc i j, if_neg (Ne.symm hji)]) hci (by norm_num),
          mul_zero]
  obtain ⟨x, rfl⟩ := hy
  have hx : J.product (c i) x = 0 := by
    apply (g62e_pos J (c i) (hidem i) x).2
    rw [← J.comm x (c i), ← J.scalar_assoc]
    exact hyc
  have hy0 : J.product (c i) (J.product x x) = 0 := g62e_sq_zero J (c i) x (hidem i) hx
  set y := J.product x x with hydef
  have key : ∀ a b, a < b → (i = a ∨ i = b) → off a b = 0 := by
    intro a b hab hi
    set w := off a b with hw
    have hwi : J.product (c i) w = (1/2 : ℝ) • w := by
      rw [hEo a b hab i, if_pos hi]
    have hyw : J.scalar y w = 0 := by
      have h := J.scalar_assoc (c i) y w
      rw [hy0, hwi, map_smul, smul_eq_mul, map_zero, LinearMap.zero_apply] at h
      linarith
    have hoff0 : ∀ j k, j < k → (j ≠ a ∨ k ≠ b) → J.scalar (off j k) w = 0 := by
      intro j k hjk hne
      by_cases hk : k = a ∨ k = b
      · by_cases hj : j = a ∨ j = b
        · exfalso
          rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
          · exact absurd hjk (lt_irrefl _)
          · simp at hne
          · exact absurd (hjk.trans hab) (lt_irrefl _)
          · exact absurd hjk (lt_irrefl _)
        · refine g62e_orth J (c j) _ _ (1/2) 0 (by rw [hEo j k hjk j, if_pos (Or.inl rfl)])
            (by rw [hEo a b hab j, if_neg hj, zero_smul]) (by norm_num)
      · refine g62e_orth J (c k) _ _ (1/2) 0 (by rw [hEo j k hjk k, if_pos (Or.inr rfl)])
          (by rw [hEo a b hab k, if_neg hk, zero_smul]) (by norm_num)
    have hcw : ∀ j, J.scalar (c j) w = 0 := by
      intro j
      refine g62e_orth J (c j) _ _ 1 (if j = a ∨ j = b then (1/2:ℝ) else 0)
        (by rw [hEc j j, if_pos rfl]) (hEo a b hab j) ?_
      split_ifs <;> norm_num
    rw [hd] at hyw
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hcw, mul_zero, Finset.sum_const_zero, zero_add] at hyw
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b, if_pos hab] at hyw
    · by_contra hne
      have := J.scalar_pos w hne
      linarith
    · intro k _ hkb
      split_ifs with hak
      · exact hoff0 a k hak (Or.inr hkb)
      · simp
    · simp
    · intro j _ hja
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with hjk
      · exact hoff0 j k hjk (Or.inl hja)
      · simp
    · simp
  exact ⟨fun l hl => key l i hl (Or.inr rfl), fun j hj => key i j hj (Or.inl rfl)⟩

end JordanStatements

end

