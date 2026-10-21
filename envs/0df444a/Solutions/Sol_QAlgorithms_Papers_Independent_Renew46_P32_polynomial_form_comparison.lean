-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.polynomial_form_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:22:54.9215+00:00
-- url     : https://prove2.me/submissions/eb5c0078-d440-4ca4-81c9-93f0a6045247

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

universe u v
open Set Filter Topology

section G66B
variable {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]

theorem g66b_lin_succ (q : A → B) (x : A) (k : ℕ) (h : Fin (k + 1) → A) :
    linearization q x (k + 1) h =
      linearization (fun y => q (y + h 0) - q y) x k (Fin.tail h) := rfl

theorem g66b_lin_sum (k : ℕ) : ∀ (q : A → B) (x : A) (h : Fin k → A),
    linearization q x k h = ∑ ε : Fin k → Bool,
      (∏ j, (if ε j then (1 : ℤ) else -1)) • q (x + ∑ j, if ε j then h j else 0) := by
  induction k with
  | zero => intro q x h; simp; rfl
  | succ k ih =>
    intro q x h
    rw [g66b_lin_succ, ih, ← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.consEquiv, Fin.tail]
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [smul_sub, add_comm (h 0), add_assoc]
theorem g66b_coef (k : ℕ) (r : Fin k → Fin k) :
    ∑ ε : Fin k → Bool, (∏ j, (if ε j then (1 : ℤ) else -1)) *
      (if ∀ i, ε (r i) = true then 1 else 0) = if Function.Surjective r then 1 else 0 := by
  classical
  let G : Fin k → Bool → ℤ := fun j b => if b then 1 else if j ∈ Set.range r then 0 else -1
  have e1 : ∀ ε : Fin k → Bool, (∏ j, (if ε j then (1 : ℤ) else -1)) *
      (if ∀ i, ε (r i) = true then 1 else 0) = ∏ j, G j (ε j) := by
    intro ε
    have : (if ∀ i, ε (r i) = true then (1 : ℤ) else 0) =
        ∏ j, (if ε j = true ∨ j ∉ Set.range r then (1 : ℤ) else 0) := by
      rw [Finset.prod_boole]
      congr 1
      apply propext
      constructor
      · intro H j _
        by_cases hj : j ∈ Set.range r
        · obtain ⟨i, rfl⟩ := hj; exact Or.inl (H i)
        · exact Or.inr hj
      · intro H i
        rcases H (r i) (Finset.mem_univ _) with h | h
        · exact h
        · exact absurd ⟨i, rfl⟩ h
    rw [this, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [G]
    cases ε j <;> by_cases hj : j ∈ Set.range r <;> simp [hj]
  rw [Finset.sum_congr rfl fun ε _ => e1 ε]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp only [Fintype.sum_bool, G, if_true]
  have : ∀ j, ((1 : ℤ) + if (false = true) then 1 else if j ∈ Set.range r then 0 else -1) =
      if j ∈ Set.range r then 1 else 0 := by
    intro j; by_cases hj : j ∈ Set.range r <;> simp [hj]
  simp only [Bool.false_eq_true, if_false] at this ⊢
  rw [Finset.prod_congr rfl fun j _ => this j, Finset.prod_boole]
  convert rfl using 2
  simp [Function.Surjective, Set.mem_range]

theorem g66b_diag_lin {K : Type u} [CommRing K] {D : Type u} [AddCommGroup D] [Module K D]
    {F : Type u} [AddCommGroup F] [Module K F] (k : ℕ)
    (m : MultilinearMap K (fun _ : Fin k => D) F) (g : Fin k → D) :
    linearization (fun y => m (fun _ => y)) 0 k g =
      ∑ σ : Equiv.Perm (Fin k), m (fun i => g (σ i)) := by
  classical
  rw [g66b_lin_sum]
  simp only [zero_add]
  have e1 : ∀ ε : Fin k → Bool, m (fun _ => ∑ j, if ε j then g j else 0) =
      ∑ r : Fin k → Fin k, (if ∀ i, ε (r i) = true then m (fun i => g (r i)) else 0) := by
    intro ε
    rw [m.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with H
    · congr 1; funext i; simp [H i]
    · push_neg at H
      obtain ⟨i, hi⟩ := H
      exact m.map_coord_zero i (by simp [hi])
  simp_rw [e1, Finset.smul_sum]
  rw [Finset.sum_comm]
  have e2 : ∀ r : Fin k → Fin k, ∑ ε : Fin k → Bool, (∏ j, (if ε j then (1 : ℤ) else -1)) •
      (if ∀ i, ε (r i) = true then m (fun i => g (r i)) else 0) =
      if Function.Surjective r then m (fun i => g (r i)) else 0 := by
    intro r
    have : ∀ ε : Fin k → Bool, (∏ j, (if ε j then (1 : ℤ) else -1)) •
        (if ∀ i, ε (r i) = true then m (fun i => g (r i)) else 0) =
        ((∏ j, (if ε j then (1 : ℤ) else -1)) * (if ∀ i, ε (r i) = true then 1 else 0)) •
          m (fun i => g (r i)) := by
      intro ε; split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.sum_smul, g66b_coef]
    split_ifs <;> simp
  simp_rw [e2]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun σ _ => ⇑σ) (fun σ _ => by simpa using σ.surjective)
    (fun σ _ τ _ h => Equiv.coe_fn_injective h) (fun r hr => ?_) (fun σ _ => rfl)
  have hs : Function.Surjective r := (Finset.mem_filter.mp hr).2
  have hb : Function.Bijective r := ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  exact ⟨Equiv.ofBijective r hb, Finset.mem_univ _, rfl⟩
end G66B

theorem g66b_lin_comp {D : Type u} [AddCommGroup D] {E : Type u} [AddCommGroup E]
    {B : Type u} [AddCommGroup B] (φ : D →+ E) (k : ℕ) : ∀ (q : E → B) (x : D) (g : Fin k → D),
    linearization (fun y => q (φ y)) x k g = linearization q (φ x) k (fun i => φ (g i)) := by
  induction k with
  | zero => intro q x g; rfl
  | succ k ih =>
    intro q x g
    rw [g66b_lin_succ, g66b_lin_succ]
    have : (fun y => q (φ (y + g 0)) - q (φ y)) = fun y => (fun z => q (z + φ (g 0)) - q z) (φ y) := by
      funext y; simp [map_add]
    rw [this]
    exact ih (fun z => q (z + φ (g 0)) - q z) x (Fin.tail g)

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

theorem g66b_poly_form (q : E → F) (k : ℕ) (hP : IsHomogeneousPolynomial (K := K) k q) :
    IsHomogeneousForm (K := K) k q := by
  classical
  let φ : (E →₀ K) →ₗ[K] E := Finsupp.linearCombination K id
  have hsurj : Function.Surjective φ := fun y => ⟨Finsupp.single y 1, by simp [φ]⟩
  obtain ⟨m, hm⟩ := hP (E →₀ K) φ hsurj
  let s := Function.surjInv hsurj
  have hs : ∀ y, φ (s y) = y := Function.surjInv_eq hsurj
  refine ⟨?_, ?_⟩
  · intro t y
    rw [← hs y, ← map_smul, hm, hm]
    have := m.map_smul_univ (fun _ => t) (fun _ => s y)
    simpa [Finset.prod_const] using this
  · let M : MultilinearMap K (fun _ : Fin k => (E →₀ K)) F :=
      ∑ σ : Equiv.Perm (Fin k), m.domDomCongr σ
    have hrep : ∀ g : Fin k → (E →₀ K), linearization q 0 k (fun i => φ (g i)) = M g := by
      intro g
      have h0 : (0 : E) = φ.toAddMonoidHom 0 := by simp
      rw [h0, show (fun i => φ (g i)) = fun i => φ.toAddMonoidHom (g i) from rfl,
        ← g66b_lin_comp]
      have : (fun y => q (φ.toAddMonoidHom y)) = fun y => m (fun _ => y) := by
        funext y; exact hm y
      rw [this, g66b_diag_lin]
      simp [M, MultilinearMap.sum_apply, MultilinearMap.domDomCongr_apply]
    refine ⟨{ toFun := fun h => linearization q 0 k h,
              map_update_add' := ?_, map_update_smul' := ?_ }, fun h => rfl⟩
    · intro _ h i a b
      have key : ∀ c' : E →₀ K, linearization q 0 k (Function.update h i (φ c')) =
          M (Function.update (fun j => s (h j)) i c') := by
        intro c'
        rw [← hrep]
        congr 1; funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, hs]
      rw [← hs a, ← hs b, ← map_add, key, key, key, M.map_update_add]
    · intro _ h i c a
      have key : ∀ c' : E →₀ K, linearization q 0 k (Function.update h i (φ c')) =
          M (Function.update (fun j => s (h j)) i c') := by
        intro c'
        rw [← hrep]
        congr 1; funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, hs]
      rw [← hs a, ← map_smul, key, key, M.map_update_smul]

theorem solution (q : E → F) (k : ℕ) :
    (Module.Free K E →
      (IsHomogeneousPolynomial (K := K) k q ↔
        ∃ m : MultilinearMap K (fun _ : Fin k => E) F,
          ∀ x : E, q x = m (fun _ => x))) ∧
    (IsHomogeneousPolynomial (K := K) k q → IsHomogeneousForm (K := K) k q) ∧
    ((k = 0 ∨ k = 1) →
      (IsHomogeneousForm (K := K) k q ↔ IsHomogeneousPolynomial (K := K) k q)) := by
  refine ⟨fun hfree => ⟨fun hP => ?_, ?_⟩, g66b_poly_form q k, ?_⟩
  · obtain ⟨m, hm⟩ := hP E LinearMap.id Function.surjective_id
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩ D _ _ _ phi _
    exact ⟨m.compLinearMap (fun _ => phi), fun x => by simp [hm]⟩
  · rintro (rfl | rfl)
    · refine ⟨?_, g66b_poly_form q 0⟩
      rintro ⟨hhom, -⟩ D _ _ _ phi _
      refine ⟨MultilinearMap.constOfIsEmpty K _ (q 0), fun x => ?_⟩
      have := hhom 0 (phi x)
      simp at this
      simpa using this.symm
    · refine ⟨?_, g66b_poly_form q 1⟩
      rintro ⟨hhom, m, hm⟩ D _ _ _ phi _
      have q0 : q 0 = 0 := by simpa using hhom 0 0
      refine ⟨m.compLinearMap (fun _ => phi), fun x => ?_⟩
      rw [MultilinearMap.compLinearMap_apply, hm]
      show q (phi x) = q (0 + phi x) - q 0
      simp [q0]

end AlgebraicDefinitions
