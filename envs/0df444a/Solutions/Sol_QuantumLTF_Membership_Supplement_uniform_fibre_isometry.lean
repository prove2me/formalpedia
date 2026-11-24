-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.uniform_fibre_isometry
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T23:23:20.263279+00:00
-- url     : https://prove2.me/submissions/73d8b409-8a17-41a6-b7b1-226484288922

import Mathlib

set_option autoImplicit false

open Classical in
noncomputable def section5_fibre_lift {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) : EuclideanSpace ℂ Y →ₗ[ℂ] EuclideanSpace ℂ X where
  toFun ψ := WithLp.toLp 2 fun x => ψ (f x)/(Real.sqrt (Nat.card {x' : X // f x' = f x}):ℂ)
  map_add' ψ φ := by
    ext x
    change (ψ (f x)+φ (f x))/_ = ψ (f x)/_+φ (f x)/_
    rw [add_div]
  map_smul' c ψ := by
    ext x
    change (c*ψ (f x))/_ = c*(ψ (f x)/_)
    ring

theorem section5_fibre_lift_norm {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Surjective f) (ψ : EuclideanSpace ℂ Y) :
    ‖section5_fibre_lift f ψ‖ = ‖ψ‖ := by
  classical
  have hcard (y : Y) : (0:ℝ) < Nat.card {x : X // f x = y} := by
    obtain ⟨x,hx⟩ := hf y
    haveI : Nonempty {x : X // f x = y} := ⟨⟨x,hx⟩⟩
    exact_mod_cast (Nat.card_pos : 0 < Nat.card {x : X // f x = y})
  have hsq : ‖section5_fibre_lift f ψ‖^2 = ‖ψ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ x : X, ‖ψ (f x)/(Real.sqrt (Nat.card {x' : X // f x' = f x}):ℂ)‖^2) =
      ∑ y : Y, ‖ψ y‖^2
    rw [← Fintype.sum_fiberwise f]
    apply Finset.sum_congr rfl
    intro y hy
    have hsum : (∑ x : {x : X // f x = y},
        ‖ψ (f x)/(Real.sqrt (Nat.card {x' : X // f x' = f x}):ℂ)‖^2) =
        ∑ _x : {x : X // f x = y},
          ‖ψ y/(Real.sqrt (Nat.card {x' : X // f x' = y}):ℂ)‖^2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [x.property]
    rw [hsum]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      div_pow, Real.sq_sqrt (hcard y).le, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (hcard y).ne'
  nlinarith [norm_nonneg (section5_fibre_lift f ψ), norm_nonneg ψ]

noncomputable def section5_fibre_isometry {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Surjective f) : EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ X :=
  { section5_fibre_lift f with norm_map' := section5_fibre_lift_norm f hf }

theorem section5_fibre_lift_constant_state {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Surjective f) (g : X → ℂ)
    (hg : ∀ x x', f x = f x' → g x = g x') :
    ∃ ψ : EuclideanSpace ℂ Y,
      section5_fibre_isometry f hf ψ = WithLp.toLp 2 g := by
  classical
  let pick := fun y : Y => (hf y).choose
  have hpick (y : Y) : f (pick y) = y := (hf y).choose_spec
  let ψ : EuclideanSpace ℂ Y := WithLp.toLp 2 fun y =>
    (Real.sqrt (Nat.card {x : X // f x = y}) : ℂ) * g (pick y)
  refine ⟨ψ,?_⟩
  ext x
  have hcard : (0:ℝ) < Nat.card {x' : X // f x' = f x} := by
    haveI : Nonempty {x' : X // f x' = f x} := ⟨⟨x,rfl⟩⟩
    exact_mod_cast (Nat.card_pos : 0 < Nat.card {x' : X // f x' = f x})
  have hs : (Real.sqrt (Nat.card {x' : X // f x' = f x}) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hcard).ne'
  change ((Real.sqrt (Nat.card {x' : X // f x' = f x}) : ℂ) * g (pick (f x)))/
    (Real.sqrt (Nat.card {x' : X // f x' = f x}) : ℂ) = g x
  rw [mul_div_cancel_left₀ _ hs]
  exact hg _ _ (hpick (f x))

theorem section5_product_by_occupation {n k : ℕ} (w : Fin n → ℂ) (x : Fin k → Fin n) :
    ∏ j : Fin k, w (x j) = ∏ i : Fin n, (w i)^(Nat.card {j : Fin k // x j = i}) := by
  classical
  rw [← Fintype.prod_fiberwise x (fun j : Fin k => w (x j))]
  apply Finset.prod_congr rfl
  intro i hi
  calc
    _ = ∏ j : {j : Fin k // x j = i}, w i := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [j.property]
    _ = _ := by simp [Nat.card_eq_fintype_card]

noncomputable def section5_occupation {n k : ℕ} (x : Fin k → Fin n) (i : Fin n) : ℕ :=
  Nat.card {j : Fin k // x j = i}

def section5_Occupation (n k : ℕ) := Set.range (@section5_occupation n k)

noncomputable def section5_occupation_label {n k : ℕ} (x : Fin k → Fin n) : section5_Occupation n k :=
  ⟨section5_occupation x,⟨x,rfl⟩⟩

theorem section5_occupation_label_surjective {n k : ℕ} :
    Function.Surjective (@section5_occupation_label n k) := by
  rintro ⟨a,x,hx⟩
  exact ⟨x,Subtype.ext hx⟩

noncomputable instance section5_occupation_fintype (n k : ℕ) : Fintype (section5_Occupation n k) := by
  classical
  exact Fintype.ofSurjective section5_occupation_label section5_occupation_label_surjective

noncomputable def section5_occupation_isometry (n k : ℕ) :
    EuclideanSpace ℂ (section5_Occupation n k) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k → Fin n) :=
  section5_fibre_isometry section5_occupation_label section5_occupation_label_surjective

open Classical in
noncomputable def section5_occupation_state {n k : ℕ} (w : Fin n → ℂ) :
    EuclideanSpace ℂ (section5_Occupation n k) := WithLp.toLp 2 fun a =>
  (Real.sqrt (Nat.card {x : Fin k → Fin n // section5_occupation_label x = a}):ℂ) *
    ∏ i : Fin n, (w i)^(a.val i)

theorem section5_occupation_isometry_tensor {n k : ℕ} (w : Fin n → ℂ) :
    section5_occupation_isometry n k (section5_occupation_state w) =
      WithLp.toLp 2 (fun x : Fin k → Fin n => ∏ j : Fin k, w (x j)) := by
  classical
  ext x
  have hc : (0:ℝ) < Nat.card {x' : Fin k → Fin n //
      section5_occupation_label x' = section5_occupation_label x} := by
    haveI : Nonempty {x' : Fin k → Fin n //
      section5_occupation_label x' = section5_occupation_label x} := ⟨⟨x,rfl⟩⟩
    exact_mod_cast (Nat.card_pos : 0 < Nat.card {x' : Fin k → Fin n //
      section5_occupation_label x' = section5_occupation_label x})
  have hs : (Real.sqrt (Nat.card {x' : Fin k → Fin n //
      section5_occupation_label x' = section5_occupation_label x}):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  change ((Real.sqrt (Nat.card {x' : Fin k → Fin n //
      section5_occupation_label x' = section5_occupation_label x}):ℂ) *
    (∏ i : Fin n, (w i)^(section5_occupation x i)))/
    (Real.sqrt (Nat.card {x' : Fin k → Fin n //
      section5_occupation_label x' = section5_occupation_label x}):ℂ) = _
  rw [mul_div_cancel_left₀ _ hs]
  simpa only [section5_occupation, Nat.card_eq_fintype_card] using (section5_product_by_occupation w x).symm

theorem section5_tensor_amplitude_norm {n k : ℕ} (w : Fin n → ℂ)
    (hw : ∑ i : Fin n, ‖w i‖^2 = 1) :
    ‖(WithLp.toLp 2 (fun x : Fin k → Fin n => ∏ j : Fin k, w (x j)) :
      EuclideanSpace ℂ (Fin k → Fin n))‖ = 1 := by
  have hsq : ‖(WithLp.toLp 2 (fun x : Fin k → Fin n => ∏ j : Fin k, w (x j)) :
      EuclideanSpace ℂ (Fin k → Fin n))‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun (_ : Fin k) (i : Fin n) => ‖w i‖^2)]
    simp [hw]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun x : Fin k → Fin n => ∏ j : Fin k, w (x j)) :
    EuclideanSpace ℂ (Fin k → Fin n))]

theorem section5_occupation_state_norm {n k : ℕ} (w : Fin n → ℂ)
    (hw : ∑ i : Fin n, ‖w i‖^2 = 1) : ‖@section5_occupation_state n k w‖ = 1 := by
  rw [← (section5_occupation_isometry n k).norm_map, section5_occupation_isometry_tensor]
  exact section5_tensor_amplitude_norm w hw

theorem solution {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Surjective f) :
    ∃ J : EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ X,
      (∀ (ψ : EuclideanSpace ℂ Y) (x : X),
        J ψ x = ψ (f x)/(Real.sqrt (Nat.card {x' : X // f x' = f x}):ℂ)) ∧
      ∀ g : X → ℂ, (∀ x x', f x = f x' → g x = g x') →
        ∃ ψ : EuclideanSpace ℂ Y, J ψ = WithLp.toLp 2 g := by
  refine ⟨section5_fibre_isometry f hf,fun _ _ => rfl,?_⟩
  exact section5_fibre_lift_constant_state f hf
