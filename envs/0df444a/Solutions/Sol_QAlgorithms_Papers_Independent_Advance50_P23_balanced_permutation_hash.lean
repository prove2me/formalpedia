-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P23.balanced_permutation_hash
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:00:01.408592+00:00
-- url     : https://prove2.me/submissions/3c67810c-fcc1-4bba-9ce9-934fb47031ed

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

open scoped BigOperators
open QAlgorithms.Papers.Independent.Advance50.P23
open QAlgorithms.Papers.Independent.Information100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

theorem s110_bph_sym {A D : Type} [Fintype A] (f : A → D) (a b b' : A) (hb : b ≠ a) (hb' : b' ≠ a) :
    (∑ g : Equiv.Perm A, if f (g a) = f (g b) then (1:ℝ) else 0) =
      ∑ g : Equiv.Perm A, if f (g a) = f (g b') then (1:ℝ) else 0 := by
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap b b')) _ _ (fun g => ?_)
  have h1 : Equiv.swap b b' a = a := Equiv.swap_apply_of_ne_of_ne hb.symm hb'.symm
  have h2 : Equiv.swap b b' b' = b := Equiv.swap_apply_right b b'
  simp only [Equiv.coe_mulRight, Equiv.Perm.coe_mul, Function.comp_apply, h1, h2]

theorem s110_bph_row {A D : Type} [Fintype A] [Fintype D] (f : A → D) (hbal : hayashiBalanced f)
    (g : Equiv.Perm A) (a : A) :
    (∑ b, if f (g a) = f (g b) then (1:ℝ) else 0) = (Fintype.card A : ℝ) / Fintype.card D := by
  have hD : (Fintype.card D : ℝ) ≠ 0 := by
    have := hbal (f a)
    have hA : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a⟩
    intro h; rw [Nat.cast_eq_zero] at h; rw [h, mul_zero] at this; omega
  rw [eq_div_iff hD]
  rw [show (∑ b, if f (g a) = f (g b) then (1:ℝ) else 0) = ∑ y, if f (g a) = f y then (1:ℝ) else 0 from
    Equiv.sum_comp g (fun y => if f (g a) = f y then (1:ℝ) else 0)]
  rw [Finset.sum_boole]
  have := hbal (f (g a))
  rw [← this]; push_cast
  congr 3
  ext y; simp [eq_comm]

theorem solution {A : Type} [Fintype A] {D : Type} [Fintype D] [Nonempty D] [Nonempty A]
    (f : A → D) (hbalanced : hayashiBalanced f) :
    Universal2 (uniform : Equiv.Perm A → ℝ) (fun g a => f (g a)) := by
  intro a b hab
  set N : A → ℝ := fun b => ∑ g : Equiv.Perm A, if f (g a) = f (g b) then (1:ℝ) else 0 with hN
  set P : ℝ := (Fintype.card (Equiv.Perm A) : ℝ) with hP
  set K : ℝ := (Fintype.card D : ℝ) with hK
  set n : ℝ := (Fintype.card A : ℝ) with hn
  have hP0 : 0 < P := by rw [hP]; exact_mod_cast Fintype.card_pos
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Fintype.card_pos
  have hn2 : 2 ≤ n := by
    rw [hn]
    have : 2 ≤ Fintype.card A := by
      rw [← Finset.card_pair hab]; exact Finset.card_le_univ _
    exact_mod_cast this
  have hlhs : (∑ g : Equiv.Perm A, if f (g a) = f (g b) then (uniform : Equiv.Perm A → ℝ) g else 0)
      = N b * P⁻¹ := by
    rw [hN, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> simp [uniform, hP]
  show (∑ g : Equiv.Perm A, if f (g a) = f (g b) then (uniform : Equiv.Perm A → ℝ) g else 0) ≤ K⁻¹
  rw [hlhs]
  have htot : ∑ b' ∈ Finset.univ.erase a, N b' = P * (n / K - 1) := by
    rw [hN]
    simp only
    rw [Finset.sum_comm]
    have : ∀ g : Equiv.Perm A, (∑ b' ∈ Finset.univ.erase a, if f (g a) = f (g b') then (1:ℝ) else 0)
        = n / K - 1 := by
      intro g
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ a), s110_bph_row f hbalanced g a, if_pos rfl]
    rw [Finset.sum_congr rfl (fun g _ => this g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hconst : ∑ b' ∈ Finset.univ.erase a, N b' = (n - 1) * N b := by
    rw [Finset.sum_congr rfl (fun b' hb' => s110_bph_sym f a b' b (Finset.ne_of_mem_erase hb') hab.symm),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, nsmul_eq_mul]
    rw [hn]; push_cast [Nat.cast_sub (Fintype.card_pos_iff.2 ⟨a⟩)]; ring
  have hKinv : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK1
  have hKpos : 0 < K := by linarith
  have key : (n - 1) * N b = P * (n * K⁻¹ - 1) := by rw [← hconst, htot, div_eq_mul_inv]
  rw [mul_inv_le_iff₀ hP0]
  have h1 : 0 < n - 1 := by linarith
  apply le_of_mul_le_mul_left _ h1
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left hKinv hP0.le]
