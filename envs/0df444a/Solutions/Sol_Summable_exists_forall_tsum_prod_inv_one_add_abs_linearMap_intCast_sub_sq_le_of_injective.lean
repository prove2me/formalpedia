-- Prove2me | solution 1 for Summable.exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6fe6f304-28d8-5e31-8fc9-2d0255a530b3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective

set_option autoImplicit false

namespace LatticeSumAux

noncomputable def hker (m : ℤ) : ℝ := (1 + |(m : ℝ)|)⁻¹ ^ 2

theorem hker_nonneg (m : ℤ) : 0 ≤ hker m := by
  unfold hker; positivity

theorem summable_hker : Summable hker := by
  have h0 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) 1).mpr
      (Real.summable_nat_pow_inv.mpr one_lt_two)
  have hnat : Summable (fun n : ℕ => (1 + (n : ℝ))⁻¹ ^ 2) := by
    refine h0.congr fun n => ?_
    push_cast
    rw [inv_pow, add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun n => ?_
    simp only [hker, Int.cast_natCast, Nat.abs_cast]
  · refine hnat.congr fun n => ?_
    simp only [hker, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]

theorem inv_one_add_abs_sq_le (x : ℝ) :
    (1 + |x|)⁻¹ ^ 2 ≤ 4 * hker ⌊x⌋ := by
  unfold hker
  have hx : 0 < 1 + |x| := by positivity
  have hn : 0 < 1 + |((⌊x⌋ : ℤ) : ℝ)| := by positivity
  have hfl : |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
    rw [abs_le]
    constructor
    · have h1 := Int.sub_one_lt_floor x
      have h2 := neg_abs_le x
      linarith
    · have h1 := Int.floor_le x
      have h2 := le_abs_self x
      linarith
  have key : (1 + |x|)⁻¹ ≤ 2 * (1 + |((⌊x⌋ : ℤ) : ℝ)|)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hn, inv_mul_le_iff₀ hx]
    have ha := abs_nonneg x
    linarith
  have h0 : 0 ≤ (1 + |x|)⁻¹ := inv_nonneg.mpr hx.le
  calc (1 + |x|)⁻¹ ^ 2 = (1 + |x|)⁻¹ * (1 + |x|)⁻¹ := pow_two _
    _ ≤ (2 * (1 + |((⌊x⌋ : ℤ) : ℝ)|)⁻¹) * (2 * (1 + |((⌊x⌋ : ℤ) : ℝ)|)⁻¹) :=
        mul_le_mul key key h0 (by positivity)
    _ = 4 * (1 + |((⌊x⌋ : ℤ) : ℝ)|)⁻¹ ^ 2 := by ring

noncomputable def G {r : ℕ} (n : Fin r → ℤ) : ℝ := ∏ i, hker (n i)

theorem G_nonneg {r : ℕ} (n : Fin r → ℤ) : 0 ≤ G n :=
  Finset.prod_nonneg fun _ _ => hker_nonneg _

theorem sum_G_le {r : ℕ} (T : Finset (Fin r → ℤ)) :
    ∑ n ∈ T, G n ≤ (∑' m, hker m) ^ r := by
  have hS : ∀ s : Finset ℤ, ∑ m ∈ s, hker m ≤ ∑' m, hker m := fun s =>
    summable_hker.sum_le_tsum s (fun m _ => hker_nonneg m)
  let t : Fin r → Finset ℤ := fun i => T.image (fun n => n i)
  have hT : T ⊆ Fintype.piFinset t := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hn
  have h1 : ∑ n ∈ T, G n ≤ ∑ n ∈ Fintype.piFinset t, G n :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun n _ _ => G_nonneg n)
  have h2 : ∑ n ∈ Fintype.piFinset t, G n = ∏ i, ∑ m ∈ t i, hker m := by
    unfold G
    exact (Finset.prod_univ_sum t (fun _ m => hker m)).symm
  have h3 : ∏ i, ∑ m ∈ t i, hker m ≤ ∏ _i : Fin r, ∑' m, hker m :=
    Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun m _ => hker_nonneg m)
      (fun i _ => hS _)
  have h4 : ∏ _i : Fin r, ∑' m, hker m = (∑' m, hker m) ^ r := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ n ∈ T, G n ≤ ∑ n ∈ Fintype.piFinset t, G n := h1
    _ = ∏ i, ∑ m ∈ t i, hker m := h2
    _ ≤ ∏ _i : Fin r, ∑' m, hker m := h3
    _ = (∑' m, hker m) ^ r := h4

noncomputable def F {a r : ℕ} (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ)
    (k : Fin a → ℤ) : ℝ :=
  ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2

noncomputable def φ {a r : ℕ} (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ)
    (k : Fin a → ℤ) : Fin r → ℤ :=
  fun i => ⌊A (fun j => (k j : ℝ)) i - t i⌋

theorem F_nonneg {a r : ℕ} (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ)
    (k : Fin a → ℤ) : 0 ≤ F A t k :=
  Finset.prod_nonneg fun i _ => by positivity

theorem F_le {a r : ℕ} (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ)
    (k : Fin a → ℤ) : F A t k ≤ 4 ^ r * G (φ A t k) := by
  unfold F G φ
  calc ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2
      ≤ ∏ i, 4 * hker ⌊A (fun j => (k j : ℝ)) i - t i⌋ :=
        Finset.prod_le_prod (fun i _ => by positivity)
          (fun i _ => inv_one_add_abs_sq_le _)
    _ = 4 ^ r * ∏ i, hker ⌊A (fun j => (k j : ℝ)) i - t i⌋ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_fiber_le {a r : ℕ} (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ)
    (C : NNReal) (hC : AntilipschitzWith C A) (u : Finset (Fin a → ℤ)) (n : Fin r → ℤ) :
    (u.filter (fun k => φ A t k = n)).card ≤ (2 * ⌈(C : ℝ)⌉₊ + 1) ^ a := by
  set R : ℕ := ⌈(C : ℝ)⌉₊ with hR
  have hCR : (C : ℝ) ≤ R := Nat.le_ceil _
  rcases (u.filter (fun k => φ A t k = n)).eq_empty_or_nonempty with he | ⟨k₀, hk₀⟩
  · simp [he]
  have hk₀' : φ A t k₀ = n := (Finset.mem_filter.mp hk₀).2
  have hsub : u.filter (fun k => φ A t k = n) ⊆
      Fintype.piFinset (fun j => Finset.Icc (k₀ j - R) (k₀ j + R)) := by
    intro k hk
    have hk' : φ A t k = n := (Finset.mem_filter.mp hk).2
    have hdA : dist (A (fun j => (k j : ℝ))) (A (fun j => (k₀ j : ℝ))) ≤ 1 := by
      rw [dist_pi_le_iff zero_le_one]
      intro i
      rw [Real.dist_eq]
      have hfl : ⌊A (fun j => (k j : ℝ)) i - t i⌋ = ⌊A (fun j => (k₀ j : ℝ)) i - t i⌋ :=
        congrFun (hk'.trans hk₀'.symm) i
      have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
      rw [sub_sub_sub_cancel_right] at h1
      exact h1.le
    have hdk : dist (fun j => (k j : ℝ)) (fun j => (k₀ j : ℝ)) ≤ R := by
      calc dist (fun j => (k j : ℝ)) (fun j => (k₀ j : ℝ))
          ≤ C * dist (A (fun j => (k j : ℝ))) (A (fun j => (k₀ j : ℝ))) := hC.le_mul_dist _ _
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hdA C.coe_nonneg
        _ ≤ R := by rw [mul_one]; exact hCR
    rw [Fintype.mem_piFinset]
    intro j
    have hj : |(k j : ℝ) - (k₀ j : ℝ)| ≤ R := by
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist (fun j => (k j : ℝ)) (fun j => (k₀ j : ℝ)) j).trans hdk
    have hj' : |k j - k₀ j| ≤ (R : ℤ) := by exact_mod_cast hj
    rw [abs_le] at hj'
    rw [Finset.mem_Icc]
    omega
  calc (u.filter (fun k => φ A t k = n)).card
      ≤ (Fintype.piFinset (fun j => Finset.Icc (k₀ j - R) (k₀ j + R))).card :=
        Finset.card_le_card hsub
    _ = ∏ j, (Finset.Icc (k₀ j - (R : ℤ)) (k₀ j + R)).card := Fintype.card_piFinset _
    _ = ∏ _j : Fin a, (2 * R + 1) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Int.card_Icc]
        omega
    _ = (2 * R + 1) ^ a := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sum_F_le {a r : ℕ} (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ)
    (C : NNReal) (hC : AntilipschitzWith C A) (u : Finset (Fin a → ℤ)) :
    ∑ k ∈ u, F A t k ≤
      4 ^ r * ((((2 * ⌈(C : ℝ)⌉₊ + 1) ^ a : ℕ) : ℝ) * (∑' m, hker m) ^ r) := by
  have h1 : ∑ k ∈ u, F A t k ≤ 4 ^ r * ∑ k ∈ u, G (φ A t k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => F_le A t k
  have h2 : ∑ k ∈ u, G (φ A t k) ≤
      (((2 * ⌈(C : ℝ)⌉₊ + 1) ^ a : ℕ) : ℝ) * ∑ n ∈ u.image (φ A t), G n := by
    rw [Finset.sum_comp, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_fiber_le A t C hC u n) (G_nonneg n)
  have h3 : ∑ n ∈ u.image (φ A t), G n ≤ (∑' m, hker m) ^ r := sum_G_le _
  calc ∑ k ∈ u, F A t k ≤ 4 ^ r * ∑ k ∈ u, G (φ A t k) := h1
    _ ≤ 4 ^ r * ((((2 * ⌈(C : ℝ)⌉₊ + 1) ^ a : ℕ) : ℝ) * ∑ n ∈ u.image (φ A t), G n) := by
        gcongr
    _ ≤ 4 ^ r * ((((2 * ⌈(C : ℝ)⌉₊ + 1) ^ a : ℕ) : ℝ) * (∑' m, hker m) ^ r) := by
        gcongr

end LatticeSumAux

theorem solution
    (a r : ℕ) (A : (Fin a → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hA : Function.Injective A) :
    ∃ K : ℝ, ∀ t : Fin r → ℝ,
      Summable (fun k : Fin a → ℤ => ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2) ∧
      ∑' k : Fin a → ℤ, ∏ i, (1 + |A (fun j => (k j : ℝ)) i - t i|)⁻¹ ^ 2 ≤ K := by
  obtain ⟨C, -, hC⟩ := A.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hA)
  refine ⟨4 ^ r * ((((2 * ⌈(C : ℝ)⌉₊ + 1) ^ a : ℕ) : ℝ) * (∑' m, LatticeSumAux.hker m) ^ r),
    fun t => ?_⟩
  have hb := LatticeSumAux.sum_F_le A t C hC
  have h0 : ∀ k, 0 ≤ LatticeSumAux.F A t k := LatticeSumAux.F_nonneg A t
  exact ⟨summable_of_sum_le (f := LatticeSumAux.F A t) (fun k => h0 k) hb,
    Real.tsum_le_of_sum_le (f := LatticeSumAux.F A t) (fun k => h0 k) hb⟩

end S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective
end P2MW
export P2MW.S_Summable_exists_forall_tsum_prod_inv_one_add_abs_linearMap_intCast_sub_sq_le_of_injective (solution)
