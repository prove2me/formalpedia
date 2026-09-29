-- Prove2me | solution 1 for ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a166906c-457f-5a8f-8c02-a09d5326e049

import Mathlib
import Theorems.Thm_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq

set_option autoImplicit false

open Complex Filter DirichletCharacter HurwitzZeta
open scoped Real Topology

noncomputable section

namespace EIS2K3

variable {N : ℕ} [NeZero N]

def f (t : (ZMod N)ˣ) : ℂ := (π : ℂ) ^ 2 / Complex.sin (π * (t : ZMod N).val / N) ^ 2

omit [NeZero N] in
lemma val_pos (hN : 2 ≤ N) (t : (ZMod N)ˣ) : 0 < (t : ZMod N).val := by
  haveI : Fact (1 < N) := ⟨hN⟩
  rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
  exact t.ne_zero

lemma val_div_mem_integerComplement (hN : 2 ≤ N) (t : (ZMod N)ˣ) :
    (((t : ZMod N).val : ℂ) / N) ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hv : ((t : ZMod N).val : ℝ) = (m : ℝ) * N := by
    have h1 : ((m : ℂ)) * (N : ℂ) = ((t : ZMod N).val : ℂ) := by
      rw [hm, div_mul_cancel₀]
      exact_mod_cast (NeZero.ne N)
    exact_mod_cast h1.symm
  have hlt : ((t : ZMod N).val : ℝ) < N := by exact_mod_cast ZMod.val_lt (t : ZMod N)
  have hpos : (0 : ℝ) < (t : ZMod N).val := by exact_mod_cast val_pos hN t
  rw [hv] at hlt hpos
  have hm1 : (m : ℝ) < 1 := by
    by_contra h
    push Not at h
    have : (N : ℝ) ≤ (m : ℝ) * N := by nlinarith
    linarith
  have hm0 : (0 : ℝ) < m := by
    by_contra h
    push Not at h
    have : (m : ℝ) * N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hNpos.le
    linarith
  have h1 : m < 1 := by exact_mod_cast hm1
  have h0 : 0 < m := by exact_mod_cast hm0
  omega

lemma f_eq_tsum (hN : 2 ≤ N) (t : (ZMod N)ˣ) :
    f t = ∑' n : ℤ, 1 / ((((t : ZMod N).val : ℂ) / N) + n) ^ 2 := by
  rw [Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq _ (val_div_mem_integerComplement hN t), f,
    mul_div_assoc]

lemma tsum_eq_two_mul_hurwitzZetaEven (x : ℝ) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 2 = 2 * hurwitzZetaEven (x : UnitAddCircle) 2 := by
  have h := hasSum_int_hurwitzZetaEven x (s := 2) (by norm_num)
  have h2 := h.mul_left 2
  have hterm : ∀ n : ℤ, (2 : ℂ) * (1 / (↑|(n : ℝ) + x| : ℂ) ^ (2 : ℂ) / 2) = 1 / ((x : ℂ) + n) ^ 2 := by
    intro n
    rw [Complex.cpow_two]
    have : ((|(n : ℝ) + x| : ℝ) : ℂ) ^ 2 = ((x : ℂ) + n) ^ 2 := by
      rw [← Complex.ofReal_pow, sq_abs]
      push_cast
      ring
    rw [this]
    ring
  simp_rw [hterm] at h2
  exact h2.tsum_eq

lemma f_eq_hurwitz (hN : 2 ≤ N) (t : (ZMod N)ˣ) :
    f t = 2 * hurwitzZetaEven (ZMod.toAddCircle (t : ZMod N)) 2 := by
  rw [f_eq_tsum hN, ZMod.toAddCircle_apply, ← tsum_eq_two_mul_hurwitzZetaEven]
  push_cast
  rfl

lemma sum_units_eq_sum (χ : DirichletCharacter ℂ N) (g : ZMod N → ℂ) :
    ∑ t : (ZMod N)ˣ, χ (t : ZMod N) * g t = ∑ j : ZMod N, χ j * g j := by
  classical
  have hmap : (Finset.univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩
      = Finset.univ.filter fun j : ZMod N => IsUnit j := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_filter]
    exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
  calc ∑ t : (ZMod N)ˣ, χ (t : ZMod N) * g t
      = ∑ j ∈ (Finset.univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩, χ j * g j := by
        rw [Finset.sum_map]; rfl
    _ = ∑ j ∈ Finset.univ.filter (fun j : ZMod N => IsUnit j), χ j * g j := by rw [hmap]
    _ = ∑ j : ZMod N, χ j * g j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hj
        · rfl
        · rw [MulChar.map_nonunit χ hj, zero_mul]

lemma charsum_eq (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N) (hχ : χ.Even) :
    ∑ t : (ZMod N)ˣ, χ (t : ZMod N) * f t = 2 * (N : ℂ) ^ 2 * DirichletCharacter.LFunction χ 2 := by
  have heven : Function.Even (χ : ZMod N → ℂ) := by
    intro x
    rw [← neg_one_mul, map_mul, hχ, one_mul]
  have hL : DirichletCharacter.LFunction χ 2
      = (N : ℂ) ^ (-(2 : ℂ)) * ∑ j : ZMod N, χ j * hurwitzZetaEven (ZMod.toAddCircle j) 2 :=
    ZMod.LFunction_def_even heven 2
  simp_rw [f_eq_hurwitz hN]
  rw [sum_units_eq_sum χ (fun j => 2 * hurwitzZetaEven (ZMod.toAddCircle j) 2), hL, cpow_neg,
    Complex.cpow_two]
  have hN0 : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  rw [← mul_assoc, mul_inv_cancel_right₀ hN0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma charsum_ne_zero (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N) (hχ : χ.Even) :
    ∑ t : (ZMod N)ˣ, χ (t : ZMod N) * f t ≠ 0 := by
  rw [charsum_eq hN χ hχ]
  refine mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N)))) ?_
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by norm_num)]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ (by norm_num)

def cinv (χ : DirichletCharacter ℂ N) : ℂ := ∑ t : (ZMod N)ˣ, f t * χ ((t⁻¹ : (ZMod N)ˣ) : ZMod N)

lemma cinv_eq (χ : DirichletCharacter ℂ N) : cinv χ = ∑ t : (ZMod N)ˣ, χ⁻¹ (t : ZMod N) * f t := by
  unfold cinv
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, MulChar.inv_apply, Ring.inverse_unit]

lemma cinv_ne_zero (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N) (hχ : χ.Even) : cinv χ ≠ 0 := by
  rw [cinv_eq]
  refine charsum_ne_zero hN χ⁻¹ ?_
  rw [DirichletCharacter.Even, MulChar.inv_apply,
    show (-1 : ZMod N) = ((-1 : (ZMod N)ˣ) : ZMod N) by simp, Ring.inverse_unit]
  simp at hχ ⊢
  exact hχ

theorem main (hN : 2 ≤ N) :
    ∃ h : (ZMod N)ˣ → ℂ, ∀ s : (ZMod N)ˣ,
      ∑ t : (ZMod N)ˣ, f t * h (t * s) = (if s = 1 then 1 else 0) + (if s = -1 then 1 else 0) := by
  classical

  let e : DirichletCharacter ℂ N → ℂ := fun χ => if χ.Even then 2 / cinv χ else 0
  have he : ∀ χ : DirichletCharacter ℂ N, e χ * cinv χ = 1 + χ (-1) := by
    intro χ
    rcases χ.even_or_odd with hχ | hχ
    · simp only [e, if_pos hχ, div_mul_cancel₀ _ (cinv_ne_zero hN χ hχ)]
      rw [hχ]; norm_num
    · have hne : ¬ χ.Even := by
        intro h'
        rw [DirichletCharacter.Even] at h'
        rw [DirichletCharacter.Odd, h'] at hχ
        norm_num at hχ
      simp only [e, if_neg hne, zero_mul]
      rw [hχ]; norm_num
  set φ : ℂ := (N.totient : ℂ) with hφ
  have hφ0 : φ ≠ 0 := by
    rw [hφ]; exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  refine ⟨fun u => φ⁻¹ * ∑ χ : DirichletCharacter ℂ N, e χ * χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N), fun s => ?_⟩

  have hstep : ∀ t : (ZMod N)ˣ,
      f t * (φ⁻¹ * ∑ χ : DirichletCharacter ℂ N, e χ * χ (((t * s)⁻¹ : (ZMod N)ˣ) : ZMod N))
        = φ⁻¹ * ∑ χ : DirichletCharacter ℂ N,
            e χ * χ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * (f t * χ ((t⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
    intro t
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [mul_inv, Units.val_mul, map_mul]
    ring
  simp_rw [hstep]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

  have h2 : ∑ χ : DirichletCharacter ℂ N, e χ * χ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * cinv χ
      = ∑ χ : DirichletCharacter ℂ N, (χ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) + χ (-((s⁻¹ : (ZMod N)ˣ) : ZMod N))) := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [mul_right_comm, he, add_mul, one_mul, ← map_mul, neg_one_mul]
  change φ⁻¹ * ∑ χ : DirichletCharacter ℂ N, e χ * χ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * cinv χ = _
  rw [h2, Finset.sum_add_distrib, DirichletCharacter.sum_characters_eq, DirichletCharacter.sum_characters_eq]
  have e1 : (((s⁻¹ : (ZMod N)ˣ) : ZMod N) = 1) ↔ s = 1 := by
    rw [Units.val_eq_one, inv_eq_one]
  have e2 : (-((s⁻¹ : (ZMod N)ˣ) : ZMod N) = 1) ↔ s = -1 := by
    constructor
    · intro h
      have h' : ((s⁻¹ : (ZMod N)ˣ) : ZMod N) = ((-1 : (ZMod N)ˣ) : ZMod N) := by
        rw [Units.val_neg, Units.val_one, ← h, neg_neg]
      have := Units.val_injective h'
      rw [inv_eq_iff_eq_inv] at this
      rw [this]; simp
    · rintro rfl; simp
  simp only [e1, e2]
  split_ifs <;> field_simp <;> ring

end EIS2K3

end

theorem solution (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ h : (ZMod N)ˣ → ℂ, ∀ s : (ZMod N)ˣ,
      ∑ t : (ZMod N)ˣ, (π : ℂ) ^ 2 / Complex.sin (π * (t : ZMod N).val / N) ^ 2 * h (t * s) =
        (if s = 1 then 1 else 0) + (if s = -1 then 1 else 0) :=
  EIS2K3.main hN

end S_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq
end P2MW
export P2MW.S_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq (solution)
