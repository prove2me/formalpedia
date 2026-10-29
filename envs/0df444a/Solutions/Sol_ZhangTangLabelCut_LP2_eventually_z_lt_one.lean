-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.eventually_z_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T05:53:46.191486+00:00
-- url     : https://prove2.me/submissions/541e5330-9dfe-4281-9d96-e5403ca0934d

import Mathlib
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

set_option autoImplicit false
open Filter Topology

namespace ZhangTangLabelCut.LP2

lemma zt_chain (a : ℝ) (ha : 1 ≤ a) :
    0 ≤ chainBound a (32 * a ^ 2) ∧ chainBound a (32 * a ^ 2) ≤ 1 - Real.exp (-(4/3)) := by
  have ha0 : 0 < a := by linarith
  have e1 : 8 * a / (32 * a ^ 2) = 1 / (4 * a) := by field_simp; ring
  set x : ℝ := 1 / (4 * a) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 4 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1x : 0 < 1 - x := by linarith
  have hlog : -(4 / 3) * x ≤ Real.log (1 - x) := by
    have h := Real.one_sub_inv_le_log_of_pos h1x
    have : -(4 / 3) * x ≤ 1 - (1 - x)⁻¹ := by
      have : (1 - x)⁻¹ ≤ 1 + 4 / 3 * x := by
        rw [inv_eq_one_div, div_le_iff₀ h1x]
        nlinarith [mul_nonneg hx0.le (by linarith : (0:ℝ) ≤ 1 / 4 - x)]
      linarith
    linarith
  have hxa : x * (4 * a) = 1 := by rw [hx]; field_simp
  have hp : (1 - x) ^ (4 * a) = Real.exp (Real.log (1 - x) * (4 * a)) := by
    rw [Real.rpow_def_of_pos h1x]
  unfold chainBound
  rw [e1, hp]
  constructor
  · have : Real.exp (Real.log (1 - x) * (4 * a)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.log_nonpos h1x.le (by linarith)
      nlinarith
    linarith
  · have : -(4 / 3) ≤ Real.log (1 - x) * (4 * a) := by
      have := mul_le_mul_of_nonneg_right hlog (by positivity : (0:ℝ) ≤ 4 * a)
      nlinarith
    have := Real.exp_le_exp.mpr this
    linarith

lemma zt_conf (k β : ℝ) (hk : 4 ≤ k) (a : ℝ) (ha : 1 ≤ a) :
    configurationBound k (k ^ β) a (32 * a ^ 2) ≤
      Real.exp (-(3 * Real.exp (-(4/3)) / 16) * (k ^ β * k ^ 2)) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨hc0, hc1⟩ := zt_chain a ha
  set e : ℝ := Real.exp (-(4/3)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hcb : chainBound a (32 * a ^ 2) ≤ Real.exp (-e) := by
    have := Real.add_one_le_exp (-e)
    linarith
  have hh : 0 < k ^ β := Real.rpow_pos_of_pos hk0 β
  set E : ℝ := k ^ β / 2 * (3 * k / 4) * (3 * k / 4 - 1) with hE
  have hE1 : 3 * (k ^ β * k ^ 2) / 16 ≤ E := by
    have h1 : k / 2 ≤ 3 * k / 4 - 1 := by linarith
    have h2 : 0 ≤ k ^ β / 2 * (3 * k / 4) := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    rw [hE]
    nlinarith
  have hE0 : 0 ≤ E := le_trans (by positivity) hE1
  unfold configurationBound
  rw [← hE]
  calc chainBound a (32 * a ^ 2) ^ E ≤ (Real.exp (-e)) ^ E :=
        Real.rpow_le_rpow hc0 hcb hE0
    _ = Real.exp (-e * E) := (Real.exp_mul (-e) E).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have : 3 * (k ^ β * k ^ 2) / 16 * e ≤ E * e := mul_le_mul_of_nonneg_right hE1 he0.le
        nlinarith

lemma zt_count (k a : ℝ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    countBound k a (32 * a ^ 2) ≤ Real.exp (6 * a * k * Real.log (32 * a ^ 2)) := by
  have hk0 : 0 < k := by linarith
  have ha0 : 0 < a := by linarith
  set d : ℝ := 32 * a ^ 2 with hd
  have hd1 : 1 ≤ d := by rw [hd]; nlinarith
  have hd0 : 0 < d := by linarith
  have h4 : 4 * a + 1 ≤ d := by rw [hd]; nlinarith
  unfold countBound
  calc (4 * a + 1) ^ k * d ^ ((4 * a + 1) * k)
      ≤ d ^ k * d ^ ((4 * a + 1) * k) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.rpow_le_rpow (by positivity) h4 hk0.le
        · exact (Real.rpow_pos_of_pos hd0 _).le
    _ = d ^ (k + (4 * a + 1) * k) := (Real.rpow_add hd0 _ _).symm
    _ ≤ d ^ (6 * a * k) := by
        apply Real.rpow_le_rpow_of_exponent_le hd1
        nlinarith
    _ = Real.exp (6 * a * k * Real.log d) := by
        rw [Real.rpow_def_of_pos hd0]; ring_nf

lemma zt_eps (δ ε γ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 6 * (Real.log 32 + 2 * δ * Real.log x) < γ * x ^ ε := by
  have h1 := (isLittleO_log_rpow_atTop hε).def' (c := γ / (48 * δ)) (by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * (6 * Real.log 32) / γ < x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_gt_atTop _
  filter_upwards [h1.bound, h2, eventually_gt_atTop 1] with x hx1 hx2 hx3
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxe] at hx1
  have hl : Real.log x ≤ γ / (48 * δ) * x ^ ε := le_trans (le_abs_self _) hx1
  have h3 : 2 * δ * Real.log x ≤ 2 * δ * (γ / (48 * δ) * x ^ ε) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have h4 : 2 * δ * (γ / (48 * δ) * x ^ ε) = γ / 24 * x ^ ε := by field_simp; ring
  have h5 : 6 * Real.log 32 < γ / 2 * x ^ ε := by
    rw [div_lt_iff₀ hγ] at hx2
    nlinarith
  nlinarith

theorem zt_main (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hgap : δ - 1 < β) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → analyticZ k β δ < 1 := by
  set γ : ℝ := 3 * Real.exp (-(4/3)) / 16 with hγ
  have hγ0 : 0 < γ := by positivity
  have hε : 0 < β + 1 - δ := by linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (zt_eps δ (β + 1 - δ) γ hδ hε hγ0)
  refine ⟨max 4 ⌈N⌉₊, le_trans (by norm_num) (le_max_left _ _), fun k hk => ?_⟩
  have hk4 : (4:ℝ) ≤ k := by
    have : 4 ≤ k := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hkN : N ≤ (k:ℝ) := by
    have : ⌈N⌉₊ ≤ k := le_trans (le_max_right _ _) hk
    exact le_trans (Nat.le_ceil N) (by exact_mod_cast this)
  have hk0 : 0 < (k:ℝ) := by linarith
  have hE := hN k hkN
  set x : ℝ := (k:ℝ) with hx
  set a : ℝ := x ^ δ with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow (by linarith) hδ.le
  have ha0 : 0 < a := by linarith
  have hd : x ^ (2 * δ) = a ^ 2 := by
    rw [ha, mul_comm, Real.rpow_mul hk0.le, Real.rpow_two]
  unfold analyticZ z
  rw [hd]
  have hc := zt_conf x β hk4 a ha1
  have hn := zt_count x a (by linarith) ha1
  have hcb0 : 0 ≤ countBound x a (32 * a ^ 2) := by
    unfold countBound; positivity
  have hcf0 : 0 ≤ configurationBound x (x ^ β) a (32 * a ^ 2) := by
    unfold configurationBound
    apply Real.rpow_nonneg (zt_chain a ha1).1
  have hlog : Real.log (32 * a ^ 2) = Real.log 32 + 2 * δ * Real.log x := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ha, Real.log_rpow hk0]
    push_cast; ring
  have hkb : x ^ β * x ^ 2 = a * x * x ^ (β + 1 - δ) := by
    rw [ha, ← Real.rpow_natCast x 2, Real.rpow_natCast]
    have : x ^ δ * x * x ^ (β + 1 - δ) = x ^ δ * (x ^ (1:ℝ) * x ^ (β + 1 - δ)) := by
      rw [Real.rpow_one]; ring
    rw [this, ← Real.rpow_add hk0, ← Real.rpow_add hk0]
    have h2 : x ^ 2 = x ^ (2:ℝ) := (Real.rpow_two x).symm
    rw [h2, ← Real.rpow_add hk0]
    congr 1; ring
  have hzle : countBound x a (32 * a ^ 2) * configurationBound x (x ^ β) a (32 * a ^ 2) ≤
      Real.exp (6 * a * x * Real.log (32 * a ^ 2)) * Real.exp (-γ * (x ^ β * x ^ 2)) :=
    mul_le_mul hn hc hcf0 (Real.exp_pos _).le
  rw [← Real.exp_add] at hzle
  refine lt_of_le_of_lt hzle ?_
  rw [Real.exp_lt_one_iff]
  rw [hlog, hkb]
  have hax : 0 < a * x := by positivity
  have := mul_lt_mul_of_pos_left hE hax
  nlinarith

end ZhangTangLabelCut.LP2

set_option autoImplicit false

theorem solution (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hgap : δ - 1 < β) :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ZhangTangLabelCut.LP2.analyticZ k β δ < 1 :=
  ZhangTangLabelCut.LP2.zt_main β δ hβ hδ hgap
