-- Prove2me | solution 1 for Polynomial.Chebyshev.U_rank_one_root_localization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:55:07.269591+00:00
-- url     : https://prove2.me/submissions/d22f9d06-56aa-4e5f-8653-1df9a80a1f4c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open Polynomial Real
open Filter (Tendsto atTop)
open scoped Topology

private lemma alternating_roots (n : ℕ) (p : ℝ[X]) (b : Fin (n+1) → ℝ)
    (hb : StrictAnti b) (hs : ∀ j, 0 < (-1 : ℝ)^j.val * p.eval (b j)) :
    ∃ x : Fin n → ℝ, StrictAnti x ∧ (∀ i, p.eval (x i) = 0) ∧
      (∀ i, b i.succ < x i ∧ x i < b i.castSucc) := by
  have hex (i : Fin n) : ∃ t, p.eval t = 0 ∧ b i.succ < t ∧ t < b i.castSucc := by
    let f : ℝ → ℝ := fun t => (-1 : ℝ)^i.val * p.eval t
    have hr : 0 < f (b i.castSucc) := hs i.castSucc
    have hl : f (b i.succ) < 0 := by
      have h := hs i.succ
      simpa [f, pow_succ, mul_assoc] using h
    have hlt : b i.succ < b i.castSucc := hb (by simp)
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hlt.le
      ((continuous_const.mul p.continuous).continuousOn) ⟨hl.le, hr.le⟩
    have hz : p.eval t = 0 := (mul_eq_zero.mp he).resolve_left (by positivity)
    refine ⟨t, hz, lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
    · intro h; rw [h] at hl; simp [f, hz] at hl
    · intro h; rw [← h] at hr; simp [f, hz] at hr
  choose x hx hlo hhi using hex
  refine ⟨x, ?_, hx, fun i => ⟨hlo i, hhi i⟩⟩
  intro i j hij
  have he : i.succ ≤ j.castSucc := by simpa using hij
  exact (hhi j).trans_le ((hb.antitone he).trans (hlo i).le)

private lemma roots_complete {n : ℕ} {p : ℝ[X]} (hp : p ≠ 0)
    (hd : p.natDegree = n) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hz : ∀ i, p.eval (x i) = 0) : ∀ t, p.eval t = 0 → ∃ i, x i = t := by
  classical
  let S := Finset.univ.image x
  have he : p.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero
    (by simpa [S] using hz) (by simp [S, Finset.card_image_of_injective _ hx, hd]) hp
  intro t ht
  have hm := (mem_roots hp).mpr ht
  rw [he] at hm
  simpa [S] using hm

private lemma root_above (p : ℝ[X]) (htop : Tendsto (fun t => p.eval t) atTop atTop)
    (t : ℝ) (ht : p.eval t ≤ 0) : ∃ z, t ≤ z ∧ p.eval z = 0 := by
  obtain ⟨B, hB⟩ := (htop.eventually (Filter.eventually_gt_atTop 0) |>.and (Filter.eventually_gt_atTop t)).exists
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc hB.2.le p.continuous.continuousOn ⟨ht, hB.1.le⟩
  exact ⟨z, hz.1, he⟩

private lemma pole_eval (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (a : ℝ) :
    ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)) - C a * Chebyshev.U ℝ (k : ℤ)).eval
      (cos ((j : ℝ)*Real.pi/((k : ℝ)+1))) = (-1 : ℝ)^j := by
  let θ := (j : ℝ)*Real.pi/((k : ℝ)+1)
  have hk : 0 < (k : ℝ)+1 := by positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθp : θ < Real.pi := by dsimp [θ]; apply (div_lt_iff₀ hk).mpr; nlinarith [pi_pos, show (j : ℝ) ≤ k by exact_mod_cast hjk]
  have hs := sin_pos_of_pos_of_lt_pi hθ hθp
  have hmul : ((k : ℝ)+1)*θ = (j : ℝ)*Real.pi := by dsimp [θ]; field_simp
  have h1 := Chebyshev.U_real_cos (n := (k : ℤ)) (θ := θ)
  have h2 := Chebyshev.U_real_cos (n := ((k+1 : ℕ) : ℤ)) (θ := θ)
  push_cast at h1 h2
  rw [hmul, sin_nat_mul_pi] at h1
  have hu : (Chebyshev.U ℝ (k : ℤ)).eval (cos θ) = 0 := (mul_eq_zero.mp h1).resolve_right hs.ne'
  have he : ((k : ℝ)+1+1)*θ = (j : ℝ)*Real.pi+θ := by linarith [hmul]
  rw [he, sin_add, sin_nat_mul_pi, cos_nat_mul_pi] at h2
  simp only [zero_mul, zero_add] at h2
  change ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)) - C a * Chebyshev.U ℝ (k : ℤ)).eval (cos θ) = _
  simp only [eval_sub, eval_mul, eval_C, hu, mul_zero, sub_zero]
  exact mul_right_cancel₀ hs.ne' (by simpa only [Nat.cast_add, Nat.cast_one] using h2)

private lemma end_eval (k : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    0 < (-1 : ℝ)^(k+1) *
      ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)) - C a * Chebyshev.U ℝ (k : ℤ)).eval (-1) := by
  simp only [eval_sub, eval_mul, eval_C, Chebyshev.U_eval_neg_one,
    Int.cast_natCast, Int.cast_negOnePow_natCast]
  have hs : ((-1 : ℝ)^k)^2 = 1 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  push_cast
  rw [pow_succ]
  calc
    _ = ((-1 : ℝ)^k)^2 * ((k : ℝ)+2+a*((k : ℝ)+1)) := by ring
    _ > 0 := by rw [hs]; positivity

private lemma data_roots (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    let p := Chebyshev.U ℝ ((k+1 : ℕ) : ℤ) - C a * Chebyshev.U ℝ (k : ℤ)
    ∃ (b : Fin (k+2) → ℝ) (x : Fin (k+1) → ℝ),
      StrictAnti b ∧ StrictAnti x ∧ (∀ i, p.eval (x i) = 0) ∧
      (∀ i, b i.succ < x i ∧ x i < b i.castSucc) ∧
      (∀ j, 0 < (-1 : ℝ)^j.val * p.eval (b j)) ∧
      (∀ j, j ≠ 0 → b j = cos ((j.val : ℝ)*Real.pi/((k : ℝ)+1))) ∧
      (∀ t, p.eval t = 0 → ∃ i, x i = t) ∧
      Tendsto (fun t => p.eval t) atTop atTop := by
  classical
  dsimp only
  let p := Chebyshev.U ℝ ((k+1 : ℕ) : ℤ) - C a * Chebyshev.U ℝ (k : ℤ)
  have hdeg : (C a * Chebyshev.U ℝ (k : ℤ)).degree <
      (Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)).degree := by
    rw [Chebyshev.degree_U_natCast]
    apply lt_of_le_of_lt (show (C a * Chebyshev.U ℝ (k : ℤ)).degree ≤ (Chebyshev.U ℝ (k : ℤ)).degree by
      simpa only [C_mul'] using degree_smul_le a (Chebyshev.U ℝ (k : ℤ)))
    rw [Chebyshev.degree_U_natCast]
    exact_mod_cast Nat.lt_succ_self k
  have hpd : p.degree = (k+1 : ℕ) := by
    change (Chebyshev.U ℝ ((k+1 : ℕ) : ℤ) - C a * Chebyshev.U ℝ (k : ℤ)).degree = _
    rw [degree_sub_eq_left_of_degree_lt hdeg, Chebyshev.degree_U_natCast]
  have hpn : p.natDegree = k+1 := natDegree_eq_of_degree_eq_some hpd
  have hp0 : p ≠ 0 := by intro h; rw [h, degree_zero] at hpd; exact WithBot.bot_ne_coe hpd
  have htop : Tendsto (fun t => p.eval t) atTop atTop := by
    apply p.tendsto_atTop_of_leadingCoeff_nonneg
    · rw [hpd]; exact_mod_cast Nat.zero_lt_succ k
    · change 0 ≤ (Chebyshev.U ℝ ((k+1 : ℕ) : ℤ) - C a * Chebyshev.U ℝ (k : ℤ)).leadingCoeff
      rw [leadingCoeff_sub_of_degree_lt hdeg, Chebyshev.leadingCoeff_U_natCast]; positivity
  obtain ⟨B, hBp, hB⟩ := (htop.eventually (Filter.eventually_gt_atTop 0) |>.and
    (Filter.eventually_gt_atTop (1 : ℝ))).exists
  let b : Fin (k+2) → ℝ := fun j => if j = 0 then B else cos ((j.val : ℝ)*Real.pi/((k : ℝ)+1))
  have hbform (j) (hj : j ≠ 0) : b j = cos ((j.val : ℝ)*Real.pi/((k : ℝ)+1)) := if_neg hj
  have hb : StrictAnti b := by
    intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by intro h; subst h; exact (not_lt_of_ge (Fin.zero_le _)) hij
      rw [hbform j hj]
      simpa [b, hi] using (cos_le_one _).trans_lt hB
    · have hj : j ≠ 0 := by intro h; subst h; exact (not_lt_of_ge (Fin.zero_le _)) hij
      rw [hbform i hi, hbform j hj]
      apply cos_lt_cos_of_nonneg_of_le_pi (by positivity)
      · apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).mpr
        have hv : (j.val : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast (show j.val ≤ k+1 by omega)
        nlinarith [pi_pos]
      · apply (div_lt_div_iff_of_pos_right (by positivity : 0 < (k : ℝ)+1)).mpr
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) pi_pos
  have hs : ∀ j, 0 < (-1 : ℝ)^j.val * p.eval (b j) := by
    intro j
    by_cases hj : j = 0
    · simpa [b, hj] using hBp
    · rw [hbform j hj]
      by_cases hlast : j.val = k+1
      · have he : (j.val : ℝ)*Real.pi/((k : ℝ)+1) = Real.pi := by rw [hlast]; push_cast; field_simp
        rw [he, cos_pi, hlast]; exact end_eval k a ha
      · rw [pole_eval k j.val (by have := Fin.val_ne_of_ne hj; simp only [Fin.val_zero] at this; omega) (by omega)]
        rw [← mul_pow]; norm_num
  obtain ⟨x, hx, hz, hbounds⟩ := alternating_roots (k+1) p b hb hs
  exact ⟨b, x, hb, hx, hz, hbounds, hs, hbform,
    roots_complete hp0 hpn hx.injective hz, htop⟩

private lemma base_eval (k : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)) - C a * Chebyshev.U ℝ (k : ℤ)).eval
      (cos (Real.pi/((k : ℝ)+2))) ≤ 0 := by
  let θ := Real.pi/((k : ℝ)+2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθp : θ < Real.pi := by
    dsimp [θ]; apply (div_lt_iff₀ (by positivity : 0 < (k : ℝ)+2)).mpr
    nlinarith [pi_pos, show 0 ≤ (k : ℝ) by positivity]
  have hs := sin_pos_of_pos_of_lt_pi hθ hθp
  have he : ((k : ℝ)+2)*θ = Real.pi := by dsimp [θ]; field_simp
  have h1 := Chebyshev.U_real_cos (n := (k : ℤ)) (θ := θ)
  have h2 := Chebyshev.U_real_cos (n := ((k+1 : ℕ) : ℤ)) (θ := θ)
  push_cast at h1 h2
  have he1 : ((k : ℝ)+1)*θ = Real.pi-θ := by linarith [he]
  have he2 : ((k : ℝ)+1+1)*θ = Real.pi := by linarith [he]
  rw [he1, sin_pi_sub] at h1
  rw [he2, sin_pi] at h2
  have hu : (Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)).eval (cos θ) = 0 := by
    apply (mul_eq_zero.mp _).resolve_right hs.ne'
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  have hv : (Chebyshev.U ℝ (k : ℤ)).eval (cos θ) = 1 := by nlinarith
  change ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)) - C a * Chebyshev.U ℝ (k : ℤ)).eval (cos θ) ≤ 0
  simp only [Nat.cast_add, Nat.cast_one] at hu
  simpa only [eval_sub, eval_mul, eval_C, Nat.cast_add, Nat.cast_one, hu, hv, zero_sub, mul_one] using neg_nonpos.mpr ha

private lemma test_eval (k : ℕ) (hk : 1 ≤ k) (a θ : ℝ)
    (hθ : θ ∈ Set.Ioo (Real.pi/((k : ℝ)+1)) (2*Real.pi/((k : ℝ)+1)))
    (ha : a < sin (((k : ℝ)+2)*θ)/sin (((k : ℝ)+1)*θ)) :
    ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)) - C a * Chebyshev.U ℝ (k : ℤ)).eval (cos θ) < 0 := by
  have hn : 0 < (k : ℝ)+1 := by positivity
  have hkp : 2 ≤ (k : ℝ)+1 := by exact_mod_cast (show 2 ≤ k+1 by omega)
  have hθ0 : 0 < θ := (by positivity : 0 < Real.pi/((k : ℝ)+1)).trans hθ.1
  have hθp : θ < Real.pi := hθ.2.trans_le ((div_le_iff₀ hn).mpr (by nlinarith [pi_pos]))
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 hθp
  have hl : Real.pi < ((k : ℝ)+1)*θ := by nlinarith [(div_lt_iff₀ hn).mp hθ.1]
  have hr : ((k : ℝ)+1)*θ < 2*Real.pi := by nlinarith [(lt_div_iff₀ hn).mp hθ.2]
  have hsn : sin (((k : ℝ)+1)*θ) < 0 := by
    have h := sin_pos_of_pos_of_lt_pi (by linarith : 0 < ((k : ℝ)+1)*θ-Real.pi) (by linarith : ((k : ℝ)+1)*θ-Real.pi < Real.pi)
    rw [sin_sub_pi] at h
    linarith
  have he := (lt_div_iff_of_neg hsn).mp ha
  have h1 := Chebyshev.U_real_cos (n := (k : ℤ)) (θ := θ)
  have h2 := Chebyshev.U_real_cos (n := ((k+1 : ℕ) : ℤ)) (θ := θ)
  push_cast at h1 h2
  have hc : (k : ℝ)+1+1 = (k : ℝ)+2 := by ring
  rw [hc] at h2
  rw [eval_sub, eval_mul, eval_C]
  have h2' : (Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)).eval (cos θ)*sin θ = sin (((k : ℝ)+2)*θ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h2
  have hval : ((Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)).eval (cos θ) -
      a * (Chebyshev.U ℝ (k : ℤ)).eval (cos θ)) * sin θ < 0 := by
    rw [sub_mul, mul_assoc, h1, h2']
    exact sub_neg.mpr he
  nlinarith only [hval, hs]

theorem solution
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    ∃ x : Fin (k+1) → ℝ, StrictAnti x ∧
      (∀ i, (Polynomial.Chebyshev.U ℝ ((k+1 : ℕ) : ℤ)).eval (x i) =
        a * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (x i)) ∧
      x ⟨1, by omega⟩ ≤ Real.cos (Real.pi / ((k : ℝ)+1)) ∧
      Real.cos (Real.pi / ((k : ℝ)+2)) ≤ x 0 ∧
      (((k : ℝ)+2) / ((k : ℝ)+1) ≤ a → 1 ≤ x 0) ∧
      (∀ θ ∈ Set.Ioo (Real.pi / ((k : ℝ)+1)) (2*Real.pi / ((k : ℝ)+1)),
        a < Real.sin (((k : ℝ)+2)*θ) / Real.sin (((k : ℝ)+1)*θ) →
        x ⟨1, by omega⟩ ≤ Real.cos θ) := by
  classical
  let p := Chebyshev.U ℝ ((k+1 : ℕ) : ℤ) - C a * Chebyshev.U ℝ (k : ℤ)
  obtain ⟨b, x, hb, hx, hz, hbounds, hs, hbform, hcomplete, htop⟩ := data_roots k hk a ha
  have hb1 : b ⟨1, by omega⟩ = cos (Real.pi/((k : ℝ)+1)) := by
    simpa using hbform ⟨1, by omega⟩ (by simp)
  have hb2 : b ⟨2, by omega⟩ = cos (2*Real.pi/((k : ℝ)+1)) := by
    simpa using hbform ⟨2, by omega⟩ (by simp)
  have hmax (t : ℝ) (ht : p.eval t ≤ 0) : t ≤ x 0 := by
    obtain ⟨z, htz, hz⟩ := root_above p htop t ht
    obtain ⟨i, rfl⟩ := hcomplete z hz
    exact htz.trans (hx.antitone (Fin.zero_le _))
  refine ⟨x, hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; have h := hz i; rw [eval_sub, eval_mul, eval_C] at h; exact sub_eq_zero.mp h
  · exact (hbounds ⟨1, by omega⟩).2.le.trans_eq hb1
  · exact hmax _ (base_eval k a ha)
  · intro h
    apply hmax
    dsimp only [p]
    rw [eval_sub, eval_mul, eval_C, Chebyshev.U_eval_one, Chebyshev.U_eval_one]
    push_cast
    have he : (k : ℝ)+1+1 = (k : ℝ)+2 := by ring
    rw [he]
    exact sub_nonpos.mpr ((div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).mp h)
  · intro θ hθ ht
    have hn : 0 < (k : ℝ)+1 := by positivity
    have hkp : 2 ≤ (k : ℝ)+1 := by exact_mod_cast (show 2 ≤ k+1 by omega)
    have hθ0 : 0 < θ := (by positivity : 0 < Real.pi/((k : ℝ)+1)).trans hθ.1
    have hθp : θ < Real.pi := hθ.2.trans_le ((div_le_iff₀ hn).mpr (by nlinarith [pi_pos]))
    have hcos1 : cos θ < b ⟨1, by omega⟩ := by
      rw [hb1]; exact cos_lt_cos_of_nonneg_of_le_pi (by positivity) hθp.le hθ.1
    have hcos2 : b ⟨2, by omega⟩ < cos θ := by
      rw [hb2]; apply cos_lt_cos_of_nonneg_of_le_pi hθ0.le _ hθ.2
      exact (div_le_iff₀ hn).mpr (by nlinarith [pi_pos])
    have hneg : p.eval (cos θ) < 0 := test_eval k hk a θ hθ ht
    have hpos : 0 < p.eval (b ⟨2, by omega⟩) := by simpa only [Fin.val_mk, neg_one_sq, one_mul] using hs ⟨2, by omega⟩
    obtain ⟨z, hzi, hzr⟩ := intermediate_value_Icc' hcos2.le p.continuous.continuousOn ⟨hneg.le, hpos.le⟩
    change p.eval z = 0 at hzr
    obtain ⟨i, hi⟩ := hcomplete z hzr
    have hlow : b ⟨2, by omega⟩ < z := by
      apply lt_of_le_of_ne hzi.1
      intro he; rw [he, hzr] at hpos; linarith
    have hi0 : i.val ≠ 0 := by
      intro he
      have hi' : i = 0 := Fin.ext he
      have hbound := (hbounds (0 : Fin (k+1))).1
      rw [hi'] at hi
      have heq : (0 : Fin (k+1)).succ = (⟨1, by omega⟩ : Fin (k+2)) := rfl
      rw [heq, hi] at hbound
      linarith [hzi.2]
    have hi2 : i.val < 2 := by
      by_contra h
      have hb' : b i.castSucc ≤ b ⟨2, by omega⟩ := hb.antitone (by change 2 ≤ i.val; omega)
      have hbound := (hbounds i).2
      rw [hi] at hbound
      linarith
    have hi' : i = ⟨1, by omega⟩ := by apply Fin.ext; change i.val = 1; omega
    rw [hi'] at hi
    exact hi.le.trans hzi.2
