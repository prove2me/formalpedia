-- Prove2me | solution 1 for PoWMining.CostStatics.eq_B4_ci_cj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:22:36.231752+00:00
-- url     : https://prove2.me/submissions/3ff9a0c6-d10a-45ce-81a7-7aa766c24147

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

open PoWMining.CostStatics

lemma pow_cumCost_update {n : ℕ} (c : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    cumCost (Function.update c k t) = t + (cumCost c - c k) := by
  unfold cumCost
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have h := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ k) c
  linarith

lemma pow_cumCost_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    0 < cumCost c := by
  have hn : 0 < n := by have := hS.two_le; omega
  unfold cumCost
  exact Finset.sum_pos (fun k _ => hS.c_pos k) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

lemma pow_g_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    0 < gH c γ R := by
  have hC := pow_cumCost_pos c γ R hS
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hS.two_le
  have hR := hS.R_pos
  unfold gH
  split_ifs with hγ
  · apply div_pos _ (by linarith)
    rw [sub_pos, Real.lt_sqrt hC.le]
    nlinarith [mul_pos (mul_pos hR hγ) (show (0:ℝ) < n - 1 by linarith)]
  · exact div_pos (mul_pos (by linarith) hR) hC

lemma pow_sqrt_eq {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hγ : 0 < γ) :
    Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) = cumCost c + 2 * γ * gH c γ R := by
  unfold gH
  rw [if_pos hγ]
  field_simp
  ring

lemma pow_K_pos {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    0 < cumCost c + 2 * γ * gH c γ R := by
  have := pow_cumCost_pos c γ R hS
  have := pow_g_pos c γ R hS
  have := hS.γ_nonneg
  positivity

lemma pow_hasDerivAt_g {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (k : Fin n) :
    HasDerivAt (fun t => gH (Function.update c k t) γ R)
      (-(gH c γ R) / (cumCost c + 2 * γ * gH c γ R)) (c k) := by
  have hC := pow_cumCost_pos c γ R hS
  have hg := pow_g_pos c γ R hS
  have hK := pow_K_pos c γ R hS
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hS.two_le
  have hR := hS.R_pos
  set A := cumCost c - c k with hA
  have hCA : c k + A = cumCost c := by rw [hA]; ring
  have hupd : ∀ t, cumCost (Function.update c k t) = t + A := fun t => by
    rw [pow_cumCost_update]
  by_cases hγ : 0 < γ
  · have hfun : (fun t => gH (Function.update c k t) γ R) =
        fun t => (Real.sqrt ((t + A) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - (t + A)) / (2 * γ) := by
      funext t
      unfold gH
      rw [if_pos hγ, hupd]
    rw [hfun]
    have hD : (c k + A) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ ≠ 0 := by
      rw [hCA]
      have : 0 < (n : ℝ) - 1 := by linarith
      have : 0 < ((n : ℝ) - 1) * R * γ := by positivity
      nlinarith
    have h1 : HasDerivAt (fun t => (t + A) ^ 2 + 4 * ((n : ℝ) - 1) * R * γ)
        (2 * (c k + A)) (c k) := by
      have := ((hasDerivAt_id (c k)).add_const A).pow 2
      simpa using this.add_const (4 * ((n : ℝ) - 1) * R * γ)
    have h2 := (h1.sqrt hD).sub ((hasDerivAt_id (c k)).add_const A)
    have h3 := h2.div_const (2 * γ)
    refine h3.congr_deriv ?_
    rw [hCA, pow_sqrt_eq c γ R hγ]
    field_simp
    ring
  · have hγ0 : γ = 0 := le_antisymm (not_lt.mp hγ) hS.γ_nonneg
    have hfun : (fun t => gH (Function.update c k t) γ R) =
        fun t => ((n : ℝ) - 1) * R * (t + A)⁻¹ := by
      funext t
      unfold gH
      rw [if_neg hγ, hupd, div_eq_mul_inv]
    rw [hfun]
    have h1 := ((hasDerivAt_id (c k)).add_const A).inv (by rw [id, hCA]; exact hC.ne')
    have h2 := h1.const_mul (((n : ℝ) - 1) * R)
    refine h2.congr_deriv ?_
    unfold gH
    rw [if_neg hγ]
    simp only [id, hCA, hγ0]
    field_simp
    ring

lemma pow_Q_pos {n : ℕ} (c : Fin n → ℝ) (γ R G : ℝ) (hS : Standing c γ R) :
    0 < R + γ * G ^ 2 := by
  have := hS.R_pos; have := hS.γ_nonneg; positivity

lemma pow_hasDerivAt_fc {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    HasDerivAt (fun t => fH (Function.update c i t) γ R (gH c γ R) i)
      (-(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)) (c i) := by
  set g := gH c γ R
  have hQ := pow_Q_pos c γ R g hS
  have hfun : (fun t => fH (Function.update c i t) γ R g i) =
      fun t => g * (R - t * g) / (R + γ * g ^ 2) := by
    funext t; unfold fH; rw [Function.update_self]
  rw [hfun]
  have h := (((hasDerivAt_id (c i)).mul_const g).const_sub R).const_mul g
  have h2 := h.div_const (R + γ * g ^ 2)
  refine h2.congr_deriv ?_
  ring

lemma pow_hasDerivAt_fG {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n)
    (G : ℝ) :
    HasDerivAt (fun G => fH c γ R G i)
      ((R - c i * G) / (R + γ * G ^ 2)
        + G * (-(c i) * R - 2 * γ * R * G + γ * c i * G ^ 2)
          / (R + γ * G ^ 2) ^ 2) G := by
  have hQ := pow_Q_pos c γ R G hS
  have hnum : HasDerivAt (fun G : ℝ => G * (R - c i * G)) (1 * (R - c i * G) + G * (-(c i * 1))) G :=
    (hasDerivAt_id G).mul (((hasDerivAt_id G).const_mul (c i)).const_sub R)
  have hden : HasDerivAt (fun G : ℝ => R + γ * G ^ 2) (γ * (2 * G ^ 1 * 1)) G := by
    have := ((hasDerivAt_id G).pow 2).const_mul γ
    simpa using this.const_add R
  have h := hnum.div hden hQ.ne'
  refine h.congr_deriv ?_
  field_simp
  ring

lemma pow_dfdg_eq {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    dfdg c γ R i = gH c γ R / (R + γ * gH c γ R ^ 2)
          * (R / gH c γ R - 2 * (c i + γ * hstar c γ R i)) := by
  have hg := pow_g_pos c γ R hS
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  unfold dfdg
  rw [(pow_hasDerivAt_fG c γ R hS i (gH c γ R)).deriv]
  unfold hstar fH
  generalize gH c γ R = g at hg hQ ⊢
  have h1 := hg.ne'
  generalize hQd : R + γ * g ^ 2 = Q at hQ ⊢
  have h2 := hQ.ne'
  field_simp
  subst hQd
  ring

lemma pow_Delta1_eq {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    Delta1 c γ R i = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2) :=
  (pow_hasDerivAt_fc c γ R hS i).deriv

lemma pow_dgdc_eq {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    dgdc c γ R i = -(gH c γ R) / (cumCost c + 2 * γ * gH c γ R) :=
  (pow_hasDerivAt_g c γ R hS i).deriv

lemma pow_dfdg_raw {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    dfdg c γ R i = (R - c i * gH c γ R) / (R + γ * gH c γ R ^ 2)
        + gH c γ R * (-(c i) * R - 2 * γ * R * gH c γ R + γ * c i * gH c γ R ^ 2)
          / (R + γ * gH c γ R ^ 2) ^ 2 :=
  (pow_hasDerivAt_fG c γ R hS i (gH c γ R)).deriv

/-- Generic chain rule for `t ↦ G(t)(R - u(t) G(t))/(R + γ G(t)²)`. -/
lemma pow_hasDerivAt_comp (γ R : ℝ) (hR : 0 < R) (hγ : 0 ≤ γ) (u G : ℝ → ℝ) (u' G' x : ℝ)
    (hu : HasDerivAt u u' x) (hG : HasDerivAt G G' x) :
    HasDerivAt (fun t => G t * (R - u t * G t) / (R + γ * G t ^ 2))
      (((G' * (R - u x * G x) + G x * (-(u' * G x + u x * G'))) * (R + γ * G x ^ 2)
        - G x * (R - u x * G x) * (γ * (2 * G x * G'))) / (R + γ * G x ^ 2) ^ 2) x := by
  have hQ : R + γ * G x ^ 2 ≠ 0 := by positivity
  have hnum := hG.mul ((hu.mul hG).const_sub R)
  have hden : HasDerivAt (fun t => R + γ * G t ^ 2) (γ * (2 * G x * G')) x := by
    have := (hG.pow 2).const_mul γ
    have := this.const_add R
    refine this.congr_deriv ?_
    simp
  have h := hnum.div hden hQ
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]

lemma pow_hasDerivAt_h_own {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    HasDerivAt (fun t => hstar (Function.update c i t) γ R i)
      (Delta1 c γ R i + Delta2 c γ R i) (c i) := by
  have hfun : (fun t => hstar (Function.update c i t) γ R i) =
      fun t => gH (Function.update c i t) γ R * (R - id t * gH (Function.update c i t) γ R)
        / (R + γ * gH (Function.update c i t) γ R ^ 2) := by
    funext t; unfold hstar fH; rw [Function.update_self]; rfl
  rw [hfun]
  have h := pow_hasDerivAt_comp γ R hS.R_pos hS.γ_nonneg id (fun t => gH (Function.update c i t) γ R)
    1 _ (c i) (hasDerivAt_id (c i)) (pow_hasDerivAt_g c γ R hS i)
  refine h.congr_deriv ?_
  simp only [Function.update_eq_self, id]
  unfold Delta2
  rw [pow_Delta1_eq c γ R hS i, pow_dfdg_raw c γ R hS i, pow_dgdc_eq c γ R hS i]
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  generalize gH c γ R = g at hQ ⊢
  generalize -g / (cumCost c + 2 * γ * g) = g'
  generalize hQd : R + γ * g ^ 2 = Q at hQ ⊢
  have h2 := hQ.ne'
  field_simp
  subst hQd
  ring

lemma pow_hasDerivAt_h_other {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => hstar (Function.update c j t) γ R i) (Delta2 c γ R i) (c j) := by
  have hfun : (fun t => hstar (Function.update c j t) γ R i) =
      fun t => gH (Function.update c j t) γ R * (R - (fun _ => c i) t * gH (Function.update c j t) γ R)
        / (R + γ * gH (Function.update c j t) γ R ^ 2) := by
    funext t; unfold hstar fH; rw [Function.update_of_ne hij]
  rw [hfun]
  have h := pow_hasDerivAt_comp γ R hS.R_pos hS.γ_nonneg (fun _ => c i)
    (fun t => gH (Function.update c j t) γ R)
    0 _ (c j) (hasDerivAt_const _ _) (pow_hasDerivAt_g c γ R hS j)
  refine h.congr_deriv ?_
  simp only [Function.update_eq_self]
  unfold Delta2
  rw [pow_dfdg_raw c γ R hS i, pow_dgdc_eq c γ R hS i]
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  generalize gH c γ R = g at hQ ⊢
  generalize -g / (cumCost c + 2 * γ * g) = g'
  generalize hQd : R + γ * g ^ 2 = Q at hQ ⊢
  have h2 := hQ.ne'
  field_simp
  subst hQd
  ring

lemma pow_hasDerivAt_share_own {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R)
    (i : Fin n) :
    HasDerivAt (fun t => share (Function.update c i t) γ R i)
      (DeltaT1 c γ R i + DeltaT2 c γ R i) (c i) := by
  have hg := pow_g_pos c γ R hS
  have h := (pow_hasDerivAt_h_own c γ R hS i).div (pow_hasDerivAt_g c γ R hS i)
    (by simp only [Function.update_eq_self]; exact hg.ne')
  unfold share
  refine h.congr_deriv ?_
  simp only [Function.update_eq_self]
  unfold DeltaT1 DeltaT2 Delta2
  rw [← pow_dgdc_eq c γ R hS i]
  field_simp
  try ring

lemma pow_hasDerivAt_share_other {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R)
    (i j : Fin n) (hij : i ≠ j) :
    HasDerivAt (fun t => share (Function.update c j t) γ R i) (DeltaT2 c γ R i) (c j) := by
  have hg := pow_g_pos c γ R hS
  have h := (pow_hasDerivAt_h_other c γ R hS i j hij).div (pow_hasDerivAt_g c γ R hS j)
    (by simp only [Function.update_eq_self]; exact hg.ne')
  unfold share
  refine h.congr_deriv ?_
  simp only [Function.update_eq_self]
  unfold DeltaT2 Delta2
  rw [← pow_dgdc_eq c γ R hS i]
  field_simp
  try ring

lemma pow_others_le {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) : c j ≤ cumCost c - c i := by
  unfold cumCost
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) c]
  have : c j ≤ ∑ x ∈ Finset.univ \ {i}, c x :=
    Finset.single_le_sum (fun k _ => (hS.c_pos k).le) (by simp [Ne.symm hij])
  linarith

lemma pow_f_le_g {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    0 < hstar c γ R i ∧ hstar c γ R i < gH c γ R := by
  have hg := pow_g_pos c γ R hS
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  have ha := hS.active i
  have hc := hS.c_pos i
  unfold hstar fH
  constructor
  · positivity
  · rw [div_lt_iff₀ hQ]
    have := hS.γ_nonneg
    nlinarith [mul_pos hc hg, mul_nonneg this (pow_nonneg hg.le 2), mul_pos hg (mul_pos hc hg)]

lemma pow_B5' {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    c i + γ * hstar c γ R i = R / gH c γ R * (1 - hstar c γ R i / gH c γ R) := by
  have hg := pow_g_pos c γ R hS
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  unfold hstar fH
  generalize gH c γ R = g at hg hQ ⊢
  generalize hQd : R + γ * g ^ 2 = Q at hQ ⊢
  have := hg.ne'; have := hQ.ne'
  field_simp
  subst hQd
  ring

lemma pow_Delta2_closed {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * ((R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
              / (cumCost c + 2 * γ * gH c γ R)) := by
  unfold Delta2
  rw [pow_dfdg_eq c γ R hS i, pow_dgdc_eq c γ R hS i]
  ring

lemma pow_sign_Delta2 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    c i + γ * hstar c γ R i = R / gH c γ R * (1 - hstar c γ R i / gH c γ R) ∧
    (0 < Delta2 c γ R i ↔ 1 / 2 * (R / gH c γ R) < c i + γ * hstar c γ R i) ∧
    (1 / 2 * (R / gH c γ R) < c i + γ * hstar c γ R i ↔ hstar c γ R i / gH c γ R < 1 / 2) := by
  have hg := pow_g_pos c γ R hS
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  have hK := pow_K_pos c γ R hS
  have hR := hS.R_pos
  refine ⟨pow_B5' c γ R hS i, ?_, ?_⟩
  · rw [pow_Delta2_closed c γ R hS i]
    have hA : 0 < gH c γ R ^ 2 / (R + γ * gH c γ R ^ 2) := by positivity
    rw [neg_div, neg_mul, neg_pos, mul_comm]
    constructor
    · intro h
      have h' : (R / gH c γ R - 2 * (c i + γ * hstar c γ R i)) / (cumCost c + 2 * γ * gH c γ R) < 0 := by
        by_contra hc; push_neg at hc; have := mul_nonneg hc hA.le; linarith
      have h'' : R / gH c γ R - 2 * (c i + γ * hstar c γ R i) < 0 := by
        by_contra hc; push_neg at hc; have := div_nonneg hc hK.le; linarith
      linarith
    · intro h
      exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) hK) hA
  · rw [pow_B5' c γ R hS i]
    have hRg : 0 < R / gH c γ R := by positivity
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

lemma pow_DeltaT2_closed {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    DeltaT2 c γ R i = gH c γ R / (R + γ * gH c γ R ^ 2)
        * ((c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R)) := by
  have hg := pow_g_pos c γ R hS
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  have hK := pow_K_pos c γ R hS
  unfold DeltaT2
  rw [pow_dgdc_eq c γ R hS i, pow_dfdg_eq c γ R hS i]
  unfold hstar fH
  generalize gH c γ R = g at hg hQ hK ⊢
  generalize hQd : R + γ * g ^ 2 = Q at hQ ⊢
  have := hg.ne'; have := hQ.ne'; have := hK.ne'
  field_simp
  subst hQd
  ring

lemma pow_DeltaT_sum_closed {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R)
    (i : Fin n) :
    DeltaT1 c γ R i + DeltaT2 c γ R i = -(gH c γ R) / (R + γ * gH c γ R ^ 2)
        * (1 - (c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R)) := by
  have hg := pow_g_pos c γ R hS
  rw [pow_DeltaT2_closed c γ R hS i]
  unfold DeltaT1
  rw [pow_Delta1_eq c γ R hS i]
  have := hg.ne'
  field_simp
  ring

lemma pow_share_coef_lt {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    c i + 2 * γ * hstar c γ R i < cumCost c + 2 * γ * gH c γ R := by
  have h1 := pow_others_le c γ R hS i j hij
  have h2 := (pow_f_le_g c γ R hS i).2
  have h3 := hS.c_pos j
  have h4 := hS.γ_nonneg
  nlinarith [mul_nonneg h4 (sub_nonneg.mpr h2.le)]

lemma pow_eq_B4 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => hstar (Function.update c i t) γ R i)
      (Delta1 c γ R i + Delta2 c γ R i) (c i) ∧
    Delta1 c γ R i + Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * (1 + (R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
                  / (cumCost c + 2 * γ * gH c γ R)) ∧
    HasDerivAt (fun t => hstar (Function.update c j t) γ R i) (Delta2 c γ R i) (c j) ∧
    Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * ((R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
              / (cumCost c + 2 * γ * gH c γ R)) := by
  refine ⟨pow_hasDerivAt_h_own c γ R hS i, ?_, pow_hasDerivAt_h_other c γ R hS i j hij,
    pow_Delta2_closed c γ R hS i⟩
  rw [pow_Delta1_eq c γ R hS i, pow_Delta2_closed c γ R hS i]
  ring

lemma pow_eq_B6 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => share (Function.update c i t) γ R i)
      (-(gH c γ R) / (R + γ * gH c γ R ^ 2)
        * (1 - (c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R))) (c i) ∧
    -(gH c γ R) / (R + γ * gH c γ R ^ 2)
        * (1 - (c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R)) < 0 ∧
    HasDerivAt (fun t => share (Function.update c j t) γ R i)
      (gH c γ R / (R + γ * gH c γ R ^ 2)
        * ((c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R))) (c j) ∧
    0 < gH c γ R / (R + γ * gH c γ R ^ 2)
        * ((c i + 2 * γ * hstar c γ R i) / (cumCost c + 2 * γ * gH c γ R)) := by
  have hg := pow_g_pos c γ R hS
  have hQ := pow_Q_pos c γ R (gH c γ R) hS
  have hK := pow_K_pos c γ R hS
  have hf := (pow_f_le_g c γ R hS i).1
  have hc := hS.c_pos i
  have hγ := hS.γ_nonneg
  have hlt := pow_share_coef_lt c γ R hS i j hij
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pow_DeltaT_sum_closed c γ R hS i]; exact pow_hasDerivAt_share_own c γ R hS i
  · apply mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) hQ)
    rw [sub_pos, div_lt_one hK]; exact hlt
  · rw [← pow_DeltaT2_closed c γ R hS i]; exact pow_hasDerivAt_share_other c γ R hS i j hij
  · positivity

theorem solution {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i j : Fin n)
    (hij : i ≠ j) :
    HasDerivAt (fun t => hstar (Function.update c i t) γ R i)
      (Delta1 c γ R i + Delta2 c γ R i) (c i) ∧
    Delta1 c γ R i + Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * (1 + (R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
                  / (cumCost c + 2 * γ * gH c γ R)) ∧
    HasDerivAt (fun t => hstar (Function.update c j t) γ R i) (Delta2 c γ R i) (c j) ∧
    Delta2 c γ R i
      = -(gH c γ R ^ 2) / (R + γ * gH c γ R ^ 2)
          * ((R / gH c γ R - 2 * (c i + γ * hstar c γ R i))
              / (cumCost c + 2 * γ * gH c γ R)) :=
  pow_eq_B4 c γ R hS i j hij
