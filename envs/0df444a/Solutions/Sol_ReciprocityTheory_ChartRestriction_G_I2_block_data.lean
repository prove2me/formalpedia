-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.block_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:23.796037+00:00
-- url     : https://prove2.me/submissions/d594f539-8701-466c-a9cf-010ae57969f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_Hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_fin_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_l2NormSq_nonneg_gaussianTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ph_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Cchi_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_inv_constant_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_onb_data


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) [IsCMField E] (X : PT E) {DF : ℕ} (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I) (σ : E →+* ℂ) (i : ℕ) (hi : i ≤ X.dim σ)
    (c : ℕ) (hcD : c ≤ DF) :
    ∃ (y : Fin i → Vsp X.dim) (s : Fin i → (Fin 1 → Vsp X.dim) → ℂ) (μ : Fin i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin c → Vsp X.dim), (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ))
          (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Module.finrank ℂ
      (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ (Vsp X.dim)) = ρ := ⟨_, rfl⟩
  obtain ⟨w, xx, u, R, ε, hw, hon, hxu, -, hεb, hc4, hc5, hc6, hc7⟩ := hc E X DF P I hI σ ρ hρ
  obtain ⟨N, bb, hNr, hρN, hbw, hin, hperp, hpars⟩ := onb_data X I σ ρ hρ hI.stable w hw hon
  set e : Fin i → Vsp X.dim := fun a => EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ)
    with he
  have he_in : ∀ a, InPart σ (e a) := by
    intro a j hj
    simp only [he, PiLp.single_apply]
    rw [if_neg]
    rintro rfl
    exact hj rfl
  have hee : ∀ a a', Hf (e a) (e a') = if a = a' then 1 else 0 := by
    intro a a'
    simp only [he]
    rw [Hf_single]
    by_cases h : a = a'
    · simp [h]
    · rw [if_neg, if_neg h]
      intro h2
      rw [Sigma.mk.inj_iff] at h2
      exact h (Fin.castLE_injective hi (eq_of_heq h2.2))
  let M : Matrix (Fin i) (Fin N) ℂ := Matrix.of fun a k => Hf (e a) (bb k)
  have hMM : M * M.conjTranspose = 1 := by
    ext a a'
    simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply, jof_Hf_conj]
    rw [hpars (e a) (e a') (he_in a) (he_in a'), hee]
  obtain ⟨s1, -, hs1⟩ := hx.2.2.2.2.2.1 i N X.r M hMM hNr
  haveI : Nonempty (Fin i → Fin N) := ⟨s1⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s : Fin i → Fin N => ‖(M.submatrix id s).det‖)
  set Δ := ‖(M.submatrix id s0).det‖ with hΔ
  have hΔr : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ Δ := hs1.trans (hs0 s1)
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔr
  have hinj : Function.Injective s0 := by
    intro j j' h
    by_contra hne
    have h0 : (M.submatrix id s0).det = 0 := Matrix.det_zero_of_column_eq hne (by intro a; simp [h])
    rw [hΔ, h0, norm_zero] at hΔpos
    exact lt_irrefl 0 hΔpos
  have hRpos : ∀ t, 0 < R t := by
    intro t
    have h1 := (hc5 t).2
    have hp := Real.pi_pos
    by_contra h
    push Not at h
    nlinarith
  have hT : ∀ t : Fin ρ, ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) (u t)‖ ≤ P.eps1 * (2 * Real.pi * R t) ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u t‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ (2 * Real.pi * R t) ^ (2 * c) :=
    fun t => ht E X DF P I hI c hcD σ (xx t) (u t) (hxu t).1 (hxu t).2 (2 * Real.pi * R t) (hc5 t).2
      (by have h1 := (hc5 t).1; have hp := Real.pi_pos; nlinarith) (hc6 t)
  choose sT hsT ζ hζ hζb hζl using hT
  have hA : ∀ k : Fin N, ρ ≤ k.val → ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k', Hf (xs k') (bb k)‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2 :=
    fun k hk => ha E X DF P I hI c hcD σ (bb k) (hin k) (hperp k hk).1 (hperp k hk).2
  choose sA hsA hAb hAl using hA
  have hK6 := inv_constant_nonneg P
  have hexp1 : Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have := Cchi_nonneg (E := E) P.m
    have := ph_nonneg P
    have := Real.pi_pos
    positivity
  have hexp : ∀ t, Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) ≤
      Real.exp (-(2 * Real.pi * ‖u t‖ ^ 2 / P.q)) := by
    intro t
    rw [Real.exp_le_exp, neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have := hc7 t
    have := Real.pi_pos
    nlinarith
  let y : Fin i → Vsp X.dim := fun j =>
    if h : (s0 j).val < ρ then ((R ⟨_, h⟩ : ℂ))⁻¹ • u ⟨_, h⟩ else bb (s0 j)
  let s : Fin i → (Fin 1 → Vsp X.dim) → ℂ := fun j =>
    if h : (s0 j).val < ρ then sT ⟨_, h⟩ else sA (s0 j) (not_lt.1 h)
  let μ : Fin i → ℂ := fun j =>
    if h : (s0 j).val < ρ then ζ ⟨_, h⟩ * (((2 * Real.pi * R ⟨_, h⟩ : ℝ)) : ℂ) ^ c
    else (c.factorial : ℂ)
  have hnμ : ∀ t, ‖ζ t * (((2 * Real.pi * R t : ℝ)) : ℂ) ^ c‖ = (2 * Real.pi * R t) ^ c := by
    intro t
    have := hRpos t
    rw [norm_mul, hζ t, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  refine ⟨y, s, μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [s, dif_pos h]; exact hsT _
    · simp only [s, dif_neg h]; exact hsA _ _
  · intro j xs hxs
    by_cases h : (s0 j).val < ρ
    · simp only [s, μ, y, dif_pos h]
      have hR := hRpos ⟨_, h⟩
      have e1 : ζ ⟨_, h⟩ * (((2 * Real.pi * R ⟨_, h⟩ : ℝ)) : ℂ) ^ c *
          ∏ k, Hf (xs k) (((R ⟨_, h⟩ : ℂ))⁻¹ • u ⟨_, h⟩) =
          ζ ⟨_, h⟩ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) (u ⟨_, h⟩) := by
        simp only [jof_Hf_smul_right, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, map_inv₀, Complex.conj_ofReal]
        have hR' : (R ⟨_, h⟩ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        push_cast
        have key : (2 * (Real.pi : ℂ) * (R ⟨_, h⟩ : ℂ)) ^ c * (1 / (R ⟨_, h⟩ : ℂ)) ^ c =
            (2 * Real.pi) ^ c := by
          rw [← mul_pow]; congr 1; field_simp
        linear_combination (ζ ⟨_, h⟩ * ∏ x, Hf (xs x) (u ⟨_, h⟩)) * key
      rw [e1, hnμ]
      exact hζb _ xs hxs
    · simp only [s, μ, y, dif_neg h]
      rw [Complex.norm_natCast]
      exact hAb _ _ xs hxs
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [s, μ, dif_pos h]
      rw [hnμ]
      have hl := l2NormSq_nonneg_gaussianTorus X P.q (sT ⟨_, h⟩)
      calc P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (sT ⟨_, h⟩)
          ≤ P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u ⟨_, h⟩‖ ^ 2 / P.q)) * X.l2 P.q (sT ⟨_, h⟩) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp _) hK6) hl
        _ ≤ (2 * Real.pi * R ⟨_, h⟩) ^ (2 * c) := hζl _
        _ = ((2 * Real.pi * R ⟨_, h⟩) ^ c) ^ 2 := by ring
    · simp only [s, μ, dif_neg h]
      rw [Complex.norm_natCast]
      have hl := l2NormSq_nonneg_gaussianTorus X P.q (sA (s0 j) (not_lt.1 h))
      calc P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) *
            X.l2 P.q (sA (s0 j) (not_lt.1 h))
          ≤ P.K6⁻¹ * X.l2 P.q (sA (s0 j) (not_lt.1 h)) :=
            mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hK6 hexp1) hl
        _ ≤ (c.factorial : ℝ) ^ 2 := hAl _ _
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [y, dif_pos h]
      have hR := hRpos ⟨_, h⟩
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, inv_mul_le_iff₀ hR]
      have := (hc5 ⟨_, h⟩).1
      linarith
    · simp only [y, dif_neg h]
      rw [(hperp _ (not_lt.1 h)).1]
      norm_num
  ·
    have hDP := hx.2.2.2.2.2.2.1
    have hDN := hx.2.2.2.2.2.2.2.1
    let wv : Fin N → Fin i → ℂ := fun k a => Hf (e a) (bb k)
    let εc : Fin i → Fin N → ℂ := fun j k =>
      if h : (s0 j).val < ρ then (if hk : k.val < ρ then ε ⟨_, h⟩ ⟨_, hk⟩ else 0) else 0
    have hentry : ∀ a j, Hf (e a) (y j) = wv (s0 j) a + ∑ k, εc j k * wv k a := by
      intro a j
      by_cases h : (s0 j).val < ρ
      · simp only [y, dif_pos h, jof_Hf_smul_right, map_inv₀, Complex.conj_ofReal]
        have hR := hRpos ⟨_, h⟩
        have hR' : (R ⟨_, h⟩ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        have h4 := hc4 ⟨_, h⟩ (e a) (he_in a)
        have hws : w ⟨_, h⟩ = bb (s0 j) := (hbw (s0 j) h).symm
        have hsum : ∑ s', ε ⟨_, h⟩ s' * Hf (e a) (w s') = ∑ k, εc j k * wv k a := by
          rw [← sum_fin_le hρN (fun s' => ε ⟨_, h⟩ s' * Hf (e a) (w s'))]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : k.val < ρ
          · simp only [εc, wv, dif_pos h, dif_pos hk]
            rw [hbw k hk]
          · simp only [εc, dif_pos h, dif_neg hk, zero_mul]
        rw [← hsum]
        simp only [wv]
        rw [← hws, ← h4, div_eq_inv_mul]
      · simp only [y, dif_neg h, εc, wv, zero_mul, Finset.sum_const_zero, add_zero]
    have hmat : (Matrix.of fun a b => Hf (EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ))
        (y b)) = Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a := by
      ext a j
      simp only [Matrix.of_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hentry a j
    have hold : (Matrix.of fun a j => wv (s0 j) a).det = (M.submatrix id s0).det := rfl
    have hmax : ∀ σ' : Fin i → Fin N, ‖(Matrix.of fun a j => wv (σ' j) a).det‖ ≤ Δ :=
      fun σ' => hs0 σ'
    have hpert := hDP ℂ i (Fin N) wv s0 εc Δ hmax

    set B : ℝ := Real.sqrt ρ / (30 * ρ ^ 2) with hB
    have hB0 : 0 ≤ B := by positivity
    have hrow : ∀ j, ∑ k, ‖εc j k‖ ≤ if (s0 j).val < ρ then B else 0 := by
      intro j
      by_cases h : (s0 j).val < ρ
      · rw [if_pos h]
        have := (hεb ⟨_, h⟩).2
        rw [← sum_fin_le hρN (fun s' => ‖ε ⟨_, h⟩ s'‖)] at this
        refine le_of_eq_of_le ?_ this
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k.val < ρ
        · simp [εc, dif_pos h, dif_pos hk]
        · simp [εc, dif_pos h, dif_neg hk]
      · rw [if_neg h]
        simp [εc, dif_neg h]
    have hprod : ∏ j, (1 + ∑ k, ‖εc j k‖) ≤ (1 + B) ^ ρ := by
      calc ∏ j, (1 + ∑ k, ‖εc j k‖)
          ≤ ∏ j, (if (s0 j).val < ρ then 1 + B else 1) := by
            refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
            have := hrow j
            by_cases h : (s0 j).val < ρ
            · simp only [h, if_true] at this ⊢; linarith
            · simp only [h, if_false] at this ⊢; linarith
        _ = (1 + B) ^ (Finset.univ.filter fun j => (s0 j).val < ρ).card := by
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        _ ≤ (1 + B) ^ ρ := by
            apply pow_le_pow_right₀ (by linarith)
            have : (Finset.univ.filter fun j => (s0 j).val < ρ).card ≤ (Finset.range ρ).card := by
              apply Finset.card_le_card_of_injOn (fun j => (s0 j).val)
              · intro j hj
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
                simpa using hj
              · intro j _ j' _ hjj
                exact hinj (Fin.ext hjj)
            simpa using this
    have hhalf : (1 + B) ^ ρ - 1 ≤ 1 / 2 := by
      rcases Nat.eq_zero_or_pos ρ with h0 | hpos
      · subst h0; norm_num
      · have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hpos
        have hnum := hDN ρ hpos
        have hBle : B ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10 := by
          have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (by positivity)
          have hsp : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by linarith)
          have hr : (ρ : ℝ) ^ (-(3 : ℝ) / 2) = 1 / (ρ * Real.sqrt ρ) := by
            rw [show (-(3 : ℝ) / 2) = -((1 : ℝ) + 1 / 2) by norm_num, Real.rpow_neg (by positivity),
              Real.rpow_add (by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
          have hBeq : B = (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 30 := by
            rw [hr, hB, div_div, div_eq_div_iff (by positivity) (by positivity)]
            linear_combination (30 * (ρ : ℝ)) * hsq
          have h0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
          rw [hBeq]
          linarith
        have : (1 + B) ^ ρ ≤ (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ :=
          pow_le_pow_left₀ (by linarith) (by linarith) ρ
        linarith
    have hfac : ((∏ j, (1 + ∑ k, ‖εc j k‖)) - 1) * Δ ≤ Δ / 2 := by
      have := hΔpos.le
      nlinarith [hprod, hhalf]
    rw [hmat]
    have h2 : ‖(Matrix.of fun a j => wv (s0 j) a).det‖ = Δ := by rw [hold]
    have h4 : Δ - ‖(Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det -
        (Matrix.of fun a j => wv (s0 j) a).det‖ ≤
        ‖(Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det‖ := by
      have := norm_sub_norm_le (Matrix.of fun a j => wv (s0 j) a).det
        (Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det
      rw [h2, norm_sub_rev] at this
      linarith
    linarith [hpert, hfac, h4, hΔr]
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [μ, dif_pos h]
      rw [← norm_ne_zero_iff, hnμ]
      have := hRpos ⟨_, h⟩
      positivity
    · simp only [μ, dif_neg h]
      exact_mod_cast Nat.factorial_ne_zero c
end ReciprocityTheory.ChartRestriction.G.I2
