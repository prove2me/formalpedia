-- Prove2me | solution 1 for ProxADMMLC.Conv.eq_3_37
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T18:40:56.442976+00:00
-- url     : https://prove2.me/submissions/843c12cb-b903-494f-9cc4-23546f16ebfb

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_1
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_2
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_3
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_5
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_10_primal
import Theorems.Thm_ProxADMMLC_Conv_lemma_3_10_dual
import Theorems.Thm_ProxADMMLC_Conv_cor_3_7
import Theorems.Thm_ProxADMMLC_Conv_cor_3_8
import Theorems.Thm_ProxADMMLC_Conv_eq_3_12_dist

set_option autoImplicit false

namespace E337Aux

open ProxADMMLC.Conv

theorem boxProj_mem {n : ℕ} {ℓ u : Fin n → ℝ} (h : ∀ i, ℓ i < u i) (v : E n) :
    boxProj ℓ u v ∈ box ℓ u := by
  intro i
  simp only [boxProj, PiLp.toLp_apply]
  have := h i
  split_ifs <;> constructor <;> linarith

theorem box_comb {n : ℕ} {ℓ u : Fin n → ℝ} {z x : E n} {β : ℝ} (hz : z ∈ box ℓ u)
    (hx : x ∈ box ℓ u) (h0 : 0 ≤ β) (h1 : β ≤ 1) : z + β • (x - z) ∈ box ℓ u := by
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  obtain ⟨hz1, hz2⟩ := hz i
  obtain ⟨hx1, hx2⟩ := hx i
  have e1 := mul_le_mul_of_nonneg_left hx1 h0
  have e2 := mul_le_mul_of_nonneg_left hz1 (sub_nonneg.2 h1)
  have e3 := mul_le_mul_of_nonneg_left hx2 h0
  have e4 := mul_le_mul_of_nonneg_left hz2 (sub_nonneg.2 h1)
  constructor <;> nlinarith

/-- The squared diameter bound of the box. -/
theorem box_diam {n : ℕ} {ℓ u : Fin n → ℝ} {x x' : E n} (hx : x ∈ box ℓ u)
    (hx' : x' ∈ box ℓ u) : ‖x - x'‖ ^ 2 ≤ ∑ i, (u i - ℓ i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  obtain ⟨a1, a2⟩ := hx i
  obtain ⟨b1, b2⟩ := hx' i
  nlinarith

/-- The final case analysis (3.28)-(3.36) of the proof of Theorem 2.4. -/
theorem final_arith {c p α β X R W Ee Mb2 dφ : ℝ} (hc : 0 < c) (hp : 0 < p) (hα : 0 < α)
    (hβ : 0 < β) (hX : 0 ≤ X) (hR : 0 ≤ R) (hW : 0 ≤ W) (hEe : 0 ≤ Ee) (hEM : Ee ≤ Mb2)
    (h325 : dφ ≥ X / (4 * c) + α * R + p / (3 * β) * W - 7 * p * β * Ee)
    (hcase : X < 56 * c * p * β * Mb2 → α * R < 14 * p * β * Mb2 → W < 42 * β ^ 2 * Ee →
      14 * p * β * Ee ≤ α * R) :
    dφ ≥ 1 / (8 * c) * X + α / 2 * R + p / (6 * β) * W := by
  have i1 : X / (4 * c) = 2 * (1 / (8 * c) * X) := by field_simp; ring
  have i2 : p / (3 * β) * W = 2 * (p / (6 * β) * W) := by field_simp; ring
  have n1 : 0 ≤ 1 / (8 * c) * X := by positivity
  have n2 : 0 ≤ p / (6 * β) * W := by positivity
  have hpβ : 0 ≤ 7 * p * β := by positivity
  have hEM' : 7 * p * β * Ee ≤ 7 * p * β * Mb2 := mul_le_mul_of_nonneg_left hEM hpβ
  by_cases hA : X < 56 * c * p * β * Mb2
  · by_cases hB : α * R < 14 * p * β * Mb2
    · by_cases hC : W < 42 * β ^ 2 * Ee
      · have := hcase hA hB hC
        nlinarith
      · have hC' : 7 * p * β * Ee ≤ p / (6 * β) * W := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          push Not at hC
          nlinarith
        nlinarith
    · push Not at hB
      nlinarith
  · push Not at hA
    have : 7 * p * β * Mb2 ≤ 1 / (8 * c) * X := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith

end E337Aux

set_option maxHeartbeats 1000000 in
open ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hA : Assumption22 f A b ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p c : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ α, 0 < α → 4 * c * ‖A‖ ^ 2 * α < (c * (p + γ)) ^ 2 → ∀ y0 : E m, ∃ β₀ > 0,
      ∀ β, 0 < β → β ≤ 1 → β ≤ β₀ → ∀ (x z : ℕ → E n) (y : ℕ → E m),
        IsRun f A b ℓ u Γ p c α β x y z → y 0 = y0 → ∀ t,
          phi f A b Γ p xs xst (x t) (z t) (y t) -
              phi f A b Γ p xs xst (x (t + 1)) (z (t + 1)) (y (t + 1)) ≥
            1 / (8 * c) * ‖x t - x (t + 1)‖ ^ 2 + α / 2 * ‖A (xs (y (t + 1)) (z t)) - b‖ ^ 2
              + p / (6 * β) * ‖z t - z (t + 1)‖ ^ 2 := by
  classical
  intro α hα hα4 y0
  have ha : Assump22a A b ℓ u := hA.1
  have hf : Assump22c f ℓ u L := hA.2.2
  have hpγ0 : 0 < p + γ := by linarith
  obtain ⟨xb, hxb, hAxb⟩ : ∃ xb ∈ box ℓ u, A xb = b := by
    obtain ⟨xb, hxb, h⟩ := intrinsicInterior_subset ha
    exact ⟨xb, hxb, sub_eq_zero.1 h⟩
  obtain ⟨Δ, σ5, hΔ, hσ5, hdual⟩ := ProxADMMLC.Conv.lemma_3_10_dual f A b ℓ u hℓu L hA γ hγ
    Γ p hΓ hp hpγ xs hxs xst hxst y0
  obtain ⟨δ7, hδ7, h37⟩ := ProxADMMLC.Conv.cor_3_7 f A b ℓ u hℓu ha L hf γ hγ Γ p c α hΓ hp hc
    hcL hpγ hα xs hxs y0 Δ hΔ
  obtain ⟨δ8, hδ8, h38⟩ := ProxADMMLC.Conv.cor_3_8 f A b ℓ u hℓu ha L hf γ hγ Γ p hΓ hp hpγ
    xs hxs xst hxst y0 (δ7 / 7) (by positivity)
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = min (min Δ δ7) δ8 := ⟨_, rfl⟩
  have hζ : 0 < ζ := by rw [hζdef]; exact lt_min (lt_min hΔ hδ7) hδ8
  have hζΔ : ζ ≤ Δ := by rw [hζdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hζ7 : ζ ≤ δ7 := by rw [hζdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hζ8 : ζ ≤ δ8 := by rw [hζdef]; exact min_le_right _ _
  obtain ⟨Mb2, hMb2⟩ : ∃ Mb2 : ℝ, Mb2 = ∑ i, (u i - ℓ i) ^ 2 := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb2 := by rw [hMb2]; positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ‖A‖ ^ 2 * σ5 ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have b1p : 0 < (p + γ) / (126 * p) := by positivity
  have b2p : 0 < ζ ^ 2 / (56 * c * p * (Mb2 + 1)) := by positivity
  have b3p : 0 < α * ζ ^ 2 / (14 * p * (Mb2 + 1)) := by positivity
  have b4p : 0 < α * (p + γ) ^ 2 / (14 * p * (S + 1)) := by positivity
  refine ⟨min (min (min ((p + γ) / (126 * p)) (ζ ^ 2 / (56 * c * p * (Mb2 + 1))))
    (α * ζ ^ 2 / (14 * p * (Mb2 + 1)))) (α * (p + γ) ^ 2 / (14 * p * (S + 1))),
    lt_min (lt_min (lt_min b1p b2p) b3p) b4p, ?_⟩
  intro β hβ hβ1 hββ₀ x z y hrun hy0 t
  have hb1 : β ≤ (p + γ) / (126 * p) :=
    hββ₀.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hb2 : β ≤ ζ ^ 2 / (56 * c * p * (Mb2 + 1)) :=
    hββ₀.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hb3 : β ≤ α * ζ ^ 2 / (14 * p * (Mb2 + 1)) :=
    hββ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb4 : β ≤ α * (p + γ) ^ 2 / (14 * p * (S + 1)) := hββ₀.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at hb1 hb2 hb3 hb4
  have hrun' := hrun
  obtain ⟨hx0, hz0, hstep⟩ := hrun'
  -- invariants of a run
  have hbox : ∀ s, x s ∈ box ℓ u ∧ z s ∈ box ℓ u := by
    intro s
    induction s with
    | zero => exact ⟨hx0, hz0⟩
    | succ s ih =>
      have hx1 : x (s + 1) ∈ box ℓ u := by
        rw [(hstep s).2.1]; exact E337Aux.boxProj_mem hℓu _
      exact ⟨hx1, by rw [(hstep s).2.2]; exact E337Aux.box_comb ih.2 hx1 hβ.le hβ1⟩
  have hyR : ∀ s, y s - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m) := by
    intro s
    induction s with
    | zero => rw [hy0, sub_self]; exact Submodule.zero_mem _
    | succ s ih =>
      have : y (s + 1) - y0 = (y s - y0) + (A : E n →ₗ[ℝ] E m) (α • (x s - xb)) := by
        rw [(hstep s).1]
        simp only [ContinuousLinearMap.coe_coe, map_smul, map_sub, hAxb]
        abel
      rw [this]
      exact Submodule.add_mem _ ih (LinearMap.mem_range_self _ _)
  -- the descent lemmas
  have h31 := ProxADMMLC.Conv.lemma_3_1 f A b ℓ u hℓu L hf Γ p c α β hΓ hp hc hcL hβ hβ1
    x z y hrun t
  have h32 := ProxADMMLC.Conv.lemma_3_2 f A b ℓ u Γ p c α β xs hxs x z y hrun t
  have h33 := ProxADMMLC.Conv.lemma_3_3 f A b ℓ u hℓu L hf γ hγ p hp hpγ xst hxst
    (z t) (hbox t).2 (z (t + 1)) (hbox (t + 1)).2
  have h35 := (ProxADMMLC.Conv.lemma_3_5 f A b ℓ u hℓu L hf γ hγ Γ p hΓ hp hpγ xs hxs xst hxst
    (z (t + 1)) (hbox (t + 1)).2 (z t) (hbox t).2 (y (t + 1)) (y (t + 1))).2.1
  have h310 := (ProxADMMLC.Conv.lemma_3_10_primal f A b ℓ u hℓu L hf γ hγ Γ p c α β hΓ hp hc
    hcL hpγ hβ hβ1 xs hxs x z y hrun t).1
  -- names
  set x0 := x t with hx0def
  set x1 := x (t + 1) with hx1def
  set z0 := z t with hz0def
  set z1 := z (t + 1) with hz1def
  set y1 := y (t + 1) with hy1def
  set xh := xs y1 z0 with hxhdef
  set x11 := xs y1 z1 with hx11def
  set xS := xst z0 with hxSdef
  set q := p / (p + γ) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hqβ : 126 * q * β ≤ 1 := by
    have e : 126 * q * β = (126 * p * β) / (p + γ) := by rw [hqdef]; ring
    rw [e, div_le_one hpγ0]; linarith
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = ‖x0 - x1‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = ‖A xh - b‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = ‖z0 - z1‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ee, hEd⟩ : ∃ Ee : ℝ, Ee = ‖xh - xS‖ ^ 2 := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXd]; positivity
  have hR0 : 0 ≤ R := by rw [hRd]; positivity
  have hW0 : 0 ≤ W := by rw [hWd]; positivity
  have hE0 : 0 ≤ Ee := by rw [hEd]; positivity
  have hxhB : xh ∈ box ℓ u := (hxs y1 z0).1
  have hxSB : xS ∈ box ℓ u := (hxst z0).1.1
  have hEM : Ee ≤ Mb2 := by rw [hEd, hMb2]; exact E337Aux.box_diam hxhB hxSB
  -- (3.25)
  obtain ⟨v, hvd⟩ : ∃ v : E n, v = z1 - z0 := ⟨_, rfl⟩
  have hvW : ‖v‖ ^ 2 = W := by rw [hvd, hWd, norm_sub_rev]
  have hvW' : ‖z1 - z0‖ = ‖v‖ := by rw [hvd]
  have hid : z1 + z0 - (2 : ℝ) • x11 =
      v + (2 : ℝ) • (z0 - xS) - (2 : ℝ) • (x11 - xh) - (2 : ℝ) • (xh - xS) := by
    rw [hvd]; module
  have hI : inner ℝ (z1 - z0) (z1 + z0 - (2 : ℝ) • x11) = W + 2 * inner ℝ v (z0 - xS)
      - 2 * inner ℝ v (x11 - xh) - 2 * inner ℝ v (xh - xS) := by
    rw [hid, ← hvd]
    simp only [inner_sub_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hvW]
  rw [hI] at h32
  rw [← hvd, show ‖z0 - z1‖ ^ 2 = W from hWd.symm] at h33
  rw [← hXd, ← hWd] at h31
  set i1 := inner ℝ v (x11 - xh) with hi1
  set i2 := inner ℝ v (xh - xS) with hi2
  set i3 := inner ℝ v (z0 - xS) with hi3
  set a := A x0 - b with had
  set r := A xh - b with hrd
  have B1 : i1 ≤ q * W := by
    rw [hvW'] at h35
    calc i1 ≤ ‖v‖ * ‖x11 - xh‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * (q * ‖v‖) := mul_le_mul_of_nonneg_left h35 (norm_nonneg _)
      _ = q * W := by rw [← hvW]; ring
  have F2 : 2 * i2 ≤ W / (7 * β) + 7 * β * Ee := by
    have h1 := real_inner_le_norm v (xh - xS)
    have h2 := sq_nonneg (‖v‖ - 7 * β * ‖xh - xS‖)
    have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 14 * β)
    have h3 : 14 * β * i2 ≤ W + 49 * β ^ 2 * Ee := by
      rw [← hvW, hEd]; linear_combination h1' + h2
    rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]
    linear_combination h3
  have B3 : ‖a‖ ^ 2 = ‖a - r‖ ^ 2 + 2 * inner ℝ a r - R := by
    have := norm_sub_sq_real a r
    rw [hRd]; linarith
  have B4 : ‖a - r‖ ≤ ‖A‖ * ‖x0 - xh‖ := by
    have : a - r = A (x0 - xh) := by rw [had, hrd, map_sub]; abel
    rw [this]; exact A.le_opNorm _
  have F1 : α * ‖a - r‖ ^ 2 ≤ X / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    have s1 : ‖a - r‖ ^ 2 ≤ (‖A‖ * ‖x0 - xh‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) B4 2
    have s2 : (c * (p + γ) * ‖x0 - xh‖) ^ 2 ≤ X := by
      rw [hXd, norm_sub_rev x0 x1]
      exact pow_le_pow_left₀ (by positivity) h310 2
    have s3 : 4 * c * ‖A‖ ^ 2 * α * ‖x0 - xh‖ ^ 2 ≤ (c * (p + γ)) ^ 2 * ‖x0 - xh‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hα4.le (by positivity)
    have s1' := mul_le_mul_of_nonneg_left s1 (by positivity : (0 : ℝ) ≤ 4 * c * α)
    linear_combination s1' + s3 + s2
  have F3 : p / (2 * β) * W - p * (W / (7 * β)) - p / (3 * β) * W ≥ 3 * p * q * W := by
    have e : p / (2 * β) * W - p * (W / (7 * β)) - p / (3 * β) * W = p * W / (42 * β) := by
      field_simp; ring
    rw [e, ge_iff_le, le_div_iff₀ (by positivity)]
    have h' := mul_le_mul_of_nonneg_left hqβ (mul_nonneg hp.le hW0)
    linear_combination h'
  have F0 : 1 / (2 * c) * X = 2 * (X / (4 * c)) := by field_simp; ring
  have pB1 := mul_le_mul_of_nonneg_left B1 hp.le
  have pF2 := mul_le_mul_of_nonneg_left F2 hp.le
  have h325 : phi f A b Γ p xs xst x0 z0 (y t) - phi f A b Γ p xs xst x1 z1 y1 ≥
      X / (4 * c) + α * R + p / (3 * β) * W - 7 * p * β * Ee := by
    simp only [phi]
    linear_combination h31 + 2 * h32 + 2 * h33 + F1 + F3 + 2 * pB1 + pF2 + α * B3
  rw [← hXd, ← hRd, ← hWd]
  refine E337Aux.final_arith hc hp hα hβ hX0 hR0 hW0 hE0 hEM h325 ?_
  intro hcA hcB hcC
  have hx0B : x0 ∈ box ℓ u := (hbox t).1
  have hz0B : z0 ∈ box ℓ u := (hbox t).2
  have hpβ0 : 0 ≤ p * β := by positivity
  -- small residuals (3.28)-(3.29)
  have hXζ : X < ζ ^ 2 := by
    have k : 0 ≤ 56 * c * p * β := by positivity
    have : 56 * c * p * β * Mb2 ≤ ζ ^ 2 := by linear_combination hb2 + k
    linarith
  have hRζ : R < ζ ^ 2 := by
    have k : 0 ≤ 14 * p * β := by positivity
    have : α * R < α * ζ ^ 2 := by linear_combination hcB + hb3 + k
    exact lt_of_mul_lt_mul_left this hα.le
  have hdx : ‖x0 - x1‖ < ζ := by
    rw [hXd] at hXζ; exact lt_of_pow_lt_pow_left₀ 2 hζ.le hXζ
  have hdr : ‖r‖ < ζ := by
    rw [hRd] at hRζ; exact lt_of_pow_lt_pow_left₀ 2 hζ.le hRζ
  -- Corollary 3.8: x(y⁺, z) is close to x*(z)
  have hE8 : ‖xh - xS‖ < δ7 / 7 := h38 z0 hz0B y1 (hyR (t + 1)) (hdr.trans_le hζ8)
  -- (3.30): ‖x⁺ - z‖ is small
  have hzx : ‖z0 - x1‖ < δ7 := by
    have hzz : z0 - z1 = -(β • (x1 - z0)) := by
      rw [hz1def, (hstep t).2.2]; abel
    have hW' : W = β ^ 2 * ‖z0 - x1‖ ^ 2 := by
      rw [hWd, hzz, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ, norm_sub_rev x1 z0]
      ring
    have h1 : ‖z0 - x1‖ ^ 2 < 42 * Ee := by
      rw [hW'] at hcC
      have hb2' : 0 < β ^ 2 := by positivity
      have : β ^ 2 * ‖z0 - x1‖ ^ 2 < β ^ 2 * (42 * Ee) := by linear_combination hcC
      exact lt_of_mul_lt_mul_left this hb2'.le
    have h2 : Ee < (δ7 / 7) ^ 2 := by
      rw [hEd]; exact pow_lt_pow_left₀ hE8 (norm_nonneg _) (by norm_num)
    have k := sq_nonneg δ7
    have h3 : ‖z0 - x1‖ ^ 2 < δ7 ^ 2 := by linear_combination h1 + 42 * h2 + (1 / 7) * k
    exact lt_of_pow_lt_pow_left₀ 2 hδ7.le h3
  -- Corollary 3.7: z is close to X*
  have hyP : yPlus A b α x0 (y t) = y1 := by
    rw [hy1def, (hstep t).1]; rfl
  have hxP : xPlus f A b ℓ u Γ p c α x0 z0 (y t) = x1 := by
    unfold xPlus; rw [hyP, hx1def, (hstep t).2.1]
  have h37' := h37 x0 hx0B z0 hz0B (y t) (hyR t) (by
    rw [hxP, hyP]
    exact max_lt (max_lt (hdx.trans_le hζ7) hzx) (hdr.trans_le hζ7))
  have hzX : Metric.infDist z0 (Xstar f A b ℓ u) ≤ Δ := ((le_max_right _ _).trans_lt h37').le
  -- the dual error bound (3.15) and (3.12)
  have hD := hdual y1 z0 (hyR (t + 1)) hz0B (hdr.le.trans hζΔ) hzX
  have h312 := ProxADMMLC.Conv.eq_3_12_dist f A b ℓ u hℓu L hf γ hγ Γ p hΓ hp hpγ xs hxs xst
    hxst z0 hz0B y1
  have k0 : (p + γ) * ‖xh - xS‖ ≤ ‖A‖ * σ5 * ‖r‖ := by
    calc (p + γ) * ‖xh - xS‖ ≤ ‖A‖ * Metric.infDist y1 (Ystar f A ℓ u p xst z0) := h312
      _ ≤ ‖A‖ * (σ5 * ‖r‖) := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ = ‖A‖ * σ5 * ‖r‖ := by ring
  have k1 : (p + γ) ^ 2 * Ee ≤ S * R := by
    have := pow_le_pow_left₀ (by positivity) k0 2
    rw [hEd, hS, hRd]
    linear_combination this
  have k1' := mul_le_mul_of_nonneg_left k1 (by positivity : (0 : ℝ) ≤ 14 * p * β)
  have k2 := mul_le_mul_of_nonneg_right hb4 hR0
  have k3 : 0 ≤ 14 * p * β * R := by positivity
  have k4 : (p + γ) ^ 2 * (14 * p * β * Ee) ≤ (p + γ) ^ 2 * (α * R) := by
    linear_combination k2 + k3 + k1'
  exact le_of_mul_le_mul_left k4 (by positivity)
