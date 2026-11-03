-- Prove2me | solution 1 for ProblemSpec.Equilibrium.eq_A_2_A_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T03:54:40.928186+00:00
-- url     : https://prove2.me/submissions/fe8b515d-8194-4773-a99b-1ea52fa119ca

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model
import Theorems.Thm_ProblemSpec_Equilibrium_eq_A_3
import Theorems.Thm_ProblemSpec_Equilibrium_rg_lt_rbar

namespace Aux_PS_eqA23

open ProblemSpec.Equilibrium

lemma right_nonpos {f : ℝ → ℝ} {a f' b : ℝ} (hf : HasDerivAt f f' a) (hab : a < b)
    (h : ∀ x, a < x → x < b → f x ≤ f a) : f' ≤ 0 := by
  have h1 := hf.hasDerivWithinAt (s := Set.Ioi a)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h1
  apply le_of_tendsto h1
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [h x hx.1 hx.2]) (by linarith [hx.1])

lemma left_nonneg {f : ℝ → ℝ} {a f' b : ℝ} (hf : HasDerivAt f f' a) (hab : b < a)
    (h : ∀ x, b < x → x < a → f x ≤ f a) : 0 ≤ f' := by
  have h1 := hf.hasDerivWithinAt (s := Set.Iio a)
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h1
  apply ge_of_tendsto h1
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (by linarith [h x hx.1 hx.2]) (by linarith [hx.2])

lemma gen (m C a : ℝ) (Q : ℝ → ℝ) (r : ℝ) (hm : 0 < m) (hC : 0 < C) (hQ : HasDerivAt Q a r) :
    HasDerivAt (fun x => m * Real.exp (Q x) / (m * Real.exp (Q x) + C))
      (m * Real.exp (Q r) * a * C / (m * Real.exp (Q r) + C) ^ 2) r := by
  have h1 := hQ.exp.const_mul m
  have h2 := h1.add_const C
  have hne : m * Real.exp (Q r) + C ≠ 0 := by positivity
  have := h1.div h2 hne
  refine this.congr_deriv ?_
  ring

lemma value (m e a N : ℝ) (hm : 0 < m) (he : 0 < e) (hN : 1 < N) :
    m * e * a * ((N - 1) * m * e) / (m * e + (N - 1) * m * e) ^ 2 = a * ((N - 1) / N ^ 2) := by
  have hN0 : N ≠ 0 := by linarith
  have : m * e + (N - 1) * m * e = N * (m * e) := by ring
  rw [this]
  have : m * e ≠ 0 := by positivity
  field_simp

/-- Upper branch of the payoff (valid for `x ≥ Sr`). -/
noncomputable def Gp (P : Params) (Sr Sg N r m : ℝ) (x : ℝ) : ℝ :=
  m * Real.exp ((Sr * P.w + (x - Sr) * P.ν * P.w) / P.μ) /
    (m * Real.exp ((Sr * P.w + (x - Sr) * P.ν * P.w) / P.μ) +
      (N - 1) * m * Real.exp (quality P Sr r / P.μ)) * P.A
  - (P.cg * (x - Sr) + P.c1 * Sr + P.c2 * (1 / P.p) ^ x + P.h Sg * m)

/-- Lower branch of the payoff (valid for `x ≤ Sr`). -/
noncomputable def Gm (P : Params) (Sr Sg N r m : ℝ) (x : ℝ) : ℝ :=
  m * Real.exp (x * P.w / P.μ) /
    (m * Real.exp (x * P.w / P.μ) + (N - 1) * m * Real.exp (quality P Sr r / P.μ)) * P.A
  - (P.cg * 0 + P.c1 * Sr + P.c2 * (1 / P.p) ^ x + P.h Sg * m)

lemma Gp_eq (P : Params) (Sr Sg N r m x : ℝ) (hx : Sr ≤ x) :
    payoff P Sr Sg N x m r m = Gp P Sr Sg N r m x := by
  unfold payoff winProb cost Gp
  have hq : quality P Sr x = Sr * P.w + (x - Sr) * P.ν * P.w := by
    unfold quality
    split_ifs with h
    · have : x = Sr := le_antisymm h hx
      subst this; ring
    · rfl
  rw [hq, max_eq_left (by linarith)]

lemma Gm_eq (P : Params) (Sr Sg N r m x : ℝ) (hx : x ≤ Sr) :
    payoff P Sr Sg N x m r m = Gm P Sr Sg N r m x := by
  unfold payoff winProb cost Gm
  have hq : quality P Sr x = x * P.w := by
    unfold quality; rw [if_pos hx]
  rw [hq, max_eq_right (by linarith)]

lemma Gp_deriv (P : Params) (hP : P.Standing) (Sr Sg N r m : ℝ) (hN : 1 < N) (hm : 0 < m)
    (hr : Sr ≤ r) :
    HasDerivAt (Gp P Sr Sg N r m)
      (P.ν * P.w / P.μ * ((N - 1) / N ^ 2) * P.A
        - (P.cg + P.c2 * ((1 / P.p) ^ r * Real.log (1 / P.p)))) r := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, hh, hhanti⟩ := hP
  have hC : 0 < (N - 1) * m * Real.exp (quality P Sr r / P.μ) := by
    have : 0 < N - 1 := by linarith
    positivity
  have hQ : HasDerivAt (fun x : ℝ => (Sr * P.w + (x - Sr) * P.ν * P.w) / P.μ)
      (1 * P.ν * P.w / P.μ) r :=
    ((((hasDerivAt_id' (x := r)).sub_const Sr).mul_const P.ν).mul_const P.w).const_add
      (Sr * P.w) |>.div_const P.μ
  have hg := gen m _ _ _ r hm hC hQ
  have hqr : (Sr * P.w + (r - Sr) * P.ν * P.w) / P.μ = quality P Sr r / P.μ := by
    unfold quality
    split_ifs with h
    · have : r = Sr := le_antisymm h hr
      subst this; ring
    · rfl
  rw [hqr, value m _ _ N hm (Real.exp_pos _) hN] at hg
  have hpow := (Real.hasStrictDerivAt_const_rpow (by positivity : (0:ℝ) < 1 / P.p) r).hasDerivAt
  have hcost : HasDerivAt (fun x : ℝ => P.cg * (x - Sr) + P.c1 * Sr + P.c2 * (1 / P.p) ^ x
      + P.h Sg * m) (P.cg * 1 + P.c2 * ((1 / P.p) ^ r * Real.log (1 / P.p))) r := by
    have := ((((hasDerivAt_id' (x := r)).sub_const Sr).const_mul P.cg).add_const (P.c1 * Sr)).add
      (hpow.const_mul P.c2)
    exact (this.add_const (P.h Sg * m))
  have := (hg.mul_const P.A).sub hcost
  refine this.congr_deriv ?_
  ring

lemma Gm_deriv (P : Params) (hP : P.Standing) (Sr Sg N r m : ℝ) (hN : 1 < N) (hm : 0 < m)
    (hr : r ≤ Sr) :
    HasDerivAt (Gm P Sr Sg N r m)
      (P.w / P.μ * ((N - 1) / N ^ 2) * P.A
        - (P.c2 * ((1 / P.p) ^ r * Real.log (1 / P.p)))) r := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, hh, hhanti⟩ := hP
  have hC : 0 < (N - 1) * m * Real.exp (quality P Sr r / P.μ) := by
    have : 0 < N - 1 := by linarith
    positivity
  have hQ : HasDerivAt (fun x : ℝ => x * P.w / P.μ) (1 * P.w / P.μ) r :=
    ((hasDerivAt_id' (x := r)).mul_const P.w).div_const P.μ
  have hg := gen m _ _ _ r hm hC hQ
  have hqr : r * P.w / P.μ = quality P Sr r / P.μ := by
    unfold quality; rw [if_pos hr]
  rw [hqr, value m _ _ N hm (Real.exp_pos _) hN] at hg
  have hpow := (Real.hasStrictDerivAt_const_rpow (by positivity : (0:ℝ) < 1 / P.p) r).hasDerivAt
  have hcost : HasDerivAt (fun x : ℝ => P.cg * 0 + P.c1 * Sr + P.c2 * (1 / P.p) ^ x
      + P.h Sg * m) (P.c2 * ((1 / P.p) ^ r * Real.log (1 / P.p))) r := by
    have := (hpow.const_mul P.c2).const_add (P.cg * 0 + P.c1 * Sr)
    exact (this.add_const (P.h Sg * m))
  have := (hg.mul_const P.A).sub hcost
  refine this.congr_deriv ?_
  ring

lemma L_pos (P : Params) (hP : P.Standing) : 0 < L P := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, hh, hhanti⟩ := hP
  unfold L
  apply Real.log_pos
  rw [lt_div_iff₀ hp0]; linarith

/-- The upper marginal payoff equals `c2 L (rgArg − (1/p)^r)`. -/
lemma Dp_eq (P : Params) (hP : P.Standing) (N r : ℝ) :
    P.ν * P.w / P.μ * ((N - 1) / N ^ 2) * P.A
        - (P.cg + P.c2 * ((1 / P.p) ^ r * Real.log (1 / P.p)))
      = P.c2 * L P * (rgArg P N - (1 / P.p) ^ r) := by
  have hL := L_pos P hP
  obtain ⟨hA, hw, hμ, hc2, _⟩ := hP
  unfold rgArg
  have : Real.log (1 / P.p) = L P := rfl
  rw [this]
  field_simp
  ring

lemma Dm_eq (P : Params) (hP : P.Standing) (N r : ℝ) :
    P.w / P.μ * ((N - 1) / N ^ 2) * P.A
        - (P.c2 * ((1 / P.p) ^ r * Real.log (1 / P.p)))
      = P.c2 * L P * (rbarArg P N - (1 / P.p) ^ r) := by
  have hL := L_pos P hP
  obtain ⟨hA, hw, hμ, hc2, _⟩ := hP
  unfold rbarArg
  have : Real.log (1 / P.p) = L P := rfl
  rw [this]
  field_simp

lemma pow_eq_exp (P : Params) (hP : P.Standing) (r : ℝ) :
    (1 / P.p) ^ r = Real.exp (L P * r) := by
  obtain ⟨hA, hw, hμ, hc2, _, _, ⟨hp0, hp1⟩, _⟩ := hP
  rw [Real.rpow_def_of_pos (by positivity)]
  rfl

/-- `X ≤ (1/p)^r` with `X > 0` iff `log X / L ≤ r`. -/
lemma le_pow_iff (P : Params) (hP : P.Standing) (X r : ℝ) (hX : 0 < X) :
    X ≤ (1 / P.p) ^ r ↔ Real.log X / L P ≤ r := by
  have hL := L_pos P hP
  rw [pow_eq_exp P hP, div_le_iff₀ hL, ← Real.log_le_iff_le_exp hX, mul_comm]

lemma pow_le_iff (P : Params) (hP : P.Standing) (X r : ℝ) (hX : 0 < X) :
    (1 / P.p) ^ r ≤ X ↔ r ≤ Real.log X / L P := by
  have hL := L_pos P hP
  rw [pow_eq_exp P hP, le_div_iff₀ hL, ← Real.le_log_iff_exp_le hX, mul_comm]

lemma rbarArg_pos (P : Params) (hP : P.Standing) (N : ℝ) (hN : 1 < N) : 0 < rbarArg P N := by
  have hL := L_pos P hP
  obtain ⟨hA, hw, hμ, hc2, _⟩ := hP
  unfold rbarArg
  have : 0 < N - 1 := by linarith
  have : 0 < N ^ 2 := by positivity
  positivity

end Aux_PS_eqA23

open ProblemSpec.Equilibrium Aux_PS_eqA23 in
theorem solution (P : Params) (hP : P.Standing) (Sr Sg N r m : ℝ) (hSr : 0 ≤ Sr)
    (hSg : 0 ≤ Sg) (hN : 1 < N) (hrbar : 0 ≤ rbar P N) (heq : IsSymEq P Sr Sg N r m) :
    r = rstar P N Sr ∧ m = mstar P Sg N := by
  obtain ⟨hr0, hm, hdev⟩ := heq
  have hL := L_pos P hP
  have hc2 : 0 < P.c2 := hP.2.2.2.1
  have hc2L : 0 < P.c2 * L P := mul_pos hc2 hL
  have hbarpos := rbarArg_pos P hP N hN
  refine ⟨?_, ?_⟩
  · -- the number of objectives
    -- payoff deviations in `ri` with `mi = m`
    have hdev' : ∀ x, 0 ≤ x → payoff P Sr Sg N x m r m ≤ payoff P Sr Sg N r m r m :=
      fun x hx => hdev x m hx hm
    rcases lt_trichotomy Sr r with hlt | heqr | hgt
    · -- r > Sr: interior first-order condition on the upper branch
      have hd := Gp_deriv P hP Sr Sg N r m hN hm hlt.le
      have hmax : IsLocalMax (Gp P Sr Sg N r m) r := by
        filter_upwards [Ioi_mem_nhds hlt] with x hx
        rw [← Gp_eq P Sr Sg N r m x hx.le, ← Gp_eq P Sr Sg N r m r hlt.le]
        exact hdev' x (by linarith [hx.out])
      have h0 := hmax.hasDerivAt_eq_zero hd
      rw [Dp_eq P hP N r] at h0
      have hgeq : rgArg P N = (1 / P.p) ^ r := by
        rcases mul_eq_zero.1 h0 with h | h
        · linarith
        · linarith
      have hgpos : 0 < rgArg P N := by
        rw [hgeq]; exact Real.rpow_pos_of_pos (by have := hP.2.2.2.2.2.2.1.1; positivity) _
      have hrg : rg P N = r := by
        unfold rg
        apply le_antisymm
        · exact (le_pow_iff P hP _ r hgpos).1 hgeq.le
        · exact (pow_le_iff P hP _ r hgpos).1 hgeq.ge
      have hG : Guessing P N Sr := ⟨hgpos, by rw [hrg]; exact hlt⟩
      unfold rstar; rw [if_pos hG, hrg]
    · -- r = Sr: kink
      subst heqr
      have hnotG : ¬ Guessing P N Sr := by
        rintro ⟨hgpos, hlt⟩
        have hd := Gp_deriv P hP Sr Sg N Sr m hN hm le_rfl
        have := right_nonpos hd (lt_add_one Sr) (fun x hx _ => by
          rw [← Gp_eq P Sr Sg N Sr m x hx.le, ← Gp_eq P Sr Sg N Sr m Sr le_rfl]
          exact hdev' x (by linarith))
        rw [Dp_eq P hP N Sr] at this
        have h2 : rgArg P N ≤ (1 / P.p) ^ Sr := by
          by_contra hc
          push Not at hc
          have : 0 < P.c2 * L P * (rgArg P N - (1 / P.p) ^ Sr) := mul_pos hc2L (by linarith)
          linarith
        have := (le_pow_iff P hP _ Sr hgpos).1 h2
        unfold rg at hlt
        linarith
      have hle : Sr ≤ rbar P N := by
        rcases eq_or_lt_of_le hSr with h0 | hpos
        · rw [← h0]; exact hrbar
        · have hd := Gm_deriv P hP Sr Sg N Sr m hN hm le_rfl
          have := left_nonneg hd hpos (fun x hx hx2 => by
            rw [← Gm_eq P Sr Sg N Sr m x hx2.le, ← Gm_eq P Sr Sg N Sr m Sr le_rfl]
            exact hdev' x hx.le)
          rw [Dm_eq P hP N Sr] at this
          have h2 : (1 / P.p) ^ Sr ≤ rbarArg P N := by
            by_contra hc
            push Not at hc
            have : P.c2 * L P * (rbarArg P N - (1 / P.p) ^ Sr) < 0 :=
              mul_neg_of_pos_of_neg hc2L (by linarith)
            linarith
          exact (pow_le_iff P hP _ Sr hbarpos).1 h2
      unfold rstar; rw [if_neg hnotG, if_pos hle]
    · -- r < Sr
      have hrb : r = rbar P N := by
        rcases eq_or_lt_of_le hr0 with h0 | hpos
        · -- boundary r = 0
          subst h0
          have hd := Gm_deriv P hP Sr Sg N 0 m hN hm hgt.le
          have := right_nonpos hd hgt (fun x hx hx2 => by
            rw [← Gm_eq P Sr Sg N 0 m x hx2.le, ← Gm_eq P Sr Sg N 0 m 0 hgt.le]
            exact hdev' x hx.le)
          rw [Dm_eq P hP N 0] at this
          have h2 : rbarArg P N ≤ (1 / P.p) ^ (0:ℝ) := by
            by_contra hc
            push Not at hc
            have : 0 < P.c2 * L P * (rbarArg P N - (1 / P.p) ^ (0:ℝ)) := mul_pos hc2L (by linarith)
            linarith
          have := (le_pow_iff P hP _ 0 hbarpos).1 h2
          unfold rbar at hrbar ⊢
          linarith
        · have hd := Gm_deriv P hP Sr Sg N r m hN hm hgt.le
          have hmax : IsLocalMax (Gm P Sr Sg N r m) r := by
            filter_upwards [Ioo_mem_nhds hpos hgt] with x hx
            rw [← Gm_eq P Sr Sg N r m x hx.2.le, ← Gm_eq P Sr Sg N r m r hgt.le]
            exact hdev' x hx.1.le
          have h0 := hmax.hasDerivAt_eq_zero hd
          rw [Dm_eq P hP N r] at h0
          have hbeq : rbarArg P N = (1 / P.p) ^ r := by
            rcases mul_eq_zero.1 h0 with h | h
            · linarith
            · linarith
          unfold rbar
          apply le_antisymm
          · exact (pow_le_iff P hP _ r hbarpos).1 hbeq.ge
          · exact (le_pow_iff P hP _ r hbarpos).1 hbeq.le
      have hnotG : ¬ Guessing P N Sr := by
        rintro ⟨hgpos, hlt⟩
        have := ProblemSpec.Equilibrium.rg_lt_rbar P hP N hN hgpos
        linarith
      have hnle : ¬ Sr ≤ rbar P N := by rw [← hrb]; linarith
      unfold rstar; rw [if_neg hnotG, if_neg hnle, hrb]
  · -- the number of trials: interior FOC in `mi`
    obtain ⟨hd, hiff⟩ := ProblemSpec.Equilibrium.eq_A_3 P hP Sr Sg N r m hSg hN hm
    have hmax : IsLocalMax (fun x => payoff P Sr Sg N r x r m) m := by
      filter_upwards [Ioi_mem_nhds hm] with x hx
      exact hdev r x hr0 hx
    exact hiff.1 (hmax.hasDerivAt_eq_zero hd)
