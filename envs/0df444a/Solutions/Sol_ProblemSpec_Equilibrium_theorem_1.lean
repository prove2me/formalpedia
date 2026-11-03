-- Prove2me | solution 1 for ProblemSpec.Equilibrium.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T03:58:36.999082+00:00
-- url     : https://prove2.me/submissions/62fb44d2-d2b8-409a-b994-d389b142eb4b

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model
import Theorems.Thm_ProblemSpec_Equilibrium_eq_A_2_A_3
import Theorems.Thm_ProblemSpec_Equilibrium_sym_win_prob_entry_utility

namespace Aux_PS_thm1

open ProblemSpec.Equilibrium

lemma L_pos (P : Params) (hP : P.Standing) : 0 < L P := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, hh, hhanti⟩ := hP
  unfold L
  apply Real.log_pos
  rw [lt_div_iff₀ hp0]; linarith

lemma one_le_inv_p (P : Params) (hP : P.Standing) : 1 ≤ 1 / P.p := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, hh, hhanti⟩ := hP
  rw [le_div_iff₀ hp0]; linarith

lemma pow_eq_exp (P : Params) (hP : P.Standing) (r : ℝ) :
    (1 / P.p) ^ r = Real.exp (L P * r) := by
  obtain ⟨hA, hw, hμ, hc2, _, _, ⟨hp0, hp1⟩, _⟩ := hP
  rw [Real.rpow_def_of_pos (by positivity)]
  rfl

/-- `K(N) = (N−1)/N²`. -/
noncomputable def K (N : ℝ) : ℝ := (N - 1) / N ^ 2

noncomputable def α (P : Params) : ℝ := P.ν * P.w / P.μ * (P.A / P.c2) * (1 / L P)
noncomputable def β (P : Params) : ℝ := P.cg / P.c2 * (1 / L P)
noncomputable def α' (P : Params) : ℝ := P.w / P.μ * (P.A / P.c2) * (1 / L P)

lemma α_pos (P : Params) (hP : P.Standing) : 0 < α P := by
  have hL := L_pos P hP
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, _⟩ := hP
  unfold α; positivity

lemma α'_pos (P : Params) (hP : P.Standing) : 0 < α' P := by
  have hL := L_pos P hP
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, _⟩ := hP
  unfold α'; positivity

lemma rgArg_eq (P : Params) (N : ℝ) : rgArg P N = K N * α P - β P := by
  unfold rgArg K α β; ring

lemma rbarArg_eq (P : Params) (N : ℝ) : rbarArg P N = K N * α' P := by
  unfold rbarArg K α'; ring

lemma K_sub (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    K y - K x = (y - x) * (1 - (x - 1) * (y - 1)) / (x ^ 2 * y ^ 2) := by
  unfold K; field_simp; ring

lemma K_pos (x : ℝ) (hx : 1 < x) : 0 < K x := by
  unfold K; have : 0 < x - 1 := by linarith
  positivity

lemma K_lt_inc (x y : ℝ) (hx : 1 < x) (hxy : x < y) (hy : y ≤ 2) : K x < K y := by
  have h := K_sub x y (by linarith) (by linarith)
  have h1 : 0 < (y - x) * (1 - (x - 1) * (y - 1)) / (x ^ 2 * y ^ 2) := by
    apply div_pos
    · apply mul_pos (by linarith)
      nlinarith
    · have : 0 < x := by linarith
      have : 0 < y := by linarith
      positivity
  linarith

lemma K_lt_dec (x y : ℝ) (hx : 2 ≤ x) (hxy : x < y) : K y < K x := by
  have h := K_sub x y (by linarith) (by linarith)
  have h1 : (y - x) * (1 - (x - 1) * (y - 1)) / (x ^ 2 * y ^ 2) < 0 := by
    apply div_neg_of_neg_of_pos
    · apply mul_neg_of_pos_of_neg (by linarith)
      nlinarith
    · have : 0 < x := by linarith
      have : 0 < y := by linarith
      positivity
  linarith

/-- On `[a, b]` with `a > 1`, `K` is at least `min (K a) (K b)` (it is unimodal). -/
lemma K_ge_right (a b N : ℝ) (ha : 1 < a) (haN : a ≤ N) (hNb : N ≤ b) (hab : K b < K a) :
    K b ≤ K N := by
  by_cases h2 : N ≤ 2
  · rcases eq_or_lt_of_le haN with h | h
    · rw [← h]; exact hab.le
    · exact hab.le.trans (K_lt_inc a N ha h h2).le
  · push Not at h2
    rcases eq_or_lt_of_le hNb with h | h
    · rw [h]
    · exact (K_lt_dec N b h2.le h).le

/-- `h₀(N) = A/N² − cg r̄^g(N) − c2 · arg^g(N)`: the guessing-region utility minus `(cg − c1) Sr`. -/
noncomputable def h0 (P : Params) (N : ℝ) : ℝ :=
  P.A / N ^ 2 - P.cg * rg P N - P.c2 * rgArg P N

/-- The numerator of `h₀'`. -/
noncomputable def φ (P : Params) (N : ℝ) : ℝ :=
  -2 * P.A + (N - 2) * α P * (P.cg / (L P * rgArg P N) + P.c2)

lemma K_deriv (N : ℝ) (hN : N ≠ 0) : HasDerivAt K ((2 - N) / N ^ 3) N := by
  have := ((hasDerivAt_id N).sub_const 1).div (hasDerivAt_pow 2 N) (pow_ne_zero 2 hN)
  unfold K
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

lemma rgArg_deriv (P : Params) (N : ℝ) (hN : N ≠ 0) :
    HasDerivAt (rgArg P) ((2 - N) / N ^ 3 * α P) N := by
  have h := ((K_deriv N hN).mul_const (α P)).sub_const (β P)
  have he : rgArg P = fun N => K N * α P - β P := funext (rgArg_eq P)
  rw [he]; exact h

lemma h0_deriv (P : Params) (hP : P.Standing) (N : ℝ) (hN : 1 < N) (hg : 0 < rgArg P N) :
    HasDerivAt (h0 P) (φ P N / N ^ 3) N := by
  have hL := L_pos P hP
  have hN0 : N ≠ 0 := by linarith
  have hR := rgArg_deriv P N hN0
  have hlog := (hR.log hg.ne').div_const (L P)
  have hA := (hasDerivAt_const N P.A).div (hasDerivAt_pow 2 N) (pow_ne_zero 2 hN0)
  have h := (hA.sub (hlog.const_mul P.cg)).sub (hR.const_mul P.c2)
  have he : h0 P = fun N => P.A / N ^ 2 - P.cg * (Real.log (rgArg P N) / L P) - P.c2 * rgArg P N := by
    funext x; unfold h0 rg; rfl
  rw [he]
  refine h.congr_deriv ?_
  unfold φ
  field_simp
  ring

lemma rg_cont (P : Params) (hP : P.Standing) (N : ℝ) (hN : 1 < N) (hg : 0 < rgArg P N) :
    ContinuousAt (rg P) N := by
  have hR := rgArg_deriv P N (by linarith)
  have hlog := (hR.log hg.ne').div_const (L P)
  have he : rg P = fun N => Real.log (rgArg P N) / L P := by funext x; rfl
  rw [he]; exact hlog.continuousAt

lemma φ_strict (P : Params) (hP : P.Standing) (x y : ℝ) (hx : 2 < x) (hxy : x < y)
    (hgy : 0 < rgArg P y) : φ P x < φ P y := by
  have hL := L_pos P hP
  have hα := α_pos P hP
  have hc2 : 0 < P.c2 := hP.2.2.2.1
  have hcg : 0 < P.cg := lt_of_le_of_lt hP.2.2.2.2.2.1.1 hP.2.2.2.2.2.1.2
  have hK := K_lt_dec x y hx.le hxy
  have hgx : rgArg P y < rgArg P x := by
    rw [rgArg_eq, rgArg_eq]; nlinarith
  have hgx' : 0 < rgArg P x := by linarith
  have h1 : P.cg / (L P * rgArg P x) ≤ P.cg / (L P * rgArg P y) := by
    apply div_le_div_of_nonneg_left hcg.le (by positivity)
    exact mul_le_mul_of_nonneg_left hgx.le hL.le
  unfold φ
  have h2 : 0 < P.cg / (L P * rgArg P x) + P.c2 := by positivity
  have h3 : (x - 2) * α P * (P.cg / (L P * rgArg P x) + P.c2)
      < (y - 2) * α P * (P.cg / (L P * rgArg P y) + P.c2) := by
    have h4 : (x - 2) * α P < (y - 2) * α P := by nlinarith
    calc (x - 2) * α P * (P.cg / (L P * rgArg P x) + P.c2)
        < (y - 2) * α P * (P.cg / (L P * rgArg P x) + P.c2) := by
          exact mul_lt_mul_of_pos_right h4 h2
      _ ≤ (y - 2) * α P * (P.cg / (L P * rgArg P y) + P.c2) := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          have : 0 < y - 2 := by linarith
          positivity
  linarith

lemma φ_neg (P : Params) (hP : P.Standing) (x : ℝ) (hx : x ≤ 2) (hg : 0 < rgArg P x) :
    φ P x < 0 := by
  have hL := L_pos P hP
  have hα := α_pos P hP
  have hA : 0 < P.A := hP.1
  have hc2 : 0 < P.c2 := hP.2.2.2.1
  have hcg : 0 < P.cg := lt_of_le_of_lt hP.2.2.2.2.2.1.1 hP.2.2.2.2.2.1.2
  unfold φ
  have h2 : 0 < α P * (P.cg / (L P * rgArg P x) + P.c2) := by positivity
  nlinarith

/-- Utility in the guessing region. -/
lemma U_guess (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSg : 0 ≤ Sg) (hN : 1 < N)
    (hG : Guessing P N Sr) :
    entryUtility P Sr Sg N = h0 P N + (P.cg - P.c1) * Sr := by
  rw [(ProblemSpec.Equilibrium.sym_win_prob_entry_utility P hP Sr Sg N hSg hN).2]
  have hr : rstar P N Sr = rg P N := by unfold rstar; rw [if_pos hG]
  rw [hr, max_eq_left (by linarith [hG.2]), pow_eq_exp P hP]
  have hL := L_pos P hP
  have : L P * rg P N = Real.log (rgArg P N) := by
    unfold rg; field_simp
  rw [this, Real.exp_log hG.1]
  unfold h0; ring

/-- Utility outside the guessing region. -/
lemma U_nonguess (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSg : 0 ≤ Sg) (hN : 1 < N)
    (hG : ¬ Guessing P N Sr) :
    entryUtility P Sr Sg N = P.A / N ^ 2 - P.c1 * Sr - P.c2 * (1 / P.p) ^ (min Sr (rbar P N)) := by
  rw [(ProblemSpec.Equilibrium.sym_win_prob_entry_utility P hP Sr Sg N hSg hN).2]
  have hr : rstar P N Sr = min Sr (rbar P N) := by
    unfold rstar; rw [if_neg hG]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm
  rw [hr, max_eq_right (by linarith [min_le_left Sr (rbar P N)])]
  ring

lemma rbar_mono (P : Params) (hP : P.Standing) (x y : ℝ) (hx : 1 < x) (hK : K x ≤ K y) :
    rbar P x ≤ rbar P y := by
  have hL := L_pos P hP
  have ha := α'_pos P hP
  unfold rbar
  apply div_le_div_of_nonneg_right _ hL.le
  apply Real.log_le_log
  · rw [rbarArg_eq]; exact mul_pos (K_pos x hx) ha
  · rw [rbarArg_eq, rbarArg_eq]; exact mul_le_mul_of_nonneg_right hK ha.le

lemma rg_lt_of (P : Params) (hP : P.Standing) (x y : ℝ) (hgx : 0 < rgArg P x)
    (hlt : rgArg P x < rgArg P y) : rg P x < rg P y := by
  have hL := L_pos P hP
  unfold rg
  exact div_lt_div_of_pos_right (Real.log_lt_log hgx hlt) hL

lemma rg_le_of (P : Params) (hP : P.Standing) (x y : ℝ) (hgx : 0 < rgArg P x)
    (hle : rgArg P x ≤ rgArg P y) : rg P x ≤ rg P y := by
  have hL := L_pos P hP
  unfold rg
  exact div_le_div_of_nonneg_right (Real.log_le_log hgx hle) hL.le

/-- Non-guessing points: `N∗` does not increase. -/
lemma nonguess_core (P : Params) (hP : P.Standing) (Sg a b N1 N2 : ℝ) (hSg : 0 ≤ Sg)
    (hab : a < b) (hF1 : IsFreeEntry P a Sg N1) (hF2 : IsFreeEntry P b Sg N2)
    (hG1 : ¬ Guessing P N1 a) (hG2 : ¬ Guessing P N2 b) : N2 ≤ N1 := by
  obtain ⟨hN1, hU1, hU1'⟩ := hF1
  obtain ⟨hN2, hU2, hU2'⟩ := hF2
  by_contra hlt
  push Not at hlt
  have hA : 0 < P.A := hP.1
  have hc1 : 0 ≤ P.c1 := hP.2.2.2.2.2.1.1
  have hc2 : 0 < P.c2 := hP.2.2.2.1
  have hp := one_le_inv_p P hP
  rcases le_or_gt (K N1) (K N2) with hK | hK
  · have hrb := rbar_mono P hP N1 N2 hN1 hK
    have hmin : min a (rbar P N1) ≤ min b (rbar P N2) := min_le_min hab.le hrb
    have hpow : (1 / P.p) ^ (min a (rbar P N1)) ≤ (1 / P.p) ^ (min b (rbar P N2)) :=
      Real.rpow_le_rpow_of_exponent_le hp hmin
    have hsq : P.A / N2 ^ 2 < P.A / N1 ^ 2 := by
      apply div_lt_div_of_pos_left hA (by positivity)
      nlinarith
    rw [U_nonguess P hP a Sg N1 hSg hN1 hG1] at hU1
    rw [U_nonguess P hP b Sg N2 hSg hN2 hG2] at hU2
    nlinarith
  · have hG1' : ¬ Guessing P N2 a := by
      rintro ⟨hpos, hlt'⟩
      have hg : rgArg P N2 < rgArg P N1 := by
        rw [rgArg_eq, rgArg_eq]; nlinarith [α_pos P hP]
      exact hG1 ⟨by linarith, lt_trans hlt' (rg_lt_of P hP _ _ hpos hg)⟩
    have h := hU1' N2 hlt
    rw [U_nonguess P hP a Sg N2 hSg hN2 hG1'] at h
    rw [U_nonguess P hP b Sg N2 hSg hN2 hG2] at hU2
    have hmin : min a (rbar P N2) ≤ min b (rbar P N2) := min_le_min hab.le le_rfl
    have hpow : (1 / P.p) ^ (min a (rbar P N2)) ≤ (1 / P.p) ^ (min b (rbar P N2)) :=
      Real.rpow_le_rpow_of_exponent_le hp hmin
    nlinarith

/-- Guessing points: `N∗` strictly increases. -/
lemma guess_core (P : Params) (hP : P.Standing) (Sg a b N1 N2 : ℝ) (hSg : 0 ≤ Sg)
    (hab : a < b) (hF1 : IsFreeEntry P a Sg N1) (hF2 : IsFreeEntry P b Sg N2)
    (hG1 : Guessing P N1 a) (hG2 : Guessing P N2 b) : N1 < N2 := by
  obtain ⟨hN1, hU1, hU1'⟩ := hF1
  obtain ⟨hN2, hU2, hU2'⟩ := hF2
  have hcc : 0 < P.cg - P.c1 := by linarith [hP.2.2.2.2.2.1.2]
  have hα := α_pos P hP
  by_contra hle
  push Not at hle
  rcases le_or_gt (K N2) (K N1) with hK | hK
  · -- `b` is still a guessing point at `N1`
    have hg : rgArg P N2 ≤ rgArg P N1 := by
      rw [rgArg_eq, rgArg_eq]; nlinarith
    have hGb : Guessing P N1 b := ⟨lt_of_lt_of_le hG2.1 hg,
      lt_of_lt_of_le hG2.2 (rg_le_of P hP _ _ hG2.1 hg)⟩
    have hUb := U_guess P hP b Sg N1 hSg hN1 hGb
    rw [U_guess P hP a Sg N1 hSg hN1 hG1] at hU1
    have hlt : P.s < entryUtility P b Sg N1 := by
      rw [hUb, ← hU1]; nlinarith
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at hU2; linarith
    · linarith [hU2' N1 h]
  · -- the hard case: `N2 < N1`, `K N1 < K N2`
    have hlt : N2 < N1 := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [h] at hK; exact absurd hK (lt_irrefl _)
      · exact h
    have h2 : 2 < N1 := by
      by_contra h
      push Not at h
      exact absurd (K_lt_inc N2 N1 hN2 hlt h) (not_lt.2 hK.le)
    have hg1 : 0 < rgArg P N1 := hG1.1
    -- positivity of `rgArg` on `[N2, N1]`
    have hgI : ∀ N ∈ Set.Icc N2 N1, 0 < rgArg P N := by
      intro N hN
      have := K_ge_right N2 N1 N hN2 hN.1 hN.2 hK
      have : rgArg P N1 ≤ rgArg P N := by rw [rgArg_eq, rgArg_eq]; nlinarith
      linarith
    have hU1e := U_guess P hP a Sg N1 hSg hN1 hG1
    have hU2e := U_guess P hP b Sg N2 hSg hN2 hG2
    have hdiff : h0 P N2 < h0 P N1 := by nlinarith
    -- mean value theorem on `[N2, N1]`
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (h0 P) (fun N => φ P N / N ^ 3) hlt
      (fun x hx => (h0_deriv P hP x (by linarith [hx.1]) (hgI x hx)).continuousAt.continuousWithinAt)
      (fun x hx => h0_deriv P hP x (by linarith [hx.1]) (hgI x (Set.Ioo_subset_Icc_self hx)))
    have hξ1 : 1 < ξ := by linarith [hξ.1]
    have hgξ : 0 < rgArg P ξ := hgI ξ (Set.Ioo_subset_Icc_self hξ)
    have hslope : 0 < (h0 P N1 - h0 P N2) / (N1 - N2) := div_pos (by linarith) (by linarith)
    have hφξ : 0 < φ P ξ := by
      have h3 : 0 < ξ ^ 3 := by positivity
      have : 0 < φ P ξ / ξ ^ 3 := by rw [hξeq]; exact hslope
      exact (div_pos_iff_of_pos_right h3).1 this
    have hξ2 : 2 < ξ := by
      by_contra h
      push Not at h
      linarith [φ_neg P hP ξ h hgξ]
    have hφ1 : 0 < φ P N1 := lt_trans hφξ (φ_strict P hP ξ N1 hξ2 hξ.2 hg1)
    have hd1 := h0_deriv P hP N1 hN1 hg1
    have hpos : 0 < φ P N1 / N1 ^ 3 := div_pos hφ1 (by positivity)
    -- `h₀` exceeds `h₀(N1)` just to the right of `N1`
    have hs := hd1.hasDerivWithinAt (s := Set.Ioi N1)
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hs
    have ev1 : ∀ᶠ x in nhdsWithin N1 (Set.Ioi N1), 0 < slope (h0 P) N1 x :=
      hs.eventually (lt_mem_nhds hpos)
    have hcr := rg_cont P hP N1 hN1 hg1
    have hcg : ContinuousAt (rgArg P) N1 := (rgArg_deriv P N1 (by linarith)).continuousAt
    have ev2 : ∀ᶠ x in nhds N1, a < rg P x := hcr.eventually (lt_mem_nhds hG1.2)
    have ev3 : ∀ᶠ x in nhds N1, 0 < rgArg P x := hcg.eventually (lt_mem_nhds hg1)
    have ev4 : ∀ᶠ x in nhdsWithin N1 (Set.Ioi N1), N1 < x := self_mem_nhdsWithin
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ :=
      (ev1.and ((ev2.filter_mono nhdsWithin_le_nhds).and ((ev3.filter_mono nhdsWithin_le_nhds).and ev4))).exists
    have hhx : h0 P N1 < h0 P x := by
      rw [slope_def_field] at hx1
      have : 0 < h0 P x - h0 P N1 := by
        by_contra hc
        push Not at hc
        have : (h0 P x - h0 P N1) / (x - N1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hc (by linarith)
        linarith
      linarith
    have hGx : Guessing P x a := ⟨hx3, hx2⟩
    have := hU1' x hx4
    rw [U_guess P hP a Sg x hSg (by linarith) hGx] at this
    linarith

end Aux_PS_thm1

open ProblemSpec.Equilibrium Aux_PS_thm1 in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ Sr Sg N r m : ℝ, 0 ≤ Sr → 0 ≤ Sg → 1 < N → 0 ≤ rbar P N →
        IsSymEq P Sr Sg N r m → r = rstar P N Sr ∧ m = mstar P Sg N) ∧
    (∀ Sr Sg Sg' N : ℝ, 0 ≤ Sr → 0 ≤ Sg → 0 ≤ Sg' →
        (IsFreeEntry P Sr Sg N ↔ IsFreeEntry P Sr Sg' N)) ∧
    (∀ (Sg : ℝ) (Nstar : ℝ → ℝ) (S : Set ℝ), 0 ≤ Sg → S ⊆ Set.Ici 0 →
        (∀ Sr ∈ S, IsFreeEntry P Sr Sg (Nstar Sr) ∧ 0 ≤ rbar P (Nstar Sr)) →
        StrictMonoOn Nstar {Sr | Sr ∈ S ∧ Guessing P (Nstar Sr) Sr} ∧
        AntitoneOn Nstar {Sr | Sr ∈ S ∧ ¬ Guessing P (Nstar Sr) Sr}) ∧
    (∀ Sr Sg Sg' N r m r' m' : ℝ, 0 ≤ Sr → 0 ≤ Sg → Sg < Sg' → 1 < N → 0 ≤ rbar P N →
        IsSymEq P Sr Sg N r m → IsSymEq P Sr Sg' N r' m' → m < m' ∧ r = r') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Sr Sg N r m hSr hSg hN hrbar heq
    exact ProblemSpec.Equilibrium.eq_A_2_A_3 P hP Sr Sg N r m hSr hSg hN hrbar heq
  · intro Sr Sg Sg' N hSr hSg hSg'
    have key : ∀ N', 1 < N' → entryUtility P Sr Sg N' = entryUtility P Sr Sg' N' := by
      intro N' hN'
      rw [(ProblemSpec.Equilibrium.sym_win_prob_entry_utility P hP Sr Sg N' hSg hN').2,
        (ProblemSpec.Equilibrium.sym_win_prob_entry_utility P hP Sr Sg' N' hSg' hN').2]
    constructor
    · rintro ⟨hN, hU, hU'⟩
      refine ⟨hN, by rw [← key N hN]; exact hU, fun N' hN' => ?_⟩
      rw [← key N' (by linarith)]; exact hU' N' hN'
    · rintro ⟨hN, hU, hU'⟩
      refine ⟨hN, by rw [key N hN]; exact hU, fun N' hN' => ?_⟩
      rw [key N' (by linarith)]; exact hU' N' hN'
  · intro Sg Nstar S hSg hS hF
    constructor
    · intro a ha b hb hab
      exact guess_core P hP Sg a b (Nstar a) (Nstar b) hSg hab (hF a ha.1).1 (hF b hb.1).1 ha.2 hb.2
    · intro a ha b hb hab
      rcases eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact nonguess_core P hP Sg a b (Nstar a) (Nstar b) hSg h (hF a ha.1).1 (hF b hb.1).1
          ha.2 hb.2
  · intro Sr Sg Sg' N r m r' m' hSr hSg hSg' hN hrbar heq heq'
    obtain ⟨hr, hm⟩ := ProblemSpec.Equilibrium.eq_A_2_A_3 P hP Sr Sg N r m hSr hSg hN hrbar heq
    obtain ⟨hr', hm'⟩ :=
      ProblemSpec.Equilibrium.eq_A_2_A_3 P hP Sr Sg' N r' m' hSr (by linarith) hN hrbar heq'
    refine ⟨?_, by rw [hr, hr']⟩
    rw [hm, hm']
    have hA : 0 < P.A := hP.1
    have hh := hP.2.2.2.2.2.2.2.2.1
    have hanti := hP.2.2.2.2.2.2.2.2.2
    have h1 : P.h Sg' < P.h Sg := hanti (Set.mem_Ici.2 hSg) (Set.mem_Ici.2 (by linarith)) hSg'
    have h2 : 0 < P.h Sg' := hh Sg' (by linarith)
    unfold mstar
    apply div_lt_div_of_pos_left
    · have : 0 < N - 1 := by linarith
      positivity
    · positivity
    · exact mul_lt_mul_of_pos_left h1 (by positivity)
