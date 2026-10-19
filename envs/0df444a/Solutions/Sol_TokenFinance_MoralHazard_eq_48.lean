-- Prove2me | solution 1 for TokenFinance.MoralHazard.eq_48
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T11:32:34.869915+00:00
-- url     : https://prove2.me/submissions/1b98f2f4-fb90-43cb-9185-d9538a4fdc17

/-
DS19D proof of the MoralHazard milestone TokenFinance.MoralHazard.eq_48
(theorem_id a33b285b-eda6-4bb7-bded-73eb1f7ff259), Appendix A, equation (48).

Mathematics.  Write L=θh−c, E=E_{θh}[π^m]=L³/(12θh), D the break-even face value
and a=2√D.  On the event π^m>D (i.e. x>c+a) the entrepreneur receives π^m−D,
else zero.  Since E[min(π^m,D)]=C₀, the entrepreneur's expected payoff is
E−C₀=NPV_h.  Also
  ∫_{c+a}^{θh} ((x−c)²/4−D) dx = L³/12 − a²L/4 + a³/6,
and dividing by θh and substituting a=δL gives
  NPV_h = L³/(12θh)·(1−3δ²+2δ³).
The strict inequality a<L follows from NPV_h>0: if D≥L²/4 then min(π^m,D)=π^m
everywhere and C₀=E, contradicting NPV_h=E−C₀>0.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

private lemma expect_pim (c θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    TokenFinance.Debt.expect θ (TokenFinance.Debt.pim c) = (θ - c) ^ 3 / (12 * θ) := by
  have hθ : 0 < θ := lt_trans hc hcθ
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hc0 : 0 ≤ c := le_of_lt hc
  have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) c, TokenFinance.Debt.pim c x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le hc0] at hx
    have hx' : x ≤ c := hx.2
    unfold TokenFinance.Debt.pim
    rw [max_eq_right (by linarith)]
    ring
  have hzero : ∫ x in (0 : ℝ)..c, TokenFinance.Debt.pim c x = 0 := by
    rw [intervalIntegral.integral_congr hzeroAux]
    exact intervalIntegral.integral_zero
  have hcong : ∀ x ∈ Set.uIcc c θ, TokenFinance.Debt.pim c x = (x - c) ^ 2 / 4 := by
    intro x hx
    rw [Set.uIcc_of_le hcθ.le] at hx
    have hge : 0 ≤ x - c := by linarith [hx.1]
    unfold TokenFinance.Debt.pim
    rw [max_eq_left hge]
  have hFcont : Continuous fun x : ℝ => (x - c) ^ 2 / 4 := by fun_prop
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (z - c) ^ 3 / 12)
      ((y - c) ^ 2 / 4) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => (z - c) ^ 3)
        ((3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1) y :=
      (hasDerivAt_id y).sub_const c |>.pow 3
    have hval : (3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1 / 12 = (y - c) ^ 2 / 4 := by
      norm_num
      ring
    rw [show (y - c) ^ 2 / 4 = (3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1 / 12 by
      rw [hval]]
    exact h1.div_const 12
  have hcalc : ∫ x in c..θ, (x - c) ^ 2 / 4 = (θ - c) ^ 3 / 12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hFcont.intervalIntegrable _ _)]
    ring
  have hpimcont : Continuous fun x : ℝ => TokenFinance.Debt.pim c x := by
    unfold TokenFinance.Debt.pim
    fun_prop
  have hsplit : (∫ x in (0 : ℝ)..c, TokenFinance.Debt.pim c x)
      + (∫ x in c..θ, TokenFinance.Debt.pim c x)
      = ∫ x in (0 : ℝ)..θ, TokenFinance.Debt.pim c x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hpimcont.intervalIntegrable 0 c) (hpimcont.intervalIntegrable c θ)
  unfold TokenFinance.Debt.expect
  rw [show (∫ x in (0 : ℝ)..θ, TokenFinance.Debt.pim c x)
      = ∫ x in c..θ, TokenFinance.Debt.pim c x by
    rw [← hsplit, hzero, zero_add]]
  rw [intervalIntegral.integral_congr hcong, hcalc]
  field_simp [hθne]

theorem solution (c C0 θh D δ : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hD : 0 ≤ D)
    (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) :
    TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) =
        TokenFinance.Debt.npv c C0 θh ∧
      TokenFinance.Debt.npv c C0 θh =
        (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := by
  have hθh : 0 < θh := lt_trans hc hcθ
  have hθhne : θh ≠ 0 := ne_of_gt hθh
  have hL : 0 < θh - c := by linarith
  have hLne : θh - c ≠ 0 := ne_of_gt hL
  have hE : TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c)
      = (θh - c) ^ 3 / (12 * θh) := expect_pim c θh hc hcθ
  set L : ℝ := θh - c with hLdef
  set a : ℝ := 2 * Real.sqrt D with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    positivity
  have ha2 : a ^ 2 = 4 * D := by
    rw [hadef]
    have := Real.sq_sqrt hD
    nlinarith
  have hD4 : D = a ^ 2 / 4 := by linarith
  -- pointwise split of the debt payoffs
  have hsum : ∀ x : ℝ, TokenFinance.Debt.debtEnt c D x
      = TokenFinance.Debt.pim c x - TokenFinance.Debt.debtInv c D x := by
    intro x
    unfold TokenFinance.Debt.debtEnt TokenFinance.Debt.debtInv
    by_cases h : TokenFinance.Debt.pim c x ≤ D
    · rw [min_eq_left h, max_eq_right (by linarith)]
      ring
    · have h' : D ≤ TokenFinance.Debt.pim c x := le_of_not_ge h
      rw [min_eq_right h', max_eq_left (by linarith)]
  have hpimcont : Continuous fun x : ℝ => TokenFinance.Debt.pim c x := by
    unfold TokenFinance.Debt.pim
    fun_prop
  have hdebtInvcont : Continuous fun x : ℝ => TokenFinance.Debt.debtInv c D x := by
    unfold TokenFinance.Debt.debtInv
    fun_prop
  have hdebtEntcont : Continuous fun x : ℝ => TokenFinance.Debt.debtEnt c D x := by
    unfold TokenFinance.Debt.debtEnt
    fun_prop
  -- first conjunct from additivity of the integral
  have hBE' : (∫ x in (0 : ℝ)..θh, TokenFinance.Debt.debtInv c D x) / θh = C0 := by
    simpa [TokenFinance.Debt.expect] using hBE
  have hfirst : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D)
      = TokenFinance.Debt.npv c C0 θh := by
    simp only [TokenFinance.Debt.expect, TokenFinance.Debt.npv]
    rw [intervalIntegral.integral_congr (fun x _ => hsum x)]
    rw [intervalIntegral.integral_sub (hpimcont.intervalIntegrable 0 θh)
      (hdebtInvcont.intervalIntegrable 0 θh)]
    rw [sub_div, hBE']
  refine ⟨hfirst, ?_⟩
  -- strict a < L from NPV_h > 0
  have hnpvE : TokenFinance.Debt.npv c C0 θh
      = TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) - C0 := rfl
  have hC0lt : C0 < TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) := by
    rw [hnpvE] at hnpv
    linarith
  have haL : a < L := by
    by_contra hcon
    have hLe : L ≤ a := le_of_not_gt hcon
    have hDa : (θh - c) ^ 2 / 4 ≤ D := by
      have hsq : L ^ 2 ≤ a ^ 2 := by nlinarith [ha0]
      rw [ha2] at hsq
      nlinarith
    have hmin : ∀ x ∈ Set.uIcc (0 : ℝ) θh,
        TokenFinance.Debt.debtInv c D x = TokenFinance.Debt.pim c x := by
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt hθh)] at hx
      have hxle : x ≤ θh := hx.2
      have hpimle : TokenFinance.Debt.pim c x ≤ (θh - c) ^ 2 / 4 := by
        unfold TokenFinance.Debt.pim
        have h1 : max (x - c) 0 ≤ θh - c := max_le (by linarith) hL.le
        have h0 : 0 ≤ max (x - c) 0 := le_max_right _ _
        nlinarith [sq_nonneg (max (x - c) 0)]
      unfold TokenFinance.Debt.debtInv
      exact min_eq_left (le_trans hpimle hDa)
    have hCE : C0 = TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) := by
      rw [← hBE]
      unfold TokenFinance.Debt.expect
      rw [intervalIntegral.integral_congr hmin]
    linarith
  -- the tail integral
  have hpos : 0 ≤ a := ha0
  have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) (c + a),
      TokenFinance.Debt.debtEnt c D x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ c + a)] at hx
    have hxle : x ≤ c + a := hx.2
    have hxle' : x - c ≤ a := by linarith
    have hpimle : TokenFinance.Debt.pim c x ≤ D := by
      unfold TokenFinance.Debt.pim
      have h0 : 0 ≤ max (x - c) 0 := le_max_right _ _
      have h1 : max (x - c) 0 ≤ a := max_le hxle' hpos
      nlinarith [sq_nonneg (max (x - c) 0)]
    unfold TokenFinance.Debt.debtEnt
    exact max_eq_right (by linarith)
  have hzero : ∫ x in (0 : ℝ)..(c + a), TokenFinance.Debt.debtEnt c D x = 0 := by
    rw [intervalIntegral.integral_congr hzeroAux]
    exact intervalIntegral.integral_zero
  have hcong : ∀ x ∈ Set.uIcc (c + a) θh,
      TokenFinance.Debt.debtEnt c D x = (x - c) ^ 2 / 4 - D := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : c + a ≤ θh)] at hx
    have hxge : c + a ≤ x := hx.1
    have hge : 0 ≤ x - c := by linarith
    have hpimge : D ≤ TokenFinance.Debt.pim c x := by
      unfold TokenFinance.Debt.pim
      have h1 : a ≤ max (x - c) 0 := le_max_of_le_left (by linarith)
      nlinarith [sq_nonneg (max (x - c) 0)]
    unfold TokenFinance.Debt.debtEnt
    rw [max_eq_left (by linarith)]
    unfold TokenFinance.Debt.pim
    rw [max_eq_left hge]
  have hFcont : Continuous fun x : ℝ => (x - c) ^ 3 / 12 - D * (x - c) := by fun_prop
  have hdcont : Continuous fun x : ℝ => (x - c) ^ 2 / 4 - D := by fun_prop
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (z - c) ^ 3 / 12 - D * (z - c))
      ((y - c) ^ 2 / 4 - D) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => (z - c) ^ 3)
        ((3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1) y :=
      (hasDerivAt_id y).sub_const c |>.pow 3
    have h2 : HasDerivAt (fun z : ℝ => D * (z - c)) (D * 1) y :=
      ((hasDerivAt_id y).sub_const c).const_mul D
    have hmain := (h1.div_const 12).sub h2
    have hscalar : (↑3 * (y - c) ^ (3 - 1) * 1) / 12 - D * 1 = (y - c) ^ 2 / 4 - D := by
      norm_num
      ring
    have hmain' := hmain.congr_deriv hscalar
    have hfun : ((fun x : ℝ => (x - c) ^ 3 / 12) - fun z : ℝ => D * (z - c))
        = fun z : ℝ => (z - c) ^ 3 / 12 - D * (z - c) := by
      ext z
      simp [Pi.sub_apply]
    rwa [hfun] at hmain'
  have htail : ∫ x in (c + a)..θh, ((x - c) ^ 2 / 4 - D)
      = (θh - c) ^ 3 / 12 - D * (θh - c) - ((a) ^ 3 / 12 - D * a) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hdcont.intervalIntegrable _ _)]
    ring
  have hsplit : (∫ x in (0 : ℝ)..(c + a), TokenFinance.Debt.debtEnt c D x)
      + (∫ x in (c + a)..θh, TokenFinance.Debt.debtEnt c D x)
      = ∫ x in (0 : ℝ)..θh, TokenFinance.Debt.debtEnt c D x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hdebtEntcont.intervalIntegrable 0 (c + a))
      (hdebtEntcont.intervalIntegrable (c + a) θh)
  have hfull : ∫ x in (0 : ℝ)..θh, TokenFinance.Debt.debtEnt c D x
      = (θh - c) ^ 3 / 12 - D * (θh - c) + a ^ 3 / 6 := by
    rw [← hsplit, hzero, zero_add,
      intervalIntegral.integral_congr hcong, htail, hD4]
    ring
  have hexpect : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D)
      = ((θh - c) ^ 3 / 12 - D * (θh - c) + a ^ 3 / 6) / θh := by
    unfold TokenFinance.Debt.expect
    rw [hfull]
  -- substitute a = δ L
  have haeq : a = δ * L := by
    rw [hδ]
    field_simp [hLne]
  have hnpvTail : TokenFinance.Debt.npv c C0 θh
      = (L ^ 3 / 12 - D * L + a ^ 3 / 6) / θh := by
    rw [← hfirst, hexpect, hLdef]
  rw [hnpvTail, hD4, haeq]
  field_simp [hθhne]
  ring
