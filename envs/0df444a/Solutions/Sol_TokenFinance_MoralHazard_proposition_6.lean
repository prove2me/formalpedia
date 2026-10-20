-- Prove2me | solution 1 for TokenFinance.MoralHazard.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T12:34:21.309784+00:00
-- url     : https://prove2.me/submissions/d07051a6-c73d-4c37-923d-c42e42dfeb20

/-
DS19H proof of the MoralHazard milestone TokenFinance.MoralHazard.proposition_6
(theorem_id 8e54b51e-4f43-4610-819b-e7f9ff3604a0), Proposition 6 / equation (24).

Mathematics.  Put L = θh − c > 0, a = 2√D, δ = a/L and λ = (θl − c)/L.
The accepted platform milestone eq_48 gives
  E_{θh}[max(π^m − D,0)] = NPV_h  and  NPV_h = L³/(12θh)·(1−δ)²(1+2δ).
The low-demand payoff max(π^m − D,0) vanishes for every x ≤ θl exactly when
θl ≤ c + a, i.e. λ ≤ δ.  In that case the effort condition reduces to
NPV_h − Ce ≥ 0, which is one of the standing assumptions, and the same D
witnesses DebtFinanceable.  When δ < λ, the tail integral gives
  E_{θl}[max(π^m − D,0)] = L³/(12θl)·(λ−δ)²(λ+2δ),
and substituting the closed form of NPV_h turns the effort condition into (24).
Finally δ < 1 follows from NPV_h > 0: D ≥ L²/4 would make min(π^m,D)=π^m
everywhere, hence C₀ = E_{θh}[π^m] and NPV_h = 0.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable
import Theorems.Thm_TokenFinance_MoralHazard_eq_48

open TokenFinance.MoralHazard

private lemma expect_debtEnt_eq_zero (c D θ : ℝ) (hD : 0 ≤ D)
    (hθ0 : 0 ≤ θ) (hθle : θ ≤ c + 2 * Real.sqrt D) :
    TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.debtEnt c D x) = 0 := by
  have hpos : 0 ≤ 2 * Real.sqrt D := by positivity
  have hsq : (2 * Real.sqrt D) ^ 2 = 4 * D := by
    have := Real.sq_sqrt hD
    nlinarith
  have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) θ, TokenFinance.Debt.debtEnt c D x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le hθ0] at hx
    have hxle : x ≤ θ := hx.2
    have hx' : x - c ≤ 2 * Real.sqrt D := by linarith
    have hpimle : TokenFinance.Debt.pim c x ≤ D := by
      unfold TokenFinance.Debt.pim
      have h0 : 0 ≤ max (x - c) 0 := le_max_right _ _
      have h1 : max (x - c) 0 ≤ 2 * Real.sqrt D := max_le hx' hpos
      have h2 : (max (x - c) 0) ^ 2 ≤ (2 * Real.sqrt D) ^ 2 := by nlinarith
      nlinarith
    unfold TokenFinance.Debt.debtEnt
    exact max_eq_right (by linarith)
  unfold TokenFinance.Debt.expect
  rw [intervalIntegral.integral_congr hzeroAux, intervalIntegral.integral_zero]
  exact zero_div θ

private lemma expect_debtEnt_eq_tail (c D θ : ℝ) (hc0 : 0 ≤ c) (hD : 0 ≤ D)
    (haθ : c + 2 * Real.sqrt D ≤ θ) :
    TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.debtEnt c D x)
      = ((θ - c) ^ 3 / 12 - D * (θ - c) + (2 * Real.sqrt D) ^ 3 / 6) / θ := by
  set a : ℝ := 2 * Real.sqrt D with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    positivity
  have ha2 : a ^ 2 = 4 * D := by
    rw [hadef]
    have := Real.sq_sqrt hD
    nlinarith
  have hD4 : D = a ^ 2 / 4 := by linarith
  have hca : c + a ≤ θ := by rw [hadef]; exact haθ
  have hdebtEntcont : Continuous fun x : ℝ => TokenFinance.Debt.debtEnt c D x := by
    unfold TokenFinance.Debt.debtEnt TokenFinance.Debt.pim
    fun_prop
  have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) (c + a),
      TokenFinance.Debt.debtEnt c D x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ c + a)] at hx
    -- (c ≥ 0 and a ≥ 0 give the lower endpoint bound)
    have hxle : x ≤ c + a := hx.2
    have hxle' : x - c ≤ a := by linarith
    have hpimle : TokenFinance.Debt.pim c x ≤ D := by
      unfold TokenFinance.Debt.pim
      have h0 : 0 ≤ max (x - c) 0 := le_max_right _ _
      have h1 : max (x - c) 0 ≤ a := max_le hxle' ha0
      have h2 : (max (x - c) 0) ^ 2 ≤ a ^ 2 := by nlinarith
      nlinarith
    unfold TokenFinance.Debt.debtEnt
    exact max_eq_right (by linarith)
  have hzero : ∫ x in (0 : ℝ)..(c + a), TokenFinance.Debt.debtEnt c D x = 0 := by
    rw [intervalIntegral.integral_congr hzeroAux]
    exact intervalIntegral.integral_zero
  have hcong : ∀ x ∈ Set.uIcc (c + a) θ,
      TokenFinance.Debt.debtEnt c D x = (x - c) ^ 2 / 4 - D := by
    intro x hx
    rw [Set.uIcc_of_le hca] at hx
    have hxge : c + a ≤ x := hx.1
    have hge : 0 ≤ x - c := by linarith
    have hpimge : D ≤ TokenFinance.Debt.pim c x := by
      unfold TokenFinance.Debt.pim
      have h1 : a ≤ max (x - c) 0 := le_max_of_le_left (by linarith)
      have h2 : a ^ 2 ≤ (max (x - c) 0) ^ 2 := by nlinarith
      nlinarith
    unfold TokenFinance.Debt.debtEnt
    rw [max_eq_left (by linarith)]
    unfold TokenFinance.Debt.pim
    rw [max_eq_left hge]
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
  have htail : ∫ x in (c + a)..θ, ((x - c) ^ 2 / 4 - D)
      = (θ - c) ^ 3 / 12 - D * (θ - c) - (a ^ 3 / 12 - D * a) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hdcont.intervalIntegrable _ _)]
    ring
  have hsplit : (∫ x in (0 : ℝ)..(c + a), TokenFinance.Debt.debtEnt c D x)
      + (∫ x in (c + a)..θ, TokenFinance.Debt.debtEnt c D x)
      = ∫ x in (0 : ℝ)..θ, TokenFinance.Debt.debtEnt c D x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hdebtEntcont.intervalIntegrable 0 (c + a))
      (hdebtEntcont.intervalIntegrable (c + a) θ)
  have hfull : ∫ x in (0 : ℝ)..θ, TokenFinance.Debt.debtEnt c D x
      = (θ - c) ^ 3 / 12 - D * (θ - c) + a ^ 3 / 6 := by
    rw [← hsplit, hzero, zero_add,
      intervalIntegral.integral_congr hcong, htail, hD4]
    ring
  unfold TokenFinance.Debt.expect
  rw [hfull]

theorem solution (c C0 Ce θl θh D δ lam : ℝ) (hA : MHAssumptions c C0 Ce θl θh)
    (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) (hlam : lam = (θl - c) / (θh - c)) :
    (lam ≤ δ →
      TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) - Ce ≥ TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D) ∧
        DebtFinanceable c C0 Ce θl θh) ∧
    (δ < lam →
      (TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) - Ce ≥ TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D) ↔
        TokenFinance.Debt.npv c C0 θh - Ce ≥
          (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) * (θh / θl) *
            TokenFinance.Debt.npv c C0 θh)) := by
  obtain ⟨hc, hcθl, hθlθh, hC0, hnpvl, hnpvh, hCe⟩ := hA
  have hcθh : c < θh := lt_trans hcθl hθlθh
  have hθh : 0 < θh := lt_trans hc hcθh
  have hθl : 0 < θl := lt_trans hc hcθl
  have hL : 0 < θh - c := by linarith
  have hLne : θh - c ≠ 0 := ne_of_gt hL
  have hθlne : θl ≠ 0 := ne_of_gt hθl
  have hθhne : θh ≠ 0 := ne_of_gt hθh
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (by positivity) hL.le
  -- delta < 1, as in the accepted lemma_6: otherwise debt pays pi^m everywhere
  have hδ1 : δ < 1 := by
    have hDlt : D < (θh - c) ^ 2 / 4 := by
      by_contra hcon
      have hge : (θh - c) ^ 2 / 4 ≤ D := le_of_not_gt hcon
      have hpoint : ∀ x ∈ Set.uIcc (0 : ℝ) θh,
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
        exact min_eq_left (le_trans hpimle hge)
      have hCE : C0 = TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) := by
        rw [← hBE]
        unfold TokenFinance.Debt.expect
        rw [intervalIntegral.integral_congr hpoint]
      have hnpv0 : TokenFinance.Debt.npv c C0 θh = 0 := by
        unfold TokenFinance.Debt.npv
        linarith
      linarith
    have hsqrt_lt : Real.sqrt D < (θh - c) / 2 := by
      rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < (θh - c) / 2)]
      nlinarith
    rw [hδ, div_lt_one hL]
    nlinarith
  have h48 := TokenFinance.MoralHazard.eq_48 c C0 θh D δ hc hcθh hC0 hnpvh hD hBE hδ
  have hEθh : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D)
      = TokenFinance.Debt.npv c C0 θh := h48.1
  have hNP : TokenFinance.Debt.npv c C0 θh
      = (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := h48.2
  have hfactor : (1 - 3 * δ ^ 2 + 2 * δ ^ 3) = (1 - δ) ^ 2 * (1 + 2 * δ) := by ring
  have hθl_eq : θl - c = lam * (θh - c) := by
    rw [hlam]
    field_simp [hLne]
  constructor
  · -- case lambda <= delta
    intro hlamδ
    have hle : θl ≤ c + 2 * Real.sqrt D := by
      have h1 : lam * (θh - c) ≤ δ * (θh - c) :=
        mul_le_mul_of_nonneg_right hlamδ hL.le
      have h2 : δ * (θh - c) = 2 * Real.sqrt D := by
        rw [hδ]
        field_simp [hLne]
      have : θl - c ≤ 2 * Real.sqrt D := by rw [hθl_eq]; linarith
      linarith
    have hzero := expect_debtEnt_eq_zero c D θl hD (le_of_lt hθl) hle
    have hinc : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtEnt c D) - Ce ≥
        TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D) := by
      rw [hzero, hEθh]
      linarith
    exact ⟨hinc, ⟨D, hD, hBE, hinc⟩⟩
  · -- case delta < lambda
    intro hδlam
    have hgt : c + 2 * Real.sqrt D < θl := by
      have h1 : δ * (θh - c) < lam * (θh - c) :=
        mul_lt_mul_of_pos_right hδlam hL
      have h2 : δ * (θh - c) = 2 * Real.sqrt D := by
        rw [hδ]
        field_simp [hLne]
      have : 2 * Real.sqrt D < θl - c := by rw [hθl_eq]; linarith
      linarith
    have htail := expect_debtEnt_eq_tail c D θl hc.le hD hgt.le
    -- normalize the low-demand payoff
    have hEql : TokenFinance.Debt.expect θl (TokenFinance.Debt.debtEnt c D)
        = (θh - c) ^ 3 / (12 * θl) * ((lam - δ) ^ 2 * (lam + 2 * δ)) := by
      set a : ℝ := 2 * Real.sqrt D with hadef
      have ha2 : a ^ 2 = 4 * D := by
        rw [hadef]
        have := Real.sq_sqrt hD
        nlinarith
      have haeq : a = δ * (θh - c) := by
        rw [hδ]
        field_simp [hLne]
      have hθl_eq' : θl - c = lam * (θh - c) := hθl_eq
      rw [htail, hθl_eq']
      have hD' : D = a ^ 2 / 4 := by linarith
      rw [hD', haeq]
      field_simp [hθlne]
      ring
    have hcoef : (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) *
          (θh / θl) * TokenFinance.Debt.npv c C0 θh
        = (θh - c) ^ 3 / (12 * θl) * ((lam - δ) ^ 2 * (lam + 2 * δ)) := by
      rw [hNP, hfactor]
      have h1d : (1 - δ) ≠ 0 := by linarith
      have h12 : 1 + 2 * δ ≠ 0 := by positivity
      field_simp [h1d, h12, hθlne, hθhne]
    constructor
    · intro hinc
      rw [hEql, hEθh] at hinc
      rw [hcoef]
      linarith
    · intro h24
      rw [hcoef] at h24
      rw [hEql, hEθh]
      linarith
