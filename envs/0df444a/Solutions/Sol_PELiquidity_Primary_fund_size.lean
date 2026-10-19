-- Prove2me | solution 1 for PELiquidity.Primary.fund_size
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:23:09.592683+00:00
-- url     : https://prove2.me/submissions/4bb6b6a5-3260-4419-9edc-11bd85554cb5

-- Research directed by Alexander Richard Towell (queelius); Lean proof by OpenAI Codex.
-- Mathematical source: Vincent Maurin, David T. Robinson and Per Strömberg, December 2020.
-- Platform definitions and formulation: mikedeng1; statement review: Shuze Chen.
-- Formal foundations: Lean and Mathlib contributors.
import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting
import Definitions.Def_PELiquidity_Primary_Market
set_option autoImplicit false
set_option maxHeartbeats 1000000
open PELiquidity.Primary
namespace PEFinance
lemma gross_pos (lam δ : ℝ) (hl0 : 0<lam) (hl1 : lam<1) (hd0 : 0<δ) (hd1 : δ<1) :
    0<1-lam*(1-δ) ∧ 0<grossReturn lam δ := by
  have hp := mul_pos hl0 hd0
  have hh : 0<1-lam*(1-δ) := by nlinarith
  exact ⟨hh,one_div_pos.mpr hh⟩
lemma feasible_equations (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hr : 0<r) (h : IsFeasibleContract P r k x I f) :
    0<I ∧ 0<P.p*P.R-expectedFee P.p P.p f ∧ P.p*P.R-expectedFee P.p P.p f<r ∧
      expectedFee P.p P.p f*I=(P.p*P.R-r)*I+r*P.A := by
  have hI : P.A<I := h.2.2.2.2.1
  have he := h.2.2.2.2.2.1
  have hI0 : 0<I := P.hA.trans hI
  have hp : 0<P.p*P.R-expectedFee P.p P.p f := by
    apply (mul_pos_iff_of_pos_right hI0).mp
    rw [he];exact mul_pos hr (sub_pos.mpr hI)
  have hh : P.p*P.R-expectedFee P.p P.p f<r := by
    have hpos := mul_pos hr P.hA
    nlinarith
  refine ⟨hI0,hp,hh,?_⟩
  nlinarith [he]
lemma fee_order (P : Params) (r k x I x' I' : ℝ) (f f' : Outcome → ℝ)
    (hr : 0<r) (h : IsFeasibleContract P r k x I f) (h' : IsFeasibleContract P r k x' I' f') :
    expectedFee P.p P.p f≤expectedFee P.p P.p f' ↔ I'≤I := by
  have ha := feasible_equations P r k x I f hr h
  have hb := feasible_equations P r k x' I' f' hr h'
  have he : (expectedFee P.p P.p f'-expectedFee P.p P.p f)*(I*I')=r*P.A*(I-I') := by
    have h1 := congrArg (fun v : ℝ => v*I') ha.2.2.2
    have h2 := congrArg (fun v : ℝ => v*I) hb.2.2.2
    nlinarith only [h1,h2]
  constructor
  · intro hf
    have hp := mul_nonneg (sub_nonneg.mpr hf) (mul_pos ha.1 hb.1).le
    rw [he] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mul_pos hr P.hA)).mp hp)
  · intro hI
    have hp := mul_nonneg (mul_pos hr P.hA).le (sub_nonneg.mpr hI)
    rw [← he] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (mul_pos ha.1 hb.1)).mp hp)
lemma fee_size_tradeoff (P : Params) (δ : ℝ) (hδ0 : 0<δ) (hδ1 : δ<1)
    (hCost : grossReturn P.lam δ<P.p*P.R) :
    let Rbar := grossReturn P.lam δ
    let c := δ*Rbar
    (∀ x I f,IsFeasibleContract P Rbar c x I f → gpProfit P I f=P.p*P.R*I-Rbar*(I-P.A)) ∧
    (∀ x I f,IsOptimalContract P Rbar c x I f ↔
      (IsFeasibleContract P Rbar c x I f ∧ ∀ x' I' f',IsFeasibleContract P Rbar c x' I' f' →
        expectedFee P.p P.p f≤expectedFee P.p P.p f')) := by
  dsimp only
  have hr := (gross_pos P.lam δ P.hlam0 P.hlam1 hδ0 hδ1).2
  constructor
  · intro x I f h
    have he := (feasible_equations P _ _ x I f hr h).2.2.2
    unfold gpProfit
    nlinarith
  · intro x I f
    constructor
    · rintro ⟨h,hopt⟩
      refine ⟨h,?_⟩
      intro x' I' f' h'
      apply (fee_order P _ _ x I x' I' f f' hr h h').mpr
      have hval := hopt x' I' f' h'
      have ha := (feasible_equations P _ _ x I f hr h).2.2.2
      have hb := (feasible_equations P _ _ x' I' f' hr h').2.2.2
      nlinarith
    · rintro ⟨h,hmin⟩
      refine ⟨h,?_⟩
      intro x' I' f' h'
      have hi := (fee_order P _ _ x I x' I' f f' hr h h').mp (hmin x' I' f' h')
      have ha := (feasible_equations P _ _ x I f hr h).2.2.2
      have hb := (feasible_equations P _ _ x' I' f' hr h').2.2.2
      have hp := mul_nonneg (sub_nonneg.mpr hCost.le) (sub_nonneg.mpr hi)
      nlinarith
lemma fund_size (P : Params) (muH : ℝ) (E : Allocation)
    (hmu0 : 0 < muH) (hmu1 : muH < 1) (hE : IsEquilibrium P muH E)
    (hαL : E.αL=0) (hRH : grossReturn P.lam P.δH<E.RH) :
    let pledge := P.p*P.R-expectedFee P.p P.p E.fH
    0<pledge ∧ pledge<E.RH ∧ muH*P.K=E.IH-P.A ∧
      E.IH-P.A=pledge*P.A/(E.RH-pledge) ∧
      StrictAntiOn (fun Rb : ℝ => pledge*P.A/(Rb-pledge)) (Set.Ioi pledge) := by
  dsimp only
  have hg := gross_pos P.lam P.δH P.hlam0 P.hlam1 P.hδH0 P.hδH1
  have hr : 0<E.RH := hg.2.trans hRH
  have hf := hE.2.1.1
  have hfe := feasible_equations P E.RH (P.δH*E.RH) E.xH E.IH E.fH hr hf
  have haH : E.αH=1 := by linarith [hE.2.2.2.2.1]
  have hv : 1<(1-P.lam)*E.RH+P.lam*(P.δH*E.RH) := by
    unfold grossReturn at hRH
    have hh := (div_lt_iff₀ hg.1).mp hRH
    nlinarith
  have hs := hE.2.2.2.2.2.2.2.2.2.2 hv
  rw [haH,one_mul] at hs
  refine ⟨hfe.2.1,hfe.2.2.1,hs.symm,?_,?_⟩
  · apply (eq_div_iff (ne_of_gt (sub_pos.mpr hfe.2.2.1))).mpr
    have he := hf.2.2.2.2.2.1
    nlinarith
  · intro a ha b hb hab
    apply (div_lt_div_iff₀ (sub_pos.mpr hb) (sub_pos.mpr ha)).mpr
    have hp := mul_pos (mul_pos hfe.2.1 P.hA) (sub_pos.mpr hab)
    nlinarith
end PEFinance


/-- (C.4), Case 2 of Proposition 2: when only H-funds are raised and their
return exceeds H-LPs' break-even return, the H capital supply is `μ_H K`.
Market clearing and (3) give `μ_H K = I_H - A = (pR - f̄_H) A /
(R̄_H - (pR - f̄_H))`. For a fixed fee the contribution falls strictly as
the promised return rises. -/
theorem solution (P : Params) (muH : ℝ) (E : Allocation)
    (hmu0 : 0 < muH) (hmu1 : muH < 1) (hE : IsEquilibrium P muH E)
    (hαL : E.αL = 0) (hRH : grossReturn P.lam P.δH < E.RH) :
    let pledge := P.p * P.R - expectedFee P.p P.p E.fH
    0 < pledge ∧ pledge < E.RH ∧
    muH * P.K = E.IH - P.A ∧
    E.IH - P.A = pledge * P.A / (E.RH - pledge) ∧
    StrictAntiOn (fun Rb : ℝ => pledge * P.A / (Rb - pledge))
      (Set.Ioi pledge) := by
  exact PEFinance.fund_size P muH E hmu0 hmu1 hE hαL hRH


