-- Prove2me | solution 1 for PELiquidity.Secondary.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T10:53:49.661581+00:00
-- url     : https://prove2.me/submissions/6e5f5d3d-91df-415b-abc5-db29179fb2d0

-- Proposition 3 (Maurin, Robinson & Stromberg, A Theory of Liquidity in Private Equity, Dec 2020).
-- The contract-theory preliminaries (namespaces PEResearch/PEFinance/PEAlgebra) are adapted from the
-- accepted platform proof of PELiquidity.Primary.proposition_2 (submission 412af1a4, by queelius).
import Mathlib
import Definitions.Def_PELiquidity_Secondary_Market

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary
namespace PEResearch
lemma fee_expand (a b : ℝ) (f : Outcome → ℝ) :
    expectedFee a b f=a*b*f (true,true)+a*(1-b)*f (true,false)+(1-a)*b*f (false,true)+(1-a)*(1-b)*f (false,false) := by
  simp [expectedFee,Fintype.sum_prod_type,Fintype.sum_bool,outcomeProb]
  ring
lemma fee_zero (R x : ℝ) (f : Outcome → ℝ) (h : IsLimitedLiability R x f) : f (false,false)=0 := by
  have hh := h.1 (false,false)
  simp [cashFlow] at hh
  exact le_antisymm hh.2 hh.1
lemma fee_bounds (p q B R x : ℝ) (hq : 0<q) (hqp : q<p) (f : Outcome → ℝ)
    (hLL : IsLimitedLiability R x f) (hIC : IsIC p q B x f) :
    p^2*B/(p^2-q^2)≤expectedFee p p f ∧
    p*B/(p-q)*x≤expectedFee p p f ∧ p*B/(p-q)*(1-x)≤expectedFee p p f := by
  have hp : 0<p := hq.trans hqp
  have hd : 0<p-q := sub_pos.mpr hqp
  have hd2 : 0<p^2-q^2 := by nlinarith
  have hf0 := fee_zero R x f hLL
  have h01 := (hLL.1 (false,true)).1
  have h10 := (hLL.1 (true,false)).1
  have hqq := mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hIC.1)
  have hqp' := mul_nonneg hp.le (sub_nonneg.mpr hIC.2.1)
  have hpq := mul_nonneg hp.le (sub_nonneg.mpr hIC.2.2)
  have he0 : expectedFee p p f*(p^2-q^2)-p^2*B =
      p^2*(expectedFee p p f-(expectedFee q q f+B))+p*q*(f (true,false)+f (false,true))*(p-q) := by
    simp only [fee_expand,hf0];ring
  have he1 : expectedFee p p f*(p-q)-p*B*x =
      p*(expectedFee p p f-(expectedFee q p f+B*x))+p*(p-q)*f (false,true) := by
    simp only [fee_expand,hf0];ring
  have he2 : expectedFee p p f*(p-q)-p*B*(1-x) =
      p*(expectedFee p p f-(expectedFee p q f+B*(1-x)))+p*(p-q)*f (true,false) := by
    simp only [fee_expand,hf0];ring
  refine ⟨(div_le_iff₀ hd2).mpr ?_,?_,?_⟩
  · have hh : 0≤p*q*(f (true,false)+f (false,true))*(p-q) := by positivity
    linarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    have hh : 0≤p*(p-q)*f (false,true) := by positivity
    linarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    have hh : 0≤p*(p-q)*f (true,false) := by positivity
    linarith
noncomputable def feeMin (p q B x : ℝ) : ℝ :=
  max (p^2*B/(p^2-q^2)) (max (p*B/(p-q)*x) (p*B/(p-q)*(1-x)))
lemma fee_lower (p q B R x : ℝ) (hq : 0<q) (hqp : q<p) (f : Outcome → ℝ)
    (hLL : IsLimitedLiability R x f) (hIC : IsIC p q B x f) : feeMin p q B x≤expectedFee p p f := by
  have hh := fee_bounds p q B R x hq hqp f hLL hIC
  exact max_le hh.1 (max_le hh.2.1 hh.2.2)
lemma fee_basic (p q B R : ℝ) (hq : 0<q) (hqp : q<p) (hp1 : p≤1) (hB : 0<B)
    (hLL : B≤p*(p-q)*R) :
    0<R ∧ 0<p*B/(p-q) ∧ p^2*B/(p^2-q^2)≤p*B/(p-q) ∧ p*B/(p-q)≤p^2*R := by
  have hp : 0<p := hq.trans hqp
  have hd : 0<p-q := sub_pos.mpr hqp
  have hd2 : 0<p^2-q^2 := by nlinarith
  have hR : 0<R := (mul_pos_iff_of_pos_left (mul_pos hp hd)).mp (hB.trans_le hLL)
  refine ⟨hR,div_pos (mul_pos hp hB) hd,?_,?_⟩
  · apply (div_le_div_iff₀ hd2 hd).mpr
    have hh := mul_nonneg (mul_nonneg hp.le hB.le) (mul_nonneg hq.le hd.le)
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hLL hp.le
    nlinarith
noncomputable def bothFee (v : ℝ) (w : Outcome) : ℝ := if w.1 && w.2 then v else 0
lemma both_expand (a b v : ℝ) : expectedFee a b (bothFee v)=a*b*v := by simp [fee_expand,bothFee]
lemma both_liability (R x v : ℝ) (hR : 0<R) (hx0 : 0<x) (hx1 : x<1) (hv0 : 0≤v) (hvR : v≤R) :
    IsLimitedLiability R x (bothFee v) := by
  have hRx := mul_pos hR hx0
  have hR1 := mul_pos hR (sub_pos.mpr hx1)
  constructor
  · rintro ⟨a,b⟩
    cases a <;> cases b <;> simp [bothFee,cashFlow]
    all_goals try constructor
    all_goals nlinarith
  · rintro ⟨a,b⟩ ⟨a',b'⟩ he
    cases a <;> cases b <;> cases a' <;> cases b' <;> simp [cashFlow,bothFee,ne_of_gt hR,ne_of_gt hx0,ne_of_gt (sub_pos.mpr hx1)] at he ⊢ <;> nlinarith
lemma both_IC (p q B x v : ℝ) (hq : 0<q) (hqp : q<p)
    (h0 : p^2*B/(p^2-q^2)≤p^2*v)
    (h1 : p*B/(p-q)*x≤p^2*v) (h2 : p*B/(p-q)*(1-x)≤p^2*v) :
    IsIC p q B x (bothFee v) := by
  have hp : 0<p := hq.trans hqp
  have hd : 0<p-q := sub_pos.mpr hqp
  have hd2 : 0<p^2-q^2 := by nlinarith
  have H0 := (div_le_iff₀ hd2).mp h0
  rw [div_mul_eq_mul_div] at h1 h2
  have H1 := (div_le_iff₀ hd).mp h1
  have H2 := (div_le_iff₀ hd).mp h2
  unfold IsIC
  simp only [both_expand]
  refine ⟨?_,?_,?_⟩
  · have hh : 0≤p^2*((p^2-q^2)*v-B) := by nlinarith only [H0]
    have he := (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hp)).mp hh
    nlinarith only [he]
  · have hh : 0≤p*((p-q)*p*v-B*x) := by nlinarith only [H1]
    have he := (mul_nonneg_iff_of_pos_left hp).mp hh
    nlinarith only [he]
  · have hh : 0≤p*((p-q)*p*v-B*(1-x)) := by nlinarith only [H2]
    have he := (mul_nonneg_iff_of_pos_left hp).mp hh
    nlinarith only [he]
lemma interior_fee_attained (p q B R x : ℝ) (hq : 0<q) (hqp : q<p) (hp1 : p≤1)
    (hB : 0<B) (hLL : B≤p*(p-q)*R) (hx0 : 0<x) (hx1 : x<1) :
    ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧ expectedFee p p f=feeMin p q B x := by
  have hp : 0<p := hq.trans hqp
  have hd : 0<p-q := sub_pos.mpr hqp
  have hd2 : 0<p^2-q^2 := by nlinarith
  have hb := fee_basic p q B R hq hqp hp1 hB hLL
  have hF0 : 0≤feeMin p q B x := le_trans (by positivity) (le_max_left _ _)
  have hFcap : feeMin p q B x≤p*B/(p-q) := by
    apply max_le hb.2.2.1
    apply max_le
    · exact mul_le_of_le_one_right hb.2.1.le hx1.le
    · exact mul_le_of_le_one_right hb.2.1.le (by linarith)
  let v := feeMin p q B x/p^2
  have hv0 : 0≤v := div_nonneg hF0 (sq_nonneg _)
  have hvR : v≤R := (div_le_iff₀ (sq_pos_of_pos hp)).mpr (by nlinarith [hFcap.trans hb.2.2.2])
  have hv : p^2*v=feeMin p q B x := by dsimp [v];field_simp
  refine ⟨bothFee v,both_liability R x v hb.1 hx0 hx1 hv0 hvR,?_,?_⟩
  · apply both_IC p q B x v hq hqp <;> rw [hv]
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · rw [both_expand];nlinarith [hv]
end PEResearch
namespace PEResearch
noncomputable def oneFee (t : Bool) (v : ℝ) (w : Outcome) : ℝ := if (if t then w.1 else w.2) then v else 0
lemma one_expand (t : Bool) (a b v : ℝ) : expectedFee a b (oneFee t v)=(if t then a else b)*v := by
  cases t <;> simp [fee_expand,oneFee] <;> ring
lemma endpoint_attained (p q B R : ℝ) (hq : 0<q) (hqp : q<p) (hp1 : p≤1)
    (hB : 0<B) (hLL : B≤p*(p-q)*R) (t : Bool) :
    ∃ f : Outcome → ℝ,IsLimitedLiability R (if t then 1 else 0) f ∧
      IsIC p q B (if t then 1 else 0) f ∧ expectedFee p p f=p*B/(p-q) := by
  have hp : 0<p := hq.trans hqp
  have hd : 0<p-q := sub_pos.mpr hqp
  have hb := fee_basic p q B R hq hqp hp1 hB hLL
  let v := B/(p-q)
  have hv0 : 0≤v := div_nonneg hB.le hd.le
  have hvR : v≤R := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_right hp1 (mul_pos hd hb.1).le
    nlinarith [hLL]
  have hv : (p-q)*v=B := by dsimp [v];field_simp
  refine ⟨oneFee t v,?_,?_,?_⟩
  · constructor
    · rintro ⟨a,b⟩
      cases t <;> cases a <;> cases b <;> simp [cashFlow,oneFee,hv0,hvR]
    · rintro ⟨a,b⟩ ⟨a',b'⟩ he
      cases t <;> cases a <;> cases b <;> cases a' <;> cases b' <;>
        simp [cashFlow,oneFee,ne_of_gt hb.1] at he ⊢ <;> linarith [hb.1]
  · cases t <;> simp only [IsIC,one_expand,Bool.false_eq_true,ite_false,ite_true,mul_zero,mul_one,sub_zero,sub_self,add_zero]
    all_goals constructor
    all_goals first | constructor | skip
    all_goals nlinarith
  · rw [one_expand]
    cases t <;> dsimp [v] <;> ring
lemma fee_attained (p q B R x : ℝ) (hq : 0<q) (hqp : q<p) (hp1 : p≤1)
    (hB : 0<B) (hLL : B≤p*(p-q)*R) (hx0 : 0≤x) (hx1 : x≤1) :
    ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧ expectedFee p p f=feeMin p q B x := by
  have hb := fee_basic p q B R hq hqp hp1 hB hLL
  by_cases h0 : x=0
  · subst x
    obtain ⟨f,hf,hi,hv⟩ := endpoint_attained p q B R hq hqp hp1 hB hLL false
    refine ⟨f,hf,hi,?_⟩
    rw [hv]
    simp [feeMin,max_eq_right hb.2.2.1,le_of_lt hb.2.1]
  by_cases h1 : x=1
  · subst x
    obtain ⟨f,hf,hi,hv⟩ := endpoint_attained p q B R hq hqp hp1 hB hLL true
    refine ⟨f,hf,hi,?_⟩
    rw [hv]
    simp [feeMin,max_eq_right hb.2.2.1,le_of_lt hb.2.1]
  exact interior_fee_attained p q B R x hq hqp hp1 hB hLL (lt_of_le_of_ne hx0 (Ne.symm h0)) (lt_of_le_of_ne hx1 h1)
lemma fee_isLeast (p q B R x : ℝ) (hq : 0<q) (hqp : q<p) (hp1 : p≤1)
    (hB : 0<B) (hLL : B≤p*(p-q)*R) (hx0 : 0≤x) (hx1 : x≤1) :
    IsLeast {v | ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧ v=expectedFee p p f}
      (feeMin p q B x) := by
  obtain ⟨f,hf,hi,hv⟩ := fee_attained p q B R x hq hqp hp1 hB hLL hx0 hx1
  refine ⟨⟨f,hf,hi,hv.symm⟩,?_⟩
  rintro v ⟨g,hg,hic,rfl⟩
  exact fee_lower p q B R x hq hqp g hg hic
end PEResearch

namespace PEResearch
lemma fee_geometry (p q B : ℝ) (hq : 0<q) (hqp : q<p) (hB : 0<B) :
    0<p*B/(p-q) ∧ 0<xLow p q ∧ xLow p q<xBar p q ∧ xBar p q<1 ∧
      xLow p q+xBar p q=1 ∧ p^2*B/(p^2-q^2)=(p*B/(p-q))*xBar p q := by
  have hp : 0<p := hq.trans hqp
  have hd : 0<p-q := sub_pos.mpr hqp
  have hs : 0<p+q := by positivity
  have hd2 : 0<p^2-q^2 := by nlinarith
  refine ⟨div_pos (mul_pos hp hB) hd,div_pos hq hs,?_,?_,?_,?_⟩
  · exact (div_lt_div_iff_of_pos_right hs).mpr hqp
  · exact (div_lt_one hs).mpr (by linarith)
  · unfold xLow xBar;field_simp;ring
  · unfold xBar
    rw [show p^2-q^2=(p-q)*(p+q) by ring]
    field_simp
lemma fee_formula_low (p q B x : ℝ) (hq : 0<q) (hqp : q<p) (hB : 0<B) (hx : x≤xLow p q) :
    feeMin p q B x=p*B/(p-q)*(1-x) := by
  have hg := fee_geometry p q B hq hqp hB
  have h1 : xBar p q≤1-x := by linarith [hg.2.2.2.2.1]
  have h2 : x≤1-x := by linarith [hg.2.2.1]
  unfold feeMin
  apply le_antisymm
  · apply max_le
    · rw [hg.2.2.2.2.2];exact mul_le_mul_of_nonneg_left h1 hg.1.le
    · exact max_le (mul_le_mul_of_nonneg_left h2 hg.1.le) le_rfl
  · exact (le_max_right _ _).trans (le_max_right _ _)
lemma fee_formula_middle (p q B x : ℝ) (hq : 0<q) (hqp : q<p) (hB : 0<B)
    (hl : xLow p q≤x) (hh : x≤xBar p q) : feeMin p q B x=p^2*B/(p^2-q^2) := by
  have hg := fee_geometry p q B hq hqp hB
  unfold feeMin
  apply le_antisymm
  · apply max_le le_rfl
    rw [hg.2.2.2.2.2]
    exact max_le (mul_le_mul_of_nonneg_left hh hg.1.le)
      (mul_le_mul_of_nonneg_left (by linarith [hg.2.2.2.2.1]) hg.1.le)
  · exact le_max_left _ _
lemma fee_formula_high (p q B x : ℝ) (hq : 0<q) (hqp : q<p) (hB : 0<B) (hx : xBar p q≤x) :
    feeMin p q B x=p*B/(p-q)*x := by
  have hg := fee_geometry p q B hq hqp hB
  have h2 : 1-x≤x := by linarith [hg.2.2.1,hg.2.2.2.2.1]
  unfold feeMin
  apply le_antisymm
  · apply max_le
    · rw [hg.2.2.2.2.2];exact mul_le_mul_of_nonneg_left hx hg.1.le
    · exact max_le le_rfl (mul_le_mul_of_nonneg_left h2 hg.1.le)
  · exact (le_max_left _ _).trans (le_max_right _ _)
lemma fee_argmin (p q B x : ℝ) (hq : 0<q) (hqp : q<p) (hB : 0<B)
    (h : feeMin p q B x≤p^2*B/(p^2-q^2)) : xLow p q≤x ∧ x≤xBar p q := by
  have hg := fee_geometry p q B hq hqp hB
  have h1 : p*B/(p-q)*x≤p^2*B/(p^2-q^2) := (le_max_left _ _).trans ((le_max_right _ _).trans h)
  have h2 : p*B/(p-q)*(1-x)≤p^2*B/(p^2-q^2) := (le_max_right _ _).trans ((le_max_right _ _).trans h)
  rw [hg.2.2.2.2.2] at h1 h2
  have hx := (mul_le_mul_iff_right₀ hg.1).mp h1
  have hy := (mul_le_mul_iff_right₀ hg.1).mp h2
  constructor <;> linarith [hg.2.2.2.2.1]
lemma fee_schedule (p q B R : ℝ) (hq : 0<q) (hqp : q<p) (hp1 : p≤1) (hB : 0<B)
    (hLL : B≤p*(p-q)*R) :
    (∀ x : ℝ,0≤x → x≤xLow p q →
      IsLeast {v | ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧ v=expectedFee p p f}
        (p*B/(p-q)*(1-x))) ∧
    (∀ x : ℝ,xLow p q≤x → x≤xBar p q →
      IsLeast {v | ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧ v=expectedFee p p f}
        (p^2*B/(p^2-q^2))) ∧
    (∀ x : ℝ,xBar p q≤x → x≤1 →
      IsLeast {v | ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧ v=expectedFee p p f}
        (p*B/(p-q)*x)) ∧
    (∀ x : ℝ,(0≤x ∧ x≤1 ∧ ∃ f : Outcome → ℝ,IsLimitedLiability R x f ∧ IsIC p q B x f ∧
      ∀ x' f',0≤x' → x'≤1 → IsLimitedLiability R x' f' → IsIC p q B x' f' →
        expectedFee p p f≤expectedFee p p f') ↔ x∈Set.Icc (xLow p q) (xBar p q)) := by
  have hg := fee_geometry p q B hq hqp hB
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx0 hxl
    rw [← fee_formula_low p q B x hq hqp hB hxl]
    exact fee_isLeast p q B R x hq hqp hp1 hB hLL hx0 (hxl.trans (hg.2.2.1.le.trans hg.2.2.2.1.le))
  · intro x hxl hxb
    rw [← fee_formula_middle p q B x hq hqp hB hxl hxb]
    exact fee_isLeast p q B R x hq hqp hp1 hB hLL (hg.2.1.le.trans hxl) (hxb.trans hg.2.2.2.1.le)
  · intro x hxb hx1
    rw [← fee_formula_high p q B x hq hqp hB hxb]
    exact fee_isLeast p q B R x hq hqp hp1 hB hLL (hg.2.1.le.trans (hg.2.2.1.le.trans hxb)) hx1
  · intro x
    constructor
    · rintro ⟨hx0,hx1,f,hf,hi,hm⟩
      obtain ⟨g,hgLL,hgIC,hgv⟩ := fee_attained p q B R (xBar p q) hq hqp hp1 hB hLL (hg.2.1.le.trans hg.2.2.1.le) hg.2.2.2.1.le
      have hv := hm _ g (hg.2.1.le.trans hg.2.2.1.le) hg.2.2.2.1.le hgLL hgIC
      rw [hgv,fee_formula_middle p q B (xBar p q) hq hqp hB hg.2.2.1.le le_rfl] at hv
      exact fee_argmin p q B x hq hqp hB ((fee_lower p q B R x hq hqp f hf hi).trans hv)
    · rintro ⟨hl,hh⟩
      have hx0 := hg.2.1.le.trans hl
      have hx1 := hh.trans hg.2.2.2.1.le
      obtain ⟨f,hf,hi,hv⟩ := fee_attained p q B R x hq hqp hp1 hB hLL hx0 hx1
      refine ⟨hx0,hx1,f,hf,hi,?_⟩
      intro x' f' hx0' hx1' hf' hi'
      rw [hv,fee_formula_middle p q B x hq hqp hB hl hh]
      exact (fee_bounds p q B R x' hq hqp f' hf' hi').1
end PEResearch

namespace PEResearch
def CallFeas (P : Params) (k x : ℝ) (f : Outcome → ℝ) : Prop :=
  0≤x ∧ x≤1 ∧ 1-x≤k ∧ IsLimitedLiability P.R x f ∧ IsIC P.p P.q P.B x f
def CallOpt (P : Params) (k x : ℝ) : Prop :=
  ∃ f,CallFeas P k x f ∧ ∀ x' f',CallFeas P k x' f' → expectedFee P.p P.p f≤expectedFee P.p P.p f'
lemma call_attained (P : Params) (k x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) (hk : 1-x≤k) :
    ∃ f,CallFeas P k x f ∧ expectedFee P.p P.p f=feeMin P.p P.q P.B x := by
  obtain ⟨f,hf,hi,hv⟩ := fee_attained P.p P.q P.B P.R x P.hq P.hqp P.hp1 P.hB P.hLL hx0 hx1
  exact ⟨f,⟨hx0,hx1,hk,hf,hi⟩,hv⟩
lemma call_high (P : Params) (k : ℝ) (h0 : 0≤1-k) (h1 : 1-k≤1) (hk : 1-k≤xBar P.p P.q) :
    {x | CallOpt P k x}=Set.Icc (max (xLow P.p P.q) (1-k)) (xBar P.p P.q) ∧
    IsLeast {v | ∃ x f,CallFeas P k x f ∧ v=expectedFee P.p P.p f}
      (P.p^2*P.B/(P.p^2-P.q^2)) := by
  have hg := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  let z := max (xLow P.p P.q) (1-k)
  have hz0 : 0≤z := hg.2.1.le.trans (le_max_left _ _)
  have hz1 : z≤xBar P.p P.q := max_le hg.2.2.1.le hk
  have hzk : 1-z≤k := by have := le_max_right (xLow P.p P.q) (1-k);dsimp [z];linarith
  obtain ⟨g,hgF,hgv⟩ := call_attained P k z hz0 (hz1.trans hg.2.2.2.1.le) hzk
  rw [fee_formula_middle P.p P.q P.B z P.hq P.hqp P.hB (le_max_left _ _) hz1] at hgv
  constructor
  · ext x
    constructor
    · rintro ⟨f,hf,hm⟩
      have hv := hm z g hgF
      rw [hgv] at hv
      have hx := fee_argmin P.p P.q P.B x P.hq P.hqp P.hB
        ((fee_lower P.p P.q P.B P.R x P.hq P.hqp f hf.2.2.2.1 hf.2.2.2.2).trans hv)
      exact ⟨max_le hx.1 (by linarith [hf.2.2.1]),hx.2⟩
    · rintro ⟨hl,hh⟩
      obtain ⟨f,hf,hv⟩ := call_attained P k x (hg.2.1.le.trans ((le_max_left _ _).trans hl))
        (hh.trans hg.2.2.2.1.le) (by have := (le_max_right _ _).trans hl;linarith)
      refine ⟨f,hf,?_⟩
      intro x' f' hf'
      rw [hv,fee_formula_middle P.p P.q P.B x P.hq P.hqp P.hB ((le_max_left _ _).trans hl) hh]
      exact (fee_bounds P.p P.q P.B P.R x' P.hq P.hqp f' hf'.2.2.2.1 hf'.2.2.2.2).1
  · refine ⟨⟨z,g,hgF,hgv.symm⟩,?_⟩
    rintro v ⟨x,f,hf,rfl⟩
    exact (fee_bounds P.p P.q P.B P.R x P.hq P.hqp f hf.2.2.2.1 hf.2.2.2.2).1
lemma call_low (P : Params) (k : ℝ) (h0 : 0≤1-k) (h1 : 1-k≤1) (hk : xBar P.p P.q<1-k) :
    {x | CallOpt P k x}={1-k} ∧
    IsLeast {v | ∃ x f,CallFeas P k x f ∧ v=expectedFee P.p P.p f}
      (P.p*P.B/(P.p-P.q)*(1-k)) ∧
    ∀ x f,CallFeas P k x f → P.p^2*P.B/(P.p^2-P.q^2)<expectedFee P.p P.p f := by
  have hg := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  obtain ⟨g,hgF,hgv⟩ := call_attained P k (1-k) h0 h1 (by linarith)
  rw [fee_formula_high P.p P.q P.B (1-k) P.hq P.hqp P.hB hk.le] at hgv
  have lower (x : ℝ) (f : Outcome → ℝ) (hf : CallFeas P k x f) :
      P.p*P.B/(P.p-P.q)*(1-k)≤expectedFee P.p P.p f := by
    have hx : 1-k≤x := by linarith [hf.2.2.1]
    exact (mul_le_mul_of_nonneg_left hx hg.1.le).trans
      (fee_bounds P.p P.q P.B P.R x P.hq P.hqp f hf.2.2.2.1 hf.2.2.2.2).2.1
  refine ⟨?_,⟨⟨1-k,g,hgF,hgv.symm⟩,?_⟩,?_⟩
  · ext x
    constructor
    · rintro ⟨f,hf,hm⟩
      have hv := hm (1-k) g hgF
      rw [hgv] at hv
      have hbound := (fee_bounds P.p P.q P.B P.R x P.hq P.hqp f hf.2.2.2.1 hf.2.2.2.2).2.1
      have hx : x≤1-k := (mul_le_mul_iff_right₀ hg.1).mp (hbound.trans hv)
      have hx' : 1-k≤x := by linarith [hf.2.2.1]
      exact le_antisymm hx hx'
    · intro he
      have hx : x=1-k := he
      subst x
      exact ⟨g,hgF,fun x' f' hf' => by rw [hgv];exact lower x' f' hf'⟩
  · rintro v ⟨x,f,hf,rfl⟩;exact lower x f hf
  · intro x f hf
    rw [hg.2.2.2.2.2]
    exact (mul_lt_mul_of_pos_left hk hg.1).trans_le (lower x f hf)
lemma call_geometry (P : Params) (δ : ℝ) (hδ0 : 0<δ) (hδ1 : δ<1) :
    0≤xHat P.lam δ ∧ xHat P.lam δ≤1 ∧
    xHat P.lam δ=1-δ*grossReturn P.lam δ ∧
    (deltaHat P.p P.q P.lam≤δ ↔ xHat P.lam δ≤xBar P.p P.q) := by
  have hp : 0<P.p := P.hq.trans P.hqp
  have hl := P.hlam0
  have hl1 : 0<1-P.lam := sub_pos.mpr P.hlam1
  have hden : 0<1-P.lam*(1-δ) := by nlinarith [mul_pos hl hδ0]
  have hsum : 0<P.p+P.q := by linarith [P.hq]
  have hhat : 0<P.p+(1-P.lam)*P.q := by have := P.hq;positivity
  have hdle : δ≤1-P.lam*(1-δ) := by nlinarith [mul_nonneg hl1.le (sub_nonneg.mpr hδ1.le)]
  refine ⟨?_,?_,?_,?_⟩
  · unfold xHat;have := (div_le_one hden).mpr hdle;linarith
  · unfold xHat;have := div_nonneg hδ0.le hden.le;linarith
  · unfold xHat grossReturn;ring
  · constructor
    · intro h
      have h' : 1-δ≤P.p/(P.p+(1-P.lam)*P.q) := by unfold deltaHat at h;linarith
      have hx := (le_div_iff₀ hhat).mp h'
      unfold xHat xBar
      apply (le_div_iff₀ hsum).mpr
      apply (mul_le_mul_iff_left₀ hden).mp
      have he : (1-δ/(1-P.lam*(1-δ)))*(P.p+P.q)*(1-P.lam*(1-δ))=
          (P.p+P.q)*(1-P.lam*(1-δ))-δ*(P.p+P.q) := by field_simp <;> ring
      rw [he]
      nlinarith
    · intro h
      unfold xHat xBar at h
      have hx := (le_div_iff₀ hsum).mp h
      have hx' := mul_le_mul_of_nonneg_right hx hden.le
      have he : (1-δ/(1-P.lam*(1-δ)))*(P.p+P.q)*(1-P.lam*(1-δ))=
          (P.p+P.q)*(1-P.lam*(1-δ))-δ*(P.p+P.q) := by field_simp <;> ring
      rw [he] at hx'
      have hh : (1-δ)*(P.p+(1-P.lam)*P.q)≤P.p := by nlinarith
      have hv := (le_div_iff₀ hhat).mpr hh
      unfold deltaHat
      linarith

end PEResearch
namespace PEResearch
lemma call_theorem (P : Params) (δ : ℝ) (hδ0 : 0<δ) (hδ1 : δ<1) :
    let c := δ*grossReturn P.lam δ
    (deltaHat P.p P.q P.lam≤δ →
      {x | CallOpt P c x}=Set.Icc (max (xLow P.p P.q) (xHat P.lam δ)) (xBar P.p P.q) ∧
      IsLeast {v | ∃ x f,CallFeas P c x f ∧ v=expectedFee P.p P.p f}
        (P.p^2*P.B/(P.p^2-P.q^2))) ∧
    (δ<deltaHat P.p P.q P.lam →
      {x | CallOpt P c x}={xHat P.lam δ} ∧
      IsLeast {v | ∃ x f,CallFeas P c x f ∧ v=expectedFee P.p P.p f}
        (P.p*P.B/(P.p-P.q)*xHat P.lam δ) ∧
      ∀ x f,CallFeas P c x f → P.p^2*P.B/(P.p^2-P.q^2)<expectedFee P.p P.p f) := by
  dsimp only
  have hg := call_geometry P δ hδ0 hδ1
  constructor
  · intro hh
    have hh' := call_high P (δ*grossReturn P.lam δ) (by rw [← hg.2.2.1];exact hg.1)
      (by rw [← hg.2.2.1];exact hg.2.1) (by rw [← hg.2.2.1];exact hg.2.2.2.mp hh)
    simpa only [← hg.2.2.1] using hh'
  · intro hh
    have hh' := call_low P (δ*grossReturn P.lam δ) (by rw [← hg.2.2.1];exact hg.1)
      (by rw [← hg.2.2.1];exact hg.2.1) (by rw [← hg.2.2.1];exact lt_of_not_ge (fun h => (not_le_of_gt hh) (hg.2.2.2.mpr h)))
    simpa only [← hg.2.2.1] using hh'
end PEResearch

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
end PEFinance
namespace PEResearch
lemma contract_of_call (P : Params) (r k x : ℝ) (f : Outcome → ℝ)
    (hf : CallFeas P k x f)
    (hmin : ∀ x' f',CallFeas P k x' f' → expectedFee P.p P.p f≤expectedFee P.p P.p f')
    (hpledge : 0<P.p*P.R-expectedFee P.p P.p f)
    (hgap : P.p*P.R-expectedFee P.p P.p f<r) (hcost : r≤P.p*P.R) :
    let I := r*P.A/(r-(P.p*P.R-expectedFee P.p P.p f))
    IsOptimalContract P r k x I f ∧
      I-P.A=(P.p*P.R-expectedFee P.p P.p f)*P.A/(r-(P.p*P.R-expectedFee P.p P.p f)) := by
  let I := r*P.A/(r-(P.p*P.R-expectedFee P.p P.p f))
  have hr : 0<r := hpledge.trans hgap
  have hd : 0<r-(P.p*P.R-expectedFee P.p P.p f) := sub_pos.mpr hgap
  have he : I-P.A=(P.p*P.R-expectedFee P.p P.p f)*P.A/(r-(P.p*P.R-expectedFee P.p P.p f)) := by
    dsimp [I];field_simp;ring
  have hI : P.A<I := by
    have hp := div_pos (mul_pos hpledge P.hA) hd
    linarith
  have hfund : IsFeasibleContract P r k x I f := by
    refine ⟨hf.1,hf.2.1,hf.2.2.2.1,hf.2.2.2.2,hI,?_,hf.2.2.1⟩
    dsimp [I];field_simp;ring
  change IsOptimalContract P r k x I f ∧ _
  refine ⟨⟨hfund,?_⟩,he⟩
  intro x' I' f' h'
  have hcall : CallFeas P k x' f' := ⟨h'.1,h'.2.1,h'.2.2.2.2.2.2,h'.2.2.1,h'.2.2.2.1⟩
  have hfees := hmin x' f' hcall
  have hi := (PEFinance.fee_order P r k x I x' I' f f' hr hfund h').mp hfees
  have ha := (PEFinance.feasible_equations P r k x I f hr hfund).2.2.2
  have hb := (PEFinance.feasible_equations P r k x' I' f' hr h').2.2.2
  have hp := mul_nonneg (sub_nonneg.mpr hcost) (sub_nonneg.mpr hi)
  nlinarith
lemma high_contract (P : Params) (r : ℝ) (hr : grossReturn P.lam P.δH≤r) (hrT : r≤P.p*P.R) :
    ∃ x I f,IsOptimalContract P r (P.δH*r) x I f ∧
      expectedFee P.p P.p f=P.p^2*P.B/(P.p^2-P.q^2) ∧
      I=r*P.A/(r-(P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2))) := by
  have hp := P.hq.trans P.hqp
  have hd : 0<P.p-P.q := sub_pos.mpr P.hqp
  have hg := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  have hc := call_geometry P P.δH P.hδH0 P.hδH1
  have hx := hc.2.2.2.mp P.hA6b.le
  have hk : 1-xBar P.p P.q≤P.δH*r := by
    rw [hc.2.2.1] at hx
    have hh := mul_nonneg P.hδH0.le (sub_nonneg.mpr hr)
    nlinarith
  obtain ⟨f,hf,hv⟩ := call_attained P (P.δH*r) (xBar P.p P.q)
    (hg.2.1.le.trans hg.2.2.1.le) hg.2.2.2.1.le hk
  rw [fee_formula_middle P.p P.q P.B (xBar P.p P.q) P.hq P.hqp P.hB hg.2.2.1.le le_rfl] at hv
  have hmin : ∀ x' f',CallFeas P (P.δH*r) x' f' → expectedFee P.p P.p f≤expectedFee P.p P.p f' := by
    intro x' f' hf';rw [hv]
    exact (fee_bounds P.p P.q P.B P.R x' P.hq P.hqp f' hf'.2.2.2.1 hf'.2.2.2.2).1
  have hR := (fee_basic P.p P.q P.B P.R P.hq P.hqp P.hp1 P.hB P.hLL).1
  have hFstrict : P.p^2*P.B/(P.p^2-P.q^2)<P.p*P.B/(P.p-P.q) := by
    rw [hg.2.2.2.2.2]
    exact mul_lt_of_lt_one_right hg.1 hg.2.2.2.1
  have hFbound := (fee_basic P.p P.q P.B P.R P.hq P.hqp P.hp1 P.hB P.hLL).2.2.2
  have hpR : P.p^2*P.R≤P.p*P.R := by
    have hh := mul_le_mul_of_nonneg_right P.hp1 (mul_pos hp hR).le
    nlinarith
  have hpledge : 0<P.p*P.R-expectedFee P.p P.p f := by rw [hv];linarith [hFstrict.trans_le (hFbound.trans hpR)]
  have hreturn : 1<grossReturn P.lam P.δH := by
    have hden := (PEFinance.gross_pos P.lam P.δH P.hlam0 P.hlam1 P.hδH0 P.hδH1).1
    unfold grossReturn
    apply (lt_div_iff₀ hden).mpr
    have hh := mul_pos P.hlam0 (sub_pos.mpr P.hδH1)
    nlinarith
  have hgap : P.p*P.R-expectedFee P.p P.p f<r := by
    rw [hv]
    have ha2 := P.hA2
    have he : P.p*(P.R-P.p*P.B/(P.p^2-P.q^2))=P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2) := by ring
    rw [he] at ha2
    exact ha2.trans (hreturn.trans_le hr)
  have hopt := contract_of_call P r (P.δH*r) (xBar P.p P.q) f hf hmin hpledge hgap hrT
  refine ⟨xBar P.p P.q,_,f,hopt.1,hv,?_⟩
  rw [hv]
end PEResearch
namespace PEResearch
noncomputable def minCallFee (P : Params) (k : ℝ) : ℝ :=
  max (P.p^2*P.B/(P.p^2-P.q^2)) (P.p*P.B/(P.p-P.q)*(1-k))
lemma cost_bounds (P : Params) : 0<P.p*P.B/(P.p-P.q) ∧ P.p*P.B/(P.p-P.q)≤1 ∧ 1<P.p*P.R := by
  have hp := P.hq.trans P.hqp
  have hd : 0<P.p-P.q := sub_pos.mpr P.hqp
  have hr := (PEFinance.gross_pos P.lam P.δL P.hlam0 P.hlam1 P.hδL0 P.hδL1).1
  have hg : 1<grossReturn P.lam P.δL := by
    unfold grossReturn
    apply (lt_div_iff₀ hr).mpr
    have := mul_pos P.hlam0 (sub_pos.mpr P.hδL1)
    nlinarith
  refine ⟨div_pos (mul_pos hp P.hB) hd,?_,hg.trans P.hA5⟩
  apply (div_le_iff₀ hd).mpr
  have h1 := mul_le_mul_of_nonneg_left P.hA1a P.hq.le
  have h2 := mul_le_mul_of_nonneg_left P.hA1b hp.le
  nlinarith
lemma cash_expected (a b R x : ℝ) : expectedFee a b (cashFlow R x)=R*(a*x+b*(1-x)) := by
  simp [fee_expand,cashFlow];ring
lemma fee_mix (a b t : ℝ) (f g : Outcome → ℝ) :
    expectedFee a b (fun ω => (1-t)*f ω+t*g ω)=(1-t)*expectedFee a b f+t*expectedFee a b g := by
  simp only [fee_expand];ring
lemma cash_call (P : Params) (k x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) (hk : 1-x≤k) :
    CallFeas P k x (cashFlow P.R x) := by
  have hR := (fee_basic P.p P.q P.B P.R P.hq P.hqp P.hp1 P.hB P.hLL).1
  have hinc : 0≤(P.p-P.q)*P.R-P.B := by linarith [P.hA1a,P.hA1b]
  refine ⟨hx0,hx1,hk,⟨?_,fun _ _ h => h⟩,?_⟩
  · intro ω
    refine ⟨?_,le_rfl⟩
    rcases ω with ⟨a,b⟩;cases a <;> cases b <;> simp [cashFlow] <;> positivity
  · unfold IsIC
    simp only [cash_expected]
    have h1 := mul_nonneg hinc hx0
    have h2 := mul_nonneg hinc (sub_nonneg.mpr hx1)
    constructor
    · nlinarith
    constructor <;> nlinarith
lemma mix_call (P : Params) (k x t : ℝ) (ht0 : 0≤t) (ht1 : t≤1)
    (f g : Outcome → ℝ) (hf : CallFeas P k x f) (hg : CallFeas P k x g) :
    CallFeas P k x (fun ω => (1-t)*f ω+t*g ω) := by
  have ht : 0≤1-t := sub_nonneg.mpr ht1
  refine ⟨hf.1,hf.2.1,hf.2.2.1,⟨?_,?_⟩,?_⟩
  · intro ω
    have h1 := hf.2.2.2.1.1 ω
    have h2 := hg.2.2.2.1.1 ω
    refine ⟨add_nonneg (mul_nonneg ht h1.1) (mul_nonneg ht0 h2.1),?_⟩
    have hu1 := mul_le_mul_of_nonneg_left h1.2 ht
    have hu2 := mul_le_mul_of_nonneg_left h2.2 ht0
    nlinarith
  · intro ω ω' he
    dsimp only
    rw [hf.2.2.2.1.2 ω ω' he,hg.2.2.2.1.2 ω ω' he]
  · unfold IsIC
    simp only [fee_mix]
    have h1 := mul_le_mul_of_nonneg_left hf.2.2.2.2.1 ht
    have h2 := mul_le_mul_of_nonneg_left hg.2.2.2.2.1 ht0
    have h3 := mul_le_mul_of_nonneg_left hf.2.2.2.2.2.1 ht
    have h4 := mul_le_mul_of_nonneg_left hg.2.2.2.2.2.1 ht0
    have h5 := mul_le_mul_of_nonneg_left hf.2.2.2.2.2.2 ht
    have h6 := mul_le_mul_of_nonneg_left hg.2.2.2.2.2.2 ht0
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩
lemma fee_cash_bound (P : Params) (x : ℝ) (f : Outcome → ℝ) (hf : IsLimitedLiability P.R x f) :
    expectedFee P.p P.p f≤P.p*P.R := by
  have hp := P.hq.trans P.hqp
  have hp1 : 0≤1-P.p := sub_nonneg.mpr P.hp1
  have hprob (ω : Outcome) : 0≤outcomeProb P.p P.p ω := by
    rcases ω with ⟨a,b⟩;cases a <;> cases b <;> simp [outcomeProb] <;> positivity
  have h : expectedFee P.p P.p f≤expectedFee P.p P.p (cashFlow P.R x) := by
    unfold expectedFee
    exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hf.1 ω).2 (hprob ω)
  rw [cash_expected] at h
  nlinarith
lemma minimum_call (P : Params) (k : ℝ) (hk : 0≤k) :
    0< minCallFee P k ∧ minCallFee P k<P.p*P.R ∧
    (∃ x f,CallFeas P k x f ∧ expectedFee P.p P.p f=minCallFee P k) ∧
    ∀ x f,CallFeas P k x f → minCallFee P k≤expectedFee P.p P.p f := by
  have hg := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  have hc := cost_bounds P
  let x := max (xBar P.p P.q) (1-k)
  have hx0 : 0≤x := hg.2.1.le.trans (hg.2.2.1.le.trans (le_max_left _ _))
  have hx1 : x≤1 := max_le hg.2.2.2.1.le (by linarith)
  have hxk : 1-x≤k := by have := le_max_right (xBar P.p P.q) (1-k);dsimp [x];linarith
  have hF : feeMin P.p P.q P.B x=minCallFee P k := by
    rw [fee_formula_high P.p P.q P.B x P.hq P.hqp P.hB (le_max_left _ _)]
    unfold minCallFee
    rw [hg.2.2.2.2.2]
    exact mul_max_of_nonneg _ _ hg.1.le
  have hm0 : 0< minCallFee P k := by
    apply lt_of_lt_of_le _ (le_max_left _ _)
    rw [hg.2.2.2.2.2]
    exact mul_pos hg.1 (hg.2.1.trans_le hg.2.2.1.le)
  have hmC : minCallFee P k≤P.p*P.B/(P.p-P.q) := by
    unfold minCallFee
    apply max_le
    · rw [hg.2.2.2.2.2];exact mul_le_of_le_one_right hg.1.le hg.2.2.2.1.le
    · exact mul_le_of_le_one_right hg.1.le (by linarith)
  obtain ⟨f,hf,hv⟩ := call_attained P k x hx0 hx1 hxk
  rw [hF] at hv
  refine ⟨hm0,(hmC.trans hc.2.1).trans_lt hc.2.2,⟨x,f,hf,hv⟩,?_⟩
  intro y g hy
  have hb := fee_bounds P.p P.q P.B P.R y P.hq P.hqp g hy.2.2.2.1 hy.2.2.2.2
  exact max_le hb.1 ((mul_le_mul_of_nonneg_left (show 1-k≤y by linarith [hy.2.2.1]) hg.1.le).trans hb.2.1)
lemma fee_attainment_interval (P : Params) (k F : ℝ) (hk : 0≤k)
    (hF : minCallFee P k≤F) (hFT : F≤P.p*P.R) :
    ∃ x f,CallFeas P k x f ∧ expectedFee P.p P.p f=F := by
  obtain ⟨hm0,hmT,⟨x,f,hf,hv⟩,hmin⟩ := minimum_call P k hk
  let t := (F-minCallFee P k)/(P.p*P.R-minCallFee P k)
  have hd : 0<P.p*P.R-minCallFee P k := sub_pos.mpr hmT
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hF) hd.le
  have ht1 : t≤1 := (div_le_one hd).mpr (by linarith)
  have hcash := cash_call P k x hf.1 hf.2.1 hf.2.2.1
  refine ⟨x,_,mix_call P k x t ht0 ht1 f _ hf hcash,?_⟩
  rw [fee_mix,hv,cash_expected]
  dsimp [t]
  field_simp;ring
end PEResearch
namespace PEResearch
lemma feasible_call (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsFeasibleContract P r k x I f) : CallFeas P k x f :=
  ⟨hf.1,hf.2.1,hf.2.2.2.2.2.2,hf.2.2.1,hf.2.2.2.1⟩
lemma finance_call (P : Params) (r k x : ℝ) (f : Outcome → ℝ) (hf : CallFeas P k x f)
    (hp : 0<P.p*P.R-expectedFee P.p P.p f) (hr : P.p*P.R-expectedFee P.p P.p f<r) :
    IsFeasibleContract P r k x (r*P.A/(r-(P.p*P.R-expectedFee P.p P.p f))) f := by
  have hd : 0<r-(P.p*P.R-expectedFee P.p P.p f) := sub_pos.mpr hr
  have he : r*P.A/(r-(P.p*P.R-expectedFee P.p P.p f))-P.A=
      (P.p*P.R-expectedFee P.p P.p f)*P.A/(r-(P.p*P.R-expectedFee P.p P.p f)) := by field_simp;ring
  have hI : P.A<r*P.A/(r-(P.p*P.R-expectedFee P.p P.p f)) := by
    have hpos := div_pos (mul_pos hp P.hA) hd
    linarith
  refine ⟨hf.1,hf.2.1,hf.2.2.2.1,hf.2.2.2.2,hI,?_,hf.2.2.1⟩
  field_simp;ring
lemma optimal_return_pos (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsOptimalContract P r k x I f) : 0<r := by
  have hI := hf.1.2.2.2.2.1
  have hI0 := P.hA.trans hI
  have hcash := fee_cash_bound P x f hf.1.2.2.1
  have he := hf.1.2.2.2.2.2.1
  have hr0 : 0≤r := by
    have hp := mul_nonneg (sub_nonneg.mpr hcash) hI0.le
    rw [he] at hp
    exact (mul_nonneg_iff_of_pos_right (sub_pos.mpr hI)).mp hp
  by_contra hn
  have hr : r=0 := le_antisymm (le_of_not_gt hn) hr0
  have hF : expectedFee P.p P.p f=P.p*P.R := by rw [hr] at he;nlinarith
  have hc : IsFeasibleContract P r k x (I+1) f := by
    refine ⟨hf.1.1,hf.1.2.1,hf.1.2.2.1,hf.1.2.2.2.1,by linarith,?_,hf.1.2.2.2.2.2.2⟩
    rw [hF,hr];ring
  have ho := hf.2 x (I+1) f hc
  rw [hF] at ho
  nlinarith [(cost_bounds P).2.2]
lemma optimal_return_le (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsOptimalContract P r k x I f) : r≤P.p*P.R := by
  have hr := optimal_return_pos P r k x I f hf
  have ha := PEFinance.feasible_equations P r k x I f hr hf.1
  have hk : 0≤k := by linarith [hf.1.2.1,hf.1.2.2.2.2.2.2]
  have hm := minimum_call P k hk
  have hlow := hm.2.2.2 x f (feasible_call P r k x I f hf.1)
  let F := (expectedFee P.p P.p f+P.p*P.R)/2
  have hF0 : minCallFee P k≤F := by dsimp [F];linarith [ha.2.1]
  have hFT : F<P.p*P.R := by dsimp [F];linarith [ha.2.1]
  obtain ⟨y,g,hg,hgv⟩ := fee_attainment_interval P k F hk hF0 hFT.le
  have hpg : 0<P.p*P.R-expectedFee P.p P.p g := by rw [hgv];linarith
  have hrg : P.p*P.R-expectedFee P.p P.p g<r := by rw [hgv];dsimp [F];linarith [ha.2.1,ha.2.2.1]
  let J := r*P.A/(r-(P.p*P.R-expectedFee P.p P.p g))
  have hJ := finance_call P r k y g hg hpg hrg
  have hb := PEFinance.feasible_equations P r k y J g hr hJ
  have hfee : expectedFee P.p P.p f<expectedFee P.p P.p g := by rw [hgv];dsimp [F];linarith [ha.2.1]
  have hJI : J<I := by
    have hle := (PEFinance.fee_order P r k x I y J f g hr hf.1 hJ).mp hfee.le
    apply lt_of_le_of_ne hle
    intro heq
    have hp := mul_pos (sub_pos.mpr hfee) ha.1
    rw [heq] at hb
    nlinarith [ha.2.2.2,hb.2.2.2]
  by_contra h
  have ht := lt_of_not_ge h
  have hp := mul_pos (sub_pos.mpr ht) (sub_pos.mpr hJI)
  have ho := hf.2 y J g hJ
  nlinarith [ha.2.2.2,hb.2.2.2]
lemma optimal_pledge_gap (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsOptimalContract P r k x I f) : P.p*P.R-minCallFee P k<r := by
  have hr := optimal_return_pos P r k x I f hf
  have ha := PEFinance.feasible_equations P r k x I f hr hf.1
  have hk : 0≤k := by linarith [hf.1.2.1,hf.1.2.2.2.2.2.2]
  have hm := minimum_call P k hk
  by_contra h
  have hbad := le_of_not_gt h
  have hrT : r<P.p*P.R := by linarith [hm.1]
  have hI := ha.1
  have hA := P.hA
  let F := P.p*P.R-r+r*P.A/(2*I)
  have hdiv : 0<r*P.A/(2*I) := by positivity
  have hF0 : minCallFee P k≤F := by dsimp [F];linarith
  have hsmall : r*P.A/(2*I)<r := by
    apply (div_lt_iff₀ (show 0<2*I by positivity)).mpr
    have hp := mul_pos hr (show 0<2*I-P.A by linarith [hf.1.2.2.2.2.1,ha.1])
    nlinarith
  have hFT : F<P.p*P.R := by dsimp [F];linarith
  obtain ⟨y,g,hg,hgv⟩ := fee_attainment_interval P k F hk hF0 hFT.le
  have hmoney : (P.p*P.R-expectedFee P.p P.p g)*(2*I)=r*(2*I-P.A) := by
    rw [hgv];dsimp [F];field_simp [ne_of_gt hI] <;> ring
  have hJ : IsFeasibleContract P r k y (2*I) g :=
    ⟨hg.1,hg.2.1,hg.2.2.2.1,hg.2.2.2.2,by linarith [hf.1.2.2.2.2.1,ha.1],hmoney,hg.2.2.1⟩
  have hb := PEFinance.feasible_equations P r k y (2*I) g hr hJ
  have hp := mul_pos (sub_pos.mpr hrT) ha.1
  have ho := hf.2 y (2*I) g hJ
  nlinarith [ha.2.2.2,hb.2.2.2]
lemma optimal_fee_size (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsOptimalContract P r k x I f) (hrT : r<P.p*P.R) :
    expectedFee P.p P.p f=minCallFee P k ∧
    I=r*P.A/(r-(P.p*P.R-minCallFee P k)) := by
  have hr := optimal_return_pos P r k x I f hf
  have ha := PEFinance.feasible_equations P r k x I f hr hf.1
  have hk : 0≤k := by linarith [hf.1.2.1,hf.1.2.2.2.2.2.2]
  have hm := minimum_call P k hk
  obtain ⟨y,g,hg,hgv⟩ := hm.2.2.1
  have hg0 : 0<P.p*P.R-expectedFee P.p P.p g := by rw [hgv];exact sub_pos.mpr hm.2.1
  have hgr : P.p*P.R-expectedFee P.p P.p g<r := by rw [hgv];exact optimal_pledge_gap P r k x I f hf
  let J := r*P.A/(r-(P.p*P.R-expectedFee P.p P.p g))
  have hJ := finance_call P r k y g hg hg0 hgr
  have hb := PEFinance.feasible_equations P r k y J g hr hJ
  have ho := hf.2 y J g hJ
  have hIJ : J≤I := by
    by_contra h
    have hp := mul_pos (sub_pos.mpr hrT) (sub_pos.mpr (lt_of_not_ge h))
    nlinarith [ha.2.2.2,hb.2.2.2]
  have hfle := (PEFinance.fee_order P r k x I y J f g hr hf.1 hJ).mpr hIJ
  rw [hgv] at hfle
  have hfe : expectedFee P.p P.p f=minCallFee P k := le_antisymm hfle (hm.2.2.2 x f (feasible_call P r k x I f hf.1))
  refine ⟨hfe,?_⟩
  apply (eq_div_iff (ne_of_gt (sub_pos.mpr (optimal_pledge_gap P r k x I f hf)))).mpr
  rw [hfe] at ha
  nlinarith [ha.2.2.2]
end PEResearch

namespace PEAlgebra
lemma profit_strict_decreasing (T C F d r s : ℝ)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hT : 1 < T) (hF0 : 0 < F) (hF1 : F ≤ C)
    (hd0 : 0 < d) (hr0 : 0 < r) (hrs : r < s) (hs1 : 1 < s) (hsT : s ≤ T)
    (hdenr : 0 < r-T+max F (C*(1-d*r)))
    (hdens : 0 < s-T+max F (C*(1-d*s))) :
    max F (C*(1-d*s))*s/(s-T+max F (C*(1-d*s))) <
      max F (C*(1-d*r))*r/(r-T+max F (C*(1-d*r))) := by
  apply (div_lt_div_iff₀ hdens hdenr).mpr
  have hds := mul_pos hd0 (sub_pos.mpr hrs)
  by_cases hflat : C*(1-d*r) ≤ F
  · have hflat' : C*(1-d*s) ≤ F := by nlinarith [mul_pos hC0 hds]
    rw [max_eq_left hflat,max_eq_left hflat']
    have hp := mul_pos (mul_pos hF0 (show 0<T-F by linarith)) (sub_pos.mpr hrs)
    nlinarith
  · have hlin := lt_of_not_ge hflat
    rw [max_eq_right hlin.le] at hdenr ⊢
    have hpos : 0 < 1-d*r := by nlinarith
    have hCr : C*(1-d*r) ≤ 1 := by nlinarith [mul_pos hC0 (mul_pos hd0 hr0)]
    have hcoeff : 0 < T*s-r*s-C*(1-d*r)*(s-r) := by
      have ha := mul_pos (sub_pos.mpr hrs) (show 0<s-C*(1-d*r) by linarith)
      have hb := mul_nonneg (sub_nonneg.mpr hsT) (hr0.trans hrs).le
      nlinarith
    have hM := le_max_right F (C*(1-d*s))
    have hmult := mul_nonneg hcoeff.le (sub_nonneg.mpr hM)
    have hp1 := mul_pos (show 0<T-C by linarith) hpos
    have hp2 := mul_pos (mul_pos hd0 (hr0.trans hrs)) hdenr
    have hp := mul_pos (mul_pos hC0 (sub_pos.mpr hrs)) (add_pos hp1 hp2)
    nlinarith
end PEAlgebra

namespace PEResearch
lemma optimal_profit_formula (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsOptimalContract P r k x I f) :
    gpProfit P I f = minCallFee P k*r*P.A/(r-P.p*P.R+minCallFee P k) := by
  have hr := optimal_return_pos P r k x I f hf
  have hrt := optimal_return_le P r k x I f hf
  rcases lt_or_eq_of_le hrt with h | h
  · obtain ⟨hF,hI⟩ := optimal_fee_size P r k x I f hf h
    unfold gpProfit
    rw [hF,hI]
    ring
  · have ha := PEFinance.feasible_equations P r k x I f hr hf.1
    have hk : 0 ≤ k := by linarith [hf.1.2.1,hf.1.2.2.2.2.2.2]
    have hM := (minimum_call P k hk).1
    unfold gpProfit
    rw [ha.2.2.2,h]
    field_simp [ne_of_gt hM] <;> ring
lemma optimal_profit_strict_decreasing (P : Params) (d r s x I y J : ℝ)
    (hd : 0 < d) (hrs : r < s) (hs : 1 < s) (f g : Outcome → ℝ)
    (hf : IsOptimalContract P r (d*r) x I f) (hg : IsOptimalContract P s (d*s) y J g) :
    gpProfit P J g < gpProfit P I f := by
  have hc := cost_bounds P
  have hgeo := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  have hF0 : 0 < P.p^2*P.B/(P.p^2-P.q^2) := by
    rw [hgeo.2.2.2.2.2]
    exact mul_pos hc.1 (hgeo.2.1.trans hgeo.2.2.1)
  have hFC : P.p^2*P.B/(P.p^2-P.q^2) ≤ P.p*P.B/(P.p-P.q) := by
    rw [hgeo.2.2.2.2.2]
    nlinarith [mul_nonneg hc.1.le (sub_nonneg.mpr hgeo.2.2.2.1.le)]
  have hr := optimal_return_pos P r (d*r) x I f hf
  have ht := optimal_return_le P s (d*s) y J g hg
  have hgr := optimal_pledge_gap P r (d*r) x I f hf
  have hgs := optimal_pledge_gap P s (d*s) y J g hg
  have h := PEAlgebra.profit_strict_decreasing (P.p*P.R) (P.p*P.B/(P.p-P.q))
    (P.p^2*P.B/(P.p^2-P.q^2)) d r s hc.1 hc.2.1 hc.2.2 hF0 hFC hd hr hrs hs ht
    (by change 0 < r-P.p*P.R+minCallFee P (d*r);linarith)
    (by change 0 < s-P.p*P.R+minCallFee P (d*s);linarith)
  have hp := mul_lt_mul_of_pos_right h P.hA
  rw [optimal_profit_formula P r (d*r) x I f hf,optimal_profit_formula P s (d*s) y J g hg]
  dsimp [minCallFee] at *
  simpa only [div_mul_eq_mul_div] using hp
end PEResearch

namespace PEResearch
lemma general_contract (P : Params) (r k : ℝ) (hr : 1 ≤ r) (ht : r ≤ P.p*P.R) (hk : 0 ≤ k) :
    ∃ x I f, IsOptimalContract P r k x I f ∧ expectedFee P.p P.p f = minCallFee P k ∧
      I = r*P.A/(r-(P.p*P.R-minCallFee P k)) := by
  have hm := minimum_call P k hk
  obtain ⟨x,f,hf,hv⟩ := hm.2.2.1
  have hmin : ∀ y g, CallFeas P k y g → expectedFee P.p P.p f ≤ expectedFee P.p P.p g := by
    intro y g hg;rw [hv];exact hm.2.2.2 y g hg
  have hp : 0 < P.p*P.R-expectedFee P.p P.p f := by rw [hv];linarith [hm.2.1]
  have hA2 : P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2) < 1 := by
    have he : P.p*(P.R-P.p*P.B/(P.p^2-P.q^2))=P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2) := by ring
    simpa only [he] using P.hA2
  have hg : P.p*P.R-expectedFee P.p P.p f < r := by
    rw [hv];have h := le_max_left (P.p^2*P.B/(P.p^2-P.q^2)) (P.p*P.B/(P.p-P.q)*(1-k));change _ ≤ minCallFee P k at h;linarith
  have ho := contract_of_call P r k x f hf hmin hp hg ht
  refine ⟨x,_,f,ho.1,hv,?_⟩
  rw [hv]
lemma contract_size_lt_cap (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsFeasibleContract P r k x I f) (hr : 1 < r) : I-P.A < P.K := by
  have hI : 0 < I := P.hA.trans hf.2.2.2.2.1
  have hF := (fee_bounds P.p P.q P.B P.R x P.hq P.hqp f hf.2.2.1 hf.2.2.2.1).1
  have he : P.p*(P.R-P.p*P.B/(P.p^2-P.q^2))=P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2) := by ring
  have hA2 := P.hA2
  have hA3 := P.hA3
  rw [he] at hA2 hA3
  have hden : 0 < 1-(P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2)) := by linarith
  have hprod := mul_pos (sub_pos.mpr hr) (sub_pos.mpr hf.2.2.2.2.1)
  have hbound := mul_nonneg (sub_nonneg.mpr hF) hI.le
  have hi : I < P.A/(1-(P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2))) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [hf.2.2.2.2.2.1]
  linarith
end PEResearch

namespace PEFinance
lemma rate_algebra (T F G r A : ℝ) (hF : 0<F) (hFG : F<G) (hGT : G<T)
    (hr : 0<r) (hrT : r<T) (hpledge : T-F<r) :
    let m := G*(T-F)/(F/r*(T-G)+G-F)
    r < m ∧ m<T ∧ F*(m*A/(m-(T-F)))=G*(r*A/(r-(T-G))) := by
  let D := F/r*(T-G)+G-F
  have hD : 0<D := by
    dsimp [D]
    have hp := mul_pos (div_pos hF hr) (sub_pos.mpr hGT)
    linarith
  let m := G*(T-F)/D
  have he : m*D=G*(T-F) := by dsimp [m];field_simp
  have hrm : r < m := by
    dsimp [m]
    apply (lt_div_iff₀ hD).mpr
    have hid : G*(T-F)-r*D=(G-F)*(T-r) := by dsimp [D];field_simp;ring
    have hp := mul_pos (sub_pos.mpr hFG) (sub_pos.mpr hrT)
    linarith
  have hmT : m<T := by
    dsimp [m]
    apply (div_lt_iff₀ hD).mpr
    have hid : T*D-G*(T-F)=F*(T-G)*(T-r)/r := by dsimp [D];field_simp;ring
    have hp := div_pos (mul_pos (mul_pos hF (sub_pos.mpr hGT)) (sub_pos.mpr hrT)) hr
    linarith
  have hmden : 0 < m-(T-F) := sub_pos.mpr (hpledge.trans hrm)
  have hrden : 0<r-(T-G) := by linarith
  change r < m ∧ m<T ∧ _
  refine ⟨hrm,hmT,?_⟩
  have hid : m*(F*(T-G)+r*(G-F))=G*r*(T-F) := by
    have hh := congrArg (fun v : ℝ => v*r) he
    dsimp [D] at hh
    field_simp [ne_of_gt hr] at hh
    nlinarith only [hh]
  have ha := congrArg (fun v : ℝ => v*A) hid
  calc
    F*(m*A/(m-(T-F)))=(F*m*A)/(m-(T-F)) := by ring
    _=(G*r*A)/(r-(T-G)) := (div_eq_div_iff (ne_of_gt hmden) (ne_of_gt hrden)).mpr (by nlinarith only [ha])
    _=G*(r*A/(r-(T-G))) := by ring
end PEFinance
namespace PEResearch
lemma indifference (P : Params) :
    let fH := P.p^2*P.B/(P.p^2-P.q^2)
    let fL := P.p*P.B*xHat P.lam P.δL/(P.p-P.q)
    let RL := grossReturn P.lam P.δL
    let Rmax := fL*(P.p*P.R-fH)/(fH/RL*(P.p*P.R-fL)+fL-fH)
    RL<Rmax ∧ Rmax<P.p*P.R ∧
      fH*(Rmax*P.A/(Rmax-(P.p*P.R-fH)))=fL*(RL*P.A/(RL-(P.p*P.R-fL))) := by
  dsimp only
  have hp : 0<P.p := P.hq.trans P.hqp
  have hd : 0<P.p-P.q := sub_pos.mpr P.hqp
  have hd2 : 0<P.p^2-P.q^2 := by nlinarith [P.hq,P.hqp]
  have hg := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  have hc := call_geometry P P.δL P.hδL0 P.hδL1
  have hxb : xBar P.p P.q<xHat P.lam P.δL := lt_of_not_ge (fun h => (not_le_of_gt P.hA6a) (hc.2.2.2.mpr h))
  have hx1 : xHat P.lam P.δL<1 := by
    have hden := (PEFinance.gross_pos P.lam P.δL P.hlam0 P.hlam1 P.hδL0 P.hδL1).1
    unfold xHat
    have hh := div_pos P.hδL0 hden
    linarith
  have hR := (fee_basic P.p P.q P.B P.R P.hq P.hqp P.hp1 P.hB P.hLL).1
  have hf0 : 0<P.p^2*P.B/(P.p^2-P.q^2) := by have := P.hB;positivity
  have hfLt : P.p^2*P.B/(P.p^2-P.q^2)<P.p*P.B*xHat P.lam P.δL/(P.p-P.q) := by
    rw [hg.2.2.2.2.2]
    have hh := mul_lt_mul_of_pos_left hxb hg.1
    simpa only [div_mul_eq_mul_div] using hh
  have hflT : P.p*P.B*xHat P.lam P.δL/(P.p-P.q)<P.p*P.R := by
    have hx := mul_lt_mul_of_pos_left hx1 hg.1
    rw [mul_one,div_mul_eq_mul_div] at hx
    have hb := (fee_basic P.p P.q P.B P.R P.hq P.hqp P.hp1 P.hB P.hLL).2.2.2
    have hpR : P.p^2*P.R≤P.p*P.R := by
      have hh := mul_le_mul_of_nonneg_right P.hp1 (mul_pos hp hR).le
      nlinarith
    exact hx.trans_le (hb.trans hpR)
  have hrl0 := (PEFinance.gross_pos P.lam P.δL P.hlam0 P.hlam1 P.hδL0 P.hδL1).2
  have hrl1 : 1<grossReturn P.lam P.δL := by
    have hden := (PEFinance.gross_pos P.lam P.δL P.hlam0 P.hlam1 P.hδL0 P.hδL1).1
    unfold grossReturn
    apply (lt_div_iff₀ hden).mpr
    have hh := mul_pos P.hlam0 (sub_pos.mpr P.hδL1)
    nlinarith
  have hpledge : P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2)<grossReturn P.lam P.δL := by
    have he : P.p*(P.R-P.p*P.B/(P.p^2-P.q^2))=P.p*P.R-P.p^2*P.B/(P.p^2-P.q^2) := by ring
    have ha2 := P.hA2
    rw [he] at ha2
    exact ha2.trans hrl1
  exact PEFinance.rate_algebra _ _ _ _ _ hf0 hfLt hflT hrl0 P.hA5 hpledge
end PEResearch


namespace PEResearch
lemma gross_gt_one (P : Params) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    1 < grossReturn P.lam d := by
  have hd := (PEFinance.gross_pos P.lam d P.hlam0 P.hlam1 hd0 hd1).1
  unfold grossReturn
  apply (lt_div_iff₀ hd).mpr
  nlinarith [mul_pos P.hlam0 (sub_pos.mpr hd1)]
lemma gross_order (P : Params) : grossReturn P.lam P.δH < grossReturn P.lam P.δL := by
  have hL := (PEFinance.gross_pos P.lam P.δL P.hlam0 P.hlam1 P.hδL0 P.hδL1).1
  have hH := (PEFinance.gross_pos P.lam P.δH P.hlam0 P.hlam1 P.hδH0 P.hδH1).1
  unfold grossReturn
  apply (div_lt_div_iff₀ hH hL).mpr
  nlinarith [mul_pos P.hlam0 (sub_pos.mpr (P.hA6a.trans P.hA6b))]
lemma low_min (P : Params) :
    minCallFee P (P.δL*grossReturn P.lam P.δL) = P.p*P.B*xHat P.lam P.δL/(P.p-P.q) := by
  have hc := call_geometry P P.δL P.hδL0 P.hδL1
  have hg := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  have hx : xBar P.p P.q < xHat P.lam P.δL :=
    lt_of_not_ge (fun h => (not_le_of_gt P.hA6a) (hc.2.2.2.mpr h))
  unfold minCallFee
  rw [← hc.2.2.1, hg.2.2.2.2.2, max_eq_right (mul_le_mul_of_nonneg_left hx.le hg.1.le)]
  ring
lemma baseline_gap (P : Params) :
    ∃ xl Il fl xh Ih fh,
      IsOptimalContract P (grossReturn P.lam P.δL) (P.δL*grossReturn P.lam P.δL) xl Il fl ∧
      IsOptimalContract P (grossReturn P.lam P.δH) (P.δH*grossReturn P.lam P.δH) xh Ih fh ∧
      gpProfit P Il fl < gpProfit P Ih fh := by
  have hL := gross_gt_one P P.δL P.hδL0 P.hδL1
  have hH := gross_gt_one P P.δH P.hδH0 P.hδH1
  obtain ⟨xl,Il,fl,hl,hfl,hIl⟩ := general_contract P (grossReturn P.lam P.δL)
    (P.δL*grossReturn P.lam P.δL) hL.le P.hA5.le (mul_pos P.hδL0 (by linarith)).le
  obtain ⟨xh,Ih,fh,hh,hfh,hIh⟩ := high_contract P (grossReturn P.lam P.δH) le_rfl
    ((gross_order P).trans P.hA5).le
  let F := P.p^2*P.B/(P.p^2-P.q^2)
  let G := P.p*P.B*xHat P.lam P.δL/(P.p-P.q)
  let r := grossReturn P.lam P.δL
  let s := G*(P.p*P.R-F)/(F/r*(P.p*P.R-G)+G-F)
  have hi := indifference P
  change r < s ∧ s < P.p*P.R ∧ F*(s*P.A/(s-(P.p*P.R-F)))=G*(r*P.A/(r-(P.p*P.R-G))) at hi
  obtain ⟨xs,Is,fs,hs,hfs,hIs⟩ := high_contract P s ((gross_order P).trans hi.1).le hi.2.1.le
  have hprof : gpProfit P Is fs = gpProfit P Il fl := by
    unfold gpProfit
    rw [hfs,hIs,hfl,hIl,low_min]
    exact hi.2.2
  have hlt := optimal_profit_strict_decreasing P P.δH (grossReturn P.lam P.δH) s
    xh Ih xs Is P.hδH0 ((gross_order P).trans hi.1) (hH.trans ((gross_order P).trans hi.1)) fh fs hh hs
  refine ⟨xl,Il,fl,xh,Ih,fh,hl,hh,?_⟩
  rw [hprof] at hlt
  exact hlt
lemma optimal_profit_antitone (P : Params) (d r s x I y J : ℝ)
    (hd : 0 < d) (hrs : r ≤ s) (hs : 1 < s) (f g : Outcome → ℝ)
    (hf : IsOptimalContract P r (d*r) x I f) (hg : IsOptimalContract P s (d*s) y J g) :
    gpProfit P J g ≤ gpProfit P I f := by
  rcases lt_or_eq_of_le hrs with h | rfl
  · exact (optimal_profit_strict_decreasing P d r s x I y J hd h hs f g hf hg).le
  · exact hf.2 y J g hg.1
end PEResearch

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

noncomputable def fH (P : Params) : ℝ := P.p^2*P.B/(P.p^2-P.q^2)
noncomputable def cc (P : Params) : ℝ := P.p*P.B/(P.p-P.q)
noncomputable def GH (P : Params) : ℝ := grossReturn P.lam P.δH
noncomputable def piH (P : Params) : ℝ := P.p*P.R - fH P
noncomputable def N0 (P : Params) : ℝ := piH P * P.A / (GH P - piH P)
noncomputable def t7 (P : Params) : ℝ := (P.p+(1-P.lam)*P.q)/((1-P.lam)*P.q)
noncomputable def RLf (P : Params) (D : ℝ) : ℝ := 1/(1-P.lam*D)
noncomputable def PLf (P : Params) (D : ℝ) : ℝ := (1-D)/(1-P.lam*D)
noncomputable def gf (P : Params) (D : ℝ) : ℝ := (1-P.lam)*D/(1-P.lam*D)
noncomputable def piL (P : Params) (D : ℝ) : ℝ := P.p*P.R - minCallFee P (PLf P D)
noncomputable def NLf (P : Params) (D : ℝ) : ℝ := piL P D * P.A/(RLf P D - piL P D)
noncomputable def Phi (P : Params) (D : ℝ) : ℝ := NLf P D * PLf P D
noncomputable def Dst (P : Params) : ℝ := xBar P.p P.q/(1-P.lam+P.lam*xBar P.p P.q)
noncomputable def mu1 (P : Params) : ℝ := Phi P (1-P.δL)/P.K
noncomputable def mu2 (P : Params) : ℝ := Phi P (Dst P)/P.K
noncomputable def mu3 (P : Params) : ℝ := Phi P (1-P.δH)/P.K
noncomputable def Pi (P : Params) (r m : ℝ) : ℝ := m*r*P.A/(r-P.p*P.R+m)

structure Basics (P : Params) : Prop where
  p0 : 0 < P.p
  pq : 0 < P.p - P.q
  pq2 : 0 < P.p^2 - P.q^2
  fH_eq : fH P = cc P * xBar P.p P.q
  fH0 : 0 < fH P
  fHc : fH P < cc P
  cc0 : 0 < cc P
  cc1 : cc P ≤ 1
  pR1 : 1 < P.p*P.R
  piH0 : 0 < piH P
  piH1 : piH P < 1
  G1 : 1 < GH P
  GpR : GH P < P.p*P.R
  GLt : GH P < grossReturn P.lam P.δL
  GLpR : grossReturn P.lam P.δL < P.p*P.R
  xLow0 : 0 < xLow P.p P.q
  xsum : xLow P.p P.q + xBar P.p P.q = 1
  xBar1 : xBar P.p P.q < 1
  xLB : xLow P.p P.q < xBar P.p P.q
  lam0 : 0 < P.lam
  lam1 : P.lam < 1
  dLH : P.δL < P.δH
  Gdef : GH P * (1 - P.lam + P.lam*P.δH) = 1
  GLdefn : grossReturn P.lam P.δL * (1 - P.lam + P.lam*P.δL) = 1
  dHG : P.δH * GH P < 1

lemma basics (P : Params) : Basics P := by
  have hp := P.hq.trans P.hqp
  have hd : 0 < P.p - P.q := sub_pos.mpr P.hqp
  have hd2 : 0 < P.p^2 - P.q^2 := by nlinarith [P.hq]
  have hc := cost_bounds P
  have hgeo := fee_geometry P.p P.q P.B P.hq P.hqp P.hB
  have hfe : fH P = cc P * xBar P.p P.q := hgeo.2.2.2.2.2
  have hcc0 : 0 < cc P := hc.1
  have hf0 : 0 < fH P := by rw [hfe]; exact mul_pos hcc0 (hgeo.2.1.trans hgeo.2.2.1)
  have hfc : fH P < cc P := by
    rw [hfe]; nlinarith [hgeo.2.2.2.1]
  have hA2 : piH P < 1 := by
    have he : P.p*(P.R-P.p*P.B/(P.p^2-P.q^2))=piH P := by unfold piH fH; ring
    have := P.hA2; rw [he] at this; exact this
  have hGL := gross_gt_one P P.δL P.hδL0 P.hδL1
  have hGH := gross_gt_one P P.δH P.hδH0 P.hδH1
  have hord := gross_order P
  have hdLH : P.δL < P.δH := P.hA6a.trans P.hA6b
  have hpos := (PEFinance.gross_pos P.lam P.δH P.hlam0 P.hlam1 P.hδH0 P.hδH1).1
  have hposL := (PEFinance.gross_pos P.lam P.δL P.hlam0 P.hlam1 P.hδL0 P.hδL1).1
  have hGdef : GH P * (1 - P.lam + P.lam*P.δH) = 1 := by
    unfold GH grossReturn
    have : 1 - P.lam + P.lam*P.δH = 1 - P.lam*(1-P.δH) := by ring
    rw [this]; field_simp
  have hGLdef : grossReturn P.lam P.δL * (1 - P.lam + P.lam*P.δL) = 1 := by
    unfold grossReturn
    have : 1 - P.lam + P.lam*P.δL = 1 - P.lam*(1-P.δL) := by ring
    rw [this]; field_simp
  refine ⟨hp, hd, hd2, hfe, hf0, hfc, hcc0, hc.2.1, hc.2.2, ?_, hA2, hGH, hord.trans P.hA5,
    hord, P.hA5, hgeo.2.1, hgeo.2.2.2.2.1, hgeo.2.2.2.1, hgeo.2.2.1, P.hlam0, P.hlam1, hdLH,
    hGdef, hGLdef, ?_⟩
  · have hcc1 : cc P ≤ 1 := hc.2.1
    unfold piH; linarith [hfc, hc.2.2]
  · have h1 : P.δH < 1 - P.lam + P.lam*P.δH := by
      have := mul_pos (sub_pos.mpr P.hlam1) (sub_pos.mpr P.hδH1)
      nlinarith [P.hlam0, P.hδH0]
    have hGp : 0 < GH P := by
      have : (1:ℝ) < GH P := hGH
      linarith
    have ha : 0 < 1 - P.lam + P.lam*P.δH := by nlinarith [P.hlam1, P.hlam0, P.hδH0]
    by_contra hn
    push Not at hn
    have := mul_le_mul_of_nonneg_right hn ha.le
    have e : P.δH * GH P * (1 - P.lam + P.lam*P.δH) = P.δH := by rw [mul_assoc, hGdef, mul_one]
    linarith

lemma minCallFee_ge (P : Params) (k : ℝ) : fH P ≤ minCallFee P k := le_max_left _ _

lemma minCallFee_eq (P : Params) (k : ℝ) (hk : xLow P.p P.q ≤ k) : minCallFee P k = fH P := by
  have b := basics P
  unfold minCallFee
  apply max_eq_left
  change cc P * (1-k) ≤ fH P
  rw [b.fH_eq]
  apply mul_le_mul_of_nonneg_left _ b.cc0.le
  linarith [b.xsum]

lemma minCallFee_anti (P : Params) (k₁ k₂ : ℝ) (h : k₁ ≤ k₂) :
    minCallFee P k₂ ≤ minCallFee P k₁ := by
  have b := basics P
  unfold minCallFee
  apply max_le_max le_rfl
  change cc P * (1-k₂) ≤ cc P * (1-k₁)
  apply mul_le_mul_of_nonneg_left _ b.cc0.le
  linarith

lemma minCallFee_lt (P : Params) (k : ℝ) (hk : 0 ≤ k) : minCallFee P k < P.p*P.R :=
  (minimum_call P k hk).2.1

/-- profit formula from optimal contracts -/
lemma profit_eq (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsOptimalContract P r k x I f) : gpProfit P I f = Pi P r (minCallFee P k) := by
  rw [optimal_profit_formula P r k x I f hf]; rfl

lemma Pi_anti_r (P : Params) (m r₁ r₂ : ℝ) (hm : 0 < m) (hmT : m < P.p*P.R)
    (h1 : P.p*P.R - m < r₁)
    (h12 : r₁ < r₂) : Pi P r₂ m < Pi P r₁ m := by
  unfold Pi
  have hA := P.hA
  have d1 : 0 < r₁ - P.p*P.R + m := by linarith
  have d2 : 0 < r₂ - P.p*P.R + m := by linarith
  rw [div_lt_div_iff₀ d2 d1]
  have b := basics P
  have : 0 < m*P.A*(r₂-r₁)*(P.p*P.R-m) :=
    mul_pos (mul_pos (mul_pos hm hA) (sub_pos.mpr h12)) (by linarith)
  nlinarith

lemma Pi_pR (P : Params) (m : ℝ) (hm : 0 < m) : Pi P (P.p*P.R) m = P.p*P.R*P.A := by
  unfold Pi
  have : P.p*P.R - P.p*P.R + m = m := by ring
  rw [this]; field_simp

lemma Pi_gt_pRA (P : Params) (m r : ℝ) (hm : 0 < m) (hmT : m < P.p*P.R) (h1 : P.p*P.R - m < r)
    (h2 : r < P.p*P.R) : P.p*P.R*P.A < Pi P r m := by
  have := Pi_anti_r P m r (P.p*P.R) hm hmT h1 h2
  rwa [Pi_pR P m hm] at this

lemma Pi_anti_m (P : Params) (r m₁ m₂ : ℝ) (hr : 0 < r) (hrT : r ≤ P.p*P.R) (hm : m₁ ≤ m₂)
    (h1 : P.p*P.R - m₁ < r) : Pi P r m₂ ≤ Pi P r m₁ := by
  unfold Pi
  have hA := P.hA
  have d1 : 0 < r - P.p*P.R + m₁ := by linarith
  have d2 : 0 < r - P.p*P.R + m₂ := by linarith
  rw [div_le_div_iff₀ d2 d1]
  have : 0 ≤ r*P.A*(P.p*P.R - r)*(m₂ - m₁) :=
    mul_nonneg (mul_nonneg (mul_nonneg hr.le hA.le) (by linarith)) (by linarith)
  nlinarith

/-- profit along the ray k = d*r is strictly decreasing -/
lemma Pi_ray (P : Params) (d r s : ℝ) (hd : 0 < d) (hr : 0 < r) (hrs : r < s) (hs : 1 < s)
    (hsT : s ≤ P.p*P.R) (hdr : 0 < r - P.p*P.R + minCallFee P (d*r))
    (hds : 0 < s - P.p*P.R + minCallFee P (d*s)) :
    Pi P s (minCallFee P (d*s)) < Pi P r (minCallFee P (d*r)) := by
  have b := basics P
  have h := PEAlgebra.profit_strict_decreasing (P.p*P.R) (P.p*P.B/(P.p-P.q))
    (P.p^2*P.B/(P.p^2-P.q^2)) d r s b.cc0 b.cc1 b.pR1 b.fH0 b.fHc.le hd hr hrs hs hsT hdr hds
  have hp := mul_lt_mul_of_pos_right h P.hA
  unfold Pi
  dsimp [minCallFee] at *
  simpa only [div_mul_eq_mul_div] using hp

end PESec

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

noncomputable def Ds (P : Params) : ℝ := 1 - deltaHat P.p P.q P.lam

lemma pql_pos (P : Params) : 0 < P.p+(1-P.lam)*P.q := by
  have b := basics P
  have := mul_pos (sub_pos.mpr b.lam1) P.hq
  linarith [b.p0]

lemma Ds_facts (P : Params) : 1 - P.δH < Ds P ∧ Ds P < 1 - P.δL := by
  unfold Ds; constructor <;> linarith [P.hA6a, P.hA6b]

lemma Ds_eq (P : Params) : Ds P = P.p/(P.p+(1-P.lam)*P.q) := by
  have b := basics P
  have h := pql_pos P
  unfold Ds deltaHat; field_simp; ring

lemma one_sub_Ds (P : Params) : 1 - Ds P = (1-P.lam)*P.q/(P.p+(1-P.lam)*P.q) := by
  have b := basics P
  have h := pql_pos P
  rw [Ds_eq]; field_simp; ring

lemma den_pos (P : Params) (D : ℝ) (hD : D < 1) : 0 < 1 - P.lam*D := by
  have b := basics P
  rcases le_or_gt D 0 with h | h
  · nlinarith [b.lam0]
  · nlinarith [b.lam1, b.lam0]

lemma gf_le_iff (P : Params) (D : ℝ) (hD : D < 1) : gf P D ≤ xBar P.p P.q ↔ D ≤ Ds P := by
  have b := basics P
  have h1 := den_pos P D hD
  have h2 : 0 < P.p + P.q := by linarith [P.hq, b.p0]
  have h3 := pql_pos P
  unfold gf xBar
  rw [Ds_eq, div_le_div_iff₀ h1 h2, le_div_iff₀ h3]
  constructor <;> intro h <;> nlinarith

lemma gf_lt_iff (P : Params) (D : ℝ) (hD : D < 1) : gf P D < xBar P.p P.q ↔ D < Ds P := by
  have b := basics P
  have h1 := den_pos P D hD
  have h2 : 0 < P.p + P.q := by linarith [P.hq, b.p0]
  have h3 := pql_pos P
  unfold gf xBar
  rw [Ds_eq, div_lt_div_iff₀ h1 h2, lt_div_iff₀ h3]
  constructor <;> intro h <;> nlinarith

lemma gf_Ds (P : Params) : gf P (Ds P) = xBar P.p P.q := by
  have b := basics P
  have h2 : 0 < P.p + P.q := by linarith [P.hq, b.p0]
  have h3 := pql_pos P
  have hd : Ds P < 1 := by linarith [(Ds_facts P).2, P.hδL0]
  have h1 := den_pos P (Ds P) hd
  unfold gf xBar
  rw [div_eq_div_iff h1.ne' h2.ne']
  rw [Ds_eq] at h1 ⊢
  field_simp
  ring

lemma one_sub_PLf (P : Params) (D : ℝ) (hD : D < 1) : 1 - PLf P D = gf P D := by
  have h1 := den_pos P D hD
  unfold PLf gf
  rw [eq_div_iff h1.ne', sub_mul, div_mul_cancel₀ _ h1.ne']; ring

lemma gf_one_sub (P : Params) (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) : gf P (1-δ) = xHat P.lam δ := by
  have h := den_pos P (1-δ) (by linarith)
  unfold gf xHat
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h.ne']; ring

lemma minCallFee_PLf (P : Params) (D : ℝ) (hD : D < 1) :
    minCallFee P (PLf P D) = max (fH P) (cc P * gf P D) := by
  unfold minCallFee; rw [← one_sub_PLf P D hD]; rfl

lemma minCallFee_PLf_le (P : Params) (D : ℝ) (hD : D < 1) (h : D ≤ Ds P) :
    minCallFee P (PLf P D) = fH P := by
  have b := basics P
  rw [minCallFee_PLf P D hD]
  apply max_eq_left
  rw [b.fH_eq]
  exact mul_le_mul_of_nonneg_left ((gf_le_iff P D hD).2 h) b.cc0.le

lemma xLow_le_PLf (P : Params) (D : ℝ) (hD : D < 1) (h : D ≤ Ds P) :
    xLow P.p P.q ≤ PLf P D := by
  have b := basics P
  have := (gf_le_iff P D hD).2 h
  rw [← one_sub_PLf P D hD] at this
  linarith [b.xsum]

lemma RLf_PLf (P : Params) (D : ℝ) : RLf P D * (1-D) = PLf P D := by
  unfold RLf PLf; ring

lemma RLf_gt_one (P : Params) (D : ℝ) (h0 : 0 < D) (h1 : D < 1) : 1 < RLf P D := by
  have b := basics P
  have hd := den_pos P D h1
  unfold RLf
  rw [lt_div_iff₀ hd]; nlinarith [b.lam0]

lemma RLf_le_GL (P : Params) (D : ℝ) (h1 : D ≤ 1 - P.δL) :
    RLf P D ≤ grossReturn P.lam P.δL := by
  have b := basics P
  have hd := den_pos P D (by linarith [P.hδL0])
  have hd2 := den_pos P (1-P.δL) (by linarith [P.hδL0])
  unfold RLf grossReturn
  rw [div_le_div_iff₀ hd hd2]; nlinarith [b.lam0]

lemma RLf_lt_pR (P : Params) (D : ℝ) (h1 : D ≤ 1 - P.δL) : RLf P D < P.p*P.R :=
  (RLf_le_GL P D h1).trans_lt (basics P).GLpR

lemma GH_eq_RLf (P : Params) : RLf P (1-P.δH) = GH P := by
  unfold RLf GH grossReturn; rfl

lemma PLf_dH (P : Params) : PLf P (1-P.δH) = P.δH * GH P := by
  unfold PLf GH grossReturn; ring

lemma xLow_le_dHG (P : Params) : xLow P.p P.q ≤ P.δH * GH P := by
  rw [← PLf_dH]
  exact xLow_le_PLf P _ (by linarith [P.hδH0]) (by linarith [(Ds_facts P).1])

lemma minCallFee_dH (P : Params) (r : ℝ) (hr : GH P ≤ r) : minCallFee P (P.δH*r) = fH P := by
  apply minCallFee_eq
  exact (xLow_le_dHG P).trans (mul_le_mul_of_nonneg_left hr P.hδH0.le)

lemma piL_pos (P : Params) (D : ℝ) (hD : D < 1) (hD0 : 0 ≤ PLf P D) : 0 < piL P D := by
  unfold piL; linarith [minCallFee_lt P (PLf P D) hD0]

lemma piL_le (P : Params) (D : ℝ) : piL P D ≤ piH P := by
  unfold piL piH; linarith [minCallFee_ge P (PLf P D)]

lemma PLf_nonneg (P : Params) (D : ℝ) (hD : D < 1) : 0 ≤ PLf P D := by
  have := den_pos P D hD
  unfold PLf; exact div_nonneg (by linarith) this.le

lemma PLf_anti (P : Params) (D₁ D₂ : ℝ) (h12 : D₁ ≤ D₂) (h2 : D₂ < 1) :
    PLf P D₂ ≤ PLf P D₁ := by
  have b := basics P
  have hd1 := den_pos P D₁ (by linarith)
  have hd2 := den_pos P D₂ h2
  unfold PLf
  rw [div_le_div_iff₀ hd2 hd1]
  nlinarith [b.lam1]

lemma piL_anti (P : Params) (D₁ D₂ : ℝ) (h12 : D₁ ≤ D₂) (h2 : D₂ < 1) :
    piL P D₂ ≤ piL P D₁ := by
  unfold piL
  linarith [minCallFee_anti P _ _ (PLf_anti P D₁ D₂ h12 h2)]

lemma Phi_formula (P : Params) (D : ℝ) (h0 : 0 < D) (h1 : D < 1) :
    Phi P D = piL P D * P.A * (1-D) / (1 - piL P D * (1 - P.lam*D)) := by
  have b := basics P
  have hd := den_pos P D h1
  have hp1 : piL P D < 1 := (piL_le P D).trans_lt b.piH1
  have hp0 := piL_pos P D h1 (PLf_nonneg P D h1)
  have hq : 0 < 1 - piL P D * (1 - P.lam*D) := by
    have : piL P D * (1 - P.lam*D) < 1 := by
      calc piL P D * (1 - P.lam*D) ≤ piL P D * 1 := by
            apply mul_le_mul_of_nonneg_left _ hp0.le; nlinarith [b.lam0]
        _ < 1 := by linarith
    linarith
  unfold Phi NLf RLf PLf
  have e : 1 / (1 - P.lam * D) - piL P D = (1 - piL P D * (1 - P.lam*D))/(1 - P.lam*D) := by
    field_simp
  rw [e]
  field_simp

lemma Phi_pos (P : Params) (D : ℝ) (h0 : 0 < D) (h1 : D < 1) : 0 < Phi P D := by
  have b := basics P
  have hd := den_pos P D h1
  have hp1 : piL P D < 1 := (piL_le P D).trans_lt b.piH1
  have hp0 := piL_pos P D h1 (PLf_nonneg P D h1)
  have hq : 0 < 1 - piL P D * (1 - P.lam*D) := by
    have : piL P D * (1 - P.lam*D) < 1 := by
      calc piL P D * (1 - P.lam*D) ≤ piL P D * 1 := by
            apply mul_le_mul_of_nonneg_left _ hp0.le; nlinarith [b.lam0]
        _ < 1 := by linarith
    linarith
  rw [Phi_formula P D h0 h1]
  apply div_pos _ hq
  exact mul_pos (mul_pos hp0 P.hA) (by linarith)

lemma Phi_strictAnti (P : Params) (D₁ D₂ : ℝ) (h0 : 0 < D₁) (h12 : D₁ < D₂) (h2 : D₂ < 1) :
    Phi P D₂ < Phi P D₁ := by
  have b := basics P
  have hD1 : D₁ < 1 := by linarith
  have hd1 := den_pos P D₁ hD1
  have hd2 := den_pos P D₂ h2
  have hp1 : piL P D₁ < 1 := (piL_le P D₁).trans_lt b.piH1
  have hp0 := piL_pos P D₁ hD1 (PLf_nonneg P D₁ hD1)
  have hp1' : piL P D₂ < 1 := (piL_le P D₂).trans_lt b.piH1
  have hp0' := piL_pos P D₂ h2 (PLf_nonneg P D₂ h2)
  have hanti := piL_anti P D₁ D₂ h12.le h2
  rw [Phi_formula P D₁ h0 hD1, Phi_formula P D₂ (h0.trans h12) h2]
  -- write as A(1-D)/(1/π - (1-λD))
  set a := piL P D₁
  set c := piL P D₂
  have q1 : 0 < 1 - a * (1 - P.lam*D₁) := by
    have : a * (1 - P.lam*D₁) < 1 := by
      calc a * (1 - P.lam*D₁) ≤ a * 1 := by
            apply mul_le_mul_of_nonneg_left _ hp0.le; nlinarith [b.lam0]
        _ < 1 := by linarith
    linarith
  have q2 : 0 < 1 - c * (1 - P.lam*D₂) := by
    have : c * (1 - P.lam*D₂) < 1 := by
      calc c * (1 - P.lam*D₂) ≤ c * 1 := by
            apply mul_le_mul_of_nonneg_left _ hp0'.le; nlinarith [b.lam0, h0.trans h12]
        _ < 1 := by linarith
    linarith
  rw [div_lt_div_iff₀ q2 q1]
  -- c*A*(1-D2)*(1 - a(1-λD1)) < a*A*(1-D1)*(1 - c(1-λD2))
  -- equivalently A[ c(1-D2) - a(1-D1) + a c ((1-D1)(1-λD2) - (1-D2)(1-λD1)) ] < 0
  have hA := P.hA
  have k1 : c*(1-D₂) ≤ a*(1-D₂) := mul_le_mul_of_nonneg_right hanti (by linarith)
  have k2 : a*(1-D₂) < a*(1-D₁) := mul_lt_mul_of_pos_left (by linarith) hp0
  have e : (1-D₁)*(1-P.lam*D₂) - (1-D₂)*(1-P.lam*D₁) = (1-P.lam)*(D₂-D₁) := by ring
  have k3 : 0 < a*c*((1-P.lam)*(D₂-D₁)) :=
    mul_pos (mul_pos hp0 hp0') (mul_pos (by linarith [b.lam1]) (by linarith))
  have hX : 0 < a*(1-D₁)*(1-c*(1-P.lam*D₂)) - c*(1-D₂)*(1-a*(1-P.lam*D₁)) := by
    have k4 : 0 < a*(D₂-D₁)*(1 - c*(1-P.lam)) :=
      mul_pos (mul_pos hp0 (by linarith)) (by nlinarith [b.lam1, b.lam0])
    nlinarith
  nlinarith [mul_pos hA hX]

lemma Phi_cont (P : Params) : ContinuousOn (Phi P) (Set.Icc (1-P.δH) (1-P.δL)) := by
  have b := basics P
  have hA : ∀ D ∈ Set.Icc (1-P.δH) (1-P.δL), 0 < D ∧ D < 1 := by
    intro D hD; exact ⟨by linarith [hD.1, P.hδH1], by linarith [hD.2, P.hδL0]⟩
  have heq : Set.EqOn (Phi P)
      (fun D => (P.p*P.R - max (fH P) (cc P * ((1-P.lam)*D/(1-P.lam*D)))) * P.A * (1-D) /
        (1 - (P.p*P.R - max (fH P) (cc P * ((1-P.lam)*D/(1-P.lam*D)))) * (1 - P.lam*D)))
      (Set.Icc (1-P.δH) (1-P.δL)) := by
    intro D hD
    obtain ⟨h0, h1⟩ := hA D hD
    simp only
    rw [Phi_formula P D h0 h1]
    unfold piL
    rw [minCallFee_PLf P D h1]
    rfl
  refine ContinuousOn.congr ?_ heq
  have hden : ∀ D ∈ Set.Icc (1-P.δH) (1-P.δL), 1 - P.lam*D ≠ 0 := by
    intro D hD; exact (den_pos P D (hA D hD).2).ne'
  have hc1 : ContinuousOn (fun D : ℝ => (1-P.lam)*D/(1-P.lam*D)) (Set.Icc (1-P.δH) (1-P.δL)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop) hden
  have hc2 : ContinuousOn (fun D : ℝ => P.p*P.R - max (fH P) (cc P * ((1-P.lam)*D/(1-P.lam*D))))
      (Set.Icc (1-P.δH) (1-P.δL)) :=
    continuousOn_const.sub (continuousOn_const.sup (continuousOn_const.mul hc1))
  apply ContinuousOn.div
  · exact (hc2.mul continuousOn_const).mul (by fun_prop)
  · exact continuousOn_const.sub (hc2.mul (by fun_prop))
  · intro D hD
    obtain ⟨h0, h1⟩ := hA D hD
    have := Phi_formula P D h0 h1
    have hd := den_pos P D h1
    have hp1 : piL P D < 1 := (piL_le P D).trans_lt b.piH1
    have hp0 := piL_pos P D h1 (PLf_nonneg P D h1)
    have : piL P D * (1 - P.lam*D) < 1 := by
      calc piL P D * (1 - P.lam*D) ≤ piL P D * 1 := by
            apply mul_le_mul_of_nonneg_left _ hp0.le; nlinarith [b.lam0]
        _ < 1 := by linarith
    have e : P.p*P.R - max (fH P) (cc P * ((1-P.lam)*D/(1-P.lam*D))) = piL P D := by
      unfold piL; rw [minCallFee_PLf P D h1]; rfl
    rw [e]; linarith

lemma Phi_dH (P : Params) : Phi P (1-P.δH) = N0 P * (P.δH * GH P) := by
  have b := basics P
  unfold Phi NLf N0
  have h1 : piL P (1-P.δH) = piH P := by
    unfold piL piH; rw [PLf_dH, minCallFee_eq P _ (xLow_le_dHG P)]
  rw [h1, GH_eq_RLf, PLf_dH]

end PESec

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

lemma vPE_self (lam δ r : ℝ) : vPE lam δ r (δ*r) = (1-lam+lam*δ)*r := by
  unfold vPE; rw [max_self]; ring

lemma vCash_H_eq (P : Params) (RL RH PL : ℝ) (hRH : 0 < RH) :
    vCash P.lam P.δH RL RH PL (P.δH*RH) = 1-P.lam+P.lam*max 1 (P.δH*(RL/PL)) := by
  have hd := P.hδH0
  have e : RH/(P.δH*RH) = 1/P.δH := by field_simp
  unfold vCash; rw [e, mul_max_of_nonneg _ _ hd.le, mul_one_div_cancel hd.ne']
  rw [max_comm (P.δH*(RL/PL)) 1, ← max_assoc, max_self]

lemma vCash_L_eq (P : Params) (RL RH PL : ℝ) (hRH : 0 < RH) :
    vCash P.lam P.δL RL RH PL (P.δH*RH) = 1-P.lam+P.lam*max 1 (P.δL*(RL/PL)) := by
  have b := basics P
  have e : RH/(P.δH*RH) = 1/P.δH := by field_simp
  unfold vCash; rw [e, mul_max_of_nonneg _ _ P.hδL0.le]
  have h : P.δL*(1/P.δH) < 1 := by rw [mul_one_div, div_lt_one P.hδH0]; exact b.dLH
  rw [max_comm (P.δL*(RL/PL)), ← max_assoc, max_eq_left h.le]

lemma size_lt (P : Params) (r k x I : ℝ) (f : Outcome → ℝ)
    (hf : IsFeasibleContract P r k x I f) (hr : 1 < r) : I-P.A < P.A/(1-piH P) - P.A := by
  have b := basics P
  have hI : 0 < I := P.hA.trans hf.2.2.2.2.1
  have hF := (fee_bounds P.p P.q P.B P.R x P.hq P.hqp f hf.2.2.1 hf.2.2.2.1).1
  have hden : 0 < 1-piH P := by linarith [b.piH1]
  have hprod := mul_pos (sub_pos.mpr hr) (sub_pos.mpr hf.2.2.2.2.1)
  change fH P ≤ _ at hF
  have hbound := mul_nonneg (sub_nonneg.mpr hF) hI.le
  have hi : I < P.A/(1-piH P) := by
    apply (lt_div_iff₀ hden).mpr
    have he := hf.2.2.2.2.2.1
    unfold piH
    nlinarith [hf.2.2.2.2.2.1]
  linarith

lemma Lcap_conv (P : Params)
    (hLcap : P.A / (1 - (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) - P.A ≤
      P.K - P.δH * PELiquidity.Primary.grossReturn P.lam P.δH *
        ((P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)) * P.A /
          (PELiquidity.Primary.grossReturn P.lam P.δH -
            (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))))) :
    P.A/(1-piH P) - P.A ≤ P.K - Phi P (1-P.δH) := by
  rw [Phi_dH]
  have : N0 P * (P.δH * GH P) = P.δH * PELiquidity.Primary.grossReturn P.lam P.δH *
        ((P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)) * P.A /
          (PELiquidity.Primary.grossReturn P.lam P.δH -
            (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)))) := by
    unfold N0 piH fH GH; ring
  rw [this]; exact hLcap

lemma A7_conv (P : Params)
    (hA7 : P.p * P.R ≤ PELiquidity.Primary.grossReturn P.lam P.δH *
      (1 - P.lam + P.lam * P.δH *
        (P.p + (1 - P.lam) * P.q) / ((1 - P.lam) * P.q))) :
    P.p*P.R ≤ GH P * (1 - P.lam + P.lam*P.δH/(1 - Ds P)) := by
  have b := basics P
  have e : P.lam * P.δH * (P.p + (1 - P.lam) * P.q) / ((1 - P.lam) * P.q) =
      P.lam*P.δH/(1 - Ds P) := by
    rw [one_sub_Ds]
    have h1 : 0 < 1 - P.lam := by linarith [b.lam1]
    have h2 := pql_pos P
    field_simp
  rw [e] at hA7; exact hA7

/-- the minimum H return grows with the discount -/
lemma VH_mono (P : Params) (D₁ D₂ : ℝ) (h12 : D₁ < D₂) (h2 : D₂ < 1) :
    GH P * (1 - P.lam + P.lam*P.δH/(1 - D₁)) < GH P * (1 - P.lam + P.lam*P.δH/(1 - D₂)) := by
  have b := basics P
  have hG : 0 < GH P := by linarith [b.G1]
  apply mul_lt_mul_of_pos_left _ hG
  have : P.lam*P.δH/(1 - D₁) < P.lam*P.δH/(1 - D₂) := by
    apply div_lt_div_of_pos_left (mul_pos b.lam0 P.hδH0) (by linarith) (by linarith)
  linarith

lemma A7_ge (P : Params)
    (hA7 : P.p*P.R ≤ GH P * (1 - P.lam + P.lam*P.δH/(1 - Ds P))) (D : ℝ)
    (hD : Ds P ≤ D) (hD1 : D < 1) : P.p*P.R ≤ GH P * (1 - P.lam + P.lam*P.δH/(1 - D)) := by
  rcases eq_or_lt_of_le hD with h | h
  · rw [← h]; exact hA7
  · exact hA7.trans (VH_mono P _ _ h hD1).le

lemma A7_gt (P : Params)
    (hA7 : P.p*P.R ≤ GH P * (1 - P.lam + P.lam*P.δH/(1 - Ds P))) (D : ℝ)
    (hD : Ds P < D) (hD1 : D < 1) : P.p*P.R < GH P * (1 - P.lam + P.lam*P.δH/(1 - D)) :=
  hA7.trans_lt (VH_mono P _ _ hD hD1)

/-- Lemma 3 in the form RminL(D) < RminH(D). -/
lemma RLf_lt_RminH (P : Params) (D : ℝ) (h0 : 1 - P.δH < D) (h1 : D < 1) :
    RLf P D < GH P * (1 - P.lam + P.lam*P.δH/(1 - D)) := by
  have b := basics P
  have hd := den_pos P D h1
  have hD0 : 0 < D := by linarith [P.hδH1]
  have hG : GH P = 1/(1 - P.lam + P.lam*P.δH) := by
    have h := b.Gdef
    have ha : 0 < 1 - P.lam + P.lam*P.δH := by nlinarith [b.lam0, b.lam1, P.hδH0]
    field_simp; linarith
  have ha : 0 < 1 - P.lam + P.lam*P.δH := by nlinarith [b.lam0, b.lam1, P.hδH0]
  have h1D : 0 < 1 - D := by linarith
  rw [hG]; unfold RLf
  have e : 1 / (1 - P.lam + P.lam * P.δH) * (1 - P.lam + P.lam * P.δH / (1 - D)) =
      ((1-P.lam)*(1-D) + P.lam*P.δH)/((1 - P.lam + P.lam * P.δH)*(1-D)) := by
    field_simp
  rw [e, div_lt_div_iff₀ hd (mul_pos ha h1D)]
  have k : 0 < P.lam*(1-P.lam)*D*(P.δH - (1-D)) :=
    mul_pos (mul_pos (mul_pos b.lam0 (by linarith [b.lam1])) hD0) (by linarith)
  nlinarith [k]

/-- If L-LPs strictly gain from PE with a claim worth less than xLow, the discount exceeds Ds. -/
lemma xLow_case (P : Params) (RL PL D : ℝ) (hRL : 0 < RL) (hD1 : D < 1)
    (hPL : PL = RL*(1-D)) (hv : 1 < (1-P.lam)*RL + P.lam*PL) (hx : PL < xLow P.p P.q) :
    Ds P < D := by
  have b := basics P
  have hd := den_pos P D hD1
  have h1 : 1 < RL*(1-P.lam*D) := by rw [hPL] at hv; nlinarith
  have h2 : PLf P D < xLow P.p P.q := by
    have : PLf P D < PL := by
      unfold PLf; rw [div_lt_iff₀ hd, hPL]
      have : 0 < 1 - D := by linarith
      nlinarith
    linarith
  by_contra hn
  push Not at hn
  linarith [xLow_le_PLf P D hD1 hn]

/-- U2: the cheapest L-fund acceptable at discount D ≤ Ds is at least as profitable as an
undistorted fund at the L-LP break-even return. -/
lemma U2 (P : Params) (RL PL D xL IL : ℝ) (fL : Outcome → ℝ) (hRL : 0 < RL)
    (h0 : 1 - P.δH < D) (hDs : D ≤ Ds P) (hPL : PL = RL*(1-D))
    (hL : IsOptimalContract P RL PL xL IL fL) (hv : RL*(1-P.lam*D) ≤ 1) :
    Pi P (RLf P D) (fH P) ≤ gpProfit P IL fL := by
  have b := basics P
  have hD1 : D < 1 := by linarith [(Ds_facts P).2, P.hδL0]
  have hD0 : 0 < D := by linarith [P.hδH1]
  have hd := den_pos P D hD1
  have hRle : RL ≤ RLf P D := by
    unfold RLf; rw [le_div_iff₀ hd]; linarith
  have hm : minCallFee P ((1-D)*RLf P D) = fH P := by
    rw [mul_comm, RLf_PLf]; exact minCallFee_PLf_le P D hD1 hDs
  rw [profit_eq P _ _ _ _ _ hL]
  have hgap := optimal_pledge_gap P _ _ _ _ _ hL
  have hPL' : PL = (1-D)*RL := by rw [hPL, mul_comm]
  rcases lt_or_eq_of_le hRle with h | h
  · have hs1 := RLf_gt_one P D hD0 hD1
    have hsT := (RLf_lt_pR P D (by linarith [(Ds_facts P).2])).le
    have := Pi_ray P (1-D) RL (RLf P D) (by linarith) hRL h hs1 hsT
      (by rw [← hPL']; linarith) (by rw [hm]; linarith [b.piH1, b.piH0, show piH P = P.p*P.R - fH P from rfl])
    rw [hm, ← hPL'] at this
    exact this.le
  · have : PL = PLf P D := by rw [hPL, h, RLf_PLf]
    rw [this, minCallFee_PLf_le P D hD1 hDs, h]

end PESec

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

lemma supply_pos_ge {vpe vc cap S : ℝ} (h : IsCapitalSupply vpe vc cap S) (hS : 0 < S) :
    vc ≤ vpe := by
  by_contra hn; push Not at hn; have := h.1 hn; linarith

lemma supply_zero_le {vpe vc cap S : ℝ} (h : IsCapitalSupply vpe vc cap S) (hS : S = 0)
    (hc : 0 < cap) : vpe ≤ vc := by
  by_contra hn; push Not at hn; have := h.2.2 hn; linarith

lemma Pi_inj (P : Params) (r s : ℝ) (hr : P.p*P.R - fH P < r) (hs : P.p*P.R - fH P < s)
    (h : Pi P r (fH P) = Pi P s (fH P)) : r = s := by
  have b := basics P
  have hT : fH P < P.p*P.R := by linarith [b.piH0, show piH P = P.p*P.R - fH P from rfl]
  rcases lt_trichotomy r s with h1 | h1 | h1
  · have := Pi_anti_r P (fH P) r s b.fH0 hT hr h1; linarith
  · exact h1
  · have := Pi_anti_r P (fH P) s r b.fH0 hT hs h1; linarith

lemma Pi_G_ge (P : Params) (r : ℝ) (hr : GH P ≤ r) :
    Pi P r (fH P) ≤ Pi P (GH P) (fH P) := by
  have b := basics P
  have hT : fH P < P.p*P.R := by linarith [b.piH0, show piH P = P.p*P.R - fH P from rfl]
  rcases eq_or_lt_of_le hr with h | h
  · rw [h]
  · exact (Pi_anti_r P (fH P) _ _ b.fH0 hT
      (by linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl]) h).le

lemma aH_pos (P : Params) : 0 < 1 - P.lam + P.lam*P.δH := by
  have := mul_pos P.hlam0 P.hδH0; linarith [P.hlam1]

lemma G_le_iff (P : Params) (r : ℝ) : GH P ≤ r ↔ 1 ≤ (1 - P.lam + P.lam*P.δH)*r := by
  have b := basics P
  have ha := aH_pos P
  have hG : GH P = 1/(1 - P.lam + P.lam*P.δH) := by
    rw [eq_div_iff ha.ne']; exact b.Gdef
  rw [hG, div_le_iff₀ ha, mul_comm]

lemma G_lt_iff (P : Params) (r : ℝ) : GH P < r ↔ 1 < (1 - P.lam + P.lam*P.δH)*r := by
  have b := basics P
  have ha := aH_pos P
  have hG : GH P = 1/(1 - P.lam + P.lam*P.δH) := by
    rw [eq_div_iff ha.ne']; exact b.Gdef
  rw [hG, div_lt_iff₀ ha, mul_comm]

/-- Classification of equilibria in which H-funds are raised. -/
theorem caseH (P : Params)
    (hA7 : P.p*P.R ≤ GH P * (1 - P.lam + P.lam*P.δH/(1 - Ds P)))
    (hLcap : P.A/(1-piH P) - P.A ≤ P.K - Phi P (1-P.δH))
    (muH : ℝ) (E : AllocationSec) (hmu0 : 0 < muH) (hmu1 : muH < 1)
    (hE : IsEquilibriumSec P muH E) (hαH : 0 < E.αH) :
    Phi P (1-P.δH) < muH * P.K ∧ (0 < E.αL → E.RH = E.RL) := by
  have b := basics P
  obtain ⟨hPL, hRL, hRH, hoL, hoH, haL0, haH0, hsum, hgpL, hgpH, hsupL, hsupH, hs1, hs2, hs3,
    hd1, hd2, hd3, hds⟩ := hE
  have hNL : P.A < E.IL := hoL.1.2.2.2.2.1
  have hNH : P.A < E.IH := hoH.1.2.2.2.2.1
  have hRLT := optimal_return_le P _ _ _ _ _ hoL
  have hRHT := optimal_return_le P _ _ _ _ _ hoH
  have hPiL := profit_eq P _ _ _ _ _ hoL
  have hPiH := profit_eq P _ _ _ _ _ hoH
  have hgapL := optimal_pledge_gap P _ _ _ _ _ hoL
  have hgapH := optimal_pledge_gap P _ _ _ _ _ hoH
  rw [vCash_L_eq P _ _ _ hRH] at hsupL
  rw [vCash_H_eq P _ _ _ hRH, vPE_self] at hsupH
  unfold vPE at hsupL
  have hK := P.hK
  have hcapL : 0 < (1-muH)*P.K := mul_pos (by linarith) hK
  have hSH : 0 < E.αH*(E.IH-P.A) := mul_pos hαH (by linarith)
  have hVH := supply_pos_ge hsupH hSH
  have ha := aH_pos P
  have hGpos : 0 < GH P := by linarith [b.G1]
  have hTfH : fH P < P.p*P.R := by linarith [b.piH0, show piH P = P.p*P.R - fH P from rfl]
  -- RH ≥ G
  have hRHG : GH P ≤ E.RH := by
    rw [G_le_iff]
    have := mul_le_mul_of_nonneg_left (le_max_left 1 (P.δH*(E.RL/E.PL))) b.lam0.le
    linarith
  have hmH : minCallFee P (P.δH*E.RH) = fH P := minCallFee_dH P _ hRHG
  rw [hmH] at hPiH
  rcases lt_trichotomy (P.δH*E.RL) E.PL with hT | hT | hT
  · -- T1: price above H valuation: no trade, contradiction
    exfalso
    have hdH := hd3 hT
    have hsL : E.sL = 0 := by rw [← hds, hdH]
    have hLlt : P.δL*E.RL < E.PL := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right b.dLH.le hRL.le) hT
    have haL : E.αL = 0 := by
      have := hs2 hLlt; rw [hsL] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · exact h
      · linarith
    have ht1 : P.δL*(E.RL/E.PL) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hPL]; exact hLlt.le
    rw [max_eq_left ht1, max_eq_right hLlt.le] at hsupL
    have hvL := supply_zero_le hsupL (by rw [haL, zero_mul]) hcapL
    have hRLG : E.RL < GH P := by
      have := mul_lt_mul_of_pos_left hT b.lam0
      have : ¬ (GH P ≤ E.RL) := by rw [G_le_iff]; linarith
      exact lt_of_not_ge this
    have k1 : Pi P E.RL (minCallFee P (P.δH*E.RL)) ≤ Pi P E.RL (minCallFee P (max (P.δL*E.RL) E.PL)) := by
      rw [max_eq_right hLlt.le]
      exact Pi_anti_m P _ _ _ hRL hRLT (minCallFee_anti P _ _ hT.le)
        (by rw [max_eq_right hLlt.le] at hgapL; exact hgapL)
    have k2 : Pi P (GH P) (minCallFee P (P.δH*GH P)) < Pi P E.RL (minCallFee P (P.δH*E.RL)) := by
      apply Pi_ray P P.δH E.RL (GH P) P.hδH0 hRL hRLG b.G1 b.GpR.le
      · have := minCallFee_anti P _ _ hT.le
        rw [max_eq_right hLlt.le] at hgapL; linarith
      · rw [minCallFee_dH P _ le_rfl]; linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl]
    rw [minCallFee_dH P _ le_rfl] at k2
    have k3 := Pi_G_ge P _ hRHG
    have := hgpH hαH
    rw [hPiL, hPiH] at this
    linarith
  · -- T2: price equals H valuation
    have hLlt : P.δL*E.RL < E.PL := by
      rw [← hT]; exact mul_lt_mul_of_pos_right b.dLH hRL
    have hkL : max (P.δL*E.RL) E.PL = P.δH*E.RL := by rw [max_eq_right hLlt.le, hT]
    have ht1 : P.δL*(E.RL/E.PL) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hPL]; exact hLlt.le
    have ht2 : P.δH*(E.RL/E.PL) = 1 := by
      rw [mul_div_assoc', div_eq_one_iff_eq hPL.ne']; exact hT
    rw [max_eq_left ht1, hkL] at hsupL
    rw [ht2, max_self] at hsupH
    rw [hkL] at hPiL hgapL
    have hsL := hs2 hLlt
    obtain ⟨hdH0, hdHle⟩ := hd2 hT.symm
    rcases eq_or_lt_of_le haL0 with haL | haL
    · -- only H-funds
      have hvL := supply_zero_le hsupL (by rw [← haL, zero_mul]) hcapL
      have hRLG : E.RL ≤ GH P := by
        have : ¬ (GH P < E.RL) := by rw [G_lt_iff]; linarith
        exact le_of_not_gt this
      have k1 : Pi P (GH P) (fH P) ≤ Pi P E.RL (minCallFee P (P.δH*E.RL)) := by
        rcases eq_or_lt_of_le hRLG with h | h
        · rw [h, minCallFee_dH P _ le_rfl]
        · have := Pi_ray P P.δH E.RL (GH P) P.hδH0 hRL h b.G1 b.GpR.le (by linarith)
            (by rw [minCallFee_dH P _ le_rfl]; linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl])
          rw [minCallFee_dH P _ le_rfl] at this; exact this.le
      have hRHeq : E.RH = GH P := by
        by_contra hne
        have hlt : GH P < E.RH := lt_of_le_of_ne hRHG (Ne.symm hne)
        have k2 := Pi_anti_r P (fH P) _ _ b.fH0 hTfH
          (by linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl]) hlt
        have := hgpH hαH
        rw [hPiL, hPiH] at this
        linarith
      have haH1 : E.αH = 1 := by linarith
      have hIH : E.IH - P.A = N0 P := by
        have := (optimal_fee_size P _ _ _ _ _ hoH (by rw [hRHeq]; exact b.GpR)).2
        rw [this, hmH, hRHeq]; unfold N0 piH
        have : 0 < GH P - (P.p*P.R - fH P) := by linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl]
        field_simp; ring
      have hv1 : (1 - P.lam + P.lam*P.δH)*E.RH = 1 - P.lam + P.lam*1 := by
        rw [hRHeq, mul_comm, b.Gdef]; ring
      have := (hsupH.2.1 hv1).2
      rw [haH1, one_mul, hIH] at this
      refine ⟨?_, fun h => absurd haL (ne_of_lt h)⟩
      rw [Phi_dH]
      have hN0 : 0 < N0 P := by rw [← hIH]; linarith
      have := mul_lt_mul_of_pos_left b.dHG hN0
      linarith
    · -- both funds
      have hvL := supply_pos_ge hsupL (mul_pos haL (by linarith))
      have hRLG : GH P ≤ E.RL := by
        rw [G_le_iff]; linarith
      rw [minCallFee_dH P _ hRLG] at hPiL hgapL
      have heqPi : Pi P E.RL (fH P) = Pi P E.RH (fH P) := by
        have h1 := hgpL haL; have h2 := hgpH hαH
        rw [hPiL, hPiH] at h1 h2; linarith
      have hRR : E.RL = E.RH := Pi_inj P _ _ hgapL
        (by rw [hmH] at hgapH; exact hgapH) heqPi
      have hRHeq : E.RH = GH P := by
        by_contra hne
        have hlt : GH P < E.RH := lt_of_le_of_ne hRHG (Ne.symm hne)
        have hv : 1 - P.lam + P.lam*1 < (1 - P.lam + P.lam*P.δH)*E.RH := by
          have : 1 < (1 - P.lam + P.lam*P.δH)*E.RH := (G_lt_iff P _).1 hlt
          linarith
        have hfull := hsupH.2.2 hv
        have : E.dH ≤ 0 := by rw [hfull, sub_self, zero_div] at hdHle; exact hdHle
        have : E.αL*(E.IL-P.A) ≤ 0 := by rw [← hsL, ← hds]; exact this
        have := mul_pos haL (show 0 < E.IL - P.A by linarith)
        linarith
      have hIH : E.IH - P.A = N0 P := by
        have := (optimal_fee_size P _ _ _ _ _ hoH (by rw [hRHeq]; exact b.GpR)).2
        rw [this, hmH, hRHeq]; unfold N0 piH
        have : 0 < GH P - (P.p*P.R - fH P) := by linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl]
        field_simp; ring
      have hIL : E.IL - P.A = N0 P := by
        have := (optimal_fee_size P _ _ _ _ _ hoL (by rw [hRR, hRHeq]; exact b.GpR)).2
        rw [this, hkL, minCallFee_dH P _ hRLG, hRR, hRHeq]; unfold N0 piH
        have : 0 < GH P - (P.p*P.R - fH P) := by linarith [b.G1, b.piH1, show piH P = P.p*P.R - fH P from rfl]
        field_simp; ring
      refine ⟨?_, fun _ => hRR.symm⟩
      rw [hds, hsL, hIL, hIH] at hdHle
      have hPLv : E.PL = P.δH * GH P := by rw [← hT, hRR, hRHeq]
      rw [hPLv, le_div_iff₀ (by rw [← hPLv]; exact hPL)] at hdHle
      rw [Phi_dH]
      have hN0 : 0 < N0 P := by rw [← hIH]; linarith
      have h1 : E.αH * N0 P * (P.δH * GH P) < E.αH * N0 P :=
        mul_lt_of_lt_one_right (mul_pos hαH hN0) b.dHG
      have e : N0 P * (P.δH * GH P) = E.αL * N0 P * (P.δH * GH P) + E.αH * N0 P * (P.δH * GH P) := by
        rw [← add_mul, ← add_mul, hsum, one_mul]
      linarith
  · -- T3: price below H valuation
    set D := 1 - E.PL/E.RL with hDdef
    have hPLD : E.PL = E.RL*(1-D) := by rw [hDdef]; field_simp; ring
    have hD1 : D < 1 := by have := div_pos hPL hRL; linarith
    have h1D : 0 < 1 - D := by linarith
    have hDH : 1 - P.δH < D := by
      have : E.PL/E.RL < P.δH := by rw [div_lt_iff₀ hRL]; linarith [hT]
      linarith
    have hD0 : 0 < D := by linarith [P.hδH1]
    have hratio : E.RL/E.PL = 1/(1-D) := by rw [hPLD]; field_simp
    have hHmax : max 1 (P.δH*(E.RL/E.PL)) = P.δH/(1-D) := by
      rw [hratio, mul_one_div]; apply max_eq_right; rw [le_div_iff₀ h1D]; linarith
    rw [hHmax] at hsupH hVH
    have hRHge : GH P * (1 - P.lam + P.lam*(P.δH/(1-D))) ≤ E.RH := by
      have := mul_le_mul_of_nonneg_left hVH hGpos.le
      rw [← mul_assoc, b.Gdef, one_mul] at this; exact this
    have hmd : P.lam*(P.δH/(1-D)) = P.lam*P.δH/(1-D) := by ring
    rw [hmd] at hRHge
    have hDs : D ≤ Ds P := by
      by_contra hn; push Not at hn
      have := A7_gt P hA7 D hn hD1
      linarith
    have hDL : D < 1 - P.δL := lt_of_le_of_lt hDs (Ds_facts P).2
    have hLlt : P.δL*E.RL < E.PL := by
      rw [hPLD]; have := mul_pos hRL (show 0 < 1-D-P.δL by linarith)
      have e : E.RL*(1-D) - P.δL*E.RL = E.RL*(1-D-P.δL) := by ring
      linarith
    have hkL : max (P.δL*E.RL) E.PL = E.PL := max_eq_right hLlt.le
    have ht1 : P.δL*(E.RL/E.PL) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hPL]; exact hLlt.le
    rw [max_eq_left ht1, hkL] at hsupL
    rw [hkL] at hPiL hgapL hoL
    have hvPE_L : (1-P.lam)*E.RL + P.lam*E.PL = E.RL*(1-P.lam*D) := by rw [hPLD]; ring
    rw [hvPE_L] at hsupL
    have hU := U2 P E.RL E.PL D E.xL E.IL E.fL hRL hDH hDs hPLD hoL
    have hRmin := RLf_lt_RminH P D hDH hD1
    have hPiHlt : Pi P E.RH (fH P) < Pi P (RLf P D) (fH P) :=
      Pi_anti_r P (fH P) _ _ b.fH0 hTfH
        (by linarith [RLf_gt_one P D hD0 hD1, b.piH1, show piH P = P.p*P.R - fH P from rfl])
        (hRmin.trans_le hRHge)
    rcases eq_or_lt_of_le haL0 with haL | haL
    · exfalso
      have hvL := supply_zero_le hsupL (by rw [← haL, zero_mul]) hcapL
      have h1 := hU (by linarith)
      have h2 := hgpH hαH
      rw [hPiH] at h2
      linarith
    · have hvL := supply_pos_ge hsupL (mul_pos haL (by linarith))
      rcases eq_or_lt_of_le hvL with hv | hv
      · exfalso
        have h1 := hU (by linarith)
        have h2 := hgpH hαH
        rw [hPiH] at h2
        linarith
      · have hfull := hsupL.2.2 hv
        have hden := den_pos P D hD1
        have hRL1 : 1 < E.RL := by
          have : 0 < E.RL*(P.lam*D) := mul_pos hRL (mul_pos b.lam0 hD0)
          have e : E.RL*(1-P.lam*D) = E.RL - E.RL*(P.lam*D) := by ring
          linarith
        have hsz := size_lt P _ _ _ _ _ hoL.1 hRL1
        refine ⟨?_, fun _ => ?_⟩
        · have haL1 : E.αL ≤ 1 := by linarith
          have hNLp : 0 < E.IL - P.A := by linarith
          have : E.αL*(E.IL-P.A) ≤ E.IL - P.A := mul_le_of_le_one_left hNLp.le haL1
          have e : (1-muH)*P.K = P.K - muH*P.K := by ring
          linarith
        · have hx : xLow P.p P.q ≤ E.PL := by
            by_contra hn; push Not at hn
            have := xLow_case P E.RL E.PL D hRL hD1 hPLD (by linarith) hn
            linarith
          have hm := minCallFee_eq P _ hx
          rw [hm] at hPiL hgapL
          have heq : Pi P E.RL (fH P) = Pi P E.RH (fH P) := by
            have h1 := hgpL haL; have h2 := hgpH hαH
            rw [hPiL, hPiH] at h1 h2; linarith
          rw [hmH] at hgapH
          exact (Pi_inj P _ _ hgapL hgapH heq).symm

end PESec

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

/-- Classification of equilibria without H-funds, for μ_H K ≤ Φ(1-δ_H). -/
theorem caseL (P : Params)
    (hLcap : P.A/(1-piH P) - P.A ≤ P.K - Phi P (1-P.δH))
    (muH : ℝ) (E : AllocationSec) (hmu0 : 0 < muH)
    (hmu3 : muH * P.K ≤ Phi P (1-P.δH))
    (hE : IsEquilibriumSec P muH E) (hαH : E.αH = 0) :
    1 - P.δH ≤ discount E ∧ discount E ≤ 1 - P.δL ∧
    E.RL = RLf P (discount E) ∧ E.PL = PLf P (discount E) ∧
    E.IL - P.A = NLf P (discount E) ∧ CallOpt P (PLf P (discount E)) E.xL ∧
    (Phi P (discount E) = muH * P.K ∨
      (discount E = 1 - P.δL ∧ muH * P.K ≤ Phi P (discount E))) := by
  have b := basics P
  obtain ⟨hPL, hRL, hRH, hoL, hoH, haL0, haH0, hsum, hgpL, hgpH, hsupL, hsupH, hs1, hs2, hs3,
    hd1, hd2, hd3, hds⟩ := hE
  have hK := P.hK
  have haL : E.αL = 1 := by linarith
  have hNL : P.A < E.IL := hoL.1.2.2.2.2.1
  have hNLp : 0 < E.IL - P.A := by linarith
  rw [haL, one_mul] at hs1 hs2 hsupL
  rw [hαH, zero_mul, sub_zero] at hd1 hd2
  have hmuK : 0 < muH * P.K := mul_pos hmu0 hK
  have hPhiH : Phi P (1-P.δH) < P.K := by
    have : 0 < P.A/(1-piH P) - P.A := by
      have h1 : 0 < 1 - piH P := by linarith [b.piH1]
      have h2 : 1 - piH P < 1 := by linarith [b.piH0]
      rw [sub_pos, lt_div_iff₀ h1]; nlinarith [P.hA]
    linarith
  have hmu1 : muH < 1 := by
    by_contra hn; push Not at hn
    have : P.K ≤ muH * P.K := by nlinarith
    linarith
  -- trade bounds
  have hup : E.PL ≤ P.δH*E.RL := by
    by_contra hn; push Not at hn
    have h1 := hd3 hn
    have hLlt : P.δL*E.RL < E.PL := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right b.dLH.le hRL.le) hn
    have h2 := hs2 hLlt
    rw [← hds, h1] at h2; linarith
  have hlo : P.δL*E.RL ≤ E.PL := by
    by_contra hn; push Not at hn
    have h1 := hs3 hn
    have hlt : E.PL < P.δH*E.RL := lt_of_lt_of_le hn
      (mul_le_mul_of_nonneg_right b.dLH.le hRL.le)
    have h2 := hd1 hlt
    rw [hds, h1] at h2
    have : 0 < muH * P.K / E.PL := div_pos hmuK hPL
    linarith
  have hkL : max (P.δL*E.RL) E.PL = E.PL := max_eq_right hlo
  rw [hkL] at hoL
  rw [vCash_L_eq P _ _ _ hRH] at hsupL
  unfold vPE at hsupL
  have ht1 : P.δL*(E.RL/E.PL) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hPL]; exact hlo
  rw [max_eq_left ht1, hkL] at hsupL
  have hvL := supply_pos_ge hsupL hNLp
  have hPLlt : E.PL < E.RL := lt_of_le_of_lt hup (by nlinarith [P.hδH1])
  have hvEq : (1-P.lam)*E.RL + P.lam*E.PL = 1 := by
    rcases eq_or_lt_of_le hvL with h | h
    · linarith
    · exfalso
      have hfull := hsupL.2.2 h
      have hRL1 : 1 < E.RL := by nlinarith [b.lam0]
      have hsz := size_lt P _ _ _ _ _ hoL.1 hRL1
      have : (1-muH)*P.K < P.K - muH*P.K := by linarith
      linarith
  set D := discount E with hDdef
  have hPLD : E.PL = E.RL*(1-D) := by rw [hDdef]; unfold discount; field_simp; ring
  have hD1 : D < 1 := by
    have := div_pos hPL hRL; rw [hDdef]; unfold discount; linarith
  have hden := den_pos P D hD1
  have hRLD : E.RL = RLf P D := by
    unfold RLf; rw [eq_div_iff hden.ne']; rw [hPLD] at hvEq; linarith
  have hPLf : E.PL = PLf P D := by rw [hPLD, hRLD, RLf_PLf]
  have hDlo : 1 - P.δH ≤ D := by
    have : E.PL/E.RL ≤ P.δH := by rw [div_le_iff₀ hRL]; linarith
    rw [hDdef]; unfold discount; linarith
  have hDhi : D ≤ 1 - P.δL := by
    have : P.δL ≤ E.PL/E.RL := by rw [le_div_iff₀ hRL]; linarith
    rw [hDdef]; unfold discount; linarith
  have hRLT : E.RL < P.p*P.R := by rw [hRLD]; exact RLf_lt_pR P D hDhi
  obtain ⟨hfee, hIL⟩ := optimal_fee_size P _ _ _ _ _ hoL hRLT
  have hNLf : E.IL - P.A = NLf P D := by
    rw [hIL]; unfold NLf piL
    rw [← hPLf, ← hRLD]
    have hg := optimal_pledge_gap P _ _ _ _ _ hoL
    have : 0 < E.RL - (P.p*P.R - minCallFee P E.PL) := by linarith
    field_simp; ring
  have hcall : CallOpt P (PLf P D) E.xL := by
    rw [← hPLf]
    refine ⟨E.fL, feasible_call P _ _ _ _ _ hoL.1, ?_⟩
    intro x' f' hf'
    rw [hfee]
    exact (minimum_call P E.PL hPL.le).2.2.2 x' f' hf'
  refine ⟨hDlo, hDhi, hRLD, hPLf, hNLf, hcall, ?_⟩
  have hPhi : Phi P D = (E.IL - P.A) * E.PL := by unfold Phi; rw [hNLf, hPLf]
  rcases eq_or_lt_of_le hlo with h | h
  · -- discount 1 - δL
    right
    have hDeq : D = 1 - P.δL := by
      have : E.PL/E.RL = P.δL := by rw [← h]; field_simp
      rw [hDdef]; unfold discount; linarith
    refine ⟨hDeq, ?_⟩
    have hlt : E.PL < P.δH*E.RL := by rw [← h]; exact mul_lt_mul_of_pos_right b.dLH hRL
    have hdH := hd1 hlt
    have hsL := (hs1 h.symm).2
    rw [← hds, hdH, div_le_iff₀ hPL] at hsL
    rw [hPhi]; exact hsL
  · left
    have hsL := hs2 h
    rcases eq_or_lt_of_le hup with h2 | h2
    · obtain ⟨-, hdle⟩ := hd2 h2
      rw [hds, hsL, le_div_iff₀ hPL] at hdle
      have hDeq : D = 1 - P.δH := by
        have : E.PL/E.RL = P.δH := by rw [h2]; field_simp
        rw [hDdef]; unfold discount; linarith
      rw [hPhi]
      have : Phi P D ≤ muH * P.K := by rw [hPhi]; exact hdle
      rw [hDeq] at this
      rw [← hPhi, hDeq]; linarith
    · have hdH := hd1 h2
      rw [hds, hsL, eq_div_iff hPL.ne'] at hdH
      rw [hPhi]; exact hdH

end PESec

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

lemma supply_of_eq {a c cap S : ℝ} (h : a = c) (h0 : 0 ≤ S) (h1 : S ≤ cap) :
    IsCapitalSupply a c cap S :=
  ⟨fun hl => absurd (h ▸ hl) (lt_irrefl _), fun _ => ⟨h0, h1⟩,
    fun hl => absurd (h ▸ hl) (lt_irrefl _)⟩

lemma supply_zero_of_le {a c cap : ℝ} (h : a ≤ c) (hcap : 0 ≤ cap) :
    IsCapitalSupply a c cap 0 :=
  ⟨fun _ => rfl, fun _ => ⟨le_rfl, hcap⟩, fun hl => absurd hl (not_lt.mpr h)⟩

/-- Existence of an equilibrium without H-funds at a discount D. -/
theorem exist_L (P : Params)
    (hA7 : P.p*P.R ≤ GH P * (1 - P.lam + P.lam*P.δH/(1 - Ds P)))
    (hLcap : P.A/(1-piH P) - P.A ≤ P.K - Phi P (1-P.δH))
    (muH : ℝ) (hmu0 : 0 < muH) (hmu : muH * P.K < Phi P (1-P.δH))
    (D : ℝ) (hD0 : 1 - P.δH < D) (hD1 : D ≤ 1 - P.δL)
    (hclear : Phi P D = muH * P.K ∨ (D = 1 - P.δL ∧ muH * P.K ≤ Phi P D)) :
    ∃ E : AllocationSec, IsEquilibriumSec P muH E := by
  have b := basics P
  have hK := P.hK
  have hDlt1 : D < 1 := by linarith [P.hδL0]
  have hDpos : 0 < D := by linarith [P.hδH1]
  have hden := den_pos P D hDlt1
  have h1D : 0 < 1 - D := by linarith
  set RL := RLf P D with hRLdef
  set PL := PLf P D with hPLdef
  have hRL1 : 1 < RL := RLf_gt_one P D hDpos hDlt1
  have hRLT : RL < P.p*P.R := RLf_lt_pR P D hD1
  have hPLRL : PL = RL*(1-D) := (RLf_PLf P D).symm
  have hPL : 0 < PL := by rw [hPLRL]; exact mul_pos (by linarith) h1D
  have hlo : P.δL*RL ≤ PL := by
    rw [hPLRL]; have := mul_nonneg (by linarith : (0:ℝ) ≤ RL) (show 0 ≤ 1-D-P.δL by linarith)
    have e : RL*(1-D) - P.δL*RL = RL*(1-D-P.δL) := by ring
    linarith
  have hhi : PL < P.δH*RL := by
    rw [hPLRL]; have := mul_pos (by linarith : (0:ℝ) < RL) (show 0 < P.δH-(1-D) by linarith)
    have e : P.δH*RL - RL*(1-D) = RL*(P.δH-(1-D)) := by ring
    linarith
  have hratio : RL/PL = 1/(1-D) := by rw [hPLRL]; field_simp
  -- L contract
  obtain ⟨xL, IL, fL, hoL, hfeeL, hIL⟩ := general_contract P RL PL hRL1.le hRLT.le hPL.le
  have hgapL := optimal_pledge_gap P _ _ _ _ _ hoL
  have hNL : IL - P.A = NLf P D := by
    rw [hIL]; unfold NLf piL
    rw [← hPLdef, ← hRLdef]
    have : 0 < RL - (P.p*P.R - minCallFee P PL) := by linarith
    field_simp; ring
  have hNLpos : 0 < IL - P.A := by linarith [hoL.1.2.2.2.2.1]
  have hPhiD : Phi P D = (IL - P.A) * PL := by unfold Phi; rw [hNL]
  -- H contract
  set VH := 1 - P.lam + P.lam*P.δH/(1-D) with hVHdef
  have hVH1 : 1 ≤ P.δH/(1-D) := by rw [le_div_iff₀ h1D]; linarith
  have hVHge : 1 ≤ VH := by
    have : P.lam ≤ P.lam*P.δH/(1-D) := by rw [mul_div_assoc]; exact le_mul_of_one_le_right b.lam0.le hVH1
    rw [hVHdef]; linarith
  have hGVH : 1 ≤ GH P * VH := one_le_mul_of_one_le_of_one_le b.G1.le hVHge
  set RH := min (GH P * VH) (P.p*P.R) with hRHdef
  have hRH1 : 1 ≤ RH := le_min hGVH b.pR1.le
  have hRHT : RH ≤ P.p*P.R := min_le_right _ _
  have hRHG : GH P ≤ RH := by
    apply le_min _ b.GpR.le
    exact le_mul_of_one_le_right (by linarith [b.G1]) hVHge
  obtain ⟨xH, IH, fH', hoH, -, -⟩ := general_contract P RH (P.δH*RH) hRH1 hRHT
    (mul_nonneg P.hδH0.le (by linarith))
  have hPiL := profit_eq P _ _ _ _ _ hoL
  have hPiH := profit_eq P _ _ _ _ _ hoH
  rw [minCallFee_dH P _ hRHG] at hPiH
  have hkL : max (P.δL*RL) PL = PL := max_eq_right hlo
  have hTfH : fH P < P.p*P.R := by linarith [b.piH0, show piH P = P.p*P.R - fH P from rfl]
  -- GP comparison
  have hGP : gpProfit P IL fL ≥ gpProfit P IH fH' := by
    rw [hPiL, hPiH]
    rcases min_cases (GH P * VH) (P.p*P.R) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- RH = G VH ≤ pR
      have hDs : D ≤ Ds P := by
        by_contra hn; push Not at hn
        have := A7_gt P hA7 D hn hDlt1
        linarith
      rw [minCallFee_PLf_le P D hDlt1 hDs]
      have hlt : RL < RH := by rw [hRHdef, h1]; exact RLf_lt_RminH P D hD0 hDlt1
      exact (Pi_anti_r P (fH P) _ _ b.fH0 hTfH (by linarith [b.piH1, show piH P = P.p*P.R - fH P from rfl]) hlt).le
    · rw [hRHdef, h1, Pi_pR P _ b.fH0]
      have hm0 : 0 < minCallFee P PL := lt_of_lt_of_le b.fH0 (minCallFee_ge P PL)
      exact (Pi_gt_pRA P _ _ hm0 (minCallFee_lt P PL hPL.le) hgapL hRLT).le
  -- values
  have hvPEL : vPE P.lam P.δL RL PL = 1 := by
    unfold vPE; rw [hkL, hPLRL]
    unfold RL RLf; field_simp; ring
  have hvCL : vCash P.lam P.δL RL RH PL (P.δH*RH) = 1 := by
    rw [vCash_L_eq P _ _ _ (by linarith)]
    have : P.δL*(RL/PL) ≤ 1 := by rw [mul_div_assoc', div_le_one hPL]; exact hlo
    rw [max_eq_left this]; ring
  have hvCH : vCash P.lam P.δH RL RH PL (P.δH*RH) = VH := by
    rw [vCash_H_eq P _ _ _ (by linarith), hratio, mul_one_div, max_eq_right hVH1]
    rw [hVHdef]; ring
  have hvPEH : vPE P.lam P.δH RH (P.δH*RH) ≤ VH := by
    rw [vPE_self]
    have h1 : RH ≤ GH P * VH := min_le_left _ _
    have ha := aH_pos P
    calc (1 - P.lam + P.lam*P.δH)*RH ≤ (1 - P.lam + P.lam*P.δH)*(GH P * VH) :=
          mul_le_mul_of_nonneg_left h1 ha.le
      _ = VH := by rw [← mul_assoc, mul_comm (1 - P.lam + P.lam*P.δH), b.Gdef, one_mul]
  have hsz := size_lt P _ _ _ _ _ hoL.1 hRL1
  have hcapL : IL - P.A ≤ (1-muH)*P.K := by
    have e : (1-muH)*P.K = P.K - muH*P.K := by ring
    linarith
  have hsLle : muH*P.K/PL ≤ IL - P.A := by
    rw [div_le_iff₀ hPL, ← hPhiD]
    rcases hclear with h | h
    · rw [h]
    · exact h.2
  refine ⟨⟨1, 0, RL, RH, PL, xL, xH, IL, IH, muH*P.K/PL, muH*P.K/PL, fL, fH'⟩, ?_⟩
  refine ⟨hPL, by linarith, by linarith, ?_, hoH, zero_le_one, le_rfl, by norm_num,
    fun _ => hGP, fun h => absurd h (lt_irrefl _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only; rw [hkL]; exact hoL
  · simp only; rw [hvPEL, hvCL, one_mul]
    exact supply_of_eq rfl hNLpos.le hcapL
  · simp only; rw [hvCH, zero_mul]
    exact supply_zero_of_le hvPEH (mul_pos hmu0 hK).le
  · intro _; simp only; rw [one_mul]
    exact ⟨div_nonneg (mul_pos hmu0 hK).le hPL.le, hsLle⟩
  · intro h; simp only at h ⊢; rw [one_mul]
    rcases hclear with h' | h'
    · rw [div_eq_iff hPL.ne', ← hPhiD, h']
    · exfalso
      have : PL = P.δL*RL := by rw [hPLRL, h'.1]; ring
      linarith
  · intro h; simp only at h; exfalso; linarith
  · intro _; simp only; rw [zero_mul, sub_zero]
  · intro h; simp only at h; exfalso; linarith
  · intro h; simp only at h; exfalso; linarith

end PESec

set_option autoImplicit false
set_option maxHeartbeats 3200000
open PELiquidity.Primary PELiquidity.Secondary

namespace PESec
open PEResearch

/-- Existence when H-LP capital is abundant: discount 1 - δ_H, both funds at 1 + r(λ, δ_H). -/
theorem exist_H (P : Params)
    (hLcap : P.A/(1-piH P) - P.A ≤ P.K - Phi P (1-P.δH))
    (muH : ℝ) (hmu0 : 0 < muH) (hmu1 : muH < 1) (hmu : Phi P (1-P.δH) ≤ muH * P.K) :
    ∃ E : AllocationSec, IsEquilibriumSec P muH E := by
  have b := basics P
  have hK := P.hK
  set G := GH P with hGdef
  have hG1 : 1 < G := b.G1
  have hGT : G < P.p*P.R := b.GpR
  obtain ⟨x, I, f, ho, hfee, hI⟩ := general_contract P G (P.δH*G) hG1.le hGT.le
    (mul_nonneg P.hδH0.le (by linarith))
  have hm := minCallFee_dH P G le_rfl
  have hN : I - P.A = N0 P := by
    rw [hI, hm]; unfold N0 piH; rw [← hGdef]
    have : 0 < G - (P.p*P.R - fH P) := by linarith [b.piH1, show piH P = P.p*P.R - fH P from rfl]
    field_simp; ring
  have hNpos : 0 < N0 P := by rw [← hN]; linarith [ho.1.2.2.2.2.1]
  have hsz := size_lt P _ _ _ _ _ ho.1 hG1
  rw [hN] at hsz
  have hPhi := Phi_dH P
  have hNK : N0 P + Phi P (1-P.δH) < P.K := by linarith
  have hPhi0 : 0 < Phi P (1-P.δH) := by rw [hPhi]; exact mul_pos hNpos (mul_pos P.hδH0 (by linarith))
  set SL := min (N0 P) ((1-muH)*P.K) with hSLdef
  have hcap : 0 < (1-muH)*P.K := mul_pos (by linarith) hK
  have hSL0 : 0 < SL := lt_min hNpos hcap
  have hSLN : SL ≤ N0 P := min_le_left _ _
  have hSLc : SL ≤ (1-muH)*P.K := min_le_right _ _
  set aL := SL / N0 P with haLdef
  have haL0 : 0 ≤ aL := div_nonneg hSL0.le hNpos.le
  have haL1 : aL ≤ 1 := (div_le_one hNpos).2 hSLN
  have haLN : aL * N0 P = SL := by rw [haLdef]; field_simp
  have hPL : 0 < P.δH * G := mul_pos P.hδH0 (by linarith)
  have hkL : max (P.δL*G) (P.δH*G) = P.δH*G :=
    max_eq_right (mul_le_mul_of_nonneg_right b.dLH.le (by linarith))
  have hLlt : P.δL*G < P.δH*G := mul_lt_mul_of_pos_right b.dLH (by linarith)
  have hv : (1 - P.lam + P.lam*P.δH)*G = 1 := by rw [mul_comm]; exact b.Gdef
  have hratio : G/(P.δH*G) = 1/P.δH := by field_simp
  -- key secondary-market inequality
  have hkey : SL*(P.δH*G) ≤ muH*P.K - (1-aL)*N0 P := by
    have e : (1-aL)*N0 P = N0 P - SL := by rw [sub_mul, one_mul, haLN]
    rw [e]
    have hdHG := b.dHG
    rcases min_cases (N0 P) ((1-muH)*P.K) with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rw [hSLdef, h1]; rw [hPhi] at hmu; linarith
    · rw [hSLdef, h1]
      have : (1-muH)*P.K*(P.δH*G) ≤ N0 P*(P.δH*G) := mul_le_mul_of_nonneg_right h2.le hPL.le
      rw [hPhi] at hNK
      have e : (1-muH)*P.K = P.K - muH*P.K := by ring
      linarith
  refine ⟨⟨aL, 1-aL, G, G, P.δH*G, x, x, I, I, SL, SL, f, f⟩, ?_⟩
  refine ⟨hPL, by linarith, by linarith, ?_, ho, haL0, by linarith, by ring,
    fun _ => le_rfl, fun _ => le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only; rw [hkL]; exact ho
  · simp only
    have h1 : vPE P.lam P.δL G (P.δH*G) = 1 := by unfold vPE; rw [hkL]; linarith
    have h2 : vCash P.lam P.δL G G (P.δH*G) (P.δH*G) = 1 := by
      rw [vCash_L_eq P _ _ _ (by linarith), hratio]
      have : P.δL*(1/P.δH) ≤ 1 := by
        rw [mul_one_div, div_le_one P.hδH0]; exact b.dLH.le
      rw [max_eq_left this]; ring
    rw [h1, h2, hN, haLN]
    exact supply_of_eq rfl hSL0.le hSLc
  · simp only
    have h1 : vPE P.lam P.δH G (P.δH*G) = 1 := by rw [vPE_self]; exact hv
    have h2 : vCash P.lam P.δH G G (P.δH*G) (P.δH*G) = 1 := by
      rw [vCash_H_eq P _ _ _ (by linarith), hratio, mul_one_div_cancel P.hδH0.ne', max_self]; ring
    rw [h1, h2, hN]
    apply supply_of_eq rfl
    · exact mul_nonneg (by linarith) hNpos.le
    · have e : (1-aL)*N0 P = N0 P - SL := by rw [sub_mul, one_mul, haLN]
      rw [e]
      rcases min_cases (N0 P) ((1-muH)*P.K) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [hSLdef, h1, sub_self]; exact (mul_pos hmu0 hK).le
      · rw [hSLdef, h1]
        have e : (1-muH)*P.K = P.K - muH*P.K := by ring
        linarith
  · intro h; simp only at h; exfalso; linarith
  · intro _; simp only; rw [hN, haLN]
  · intro h; simp only at h; exfalso; linarith
  · intro h; simp only at h; exfalso; linarith
  · intro _; simp only
    refine ⟨hSL0.le, ?_⟩
    rw [le_div_iff₀ hPL, hN]; exact hkey
  · intro h; simp only at h; exfalso; linarith

end PESec

open PESec PEResearch in
open PELiquidity.Secondary in
theorem solution (P : PELiquidity.Primary.Params)
    (hA7 : P.p * P.R ≤ PELiquidity.Primary.grossReturn P.lam P.δH *
      (1 - P.lam + P.lam * P.δH *
        (P.p + (1 - P.lam) * P.q) / ((1 - P.lam) * P.q)))
    (hLcap : P.A / (1 - (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) - P.A ≤
      P.K - P.δH * PELiquidity.Primary.grossReturn P.lam P.δH *
        ((P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)) * P.A /
          (PELiquidity.Primary.grossReturn P.lam P.δH -
            (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))))) :
    let muBar := (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)) * P.A /
      ((PELiquidity.Primary.grossReturn P.lam P.δH -
        (P.p * P.R - P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) * P.K)
    ∃ mu₁ mu₂ mu₃ : ℝ,
      0 < mu₁ ∧ mu₁ < mu₂ ∧ mu₂ < mu₃ ∧ mu₃ < muBar ∧
      (∀ muH : ℝ, 0 < muH → muH < 1 →
        ∃ E : AllocationSec, IsEquilibriumSec P muH E) ∧
      (∀ (muH : ℝ) (E : AllocationSec),
        0 < muH → muH < 1 → IsEquilibriumSec P muH E → 0 < E.αH →
          mu₃ ≤ muH ∧ (0 < E.αL → E.RH = E.RL)) ∧
      (∀ (muH : ℝ) (E : AllocationSec),
        0 < muH → muH ≤ mu₃ → IsEquilibriumSec P muH E →
          E.αH = 0 ∧
          E.RL = 1 / (1 - P.lam * discount E) ∧
          (muH ≤ mu₁ → discount E = 1 - P.δL ∧
            E.xL = PELiquidity.Primary.xHat P.lam P.δL) ∧
          (mu₁ ≤ muH →
            discount E = (E.IL - P.A - muH * P.K) /
              (E.IL - P.A - P.lam * muH * P.K)) ∧
          (mu₁ ≤ muH → muH ≤ mu₂ →
            E.xL = (1 - P.lam) * discount E / (1 - P.lam * discount E)) ∧
          (mu₂ ≤ muH →
            max (PELiquidity.Primary.xLow P.p P.q)
              ((1 - P.lam) * discount E / (1 - P.lam * discount E)) ≤ E.xL ∧
            E.xL ≤ PELiquidity.Primary.xBar P.p P.q) ∧
          (muH = mu₃ → discount E = 1 - P.δH)) := by
  intro muBar
  have b := basics P
  have hK := P.hK
  have A7 := A7_conv P hA7
  have Lc := Lcap_conv P hLcap
  have hDs := Ds_facts P
  have hdL0 := P.hδL0
  have hdH1 := P.hδH1
  have hdLH := b.dLH
  -- the three levels of Φ
  set p1 := Phi P (1-P.δL) with hp1
  set p2 := Phi P (Ds P) with hp2
  set p3 := Phi P (1-P.δH) with hp3
  have hp12 : p1 < p2 := Phi_strictAnti P _ _ (by linarith) hDs.2 (by linarith)
  have hp23 : p2 < p3 := Phi_strictAnti P _ _ (by linarith) hDs.1 (by linarith)
  have hp1pos : 0 < p1 := Phi_pos P _ (by linarith) (by linarith)
  have hN0 : p3 = N0 P * (P.δH * GH P) := Phi_dH P
  have hmuBar : muBar = N0 P / P.K := by
    show _ = N0 P / P.K
    unfold N0 piH fH GH; rw [div_div]
  have hN0pos : 0 < N0 P := by
    have h0 : 0 < p3 := lt_trans hp1pos (hp12.trans hp23)
    rw [hN0] at h0
    exact pos_of_mul_pos_left h0 (mul_pos P.hδH0 (by linarith [b.G1])).le
  have hp3N : p3 < N0 P := by
    rw [hN0]; exact mul_lt_of_lt_one_right hN0pos b.dHG
  have hp3K : p3 < P.K := by
    have : 0 < P.A/(1-piH P) - P.A := by
      have h1 : 0 < 1 - piH P := by linarith [b.piH1]
      have h2 : 1 - piH P < 1 := by linarith [b.piH0]
      rw [sub_pos, lt_div_iff₀ h1]
      have := mul_pos P.hA b.piH0
      have e : P.A*(1-piH P) = P.A - P.A*piH P := by ring
      linarith
    linarith
  refine ⟨p1/P.K, p2/P.K, p3/P.K, div_pos hp1pos hK, div_lt_div_of_pos_right hp12 hK,
    div_lt_div_of_pos_right hp23 hK, ?_, ?_, ?_, ?_⟩
  · rw [hmuBar]; exact div_lt_div_of_pos_right hp3N hK
  · -- existence
    intro muH hmu0 hmu1
    rcases le_or_gt p3 (muH*P.K) with h | h
    · exact exist_H P Lc muH hmu0 hmu1 h
    · rcases le_or_gt (muH*P.K) p1 with h' | h'
      · exact exist_L P A7 Lc muH hmu0 h (1-P.δL) (by linarith) le_rfl (Or.inr ⟨rfl, h'⟩)
      · have hsub := intermediate_value_Icc' (show 1-P.δH ≤ 1-P.δL by linarith) (Phi_cont P)
        obtain ⟨D, hD, hPhiD⟩ := hsub ⟨h'.le, h.le⟩
        have hD0 : 1 - P.δH < D := by
          rcases eq_or_lt_of_le hD.1 with e | e
          · rw [← e] at hPhiD; linarith
          · exact e
        exact exist_L P A7 Lc muH hmu0 h D hD0 hD.2 (Or.inl hPhiD)
  · intro muH E hmu0 hmu1 hE hαH
    obtain ⟨h1, h2⟩ := caseH P A7 Lc muH E hmu0 hmu1 hE hαH
    exact ⟨((div_le_iff₀ hK).2 h1.le), h2⟩
  · intro muH E hmu0 hmu3 hE
    have hmu3' : muH * P.K ≤ p3 := (le_div_iff₀ hK).1 hmu3
    have hmu1 : muH < 1 := by
      have : muH * P.K < 1 * P.K := by rw [one_mul]; exact lt_of_le_of_lt hmu3' hp3K
      exact lt_of_mul_lt_mul_right this hK.le
    have hαH : E.αH = 0 := by
      have h0 := hE.2.2.2.2.2.2.1
      rcases eq_or_lt_of_le h0 with e | e
      · exact e.symm
      · have := (caseH P A7 Lc muH E hmu0 hmu1 hE e).1
        linarith
    obtain ⟨hDlo, hDhi, hRL, hPLe, hNL, hcall, hclr⟩ := caseL P Lc muH E hmu0 hmu3' hE hαH
    set D := discount E with hDdef
    have hD0 : 0 < D := by linarith
    have hD1 : D < 1 := by linarith
    have hden := den_pos P D hD1
    -- clearing gives Φ(D) = μ_H K once μ_H ≥ μ_1
    have hclr1 : p1 ≤ muH * P.K → Phi P D = muH * P.K := by
      intro hp
      rcases hclr with e | ⟨e1, e2⟩
      · exact e
      · rw [e1] at e2 ⊢; linarith
    have hk0 : 0 ≤ 1 - PLf P D := by rw [one_sub_PLf P D hD1]; unfold gf; exact div_nonneg (mul_nonneg (by linarith [b.lam1]) hD0.le) hden.le
    have hk1 : 1 - PLf P D ≤ 1 := by linarith [PLf_nonneg P D hD1]
    refine ⟨hαH, hRL, ?_, ?_, ?_, ?_, ?_⟩
    · intro hmu
      have hmu' : muH * P.K ≤ p1 := (le_div_iff₀ hK).1 hmu
      have hDeq : D = 1 - P.δL := by
        rcases hclr with e | ⟨e1, -⟩
        · rcases eq_or_lt_of_le hDhi with e' | e'
          · exact e'
          · have := Phi_strictAnti P _ _ hD0 e' (by linarith); linarith
        · exact e1
      refine ⟨hDeq, ?_⟩
      have hgt : xBar P.p P.q < 1 - PLf P D := by
        rw [one_sub_PLf P D hD1]
        by_contra hn; push Not at hn
        have := (gf_le_iff P D hD1).1 hn
        linarith
      have := (call_low P (PLf P D) hk0 hk1 hgt).1
      have hx : E.xL ∈ {x | CallOpt P (PLf P D) x} := hcall
      rw [this] at hx
      rw [Set.mem_singleton_iff.mp hx, one_sub_PLf P D hD1, hDeq, gf_one_sub P P.δL P.hδL0 P.hδL1]
    · intro hmu
      have hmu' : p1 ≤ muH * P.K := (div_le_iff₀ hK).1 hmu
      have hPhi := hclr1 hmu'
      unfold Phi at hPhi
      rw [← hNL, ← hPLe] at hPhi
      have hPL1 : E.PL < 1 := by
        rw [hPLe]; unfold PLf; rw [div_lt_one hden]
        have := mul_lt_mul_of_pos_right b.lam1 hD0
        linarith
      have hNLp : 0 < E.IL - P.A := by linarith [hE.2.2.2.1.1.2.2.2.2.1]
      have hdenpos : 0 < E.IL - P.A - P.lam * muH * P.K := by
        rw [mul_assoc, ← hPhi]
        have h1 : P.lam*E.PL < 1 := mul_lt_one_of_nonneg_of_lt_one_left b.lam0.le b.lam1 hPL1.le
        have := mul_pos hNLp (show 0 < 1 - P.lam*E.PL by linarith)
        have e : (E.IL - P.A)*(1 - P.lam*E.PL) = E.IL - P.A - P.lam*((E.IL - P.A)*E.PL) := by ring
        linarith
      rw [eq_div_iff hdenpos.ne']
      rw [hPLe] at hPhi; unfold PLf at hPhi
      rw [mul_div_assoc', div_eq_iff hden.ne'] at hPhi
      linear_combination (-1:ℝ)*hPhi
    · intro hmu1' hmu2
      have hmu' : p1 ≤ muH * P.K := (div_le_iff₀ hK).1 hmu1'
      have hmu2' : muH * P.K ≤ p2 := (le_div_iff₀ hK).1 hmu2
      have hPhi := hclr1 hmu'
      have hDs' : Ds P ≤ D := by
        by_contra hn; push Not at hn
        have := Phi_strictAnti P _ _ hD0 hn (by linarith); linarith
      have hge : xBar P.p P.q ≤ gf P D := by
        rcases eq_or_lt_of_le hDs' with e | e
        · rw [← e, gf_Ds]
        · by_contra hn; push Not at hn
          have := (gf_lt_iff P D hD1).1 hn; linarith
      have hx : E.xL ∈ {x | CallOpt P (PLf P D) x} := hcall
      show E.xL = gf P D
      rcases eq_or_lt_of_le hge with e | e
      · have hk : 1 - PLf P D ≤ xBar P.p P.q := by rw [one_sub_PLf P D hD1]; exact e.ge
        rw [(call_high P (PLf P D) hk0 hk1 hk).1] at hx
        rw [one_sub_PLf P D hD1, ← e, max_eq_right b.xLB.le] at hx
        rw [← e]; exact le_antisymm hx.2 hx.1
      · have hk : xBar P.p P.q < 1 - PLf P D := by rw [one_sub_PLf P D hD1]; exact e
        rw [(call_low P (PLf P D) hk0 hk1 hk).1] at hx
        rw [Set.mem_singleton_iff.mp hx, one_sub_PLf P D hD1]
    · intro hmu2
      have hmu2' : p2 ≤ muH * P.K := (div_le_iff₀ hK).1 hmu2
      have hPhi := hclr1 (hp12.le.trans hmu2')
      have hDs' : D ≤ Ds P := by
        by_contra hn; push Not at hn
        have := Phi_strictAnti P _ _ (by linarith) hn hD1; linarith
      have hk : 1 - PLf P D ≤ xBar P.p P.q := by
        rw [one_sub_PLf P D hD1]; exact (gf_le_iff P D hD1).2 hDs'
      have hx : E.xL ∈ {x | CallOpt P (PLf P D) x} := hcall
      rw [(call_high P (PLf P D) hk0 hk1 hk).1, one_sub_PLf P D hD1] at hx
      exact hx
    · intro hmu
      have hmu' : muH * P.K = p3 := by rw [hmu]; field_simp
      have hPhi := hclr1 (by rw [hmu']; exact (hp12.trans hp23).le)
      rcases eq_or_lt_of_le hDlo with e | e
      · exact e.symm
      · have := Phi_strictAnti P _ _ (by linarith) e hD1; linarith
