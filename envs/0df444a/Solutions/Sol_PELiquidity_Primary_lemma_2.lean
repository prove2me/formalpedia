-- Prove2me | solution 1 for PELiquidity.Primary.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:24:32.037894+00:00
-- url     : https://prove2.me/submissions/f05c063e-ee53-4431-9b66-83e6127555cc

-- Research directed by Alexander Richard Towell (queelius); Lean proof by OpenAI Codex.
-- Mathematical source: Vincent Maurin, David T. Robinson and Per Strömberg, December 2020.
-- Platform definitions and formulation: mikedeng1; statement review: Shuze Chen.
-- Formal foundations: Lean and Mathlib contributors.
import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting
import Definitions.Def_PELiquidity_Primary_Market
set_option autoImplicit false
set_option maxHeartbeats 1600000
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


/-- Lemma 2: the minimal expected fee over limited-liability, incentive-compatible fee
schedules, for a first call `x ∈ [0, 1]`, is (15); and the call fractions `x` that are
part of an unconstrained fee-minimizing pair `(x, f)` are exactly `[q/(p+q), p/(p+q)]`. -/
theorem solution (p q B R : ℝ) (hq : 0 < q) (hqp : q < p) (hp1 : p ≤ 1) (hB : 0 < B)
    (hLL : B ≤ p * (p - q) * R) :
    (∀ x : ℝ, 0 ≤ x → x ≤ xLow p q →
      IsLeast {v | ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
          v = expectedFee p p f}
        (p * B / (p - q) * (1 - x))) ∧
    (∀ x : ℝ, xLow p q ≤ x → x ≤ xBar p q →
      IsLeast {v | ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
          v = expectedFee p p f}
        (p ^ 2 * B / (p ^ 2 - q ^ 2))) ∧
    (∀ x : ℝ, xBar p q ≤ x → x ≤ 1 →
      IsLeast {v | ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
          v = expectedFee p p f}
        (p * B / (p - q) * x)) ∧
    (∀ x : ℝ, (0 ≤ x ∧ x ≤ 1 ∧ ∃ f : Outcome → ℝ, IsLimitedLiability R x f ∧ IsIC p q B x f ∧
        ∀ (x' : ℝ) (f' : Outcome → ℝ), 0 ≤ x' → x' ≤ 1 → IsLimitedLiability R x' f' →
          IsIC p q B x' f' → expectedFee p p f ≤ expectedFee p p f') ↔
      x ∈ Set.Icc (xLow p q) (xBar p q)) := by
  exact PEResearch.fee_schedule p q B R hq hqp hp1 hB hLL


