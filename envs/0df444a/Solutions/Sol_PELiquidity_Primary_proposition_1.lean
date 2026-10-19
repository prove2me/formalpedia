-- Prove2me | solution 1 for PELiquidity.Primary.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:26:41.224631+00:00
-- url     : https://prove2.me/submissions/72a8dfdf-3bdd-47a0-85bc-327644cdbeef

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


/-- Proposition 1 with (16)–(17): under the no-default constraint (5b),
`1 - x ≤ δ (1 + r(λ, δ))`, the optimal first calls are `[max {x̲, x̂(λ, δ)}, x̄]` when
`δ ≥ δ̂(λ)` and `x̂(λ, δ)` alone when `δ < δ̂(λ)`; the minimal expected fee is (15) at
the optimal call, and for `δ < δ̂(λ)` every feasible fee strictly exceeds the undistorted
`p²B/(p² - q²)`. -/
theorem solution (P : Params) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let c := δ * grossReturn P.lam δ
    let IsFeasibleCall : ℝ → (Outcome → ℝ) → Prop := fun x f =>
      0 ≤ x ∧ x ≤ 1 ∧ 1 - x ≤ c ∧ IsLimitedLiability P.R x f ∧ IsIC P.p P.q P.B x f
    let IsOptimalCall : ℝ → Prop := fun x =>
      ∃ f : Outcome → ℝ, IsFeasibleCall x f ∧
        ∀ (x' : ℝ) (f' : Outcome → ℝ), IsFeasibleCall x' f' →
          expectedFee P.p P.p f ≤ expectedFee P.p P.p f'
    (deltaHat P.p P.q P.lam ≤ δ →
      {x | IsOptimalCall x} = Set.Icc (max (xLow P.p P.q) (xHat P.lam δ)) (xBar P.p P.q) ∧
      IsLeast {v | ∃ x f, IsFeasibleCall x f ∧ v = expectedFee P.p P.p f}
        (P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) ∧
    (δ < deltaHat P.p P.q P.lam →
      {x | IsOptimalCall x} = {xHat P.lam δ} ∧
      IsLeast {v | ∃ x f, IsFeasibleCall x f ∧ v = expectedFee P.p P.p f}
        (P.p * P.B / (P.p - P.q) * xHat P.lam δ) ∧
      ∀ (x : ℝ) (f : Outcome → ℝ), IsFeasibleCall x f →
        P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2) < expectedFee P.p P.p f) := by
  exact PEResearch.call_theorem P δ hδ0 hδ1


