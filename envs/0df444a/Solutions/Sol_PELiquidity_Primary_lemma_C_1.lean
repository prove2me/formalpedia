-- Prove2me | solution 1 for PELiquidity.Primary.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T09:45:28.416767+00:00
-- url     : https://prove2.me/submissions/bd238f5e-c5cd-4b6c-9090-283ca6265140

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
lemma supply_value (P : Params) (d r : ℝ) :
    (1-P.lam)*r+P.lam*(d*r)=(1-P.lam*(1-d))*r := by ring
lemma supply_active (P : Params) (d cap a I r : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (ha : 0 < a) (hI : P.A < I)
    (h : IsCapitalSupply ((1-P.lam)*r+P.lam*(d*r)) 1 cap (a*(I-P.A))) :
    grossReturn P.lam d ≤ r := by
  have hd := (PEFinance.gross_pos P.lam d P.hlam0 P.hlam1 hd0 hd1).1
  have hp := mul_pos ha (sub_pos.mpr hI)
  have hv : 1 ≤ (1-P.lam)*r+P.lam*(d*r) := by
    by_contra hn
    have hz := h.1 (lt_of_not_ge hn)
    linarith
  rw [supply_value] at hv
  exact (div_le_iff₀ hd).mpr (by nlinarith)
lemma supply_full (P : Params) (d cap a I r : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (hr : grossReturn P.lam d < r)
    (h : IsCapitalSupply ((1-P.lam)*r+P.lam*(d*r)) 1 cap (a*(I-P.A))) :
    a*(I-P.A)=cap := by
  have hd := (PEFinance.gross_pos P.lam d P.hlam0 P.hlam1 hd0 hd1).1
  have hv := (div_lt_iff₀ hd).mp hr
  apply h.2.2
  rw [supply_value]
  nlinarith
lemma low_break_even (P : Params) (muH : ℝ) (E : Allocation)
    (hE : IsEquilibrium P muH E) (hαL : 0 < E.αL) :
    E.RL = grossReturn P.lam P.δL := by
  rcases hE with ⟨hl,hh,haL,haH,hsum,hactL,hactH,hcapL,hcapH⟩
  have hL := gross_gt_one P P.δL P.hδL0 P.hδL1
  have hH := gross_gt_one P P.δH P.hδH0 P.hδH1
  have hrl := supply_active P P.δL ((1-muH)*P.K) E.αL E.IL E.RL P.hδL0 P.hδL1
    hαL hl.1.2.2.2.2.1 hcapL
  apply le_antisymm ?_ hrl
  by_contra hn
  have hrL := lt_of_not_ge hn
  obtain ⟨xl,Il,fl,xh,Ih,fh,bl,bh,hgap⟩ := baseline_gap P
  have hLless := optimal_profit_strict_decreasing P P.δL (grossReturn P.lam P.δL) E.RL
    xl Il E.xL E.IL P.hδL0 hrL (hL.trans hrL) fl E.fL bl hl
  have hrH : grossReturn P.lam P.δH < E.RH := by
    by_contra hnH
    have hge := optimal_profit_antitone P P.δH E.RH (grossReturn P.lam P.δH)
      E.xH E.IH xh Ih P.hδH0 (le_of_not_gt hnH) hH E.fH fh hh bh
    have hact := hactL hαL
    linarith
  have hfullL := supply_full P P.δL ((1-muH)*P.K) E.αL E.IL E.RL P.hδL0 P.hδL1 hrL hcapL
  have hfullH := supply_full P P.δH (muH*P.K) E.αH E.IH E.RH P.hδH0 P.hδH1 hrH hcapH
  have hboundL := contract_size_lt_cap P E.RL (P.δL*E.RL) E.xL E.IL E.fL hl.1 (hL.trans hrL)
  have hboundH := contract_size_lt_cap P E.RH (P.δH*E.RH) E.xH E.IH E.fH hh.1 (hH.trans hrH)
  have hprodL := mul_pos hαL (sub_pos.mpr hboundL)
  have hprodH := mul_nonneg haH (sub_nonneg.mpr hboundH.le)
  have hsumK := congrArg (fun z : ℝ => z*P.K) hsum
  nlinarith
end PEResearch


/-- Lemma C.1: in an equilibrium without a secondary market, if L-funds are raised
(`α*_L > 0`) then L-LPs earn exactly their break-even return `1 + r(λ, δ_L)`. -/
theorem solution (P : Params) (muH : ℝ) (hmu0 : 0 < muH) (hmu1 : muH < 1) (E : Allocation)
    (hE : IsEquilibrium P muH E) (hαL : 0 < E.αL) :
    E.RL = grossReturn P.lam P.δL := by
  exact PEResearch.low_break_even P muH E hE hαL


