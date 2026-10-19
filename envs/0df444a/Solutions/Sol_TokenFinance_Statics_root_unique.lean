-- Prove2me | solution 1 for TokenFinance.Statics.root_unique
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T11:07:51.795842+00:00
-- url     : https://prove2.me/submissions/8df13cb1-3fdf-493d-85b7-88be9f94f156

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace TokenResearch
open TokenFinance.Debt
 def G (c θ t : ℝ) : ℝ := c/(c+t)*(2/(3*θ))*((θ-c)/2-t)^3-(θ-c)^3/(12*θ)
 def Dt (c θ t : ℝ) : ℝ := -(c/(c+t)^2)*(2/(3*θ))*((θ-c)/2-t)^3-2*c/((c+t)*θ)*((θ-c)/2-t)^2
 def Dc (c θ t : ℝ) : ℝ := 2*t/3*((θ-c)/2-t)^3/((c+t)^2*θ)+((θ-c)^2/(4*θ)-c*((θ-c)/2-t)^2/((c+t)*θ))
 def Dh (c θ t : ℝ) : ℝ := c/3*((θ-c)/2-t)^2*(2*θ+c+2*t)/((c+t)*θ^2)-(θ-c)^2*(2*θ+c)/(12*θ^2)
lemma deriv_t (c θ t : ℝ) (hct : c+t≠0) : HasDerivAt (G c θ) (Dt c θ t) t := by
  have h := ((((hasDerivAt_const t c).div ((hasDerivAt_id t).const_add c) hct).mul_const (2/(3*θ))).mul
    (((hasDerivAt_const t ((θ-c)/2)).sub (hasDerivAt_id t)).pow 3)).sub_const ((θ-c)^3/(12*θ))
  convert h using 1 <;> (try rfl) <;> (try dsimp [G,Dt]) <;> (try field_simp) <;> ring
lemma deriv_c (c θ t : ℝ) (hct : c+t≠0) : HasDerivAt (fun d => G d θ t) (Dc c θ t) c := by
  have h := ((((hasDerivAt_id c).div ((hasDerivAt_id c).add_const t) hct).mul_const (2/(3*θ))).mul
    ((((hasDerivAt_const c θ).sub (hasDerivAt_id c)).div_const 2).sub_const t |>.pow 3)).sub
      ((((hasDerivAt_const c θ).sub (hasDerivAt_id c)).pow 3).div_const (12*θ))
  convert h using 1 <;> (try rfl) <;> (try dsimp [G,Dc]) <;> (try field_simp) <;> ring
lemma deriv_h (c θ t : ℝ) (hθ : θ≠0) : HasDerivAt (fun T => G c T t) (Dh c θ t) θ := by
  have h := (((hasDerivAt_const θ (c/(c+t))).mul
      ((hasDerivAt_const θ 2).div ((hasDerivAt_id θ).const_mul 3) (by positivity : 3*θ≠0))).mul
      ((((hasDerivAt_id θ).sub_const c).div_const 2).sub_const t |>.pow 3)).sub
      ((((hasDerivAt_id θ).sub_const c).pow 3).div ((hasDerivAt_id θ).const_mul 12) (by positivity : 12*θ≠0))
  convert h using 1 <;> (try rfl) <;> (try dsimp [G,Dh]) <;> (try field_simp) <;> ring
lemma dt_neg (c θ t : ℝ) (hc : 0<c) (hθ : 0<θ) (ht : 0≤t) (hregion : t<(θ-c)/2) : Dt c θ t<0 := by
  have hct : 0<c+t := by linarith
  have hgap : 0<(θ-c)/2-t := by linarith
  have h1 : 0<c/(c+t)^2*(2/(3*θ))*((θ-c)/2-t)^3 := by positivity
  have h2 : 0<2*c/((c+t)*θ)*((θ-c)/2-t)^2 := by positivity
  dsimp [Dt]
  nlinarith only [h1,h2]
lemma dc_pos (c θ t : ℝ) (hc : 0<c) (ht : 0<t) (hregion : c+2*t<θ) : 0<Dc c θ t := by
  have hθ : 0<θ := by linarith
  have hct : 0<c+t := by linarith
  let u := θ-c-2*t
  have hu : 0<u := by dsimp [u];linarith
  have hid : Dc c θ t = t*(12*c^2*t+12*c^2*u+24*c*t^2+24*c*t*u+3*c*u^2+12*t^3+12*t^2*u+3*t*u^2+u^3)/(12*(c+t)^2*θ) := by
    dsimp [Dc,u]
    field_simp
    <;> ring
  rw [hid]
  positivity
lemma dh_neg (c θ t : ℝ) (hc : 0<c) (ht : 0<t) (hregion : c+2*t<θ) : Dh c θ t<0 := by
  have hθ : 0<θ := by linarith
  have hct : 0<c+t := by linarith
  let u := θ-c-2*t
  have hu : 0<u := by dsimp [u];linarith
  have hid : Dh c θ t = -(t*(12*c^2*t+12*c^2*u+28*c*t^2+36*c*t*u+9*c*u^2+16*t^3+24*t^2*u+12*t*u^2+2*u^3)/(12*(c+t)*θ^2)) := by
    dsimp [Dh,u]
    field_simp
    <;> ring
  rw [hid]
  apply neg_neg_of_pos
  positivity
end TokenResearch
namespace TokenResearch
open TokenFinance.Debt
lemma be_iff (c C0 θ t : ℝ) : tokenBreakEven c C0 θ t ↔ G c θ t = -C0 := by
  unfold tokenBreakEven G
  constructor <;> intro h <;> linarith
lemma root_bound (c C0 θ t : ℝ) (hc : 0<c) (hcθ : c<θ)
    (hNPV : C0<(θ-c)^3/(12*θ)) (ht : 0<t) (he : tokenBreakEven c C0 θ t) : t<(θ-c)/2 := by
  have hθ : 0<θ := hc.trans hcθ
  have hcoef : 0<c/(c+t)*(2/(3*θ)) := by positivity
  have hpow : 0<((θ-c)/2-t)^3 := by
    apply (mul_pos_iff_of_pos_left hcoef).mp
    rw [he]
    linarith
  have hgap := (Odd.pow_pos_iff (by decide : Odd 3)).mp hpow
  linarith
lemma anti_t (c θ : ℝ) (hc : 0<c) (hθ : 0<θ) :
    StrictAntiOn (G c θ) (Set.Ioo 0 ((θ-c)/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · intro t ht
    exact (deriv_t c θ t (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t∈Set.Ioo 0 ((θ-c)/2) := interior_subset ht
    rw [(deriv_t c θ t (by linarith [ht'.1])).deriv]
    exact dt_neg c θ t hc hθ ht'.1.le ht'.2
lemma mono_c (θ t : ℝ) (ht : 0<t) :
    StrictMonoOn (fun c => G c θ t) (Set.Ioo 0 (θ-2*t)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
  · intro c hc
    exact (deriv_c c θ t (by linarith [hc.1])).continuousAt.continuousWithinAt
  · intro c hc
    have hc' : c∈Set.Ioo 0 (θ-2*t) := interior_subset hc
    rw [(deriv_c c θ t (by linarith [hc'.1])).deriv]
    exact dc_pos c θ t hc'.1 ht (by linarith [hc'.2])
lemma anti_h (c t : ℝ) (hc : 0<c) (ht : 0<t) :
    StrictAntiOn (fun θ => G c θ t) (Set.Ioi (c+2*t)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _) ?_ ?_
  · intro θ hθ
    have hθpos : 0<θ := by change c+2*t<θ at hθ;linarith
    exact (deriv_h c θ t (ne_of_gt hθpos)).continuousAt.continuousWithinAt
  · intro θ hθ
    have hθ' : c+2*t<θ := interior_subset hθ
    have hθpos : 0<θ := by linarith
    rw [(deriv_h c θ t (ne_of_gt hθpos)).deriv]
    exact dh_neg c θ t hc ht hθ'
lemma root_unique_core (c C0 θ : ℝ) (hc : 0<c) (hcθ : c<θ)
    (hC0 : 0<C0) (hNPV : C0<(θ-c)^3/(12*θ)) :
    (∃! t : ℝ,0<t ∧ tokenBreakEven c C0 θ t) ∧
      (∀ t : ℝ,0<t → tokenBreakEven c C0 θ t → t<(θ-c)/2) := by
  have hθ : 0<θ := hc.trans hcθ
  have htop : 0<(θ-c)/2 := by linarith
  have hz : G c θ 0=0 := by dsimp [G];field_simp;ring
  have he : G c θ ((θ-c)/2) = -((θ-c)^3/(12*θ)) := by simp [G]
  have hcont : ContinuousOn (G c θ) (Set.Icc 0 ((θ-c)/2)) := by
    intro t ht
    exact (deriv_t c θ t (by linarith [ht.1])).continuousAt.continuousWithinAt
  obtain ⟨t,ht,heq⟩ := intermediate_value_Icc' htop.le hcont
    (show -C0∈Set.Icc (G c θ ((θ-c)/2)) (G c θ 0) by rw [hz,he];constructor <;> linarith)
  have ht0 : 0<t := by
    by_contra h
    have he0 : t=0 := by linarith [ht.1]
    rw [he0,hz] at heq
    linarith
  have hbe : tokenBreakEven c C0 θ t := (be_iff c C0 θ t).mpr heq
  have hb : ∀ s:ℝ,0<s → tokenBreakEven c C0 θ s → s<(θ-c)/2 := fun s hs he => root_bound c C0 θ s hc hcθ hNPV hs he
  refine ⟨⟨t,⟨ht0,hbe⟩,?_⟩,hb⟩
  intro s hs
  exact (anti_t c θ hc hθ).injOn ⟨hs.1,hb s hs.1 hs.2⟩ ⟨ht0,hb t ht0 hbe⟩
    (((be_iff c C0 θ s).mp hs.2).trans heq.symm)
lemma baseline_mono (c θ θ' : ℝ) (hc : 0<c) (hcθ : c<θ) (hh : θ≤θ') :
    (θ-c)^3/(12*θ) ≤ (θ'-c)^3/(12*θ') := by
  have hθ : 0<θ := hc.trans hcθ
  have hθ' : 0<θ' := hθ.trans_le hh
  have hid (T : ℝ) (hT : 0<T) : (T-c)^3/(12*T) = (T-c)^2*(1-c/T)/12 := by field_simp <;> ring
  rw [hid θ hθ,hid θ' hθ']
  have hdiv : c/θ'≤c/θ := div_le_div_of_nonneg_left hc.le hθ hh
  have hf0 : 0≤1-c/θ := sub_nonneg.mpr ((div_le_one₀ hθ).mpr hcθ.le)
  have hs : (θ-c)^2≤(θ'-c)^2 := by gcongr
  exact div_le_div_of_nonneg_right (mul_le_mul hs (by linarith) hf0 (sq_nonneg _)) (by norm_num)
end TokenResearch



theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hC0 : 0 < C0) (hNPV : C0 < (θ - c) ^ 3 / (12 * θ)) :
    (∃! t : ℝ, 0 < t ∧ TokenFinance.Debt.tokenBreakEven c C0 θ t) ∧
      (∀ t : ℝ, 0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t → t < (θ - c) / 2) := by exact TokenResearch.root_unique_core c C0 θ hc hcθ hC0 hNPV



#print axioms solution
