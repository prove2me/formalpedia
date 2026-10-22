-- Prove2me | solution 1 for VaccineAMC.Framework.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:54:25.091789+00:00
-- url     : https://prove2.me/submissions/389052a4-5a83-4499-9a6f-8fc6fa9d0cae

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace VaccineAMC.Framework.P3aux

open VaccineAMC.Framework

lemma df_eq (r f : ℝ) (S : Set ℝ) :
    discountedFlow r f S = f * ∫ t in S, Real.exp (-(r * t)) := by
  unfold discountedFlow
  exact integral_const_mul f _

lemma int_Ioi (r c : ℝ) (hr : 0 < r) :
    ∫ t in Ioi c, Real.exp (-(r * t)) = Real.exp (-(r * c)) / r := by
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hr) c
  have e : (fun t : ℝ => Real.exp (-(r * t))) = fun t => Real.exp ((-r) * t) := by
    funext t; ring_nf
  rw [e, h]
  have : (-r) * c = -(r * c) := by ring
  rw [this, div_neg, neg_div, neg_neg]

lemma integ (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-(r * t))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 hr
  simpa [neg_mul] using this

lemma rest_eq (T : ℝ) (hT : 0 < T) : Ioi (0:ℝ) \ Ioo 0 T = Ici T := by
  ext x
  simp only [Set.mem_sdiff, mem_Ioi, mem_Ioo, mem_Ici, not_and, not_lt]
  constructor
  · rintro ⟨h0, h⟩; exact h h0
  · intro h; exact ⟨lt_of_lt_of_le hT h, fun _ => h⟩

lemma int_rest (r T : ℝ) (hr : 0 < r) (hT : 0 < T) :
    ∫ t in Ioi (0:ℝ) \ Ioo 0 T, Real.exp (-(r * t)) = Real.exp (-(r * T)) / r := by
  rw [rest_eq T hT, integral_Ici_eq_integral_Ioi, int_Ioi r T hr]

lemma int_Ioo (r T : ℝ) (hr : 0 < r) (hT : 0 < T) :
    ∫ t in Ioo (0:ℝ) T, Real.exp (-(r * t)) = (1 - Real.exp (-(r * T))) / r := by
  have h := setIntegral_sdiff (μ := volume) (f := fun t : ℝ => Real.exp (-(r * t)))
    (s := Ioi (0:ℝ)) (t := Ioo 0 T) measurableSet_Ioo (integ r hr) Ioo_subset_Ioi_self
  rw [int_rest r T hr hT, int_Ioi r 0 hr] at h
  simp only [mul_zero, neg_zero, Real.exp_zero] at h
  have : ∫ t in Ioo (0:ℝ) T, Real.exp (-(r * t)) = 1 / r - Real.exp (-(r * T)) / r := by
    linarith
  rw [this]; ring

lemma jointTS_temp (θ : Params) (s F a b : ℝ) (hr : 0 < θ.r) (hs : 0 < s) (hF : 0 < F)
    (h : θ.r * F < s * a) :
    jointTS θ s F a b = F + (θ.r * F / (s * a) * flow θ a
      + (1 - θ.r * F / (s * a)) * flow θ b) / θ.r := by
  have ha : 0 < s * a := lt_trans (mul_pos hr hF) h
  have hd : 0 < s * a - θ.r * F := by linarith
  have hx : 1 < s * a / (s * a - θ.r * F) := by
    rw [one_lt_div hd]; linarith [mul_pos hr hF]
  have hT : 0 < amcLength θ s F a := by
    unfold amcLength
    exact mul_pos (by positivity) (Real.log_pos hx)
  have hE : Real.exp (-(θ.r * amcLength θ s F a)) = (s * a - θ.r * F) / (s * a) := by
    unfold amcLength
    have : θ.r * (1 / θ.r * Real.log (s * a / (s * a - θ.r * F)))
        = Real.log (s * a / (s * a - θ.r * F)) := by field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  unfold jointTS amcPeriod
  rw [if_pos h, df_eq, df_eq, int_Ioo _ _ hr hT, int_rest _ _ hr hT, hE]
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hs0 : s ≠ 0 := hs.ne'
  field_simp
  ring

lemma jointTS_perm (θ : Params) (s F a b : ℝ) (hr : 0 < θ.r)
    (h : ¬ θ.r * F < s * a) :
    jointTS θ s F a b = (flow θ a + s * a) / θ.r := by
  unfold jointTS amcPeriod
  rw [if_neg h, sdiff_self, df_eq, df_eq, setIntegral_empty, int_Ioi _ 0 hr]
  simp [div_eq_mul_inv]

lemma joint_diag (θ : Params) (s F a : ℝ) (hr : 0 < θ.r) (hs : 0 < s) (hF : 0 < F)
    (h : θ.r * F ≤ s * a) :
    jointTS θ s F a a = F + flow θ a / θ.r := by
  rcases lt_or_eq_of_le h with h | h
  · rw [jointTS_temp θ s F a a hr hs hF h]
    field_simp
    ring
  · rw [jointTS_perm θ s F a a hr (by rw [h]; exact lt_irrefl _), ← h]
    field_simp
    ring

lemma joint_le (θ : Params) (s F a b m : ℝ) (hr : 0 < θ.r) (hs : 0 < s) (hF : 0 < F)
    (ha : flow θ a ≤ m) (hb : flow θ b ≤ m) :
    jointTS θ s F a b ≤ F + m / θ.r := by
  by_cases h : θ.r * F < s * a
  · rw [jointTS_temp θ s F a b hr hs hF h]
    have hsa : 0 < s * a := lt_trans (mul_pos hr hF) h
    have hw0 : 0 < θ.r * F / (s * a) := div_pos (mul_pos hr hF) hsa
    have hw1 : θ.r * F / (s * a) < 1 := (div_lt_one hsa).2 h
    have : θ.r * F / (s * a) * flow θ a + (1 - θ.r * F / (s * a)) * flow θ b ≤ m := by
      nlinarith
    have := div_le_div_of_nonneg_right this hr.le
    linarith
  · rw [jointTS_perm θ s F a b hr h]
    push Not at h
    have : flow θ a + s * a ≤ m + θ.r * F := by linarith
    have := div_le_div_of_nonneg_right this hr.le
    have e : (m + θ.r * F) / θ.r = F + m / θ.r := by field_simp; ring
    linarith

/-- calculus facts on `B` -/
lemma B_facts (θ : Params) (hS : θ.Standing) :
    Differentiable ℝ θ.B ∧ Differentiable ℝ (deriv θ.B) ∧
      StrictAntiOn (deriv θ.B) (Ici 0) := by
  obtain ⟨_, _, _, _, _, _, _, hB2, _, _, hB'', _⟩ := hS
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv] at hB2
  obtain ⟨hd, _, h1⟩ := hB2
  have hd1 : Differentiable ℝ (deriv θ.B) := h1.differentiable one_ne_zero
  refine ⟨hd, hd1, ?_⟩
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) hd1.continuous.continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  exact hB'' x (le_of_lt hx)

lemma hasDerivAt_flow (θ : Params) (hd : Differentiable ℝ θ.B) (x : ℝ) :
    HasDerivAt (flow θ) (θ.α * deriv θ.B x - θ.c) x := by
  have h := ((hd x).hasDerivAt.const_mul θ.α).sub ((hasDerivAt_id' x).const_mul θ.c)
  rw [mul_one] at h
  exact h

lemma hasDerivAt_profit (θ : Params) (hd : Differentiable ℝ θ.B) (x : ℝ) :
    HasDerivAt (profitNA θ)
      (θ.β / θ.r * (θ.α * deriv θ.B x - (θ.c + θ.κ / θ.β))) x := by
  have h := (((hd x).hasDerivAt.const_mul θ.α).sub
    ((hasDerivAt_id' x).const_mul (θ.c + θ.κ / θ.β))).const_mul (θ.β / θ.r)
  rw [mul_one] at h
  exact h

lemma flow_concave (θ : Params) (hS : θ.Standing) : ConcaveOn ℝ (Ici 0) (flow θ) := by
  obtain ⟨hd, _, hanti⟩ := B_facts θ hS
  have hα : 0 < θ.α := hS.2.1
  have hfd : Differentiable ℝ (flow θ) := fun x => (hasDerivAt_flow θ hd x).differentiableAt
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hfd.continuous.continuousOn
    hfd.differentiableOn ?_
  intro x hx y hy hxy
  rw [interior_Ici] at hx hy
  rw [(hasDerivAt_flow θ hd x).deriv, (hasDerivAt_flow θ hd y).deriv]
  have := hanti.antitoneOn (mem_Ici.2 (le_of_lt hx)) (mem_Ici.2 (le_of_lt hy)) hxy
  nlinarith

lemma profit_eq (θ : Params) (hS : θ.Standing) (q : ℝ) :
    profitNA θ q = θ.β / θ.r * flow θ q - θ.K * q := by
  have hr : 0 < θ.r := hS.1
  have hβ : 0 < θ.β := hS.2.2.2.1
  unfold profitNA flow Params.κ
  field_simp
  ring

/-- `profitNA` is maximized on `[0, ∞)` at a positive root of `invDemand = c + κ/β`. -/
lemma profit_max (θ : Params) (hS : θ.Standing) (D : ℝ) (hD : 0 < D)
    (hinv : invDemand θ D = θ.c + θ.κ / θ.β) :
    ∀ x, 0 ≤ x → profitNA θ x ≤ profitNA θ D := by
  obtain ⟨hd, _, hanti⟩ := B_facts θ hS
  have hr : 0 < θ.r := hS.1
  have hα : 0 < θ.α := hS.2.1
  have hβ : 0 < θ.β := hS.2.2.2.1
  have hbr : 0 < θ.β / θ.r := div_pos hβ hr
  unfold invDemand at hinv
  have hcont : Continuous (profitNA θ) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_profit θ hd x).continuousAt
  intro x hx
  rcases lt_trichotomy x D with hxD | hxD | hxD
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (profitNA θ) _ hxD
      hcont.continuousOn (fun y _ => hasDerivAt_profit θ hd y)
    have h1 : deriv θ.B D < deriv θ.B ξ :=
      hanti (hx.trans hξ.1.le) hD.le hξ.2
    have hpos : 0 < θ.β / θ.r * (θ.α * deriv θ.B ξ - (θ.c + θ.κ / θ.β)) := by
      apply mul_pos hbr; nlinarith
    rw [hξe] at hpos
    have hden : 0 < D - x := by linarith
    have := (lt_div_iff₀ hden).1 hpos
    linarith
  · rw [hxD]
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (profitNA θ) _ hxD
      hcont.continuousOn (fun y _ => hasDerivAt_profit θ hd y)
    have h1 : deriv θ.B ξ < deriv θ.B D :=
      hanti hD.le (hD.trans hξ.1).le hξ.1
    have hneg : θ.β / θ.r * (θ.α * deriv θ.B ξ - (θ.c + θ.κ / θ.β)) < 0 := by
      apply mul_neg_of_pos_of_neg hbr; nlinarith
    rw [hξe] at hneg
    have hden : 0 < x - D := by linarith
    have := (div_lt_iff₀ hden).1 hneg
    linarith

lemma flow_le (θ : Params) (hS : θ.Standing) (D : ℝ) (hD : 0 < D)
    (hinv : invDemand θ D = θ.c + θ.κ / θ.β) (q : ℝ) (hq : q ∈ Icc 0 D) :
    flow θ q ≤ flow θ D := by
  have hr : 0 < θ.r := hS.1
  have hβ : 0 < θ.β := hS.2.2.2.1
  have hK : 0 < θ.K := hS.2.2.2.2.2.2.1
  have h := profit_max θ hS D hD hinv q hq.1
  rw [profit_eq θ hS, profit_eq θ hS] at h
  have hKq : θ.K * q ≤ θ.K * D := mul_le_mul_of_nonneg_left hq.2 hK.le
  have : θ.β / θ.r * flow θ q ≤ θ.β / θ.r * flow θ D := by linarith
  exact le_of_mul_le_mul_left this (div_pos hβ hr)

lemma jointNA_eq (θ : Params) (hr : 0 < θ.r) (q : ℝ) : jointNA θ q = flow θ q / θ.r := by
  unfold jointNA
  rw [df_eq, int_Ioi _ 0 hr]
  simp [div_eq_mul_inv]

lemma eqNA (θ : Params) (hS : θ.Standing) (D : ℝ) (hD : 0 < D)
    (hinv : invDemand θ D = θ.c + θ.κ / θ.β) : IsEqNA θ D D := by
  have hr : 0 < θ.r := hS.1
  have hβ : 0 < θ.β := hS.2.2.2.1
  have hK : 0 < θ.K := hS.2.2.2.2.2.2.1
  have hmem : D ∈ Icc 0 D := ⟨hD.le, le_rfl⟩
  have hbarg : ∀ q' ∈ Icc 0 D, jointNA θ q' ≤ jointNA θ D := by
    intro q' hq'
    rw [jointNA_eq θ hr, jointNA_eq θ hr]
    exact div_le_div_of_nonneg_right (flow_le θ hS D hD hinv q' hq') hr.le
  refine ⟨hD.le, ⟨hmem, hbarg⟩, ?_⟩
  intro Q' hQ'
  have hsupD : sSup (jointNA θ '' Icc 0 D) = jointNA θ D :=
    IsGreatest.csSup_eq ⟨mem_image_of_mem _ hmem, by
      rintro _ ⟨q, hq, rfl⟩; exact hbarg q hq⟩
  unfold firmValueNA
  rw [hsupD]
  have hne : (jointNA θ '' Icc 0 Q').Nonempty := ⟨_, mem_image_of_mem _ ⟨le_rfl, hQ'⟩⟩
  have hle : sSup (jointNA θ '' Icc 0 Q') ≤
      (θ.β * jointNA θ D - θ.K * D + θ.K * Q') / θ.β := by
    apply csSup_le hne
    rintro _ ⟨q, hq, rfl⟩
    rw [le_div_iff₀ hβ]
    have hp := profit_max θ hS D hD hinv q hq.1
    rw [profit_eq θ hS, profit_eq θ hS] at hp
    rw [jointNA_eq θ hr, jointNA_eq θ hr]
    have hKq : θ.K * q ≤ θ.K * Q' := mul_le_mul_of_nonneg_left hq.2 hK.le
    have e1 : flow θ q / θ.r * θ.β = θ.β / θ.r * flow θ q := by ring
    have e2 : θ.β * (flow θ D / θ.r) = θ.β / θ.r * flow θ D := by ring
    rw [e1, e2]
    linarith
  have := mul_le_mul_of_nonneg_left hle hβ.le
  rw [mul_div_cancel₀ _ hβ.ne'] at this
  linarith

lemma demand_eq (θ : Params) (hS : θ.Standing) (Q : ℝ) (hQ : 0 < Q) (p : ℝ)
    (hinv : invDemand θ Q = p) : demand θ p = Q := by
  obtain ⟨_, _, hanti⟩ := B_facts θ hS
  have hα : 0 < θ.α := hS.2.1
  unfold demand
  apply IsLeast.csInf_eq
  refine ⟨⟨hQ.le, le_of_eq hinv⟩, ?_⟩
  rintro q ⟨hq0, hq⟩
  by_contra hlt
  push Not at hlt
  have := hanti hq0 hQ.le hlt
  unfold invDemand at hinv hq
  nlinarith

lemma demand_pos_inv (θ : Params) (hS : θ.Standing) (p : ℝ) (hD : 0 < demand θ p) :
    invDemand θ (demand θ p) = p := by
  obtain ⟨_, hd1, _⟩ := B_facts θ hS
  set S := {q : ℝ | 0 ≤ q ∧ invDemand θ q ≤ p} with hSdef
  have hcont : Continuous (invDemand θ) := by
    unfold invDemand; exact continuous_const.mul hd1.continuous
  have hne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : demand θ p = 0 := by unfold demand; rw [← hSdef, h, Real.sInf_empty]
    linarith
  have hbdd : BddBelow S := ⟨0, fun q hq => hq.1⟩
  have hclosed : IsClosed S := isClosed_Ici.inter (isClosed_le hcont continuous_const)
  have hmem : demand θ p ∈ S := hclosed.csInf_mem hne hbdd
  rcases lt_or_eq_of_le hmem.2 with hlt | heq
  · exfalso
    have hev : ∀ᶠ y in 𝓝 (demand θ p), invDemand θ y < p :=
      (hcont.tendsto _).eventually (gt_mem_nhds hlt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set D := demand θ p
    set y := D - min ε D / 2
    have hm0 : 0 < min ε D := lt_min hε hD
    have hmD : min ε D ≤ D := min_le_right _ _
    have hmε : min ε D ≤ ε := min_le_left _ _
    have hy0 : 0 ≤ y := by simp only [y]; linarith
    have hyD : y < D := by simp only [y]; linarith
    have hdist : dist y D < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> simp only [y] <;> linarith
    have hyS : y ∈ S := ⟨hy0, (hball hdist).le⟩
    have := csInf_le hbdd hyS
    have hDdef : D = sInf S := rfl
    linarith
  · exact heq

lemma bddTS (θ : Params) (hS : θ.Standing) (s F Q' : ℝ) (hs : 0 < s) (hF : 0 < F)
    (hQ' : 0 ≤ Q') :
    BddAbove ((fun x : ℝ × ℝ => jointTS θ s F x.1 x.2) '' (Icc 0 Q' ×ˢ Icc 0 Q')) := by
  obtain ⟨hd, _, _⟩ := B_facts θ hS
  have hr : 0 < θ.r := hS.1
  have hfc : Continuous (flow θ) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_flow θ hd x).continuousAt
  obtain ⟨x0, _, hx0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Q')).exists_isMaxOn
    ⟨0, le_rfl, hQ'⟩ hfc.continuousOn
  refine ⟨F + flow θ x0 / θ.r, ?_⟩
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact joint_le θ s F a b _ hr hs hF (hx0 ha) (hx0 hb)

lemma firm_ge (θ : Params) (hS : θ.Standing) (s F Q' a b : ℝ) (hs : 0 < s) (hF : 0 < F)
    (hQ' : 0 ≤ Q') (ha : a ∈ Icc 0 Q') (hb : b ∈ Icc 0 Q') :
    θ.β * jointTS θ s F a b - θ.K * Q' ≤ firmValueTS θ s F Q' := by
  have hβ : 0 < θ.β := hS.2.2.2.1
  unfold firmValueTS
  have := le_csSup (bddTS θ hS s F Q' hs hF hQ')
    (mem_image_of_mem (fun x : ℝ × ℝ => jointTS θ s F x.1 x.2)
      (show (a, b) ∈ Icc 0 Q' ×ˢ Icc 0 Q' from ⟨ha, hb⟩))
  have := mul_le_mul_of_nonneg_left this hβ.le
  linarith

end VaccineAMC.Framework.P3aux

open VaccineAMC.Framework.P3aux in
open VaccineAMC.Framework in
theorem solution (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ)
    (s F : ℝ) (hs : 0 < s) (hF : 0 < F) :
    (∀ Q qA qT : ℝ, IsEqTS θ s F Q qA qT → θ.r * F < s * qA →
      Q = demand θ (θ.c + θ.κ / θ.β) ∧ qA = Q ∧ qT = Q ∧ IsEqNA θ Q Q) ∧
    (θ.r * F < s * demand θ (θ.c + θ.κ / θ.β) →
      IsEqTS θ s F (demand θ (θ.c + θ.κ / θ.β))
        (demand θ (θ.c + θ.κ / θ.β))
        (demand θ (θ.c + θ.κ / θ.β))) := by
  have hr : 0 < θ.r := hS.1
  have hβ : 0 < θ.β := hS.2.2.2.1
  have hK : 0 < θ.K := hS.2.2.2.2.2.2.1
  obtain ⟨hd, _, _⟩ := B_facts θ hS
  have hrF : 0 < θ.r * F := mul_pos hr hF
  refine ⟨?_, ?_⟩
  · -- every temporary equilibrium is the no-AMC one
    rintro Q qA qT ⟨hQ0, ⟨hqA, hqT, hmax⟩, hfirm⟩ h
    have hsa : 0 < s * qA := lt_trans hrF h
    set w := θ.r * F / (s * qA) with hw
    have hw0 : 0 < w := div_pos hrF hsa
    have hw1 : w < 1 := (div_lt_one hsa).2 h
    have hqA0 : qA ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hsa; exact lt_irrefl _ hsa
    have hwq : s * (w * qA) = θ.r * F := by
      rw [hw]; field_simp
    set z := w * qA + (1 - w) * qT with hz
    have hz0 : 0 ≤ z := by
      have := mul_nonneg hw0.le hqA.1; have := mul_nonneg (sub_nonneg.2 hw1.le) hqT.1
      linarith
    have hzQ : z ≤ Q := by
      have := mul_le_mul_of_nonneg_left hqA.2 hw0.le
      have := mul_le_mul_of_nonneg_left hqT.2 (sub_nonneg.2 hw1.le)
      nlinarith
    have hsz : θ.r * F ≤ s * z := by
      have : s * z = θ.r * F + s * ((1 - w) * qT) := by rw [hz, ← hwq]; ring
      have := mul_nonneg hs.le (mul_nonneg (sub_nonneg.2 hw1.le) hqT.1)
      linarith
    have hJ := jointTS_temp θ s F qA qT hr hs hF h
    rw [← hw] at hJ
    have hconc := (flow_concave θ hS).2 (show qA ∈ Ici (0:ℝ) from hqA.1)
      (show qT ∈ Ici (0:ℝ) from hqT.1) hw0.le (sub_nonneg.2 hw1.le) (by ring)
    simp only [smul_eq_mul] at hconc
    have hJz : jointTS θ s F qA qT ≤ jointTS θ s F z z := by
      rw [hJ, joint_diag θ s F z hr hs hF hsz]
      have := div_le_div_of_nonneg_right hconc hr.le
      linarith
    have hsupQ : sSup ((fun x : ℝ × ℝ => jointTS θ s F x.1 x.2) '' (Icc 0 Q ×ˢ Icc 0 Q))
        = jointTS θ s F qA qT := by
      apply IsGreatest.csSup_eq
      refine ⟨mem_image_of_mem (fun x : ℝ × ℝ => jointTS θ s F x.1 x.2)
        (show (qA, qT) ∈ Icc 0 Q ×ˢ Icc 0 Q from ⟨hqA, hqT⟩), ?_⟩
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact hmax a ha b hb
    have hVQ : firmValueTS θ s F Q = θ.β * jointTS θ s F qA qT - θ.K * Q := by
      unfold firmValueTS; rw [hsupQ]
    have hVz := firm_ge θ hS s F z z z hs hF hz0 ⟨hz0, le_rfl⟩ ⟨hz0, le_rfl⟩
    have hfz := hfirm z hz0
    have hQz : Q ≤ z := by
      have := mul_le_mul_of_nonneg_left hJz hβ.le
      have : θ.K * Q ≤ θ.K * z := by linarith
      exact le_of_mul_le_mul_left this hK
    have hqAQ : qA = Q := by
      by_contra hne
      have hlt : qA < Q := lt_of_le_of_ne hqA.2 hne
      nlinarith [mul_pos hw0 (sub_pos.2 hlt),
        mul_nonneg (sub_nonneg.2 hw1.le) (sub_nonneg.2 hqT.2)]
    have hqTQ : qT = Q := by
      by_contra hne
      have hlt : qT < Q := lt_of_le_of_ne hqT.2 hne
      nlinarith [mul_pos (sub_pos.2 hw1) (sub_pos.2 hlt),
        mul_nonneg hw0.le (sub_nonneg.2 hqA.2)]
    subst hqTQ
    subst hqAQ
    -- now Q = qA = qT maximizes profitNA on [rF/s, ∞)
    have hQpos : 0 < qA := pos_of_mul_pos_right hsa hs.le
    have hVQ' : firmValueTS θ s F qA = θ.β * F + profitNA θ qA := by
      rw [hVQ, joint_diag θ s F qA hr hs hF h.le, profit_eq θ hS]; ring
    have hloc : IsLocalMax (profitNA θ) qA := by
      have hlt : θ.r * F / s < qA := by rw [div_lt_iff₀ hs]; linarith
      filter_upwards [Ioi_mem_nhds hlt] with Q' hQ'
      have hsQ' : θ.r * F < s * Q' := by
        rw [mem_Ioi, div_lt_iff₀ hs] at hQ'; linarith
      have hQ'0 : 0 ≤ Q' := (pos_of_mul_pos_right (lt_trans hrF hsQ') hs.le).le
      have h1 := firm_ge θ hS s F Q' Q' Q' hs hF hQ'0 ⟨hQ'0, le_rfl⟩ ⟨hQ'0, le_rfl⟩
      have h2 := hfirm Q' hQ'0
      rw [joint_diag θ s F Q' hr hs hF hsQ'.le] at h1
      rw [hVQ'] at h2
      have e : θ.β * (F + flow θ Q' / θ.r) - θ.K * Q' = θ.β * F + profitNA θ Q' := by
        rw [profit_eq θ hS]; ring
      linarith
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_profit θ hd qA)
    have hbr : θ.β / θ.r ≠ 0 := (div_pos hβ hr).ne'
    have hinv : invDemand θ qA = θ.c + θ.κ / θ.β := by
      unfold invDemand
      have := (mul_eq_zero.1 h0).resolve_left hbr
      linarith
    exact ⟨(demand_eq θ hS qA hQpos _ hinv).symm, rfl, rfl, eqNA θ hS qA hQpos hinv⟩
  · -- existence on the temporary branch
    intro h
    set D := demand θ (θ.c + θ.κ / θ.β) with hDdef
    have hsD : 0 < s * D := lt_trans hrF h
    have hD : 0 < D := pos_of_mul_pos_right hsD hs.le
    have hinv : invDemand θ D = θ.c + θ.κ / θ.β := demand_pos_inv θ hS _ hD
    have hmem : D ∈ Icc 0 D := ⟨hD.le, le_rfl⟩
    have hdiag := joint_diag θ s F D hr hs hF h.le
    have hbarg : ∀ a ∈ Icc 0 D, ∀ b ∈ Icc 0 D, jointTS θ s F a b ≤ jointTS θ s F D D := by
      intro a ha b hb
      rw [hdiag]
      exact joint_le θ s F a b _ hr hs hF (flow_le θ hS D hD hinv a ha)
        (flow_le θ hS D hD hinv b hb)
    refine ⟨hD.le, ⟨hmem, hmem, hbarg⟩, ?_⟩
    intro Q' hQ'
    have hsupD : sSup ((fun x : ℝ × ℝ => jointTS θ s F x.1 x.2) '' (Icc 0 D ×ˢ Icc 0 D))
        = jointTS θ s F D D := by
      apply IsGreatest.csSup_eq
      refine ⟨mem_image_of_mem (fun x : ℝ × ℝ => jointTS θ s F x.1 x.2)
        (show (D, D) ∈ Icc 0 D ×ˢ Icc 0 D from ⟨hmem, hmem⟩), ?_⟩
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact hbarg a ha b hb
    unfold firmValueTS
    rw [hsupD, hdiag]
    have hne : ((fun x : ℝ × ℝ => jointTS θ s F x.1 x.2) '' (Icc 0 Q' ×ˢ Icc 0 Q')).Nonempty :=
      ⟨_, mem_image_of_mem _ (show ((0:ℝ), (0:ℝ)) ∈ Icc 0 Q' ×ˢ Icc 0 Q' from
        ⟨⟨le_rfl, hQ'⟩, ⟨le_rfl, hQ'⟩⟩)⟩
    have hle : sSup ((fun x : ℝ × ℝ => jointTS θ s F x.1 x.2) '' (Icc 0 Q' ×ˢ Icc 0 Q')) ≤
        (θ.β * (F + flow θ D / θ.r) - θ.K * D + θ.K * Q') / θ.β := by
      apply csSup_le hne
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      rw [le_div_iff₀ hβ]
      have key : ∀ x ∈ Icc 0 Q', jointTS θ s F a b ≤ F + flow θ x / θ.r →
          jointTS θ s F a b * θ.β ≤ θ.β * (F + flow θ D / θ.r) - θ.K * D + θ.K * Q' := by
        intro x hx hj
        have hp := profit_max θ hS D hD hinv x hx.1
        rw [profit_eq θ hS, profit_eq θ hS] at hp
        have hKx : θ.K * x ≤ θ.K * Q' := mul_le_mul_of_nonneg_left hx.2 hK.le
        have := mul_le_mul_of_nonneg_left hj hβ.le
        have e1 : θ.β * (F + flow θ x / θ.r) = θ.β * F + θ.β / θ.r * flow θ x := by ring
        have e2 : θ.β * (F + flow θ D / θ.r) = θ.β * F + θ.β / θ.r * flow θ D := by ring
        rw [e1] at this; rw [e2]
        linarith
      rcases le_total (flow θ a) (flow θ b) with hab | hab
      · exact key b hb (joint_le θ s F a b _ hr hs hF hab le_rfl)
      · exact key a ha (joint_le θ s F a b _ hr hs hF le_rfl hab)
    have := mul_le_mul_of_nonneg_left hle hβ.le
    rw [mul_div_cancel₀ _ hβ.ne'] at this
    linarith
