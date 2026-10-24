-- Prove2me | solution 1 for SuspensionContract.HighCostC1.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:34:19.173854+00:00
-- url     : https://prove2.me/submissions/4b03f28a-b635-4992-a1a3-dd420c7d9943
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_Thresholds
import Theorems.Thm_SuspensionContract_HighCostC1_lemma_EC_2
import Theorems.Thm_SuspensionContract_HighCostC1_lemma_2_ii_iii
import Theorems.Thm_SuspensionContract_HighCostC1_lemma_3
import Theorems.Thm_SuspensionContract_HighCostC1_proposition_2

open Set SuspensionContract.HighCostC1

/-- Supergradient inequality for a concave function on `ℝ₊` differentiable at `θ > 0`. -/
private lemma hc1p3_supergrad {F : ℝ → ℝ} (hconc : ConcaveOn ℝ (Ici 0) F) {θ : ℝ} (hθ : 0 < θ)
    (hd : DifferentiableAt ℝ F θ) {y : ℝ} (hy : 0 ≤ y) :
    F y ≤ F θ + deriv F θ * (y - θ) := by
  rcases lt_trichotomy y θ with h | h | h
  · have := hconc.deriv_le_slope (x := y) (y := θ) hy hθ.le h hd
    rw [slope_def_field] at this
    have hpos : 0 < θ - y := by linarith
    rw [le_div_iff₀ hpos] at this
    nlinarith
  · subst h; simp
  · have := hconc.slope_le_deriv (x := θ) (y := y) hθ.le hy h hd
    rw [slope_def_field] at this
    have hpos : 0 < y - θ := by linarith
    rw [div_le_iff₀ hpos] at this
    nlinarith

private lemma hc1p3_what (P : Params) (k : ℝ) : ({P with K := k} : Params).what = P.what := by
  unfold Params.what Params.calV Params.wcheck Params.Vt Params.SolvesDDE Params.VbarFn
    Params.vlow Params.wbar Params.β Params.Δμ
  rfl

private lemma hc1p3_calV (P : Params) (k : ℝ) : ({P with K := k} : Params).calV = P.calV := by
  funext w
  unfold Params.calV Params.wcheck Params.Vt Params.SolvesDDE Params.VbarFn
    Params.wbar Params.β Params.Δμ
  rfl

private lemma hc1p3_AI (P : Params) (k : ℝ) : ({P with K := k} : Params).AI = P.AI := by
  funext f w
  unfold Params.AI Params.wbar Params.β Params.Δμ
  rfl

theorem solution (P : Params) (hP : P.Standing) (h1 : P.Condition1)
    (hK : P.Kbar1 ≤ P.K ∧ P.K ≤ P.VbarFn P.what - P.vlow)
    (θ m : ℝ) (hθm : P.TangentPair P.K θ m) :
    P.OptCond (P.calV P.what) (P.V030 θ m) := by
  obtain ⟨hμlow, hμ, hb, hbc, hKpos, hr, hrρ, hRc⟩ := hP
  have hP : P.Standing := ⟨hμlow, hμ, hb, hbc, hKpos, hr, hrρ, hRc⟩
  have hρ : 0 < P.ρ := lt_of_lt_of_le hr hrρ
  have hΔ : 0 < P.Δμ := by unfold Params.Δμ; linarith
  have hβ : 0 < P.β := by unfold Params.β; positivity
  have hμpos : 0 < P.μ := by linarith
  have hwbar : 0 < P.wbar := by unfold Params.wbar; positivity
  have hrvlow : P.r * P.vlow = P.μlow * P.R := by
    unfold Params.vlow; field_simp
  -- solutions of the delay ODE
  have hsol : ∀ wt, 0 ≤ wt → wt < P.wbar → P.SolvesDDE wt (P.Vt wt) := by
    intro wt h0 h1'
    have hex := (lemma_EC_2 P hP wt h0 h1').1
    unfold Params.Vt
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  -- the threshold `wcheck` lies in `[0, wt]`
  have hwc : ∀ wt, 0 ≤ wt → 0 ≤ P.wcheck wt ∧ P.wcheck wt ≤ wt := by
    intro wt h0
    constructor
    · exact Real.sSup_nonneg (fun x hx => hx.1)
    · exact Real.sSup_le (fun x hx => hx.2.1) h0
  -- identify `what`
  obtain ⟨⟨ws, ⟨hws0, hws1, hwsV⟩, hwsu⟩, -⟩ := lemma_3 P hP h1
  have hwhat : P.what = ws := by
    have hset : {w : ℝ | 0 ≤ w ∧ w < P.wbar ∧ P.calV w 0 = P.vlow} = {ws} := by
      ext w
      simp only [mem_setOf_eq, mem_singleton_iff]
      constructor
      · intro hw; exact hwsu w hw
      · rintro rfl; exact ⟨hws0, hws1, hwsV⟩
    unfold Params.what
    rw [hset, csInf_singleton]
  have hW0' : 0 ≤ P.what := by rw [hwhat]; exact hws0
  have hW1 : P.what < P.wbar := by rw [hwhat]; exact hws1
  have hF0 : P.calV P.what 0 = P.vlow := by rw [hwhat]; exact hwsV
  have hW0 : 0 < P.what := by
    rcases hW0'.eq_or_lt with h | h
    · exfalso
      rw [← h] at hF0
      have hc0 : P.wcheck 0 = 0 := le_antisymm (hwc 0 le_rfl).2 (hwc 0 le_rfl).1
      have hs0 := hsol 0 le_rfl hwbar
      have hv : P.Vt 0 0 = P.VbarFn 0 := hs0.2.2 0 le_rfl
      have hF0' : P.calV 0 0 = P.Vt 0 (min 0 0) := by
        unfold Params.calV; rw [hc0, if_neg (lt_irrefl 0)]
      rw [hF0', min_self, hv] at hF0
      unfold Params.VbarFn Params.vlow at hF0
      rw [div_eq_div_iff hr.ne' hr.ne'] at hF0
      have : P.R * P.μ - P.c - (P.ρ - P.r) * 0 = P.μlow * P.R := mul_right_cancel₀ hr.ne' hF0
      nlinarith
    · exact h
  have hV := hsol P.what hW0' hW1
  obtain ⟨hwc0, hwcW⟩ := hwc P.what hW0'
  have hVb : ∀ y, P.what ≤ y → P.Vt P.what y = P.VbarFn P.what := hV.2.2
  have hVdiffIoo : ∀ w ∈ Ioo 0 P.what, DifferentiableAt ℝ (P.Vt P.what) w := by
    intro w hw
    have := hV.1.differentiableOn (by norm_num) w (Ioo_subset_Icc_self hw)
    exact this.differentiableAt (Icc_mem_nhds hw.1 hw.2)
  have hVderivW : HasDerivAt (P.Vt P.what) 0 P.what := by
    have hdw : DifferentiableWithinAt ℝ (P.Vt P.what) (Icc 0 P.what) P.what :=
      hV.1.differentiableOn (by norm_num) P.what ⟨hW0', le_rfl⟩
    have hode := hV.2.1 P.what ⟨hW0', le_rfl⟩
    have hmin : min (P.what + P.β) P.what = P.what := min_eq_right (by linarith)
    rw [hmin, hVb P.what le_rfl] at hode
    have hd0 : derivWithin (P.Vt P.what) (Icc 0 P.what) P.what = 0 := by
      have hVbar : P.r * P.VbarFn P.what = P.R * P.μ - P.c - (P.ρ - P.r) * P.what := by
        unfold Params.VbarFn; field_simp
      have h2 : P.ρ * (P.wbar - P.what) * derivWithin (P.Vt P.what) (Icc 0 P.what) P.what = 0 := by
        nlinarith
      have h3 : P.ρ * (P.wbar - P.what) ≠ 0 := by
        have : 0 < P.wbar - P.what := by linarith
        positivity
      exact (mul_eq_zero.mp h2).resolve_left h3
    have h1' : HasDerivWithinAt (P.Vt P.what) 0 (Icc 0 P.what) P.what := hdw.hasDerivWithinAt.congr_deriv hd0
    have h2' : HasDerivWithinAt (P.Vt P.what) 0 (Ici P.what) P.what := by
      apply (hasDerivWithinAt_const P.what (Ici P.what) (P.VbarFn P.what)).congr
      · intro y hy; exact hVb y hy
      · exact hVb P.what le_rfl
    have h3' := h1'.union h2'
    apply h3'.hasDerivAt
    apply Filter.mem_of_superset (Ioi_mem_nhds hW0)
    intro y hy
    rcases le_total y P.what with h | h
    · exact Or.inl ⟨le_of_lt hy, h⟩
    · exact Or.inr h
  have hVconstGt : ∀ w, P.what < w → HasDerivAt (P.Vt P.what) 0 w := by
    intro w hw
    apply (hasDerivAt_const w (P.VbarFn P.what)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hw] with y hy
    exact hVb y (le_of_lt hy)
  have hVdiff : ∀ w, 0 < w → DifferentiableAt ℝ (P.Vt P.what) w := by
    intro w hw
    rcases lt_trichotomy w P.what with h | h | h
    · exact hVdiffIoo w ⟨hw, h⟩
    · rw [h]; exact hVderivW.differentiableAt
    · exact (hVconstGt w h).differentiableAt
  have hVderiv0 : ∀ w, P.what ≤ w → deriv (P.Vt P.what) w = 0 := by
    intro w hw
    rcases hw.eq_or_lt with h | h
    · rw [← h]; exact hVderivW.deriv
    · exact (hVconstGt w h).deriv
  -- the concavified function
  have hFeq : ∀ y, P.calV P.what y = if y < P.wcheck P.what then
      P.Vt P.what (P.wcheck P.what) + d1 (P.Vt P.what) (P.wcheck P.what) * (y - P.wcheck P.what)
      else P.Vt P.what (min y P.what) := fun y => rfl
  have hFV : ∀ y, P.wcheck P.what ≤ y → P.calV P.what y = P.Vt P.what y := by
    intro y hy
    rw [hFeq, if_neg (not_lt.mpr hy)]
    rcases le_total y P.what with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, hVb P.what le_rfl, hVb y h]
  have hFL : ∀ y, y < P.wcheck P.what → P.calV P.what y =
      P.Vt P.what (P.wcheck P.what) + d1 (P.Vt P.what) (P.wcheck P.what) * (y - P.wcheck P.what) := by
    intro y hy; rw [hFeq, if_pos hy]
  have hd1 : ∀ (f : ℝ → ℝ) (x : ℝ), 0 < x → d1 f x = deriv f x := by
    intro f x hx; exact derivWithin_of_mem_nhds (Ici_mem_nhds hx)
  have hlin : ∀ w, 0 < P.wcheck P.what → HasDerivAt (fun y => P.Vt P.what (P.wcheck P.what) +
      d1 (P.Vt P.what) (P.wcheck P.what) * (y - P.wcheck P.what))
      (deriv (P.Vt P.what) (P.wcheck P.what)) w := by
    intro w hwc'
    rw [hd1 _ _ hwc']
    have := (((hasDerivAt_id w).sub_const (P.wcheck P.what)).const_mul
      (deriv (P.Vt P.what) (P.wcheck P.what))).const_add (P.Vt P.what (P.wcheck P.what))
    simpa using this
  have hFderiv : ∀ w, 0 < w → HasDerivAt (P.calV P.what)
      (if w < P.wcheck P.what then deriv (P.Vt P.what) (P.wcheck P.what)
        else deriv (P.Vt P.what) w) w := by
    intro w hw
    rcases lt_trichotomy w (P.wcheck P.what) with h | h | h
    · rw [if_pos h]
      apply (hlin w (hw.trans h)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds h] with y hy
      exact hFL y hy
    · rw [h, if_neg (lt_irrefl _)]
      have hwc' : 0 < P.wcheck P.what := h ▸ hw
      have hl : HasDerivWithinAt (P.calV P.what) (deriv (P.Vt P.what) (P.wcheck P.what))
          (Iic (P.wcheck P.what)) (P.wcheck P.what) := by
        apply (hlin (P.wcheck P.what) hwc').hasDerivWithinAt.congr
        · intro y hy
          rcases (show y ≤ P.wcheck P.what from hy).lt_or_eq with h' | h'
          · exact hFL y h'
          · rw [h', hFV _ le_rfl]; ring
        · rw [hFV _ le_rfl]; ring
      have hrt : HasDerivWithinAt (P.calV P.what) (deriv (P.Vt P.what) (P.wcheck P.what))
          (Ici (P.wcheck P.what)) (P.wcheck P.what) := by
        apply (hVdiff _ hwc').hasDerivAt.hasDerivWithinAt.congr
        · intro y hy; exact hFV y hy
        · exact hFV _ le_rfl
      have := hl.union hrt
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this
    · rw [if_neg (not_lt.mpr h.le)]
      apply (hVdiff w hw).hasDerivAt.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact hFV y hy.le
  have hFdiff : ∀ w, 0 < w → DifferentiableAt ℝ (P.calV P.what) w :=
    fun w hw => (hFderiv w hw).differentiableAt
  have hFderivW : ∀ w, P.what ≤ w → deriv (P.calV P.what) w = 0 := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le hW0 hw
    rw [(hFderiv w hw0).deriv, if_neg (not_lt.mpr (hwcW.trans hw)), hVderiv0 w hw]
  obtain ⟨hmonoconc, -⟩ := lemma_2_ii_iii P hP
  obtain ⟨hFmono, hFconcIco⟩ := hmonoconc P.what ⟨hW0, hW1⟩
  have hFconcIoo : ConcaveOn ℝ (Ioo 0 P.what) (P.calV P.what) :=
    hFconcIco.subset Ioo_subset_Ico_self (convex_Ioo 0 P.what)
  have hFanti : AntitoneOn (deriv (P.calV P.what)) (Ioo 0 P.what) :=
    hFconcIoo.antitoneOn_deriv (fun x hx => hFdiff x hx.1)
  have hFnonneg : ∀ x ∈ Ioo 0 P.what, 0 ≤ deriv (P.calV P.what) x := by
    intro x hx
    have := (hFmono.monotoneOn.mono Ioo_subset_Ico_self).derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at this
  have hFantiI : AntitoneOn (deriv (P.calV P.what)) (Ioi 0) := by
    intro x hx y hy hxy
    by_cases hyW : y < P.what
    · exact hFanti ⟨hx, lt_of_le_of_lt hxy hyW⟩ ⟨hy, hyW⟩ hxy
    · rw [hFderivW y (not_lt.mp hyW)]
      by_cases hxW : x < P.what
      · exact hFnonneg x ⟨hx, hxW⟩
      · rw [hFderivW x (not_lt.mp hxW)]
  have hFcont : ContinuousOn (P.calV P.what) (Ici 0) := by
    intro x hx
    rcases (show (0:ℝ) ≤ x from hx).eq_or_lt with h | h
    · rw [← h]
      by_cases hwcp : 0 < P.wcheck P.what
      · have : ContinuousAt (P.calV P.what) 0 := by
          apply (hlin 0 hwcp).continuousAt.congr
          filter_upwards [Iio_mem_nhds hwcp] with y hy
          exact (hFL y hy).symm
        exact this.continuousWithinAt
      · have hwc00 : P.wcheck P.what = 0 := le_antisymm (not_lt.mp hwcp) hwc0
        have hVc : ContinuousWithinAt (P.Vt P.what) (Ici 0) 0 :=
          (hV.1.continuousOn 0 ⟨le_rfl, hW0'⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hW0)
        apply hVc.congr
        · intro y hy; exact hFV y (by rw [hwc00]; exact hy)
        · exact hFV 0 (by rw [hwc00])
    · exact (hFdiff x h).continuousAt.continuousWithinAt
  have hFconc : ConcaveOn ℝ (Ici 0) (P.calV P.what) := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hFcont
    · rw [interior_Ici]; intro x hx; exact (hFdiff x hx).differentiableWithinAt
    · rw [interior_Ici]; exact hFantiI
  have hFmonoI : MonotoneOn (P.calV P.what) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hFcont
    · rw [interior_Ici]; intro x hx; exact (hFdiff x hx).differentiableWithinAt
    · rw [interior_Ici]; intro x hx
      by_cases hxW : x < P.what
      · exact hFnonneg x ⟨hx, hxW⟩
      · rw [hFderivW x (not_lt.mp hxW)]
  have hsg : ∀ t, 0 < t → ∀ y, 0 ≤ y →
      P.calV P.what y ≤ P.calV P.what t + d1 (P.calV P.what) t * (y - t) := by
    intro t ht y hy; rw [hd1 _ t ht]; exact hc1p3_supergrad hFconc ht (hFdiff t ht) hy
  have hθpos : ∀ K' θ' m', 0 < K' → P.TangentPair K' θ' m' → 0 < θ' := by
    intro K' θ' m' hK' hT
    obtain ⟨⟨hθ1, -⟩, -, hT3, -⟩ := hT
    have hθ0 : 0 ≤ θ' := le_trans hwc0 hθ1
    rcases hθ0.eq_or_lt with h | h
    · exfalso; rw [← h, hF0] at hT3; nlinarith
    · exact h
  have hθ0 : 0 < θ := hθpos P.K θ m hKpos hθm
  obtain ⟨hθI, hmI, hθV, hθd⟩ := hθm
  have hKtop : P.VbarFn P.what - P.vlow ∈ {K : ℝ | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧
      ∃ θ m, P.TangentPair K θ m ∧ m < 1} := by
    have hT : P.TangentPair (P.VbarFn P.what - P.vlow) P.what 0 := by
      unfold Params.TangentPair
      refine ⟨⟨hwcW, le_rfl⟩, ⟨le_rfl, hFmonoI.derivWithin_nonneg⟩, ?_, ?_⟩
      · rw [hFV P.what hwcW, hVb P.what le_rfl]; ring
      · rw [hd1 _ P.what hW0]; exact hFderivW P.what le_rfl
    exact ⟨lt_of_lt_of_le hKpos hK.2, le_rfl, P.what, 0, hT, by norm_num⟩
  have hm1 : m ≤ 1 := by
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have hne : ({K : ℝ | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧
      ∃ θ m, P.TangentPair K θ m ∧ m < 1}).Nonempty := ⟨_, hKtop⟩
    have hlt : sInf {K : ℝ | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧
        ∃ θ m, P.TangentPair K θ m ∧ m < 1} < P.K + (m - 1) * θ := by
      have : P.Kbar1 = sInf {K : ℝ | 0 < K ∧ K ≤ P.VbarFn P.what - P.vlow ∧
        ∃ θ m, P.TangentPair K θ m ∧ m < 1} := rfl
      nlinarith [hK.1, mul_pos (sub_pos.mpr hcon) hθ0]
    obtain ⟨K', hK'S, hK'lt⟩ := exists_lt_of_csInf_lt hne hlt
    obtain ⟨hK'0, -, θ', m', hT', hm'⟩ := hK'S
    have hθ'0 := hθpos K' θ' m' hK'0 hT'
    obtain ⟨-, -, hT'3, hT'4⟩ := hT'
    have := hsg θ' hθ'0 θ hθ0.le
    rw [hT'4, hT'3, hθV] at this
    nlinarith [mul_pos hθ0 (sub_pos.mpr hm')]
  -- `A_I` part from Proposition 2 (which does not depend on `K`)
  have hAI : ∀ w, 0 < w → 0 ≤ P.AI (P.calV P.what) w := by
    have hP' : ({P with K := P.VbarFn P.what - P.vlow + P.K} : Params).Standing :=
      ⟨hμlow, hμ, hb, hbc, by show 0 < P.VbarFn P.what - P.vlow + P.K; linarith [hK.2],
        hr, hrρ, hRc⟩
    have hK' : ({P with K := P.VbarFn P.what - P.vlow + P.K} : Params).VbarFn
        ({P with K := P.VbarFn P.what - P.vlow + P.K} : Params).what
        - ({P with K := P.VbarFn P.what - P.vlow + P.K} : Params).vlow
        ≤ ({P with K := P.VbarFn P.what - P.vlow + P.K} : Params).K := by
      rw [hc1p3_what]
      show P.VbarFn P.what - P.vlow ≤ P.VbarFn P.what - P.vlow + P.K; linarith
    have h2 := proposition_2 _ hP' h1 hK'
    intro w hw
    have := (h2.1 w hw).1
    rwa [hc1p3_AI, hc1p3_calV, hc1p3_what] at this
  have hV030 : ∀ y, P.V030 θ m y = if y ≤ θ then m * y + P.vlow else P.calV P.what y - P.K :=
    fun y => rfl
  have hdθ : deriv (P.calV P.what) θ = m := by rw [← hd1 _ θ hθ0]; exact hθd
  unfold Params.OptCond
  refine ⟨fun w hw => ⟨hAI w hw, ?_⟩, fun w hw => ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Params.A0
    by_cases hwθ : w ≤ θ
    · have hd : derivWithin (P.V030 θ m) (Iic w) w = m := by
        have hl : HasDerivWithinAt (fun y => m * y + P.vlow) m (Iic w) w := by
          simpa using (((hasDerivAt_id w).const_mul m).add_const P.vlow).hasDerivWithinAt
        have : HasDerivWithinAt (P.V030 θ m) m (Iic w) w := by
          apply hl.congr
          · intro y hy; rw [hV030, if_pos (le_trans hy hwθ)]
          · rw [hV030, if_pos hwθ]
        exact this.derivWithin (uniqueDiffWithinAt_Iic w)
      rw [hd, hV030, if_pos hwθ]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hrρ) (sub_nonneg.2 hm1)) hw.le]
    · replace hwθ := lt_of_not_ge hwθ
      have hd : derivWithin (P.V030 θ m) (Iic w) w = deriv (P.calV P.what) w := by
        have h1' : HasDerivAt (fun y => P.calV P.what y - P.K) (deriv (P.calV P.what) w) w :=
          (hFdiff w hw).hasDerivAt.sub_const P.K
        have h2' : HasDerivAt (P.V030 θ m) (deriv (P.calV P.what) w) w := by
          apply h1'.congr_of_eventuallyEq
          filter_upwards [Ioi_mem_nhds hwθ] with y hy
          rw [hV030, if_neg (not_le.mpr hy)]
        exact h2'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic w)
      rw [hd, hV030, if_neg (not_le.mpr hwθ)]
      have hD : deriv (P.calV P.what) w ≤ m := by
        rw [← hdθ]; exact hFantiI hθ0 hw hwθ.le
      have hsl := hFconc.deriv_le_slope (x := θ) (y := w) hθ0.le hw.le hwθ (hFdiff w hw)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at hsl
      rw [hθV] at hsl
      have t1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hrρ) (sub_nonneg.2 hwθ.le))
          (sub_nonneg.2 (hD.trans hm1))
      have t2 := mul_nonneg hθ0.le (mul_nonneg (sub_nonneg.2 hrρ) (sub_nonneg.2 hm1))
      have t3 := mul_nonneg hθ0.le (mul_nonneg hρ.le (sub_nonneg.2 hD))
      have t4 := mul_le_mul_of_nonneg_left hsl hr.le
      linarith
  · by_cases hwθ : w ≤ θ
    · rw [hV030, if_pos hwθ]
      have hb0 : 0 ≤ w / θ := div_nonneg hw hθ0.le
      have hb1 : w / θ ≤ 1 := (div_le_one hθ0).mpr hwθ
      have hc := hFconc.2 (Set.mem_Ici.mpr (le_refl (0:ℝ))) (show θ ∈ Ici 0 from hθ0.le)
        (sub_nonneg.mpr hb1) hb0 (by ring)
      simp only [smul_eq_mul] at hc
      have e : (1 - w / θ) * 0 + w / θ * θ = w := by field_simp; ring
      rw [e, hF0, hθV] at hc
      have e2 : w / θ * (m * θ + P.K + P.vlow) = m * w + w / θ * P.K + w / θ * P.vlow := by
        field_simp
      rw [e2] at hc
      have := mul_nonneg hb0 hKpos.le
      linarith
    · rw [hV030, if_neg hwθ]; linarith
  · by_cases hwθ : w ≤ θ
    · rw [hV030, if_pos hwθ]
      have := hsg θ hθ0 w hw
      rw [hθd, hθV] at this
      linarith
    · rw [hV030, if_neg hwθ]; linarith
  · rw [hF0]
  · rw [hV030, if_pos hθ0.le]; simp
