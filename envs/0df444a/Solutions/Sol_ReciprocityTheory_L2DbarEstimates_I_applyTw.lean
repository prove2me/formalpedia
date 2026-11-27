-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.applyTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:30:32.046903+00:00
-- url     : https://prove2.me/submissions/5d40bc00-2b92-4868-bb89-46a311f79880

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cont_of_smoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cutExt_support
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_cutExt_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_db_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_dbar_cutExt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_measurable_gt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_pt_in
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_pt_out
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smoothR_ev
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smooth_cutExt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hTW : TWStatement n M) (hT : TwistLeviStatement n M) (hD : DualStatement n M)
    (hB : BasicStatement n M) : ApplyStatement n M := by
  intro X g ph ph2 r j c W m χ ε δ hg hph hpl hph2 hpl2 hr hj hbd hS hJ hW hχ hε hε50 hm hδ hδε
  have hz := X.isLocalHomeomorph
  obtain ⟨hψs, hΦs, hΘ1, -⟩ := hT X.z g ph ph2 r j ε δ hz hg hph hpl hph2 hpl2 hr hj hε hδ hbd
  obtain ⟨hd1, hd2, hd3⟩ := hD X.z g ph ph2 r j ε δ hz hg hph hpl hph2 hpl2 hr hj hε hδ hbd
  obtain ⟨hb1, hΦb, hb8, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  obtain ⟨hχs, hχ1, hχ0, -, hχd⟩ := hχ
  have hε2 : 0 < ε ^ 2 := by positivity
  have hev := ap_smoothR_ev n X.z g hg ph hph r
  have hevc := ap_cont_of_smoothR n X.z hz _ hev
  have hψc := ap_cont_of_smoothR n X.z hz _ hψs
  have hη1 : ∀ x, 1 ≤ eta n g ph r ε x := fun x => (hb1 x).2.1
  have hΘ : ∀ x ξ, 0 ≤ (Levi n X.z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
    intro x ξ
    refine le_trans (mul_nonneg (add_nonneg (div_nonneg zero_le_one
      (mul_nonneg (sq_nonneg _) (by linarith [hη1 x]))) (sq_nonneg _)) (sq_nonneg _)) (hΘ1 x ξ)
  have hF0s : Smooth n X.z (cutExt n X.z g ph r c W χ ε) :=
    ap_smooth_cutExt n X.z hz g hg ph hph r c W m χ ε hS hW hχs hχ0 hε (by linarith)
  have hF0c := Smooth.continuous n X.z hz _ hF0s
  have hK : IsCompact (⋃ p ∈ hS.toFinset, closure (W p)) :=
    hS.toFinset.isCompact_biUnion (fun p hp => (hW.2 p (hS.mem_toFinset.1 hp)).2.2.1)
  have hwint : wint n X.z (cutExt n X.z g ph r c W χ ε) (wgt n g ph ph2 r j δ) < ⊤ := by
    have hcs : HasCompactSupport (fun x => ‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 *
        Real.exp (-wgt n g ph ph2 r j δ x)) := by
      refine HasCompactSupport.intro hK (fun x hx => ?_)
      have h0 := ap_cutExt_support n X.z g ph r c W χ ε hS x hx
      simp [h0]
    have hcont : Continuous (fun x => ‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 *
        Real.exp (-wgt n g ph ph2 r j δ x)) :=
      (hF0c.norm.pow 2).mul (Real.continuous_exp.comp hψc.neg)
    exact (integrable_of_continuous_real n X.z hz _ hcont hcs).lintegral_lt_top
  have hevm : Measurable (ev n g ph r) := hevc.measurable
  have hetam : Measurable (eta n g ph r ε) := by
    unfold eta xx lw
    fun_prop
  have hxxm : Measurable (xx n g ph r ε) := by
    unfold xx lw
    fun_prop
  have hgtm := ap_measurable_gt n X.z hz g hg ph r c W m hS hW
  have hshm : MeasurableSet (shell n g ph r ε) := by
    have hcl : IsClosed (shell n g ph r ε) :=
      (isClosed_le continuous_const hevc).inter (isClosed_le hevc continuous_const)
    exact hcl.measurableSet
  obtain ⟨a, ha⟩ : ∃ a : M → ℝ, a = (shell n g ph r ε).indicator
      (fun x => 36 * eta n g ph r ε x * ‖gt n X.z g c W x‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : M → ℝ, b = fun x => if ev n g ph r x ≤ ε ^ 2 then
      2 / eta n g ph r ε x else bfun n g ph r ε x := ⟨_, rfl⟩
  have ha_in : ∀ x ∈ shell n g ph r ε, a x = 36 * eta n g ph r ε x * ‖gt n X.z g c W x‖ ^ 2 := by
    intro x hx; rw [ha]; exact Set.indicator_of_mem hx _
  have ha_out : ∀ x ∉ shell n g ph r ε, a x = 0 := by
    intro x hx; rw [ha]; exact Set.indicator_of_notMem hx _
  have hb_in : ∀ x, ev n g ph r x ≤ ε ^ 2 → b x = 2 / eta n g ph r ε x := by
    intro x hx; rw [hb]; exact if_pos hx
  have hb_out : ∀ x, ¬ ev n g ph r x ≤ ε ^ 2 → b x =
      (xx n g ph r ε x + 1) ^ 2 / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x) := by
    intro x hx; rw [hb]; exact if_neg hx
  have ham : Measurable a := by
    rw [ha]
    exact ((measurable_const.mul hetam).mul (hgtm.norm.pow_const 2)).indicator hshm
  have hbm : Measurable b := by
    rw [hb]
    refine Measurable.ite (measurableSet_le hevm measurable_const) (measurable_const.div hetam) ?_
    unfold bfun
    fun_prop
  have ha0 : ∀ x, 0 ≤ a x := by
    intro x
    by_cases hx : x ∈ shell n g ph r ε
    · rw [ha_in x hx]; have := hη1 x; positivity
    · rw [ha_out x hx]
  have hb0 : ∀ x, 0 ≤ b x := by
    intro x
    by_cases hx : ev n g ph r x ≤ ε ^ 2
    · rw [hb_in x hx]; have := hη1 x; positivity
    · rw [hb_out x hx]; have := hη1 x; positivity
  have hb1' : ∀ x, b x ≤ 1 := by
    intro x
    by_cases hx : ev n g ph r x ≤ ε ^ 2
    · rw [hb_in x hx]
      have := hb8 hε50 x hx
      rw [div_le_one (by linarith)]; linarith
    · rw [hb_out x hx]; have := hη1 x
      exact div_le_one_of_le₀ (by linarith) (by positivity)
  have hdF0 : ∀ (x : M) (ξ : Fin n → ℂ), ‖dbarDot n X.z (cutExt n X.z g ph r c W χ ε) x ξ‖ ^ 2 ≤
      a x * (Levi n X.z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
    intro x ξ
    by_cases hx : ev n g ph r x ≤ ε ^ 2
    · have hxm : ev n g ph r x < m := by linarith
      rw [ap_dbar_cutExt n X.z hz g hg ph hph r c W m χ ε hS hW hχs x hxm ξ]
      by_cases hsh : x ∈ shell n g ph r ε
      · rw [ha_in x hsh]
        exact ap_bound _ ε _ _ _ _ hε (hχd _) (hd3 x ξ hx) (by linarith [hη1 x]) (hΘ x ξ)
      · have hlt : ev n g ph r x < ε ^ 2 / 2 := by
          by_contra h; exact hsh ⟨not_lt.1 h, hx⟩
        have hD0 : deriv χ (ev n g ph r x / ε ^ 2) = 0 := by
          have hloc : χ =ᶠ[𝓝 (ev n g ph r x / ε ^ 2)] fun _ => 1 := by
            have h12 : ev n g ph r x / ε ^ 2 < 1 / 2 := by
              rw [div_lt_iff₀ hε2]; linarith
            filter_upwards [Iio_mem_nhds h12] with t ht
            exact hχ1 t (le_of_lt ht)
          rw [hloc.deriv_eq]; simp
        rw [hD0]
        simpa using mul_nonneg (ha0 x) (hΘ x ξ)
    · have h0 := ap_cutExt_zero n X.z g ph r c W χ ε hevc hχ0 hε x (not_le.1 hx)
      have hz0 : dbarDot n X.z (cutExt n X.z g ph r c W χ ε) x ξ = 0 := by
        unfold dbarDot
        apply Finset.sum_eq_zero
        intro i _
        rw [ap_db_congr n X.z hz i _ _ x h0, db_const]
        simp
      rw [hz0]
      simpa using mul_nonneg (ha0 x) (hΘ x ξ)
  have hdΦ : ∀ (x : M) (ξ : Fin n → ℂ), ‖dbarDot n X.z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ ^ 2 ≤
      b x * (Levi n X.z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
    intro x ξ
    by_cases hx : ev n g ph r x ≤ ε ^ 2
    · rw [hb_in x hx]; exact hd2 x ξ hx
    · rw [hb]; simp only [if_neg hx]; exact hd1 x ξ
  obtain ⟨⟨F, hF⟩, hTWb⟩ := hTW X (wgt n g ph ph2 r j δ) (twist n g ph r ε)
    (cutExt n X.z g ph r c W χ ε) a b hψs hΦs hΦb (fun x ξ => hΘ x ξ) hF0s hwint ham hbm ha0 hb0
    hb1' hdF0 hdΦ
  have hbound := hTWb F hF
  refine ⟨F, hF.1, ?_⟩
  have hexp : ∀ x, Real.exp (twist n g ph r ε x - wgt n g ph ph2 r j δ x) =
      Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x := by
    intro x
    have hη0 : 0 < eta n g ph r ε x := by linarith [hη1 x]
    rw [twist, Real.exp_sub, Real.exp_neg, Real.exp_log hη0, Real.exp_neg, div_eq_mul_inv,
      div_eq_mul_inv, mul_comm]
  have hD2 : ∀ x, 2 * eta n g ph r ε x ≤ ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x) := fun x => by linarith [(hb1 x).2.2.2]
  have hPnn : ∀ x, 0 ≤ (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) - ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) := by
    intro x
    have hη0 : 0 < eta n g ph r ε x := by linarith [hη1 x]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.exp_pos _).le
      hη0 (by linarith [hD2 x])) (sq_nonneg _))
  have hQnn : ∀ x, 0 ≤ (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) := fun x =>
    mul_nonneg (sq_nonneg _) (div_nonneg (Real.exp_pos _).le (by linarith [hD2 x, hη1 x]))
  have hPQ : ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) - ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z + ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z ≤
      ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * Real.exp (twist n g ph r ε x - wgt n g ph ph2 r j δ x)) ∂vol n X.z := by
    refine le_trans (le_lintegral_add _ _) (le_of_eq (lintegral_congr fun x => ?_))
    try dsimp only
    rw [← ENNReal.ofReal_add (hPnn x) (hQnn x), hexp x]
    congr 1
    ring
  have hIm : Measurable (fun x => (shell n g ph r ε).indicator (fun x => 72 * ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) x) := by
    refine Measurable.indicator ?_ hshm
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp ((hgtm.norm.pow_const 2).mul
      (Real.continuous_exp.comp hψc.neg).measurable))
  have hTK : ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * Real.exp (twist n g ph r ε x - wgt n g ph ph2 r j δ x)) ∂vol n X.z ≤
      ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) - ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z + 72 * ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)) ∂vol n X.z := by
    refine le_trans hbound ?_
    calc _ ≤ ∫⁻ x, (ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) - ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) + (shell n g ph r ε).indicator (fun x => 72 * ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) x) ∂vol n X.z := by
          refine lintegral_mono fun x => ?_
          try dsimp only
          rw [hexp x]
          have hη0 : 0 < eta n g ph r ε x := by linarith [hη1 x]
          by_cases hx : ev n g ph r x ≤ ε ^ 2
          · have h8 := hb8 hε50 x hx
            rw [hb_in x hx]
            by_cases hsh : x ∈ shell n g ph r ε
            · rw [ha_in x hsh, Set.indicator_of_mem hsh]
              have e2 : 2 * (36 * eta n g ph r ε x * ‖gt n X.z g c W x‖ ^ 2) * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) =
                  72 * (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)) := by
                field_simp
                try ring
              have hr := ap_pt_in ‖cutExt n X.z g ph r c W χ ε x - F x‖ (Real.exp (-wgt n g ph ph2 r j δ x)) (eta n g ph r ε x) ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x)
                (36 * eta n g ph r ε x * ‖gt n X.z g c W x‖ ^ 2) (72 * (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)))
                (norm_nonneg _) (Real.exp_pos _).le h8 (hD2 x) (by positivity) (le_of_eq e2)
              calc _ ≤ ENNReal.ofReal ((‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) - ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) + 72 * (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) :=
                    ENNReal.ofReal_le_ofReal hr
                _ = _ := by
                    rw [ENNReal.ofReal_add (hPnn x) (by positivity), ENNReal.ofReal_mul (by norm_num)]
                    simp
            · rw [ha_out x hsh, Set.indicator_of_notMem hsh, add_zero]
              apply ENNReal.ofReal_le_ofReal
              have hr := ap_pt_in ‖cutExt n X.z g ph r c W χ ε x - F x‖ (Real.exp (-wgt n g ph ph2 r j δ x)) (eta n g ph r ε x) ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x) 0 0
                (norm_nonneg _) (Real.exp_pos _).le h8 (hD2 x) le_rfl (by simp)
              linarith
          · have hsh : x ∉ shell n g ph r ε := fun h => hx h.2
            rw [hb_out x hx, ha_out x hsh, Set.indicator_of_notMem hsh, add_zero,
              ap_pt_out _ _ _ _ hη0]
      _ = ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) - ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z + ∫⁻ x, (shell n g ph r ε).indicator (fun x => 72 * ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) x ∂vol n X.z :=
          lintegral_add_right _ hIm
      _ = _ := by
          rw [lintegral_indicator hshm, lintegral_const_mul' _ _ (by simp)]
  have hFc : Continuous F := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hF.1)
  have hT_fin : ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * Real.exp (twist n g ph r ε x - wgt n g ph ph2 r j δ x)) ∂vol n X.z < ⊤ := by
    have hm1 : Measurable (fun x => 2 * ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) :=
      measurable_const.mul (ENNReal.measurable_ofReal.comp
        ((hF0c.norm.pow 2).mul (Real.continuous_exp.comp hψc.neg)).measurable)
    calc _ ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)) +
          2 * ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) ∂vol n X.z := by
          refine lintegral_mono fun x => ?_
          try dsimp only
          rw [hexp x]
          have hle : ‖cutExt n X.z g ph r c W χ ε x - F x‖ ≤ ‖cutExt n X.z g ph r c W χ ε x‖ + ‖F x‖ := norm_sub_le _ _
          have h1 : ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 ≤ (‖cutExt n X.z g ph r c W χ ε x‖ + ‖F x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
          have h1' : ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 ≤ 2 * ‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 + 2 * ‖F x‖ ^ 2 := by
            nlinarith [sq_nonneg (‖cutExt n X.z g ph r c W χ ε x‖ - ‖F x‖)]
          have hEη : Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x ≤ Real.exp (-wgt n g ph ph2 r j δ x) := div_le_self (Real.exp_pos _).le (hη1 x)
          have hE0 : 0 ≤ Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x := div_nonneg (Real.exp_pos _).le (by linarith [hη1 x])
          have h2 : ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * (Real.exp (-wgt n g ph ph2 r j δ x) / eta n g ph r ε x) ≤
              2 * (‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)) + 2 * (‖F x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)) := by
            calc _ ≤ ‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x) := mul_le_mul_of_nonneg_left hEη (sq_nonneg _)
              _ ≤ (2 * ‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 + 2 * ‖F x‖ ^ 2) * Real.exp (-wgt n g ph ph2 r j δ x) :=
                  mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
              _ = _ := by ring
          calc _ ≤ ENNReal.ofReal (2 * (‖cutExt n X.z g ph r c W χ ε x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x)) + 2 * (‖F x‖ ^ 2 * Real.exp (-wgt n g ph ph2 r j δ x))) :=
                ENNReal.ofReal_le_ofReal h2
            _ = _ := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
                  ENNReal.ofReal_mul (by norm_num)]
                simp
      _ = 2 * wint n X.z (cutExt n X.z g ph r c W χ ε) (wgt n g ph ph2 r j δ) + 2 * wint n X.z F (wgt n g ph ph2 r j δ) := by
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
          rfl
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hwint,
          ENNReal.mul_lt_top (by simp) hF.2.1⟩
  have hPT := le_trans le_self_add hPQ
  have hPne := ne_top_of_le_ne_top hT_fin.ne hPT
  exact (ENNReal.add_le_add_iff_left hPne).1 (hPQ.trans hTK)
end ReciprocityTheory.L2DbarEstimates.I
