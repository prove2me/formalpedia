-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.kill_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:09.851137+00:00
-- url     : https://prove2.me/submissions/21b9c78e-677c-4043-9ce1-1377757019aa

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_KillCoef
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero
import Theorems.Thm_PositivityTheory_ThKEnd_Two_kill_ind


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open MeasureTheory Topology Filter PositivityTheory.ThKEnd.Two
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G}
  {a : G} {lam : Measure X} [IsProbabilityMeasure lam] {φ c : G → ℂ}
namespace PositivityTheory.ThKEnd.Cusp
theorem _root_.solution (hC : Cusp Γ n a) (hn : Continuous n) {e : X → ℂ} (ce : Continuous e) (ne : ∀ x, ‖e x‖ ≤ 1) (b : ℕ → G) {y : ℕ → ℂ}
    (hy : Tendsto (fun i => ‖y i‖) atTop atTop) {m : ℕ} (h : Dat Γ n a lam 0 φ c) (hm : Gr a m φ) {V : Set G} (hV : V ∈ 𝓝 1)
    (H : ∀ z ∈ V, ∀ i, y 0 * ∫ x, e x * φ (n x * (b i * z)) ∂lam = y i * ∫ x, e x * φ (n x * z) ∂lam) :
    ∫ x, e x * φ (n x * 1) ∂lam = 0 := by
  have nb : ∀ {x z M}, ‖z‖ ≤ M → ‖e x * z‖ ≤ M := fun {x z M} h => by
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (ne x)).trans h
  refine kill_ind Measure.haar hC hn (l := 0) (by simp) (fun φ _ => ∀ V ∈ 𝓝 (1 : G), (∀ z ∈ V, ∀ i,
    y 0 * ∫ x, e x * φ (n x * (b i * z)) ∂lam = y i * ∫ x, e x * φ (n x * z) ∂lam) → ∫ x, e x * φ (n x * 1) ∂lam = 0)
    (fun φ c _ ⟨M, hM⟩ V hV H => ?_) (fun φ c h h1 V hV H => ?_) m φ c h hm V hV H
  · by_contra h0
    obtain ⟨i, hi⟩ := ((hy.atTop_mul_const (norm_pos_iff.2 h0)).eventually_gt_atTop (‖y 0‖ * M)).exists
    rw [← norm_mul, ← H 1 (mem_of_mem_nhds hV) i, norm_mul] at hi
    refine hi.not_ge (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    simpa using norm_integral_le_of_norm_le_const (μ := lam) (.of_forall fun x => nb (hM (n x * (b i * 1))))
  · have := h.cont
    let w : G → ℂ := fun g => ∫ x, e x * φ (n x * g) ∂lam
    have cw : Continuous w := continuous_iff_continuousAt.2 fun g => by
      obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds g
      obtain ⟨M, hM⟩ := h.bound hC hK
      exact continuousAt_of_dominated (bound := fun _ => M) (.of_forall fun y => Continuous.aestronglyMeasurable (by fun_prop))
        (eventually_of_mem hx fun y hy => .of_forall fun u => nb (hM u y hy)) (integrable_const M)
        (.of_forall fun u => Continuous.continuousAt (by fun_prop))
    obtain ⟨V', hV', hs⟩ := exists_nhds_one_split hV
    refine Bump.zero Measure.haar w cw 1 fun U hU => ?_
    obtain ⟨η, hη, h2⟩ := h1 _ (inter_mem hU hV')
    have fub : ∀ g, ∫ x, e x * conv Measure.haar η φ (n x * g) ∂lam = conv Measure.haar η w g := fun g => by
      simp only [conv, w, ← integral_mul_const, ← integral_const_mul, mul_assoc]
      refine (integral_integral_swap ?_).symm
      obtain ⟨M, hM⟩ := h.bound hC (hη.cpt.isCompact.image (continuous_const_mul g))
      have := hη.cont
      refine Integrable.mono' ((hη.cont.integrable_of_hasCompactSupport hη.cpt).mul_prod (integrable_const M))
        (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun z => nb ?_)
      by_cases hy : z.1 ∈ tsupport η
      · simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hη.nonneg _)]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hM _ _ ⟨_, hy, rfl⟩) (hη.nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hy]
    refine ⟨η, ⟨hη.cont, hη.cpt, hη.sub.trans Set.inter_subset_left, hη.nonneg, hη.one⟩, ?_⟩
    rw [← fub]
    refine h2 V' hV' fun z hz i => ?_
    rw [fub, fub, conv, conv, ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext u
    by_cases hu : u ∈ tsupport η
    · rw [← mul_assoc, ← mul_assoc, mul_assoc (b i)]
      exact congrArg (· * _) (H _ (hs z hz u (hη.sub hu).2) i)
    · simp [image_eq_zero_of_notMem_tsupport hu]
end PositivityTheory.ThKEnd.Cusp
