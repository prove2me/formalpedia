-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.hasFDerivAt_of_partials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:30.243031+00:00
-- url     : https://prove2.me/submissions/3e5a4329-dc86-4139-bf15-7ecd443c3753

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.UMGS
open Filter Topology Function
namespace PositivityTheory.ThKEst.UMGS
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    ∀ (Φ : (Fin k → ℝ) → V) (D : Fin k → (Fin k → ℝ) → V), (∀ i, Continuous (D i)) →
      (∀ i t, HasDerivAt (fun s => Φ (update t i (t i + s))) (D i t) 0) →
      ∀ t, HasFDerivAt Φ (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t)) t := by
  induction k with
  | zero =>
    intro Φ D _ _ t
    simpa using hasFDerivAt_of_subsingleton (𝕜 := ℝ) Φ t
  | succ k ih =>
    intro Φ D hc hd t
    have hcons : Continuous fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp continuous_snd
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (t 0, Fin.tail t))
      (f := fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u))
      (f₁ := fun s u => (ContinuousLinearMap.id ℝ ℝ).smulRight (D 0 (Fin.cons s u)))
      (f₂ := fun s u => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i.succ (Fin.cons s u)))
      (Eventually.of_forall fun v => by
        have h := hd 0 (Fin.cons v.1 v.2)
        simp only [Fin.update_cons_zero, Fin.cons_zero] at h
        have h0 : HasDerivAt (fun s => Φ (Fin.cons (v.1 + s) v.2)) (D 0 (Fin.cons v.1 v.2)) (v.1 - v.1) := by
          simpa using h
        have h1 := h0.comp_sub_const v.1 v.1
        simp only [add_sub_cancel] at h1
        exact h1.hasFDerivAt)
      (Eventually.of_forall fun v => ih (fun u => Φ (Fin.cons v.1 u)) (fun i u => D i.succ (Fin.cons v.1 u))
        (fun i => (hc i.succ).comp (hcons.comp (continuous_const.prodMk continuous_id)))
        (fun i u => by
          have h := hd i.succ (Fin.cons v.1 u)
          simpa only [Fin.cons_update, Fin.cons_succ] using h) v.2)
      (((ContinuousLinearMap.smulRightL ℝ ℝ V (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
        ((hc 0).comp hcons)).continuousAt)
      ((continuous_finsetSum Finset.univ fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) V (ContinuousLinearMap.proj i)).continuous.comp
          ((hc i.succ).comp hcons)).continuousAt)
    let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ i))
    have h2 := HasFDerivAt.comp (f := e) t key.hasFDerivAt e.hasFDerivAt
    have h3 : (↿fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u)) ∘ e = Φ := by
      funext x
      exact congrArg Φ (Fin.cons_self_tail x)
    rw [h3] at h2
    refine h2.congr_fderiv ?_
    ext1 x
    simp [e, HasUncurry.uncurry, Fin.sum_univ_succ, Fin.cons_self_tail]
end PositivityTheory.ThKEst.UMGS
