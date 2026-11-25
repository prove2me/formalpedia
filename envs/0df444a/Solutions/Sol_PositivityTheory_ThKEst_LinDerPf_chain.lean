-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:11.270467+00:00
-- url     : https://prove2.me/submissions/3bd3ed2d-141a-4364-97df-e1bcb1f9cfd0

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
import Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
namespace PositivityTheory.ThKEst.LinDerPf
theorem _root_.solution (f : H → ℂ) : ∀ (m : ℕ) (β : Fin m → Multiplicative ℝ →* H) (_ : ∀ i, Continuous (β i))
    (f' : Fin m → H → ℂ) (_ : ∀ i, Continuous (f' i))
    (_ : ∀ i h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0)
    (p : ℝ → H) (_ : ContinuousAt p 0) (u : Fin m → ℝ → ℝ) (u' : Fin m → ℝ) (_ : ∀ i, HasDerivAt (u i) (u' i) 0)
    (_ : ∀ i, u i 0 = 0) (D : ℂ) (_ : HasDerivAt (fun t => f (p t)) D 0),
    HasDerivAt (fun t => f (p t * (List.ofFn fun i => β i (Multiplicative.ofAdd (u i t))).prod))
      (D + ∑ i, (u' i : ℂ) * f' i (p 0)) 0 := by
  intro m
  induction m with
  | zero =>
    intro β _ f' _ _ p _ u u' _ _ D hD
    simpa using hD
  | succ m ih =>
    intro β hβ f' hf' hd p hp u u' hu hu0 D hD
    have h1 := step (β 0) (hβ 0) f (f' 0) (hf' 0) (hd 0) p hp (u 0) (u' 0) (hu 0) (hu0 0) D hD
    have h2 := ih (fun i => β i.succ) (fun i => hβ _) (fun i => f' i.succ) (fun i => hf' _) (fun i => hd _)
      (fun t => p t * β 0 (Multiplicative.ofAdd (u 0 t)))
      (hp.mul (((hβ 0).comp continuous_ofAdd).continuousAt.comp (hu 0).continuousAt))
      (fun i => u i.succ) (fun i => u' i.succ) (fun i => hu _) (fun i => hu0 _) _ h1
    simp only [hu0, ofAdd_zero, map_one, mul_one] at h2
    simpa only [List.ofFn_succ, List.prod_cons, mul_assoc, Fin.sum_univ_succ, add_assoc] using h2
end PositivityTheory.ThKEst.LinDerPf
