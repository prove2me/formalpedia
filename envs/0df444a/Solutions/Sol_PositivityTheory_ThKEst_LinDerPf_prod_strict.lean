-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.prod_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:13.072206+00:00
-- url     : https://prove2.me/submissions/e46fb5b2-cfdc-4237-a473-11b328179c50

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA

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
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}
namespace PositivityTheory.ThKEst.LinDerPf
theorem _root_.solution : ∀ (m : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (e : Fin m → V → A)
    (e' : Fin m → V →L[ℝ] A) (_ : ∀ i, HasStrictFDerivAt (e i) (e' i) 0) (_ : ∀ i, e i 0 = 1),
    HasStrictFDerivAt (fun s => (List.ofFn fun i => e i s).prod) (∑ i, e' i) 0 := by
  intro m V _ _
  induction m with
  | zero =>
    intro e e' _ _
    simpa using hasStrictFDerivAt_const (1 : A) (0 : V)
  | succ m ih =>
    intro e e' he h0
    have h1 := (he 0).mul' (ih (fun i => e i.succ) (fun i => e' i.succ) (fun i => he _) (fun i => h0 _))
    have h2 : (List.ofFn fun i : Fin m => e i.succ 0).prod = 1 := by simp [h0]
    simp only [h2] at h1
    simp only [h0, one_smul, MulOpposite.op_one] at h1
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    rw [add_comm (e' 0)]
    exact h1
end PositivityTheory.ThKEst.LinDerPf
