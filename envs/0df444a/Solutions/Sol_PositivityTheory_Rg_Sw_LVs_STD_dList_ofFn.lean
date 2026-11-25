-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.dList_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:26.35696+00:00
-- url     : https://prove2.me/submissions/b85b4c0c-76b6-443d-82e2-b96ff6c1e78a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_dc_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution {r : ℝ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hG : ContDiffOn ℂ ∞ G (Metric.ball 0 r)) :
    ∀ (k : ℕ) (m : Fin k → Fin n × Fin n) (x : Vr n), herm x ∈ Metric.ball 0 r →
      dList (List.ofFn m) (fun y => G (herm y)) x =
        iteratedFDeriv ℂ k G (herm x) (fun i => Matrix.single (m i).1 (m i).2 1)
  | 0, m, x, _ => by simp [dList]
  | k + 1, m, x, hx => by
    have hU : IsOpen ((hermL n) ⁻¹' Metric.ball 0 r) := Metric.isOpen_ball.preimage (hermL n).continuous
    set V : Fin k → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.single (m i.succ).1 (m i.succ).2 1 with hV
    set Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun H => iteratedFDeriv ℂ k G H V with hΨ
    have hIt : DifferentiableOn ℂ (fun H => iteratedFDeriv ℂ k G H) (Metric.ball 0 r) := by
      have := hG.differentiableOn_iteratedFDerivWithin (m := k) (by exact_mod_cast ENat.natCast_lt_top k)
        Metric.isOpen_ball.uniqueDiffOn
      exact this.congr (fun H hH => (iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball hH).symm)
    have hA : HasFDerivAt (fun H => iteratedFDeriv ℂ k G H)
        (fderiv ℂ (fun H => iteratedFDeriv ℂ k G H) (herm x)) (herm x) :=
      ((hIt _ hx).differentiableAt (Metric.isOpen_ball.mem_nhds hx)).hasFDerivAt
    have hΨ' := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => Matrix (Fin n) (Fin n) ℂ) ℂ V).hasFDerivAt.comp
      (herm x) hA
    have hΨd : DifferentiableAt ℂ Ψ (herm x) := hΨ'.differentiableAt
    have heq : dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y)) =ᶠ[𝓝 x] fun y => Ψ (herm y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact solution hG k (fun i => m i.succ) y hy
    rw [List.ofFn_succ]
    simp only [dList]
    have h1 : dc (m 0) (dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y))) x =
        dc (m 0) (fun y => Ψ (herm y)) x := by
      simp only [dc, heq.fderiv_eq]
    rw [h1, dc_comp hΨd]
    rw [iteratedFDeriv_succ_apply_left, show fderiv ℂ Ψ (herm x) = _ from hΨ'.fderiv]
    rfl
end PositivityTheory.Rg.Sw.LVs.STD
