-- Prove2me | solution 1 for PositivityTheory.RL.Up.seminorm_succ_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:28:54.977168+00:00
-- url     : https://prove2.me/submissions/a3ae303a-52ae-4f7f-b60a-3aa6da2bc0b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.RL.Up
theorem _root_.solution (k n : ℕ) (g : Sch l) :
    SchwartzMap.seminorm ℂ k (n + 1) g ≤ ∑ i, SchwartzMap.seminorm ℂ k n (dRho (Pi.single (Sum.inl i) 1) g) := by
  refine SchwartzMap.seminorm_le_bound ℂ k (n + 1) g (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun x => ?_
  let L : l → ℂ →L[ℝ] (EuclideanSpace ℝ l →L[ℝ] ℂ) := fun i =>
    ContinuousLinearMap.smulRightL ℝ _ ℂ (EuclideanSpace.proj i)
  have hL : ∀ i, ‖L i‖ ≤ 1 := fun i => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    show ‖(v i) • z‖ ≤ _
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v i) (norm_nonneg _)
  have e : fderiv ℝ g = fun y => ∑ i, (L i ∘ dRho (Pi.single (Sum.inl i) 1) g) y := by
    funext y
    ext v
    have hv : v = ∑ i, v i • (EuclideanSpace.single i 1 : EuclideanSpace ℝ l) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp [L, dRho_single_inl, lineDerivOp_apply_eq_fderiv]
  have hs : ∀ i, ContDiff ℝ ∞ (dRho (Pi.single (Sum.inl i) 1) g : Sch l) := fun i => SchwartzMap.smooth _ ⊤
  rw [← norm_iteratedFDeriv_fderiv, e, iteratedFDeriv_fun_sum_apply (fun i _ =>
    (((L i).contDiff.comp (hs i)).of_le (by exact_mod_cast le_top)).contDiffAt)]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => le_trans ?_ (SchwartzMap.le_seminorm ℂ k n _ x)
  refine mul_le_mul_of_nonneg_left (((L i).norm_iteratedFDeriv_comp_left (hs i).contDiffAt
    (by exact_mod_cast le_top)).trans ?_) (by positivity)
  exact mul_le_of_le_one_left (norm_nonneg _) (hL i)
end PositivityTheory.RL.Up
