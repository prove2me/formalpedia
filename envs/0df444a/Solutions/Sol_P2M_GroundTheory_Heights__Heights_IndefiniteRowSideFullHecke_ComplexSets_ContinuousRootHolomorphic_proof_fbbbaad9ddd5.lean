-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ContinuousRootHolomorphic_proof_fbbbaad9ddd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:47.118807+00:00
-- url     : https://prove2.me/submissions/abc2a107-a2d3-4927-af96-b6f5b2123b01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousRootHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PContinuousRootHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasDerivAt_eval_cons_14db9463b806

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter
open scoped Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ContinuousRootHolomorphic
theorem _root_.solution : ContinuousRootHolomorphic.Statement := by
  intro k Q O h hO hh hQ y hy hd
  set c := eval (Fin.cons (h y) y : Fin (k + 1) → ℂ) (pderiv 0 Q) with hc
  let f : (Fin k → ℂ) × ℂ → ℂ := fun v => eval (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) Q
  have hfa : AnalyticAt ℂ f (y, h y) := by
    have hi : ∀ i : Fin (k + 1),
        AnalyticAt ℂ (fun v : (Fin k → ℂ) × ℂ => (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) i) (y, h y) := by
      intro i
      cases i using Fin.cases with
      | zero => simpa using analyticAt_snd
      | succ j =>
        have e : (fun v : (Fin k → ℂ) × ℂ => (Fin.cons v.2 v.1 : Fin (k + 1) → ℂ) j.succ) =
            ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) j).comp
              (ContinuousLinearMap.fst ℂ (Fin k → ℂ) ℂ)) := by
          funext v; simp
        rw [e]; exact ContinuousLinearMap.analyticAt _ _
    simpa [f, MvPolynomial.coe_aeval_eq_eval] using AnalyticAt.aeval_mvPolynomial hi Q
  have hf := hfa.hasStrictFDerivAt
  have hderiv : HasDerivAt (fun s => f (y, s)) c (h y) := hasDerivAt_eval_cons y Q (h y)
  have hcomp : HasFDerivAt (fun s => f (y, s))
      (fderiv ℂ f (y, h y) ∘L ContinuousLinearMap.inr ℂ (Fin k → ℂ) ℂ) (h y) :=
    hf.hasFDerivAt.comp (h y) (hasFDerivAt_prodMk_right y (h y))
  set D := fderiv ℂ f (y, h y) ∘L ContinuousLinearMap.inr ℂ (Fin k → ℂ) ℂ with hDdef
  have hD1 : D 1 = c := by
    rw [hcomp.unique hderiv.hasFDerivAt]; simp
  have hDx : ∀ x : ℂ, D x = x * c := fun x => by
    rw [← hD1, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hinv : D.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℂ ℂ) ?_ ?_ <;>
      refine ContinuousLinearMap.ext_ring ?_ <;> simp [hDx, hd]
  have hφ := hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  have hev := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  refine hφ.differentiableAt.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun t => (t, h t)) (𝓝 y) (𝓝 (y, h y)) :=
    (continuousAt_id.prodMk (hh.continuousAt (hO.mem_nhds hy))).tendsto
  filter_upwards [ht.eventually hev, hO.mem_nhds hy] with t ht1 ht2
  exact (ht1.mp (by simp only [f]; rw [hQ t ht2, hQ y hy])).symm
end ContinuousRootHolomorphic
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
