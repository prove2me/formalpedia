-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasDerivAt_eval_cons_14db9463b806
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:47.488129+00:00
-- url     : https://prove2.me/submissions/df0a65b4-2579-4bb5-8afc-898d5fc71cf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousRootHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PContinuousRootHolomorphic

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
theorem _root_.solution {k : ℕ} (y : Fin k → ℂ) (P : MvPolynomial (Fin (k + 1)) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) P)
      (eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 P)) s := by
  apply P.induction_on (fun a => ?_) (fun p q hp hq => ?_) fun p i hp => ?_
  · simpa using hasDerivAt_const s a
  · simp only [map_add]
    exact hp.add hq
  · cases i using Fin.cases with
    | zero =>
      have h0 := hp.mul (hasDerivAt_id s)
      have e1 : (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) (p * X 0)) =
          fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) p * id s := by
        funext x; simp
      have e2 : eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 (p * X 0)) =
          eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 p) * id s +
            eval (Fin.cons s y : Fin (k + 1) → ℂ) p * 1 := by
        simp [Derivation.leibniz]; ring
      rw [e1, e2]; exact h0
    | succ j =>
      have h0 := hp.mul (hasDerivAt_const s (y j))
      have e1 : (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) (p * X j.succ)) =
          fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) p * y j := by
        funext x; simp
      have e2 : eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 (p * X j.succ)) =
          eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 p) * y j +
            eval (Fin.cons s y : Fin (k + 1) → ℂ) p * 0 := by
        simp [Derivation.leibniz, pderiv_X_of_ne (Fin.succ_ne_zero j)]; ring
      rw [e1, e2]; exact h0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
