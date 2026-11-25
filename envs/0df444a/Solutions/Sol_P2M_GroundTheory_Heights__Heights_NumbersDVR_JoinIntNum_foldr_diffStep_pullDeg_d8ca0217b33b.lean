-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_foldr_diffStep_pullDeg_d8ca0217b33b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:35.728352+00:00
-- url     : https://prove2.me/submissions/5b2e6e95-3911-40a1-a091-7c3543700e32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution (L : List (K → ℤ)) (h : (K → ℤ) → ℤ)
    (h' : (K ⊕ Unit → ℤ) → ℤ)
    (hh : ∀ m', h' m' = if 0 ≤ m' (.inr ()) then h (fun k => m' (.inl k)) else 0)
    (m' : K ⊕ Unit → ℤ) :
    (L.map (pullDeg (K' := Unit))).foldr diffStep h' m' =
      if 0 ≤ m' (.inr ()) then L.foldr diffStep h (fun k => m' (.inl k)) else 0 := by
  induction L generalizing m' with
  | nil => exact hh m'
  | cons b L ih =>
    simp only [List.map_cons, List.foldr_cons, diffStep]
    rw [ih, ih]
    have h1 : (m' - pullDeg (K' := Unit) b) (.inr ()) = m' (.inr ()) := by
      simp [pullDeg, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]
    have h2 : (fun k => (m' - pullDeg (K' := Unit) b) (.inl k)) =
        (fun k => m' (.inl k)) - b := by
      funext k
      simp [pullDeg, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]
    rw [h1, h2]
    split_ifs <;> simp
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
