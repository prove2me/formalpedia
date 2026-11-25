-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mixedDiff_map_ae37bf432065
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:37.428232+00:00
-- url     : https://prove2.me/submissions/1ea69dbe-220c-42f7-90a7-25523e91bce3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_hilbFn_map_c5a78f77fece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_foldr_diffStep_pullDeg_d8ca0217b33b

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
theorem _root_.solution (V : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (m' : K ⊕ Unit → ℤ) :
    mixedDiff (fun j => pullDeg (K' := Unit) (bs j))
        (hilbFn (V.map (rename (liftVar (ι := ι) ptIdx)))) m' =
      if 0 ≤ m' (.inr ()) then mixedDiff bs (hilbFn V) (fun k => m' (.inl k)) else 0 := by
  unfold mixedDiff
  have hl : List.ofFn (fun j => pullDeg (K' := Unit) (bs j)) =
      (List.ofFn bs).map (pullDeg (K' := Unit)) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  exact foldr_diffStep_pullDeg _ _ _ (hilbFn_map V) m'
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
