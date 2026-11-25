-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_degLT_listSum_94fc907d46a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:26.826213+00:00
-- url     : https://prove2.me/submissions/dd7f6d67-0461-4ecb-af3d-93644b71a666

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_degLT_zero_8822dfd84ef9


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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
theorem _root_.solution (h6 : DegLTClosure.Statement) {α : Type*} (n : ℕ)
    (g : α → (K → ℤ) → ℤ) (l : List α) (hl : ∀ a ∈ l, DegLT (g a) n) :
    DegLT (fun m => (l.map fun a => g a m).sum) n := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact degLT_zero n
  | cons a l ih =>
    have e : (fun m => ((a :: l).map fun a => g a m).sum) =
        g a + fun m => (l.map fun a => g a m).sum := by
      funext m
      simp
    rw [e]
    exact (h6 K n _ _ 0 0).1 (hl a (by simp)) (ih fun b hb => hl b (by simp [hb]))
end GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
