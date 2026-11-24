-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_PolyVanishesOnHyperplane_hypotheses_inhabited_2ef4b25abd3a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:23.949721+00:00
-- url     : https://prove2.me/submissions/f004457e-bfdc-4d84-a29f-9c871d271245

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace PolyVanishesOnHyperplane
theorem _root_.solution :
    let a : Fin d1.N := ⟨0, by norm_num⟩
    let b : Fin d1.N := ⟨1, by norm_num⟩
    a ≠ b ∧
      (∃ O : Set (Weight d1), IsOpen O ∧ (O ∩ rootHyperplane d1 0 a b).Nonempty ∧
        ∀ x ∈ O ∩ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0) ∧
      ∀ x ∈ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0 := by
  intro a b
  have hv : ∀ x ∈ rootHyperplane d1 0 a b, eval x (X (0, a) - X (0, b) : LamPoly d1) = 0 := by
    intro x hx
    have hx' : x (0, a) = x (0, b) := hx
    simp [hx']
  refine ⟨by decide, ⟨Set.univ, isOpen_univ, ⟨0, Set.mem_univ _, ?_⟩, fun x hx => hv x hx.2⟩, hv⟩
  show (0 : Weight d1) (0, a) = (0 : Weight d1) (0, b)
  rfl
end PolyVanishesOnHyperplane
end GroundTheory.Heights₂.Heights.TheoremB
