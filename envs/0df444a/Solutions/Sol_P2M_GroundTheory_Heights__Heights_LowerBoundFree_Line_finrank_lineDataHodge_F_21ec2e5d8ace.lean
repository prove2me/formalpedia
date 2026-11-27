-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_finrank_lineDataHodge_F_21ec2e5d8ace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:10:33.713801+00:00
-- url     : https://prove2.me/submissions/a6f0982b-ac1f-4ac3-af23-4e25b658e984

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_DataHodge

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GroundTheory.Heights₂.Heights.LowerBoundFree.Line
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution (II : IntersectionSystem) (hII) :
    Module.finrank Ω ((lineDataHodge II hII).F ()) = 1 := by
  show Module.finrank Ω (Submodule.span Ω ((Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1})) = 1
  have : (Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1} = {Pi.basisFun Ω (Fin 2) 0} := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp hi)]
    · rintro rfl
      exact ⟨0, by simp, rfl⟩
  rw [this, finrank_span_singleton ((Pi.basisFun Ω (Fin 2)).ne_zero 0)]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
