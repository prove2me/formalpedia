-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_preimage_ball_8484a5535331
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:14.326493+00:00
-- url     : https://prove2.me/submissions/9e6c0b65-3c36-4f19-b7ae-1015bea000f6

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (R : ℝ) : (phi ε e h1 h2) ⁻¹' {a | hsG a ≤ R} = TR P Q R := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, TR]
  have h : hsG (phi ε e h1 h2 g) = ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2 := by
    show hs (coeMatrixAlt ε (phi ε e h1 h2 g)) = _
    rw [coe_phi, hs]
    refine (Fintype.sum_equiv e.symm _ _ fun i => ?_)
    exact Fintype.sum_equiv e.symm _ _ fun j => by simp [Matrix.reindex_apply]
  rw [h]
end Formalism.BasicNotions.Examples₂.CD
