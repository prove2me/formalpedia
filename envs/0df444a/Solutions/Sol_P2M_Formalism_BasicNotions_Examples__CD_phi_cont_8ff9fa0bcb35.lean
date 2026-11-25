-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_phi_cont_8ff9fa0bcb35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:44:30.253362+00:00
-- url     : https://prove2.me/submissions/901f5b71-ca90-4fef-8087-1e2c95e85f73

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_coe_phi_846279105f53
import Theorems.Thm_Formalism_REAL_isInducing_coeMatrix
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_mat_cont_02d5d16c2ef0
import Theorems.Thm_UpperTheory_Reformulated_B_Qk27_isInducing_coeMatrix


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
theorem _root_.solution : Continuous (phi ε e h1 h2) := by
  rw [(isInducing_coeMatrix ε).continuous_iff]
  have h : coeMatrixAlt ε ∘ (phi ε e h1 h2) = fun g => (UpqT.mat g).submatrix e.symm e.symm := by
    funext g
    rw [Function.comp_apply, coe_phi, Matrix.reindex_apply]
  rw [h]
  exact (mat_cont P Q).matrix_submatrix _ _
end Formalism.BasicNotions.Examples₂.CD
