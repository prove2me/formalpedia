-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_phi_symm_cont_471bef33b37b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:29:58.719371+00:00
-- url     : https://prove2.me/submissions/73582eea-d715-4b25-b83a-81a2800ab20b

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_Formalism_REAL_continuous_coeMatrix


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
theorem _root_.solution : Continuous (phi ε e h1 h2).symm := by
  rw [(mat_inducing P Q).continuous_iff]
  have h : UpqT.mat ∘ (phi ε e h1 h2).symm = fun a => (coeMatrixAlt ε a).submatrix e e := by
    funext a
    rw [Function.comp_apply]
    exact mat_ofMatU _ (symm_mem ε e h1 h2 a)
  rw [h]
  exact (continuous_coeMatrix ε).matrix_submatrix _ _
end Formalism.BasicNotions.Examples₂.CD
