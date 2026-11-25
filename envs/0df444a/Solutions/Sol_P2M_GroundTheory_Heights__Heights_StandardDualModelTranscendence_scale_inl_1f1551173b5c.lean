-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inl_1f1551173b5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:00.123814+00:00
-- url     : https://prove2.me/submissions/b1eb64ed-38ff-4821-8b8f-cd23f8779eed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
variable {L : Type} [Field L]
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K] {F : HermLattice K i} {T : Type} (b : Module.Basis T ℤ (dualLattice F))
namespace GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
theorem _root_.solution {a : ProjField K i} (ha : a ≠ 0) (t : T) :
    scale ha (dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelEmb K i a * dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S]
  ring
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
