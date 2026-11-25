-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inr_f74ac1b56685
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:27.367734+00:00
-- url     : https://prove2.me/submissions/5f354c96-eb71-4d28-bda1-9f10c59efada

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_alt_3dfd9be9352d

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
theorem _root_.solution {a : ProjField K i} (ha : a ≠ 0) (j : PBlk i ()) :
    scale ha (dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  have h : dualStdModelEmb K i a * dualStdModelEmb K i a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S, scale_alt]
  linear_combination
    (dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i) * h
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
