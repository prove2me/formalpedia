-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualStdFibreRatios_proof_3d41a8e6dfa0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:59.874281+00:00
-- url     : https://prove2.me/submissions/88a8c65b-912e-4ccf-ae8a-ee9a57876085

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdFibreRatios
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualFibreRatios_nonempty_of_basis_83e6d3c219e3

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial
open StandardDualFibreRatios
namespace GroundTheory.Heights₂.Heights
namespace DualStdFibreRatios
theorem _root_.solution (hTr : GenFibreModelTransport.Statement) (hMod : DualStdGraphModel.Statement)
    (hRk : DualStdModelRank.Statement) (hTc : DualStdModelTransc.Statement) : DualStdFibreRatios.Statement := by
  intro K _ _ i T _ _ b G hi
  obtain ⟨c⟩ := nonempty_of_basis b hi
  let Φ₀ : Subfield (dualStdModelField K i) :=
    Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)))
  have hΦ₀ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Φ₀ := Subfield.fieldRange_subtype _
  obtain ⟨h0, hrk, htr⟩ := hTr Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i))
    (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
    (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) G (dualStdModelField K i)
    (dualStdModelPt b) (hMod K i T b) Φ₀ hΦ₀ T
    (fun t => (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))
    (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)
  obtain ⟨hz, hrk₀⟩ := hRk K i T b Φ₀ hΦ₀ hi c
  refine ⟨c, fun h => hz (h0.mp h), ?_, ?_⟩
  · exact hrk.trans hrk₀
  · exact htr.mpr (hTc K i T b Φ₀ hΦ₀ hi c)
end DualStdFibreRatios
end GroundTheory.Heights₂.Heights
