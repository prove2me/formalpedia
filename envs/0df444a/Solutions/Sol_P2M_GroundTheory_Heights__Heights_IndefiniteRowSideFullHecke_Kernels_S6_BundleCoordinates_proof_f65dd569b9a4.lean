-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_BundleCoordinates_proof_f65dd569b9a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:35.038925+00:00
-- url     : https://prove2.me/submissions/3990eb92-156f-4ddf-a2c5-4f0d0860985a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RangeInclSaturated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_range_incl_saturated_7cd10a09373f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordDet_full_c35610a5b491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordImage_full_39a2e8bb2bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesDiagGram_full_8ff11ddb230b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesExtendBasis_full_63f55d25134d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesFischer_full_deb5581a4d66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexDet_full_b60a8a3c7864
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexMono_full_6f6f30f807ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexPi_full_33ed3f72d0c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexTrans_full_3ca845fd298c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramChange_full_dcb0a61411bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramDetChange_full_12fe0540b59d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramFischerBound_full_1469f2c017cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramPosDef_full_e43342dbfc82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealIndexPos_full_4f9c5f06aec4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealLatticeFG_full_1aee04d7db78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealStdIndex_full_42daaad5b08f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIsLattice_full_bf47e659fe20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLatticeBasis_full_7e8167254293
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLineDegree_full_c44e0f792b53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProductFormula_full_ff39a65d05f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjIndexLower_full_1df55b623de3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjLattice_full_509886f65659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotDegreeBound_full_f1f9aab9b801
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotGramLog_full_1c29f5d3742d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexLog_full_349909a2722b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexSplit_full_f051c7119c9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndex_full_e73217d08651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdIndexDet_full_f76414530167
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdPi_full_9d1e83483f6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrthogonalLines_full_ff0437c876fb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.BundleCoordinates
theorem _root_.solution (hA : S6.LineCoordinates.Statement)
    (hB : S6.CoordinateDegree.Statement) (hC : S6.QuotientDegreeSplit.Statement)
    (hD : S6.ExtensionDegree.Statement) (hE : S6.SaturatedSpan.Statement) :
    S6.BundleCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho E' E'' Y
  obtain ⟨n, e, a, d, ψ, ha, hd, hc, hψ, hrange, hfin, hline, hmet⟩ := hA K E X L hI hr ho
  obtain ⟨hFG, hspanA⟩ := LinesIdealLatticeFG.full K n a ha
  have hspan : Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ := by
    rw [hrange]; exact hspanA
  have hdeg := hB K E n (diagMetric d) ψ hψ hspan hmet
  refine ⟨n, e, a, d, ha, hd, hc, fun i => ?_, ?_⟩
  ·
    have hu : LinearIndependent K (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K)) :=
      linearIndependent_unique_iff.mpr (by simp)
    have h1 := hdeg (L (e i)) (Fin 1) _ hu (by rw [hline i, hrange, Set.range_const])
    rw [HermitianBundle.normDegree, h1, hrange]
    rfl
  ·
    set G := LinearMap.range Y.incl
    obtain ⟨b, hb, hbmap⟩ := hE K E.carrier n ψ hψ G (range_incl_saturated Y)
    have hGr : Module.finrank (𝓞 K) G = Module.finrank (𝓞 K) E'.carrier :=
      LinearMap.finrank_range_of_inj Y.incl_injective
    have hmk : Module.finrank (𝓞 K) G + E''.rank ⊤ = n := by
      rw [hGr, HermitianBundle.rank, finrank_top, ← hfin, Y.finrank_eq]
    obtain ⟨τ, -, hli⟩ := LinesExtendBasis.full K n _ _ b hb hmk
    refine ⟨_, _, b, fun j => Pi.single (τ j) 1, hli, hmk, rfl, ?_⟩
    have htop : Submodule.span K
        (Set.range (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun, hmk])
    have hE1 := hdeg ⊤ _ (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) hli (by
      rw [Submodule.map_top, htop, Submodule.restrictScalars_top, inf_top_eq])
    have hG1 := hdeg G _ b hb hbmap
    rw [hC K n (idealLattice a) (diagMetric d) hFG hspanA _ _ b _ hli hmk,
      HermitianBundle.normDegree, hD K E' E E'' Y, hE1, hG1, hrange]
    rfl
end S6.BundleCoordinates
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
