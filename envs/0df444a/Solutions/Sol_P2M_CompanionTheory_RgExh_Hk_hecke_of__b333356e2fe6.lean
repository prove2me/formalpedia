-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_hecke_of__b333356e2fe6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:02.14982+00:00
-- url     : https://prove2.me/submissions/28c2c9e9-48ed-4a3a-9e41-020797247cf2

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple
import Theorems.Thm_CompanionTheory_RgExh_Hk_backPath
import Theorems.Thm_CompanionTheory_RgExh_Hk_fwdPath

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution (hQ : QdetEq) (hC : StepChar) (_hCH : CayleyHam) (hV : NonVan) (hNS : NonScal) (hB : Back)
    (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) : Hecke := by
  unfold CompanionTheory.RgExh.Hecke
  intro m X χ ss hG hS hH hSc
  have hb := backPath hC hV hNS hB ss X χ hG hH hS.1 hSc
  have hf := fwdPath hQ hC hOS hF hR ss X χ hG hb.2 hS hH
  exact ⟨hb.2, hf.1, hf.2⟩
end CompanionTheory.RgExh.Hk
