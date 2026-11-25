-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_of_neg_548ce6f97ee6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:44:53.130526+00:00
-- url     : https://prove2.me/submissions/49ede8e5-98b1-4c1a-afc4-61e931effe84

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reF_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_imF_star
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gal_KEd_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (d : cmF K) [Fact (Irreducible (polE d))]
  [Fact (Irreducible (polKE d (skewSq w hw)))]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw))
    (h : τ (AdjoinRoot.root (polKE d (skewSq w hw))) = -AdjoinRoot.root (polKE d (skewSq w hw)))
    (x : K) : τ (ιK w hw d x) = ιK w hw d (star x) := by
  rw [ιK_apply, ιK_apply, map_add, map_mul, gal_KEd_algebraMap, gal_KEd_algebraMap, h, reF_star,
    imF_star, map_neg]
  ring
end Formalism.HermitianLattices.Ext.L3
