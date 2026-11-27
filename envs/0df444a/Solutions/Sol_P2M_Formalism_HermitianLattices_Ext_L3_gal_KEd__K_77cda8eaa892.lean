-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_77cda8eaa892
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:50:54.688866+00:00
-- url     : https://prove2.me/submissions/1bfadf3a-5f90-437f-ab27-07d16dc7422d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gal_KEd_algebraMap
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_gal_KEd__K_of_neg_548ce6f97ee6
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_gal_root


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
theorem _root_.solution (τ : KEd d (skewSq w hw) ≃ₐ[Ed d] KEd d (skewSq w hw)) :
    (∀ x : K, τ (ιK w hw d x) = ιK w hw d x) ∨ ∀ x : K, τ (ιK w hw d x) = ιK w hw d (star x) := by
  rcases QuadAdj.gal_root (algebraMap (cmF K) (Ed d) (skewSq w hw)) τ with h | h
  · left
    intro x
    rw [ιK_apply, map_add, map_mul, gal_KEd_algebraMap, gal_KEd_algebraMap, h]
  · right
    exact gal_KEd_ιK_of_neg w hw d τ h
end Formalism.HermitianLattices.Ext.L3
