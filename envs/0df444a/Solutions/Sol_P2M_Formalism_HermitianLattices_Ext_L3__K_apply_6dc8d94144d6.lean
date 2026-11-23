-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3__K_apply_6dc8d94144d6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:47.513605+00:00
-- url     : https://prove2.me/submissions/bcd62c15-2261-4e77-8d3d-bbf27b30c29b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD

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
theorem _root_.solution (x : K) : ιK w hw d x = algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
    algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) *
      AdjoinRoot.root (polKE d (skewSq w hw)) := rfl
end Formalism.HermitianLattices.Ext.L3
