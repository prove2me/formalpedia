-- Prove2me | solution 1 for P2M_Formalism_L2_PjFree_intAll_of__a8f6922f0e5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:11.718878+00:00
-- url     : https://prove2.me/submissions/9044c213-d333-49da-8e40-ed609c0093ea

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Theorems.Thm_Formalism_L2_PjFree_intAll_of
import Theorems.Thm_Formalism_L2_PjFree_reFrame_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace Formalism.L2.PjFree
theorem _root_.solution (hE : IntFrExt Xo c) (hB : FrBaseChg Xo c) (hT : TanLin Xo) (hR : IntRebase Xo c) :
    IntAll Xo c :=
  intAll_of hE hB (reFrame_of hT hR)
end Formalism.L2.PjFree
