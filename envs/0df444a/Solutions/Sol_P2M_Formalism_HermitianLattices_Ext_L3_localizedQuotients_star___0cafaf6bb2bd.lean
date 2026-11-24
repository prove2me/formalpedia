-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_localizedQuotients_star___0cafaf6bb2bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:16.89279+00:00
-- url     : https://prove2.me/submissions/2312af12-c7d7-4692-a223-5469448faa0d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients
theorem _root_.solution (hF : IsFixF K F) (a : 𝓞 F) :
    star (algebraMap (𝓞 K) K (ι a)) = algebraMap (𝓞 K) K (ι a) :=
  MeanB.star_algebraMap hF _
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
