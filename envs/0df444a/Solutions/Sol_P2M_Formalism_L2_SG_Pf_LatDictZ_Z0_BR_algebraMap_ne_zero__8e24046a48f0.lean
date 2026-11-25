-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_algebraMap_ne_zero__8e24046a48f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:17.53267+00:00
-- url     : https://prove2.me/submissions/a0433ff7-da06-41b2-950e-508df1487d8f

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_AlgebraMapNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_ne_zero_of_mem_hcompl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR
theorem _root_.solution {p : Ideal (𝓞 E)} (hp : p.IsPrime) {t : 𝓞 E}
    (ht : t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) : algebraMap (𝓞 E) E t ≠ 0 :=
  algebraMap_ne_zero_of_mem_hcompl hp ht
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
