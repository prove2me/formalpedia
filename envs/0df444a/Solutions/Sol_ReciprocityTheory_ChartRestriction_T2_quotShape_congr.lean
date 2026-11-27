-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.quotShape_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:38:54.640832+00:00
-- url     : https://prove2.me/submissions/05bfb7f7-abd9-4746-946c-1224f4d2aec7

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace ReciprocityTheory.ChartRestriction.T2
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X] [Module O X]
    (Hc F F' : Submodule O X) (d : ℕ) (h : ∀ x ∈ Hc, x ∈ F ↔ x ∈ F') (hs : QuotShape Hc F d) : QuotShape Hc F' d := by
  have e : F.comap Hc.subtype = F'.comap Hc.subtype := Submodule.ext fun x => h x.1 x.2
  unfold QuotShape at hs ⊢
  rw [← e]
  exact hs
end ReciprocityTheory.ChartRestriction.T2
