-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.inv_smul_smul_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:57.329811+00:00
-- url     : https://prove2.me/submissions/b57f373c-ef32-4abc-b2b2-e445c9c713d4

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace ReciprocityTheory.ChartRestriction.T2
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] {X : Type} [AddCommGroup X] [Module O X]
    [Module (FractionRing O) X] [IsScalarTower O (FractionRing O) X] {c : O} (hc : c ≠ 0) (y : X) :
    (algebraMap O (FractionRing O) c)⁻¹ • (c • y) = y := by
  have h0 : algebraMap O (FractionRing O) c ≠ 0 := fun h => hc (IsFractionRing.injective O (FractionRing O) (by simpa using h))
  rw [← algebraMap_smul (FractionRing O) c y, smul_smul, inv_mul_cancel₀ h0, one_smul]
end ReciprocityTheory.ChartRestriction.T2
