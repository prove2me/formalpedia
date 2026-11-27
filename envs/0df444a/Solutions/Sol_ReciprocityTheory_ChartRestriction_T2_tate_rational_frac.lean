-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.tate_rational_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:33.480134+00:00
-- url     : https://prove2.me/submissions/548abeca-50ef-4b47-ac30-cbbd29412814

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
variable [hT2Core : Fact Core]
namespace ReciprocityTheory.ChartRestriction.T2
theorem _root_.solution {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}
    (hD : RealLatG i D) (hi : Function.Injective D.invF)
    [Module (FractionRing O) (H1 D.ρT)] [IsScalarTower O (FractionRing O) (H1 D.ρT)]
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (f : H1 D.ρT' →ₗ[FractionRing O] FractionRing O) :
    ∃ a, ∀ b, fracBilinear ((cupFG D).compr₂ D.invF) a b = f b :=
  hT2Core.out.rat hK hO hF i hD hi (f.restrictScalars O)
end ReciprocityTheory.ChartRestriction.T2
