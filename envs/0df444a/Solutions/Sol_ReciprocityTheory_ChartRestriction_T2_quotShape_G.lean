-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.quotShape_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:23.087816+00:00
-- url     : https://prove2.me/submissions/130420bf-f092-4434-932d-8c7faedac9bd

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
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}
    (hε : IsCyc p K (carry i ε)) (e : ℕ) (he : 0 < e) {M : Type} [AddCommGroup M] [Module O M] (u : M ≃ₗ[O] KO O)
    (ρ : Representation O G M) (h : ∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) :
    QuotShape (HcLC ρ) ⊥ (Module.finrank ℚ_[p] K) := hT2Core.out.shape hK hO hF i hε e he u ρ h
end ReciprocityTheory.ChartRestriction.T2
