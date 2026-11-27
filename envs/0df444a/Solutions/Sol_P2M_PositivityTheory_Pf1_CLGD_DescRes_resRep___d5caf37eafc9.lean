-- Prove2me | solution 1 for P2M_PositivityTheory_Pf1_CLGD_DescRes_resRep___d5caf37eafc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:48.259967+00:00
-- url     : https://prove2.me/submissions/7fb5463e-1446-4bb6-a80d-f63822f662d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_LocalGlobalCompatibility_NormVEqPowResF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise Topology
open PositivityTheory PositivityTheory.Pf1 PositivityTheory.Pf1.CLGD PositivityTheory.Pf1.CLGD.DescRes
variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace PositivityTheory.Pf1.CLGD.DescRes
theorem _root_.solution (a : WDRep h V) (σ : ↥(Weil h')) : (resRep h h' a).ρ σ = a.ρ (resW h h' σ) := rfl
end PositivityTheory.Pf1.CLGD.DescRes
