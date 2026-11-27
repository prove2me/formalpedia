-- Prove2me | solution 1 for PositivityTheory.Pf1.CLGD.DescRes.WD.res_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:39.727654+00:00
-- url     : https://prove2.me/submissions/2663ded8-5abb-4d04-a409-cf879ac7ef8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_LocalGlobalCompatibility_NormVEqPowResF
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_quotientMk_eq


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
namespace WD
theorem _root_.solution (a : WDRep h V) : WD.res h h' (WD.mk a) = WD.mk (resRep h h' a) := by
  show Quotient.mk _ (⟨_, resRep h h' (WD.std a).2⟩ : Σ n : ℕ, WDRep h' (Fin n → ℂ)) = _
  rw [WD.quotientMk_eq]
  exact WD.sound (iso_resRep h h' (WD.iso_std a).symm)
end WD
end PositivityTheory.Pf1.CLGD.DescRes
