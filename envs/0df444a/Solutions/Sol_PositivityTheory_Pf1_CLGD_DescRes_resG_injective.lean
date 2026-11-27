-- Prove2me | solution 1 for PositivityTheory.Pf1.CLGD.DescRes.resG_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:44.834856+00:00
-- url     : https://prove2.me/submissions/aa346890-a6df-459b-8514-c0fb9235fe8e

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
variable {E E' Ω : Type} [Field E] [Field E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω]
namespace PositivityTheory.Pf1.CLGD.DescRes
theorem _root_.solution : Function.Injective (resG E (E' := E') (Ω := Ω)) :=
  AlgEquiv.restrictScalarsHom_injective E
end PositivityTheory.Pf1.CLGD.DescRes
