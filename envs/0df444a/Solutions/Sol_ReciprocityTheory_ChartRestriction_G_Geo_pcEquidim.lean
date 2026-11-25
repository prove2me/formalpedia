-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.pcEquidim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:48:25.932807+00:00
-- url     : https://prove2.me/submissions/8f25476b-fc00-4b27-bb15-e77387335c60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_Lemmata_GeneralBFactThirdLast_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pC_eq_extC_extQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_horizontal_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_of_mem_minimalPrimes_extC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : PCEquidimStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [ringKrullDim_of_mem_minimalPrimes_extC (extQ P) Q hQ]
  apply withBot_eq_of_add_one
  rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]
end ReciprocityTheory.ChartRestriction.G.Geo
