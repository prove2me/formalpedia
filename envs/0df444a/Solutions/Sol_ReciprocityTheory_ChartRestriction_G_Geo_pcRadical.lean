-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.pcRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:15.297117+00:00
-- url     : https://prove2.me/submissions/fccce809-b890-4078-91f2-83db39af2d80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_Lemmata_GeneralBFactThirdLast_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pC_eq_extC_extQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_horizontal_spec
import Theorems.Thm_ReciprocityTheory_AnForm_R_extC_isRadical
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


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
theorem _root_.solution : PCRadicalStatement := by
  intro K _ ι _ P e hP
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, _⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ]
  exact extC_isRadical (extQ P)
end ReciprocityTheory.ChartRestriction.G.Geo
