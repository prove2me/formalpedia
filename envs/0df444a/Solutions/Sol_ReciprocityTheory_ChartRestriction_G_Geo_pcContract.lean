-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.pcContract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:20.025668+00:00
-- url     : https://prove2.me/submissions/8bd75950-9c81-4cc3-939a-724ebd980817

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_Lemmata_GeneralBFactThirdLast_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_map_int_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pC_eq_extC_extQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_horizontal_spec
import Theorems.Thm_ReciprocityTheory_AnForm_R_comap_extC
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
theorem _root_.solution : PCContractStatement := by
  intro K _ ι _ P e hP f hf
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨_, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  rw [pC_eq_extC_extQ] at hf
  have h1 : f ∈ (extC (extQ P)).comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := hf
  rw [← map_int_comp, ← Ideal.comap_comap, comap_extC, hcomap] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.Geo
