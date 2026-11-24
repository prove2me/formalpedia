-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isMultiHomog_C_cab39863dc5a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:57.741881+00:00
-- url     : https://prove2.me/submissions/e9529f21-4312-4dff-a662-0357157c3ca9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution (a : O) : IsMultiHomog (C a : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
