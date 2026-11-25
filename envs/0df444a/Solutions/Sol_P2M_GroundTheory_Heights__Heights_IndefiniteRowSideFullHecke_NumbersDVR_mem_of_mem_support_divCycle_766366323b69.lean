-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_mem_of_mem_support_divCycle_766366323b69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:02.824171+00:00
-- url     : https://prove2.me/submissions/1969edec-aae1-4ffd-9379-1fa1e8bcbdc6

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W : Ideal (MRingOver R ι)} {s : MRingOver R ι} (h : W ∈ (divCycle P s).support) :
    W.IsPrime ∧ s ∈ W := by
  classical
  have hW : W ∈ divSupp P s := by
    by_contra hn
    apply Finsupp.mem_support_iff.mp h
    simp only [divCycle]
    rw [Finsupp.ofSupportFinite_coe, if_neg hn]
  exact ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
