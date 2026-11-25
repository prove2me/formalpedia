-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Choice_coordProd_not_mem_bf32af54f2d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:41.96356+00:00
-- url     : https://prove2.me/submissions/76c70a76-eeec-4767-afc5-b11f5c459a39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.Choice
theorem _root_.solution {V : Ideal (MRingOver R ι)} (hV : V.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver R ι) ∉ V) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hc k (hV.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.Inter.Choice
