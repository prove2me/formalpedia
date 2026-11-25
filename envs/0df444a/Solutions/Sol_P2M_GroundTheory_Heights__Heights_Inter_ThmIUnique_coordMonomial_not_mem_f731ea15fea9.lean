-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_coordMonomial_not_mem_f731ea15fea9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:12.878823+00:00
-- url     : https://prove2.me/submissions/7642e0c8-6ad6-4b8e-8f26-0d239bfa0b22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIUnique
theorem _root_.solution {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).mp h
  exact hc k (hP.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.Inter.ThmIUnique
