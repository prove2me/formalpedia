-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_snoc_comp_2c85a72d5335
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:45.839049+00:00
-- url     : https://prove2.me/submissions/7594b716-d0aa-42e6-bb25-e63f6ee920f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution {K₁ K₂ : Type*} (c : K₁ → K₂) {n : ℕ} (L : Fin n → K₂ → ℤ) (A : K₂ → ℤ) :
    (fun j => Fin.snoc (α := fun _ => K₂ → ℤ) L A j ∘ c) =
      Fin.snoc (α := fun _ => K₁ → ℤ) (fun j => L j ∘ c) (A ∘ c) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]
end GroundTheory.Heights₂.Heights.Targets.Relabel
