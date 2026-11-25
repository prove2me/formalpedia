-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mul_mem_sup_span_b3608818911e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:02.291026+00:00
-- url     : https://prove2.me/submissions/fff8af24-9b77-47de-b209-0a5b58d85321

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
theorem _root_.solution {P : Ideal (MRing κ)} {f g u v : MRing κ} (huv : u * f - v * g ∈ P) :
    ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
  intro x hx
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
  rw [e]
  exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ huv))
    (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
