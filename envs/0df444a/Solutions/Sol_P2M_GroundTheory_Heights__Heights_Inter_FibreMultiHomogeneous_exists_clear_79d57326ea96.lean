-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_exists_clear_79d57326ea96
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:44.446662+00:00
-- url     : https://prove2.me/submissions/92645665-252b-4668-8279-b08a254e1de1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LiftZComponent

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W') {τ : Type*}
    (f : MvPolynomial τ G.Φ) : ∃ b : MRing ι, aeval G.x b ≠ 0 ∧
      ∃ F : MvPolynomial τ (MRing ι), C (aeval G.x b) * f = map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    obtain ⟨a, b, hb, rfl⟩ := G.gen c
    refine ⟨b, hb, monomial m a, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp
  | add f g hf hg =>
    obtain ⟨b₁, hb₁, F₁, e₁⟩ := hf
    obtain ⟨b₂, hb₂, F₂, e₂⟩ := hg
    refine ⟨b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, C b₂ * F₁ + C b₁ * F₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e₁, ← e₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring
end GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
