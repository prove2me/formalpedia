-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:28.208975+00:00
-- url     : https://prove2.me/submissions/057da72b-34c6-4aa3-b595-dfa75404e54b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
variable [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Bridge
theorem _root_.solution (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  simp only [NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  classical
  set T : Finset (Σ k, ι k) := (Finset.univ : Finset (ι k)).map ⟨Sigma.mk k, sigma_mk_injective⟩
  have h1 : ∑ x ∈ m.support, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_left fun x _ hx => ?_
    rw [Finsupp.notMem_support_iff.mp hx, ite_self]
  have h2 : ∑ x ∈ T, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_right fun x _ hx => ?_
    rw [if_neg]
    rintro rfl
    exact hx (Finset.mem_map.mpr ⟨x.2, Finset.mem_univ _, rfl⟩)
  rw [h1, ← h2, Finset.sum_map]
  simp
end GroundTheory.Heights₂.Heights.Bridge
