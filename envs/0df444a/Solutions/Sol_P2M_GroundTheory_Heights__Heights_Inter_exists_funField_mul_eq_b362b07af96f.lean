-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_exists_funField_mul_eq_b362b07af96f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:50.22336+00:00
-- url     : https://prove2.me/submissions/8392f63d-367d-48d0-a601-3dbcac0abc1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} [P.IsPrime] {f g : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) := by
  have hv : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  exact ⟨⟨IsLocalization.mk' _ (Ideal.Quotient.mk P f) ⟨_, hv⟩,
    Subring.subset_closure ⟨f, g, a, hv, hf, hg, rfl⟩⟩, IsLocalization.mk'_spec _ _ _⟩
end GroundTheory.Heights₂.Heights.Inter
