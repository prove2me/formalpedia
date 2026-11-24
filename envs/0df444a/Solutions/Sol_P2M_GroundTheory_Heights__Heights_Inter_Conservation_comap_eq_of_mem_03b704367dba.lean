-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_comap_eq_of_mem_03b704367dba
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:19.111194+00:00
-- url     : https://prove2.me/submissions/159067ac-f876-40df-bbd9-800ec716c5ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.Conservation
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.Conservation
theorem _root_.solution {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    W.comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by
  have hWp : W.IsPrime := hW.1.1.1
  have hpW : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_comap.mpr (hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact (hmax.eq_of_le (Ideal.IsPrime.comap C).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hpW)).symm
end GroundTheory.Heights₂.Heights.Inter.Conservation
