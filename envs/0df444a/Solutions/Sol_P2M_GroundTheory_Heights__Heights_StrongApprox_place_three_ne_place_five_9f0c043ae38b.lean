-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_place_three_ne_place_five_9f0c043ae38b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:50.143489+00:00
-- url     : https://prove2.me/submissions/2963316b-51b3-48a3-9e17-20dfa34dfa15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution : v3 ≠ v5 := by
  intro h
  have h1 : Rat.ringOfIntegersEquiv.symm ((3 : ℕ) : ℤ) ∈ v3.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact Ideal.mem_span_singleton_self ((3 : ℕ) : ℤ)
  rw [h] at h1
  change _ ∈ Ideal.comap _ _ at h1
  rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, Ideal.mem_span_singleton] at h1
  norm_num at h1
end GroundTheory.Heights₂.Heights.StrongApprox
