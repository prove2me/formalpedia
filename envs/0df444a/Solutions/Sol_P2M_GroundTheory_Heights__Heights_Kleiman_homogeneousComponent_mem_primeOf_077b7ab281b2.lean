-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:01.953973+00:00
-- url     : https://prove2.me/submissions/ca75335e-cda9-489c-b478-6add6023250e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_homogeneousComponent_066005156b15

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f : Poly S N} (hf : f ∈ primeOf x) (d : ℕ) :
    homogeneousComponent d f ∈ primeOf x :=
  coneGen_homogeneousComponent x hf d
end GroundTheory.Heights₂.Heights.Kleiman
