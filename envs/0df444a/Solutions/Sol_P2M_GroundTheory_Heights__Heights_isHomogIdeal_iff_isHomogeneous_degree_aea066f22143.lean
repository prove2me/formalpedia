-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:37.181621+00:00
-- url     : https://prove2.me/submissions/a85d7750-314e-4ebf-9e40-40904340163c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    convert h r hr i using 1
    exact decomposition.decompose'_apply r i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d
end GroundTheory.Heights₂.Heights
