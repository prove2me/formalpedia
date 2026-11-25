-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_invol_a7260028bf49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:58.385599+00:00
-- url     : https://prove2.me/submissions/cc8b9457-69e6-4fce-9453-0af1ea87a73e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
attribute [local instance] topAE
attribute [local instance] isModuleTopology_AE
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution (x : AE ℚ GaussQ) : sigA (conj ℚ GaussQ) (sigA (conj ℚ GaussQ) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigA, Algebra.TensorProduct.map_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end GroundTheory.Heights₂.Heights.StrongApprox
