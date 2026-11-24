-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:07.041805+00:00
-- url     : https://prove2.me/submissions/b496f69b-2589-4c1a-a6c8-0a0c4dc90849

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
variable [NumberField K] {i : ℕ}
variable {F : HermLattice K i} {T : Type}
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    dualLatticeCoord b ⟨(), t⟩ = evalForm i (b t : Fin i → K) := by
  rw [dualLatticeCoord, evalForm, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin i) K),
    MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
