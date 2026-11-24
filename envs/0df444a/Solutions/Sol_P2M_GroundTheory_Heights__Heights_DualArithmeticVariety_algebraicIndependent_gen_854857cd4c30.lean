-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:29.75118+00:00
-- url     : https://prove2.me/submissions/aad1f098-5e68-499b-9b32-5c4bfb04444d

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
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution (m : ℕ) :
    AlgebraicIndependent K fun j : Fin m =>
      algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) :=
  (MvPolynomial.algebraicIndependent_X (Fin m) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (ProjField K m))
    (IsFractionRing.injective _ _)
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
