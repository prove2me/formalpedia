-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:33:59.538521+00:00
-- url     : https://prove2.me/submissions/fd458189-8fd2-43c2-95d3-d0b074688d61

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    (lpsOriginalLevelPhasePrime N hN p hp).comap
      (algebraMap ℤ (lpsOriginalLevelPhaseRing N)) =
        RingHom.ker (Int.castRingHom (ZMod p)) :=
  (lpsOriginalLevelPhaseRing_maximalOverPrime N hN p hp).choose_spec.2
end QEC.Coding.TannerLiftedProduct
