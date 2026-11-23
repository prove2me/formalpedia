-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:38.733945+00:00
-- url     : https://prove2.me/submissions/4a4077a3-d820-4792-a375-3df05ae872a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
import Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_algebraMap_cO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution {K : UQ} (B : InvAlg K) (x : K.O) :
    B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A (cO K x) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← algebraMap_cO,
    ← IsScalarTower.algebraMap_apply]
end GlobalTheory.UnitLemma.UnitBase
