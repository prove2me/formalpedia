-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormCycleSmul_proof_835f1c6a3356
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:26.394056+00:00
-- url     : https://prove2.me/submissions/b5ea44a5-d542-4817-8e2e-110e15b97242

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormCycleSmul

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
namespace GroundTheory.Heights₂.Heights
namespace ChowFormCycleSmul
theorem _root_.solution : ChowFormCycleSmul.Statement := by
  intro F _ n k m Z f hZ
  obtain ⟨c, hc, g, hg, hf⟩ := hZ
  refine ⟨c ^ m, pow_ne_zero _ hc, g, fun W hW => hg W (Finsupp.support_smul hW), ?_⟩
  have hsub : (m • Z).support ⊆ Z.support := Finsupp.support_smul
  rw [Finset.prod_subset hsub (fun W _ hW => by rw [Finsupp.notMem_support_iff.mp hW, pow_zero]), hf,
    mul_pow, ← map_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun W _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]
end ChowFormCycleSmul
end GroundTheory.Heights₂.Heights
