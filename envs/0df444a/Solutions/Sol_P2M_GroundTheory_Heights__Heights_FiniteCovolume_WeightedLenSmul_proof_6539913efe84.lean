-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_proof_6539913efe84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:02:01.087173+00:00
-- url     : https://prove2.me/submissions/df60e002-b4a8-4141-9453-7d6145a23d84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightedLenSmul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_invApply_vecAt_smul_74ddd4ed4bc9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WeightedLenSmul_star_smul_dotProduct_mulVec_smul_d6db9280daa8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace WeightedLenSmul
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LenSq.Statement h v) : WeightedLenSmul.Statement h v := by
  intro M g x a
  rw [(h₁ M _).2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [WeightedLenSmul.invApply_vecAt_smul, WeightedLenSmul.star_smul_dotProduct_mulVec_smul,
    Complex.re_ofReal_mul]
end WeightedLenSmul
end GroundTheory.Heights₂.Heights.FiniteCovolume
