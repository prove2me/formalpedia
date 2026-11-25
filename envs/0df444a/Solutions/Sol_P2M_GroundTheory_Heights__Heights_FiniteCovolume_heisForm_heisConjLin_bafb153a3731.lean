-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_heisConjLin_bafb153a3731
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:42.345729+00:00
-- url     : https://prove2.me/submissions/94cf864c-57f5-4795-8f25-d8b59e20ff32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisConjLin_apply_aa93a34fa3c4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ (heisConjLin g hg y) (heisConjLin g hg z) = heisForm h v x₀ w₀ y z := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [heisConjLin_apply, heisConjLin_apply, hForm_mulVec_of_unitary _ (archUnitary_at_place g w)]
end GroundTheory.Heights₂.Heights.FiniteCovolume
