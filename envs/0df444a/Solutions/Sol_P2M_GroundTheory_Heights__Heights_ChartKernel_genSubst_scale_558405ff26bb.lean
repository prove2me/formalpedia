-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_genSubst_scale_558405ff26bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:12.593537+00:00
-- url     : https://prove2.me/submissions/df911390-5e96-4057-b94d-42db477a9bc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel

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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {K : Type*} [Field K] {e : ℕ} (ξ s : Fin n → K) (τ : K) (ij : Fin e × Fin n) :
    genSubst ξ (fun m => τ⁻¹ * s m) ij = genSubst (τ⁻¹ • ξ) s ij := by
  simp only [genSubst, Pi.smul_apply, smul_eq_mul, C_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end GroundTheory.Heights₂.Heights.ChartKernel
