-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_chartX_eq_zero_bb52bd00c10d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:01.005193+00:00
-- url     : https://prove2.me/submissions/9c489470-651c-4fcd-9b1d-1460c20cd157

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
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {g : MvPolynomial (Fin n) F} (hg : g ∈ I ⊔ Ideal.span {linForm t - 1}) :
    chartX I t e g = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
end GroundTheory.Heights₂.Heights.ChartKernel
