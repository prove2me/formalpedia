-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_C_toBase_mem_Q_0755be110dc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:26.082802+00:00
-- url     : https://prove2.me/submissions/09630100-9d77-41c2-9d64-4e67a4cbc9ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_eq_217fcd3dcb1f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution {g : MvPolynomial (Fin n) (𝓞 K)} (hg : g ∈ W) : C (toBase I j g) ∈ Q e I j W := by
  rw [Q_eq]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
