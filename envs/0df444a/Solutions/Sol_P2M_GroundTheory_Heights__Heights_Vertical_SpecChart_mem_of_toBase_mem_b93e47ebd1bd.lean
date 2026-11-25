-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toBase_mem_b93e47ebd1bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:30.239242+00:00
-- url     : https://prove2.me/submissions/86dbf5df-4548-4e0b-aeef-c64831bb86b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_map_mk_isPrime_117a21e5f9cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_disjoint_powers_8cdf492256f5

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
theorem _root_.solution [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : toBase I j g ∈ Wb I j W) : g ∈ W := by
  have := map_mk_isPrime hPW
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers _) (Base I j) this
    (disjoint_powers j hPW hXj)
  apply mem_of_mk_mem hPW
  rw [← h2]
  exact h
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
