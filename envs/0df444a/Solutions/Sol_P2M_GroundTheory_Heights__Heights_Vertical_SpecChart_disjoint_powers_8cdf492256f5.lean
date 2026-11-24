-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_disjoint_powers_8cdf492256f5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:47.86931+00:00
-- url     : https://prove2.me/submissions/a03ca7d2-9a4a-4851-9b79-80281755b8c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3

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
theorem _root_.solution [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) :
    Disjoint (↑(Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))) :
        Set (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I))
      ↑(W.map (Ideal.Quotient.mk (integralModel I))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, rfl⟩ hk
  simp only [SetLike.mem_coe] at hk
  rw [← map_pow] at hk
  exact hXj (Ideal.IsPrime.mem_of_pow_mem ‹_› k (mem_of_mk_mem hPW hk))
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
