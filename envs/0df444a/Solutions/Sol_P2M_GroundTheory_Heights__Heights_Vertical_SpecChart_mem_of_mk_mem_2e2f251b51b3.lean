-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:17.424183+00:00
-- url     : https://prove2.me/submissions/97c8be30-1f3d-4e8f-9f95-3a8fba88db72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso

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
theorem _root_.solution [W.IsPrime] (hPW : integralModel I ≤ W) {g : MvPolynomial (Fin n) (𝓞 K)}
    (h : Ideal.Quotient.mk (integralModel I) g ∈ W.map (Ideal.Quotient.mk _)) : g ∈ W := by
  have h2 : g ∈ Ideal.comap (Ideal.Quotient.mk (integralModel I)) (W.map (Ideal.Quotient.mk _)) := h
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hPW] at h2
  exact h2
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
