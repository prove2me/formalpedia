-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:44.5988+00:00
-- url     : https://prove2.me/submissions/ab5fb892-0a4a-437e-8f4d-33752ea4d338

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {a : ι → ℤ} (s : IntegralSection P a) {c : (k : ι) → Fin (n k + 1)} {d : ι → ℕ}
    {e : MvPolynomial (Coord n) ℤ} (he : IsChartForm P a s.num s.den c d e) :
    P.mkF e = s.toFun * P.mkF (chartMonomial c d) := by
  have h1 := (P.mkF_eq_zero_iff _).mpr he.2
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
  have hden : P.mkF s.den ≠ 0 := fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)
  rw [IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination h1
end GroundTheory.Heights₂.Heights.MonomialMapNorm
