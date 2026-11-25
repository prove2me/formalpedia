-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_eq_of_mem_c6a1a6b1f6e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:09.473801+00:00
-- url     : https://prove2.me/submissions/b83197db-fd94-4717-a2d9-87761cc1a914

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_den_ne_zero_3d31e6ab25c8
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall
namespace GroundTheory.Heights₂.Heights.SectionSmall
theorem _root_.solution {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {e m : MvPolynomial (Coord n) ℤ} (h : s.den * e - s.num * m ∈ P.ideal) :
    P.mkF e = s.toFun * P.mkF m := by
  have hG := mkF_den_ne_zero s
  have h' := (P.mkF_eq_zero_iff _).mpr h
  rw [map_sub, map_mul, map_mul] at h'
  rw [IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hG]
  linear_combination h'
end GroundTheory.Heights₂.Heights.SectionSmall
