-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionSmall_den_mul_sub_mem_b5370e9419ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:16:10.182889+00:00
-- url     : https://prove2.me/submissions/24163a4b-6a58-48b8-8ba0-c07bb5e233a6

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
    {p q : MvPolynomial (Coord n) ℤ} (h : P.mkF p = s.toFun * P.mkF q) :
    s.den * p - s.num * q ∈ P.ideal := by
  have hG := mkF_den_ne_zero s
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h, IntegralSection.toFun]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.SectionSmall
