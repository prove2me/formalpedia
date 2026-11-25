-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionSmall_eval_cross_e4a6675d6be6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:16:14.028684+00:00
-- url     : https://prove2.me/submissions/c0d44bc8-a159-453c-ab91-a01a6a97f8b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall

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
    {p q e m : MvPolynomial (Coord n) ℤ} (hpq : s.den * p - s.num * q ∈ P.ideal)
    (hem : s.den * e - s.num * m ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z q = evalCone z p * evalCone z m := by
  have hmul : s.den * (e * q - p * m) ∈ P.ideal := by
    have h := P.ideal.sub_mem (P.ideal.mul_mem_right q hem) (P.ideal.mul_mem_right m hpq)
    convert h using 1
    ring
  have hmem : e * q - p * m ∈ P.ideal :=
    (P.isPrime.mem_or_mem hmul).resolve_left s.den_not_mem
  have h0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul] at h0 ⊢
  exact sub_eq_zero.mp h0
end GroundTheory.Heights₂.Heights.SectionSmall
