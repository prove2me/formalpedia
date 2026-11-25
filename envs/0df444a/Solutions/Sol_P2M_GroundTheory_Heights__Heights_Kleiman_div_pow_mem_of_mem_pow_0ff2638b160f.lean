-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_div_pow_mem_of_mem_pow_0ff2638b160f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:04.481819+00:00
-- url     : https://prove2.me/submissions/02b4d43c-f264-460b-a5e1-cf269c396ad0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {B : Subalgebra k Ω} {T : Set Ω} {s : Ω}
    (hT : ∀ y ∈ T, y / s ∈ B) : ∀ n : ℕ, ∀ y ∈ T ^ n, y / s ^ n ∈ B := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    rw [Set.mem_one.mp hy, pow_zero, div_one]
    exact one_mem B
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy
    rw [pow_succ, mul_div_mul_comm]
    exact mul_mem (ih u hu) (hT v hv)
end GroundTheory.Heights₂.Heights.Kleiman
