-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qj10_dc_aeval_intertwine__1507d8f6c6fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:17.947826+00:00
-- url     : https://prove2.me/submissions/f8edf023-b105-4162-9cc9-c02bdceebf28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DcAevalIntertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qj10.dc_aeval_intertwine
theorem _root_.solution.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p y
  have hpow : ∀ (n : ℕ) (x : Y), ψ ((A ^ n) x) = (B ^ n) (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end UpperTheory.Reformulated.B.Qj10.dc_aeval_intertwine
