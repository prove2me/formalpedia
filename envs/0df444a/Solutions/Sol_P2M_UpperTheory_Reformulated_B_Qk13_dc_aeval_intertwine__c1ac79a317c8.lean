-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qk13_dc_aeval_intertwine__c1ac79a317c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:15.384305+00:00
-- url     : https://prove2.me/submissions/63879182-755a-4720-8665-ad0892983af2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DcAevalIntertwineAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine
theorem _root_.solution.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p
  have hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | monomial n a =>
    intro y
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine
