-- Prove2me | solution 1 for PI.CompDegEF.ballCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:58:19.220654+00:00
-- url     : https://prove2.me/submissions/f3059d18-3481-47c5-891f-cbc2f39b9f36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
import Theorems.Thm_PI_CompDegEF_mem_integralClosure_iff_mem_ball
import Theorems.Thm_PI_CompDegEF_card_quot_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.CompDegEF
theorem _root_.solution : BallCard := by
  intro l _ K
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let S := integralClosure ℤ_[l] ↥K.1
  let e : ↥(ball K) ≃+* ↥S :=
    { toFun := fun x => ⟨x.1, (mem_integralClosure_iff_mem_ball K x.1).mpr x.2⟩
      invFun := fun y => ⟨y.1, (mem_integralClosure_iff_mem_ball K y.1).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hIJ : Ideal.span {((l : ℕ) : ↥S)} = (Ideal.span {((l : ℕ) : ↥(ball K))}).map e := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e hIJ).toEquiv]
  haveI : Module.Free ℤ_[l] S :=
    IsIntegralClosure.module_free (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)
  haveI : Module.Finite ℤ_[l] S :=
    IsIntegralClosure.finite (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)
  rw [card_quot_l (Module.finBasis ℤ_[l] S),
    IsIntegralClosure.rank (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥K.1) (C := S)]
end PI.CompDegEF
