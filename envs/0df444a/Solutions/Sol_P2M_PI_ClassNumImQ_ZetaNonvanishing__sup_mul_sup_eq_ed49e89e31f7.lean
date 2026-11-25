-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_mul_sup_eq_ed49e89e31f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:36.424606+00:00
-- url     : https://prove2.me/submissions/5abac700-0361-4d58-b3d8-37048d7d73cf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
namespace PI.ClassNumImQ.ZetaNonvanishing₂
theorem _root_.solution {R : Type*} [CommRing R] (A M N : Ideal R) (hMN : M ⊔ N = ⊤)
    (h : M * N ≤ A) : (A ⊔ M) * (A ⊔ N) = A := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    have r1 : ∀ X : Ideal R, A * X ≤ A := fun X => Ideal.mul_le.mpr fun x hx y _ => Ideal.mul_mem_right y _ hx
    have r2 : ∀ X : Ideal R, X * A ≤ A := fun X => Ideal.mul_le.mpr fun x _ y hy => Ideal.mul_mem_left _ x hy
    exact sup_le (sup_le (r1 _) (r1 _)) (sup_le (r2 _) h)
  · calc A = A * (M ⊔ N) := by rw [hMN, Ideal.mul_top]
      _ = A * M ⊔ A * N := Ideal.mul_sup _ _ _
      _ ≤ (A ⊔ M) * (A ⊔ N) := by
        refine sup_le ?_ (Ideal.mul_mono le_sup_left le_sup_right)
        rw [mul_comm]
        exact Ideal.mul_mono le_sup_right le_sup_left
end PI.ClassNumImQ.ZetaNonvanishing₂
