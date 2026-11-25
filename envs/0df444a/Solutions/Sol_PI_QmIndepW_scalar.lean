-- Prove2me | solution 1 for PI.QmIndepW.scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:46.732799+00:00
-- url     : https://prove2.me/submissions/ac7475c3-f78a-4291-a796-8467574829f2

import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepPoly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_QmIndep
import Theorems.Thm_PI_QmIndepW_indepC
import Theorems.Thm_PI_QmIndepW_indepPoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex
namespace PI.QmIndepW
theorem _root_.solution (z : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ) (Y Y' : ℂ) (hY : Y' ≠ Y + 1)
    (hz : ∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) * z A B = 0) :
    ∀ A B, z A B = 0 := by
  apply indepPoly Y Y' hY z
  rintro β α ⟨n, rfl⟩
  have h9 := indepC
    ((Y - β) * (Y' - β) * ((Y' + (β + n)) * (Y + (β + n))) * z (0, 0) (0, 0))
    ((Y - β) * (Y' - β) * ((Y' + (β + n) - 1) * z (0, 0) (0, 1) + (Y + (β + n)) * z (0, 0) (1, 0)))
    ((Y - β) * (Y' - β) * z (0, 0) (1, 1))
    (((Y' - β) * z (0, 1) (0, 0) + (Y - β + 1) * z (1, 0) (0, 0)) * ((Y' + (β + n)) * (Y + (β + n))))
    ((Y' - β) * (Y' + (β + n) - 1) * z (0, 1) (0, 1) + (Y' - β) * (Y + (β + n)) * z (0, 1) (1, 0) +
      (Y - β + 1) * (Y' + (β + n) - 1) * z (1, 0) (0, 1) + (Y - β + 1) * (Y + (β + n)) * z (1, 0) (1, 0))
    ((Y' - β) * z (0, 1) (1, 1) + (Y - β + 1) * z (1, 0) (1, 1))
    ((Y' + (β + n)) * (Y + (β + n)) * z (1, 1) (0, 0))
    ((Y' + (β + n) - 1) * z (1, 1) (0, 1) + (Y + (β + n)) * z (1, 1) (1, 0))
    (z (1, 1) (1, 1)) (by
      intro c hc
      have h := hz c hc β n
      have hne : ((‖c‖ : ℂ) ^ (2 * β)) * c ^ n ≠ 0 := by
        refine mul_ne_zero ?_ (zpow_ne_zero n hc)
        rw [Ne, Complex.cpow_eq_zero_iff]
        simp [hc]
      refine (mul_eq_zero.mp ?_).resolve_left hne
      rw [← h]
      simp only [nine, Fintype.sum_prod_type, Fin.sum_univ_two, Prod.mk.injEq, Fin.isValue,
        Fin.val_zero, Fin.val_one, zero_ne_one, one_ne_zero, and_true, and_false, true_and, false_and,
        if_true, if_false, add_zero, zero_add]
      ring)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
end PI.QmIndepW
