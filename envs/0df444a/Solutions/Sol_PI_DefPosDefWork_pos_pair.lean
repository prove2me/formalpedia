-- Prove2me | solution 1 for PI.DefPosDefWork.pos_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:39.964623+00:00
-- url     : https://prove2.me/submissions/6793cf67-c229-4d84-bb78-063ca6261f63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_SplittingOfExtension
import Theorems.Thm_PI_DefPosDefWork_hform_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder
namespace PI.DefPosDefWork
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (hk : 0 < k) (hD : IsDef σ J)
    (φ : E →+* ℂ) (r : F →+* ℝ) (hr : ∀ a, φ (algebraMap F E a) = (r a : ℂ))
    (s : E) (hs : s ≠ 0) : ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = (c : ℂ) := by
  obtain ⟨i0⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hx1 : (Pi.single i0 s : Fin k → E) ≠ 0 := fun h0 => hs (by simpa using congrFun h0 i0)
  have hx2 : (Pi.single i0 (1 : E) : Fin k → E) ≠ 0 := fun h0 => by
    simpa using congrFun h0 i0
  have hv1 : hform (σ : E →+* E) J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s :=
    hform_single (σ : E →+* E) J i0 s
  have hv2 : hform (σ : E →+* E) J (Pi.single i0 1) (Pi.single i0 1) = J i0 i0 := by
    rw [hform_single]
    simp
  have key : ∀ a b : F, algebraMap F E a = σ s * J i0 i0 * s → algebraMap F E b = J i0 i0 →
      0 < r a * r b → ∃ c : ℝ, 0 < c ∧ φ (σ s) * φ s = c := by
    intro a b ha hb hab
    have hb0 : r b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hab
      exact lt_irrefl _ hab
    refine ⟨r a / r b, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hb0 with h | h
      · exact div_pos_of_neg_of_neg (by nlinarith) h
      · exact div_pos (by nlinarith) h
    · have e1 : (r a : ℂ) = φ (σ s) * (r b : ℂ) * φ s := by
        rw [← hr a, ← hr b, ha, hb, map_mul, map_mul]
      have hb0' : (r b : ℂ) ≠ 0 := by exact_mod_cast hb0
      rw [Complex.ofReal_div, e1, eq_div_iff hb0']
      ring
  rcases hD r with hpos | hneg
  · obtain ⟨a, ha, ha0⟩ := hpos _ hx1
    obtain ⟨b, hb, hb0⟩ := hpos _ hx2
    exact key a b (ha.trans hv1) (hb.trans hv2) (mul_pos ha0 hb0)
  · obtain ⟨a, ha, ha0⟩ := hneg _ hx1
    obtain ⟨b, hb, hb0⟩ := hneg _ hx2
    exact key a b (ha.trans hv1) (hb.trans hv2) (mul_pos_of_neg_of_neg ha0 hb0)
end PI.DefPosDefWork
