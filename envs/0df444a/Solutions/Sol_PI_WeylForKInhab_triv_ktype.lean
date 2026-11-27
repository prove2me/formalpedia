-- Prove2me | solution 1 for PI.WeylForKInhab.triv_ktype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:44.702646+00:00
-- url     : https://prove2.me/submissions/dda08fac-a422-435e-b5c0-4796073c9732

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Theorems.Thm_PI_WeylForKInhab_diag_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UpqRep Matrix
noncomputable section
open PI PI.WeylForKInhab
namespace PI.WeylForKInhab
theorem _root_.solution {N : ℕ} (ε : Fin N → Bool) : IsKTypeOf ε (triv N) 0 ⊤ := by
  refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, fun S' _ _ => Ideal.eq_bot_or_top S',
    ⟨1, Submodule.mem_top, one_ne_zero, fun θ _ => by simp [triv]⟩, ?_⟩
  intro μ v _ hv hw
  have hμ : μ = 0 := by
    funext b
    by_contra hb
    have hb' : μ b ≠ 0 := hb
    have h := hw (Pi.single b (Real.pi / μ b)) (diag_mem ε _)
    have hs : (∑ a, μ a * (Pi.single b (Real.pi / μ b) : Fin N → ℝ) a) = Real.pi := by
      rw [Finset.sum_eq_single b]
      · rw [Pi.single_eq_same]
        field_simp
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ b) h'
    rw [hs] at h
    have h' : v = 0 := by
      first
        | simpa [triv, Complex.exp_pi_mul_I] using h
        | (simp [triv, Complex.exp_pi_mul_I] at h
           linear_combination h / 2)
    exact hv h'
  subst hμ
  exact ⟨0, fun a b h => absurd rfl h, by simp⟩
end PI.WeylForKInhab
