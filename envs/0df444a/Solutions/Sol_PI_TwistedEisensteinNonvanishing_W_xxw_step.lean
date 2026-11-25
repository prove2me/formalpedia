-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.xxw_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:02.534844+00:00
-- url     : https://prove2.me/submissions/8ff01261-e3c7-4f4d-be6f-a7691664d5d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_mem_Ufl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : R1cond E n c ρ) (i : ℕ)
    (v : Fin (n + c) → E) (hv : v ∈ Ufl E n c (i + 1)) : ρ v - v ∈ Ufl E n c i := by
  by_cases hi : n + i < n + c
  · have hw : v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i) ∈ Ufl E n c i := by
      rw [xxw_mem_Ufl] at hv ⊢
      intro l hl
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eN]
      by_cases hli : l.1 = n + i
      · have hl' : l = ⟨n + i, hi⟩ := Fin.ext hli
        rw [if_pos hli, hl']
        simp
      · rw [if_neg hli, mul_zero, sub_zero]
        exact hv l (by omega)
    have h1 := hρ.1 i _ hw
    have h2 := hρ.2.2 i
    have e1 : ρ v - v = (ρ (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i)) -
        (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i))) +
        v ⟨n + i, hi⟩ • (ρ (eN E (n + c) (n + i)) - eN E (n + c) (n + i)) := by
      rw [map_sub, map_smul, smul_sub]
      abel
    rw [e1]
    exact (Ufl E n c i).add_mem ((Ufl E n c i).sub_mem h1 hw) ((Ufl E n c i).smul_mem _ h2)
  · rw [xxw_mem_Ufl]
    intro l hl
    have := l.isLt
    omega
end PI.TwistedEisensteinNonvanishing.W
