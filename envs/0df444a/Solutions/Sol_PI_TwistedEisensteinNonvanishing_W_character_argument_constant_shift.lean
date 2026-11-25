-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.character_argument_constant_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:42.4778+00:00
-- url     : https://prove2.me/submissions/036550b3-fb7f-462c-9dee-2e24517a43da

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_eN_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_mem_Ufl
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_entry
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_step
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_diff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section XX
variable {E : Type} [Field E]
private theorem xx1_single_eq_of_not_lt {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : ¬ s.1 < n') :
    xx1 xj t (Pi.single s 1) = xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t (Pi.single s 1) := by
  funext l
  simp only [xxw_entry, dif_neg hs]
end XX
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : ChArgP := by
  intro E _ n' c' n c ρ hρ xj t
  obtain ⟨h1, -⟩ := hρ
  unfold chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hic : i < c := Finset.mem_range.mp hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  by_cases hs : n' + i + 1 < n' + c'
  · obtain ⟨s, hs_eq⟩ : ∃ s : Fin (n' + c'), s.1 = n' + i + 1 := ⟨⟨_, hs⟩, rfl⟩
    rw [← hs_eq, xxw_eN_eq s]
    have hsn : ¬ s.1 < n' := by omega
    have hu : xx1 xj t (Pi.single s 1) -
        xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ∈ Ufl E n c (i + 1) := by
      rw [xx1_single_eq_of_not_lt xj t s hsn, xxw_diff, xxw_mem_Ufl]
      intro l hl
      have hlt := l.isLt
      rw [dif_neg]
      rintro ⟨-, h | ⟨-, h⟩⟩ <;> omega
    have hstep := xxw_step h1 i _ hu
    rw [xxw_mem_Ufl] at hstep
    have hn : n + i < n + c := by omega
    have h2 := hstep ⟨n + i, hn⟩ le_rfl
    have h0 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ⟨n + i, hn⟩ = 0 := by
      rw [xxw_entry, dif_pos]
      · rfl
      · refine ⟨by omega, Or.inr ⟨by omega, Or.inr ?_⟩⟩
        simp only [Fin.val_mk]
        omega
    simp only [atN, dif_pos hn]
    rw [map_sub, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0] at h2
    linear_combination h2
  · have h0 : eN E (n' + c') (n' + i + 1) = 0 := by
      funext l
      simp only [eN, Pi.zero_apply]
      rw [if_neg]
      have := l.isLt
      omega
    rw [h0]
    simp [atN]
end PI.TwistedEisensteinNonvanishing.W
