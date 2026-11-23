-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.unfolding_affine_space_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:52.865212+00:00
-- url     : https://prove2.me/submissions/65789a92-8436-44ab-a53d-6253a890d515

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_eN_eq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_mem_Ufl
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_entry
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_res
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
private theorem xx1_single_eq_inX_of_lt {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : s.1 < n') :
    xx1 xj t (Pi.single s 1) = inX E n c (xj (Pi.single ⟨s.1, hs⟩ 1)) := by
  funext l
  rw [xxw_entry]
  have hnf : ¬ IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
  rw [dif_neg hnf, dif_pos hs]
  simp only [inX, LinearMap.pi_apply]
  by_cases hl : l.1 < n
  · rw [dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply]
  · rw [dif_neg hl, dif_neg hl, LinearMap.zero_apply]
private theorem xx1_single_apply_eq_eN_of_le {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : ¬ s.1 < n') (hj : s.1 - n' < c) :
    ∀ l : Fin (n + c), n + (s.1 - n') ≤ l.1 →
      xx1 xj t (Pi.single s 1) l = eN E (n + c) (n + (s.1 - n')) l := by
  intro l hl
  rw [xxw_entry]
  have hnf : ¬ IsFree n' n c l.1 s.1 := by
    rintro ⟨-, h | ⟨-, h⟩⟩
    · omega
    · omega
  rw [dif_neg hnf, dif_neg hs]
  rfl
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
theorem _root_.solution : XXP := by
  intro E _ n' c' n c ρ hρ xj t
  obtain ⟨h1, -⟩ := hρ
  apply (Pi.basisFun E (Fin (n' + c'))).ext
  intro s
  rw [Pi.basisFun_apply]
  funext l
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [xxw_entry]
  by_cases hf : IsFree n' n c l.1 s.1
  · rw [dif_pos hf]
    have hs : ¬ s.1 < n' := by have := hf.1; omega
    rw [xx1_single_eq_of_not_lt xj t s hs]
    show _ = (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t) (eN E (n' + c') s.1) l
    rw [xxw_eN_eq]
    rfl
  · rw [dif_neg hf]
    by_cases hs : s.1 < n'
    · rw [dif_pos hs, xx1_single_eq_inX_of_lt xj t s hs, xxw_res h1]
      simp only [inX, LinearMap.pi_apply]
      by_cases hl : l.1 < n
      · rw [dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply,
          LinearMap.comp_apply]
      · rw [dif_neg hl, dif_neg hl, LinearMap.zero_apply]
    · rw [dif_neg hs]
      have hj : s.1 - n' < c := by
        by_contra hj
        apply hf
        refine ⟨by omega, ?_⟩
        by_cases hjc : s.1 - n' = c
        · exact Or.inl hjc
        · exact Or.inr ⟨by omega, by have := l.isLt; omega⟩
      by_cases hj0 : s.1 - n' = 0
      · have hcol : xx1 xj t (Pi.single s 1) = eN E (n + c) n := by
          funext l'
          rw [xxw_entry]
          have hnf : ¬ IsFree n' n c l'.1 s.1 := by
            rintro ⟨-, h | ⟨h, -⟩⟩ <;> omega
          rw [dif_neg hnf, dif_neg hs, hj0, add_zero]
          rfl
        rw [hcol, h1.2.1, hj0, add_zero]
        rfl
      · have hl : n + (s.1 - n') ≤ l.1 := by
          by_contra hl
          apply hf
          exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
        have hu : xx1 xj t (Pi.single s 1) - eN E (n + c) (n + (s.1 - n')) ∈ Ufl E n c (s.1 - n') := by
          rw [xxw_mem_Ufl]
          intro l' hl'
          rw [Pi.sub_apply, xx1_single_apply_eq_eN_of_le xj t s hs hj l' hl', sub_self]
        have hA := h1.1 _ _ hu
        have hB := h1.2.2 (s.1 - n')
        have hC := (Ufl E n c (s.1 - n')).add_mem hA hB
        rw [map_sub, xxw_mem_Ufl] at hC
        have h3 := hC l hl
        simp only [Pi.add_apply, Pi.sub_apply] at h3
        have e2 : ρ (xx1 xj t (Pi.single s 1)) l = eN E (n + c) (n + (s.1 - n')) l := by
          linear_combination h3
        rw [e2]
        rfl
end PI.TwistedEisensteinNonvanishing.W
