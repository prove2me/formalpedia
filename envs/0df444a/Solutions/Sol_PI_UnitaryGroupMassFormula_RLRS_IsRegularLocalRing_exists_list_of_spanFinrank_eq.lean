-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_list_of_spanFinrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:50.24406+00:00
-- url     : https://prove2.me/submissions/2d307281-1ce1-46dd-9140-e824b65088b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_ExistsIsRegularOfListEqMaximalIdeal
import Theorems.Thm_PI_UnitaryGroupMassFormula_RLRS_IsRegularLocalRing_isWeaklyRegular_cons_of_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.RLRS
open PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
namespace PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
theorem _root_.solution :
    ∀ (n : ℕ) (A : Type u) [CommRing A] [IsRegularLocalRing A],
      Submodule.spanFinrank (maximalIdeal A) = n →
      ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧ xs.length = n ∧
        IsWeaklyRegular A xs := by
  intro n
  induction n with
  | zero =>
    intro A _ _ h
    refine ⟨[], ?_, rfl, IsWeaklyRegular.nil A A⟩
    rw [Ideal.ofList_nil]
    exact ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (IsNoetherian.noetherian (maximalIdeal A))).mp h).symm
  | succ n IH =>
    intro A _ _ h
    have hsq : ¬ maximalIdeal A ≤ maximalIdeal A ^ 2 := by
      intro hle
      have hbot := maximalIdeal_eq_bot_of_le_sq A hle
      rw [hbot, Submodule.spanFinrank_bot] at h
      omega
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal A ∧ x ∉ maximalIdeal A ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have hreg : IsRegularLocalRing (A ⧸ Ideal.span ({x} : Set A)) :=
      quotient_span_singleton hx hx2
    have hdim := spanFinrank_quotient_eq_and_ringKrullDim_add_one A hx hx2
    have hn : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = n := by
      have h3 : ((Submodule.spanFinrank (maximalIdeal A) : ℕ) : WithBot ℕ∞) = ringKrullDim A :=
        _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
      have h2 := hdim.2
      rw [← hdim.1, ← h3, h] at h2
      have h4 : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) + 1
          = n + 1 := by exact_mod_cast h2
      omega
    obtain ⟨ys', hys'1, hys'2, hys'3⟩ := IH (A ⧸ Ideal.span ({x} : Set A)) hn
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) :=
      Ideal.Quotient.mk_surjective
    have hmap : (ys'.map (Function.surjInv hsurj)).map
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) = ys' := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id ys']
      apply List.map_congr_left
      intro a _
      exact Function.surjInv_eq hsurj a
    generalize hL : ys'.map (Function.surjInv hsurj) = L at hmap
    have hcomap : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({x} : Set A)))
        (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = maximalIdeal A := by
      have hmax := Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) hsurj
        (K := maximalIdeal (A ⧸ Ideal.span ({x} : Set A)))
      exact IsLocalRing.eq_maximalIdeal hmax
    have hofl : Ideal.ofList (x :: L) = maximalIdeal A := by
      rw [← hcomap, ← hys'1, ← hmap, ← Ideal.map_ofList,
        Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        Ideal.ofList_cons, sup_comm]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx2 (zero_mem _)
    have hxreg : IsSMulRegular A x := fun a b hab => mul_left_cancel₀ hx0 hab
    refine ⟨x :: L, hofl, by rw [← hL]; simp [hys'2], ?_⟩
    refine isWeaklyRegular_cons_of_quotient hxreg _ ?_
    rw [hmap]
    exact hys'3
end PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
