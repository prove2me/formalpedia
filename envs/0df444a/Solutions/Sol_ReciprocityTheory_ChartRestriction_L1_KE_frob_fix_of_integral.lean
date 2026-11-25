-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.frob_fix_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:14.031926+00:00
-- url     : https://prove2.me/submissions/3b02df9d-7bd0-4de0-af4f-303728736448

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_le_one_of_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_int_le_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_finite_domain_frob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] (l : ℕ)
    (hlp : l.Prime) (hl : ‖(l : K)‖ < 1) (δ : K) (hδ : IsIntegral ℤ δ) :
    ∃ f : ℕ, 0 < f ∧ ‖δ ^ (l ^ f) - δ‖ < 1 := by
  let A : Subalgebra ℤ K := Algebra.adjoin ℤ {δ}
  have hA : ∀ x : A, ‖(x : K)‖ ≤ 1 := fun x =>
    norm_le_one_of_integral norm_int_le_one _ (adjoin_le_integralClosure hδ x.2)
  let I : Ideal A :=
    { carrier := {x | ‖(x : K)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖((c * x : A) : K)‖ < 1
        rw [MulMemClass.coe_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hA c) (norm_nonneg _) hx }
  have hImem : ∀ x : A, x ∈ I ↔ ‖(x : K)‖ < 1 := fun x => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
      rw [hImem] at h1
      simp at h1
    · intro x y hxy
      by_contra hcon
      rw [not_or, hImem, hImem, not_lt, not_lt] at hcon
      rw [hImem, MulMemClass.coe_mul, norm_mul] at hxy
      have := one_le_mul_of_one_le_of_one_le hcon.1 hcon.2
      linarith
  have : Module.Finite ℤ A := Algebra.finite_adjoin_simple_of_isIntegral hδ
  have hl0 : ((l : ℕ) : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) l, Ideal.Quotient.eq_zero_iff_mem, hImem]
    have h2 : (((l : ℕ) : A) : K) = (l : K) := map_natCast A.val l
    rw [h2]
    exact hl
  have htors : Module.IsTorsion ℤ (A ⧸ I) := fun {x} =>
    ⟨⟨(l : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hlp.ne_zero)⟩, by
      change (l : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hl0, zero_mul]⟩
  have : Finite (A ⧸ I) := Module.finite_of_fg_torsion _ htors
  obtain ⟨f, hf, h⟩ := finite_domain_frob (A ⧸ I) l hlp hl0
  refine ⟨f, hf, ?_⟩
  let d : A := ⟨δ, Algebra.self_mem_adjoin_singleton ℤ δ⟩
  have h3 := h (Ideal.Quotient.mk I d)
  rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hImem] at h3
  exact h3
end ReciprocityTheory.ChartRestriction.L1.KE
