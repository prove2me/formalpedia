-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_pow_3b8b2f5fe473
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:31.656313+00:00
-- url     : https://prove2.me/submissions/3ceafce4-90a0-43f4-8d82-5e2f3391f7c2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pi_ne_da2d4218d599
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.MainNotions.G
variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)
local notation "π" => algebraMap W Q ϖ
include hϖ
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (I : Submodule W Q) (h0 : ∃ x ∈ I, x ≠ 0) (N : ℕ)
    (hN : ∀ x ∈ I, π ^ N * x ∈ (algebraMap W Q).range) :
    ∃ n : ℤ, π ^ n ∈ I ∧ ∀ x ∈ I, ∃ a : W, x = algebraMap W Q a * π ^ n := by
  have hp := pi_ne (Q := Q) ϖ hϖ
  let J : Ideal W :=
    { carrier := {a | ∃ x ∈ I, algebraMap W Q a = π ^ N * x}
      add_mem' := by
        rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
        exact ⟨x + y, I.add_mem hx hy, by rw [map_add, h1, h2, mul_add]⟩
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, h1⟩
        exact ⟨c • x, I.smul_mem c hx, by rw [smul_eq_mul, map_mul, h1, Algebra.smul_def]; ring⟩ }
  have hJ : J ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := h0
    obtain ⟨a, ha⟩ := hN x hx
    intro hb
    have : a ∈ J := ⟨x, hx, ha⟩
    rw [hb, Ideal.mem_bot] at this
    rw [this, map_zero] at ha
    exact (mul_ne_zero (pow_ne_zero _ hp) hx0) ha.symm
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ
  refine ⟨(m : ℤ) - N, ?_, fun x hx => ?_⟩
  · have : ϖ ^ m ∈ J := by rw [hm]; exact Ideal.mem_span_singleton_self _
    obtain ⟨x, hx, h1⟩ := this
    have : π ^ ((m : ℤ) - N) = x := by
      rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, ← map_pow, h1]
      field_simp
    rw [this]; exact hx
  · obtain ⟨a, ha⟩ := hN x hx
    have : a ∈ J := ⟨x, hx, ha⟩
    rw [hm, Ideal.mem_span_singleton] at this
    obtain ⟨b, rfl⟩ := this
    refine ⟨b, ?_⟩
    rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
    rw [map_mul, map_pow] at ha
    field_simp
    rw [mul_comm x, ← ha]; ring
end Formalism.BasicNotions.Examples₂.NZ
