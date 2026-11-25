-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_exists_prime_mul_eq_of_not_dvd_4251d0fa5e4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:38:39.804417+00:00
-- url     : https://prove2.me/submissions/1ade2422-fca7-4756-9937-f798fb0459a1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralOnModel
import Theorems.Thm_GroundTheory_Arith_Toric_smul_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hab : ¬ b ∣ a) :
    ∃ P : Ideal A, P.IsPrime ∧ ∃ w ∉ P, ∃ c ∈ P, w * b = c * a := by
  classical
  by_cases hb : b = 0
  · refine ⟨⊥, Ideal.isPrime_bot, 1, ?_, 0, (⊥ : Ideal A).zero_mem, by simp [hb]⟩
    rw [Submodule.mem_bot]
    exact one_ne_zero
  let N : Submodule A (A ⧸ Ideal.span {b}) := Submodule.span A {Ideal.Quotient.mk _ a}
  let n₀ : N := ⟨Ideal.Quotient.mk _ a, Submodule.subset_span rfl⟩
  have hn₀ : n₀ ≠ 0 := by
    intro h
    apply hab
    have : Ideal.Quotient.mk (Ideal.span {b}) a = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A n₀ hn₀
  obtain ⟨hPp, ⟨m, hm⟩, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hm
  obtain ⟨y, hy⟩ : ∃ y, y = x * a := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.coe_inj]
    show r • (x • Ideal.Quotient.mk (Ideal.span {b}) a) = 0 ↔ b ∣ r * y
    rw [smul_smul, GroundTheory.Arith.Toric.smul_mk_eq_zero_iff, hy, mul_assoc]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let M : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hMfg : M.FG := (IsNoetherian.noetherian P).map _
    have hM0 : M ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ M := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule M hM0 hMfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    refine ⟨P, hPp, s₀, hs₀, r₀ * x, P.mul_mem_right x hr₀, ?_⟩
    rw [mul_assoc, ← hy, hrs, mul_comm]
end GroundTheory.Heights₂.Heights.FourB
