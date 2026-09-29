-- Prove2me | solution 1 for ValuationSubring.valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d37f3c1d-7a51-571b-a609-7c5df54c5ed1

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional
set_option autoImplicit false

open NumberField

namespace SolutionAux

private theorem engine (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] :
    ∃ π₀ : A.ValueGroup, 0 < π₀ ∧ ∀ x : AlgebraicClosure ℚ, x ∈ K → x ≠ 0 → ∃ e : ℤ, A.valuation x = π₀ ^ e := by
  classical
  letI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

  set B : ValuationSubring K := A.comap (algebraMap K (AlgebraicClosure ℚ)) with hBdef
  have memB : ∀ y : K, y ∈ B ↔ A.valuation (algebraMap K (AlgebraicClosure ℚ) y) ≤ 1 := fun y =>
    ValuationSubring.mem_comap.trans (A.valuation_le_one_iff _).symm
  have val_one_of_unit : ∀ y : K, y ≠ 0 → y ∈ B → y⁻¹ ∈ B →
      A.valuation (algebraMap K (AlgebraicClosure ℚ) y) = 1 := by
    intro y hy hyB hyiB
    have h1 := (memB y).1 hyB
    have h2 := (memB y⁻¹).1 hyiB
    rw [map_inv₀, map_inv₀] at h2
    have hv0 : A.valuation (algebraMap K (AlgebraicClosure ℚ) y) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero _).2 hy
    refine le_antisymm h1 ?_
    by_contra hlt
    rw [not_le] at hlt
    exact absurd h2 (not_le.2 ((one_lt_inv₀ (pos_iff_ne_zero.2 hv0)).2 hlt))

  have top_case : B = ⊤ → ∃ π₀ : A.ValueGroup, 0 < π₀ ∧ ∀ x : AlgebraicClosure ℚ, x ∈ K → x ≠ 0 →
      ∃ e : ℤ, A.valuation x = π₀ ^ e := by
    intro hB
    refine ⟨1, one_pos, fun x hxK hx0 => ⟨0, ?_⟩⟩
    rw [zpow_zero]
    have hy : (⟨x, hxK⟩ : K) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
    have := val_one_of_unit ⟨x, hxK⟩ hy (hB ▸ ValuationSubring.mem_top _) (hB ▸ ValuationSubring.mem_top _)
    simpa using this
  by_cases hBtop : B = ⊤
  · exact top_case hBtop

  have hOK : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ B := by
    intro a
    rw [hBdef, ValuationSubring.mem_comap]

    have hint : IsIntegral A.valuation.integer (algebraMap K (AlgebraicClosure ℚ) (algebraMap (𝓞 K) K a)) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map_of_comp_eq (algebraMap ℤ A.valuation.integer)
        (algebraMap K (AlgebraicClosure ℚ)) (Subsingleton.elim _ _)
    rw [← A.valuation_le_one_iff]
    exact (Valuation.integer.integers A.valuation).isIntegral_iff_v_le_one.1 hint

  let f : 𝓞 K →+* B := (algebraMap (𝓞 K) K).codRestrict B hOK
  have hf : ∀ a : 𝓞 K, ((f a : B) : K) = algebraMap (𝓞 K) K a := fun a => rfl
  let 𝔭 : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal B).comap f
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.IsPrime.comap f
  have h𝔭 : 𝔭 ≠ ⊥ := by
    intro h𝔭bot
    apply hBtop
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbunit : IsUnit (f b) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have : b ∈ 𝔭 := hmem
      rw [h𝔭bot, Ideal.mem_bot] at this
      exact hb0 this
    rw [← B.valuation_le_one_iff, map_div₀]
    have hvb : B.valuation (algebraMap (𝓞 K) K b) = 1 := by
      have := (B.valuation_eq_one_iff (f b)).1 hbunit
      simpa [hf] using this
    rw [hvb, div_one, B.valuation_le_one_iff]
    exact hOK a

  let R := Localization.AtPrime 𝔭
  haveI hRdvr : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) h𝔭 R
  letI : Algebra R K := IsLocalization.localizationAlgebraOfSubmonoidLe R K 𝔭.primeCompl
    (nonZeroDivisors (𝓞 K)) 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower (𝓞 K) R K := IsLocalization.localization_isScalarTower_of_submonoid_le R K
    𝔭.primeCompl (nonZeroDivisors (𝓞 K)) 𝔭.primeCompl_le_nonZeroDivisors
  haveI hRfr : IsFractionRing R K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl R K
  have hvs : ∀ s : 𝔭.primeCompl, B.valuation (algebraMap (𝓞 K) K s) = 1 := by
    intro s
    have hunit : IsUnit (f s) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      exact s.2
    have := (B.valuation_eq_one_iff (f s)).1 hunit
    simpa [hf] using this
  have hR : ∀ r : R, algebraMap R K r ∈ B := by
    intro r
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl r
    have hspec := congrArg (algebraMap R K) (IsLocalization.mk'_spec R a s)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
    rw [← B.valuation_le_one_iff]
    have hval := congrArg B.valuation hspec
    rw [map_mul, hvs s, mul_one] at hval
    rw [hval, B.valuation_le_one_iff]
    exact hOK a

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set g : R →+* AlgebraicClosure ℚ := (algebraMap K (AlgebraicClosure ℚ)).comp (algebraMap R K) with hg
  have hunit_val : ∀ u : Rˣ, A.valuation (g u) = 1 := by
    intro u
    have hu0 : algebraMap R K (u : R) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective R K)]
      exact u.ne_zero
    refine val_one_of_unit _ hu0 (hR _) ?_
    have hmul : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [← eq_inv_of_mul_eq_one_left hmul]
    exact hR _
  have hpow : ∀ r : R, r ≠ 0 → ∃ n : ℕ, A.valuation (g r) = A.valuation (g ϖ) ^ n := by
    intro r hr
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    refine ⟨n, ?_⟩
    rw [map_mul, map_mul, map_pow, map_pow, hunit_val u, one_mul]
  have hϖ0 : (0 : A.ValueGroup) < A.valuation (g ϖ) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff, hg, RingHom.comp_apply, map_ne_zero,
      map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hϖ.ne_zero
  refine ⟨A.valuation (g ϖ), hϖ0, fun x hxK hx0 => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) (⟨x, hxK⟩ : K)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hx0
    have := congrArg (fun y : K => (y : AlgebraicClosure ℚ)) hrs
    simpa using this.symm
  obtain ⟨n, hn⟩ := hpow r hr0
  obtain ⟨m, hm⟩ := hpow s hs0
  refine ⟨(n : ℤ) - m, ?_⟩
  have hx : x = g r / g s := by
    have := congrArg (fun y : K => (y : AlgebraicClosure ℚ)) hrs
    simp only [hg, RingHom.comp_apply] at this ⊢
    rw [← this]
    simp
  rw [hx, map_div₀, hn, hm, zpow_sub₀ hϖ0.ne', zpow_natCast, zpow_natCast]

end SolutionAux

open SolutionAux ValuationSubring in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] {q : ℕ} (hq : 1 < q) (γ : ℕ → A.ValueGroup)
    (hK : ∀ n, ∃ x ∈ K, x ≠ 0 ∧ A.valuation x = γ n)
    (hstep : ∀ n, γ (n + 1) ^ q = γ n) :
    γ 0 = 1 := by
  obtain ⟨π₀, hpos, hE⟩ := engine A K
  have hexp : ∀ n, ∃ e : ℤ, γ n = π₀ ^ e := fun n => by
    obtain ⟨x, hxK, hx0, hx⟩ := hK n
    obtain ⟨e, he⟩ := hE x hxK hx0
    exact ⟨e, hx.symm.trans he⟩
  choose e he using hexp
  by_cases h1 : π₀ = 1
  · rw [he 0, h1, one_zpow]
  · have hstep' : ∀ n, (q : ℤ) * e (n + 1) = e n := fun n => by
      have h := hstep n
      rw [he (n + 1), he n, ← zpow_natCast, ← zpow_mul] at h
      have h' := (zpow_right_inj₀ hpos h1).1 h
      rw [mul_comm] at h'
      exact h'
    have hfac : ∀ n, e 0 = (q : ℤ) ^ n * e n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [ih, ← hstep' n, pow_succ]; ring
    have he0 : e 0 = 0 := by
      by_contra hne
      have hd : ((q : ℤ) ^ (e 0).natAbs) ∣ e 0 := ⟨e (e 0).natAbs, hfac (e 0).natAbs⟩
      have hd' : q ^ (e 0).natAbs ∣ (e 0).natAbs := by
        have h := Int.natAbs_dvd_natAbs.2 hd
        simpa [Int.natAbs_pow] using h
      have hle : q ^ (e 0).natAbs ≤ (e 0).natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hne) hd'
      exact absurd hle (not_le.2 (Nat.lt_pow_self hq))
    rw [he 0, he0, zpow_zero]

end S_ValuationSubring_valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional
end P2MW
export P2MW.S_ValuationSubring_valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional (solution)
