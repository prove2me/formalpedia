-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.dim_le_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:47.098645+00:00
-- url     : https://prove2.me/submissions/16f8bd2e-6bf9-47b4-a792-7b2d5fd448c8

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_map_isPrime
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_map_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_eq_zero_of_aeval_mem
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution (q q' : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] [q'.IsPrime] (hle : q ≤ q')
    (hq : ChZero q) (hq' : ¬ ChZero q') :
    ringKrullDim (MvPolynomial σ ℤ ⧸ q') ≤
      ringKrullDim (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) := by
  classical
  obtain ⟨m, hmq', hm0⟩ : ∃ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ q' ∧ m ≠ 0 := by
    by_contra h
    exact hq' fun m hm => by_contra fun hne => h ⟨m, hm, hne⟩

  have hgen := Ideal.span_singleton_generator (q'.comap (C : ℤ →+* MvPolynomial σ ℤ))
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = q'.comap (C : ℤ →+* MvPolynomial σ ℤ) := ⟨_, hgen⟩
  have hspan : Ideal.span {((g.natAbs : ℕ) : ℤ)} = q'.comap (C : ℤ →+* MvPolynomial σ ℤ) := by
    rw [Int.span_natAbs, hg]
  have hmemC : ∀ n : ℤ, (C n : MvPolynomial σ ℤ) ∈ q' ↔ ((g.natAbs : ℕ) : ℤ) ∣ n := by
    intro n
    rw [← Ideal.mem_span_singleton, hspan]
    rfl
  have hp0 : ((g.natAbs : ℕ) : ℤ) ≠ 0 := by
    intro h
    have := (hmemC m).mp hmq'
    rw [h, zero_dvd_iff] at this
    exact hm0 this
  have hpP : Nat.Prime g.natAbs := by
    have hpr : (Ideal.span {((g.natAbs : ℕ) : ℤ)}).IsPrime := by
      rw [hspan]
      infer_instance
    have := (Ideal.span_singleton_prime hp0).mp hpr
    rw [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] at this
    exact this
  set p := g.natAbs with hpdef
  have : Fact p.Prime := ⟨hpP⟩

  have : CharP (MvPolynomial σ ℤ ⧸ q') p := ⟨fun n => by
    rw [← map_natCast (Ideal.Quotient.mk q'), Ideal.Quotient.eq_zero_iff_mem,
      ← map_natCast (C : ℤ →+* MvPolynomial σ ℤ), hmemC, Int.natCast_dvd_natCast]⟩
  let : Algebra (ZMod p) (MvPolynomial σ ℤ ⧸ q') := ZMod.algebra _ p
  have : Algebra.FiniteType ℤ (MvPolynomial σ ℤ ⧸ q') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q') (Ideal.Quotient.mkₐ_surjective ℤ q')
  have : Algebra.FiniteType (ZMod p) (MvPolynomial σ ℤ ⧸ q') :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) _
  obtain ⟨d, hdB, htrB⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MvPolynomial σ ℤ ⧸ q')
  have : FaithfulSMul (ZMod p) (MvPolynomial σ ℤ ⧸ q') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) (MvPolynomial σ ℤ ⧸ q')

  let x : s → MvPolynomial σ ℤ := fun i => (Ideal.Quotient.mk_surjective (i : MvPolynomial σ ℤ ⧸ q')).choose
  have hx : ∀ i, Ideal.Quotient.mk q' (x i) = i := fun i =>
    (Ideal.Quotient.mk_surjective (i : MvPolynomial σ ℤ ⧸ q')).choose_spec
  have hred : ∀ G : MvPolynomial s ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0 := by
    intro G hG
    apply hs.1.eq_zero_of_aeval_eq_zero
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap,
      show ((↑) : s → MvPolynomial σ ℤ ⧸ q') = fun i => Ideal.Quotient.mkₐ ℤ q' (x i) from
        funext fun i => (hx i).symm,
      ← MvPolynomial.comp_aeval_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hle hG
  have hinj := eq_zero_of_aeval_mem q hq p hpP.one_lt x hred

  have := map_isPrime q hq
  have : Algebra.FiniteType ℚ (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ _) (Ideal.Quotient.mkₐ_surjective ℚ _)
  obtain ⟨e, hdC, htrC⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ)
    (A := MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q)
  let φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q :=
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (Int.castRingHom ℚ))).toIntAlgHom
  let y : s → MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q := fun i => φ (x i)
  have hy : AlgebraicIndependent ℚ y := by
    rw [algebraicIndependent_iff]
    intro H hH
    obtain ⟨⟨G, c⟩, hGH⟩ := IsLocalization.surj ((nonZeroDivisors ℤ).map (C (σ := s))) H
    obtain ⟨n, hn, hnc⟩ := Submonoid.mem_map.mp c.2
    have hG0 : G = 0 := by
      apply hinj G
      have h1 := congrArg (MvPolynomial.aeval y) hGH
      rw [map_mul, hH, zero_mul, MvPolynomial.algebraMap_def, MvPolynomial.aeval_map_algebraMap,
        ← MvPolynomial.comp_aeval_apply] at h1
      have h2 : Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom ℚ) (aeval x G)) = 0 := h1.symm
      rw [Ideal.Quotient.eq_zero_iff_mem] at h2
      rw [← comap_map_eq q hq]
      exact h2
    rw [hG0, map_zero] at hGH
    have hc0 : algebraMap (MvPolynomial s ℤ) (MvPolynomial s ℚ) (c : MvPolynomial s ℤ) ≠ 0 := by
      rw [← hnc, MvPolynomial.algebraMap_def, MvPolynomial.map_C, Ne, MvPolynomial.C_eq_zero]
      simpa using nonZeroDivisors.ne_zero hn
    exact (mul_eq_zero.mp hGH).resolve_right hc0
  have hle' := hy.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, htrB, htrC] at hle'
  have hde : d ≤ e := by exact_mod_cast hle'
  rw [hdB, hdC]
  exact_mod_cast hde
end ReciprocityTheory.AnForm.R.IntegerToRational
