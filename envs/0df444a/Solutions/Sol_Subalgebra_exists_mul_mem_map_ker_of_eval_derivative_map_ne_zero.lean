-- Prove2me | solution 1 for Subalgebra.exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/db1fc874-3d73-59e0-9d2b-b260206d9d94

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero

set_option linter.unusedSectionVars false
set_option autoImplicit false

open Polynomial

namespace DedekindKummerSimpleRoot

variable {P K L : Type*} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
  [Field K] [Algebra P K] [IsFractionRing P K]
  [Field L] [Algebra K L] [Algebra P L] [IsScalarTower P K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem exists_aeval_eq_derivative_minpoly_mul {x : L} (hx : Algebra.adjoin K {x} = ⊤) (hPx : IsIntegral P x)
    {y : L} (hy : IsIntegral P y) :
    ∃ f : P[X], aeval x (derivative (minpoly P x)) * y = aeval x f := by
  classical
  have hdual := traceForm_dualSubmodule_adjoin P K hx hPx
  have hy_dual : y ∈ (Algebra.traceForm K L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin P {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    have hz' : IsIntegral P z := by
      have hle : Algebra.adjoin P {x} ≤ integralClosure P L := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        exact hPx
      exact hle hz
    have htr : IsIntegral P (Algebra.trace K L (y * z)) := Algebra.isIntegral_trace (hy.mul hz')
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := K)).mp htr
    rw [Algebra.traceForm_apply, Submodule.mem_one]
    exact ⟨a, ha⟩
  rw [hdual, Submodule.mem_smul_pointwise_iff_exists] at hy_dual
  obtain ⟨n, hn, rfl⟩ := hy_dual
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hn
  obtain ⟨f, rfl⟩ := hn
  refine ⟨f, ?_⟩
  have hne : aeval x (derivative (minpoly K x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K x).aeval_derivative_ne_zero (minpoly.aeval K x)
  have hmin : minpoly K x = (minpoly P x).map (algebraMap P K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hPx
  have hder : aeval x (derivative (minpoly P x)) = aeval x (derivative (minpoly K x)) := by
    rw [hmin, derivative_map, aeval_map_algebraMap]
  rw [hder, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rfl

theorem exists_aeval_eq_derivative_mul {x : L} (hx : Algebra.adjoin K {x} = ⊤)
    {g : P[X]} (hg : g.Monic) (hgx : aeval x g = 0) {y : L} (hy : IsIntegral P y) :
    ∃ f : P[X], aeval x (derivative g) * y = aeval x f := by
  have hPx : IsIntegral P x := ⟨g, hg, by rw [← aeval_def]; exact hgx⟩
  obtain ⟨f₀, hf₀⟩ := exists_aeval_eq_derivative_minpoly_mul (P := P) (K := K) hx hPx hy
  haveI : FaithfulSMul P L := (faithfulSMul_iff_algebraMap_injective P L).mpr (by
    rw [IsScalarTower.algebraMap_eq P K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective P K))
  obtain ⟨k, hk⟩ := minpoly.isIntegrallyClosed_dvd hPx hgx
  refine ⟨k * f₀, ?_⟩
  rw [hk, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero, map_mul, ← hf₀]
  ring

theorem aeval_mem_map_of_forall_coeff_mem {D : Type*} [CommRing D] [Algebra P D] (I : Ideal P)
    (t : D) (q : P[X]) (hq : ∀ i, q.coeff i ∈ I) :
    aeval t q ∈ I.map (algebraMap P D) := by
  rw [aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hq i))

theorem map_aeval_eq_eval_map {D κ : Type*} [CommRing D] [Algebra P D] [CommRing κ] (φ : D →+* κ)
    (t : D) (q : P[X]) :
    φ (aeval t q) = (q.map (φ.comp (algebraMap P D))).eval (φ t) := by
  rw [aeval_def, hom_eval₂, eval_map]

variable {κ : Type*} [Field κ]

theorem main (D : Subalgebra P L) (φ : ↥D →+* κ) (hφ : Function.Surjective (φ.comp (algebraMap P ↥D)))
    (t : ↥D) (ht : Algebra.adjoin K {(t : L)} = ⊤)
    (g : P[X]) (hg : g.Monic) (hgt : aeval t g = 0)
    (hsimple : (g.map (φ.comp (algebraMap P ↥D))).derivative.eval (φ t) ≠ 0)
    (c : ↥D) (hcint : IsIntegral P (c : L)) (hc : φ c = 0) :
    ∃ s : ↥D, φ s ≠ 0 ∧
      s * c ∈ (RingHom.ker (φ.comp (algebraMap P ↥D))).map (algebraMap P ↥D) := by
  classical
  have hinj : Function.Injective (algebraMap ↥D L) := Subtype.coe_injective
  set x : L := (t : L) with hxdef
  set ψ : P →+* κ := φ.comp (algebraMap P ↥D) with hψ
  set a : κ := φ t with hadef
  have hgx : aeval x g = 0 := by
    have := congrArg (algebraMap ↥D L) hgt
    rwa [map_zero, ← aeval_algebraMap_apply] at this

  obtain ⟨f, hf⟩ := exists_aeval_eq_derivative_mul (P := P) (K := K) ht hg hgx hcint
  have hfD : aeval t (derivative g) * c = aeval t f := by
    apply hinj
    rw [map_mul, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply]
    exact hf

  set gbar : κ[X] := g.map ψ with hgbar
  have hroot : gbar.eval a = 0 := by
    have h := map_aeval_eq_eval_map φ t g
    rw [hgt, map_zero] at h
    exact h.symm
  have hfbar : (f.map ψ).eval a = 0 := by
    have h := map_aeval_eq_eval_map φ t f
    rw [← hfD, map_mul, hc, mul_zero] at h
    exact h.symm

  set w : κ[X] := gbar /ₘ (X - Polynomial.C a) with hw
  have hgw : (X - Polynomial.C a) * w = gbar := (mul_divByMonic_eq_iff_isRoot).mpr hroot
  set f₁ : κ[X] := f.map ψ /ₘ (X - Polynomial.C a) with hf₁
  have hff₁ : (X - Polynomial.C a) * f₁ = f.map ψ := (mul_divByMonic_eq_iff_isRoot).mpr hfbar
  have hw1 : w.eval a ≠ 0 := by
    have hd : gbar.derivative = w + (X - Polynomial.C a) * derivative w := by
      rw [← hgw, derivative_mul, derivative_X_sub_C, one_mul]
    have h2 : gbar.derivative.eval a = w.eval a := by
      rw [hd, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
    rw [← h2]
    exact hsimple

  obtain ⟨W, hW⟩ := map_surjective ψ hφ w
  obtain ⟨F₁, hF₁⟩ := map_surjective ψ hφ f₁
  set Dp : P[X] := f * W - F₁ * g with hDp
  have hDmap : Dp.map ψ = 0 := by
    rw [hDp, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, hW, hF₁, ← hgbar, ← hff₁, ← hgw]
    ring
  have hcoeff : ∀ i, Dp.coeff i ∈ RingHom.ker ψ := by
    intro i
    rw [RingHom.mem_ker, ← coeff_map, hDmap, coeff_zero]
  have hDt : aeval t Dp = (aeval t (derivative g) * aeval t W) * c := by
    rw [hDp, map_sub, map_mul, map_mul, hgt, mul_zero, sub_zero, ← hfD]
    ring
  refine ⟨aeval t (derivative g) * aeval t W, ?_, ?_⟩
  · rw [map_mul, map_aeval_eq_eval_map φ t (derivative g), map_aeval_eq_eval_map φ t W,
      ← derivative_map, hW]
    exact mul_ne_zero hsimple hw1
  · rw [← hDt]
    exact aeval_mem_map_of_forall_coeff_mem _ t Dp hcoeff

end DedekindKummerSimpleRoot

theorem solution
    {P K L κ : Type*} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [Field K] [Algebra P K] [IsFractionRing P K]
    [Field L] [Algebra K L] [Algebra P L] [IsScalarTower P K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Field κ]
    (D : Subalgebra P L) (φ : ↥D →+* κ) (hφ : Function.Surjective (φ.comp (algebraMap P ↥D)))
    (t : ↥D) (ht : Algebra.adjoin K {(t : L)} = ⊤)
    (g : Polynomial P) (hg : g.Monic) (hgt : Polynomial.aeval t g = 0)
    (hsimple : ((g.map (φ.comp (algebraMap P ↥D))).derivative).eval (φ t) ≠ 0)
    (c : ↥D) (hcint : IsIntegral P (c : L)) (hc : φ c = 0) :
    ∃ s : ↥D, φ s ≠ 0 ∧
      s * c ∈ (RingHom.ker (φ.comp (algebraMap P ↥D))).map (algebraMap P ↥D) :=
  DedekindKummerSimpleRoot.main D φ hφ t ht g hg hgt hsimple c hcint hc

end S_Subalgebra_exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero
end P2MW
export P2MW.S_Subalgebra_exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero (solution)
