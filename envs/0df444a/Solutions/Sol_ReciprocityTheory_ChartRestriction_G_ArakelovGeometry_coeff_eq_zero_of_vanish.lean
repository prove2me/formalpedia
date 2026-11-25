-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.coeff_eq_zero_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:17.842909+00:00
-- url     : https://prove2.me/submissions/a8b1b743-7342-49f7-9561-f81d64c550e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_nilp_coeff_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_eq_zero_of_mem_coordIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_evalT_map_rat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_evalT_map_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : J → Ω} {r : ℕ} {b : Fin r → MvPolynomial J ℚ}
    (hs : LinearIndependent ℚ fun k => aeval x (b k)) {c : Fin r → ℂ}
    (h : ∀ z : J → ℂ, (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) →
      ∑ k, c k * secFun (b k) z = 0) : c = 0 := by
  classical
  set I : Ideal (MvPolynomial J ℂ) := Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) (coordIdeal ℤ x) with hI
  set P : MvPolynomial J ℂ := ∑ k, MvPolynomial.C (c k) * MvPolynomial.map (algebraMap ℚ ℂ) (b k) with hP
  have hPmem : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.mem_zeroLocus_iff] at hz
    have hz' : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      have hf' := hz _ (Ideal.mem_map_of_mem _ hf)
      exact hf'
    have hsum := h z hz'
    change eval z P = 0
    rw [hP, map_sum]
    simpa [secFun] using hsum
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hPmem
  obtain ⟨n, hn⟩ := hPmem
  have hker : I ≤ RingHom.ker (evalT x : MvPolynomial J ℂ →+* ℂ ⊗[ℚ] Ω) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change evalT x (map (Int.castRingHom ℂ) f) = 0
    rw [evalT_map_int, aeval_eq_zero_of_mem_coordIdeal hf, TensorProduct.tmul_zero]
  have hnil : IsNilpotent (evalT x P) := ⟨n, by
    rw [← map_pow]
    exact hker hn⟩
  have hev : evalT x P = ∑ k, c k ⊗ₜ[ℚ] aeval x (b k) := by
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, evalT_map_rat, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp
  rw [hev] at hnil
  exact nilp_coeff_eq_zero hs hnil
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
