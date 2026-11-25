-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.eq_zero_of_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:19.798597+00:00
-- url     : https://prove2.me/submissions/846f7cad-d61e-462a-8907-745f55d0addd

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA

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
theorem _root_.solution {ι : Type*} (q : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] (hq : ChZero q)
    (p : ℕ) (hp : 1 < p) (x : ι → MvPolynomial σ ℤ)
    (hred : ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0)
    (G : MvPolynomial ι ℤ) (hG : aeval x G ∈ q) : G = 0 := by
  have : NeZero p := ⟨by omega⟩
  have hp0 : (C (p : ℤ) : MvPolynomial σ ℤ) ∉ q := fun h => by
    have := hq _ h
    omega
  have key : ∀ k : ℕ, ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → ∀ s, ((p : ℤ) ^ k) ∣ G.coeff s := by
    intro k
    induction k with
    | zero => intros; simp
    | succ k ih =>
      intro G hG s
      have hdiv : C (p : ℤ) ∣ G := by
        rw [MvPolynomial.C_dvd_iff_dvd_coeff]
        intro i
        have h0 := congrArg (MvPolynomial.coeff i) (hred G hG)
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
        exact h0
      obtain ⟨H, rfl⟩ := hdiv
      have hH : aeval x H ∈ q := by
        rw [map_mul, MvPolynomial.aeval_C] at hG
        exact (‹q.IsPrime›.mem_or_mem hG).resolve_left (by simpa using hp0)
      rw [MvPolynomial.coeff_C_mul, pow_succ']
      exact mul_dvd_mul_left _ (ih H hH s)
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  have hd := key (G.coeff s).natAbs G hG s
  have h1 := Int.natAbs_dvd_natAbs.mpr hd
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h1
  have h3 : (G.coeff s).natAbs < p ^ (G.coeff s).natAbs := Nat.lt_pow_self hp
  omega
end ReciprocityTheory.AnForm.R.IntegerToRational
