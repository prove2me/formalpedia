-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.algebraicIndependent_of_derivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:06:46.659869+00:00
-- url     : https://prove2.me/submissions/a22c24c6-38bb-4709-88b1-181c0b25c802

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_derivation_aeval_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_totalDegree_pderiv_lt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_eq_C_of_pderiv_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {K R ι J : Type*} [Field K] [CharZero K] [CommRing R]
    [Nontrivial R] [Algebra K R] [Fintype ι] (z : ι → R) (δ : J → Derivation K R R)
    (h : ∀ c : ι → R, (∀ j, ∑ i, c i * δ j (z i) = 0) → ∀ i, c i = 0) :
    AlgebraicIndependent K z := by
  classical
  rw [algebraicIndependent_iff]
  suffices H : ∀ n (P : MvPolynomial ι K), P.totalDegree = n → aeval z P = 0 → P = 0 from
    fun P => H _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP
  have hd : ∀ i, pderiv i P = 0 := by
    have hv : ∀ i, aeval z (pderiv i P) = 0 :=
      h (fun i => aeval z (pderiv i P)) (fun j => by rw [← derivation_aeval_eq, hP, map_zero])
    intro i
    by_cases h0 : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C] at h0
      rw [h0]
      simp
    · exact ih _ (hn ▸ totalDegree_pderiv_lt P i (Nat.pos_of_ne_zero h0)) _ rfl (hv i)
  have h0 := eq_C_of_pderiv_eq_zero P hd
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, aeval_C] at hP
  have hc : coeff 0 P = 0 := (algebraMap K R).injective (hP.trans (map_zero _).symm)
  rw [h0, hc, map_zero]
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
