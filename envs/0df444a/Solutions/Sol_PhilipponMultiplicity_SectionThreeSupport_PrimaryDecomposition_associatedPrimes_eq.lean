-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.PrimaryDecomposition.associatedPrimes_eq
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:43:06.660138+00:00
-- url     : https://prove2.me/submissions/1fff0db6-af79-4130-9dd2-712022410c7e

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponPrimaryAssociated.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem associatedPrimes_quotient_eq (I : Ideal R) :
    associatedPrimes R (R ⧸ I) = I.associatedPrimes := by
  have hc (f : R) : (⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I f} = I.colon {f} := by
    ext x
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
    rfl
  ext q
  constructor
  · rintro ⟨hp, x, heq⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨hp, f, heq.trans (congrArg Ideal.radical (hc f))⟩
  · rintro ⟨hp, f, heq⟩
    exact ⟨hp, Ideal.Quotient.mk I f, heq.trans (congrArg Ideal.radical (hc f).symm)⟩

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The supplied genuine minimal primary decomposition has exactly the
actual associated primes of the quotient, including embedded primes. -/
theorem PrimaryDecomposition.associatedPrimes_eq (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
      Set.range (fun i => (D.component i).radical) := by
  classical
  let S : Finset (Ideal M.CoordinateRing) := Finset.univ.image D.component
  have hS : Submodule.IsMinimalPrimaryDecomposition I S := by
    constructor
    · simpa only [S, Finset.inf_image, Finset.inf_univ_eq_iInf, Function.comp_id,
        Function.comp_def, id_eq] using D.intersection_eq.symm
    · intro Q hQ
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      exact D.primary i
    · intro Q hQ T hT hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
      simp only [Function.onFun, Submodule.colon_univ]
      exact fun h => hne (congrArg D.component (D.radicals_injective h))
    · intro Q hQ hle
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      let A : Ideal M.CoordinateRing := ⨅ j : {j : Fin D.count // j ≠ i}, D.component j.1
      have hdrop : A ≤ (S.erase (D.component i)).inf id := by
        apply Finset.le_inf_iff.mpr
        intro Q hQ
        obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp hQ
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
        have hji : j ≠ i := fun h => hneq (congrArg D.component h)
        exact iInf_le _ (⟨j, hji⟩ : {j : Fin D.count // j ≠ i})
      have hAI : A ≤ I := by
        apply le_trans (b := ⨅ j, D.component j) _ D.intersection_eq.symm.le
        apply le_iInf
        intro j
        by_cases hji : j = i
        · exact hji ▸ hdrop.trans hle
        · exact iInf_le _ (⟨j, hji⟩ : {j : Fin D.count // j ≠ i})
      have hIA : I ≤ A := by
        apply le_iInf
        intro j
        exact D.intersection_eq.le.trans (iInf_le _ j.1)
      exact D.irredundant i (le_antisymm hAI hIA)
  rw [associatedPrimes_quotient_eq, ← hS.image_radical_eq_associated_primes]
  ext q
  simp only [Set.mem_image, Finset.mem_coe, S, Finset.mem_image,
    Finset.mem_univ, true_and, Submodule.colon_univ, Set.mem_range]
  constructor
  · rintro ⟨Q, ⟨i, rfl⟩, heq⟩
    exact ⟨i, heq⟩
  · rintro ⟨i, rfl⟩
    exact ⟨D.component i, ⟨i, rfl⟩, rfl⟩

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
      Set.range (fun i => (D.component i).radical) := by
  exact PhilipponMultiplicity.SectionThreeSupport.PrimaryDecomposition.associatedPrimes_eq M I D
