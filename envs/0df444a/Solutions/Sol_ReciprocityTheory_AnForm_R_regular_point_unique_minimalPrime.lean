-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.regular_point_unique_minimalPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:45.285164+00:00
-- url     : https://prove2.me/submissions/99f21335-ea9d-45ee-8fb5-2131bf113924

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RingKrullDimLocRingEqOfMinimalPrime
import Theorems.Thm_P2M_RH_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal_a3d235ebb1deb6ff
import Theorems.Thm_ReciprocityTheory_CA_height_add_height_maximal_quotient_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsRegularLocalRing (locRing K p)] :
    ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧
      (∀ 𝔮' ∈ K.minimalPrimes, 𝔮' ≤ ptIdeal p → 𝔮' = 𝔮) ∧
      ringKrullDim (locRing K p) + (𝔮.height : WithBot ℕ∞) = n := by
  set A := MvPolynomial (Fin n) ℂ
  set P := ptIdeal p
  set S := locPt p
  set I : Ideal S := Ideal.map (algebraMap A S) K with hI
  have : IsDomain (S ⧸ I) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  have hIp : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  set 𝔮 : Ideal A := I.under A with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under A I
  have hdisj : Disjoint (P.primeCompl : Set A) 𝔮 :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint P.primeCompl S I).mp hIp).2
  have h𝔮P : 𝔮 ≤ P := by
    intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hdisj (show x ∈ (P.primeCompl : Set A) from hxP) hx
  have hK𝔮 : K ≤ 𝔮 := fun x hx => Ideal.mem_map_of_mem _ hx

  have key : ∀ Q : Ideal A, Q.IsPrime → K ≤ Q → Q ≤ P → 𝔮 ≤ Q := by
    intro Q hQ hKQ hQP
    have hd : Disjoint (P.primeCompl : Set A) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQP hxQ)
    have hmap : I ≤ Ideal.map (algebraMap A S) Q := Ideal.map_mono hKQ
    calc 𝔮 ≤ (Ideal.map (algebraMap A S) Q).under A := Ideal.comap_mono hmap
      _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl S hQ hd
  have hmin : 𝔮 ∈ K.minimalPrimes :=
    ⟨⟨h𝔮p, hK𝔮⟩, fun Q ⟨hQ, hKQ⟩ hQ𝔮 => key Q hQ hKQ (hQ𝔮.trans h𝔮P)⟩
  refine ⟨𝔮, hmin, h𝔮P, ?_, ?_⟩
  · intro 𝔮' h' h'P
    exact le_antisymm (h'.2 ⟨h𝔮p, hK𝔮⟩ (key 𝔮' h'.1.1 h'.1.2 h'P)) (key 𝔮' h'.1.1 h'.1.2 h'P)
  ·
    set 𝔪 : Ideal (A ⧸ 𝔮) := P.map (Ideal.Quotient.mk 𝔮) with h𝔪
    have hmem : ∀ a : A, Ideal.Quotient.mk 𝔮 a ∈ 𝔪 ↔ a ∈ P := fun a =>
      Ideal.mem_quotient_iff_mem h𝔮P
    have hPmax : P.IsMaximal := ptIdeal_isMaximal p
    have h𝔪max : 𝔪.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective hPmax with h | h
      · exfalso
        have h1 : Ideal.Quotient.mk 𝔮 1 ∈ 𝔪 := by rw [h𝔪, h]; exact Submodule.mem_top
        exact hPmax.ne_top ((Ideal.eq_top_iff_one (I := P)).mpr ((hmem 1).mp h1))
      · exact h
    let f : A ⧸ 𝔮 →+* S ⧸ I := Ideal.quotientMap I (algebraMap A S) le_rfl
    letI : Algebra (A ⧸ 𝔮) (S ⧸ I) := f.toAlgebra
    have hf : ∀ a : A, algebraMap (A ⧸ 𝔮) (S ⧸ I) (Ideal.Quotient.mk 𝔮 a) =
        Ideal.Quotient.mk I (algebraMap A S a) := fun a => Ideal.quotientMap_mk
    have hloc : IsLocalization.AtPrime (S ⧸ I) 𝔪 := by
      show IsLocalization 𝔪.primeCompl (S ⧸ I)
      rw [isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        have ha : a ∈ P.primeCompl := fun h => hy ((hmem a).mpr h)
        rw [hf]
        exact (IsLocalization.map_units S (⟨a, ha⟩ : P.primeCompl)).map _
      · intro z
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
        have ht : Ideal.Quotient.mk 𝔮 (t : A) ∈ 𝔪.primeCompl := fun h => t.2 ((hmem _).mp h)
        refine ⟨⟨Ideal.Quotient.mk 𝔮 a, ⟨_, ht⟩⟩, ?_⟩
        simp only [hf, ← map_mul]
        rw [IsLocalization.mk'_spec]
      · intro x y hxy
        exact ⟨1, by rw [Ideal.quotientMap_injective hxy]⟩
    have hdim : ringKrullDim (S ⧸ I) = 𝔪.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (S ⧸ I)
    have hsum := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 𝔪
    show ringKrullDim (S ⧸ I) + _ = _
    rw [hdim, ← WithBot.coe_add, add_comm, hsum]
    rfl
end ReciprocityTheory.AnForm.R
