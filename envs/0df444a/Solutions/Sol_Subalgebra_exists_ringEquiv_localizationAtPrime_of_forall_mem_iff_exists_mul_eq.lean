-- Prove2me | solution 1 for Subalgebra.exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b6968869-2f3f-5ff3-bf96-75159938cba9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq

set_option autoImplicit false

namespace LocalisationPinSol

open IsLocalRing

universe u v

variable {A : Type u} {K : Type v} [CommRing A] [Field K] [Algebra A K]

theorem coe_mem (R : Subalgebra A K) (P : Ideal ↥R) (hP : P ≠ ⊤) (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥R, h ∉ P ∧ f * (h : K) = (g : K)) (r : ↥R) :
    (r : K) ∈ O :=
  (hO r).2 ⟨r, 1, fun h1 => hP ((Ideal.eq_top_iff_one P).2 h1), by simp⟩

def incl (R : Subalgebra A K) (O : Subring K) (h : ∀ r : ↥R, (r : K) ∈ O) : ↥R →+* ↥O where
  toFun r := ⟨r, h r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_incl (R : Subalgebra A K) (O : Subring K) (h : ∀ r : ↥R, (r : K) ∈ O) (r : ↥R) :
    ((incl R O h r : ↥O) : K) = (r : K) := rfl

theorem incl_injective (R : Subalgebra A K) (O : Subring K) (h : ∀ r : ↥R, (r : K) ∈ O) :
    Function.Injective (incl R O h) := by
  intro x y hxy
  have := congrArg (fun z : ↥O => (z : K)) hxy
  simpa using this

theorem isLocalization (R : Subalgebra A K) (P : Ideal ↥R) [P.IsPrime] (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥R, h ∉ P ∧ f * (h : K) = (g : K))
    (h : ∀ r : ↥R, (r : K) ∈ O) :
    @IsLocalization.AtPrime ↥R _ ↥O _ (incl R O h).toAlgebra P _ := by
  letI : Algebra ↥R ↥O := (incl R O h).toAlgebra
  have halg : ∀ r : ↥R, algebraMap ↥R ↥O r = incl R O h r := fun r => rfl
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy0 : (y : K) ≠ 0 := by
      intro h0
      apply hy
      have : y = 0 := by exact_mod_cast h0
      rw [this]; exact P.zero_mem
    have hinv : (y : K)⁻¹ ∈ O := (hO _).2 ⟨1, y, hy, by simp [inv_mul_cancel₀ hy0]⟩
    refine isUnit_iff_exists_inv.2 ⟨⟨(y : K)⁻¹, hinv⟩, Subtype.ext ?_⟩
    change (y : K) * (y : K)⁻¹ = 1
    exact mul_inv_cancel₀ hy0
  · intro z
    obtain ⟨g, k, hk, hz⟩ := (hO z).1 z.2
    refine ⟨(g, ⟨k, hk⟩), Subtype.ext ?_⟩
    simpa [halg] using hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    have := incl_injective R O h (by simpa [halg] using hxy)
    simp [this]

end LocalisationPinSol
p2m_reactivate "P2MW.S_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq.LocalisationPinSol"

open IsLocalRing in

theorem solution
    {A : Type*} {K : Type*} [CommRing A] [Field K] [Algebra A K]
    (R : Subalgebra A K) (P : Ideal ↥R) (hP : P.IsMaximal) (O : Subring K)
    (hO : ∀ f : K, f ∈ O ↔ ∃ g h : ↥R, h ∉ P ∧ f * (h : K) = (g : K)) :
    ∃ (hRO : ∀ r : ↥R, (r : K) ∈ O)
      (e : Localization.AtPrime P ≃+* ↥O),
      (∀ r : ↥R, e (algebraMap ↥R (Localization.AtPrime P) r) = ⟨(r : K), hRO r⟩) ∧
      ∃ _ : IsLocalRing ↥O,
        (∀ (f : K) (hf : f ∈ O), (⟨f, hf⟩ : ↥O) ∈ maximalIdeal ↥O ↔
            ∃ g h : ↥R, g ∈ P ∧ h ∉ P ∧ f * (h : K) = (g : K)) ∧
        (∀ r : ↥R, (⟨(r : K), hRO r⟩ : ↥O) ∈ maximalIdeal ↥O ↔ r ∈ P) ∧
        (IsNoetherianRing ↥R → IsNoetherianRing ↥O) ∧
        ((∀ r : ↥R, ∃ a : A, r - algebraMap A ↥R a ∈ P) →
          ∀ (f : K) (hf : f ∈ O), ∃ (a : A) (ha : algebraMap A K a ∈ O),
            ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨algebraMap A K a, ha⟩)) := by
  classical
  haveI : P.IsPrime := hP.isPrime
  have hRO : ∀ r : ↥R, (r : K) ∈ O :=
    LocalisationPinSol.coe_mem R P hP.ne_top O hO
  letI : Algebra ↥R ↥O := (LocalisationPinSol.incl R O hRO).toAlgebra
  have halg : ∀ r : ↥R, algebraMap ↥R ↥O r = ⟨(r : K), hRO r⟩ := fun r => rfl
  haveI hloc : IsLocalization.AtPrime ↥O P := LocalisationPinSol.isLocalization R P O hO hRO
  haveI hlr : IsLocalRing ↥O := IsLocalization.AtPrime.isLocalRing ↥O P
  have hmax : ∀ r : ↥R, algebraMap ↥R ↥O r ∈ maximalIdeal ↥O ↔ r ∈ P :=
    fun r => IsLocalization.AtPrime.to_map_mem_maximal_iff ↥O P r
  refine ⟨hRO, (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) ↥O).toRingEquiv, ?_, hlr,
    ?_, ?_, ?_, ?_⟩
  · intro r
    change (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) ↥O)
      (algebraMap ↥R (Localization.AtPrime P) r) = _
    rw [AlgEquiv.commutes, halg]
  · intro f hf
    constructor
    · intro hfm
      obtain ⟨g, k, hk, hfk⟩ := (hO f).1 hf
      refine ⟨g, k, ?_, hk, hfk⟩
      have hprod : (⟨f, hf⟩ : ↥O) * algebraMap ↥R ↥O k = algebraMap ↥R ↥O g := by
        apply Subtype.ext
        simpa [halg] using hfk
      have : algebraMap ↥R ↥O g ∈ maximalIdeal ↥O := by
        rw [← hprod]; exact Ideal.mul_mem_right _ _ hfm
      exact (hmax g).1 this
    · rintro ⟨g, k, hg, hk, hfk⟩
      have hprod : (⟨f, hf⟩ : ↥O) * algebraMap ↥R ↥O k = algebraMap ↥R ↥O g := by
        apply Subtype.ext
        simpa [halg] using hfk
      have hku : IsUnit (algebraMap ↥R ↥O k) := IsLocalization.map_units ↥O (⟨k, hk⟩ : P.primeCompl)
      have hgm : algebraMap ↥R ↥O g ∈ maximalIdeal ↥O := (hmax g).2 hg
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hfu
      have : IsUnit (algebraMap ↥R ↥O g) := by rw [← hprod]; exact hfu.mul hku
      exact (IsLocalRing.mem_maximalIdeal _ |>.1 hgm) this
  · intro r
    exact hmax r
  · intro hR
    exact IsLocalization.isNoetherianRing P.primeCompl ↥O hR
  · intro hres f hf
    obtain ⟨g, k, hk, hfk⟩ := (hO f).1 hf

    obtain ⟨k', i, hi, hkk'⟩ := hP.exists_inv hk
    obtain ⟨a, ha⟩ := hres (g * k')
    refine ⟨a, hRO (algebraMap A ↥R a), ?_⟩
    have hprod : (⟨f, hf⟩ : ↥O) * algebraMap ↥R ↥O k = algebraMap ↥R ↥O g := by
      apply Subtype.ext
      simpa [halg] using hfk

    have hmem : (⟨f, hf⟩ : ↥O) - ⟨algebraMap A K a, hRO (algebraMap A ↥R a)⟩ ∈ maximalIdeal ↥O := by
      have h1 : algebraMap ↥R ↥O (g * k' - algebraMap A ↥R a) ∈ maximalIdeal ↥O := (hmax _).2 ha
      have h2 : algebraMap ↥R ↥O i ∈ maximalIdeal ↥O := (hmax _).2 hi
      have hkey : (⟨f, hf⟩ : ↥O) - ⟨algebraMap A K a, hRO (algebraMap A ↥R a)⟩ =
          algebraMap ↥R ↥O (g * k' - algebraMap A ↥R a) + (⟨f, hf⟩ : ↥O) * algebraMap ↥R ↥O i := by
        have hi' : algebraMap ↥R ↥O i = 1 - algebraMap ↥R ↥O k' * algebraMap ↥R ↥O k := by
          have := congrArg (algebraMap ↥R ↥O) hkk'
          rw [map_add, map_mul, map_one] at this
          rw [← this]; ring
        have haO : (⟨algebraMap A K a, hRO (algebraMap A ↥R a)⟩ : ↥O) =
            algebraMap ↥R ↥O (algebraMap A ↥R a) := by
          rw [halg]
          exact Subtype.ext (by simp)
        rw [haO, map_sub, map_mul, hi']
        have : (⟨f, hf⟩ : ↥O) * (1 - algebraMap ↥R ↥O k' * algebraMap ↥R ↥O k) =
            (⟨f, hf⟩ : ↥O) - algebraMap ↥R ↥O k' * ((⟨f, hf⟩ : ↥O) * algebraMap ↥R ↥O k) := by ring
        rw [this, hprod]; ring
      rw [hkey]
      exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ h2)
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem

end S_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
end P2MW
export P2MW.S_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq (solution)
