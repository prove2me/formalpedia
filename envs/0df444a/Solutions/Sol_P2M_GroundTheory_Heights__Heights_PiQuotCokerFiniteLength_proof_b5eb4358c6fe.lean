-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PiQuotCokerFiniteLength_proof_b5eb4358c6fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:52.250305+00:00
-- url     : https://prove2.me/submissions/ec6e9151-c3be-42ab-a3e3-69e290edc477

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPiQuotCokerFiniteLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights
namespace PiQuotCokerFiniteLength
theorem _root_.solution : PiQuotCokerFiniteLength.Statement := by
  intro B _ _ _ J hJ hQ
  have : Finite J.minimalPrimes := (J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype
  let : Fintype J.minimalPrimes := Fintype.ofFinite _
  classical
  have hfac : ∀ (P : J.minimalPrimes) (x : B),
      quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x :=
    fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B) := fun P => by
      have h1 := congrFun hy P
      rwa [hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hx : x ∈ sInf J.minimalPrimes := Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, hJ.radical] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

  have hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' →
      (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp P P' hne hPQ hP'Q
    rcases hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm
    · exfalso
      apply hne
      have e1 : (P : Ideal B) = Q := le_antisymm hPQ (hmin.2 P.2.1 hPQ)
      have e2 : (P' : Ideal B) = Q := le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)
      exact Subtype.ext (e1.trans e2.symm)
    · exact hm
  let IP : J.minimalPrimes → Ideal B := fun P =>
    (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)
  let I : Ideal B := Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)
  have hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp hIQ
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.mp hIQ
    obtain ⟨P', hP', hP'Q⟩ := hQp.inf_le'.mp (le_sup_left.trans hPQ)
    exact hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q
  have htors : Module.IsTorsionBySet B
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))
      (I : Set B) := by
    intro c z
    obtain ⟨y, hy⟩ := z
    show y • c = 0
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B) := fun P =>
      Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)
    choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)
    choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)
    refine ⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩
    funext Q
    rw [hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]
    · rw [← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]
    · intro P _ hPQ
      have hle : IP P ≤ (Q : Ideal B) :=
        Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))
    · intro h
      exact absurd (Finset.mem_univ Q) h
  by_cases hItop : I = ⊤
  · haveI : Subsingleton
        (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
      ⟨fun c d => by
        have hc := @htors c ⟨1, by rw [hItop]; trivial⟩
        have hd := @htors d ⟨1, by rw [hItop]; trivial⟩
        rw [one_smul] at hc hd
        rw [hc, hd]⟩
    exact IsFiniteLength.of_subsingleton
  have hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩
  have : IsArtinianRing (B ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let := htors.module
  have : IsScalarTower B (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    htors.isScalarTower
  have : Module.Finite (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  have : IsArtinian (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    isArtinian_of_fg_of_artinian'
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective
end PiQuotCokerFiniteLength
end GroundTheory.Heights₂.Heights
