-- Prove2me | solution 1 for ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8fb4cdc0-a8e7-5c7b-b04d-4203f01055e8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot

set_option autoImplicit false

namespace GVC3

open Polynomial

section Rel

theorem coeff_relMap_mem {E : Type*} [CommRing E] {S : Type*} [SetLike S E] [SubringClass S E] (s : S) (x : E) (hx : x ∈ s)
    (Θ : Polynomial (Polynomial ℤ)) (n : ℕ) :
    (Θ.map (eval₂RingHom (Int.castRingHom E) x)).coeff n ∈ s := by
  rw [coeff_map, coe_eval₂RingHom, eval₂_eq_sum_range]
  refine sum_mem fun i _ => mul_mem ?_ (pow_mem hx i)
  simp only [eq_intCast]
  exact intCast_mem s _

theorem monicRel_map {E E' : Type*} [CommRing E] [CommRing E'] (g : E →+* E') (x y : E) (Θ : Polynomial (Polynomial ℤ))
    (hroot : (Θ.map (eval₂RingHom (Int.castRingHom E) x)).IsRoot y) :
    (Θ.map (eval₂RingHom (Int.castRingHom E') (g x))).IsRoot (g y) := by
  have hcomp : (g.comp (eval₂RingHom (Int.castRingHom E) x)) = eval₂RingHom (Int.castRingHom E') (g x) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  rw [IsRoot, eval_map] at hroot ⊢
  rw [← hcomp, ← hom_eval₂, hroot, map_zero]

variable {E : Type*} [Field E]

theorem isIntegral_subring_of_monicRel (s : Subring E) (x y : E) (hx : x ∈ s)
    (Θ : Polynomial (Polynomial ℤ)) (hΘ : Θ.Monic)
    (hroot : (Θ.map (eval₂RingHom (Int.castRingHom E) x)).IsRoot y) : IsIntegral s y := by
  set T := Θ.map (eval₂RingHom (Int.castRingHom E) x) with hT
  have hTm : T.Monic := hΘ.map _
  have hlifts : T ∈ lifts (algebraMap s E) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, coeff_relMap_mem s x hx Θ n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hTm
  refine ⟨q, hqm, ?_⟩
  rw [eval₂_eq_eval_map, hq]
  exact hroot

theorem isIntegral_adjoin_of_monicRel {κ : Type*} [Field κ] [Algebra κ E] (x y : E)
    (Θ : Polynomial (Polynomial ℤ)) (hΘ : Θ.Monic)
    (hroot : (Θ.map (eval₂RingHom (Int.castRingHom E) x)).IsRoot y) :
    IsIntegral (↥(IntermediateField.adjoin κ {x})) y := by
  set F := IntermediateField.adjoin κ {x}
  set T := Θ.map (eval₂RingHom (Int.castRingHom E) x) with hT
  have hTm : T.Monic := hΘ.map _
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self κ x
  have hlifts : T ∈ lifts (algebraMap F E) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, coeff_relMap_mem F x hxF Θ n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hTm
  refine ⟨q, hqm, ?_⟩
  rw [eval₂_eq_eval_map, hq]
  exact hroot

theorem isIntegral_of_monicRel_of_isIntegral {κ : Type*} [Field κ] [Algebra κ E] (x y : E)
    (Θ : Polynomial (Polynomial ℤ)) (hΘ : Θ.Monic)
    (hroot : (Θ.map (eval₂RingHom (Int.castRingHom E) x)).IsRoot y) (hx : IsIntegral κ x) :
    IsIntegral κ y := by
  haveI : FiniteDimensional κ ↥(IntermediateField.adjoin κ {x}) := IntermediateField.adjoin.finiteDimensional hx
  haveI : Algebra.IsIntegral κ ↥(IntermediateField.adjoin κ {x}) := Algebra.IsIntegral.of_finite κ _
  exact isIntegral_trans (R := κ) y (isIntegral_adjoin_of_monicRel (κ := κ) x y Θ hΘ hroot)

end Rel

section Main

variable {A : Type*} [CommRing A] [IsLocalRing A] {K' : Type*} [Field K'] [Algebra A K']

theorem inv_mem_of_isUnit (V : ValuationSubring K') (y : ↥V) (hy : IsUnit y) : ((y : K')⁻¹) ∈ V := by
  obtain ⟨u, rfl⟩ := hy
  have h : (u : ↥V) * ((u⁻¹ : (↥V)ˣ) : ↥V) = 1 := u.mul_inv
  have h' : ((u : ↥V) : K') * (((u⁻¹ : (↥V)ˣ) : ↥V) : K') = 1 := by
    have := congrArg (fun z : ↥V => (z : K')) h
    simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
  rw [inv_eq_of_mul_eq_one_right h']
  exact ((u⁻¹ : (↥V)ˣ) : ↥V).2

theorem isUnit_of_inv_mem (V : ValuationSubring K') (y : K') (hy : y ∈ V) (hinv : y⁻¹ ∈ V) (hne : y ≠ 0) :
    IsUnit (⟨y, hy⟩ : ↥V) :=
  isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩

theorem main (V : ValuationSubring K')
    (hA : ∀ a : A, algebraMap A K' a ∈ V) (hAm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A K' a ∈ V.nonunits)
    (J J' : K')
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (hΦJ : (Φ.map (eval₂RingHom (Int.castRingHom K') J)).IsRoot J')
    (Ψ : Polynomial (Polynomial ℤ)) (hΨ : Ψ.Monic)
    (hΨJ : (Ψ.map (eval₂RingHom (Int.castRingHom K') J')).IsRoot J)
    (hgen : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      aeval J P ∈ V ∧ (aeval J P)⁻¹ ∈ V)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    aeval J' P ∈ V ∧ (aeval J' P)⁻¹ ∈ V := by
  classical

  let θ : A →+* ↥V := (algebraMap A K').codRestrict V hA
  have hθ : ∀ a : A, ((θ a : ↥V) : K') = algebraMap A K' a := fun a => rfl
  have hsubθ : V.subtype.comp θ = algebraMap A K' := RingHom.ext fun a => rfl
  have hE1 : ∀ (Q : Polynomial A) (x : ↥V), (((Q.map θ).eval x : ↥V) : K') = aeval (x : K') Q := by
    intro Q x
    change V.subtype ((Q.map θ).eval x) = _
    rw [eval_map, hom_eval₂, hsubθ, aeval_def]
    rfl
  have haevalmem : ∀ (Q : Polynomial A) (x : ↥V), aeval (x : K') Q ∈ V := by
    intro Q x; rw [← hE1]; exact SetLike.coe_mem _

  have hX : (X : Polynomial A).map (IsLocalRing.residue A) ≠ 0 := by rw [Polynomial.map_X]; exact X_ne_zero
  have hJ : J ∈ V := by simpa using (hgen X hX).1

  have hJ' : J' ∈ V := by
    have hint : IsIntegral (↥V.toSubring) J' := isIntegral_subring_of_monicRel V.toSubring J J' hJ Φ hΦ hΦJ
    have hint' : IsIntegral (↥V) J' := hint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := K')).mp hint'
    rw [← hy]; exact y.2

  set k := IsLocalRing.ResidueField ↥V
  let π : ↥V →+* k := IsLocalRing.residue ↥V
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A, (π.comp θ) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff, hθ]
    exact hAm a ha
  let ρ : IsLocalRing.ResidueField A →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (π.comp θ) hker
  have hρ : ρ.comp (IsLocalRing.residue A) = π.comp θ := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact Ideal.Quotient.lift_mk _ _ _
  have hρinj : Function.Injective ρ := ρ.injective

  set j : k := π ⟨J, hJ⟩ with hjdef
  set j' : k := π ⟨J', hJ'⟩ with hj'def
  have hE2 : ∀ (Q : Polynomial A) (x : ↥V),
      π ((Q.map θ).eval x) = ((Q.map (IsLocalRing.residue A)).map ρ).eval (π x) := by
    intro Q x
    rw [eval_map, hom_eval₂, Polynomial.map_map, hρ, eval_map]

  have hPmem : aeval J' P ∈ V := haevalmem P ⟨J', hJ'⟩
  refine ⟨hPmem, ?_⟩

  letI : Algebra (IsLocalRing.ResidueField A) k := ρ.toAlgebra
  have halg : algebraMap (IsLocalRing.ResidueField A) k = ρ := rfl
  by_cases hT : ∀ Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 → aeval J Q ≠ 0
  ·

    have hjT : ∀ Qb : Polynomial (IsLocalRing.ResidueField A), Qb ≠ 0 → (Qb.map ρ).eval j ≠ 0 := by
      intro Qb hQb
      obtain ⟨Q, rfl⟩ := map_surjective (IsLocalRing.residue A) Ideal.Quotient.mk_surjective Qb
      have hne := hT Q hQb
      obtain ⟨hmem, hinv⟩ := hgen Q hQb
      have hunit : IsUnit ((Q.map θ).eval ⟨J, hJ⟩) := by
        have heq : (Q.map θ).eval ⟨J, hJ⟩ = ⟨aeval J Q, hmem⟩ := Subtype.ext (hE1 Q ⟨J, hJ⟩)
        rw [heq]
        exact isUnit_of_inv_mem V _ hmem hinv hne
      rw [← hE2]
      intro h0
      rw [IsLocalRing.residue_eq_zero_iff] at h0
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp h0) hunit

    have hunit' : IsUnit ((P.map θ).eval ⟨J', hJ'⟩) := by
      by_contra hnu
      have h0 : π ((P.map θ).eval ⟨J', hJ'⟩) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hE2] at h0

      have hPb : (P.map (IsLocalRing.residue A)) ≠ 0 := hP
      have hj'alg : IsIntegral (IsLocalRing.ResidueField A) j' := by
        have : IsAlgebraic (IsLocalRing.ResidueField A) j' :=
          ⟨P.map (IsLocalRing.residue A), hPb, by rw [aeval_def, halg, ← eval_map]; exact h0⟩
        exact this.isIntegral

      have hΨk : (Ψ.map (eval₂RingHom (Int.castRingHom k) j')).IsRoot j := by
        have h1 : (Ψ.map (eval₂RingHom (Int.castRingHom ↥V) ⟨J', hJ'⟩)).IsRoot ⟨J, hJ⟩ := by

          have hcomp : V.subtype.comp (eval₂RingHom (Int.castRingHom ↥V) ⟨J', hJ'⟩)
              = eval₂RingHom (Int.castRingHom K') J' := by
            apply Polynomial.ringHom_ext
            · intro a; simp
            · simp
          rw [IsRoot, eval_map]
          apply Subtype.val_injective
          change V.subtype (eval₂ _ _ Ψ) = ((0 : ↥V) : K')
          rw [hom_eval₂, hcomp, ZeroMemClass.coe_zero]
          have h3 := hΨJ
          rw [IsRoot, eval_map] at h3
          exact h3
        exact monicRel_map π ⟨J', hJ'⟩ ⟨J, hJ⟩ Ψ h1
      have hjint : IsIntegral (IsLocalRing.ResidueField A) j :=
        isIntegral_of_monicRel_of_isIntegral j' j Ψ hΨ hΨk hj'alg

      obtain ⟨Qb, hQbm, hQb0⟩ := hjint
      apply hjT Qb hQbm.ne_zero
      rw [eval_map, ← halg, ← aeval_def]
      exact hQb0
    have := inv_mem_of_isUnit V _ hunit'
    rwa [hE1] at this
  ·
    push Not at hT
    obtain ⟨Q₀, hQ₀, hQ₀J⟩ := hT

    have hm0 : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A K' a = 0 := by
      intro a ha
      have hred : (Q₀ + C a).map (IsLocalRing.residue A) ≠ 0 := by
        rw [Polynomial.map_add, Polynomial.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, add_zero]
        exact hQ₀
      obtain ⟨hmem, hinv⟩ := hgen _ hred
      rw [map_add, aeval_C, hQ₀J, zero_add] at hmem hinv
      by_contra hne
      have hu := isUnit_of_inv_mem V _ hmem hinv hne
      have hnu : (⟨algebraMap A K' a, hmem⟩ : ↥V) ∈ IsLocalRing.maximalIdeal ↥V :=
        ValuationSubring.coe_mem_nonunits_iff.mp (hAm a ha)
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp hnu) hu

    have hkerθ : ∀ a ∈ IsLocalRing.maximalIdeal A, θ a = 0 := fun a ha => Subtype.ext (hm0 a ha)
    let θ' : IsLocalRing.ResidueField A →+* ↥V := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) θ hkerθ
    let σ : IsLocalRing.ResidueField A →+* K' := V.subtype.comp θ'
    have hσres : σ.comp (IsLocalRing.residue A) = algebraMap A K' := by
      refine RingHom.ext fun a => ?_
      show ((Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) θ hkerθ (Ideal.Quotient.mk _ a) : ↥V) : K') = _
      rw [Ideal.Quotient.lift_mk]
      rfl
    have hσV : ∀ c, σ c ∈ V := fun c => (θ' c).2
    letI : Algebra (IsLocalRing.ResidueField A) K' := σ.toAlgebra
    have halgK : algebraMap (IsLocalRing.ResidueField A) K' = σ := rfl
    have hEσ : ∀ Q : Polynomial A, ∀ x : K', aeval x (Q.map (IsLocalRing.residue A)) = aeval x Q := by
      intro Q x
      rw [aeval_def, halgK, eval₂_map, hσres, ← aeval_def]

    have hJint : IsIntegral (IsLocalRing.ResidueField A) J := by
      have : IsAlgebraic (IsLocalRing.ResidueField A) J := ⟨Q₀.map (IsLocalRing.residue A), hQ₀, by rw [hEσ]; exact hQ₀J⟩
      exact this.isIntegral
    have hJ'int : IsIntegral (IsLocalRing.ResidueField A) J' := isIntegral_of_monicRel_of_isIntegral J J' Φ hΦ hΦJ hJint

    let VS : Subalgebra (IsLocalRing.ResidueField A) K' :=
      { V.toSubring with
        algebraMap_mem' := fun c => hσV c }
    have hFV : (IntermediateField.adjoin (IsLocalRing.ResidueField A) {J'}).toSubalgebra ≤ VS := by
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hJ'int.isAlgebraic]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hJ')

    have hPF : aeval J' P ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A) {J'} := by
      rw [← hEσ]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    have hinvF : (aeval J' P)⁻¹ ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A) {J'} :=
      IntermediateField.inv_mem _ hPF
    exact hFV hinvF

end Main

end GVC3

theorem solution
    (A : Type*) [CommRing A] [IsLocalRing A] (K' : Type*) [Field K'] [Algebra A K']
    (V : ValuationSubring K')
    (hA : ∀ a : A, algebraMap A K' a ∈ V) (hAm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A K' a ∈ V.nonunits)
    (J J' : K')
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (hΦJ : (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K') J)).IsRoot J')
    (Ψ : Polynomial (Polynomial ℤ)) (hΨ : Ψ.Monic)
    (hΨJ : (Ψ.map (Polynomial.eval₂RingHom (Int.castRingHom K') J')).IsRoot J)
    (hgen : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval J P ∈ V ∧ (Polynomial.aeval J P)⁻¹ ∈ V) :
    ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval J' P ∈ V ∧ (Polynomial.aeval J' P)⁻¹ ∈ V :=
  fun P hP => GVC3.main V hA hAm J J' Φ hΦ hΦJ Ψ hΨ hΨJ hgen P hP

end S_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
end P2MW
export P2MW.S_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot (solution)
