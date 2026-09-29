-- Prove2me | solution 1 for TWNum.finrank_continuousH2_extArithLoc_inl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ac0a97eb-e264-5b8e-acbe-d2d838f7b6d1

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TWNum_finrank_continuousH2_extArithLoc_inl_eq_zero

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

namespace WnumArchH2

universe u

section Engine

open Rep.FiniteCyclicGroup

variable {k : Type u} [Field k]

theorem finrank_h1_add_finrank
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A] :
    finrank k (groupCohomology A 1) + finrank k A
      = finrank k (LinearMap.ker A.norm.hom.toLinearMap)
        + finrank k A.ρ.invariants := by
  classical
  let πlin := ConcreteCategory.hom (groupCohomologyπOdd A g hg 1 odd_one)
  have hπsurj : Function.Surjective πlin := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  have hπker : LinearMap.ker πlin =
      Submodule.comap (LinearMap.ker A.norm.hom.toLinearMap).subtype
        (LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap) := by
    ext x
    have h__af := groupCohomologyπOdd_eq_zero_iff A g hg 1 odd_one x
    simp [LinearMap.mem_ker] at h__af
    exact h__af
  have hrange_le : LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap
      ≤ LinearMap.ker A.norm.hom.toLinearMap := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker]
    have hbridge : (A.applyAsHom g - 𝟙 A).hom.toLinearMap x = A.ρ g x - x := by
      simp [Rep.sub_hom, Rep.applyAsHom]
    rw [hbridge]
    show Representation.norm A.ρ (A.ρ g x - x) = 0
    rw [map_sub, Representation.norm_self_apply, sub_self]
  have h2 : finrank k (LinearMap.ker πlin) =
      finrank k (LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap) := by
    rw [hπker]
    exact (Submodule.comapSubtypeEquivOfLe hrange_le).finrank_eq
  have h1 : finrank k (LinearMap.range πlin) + finrank k (LinearMap.ker πlin)
      = finrank k (LinearMap.ker A.norm.hom.toLinearMap) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h1' : finrank k (LinearMap.range πlin) = finrank k (groupCohomology A 1) := by
    rw [LinearMap.range_eq_top.2 hπsurj]
    exact finrank_top k _
  have h3 : finrank k (LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap)
      + finrank k (LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap)
      = finrank k A :=
    LinearMap.finrank_range_add_finrank_ker _
  have h4 : LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap = A.ρ.invariants := by
    ext x
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x]
    have hbridge : (A.applyAsHom g - 𝟙 A).hom.toLinearMap x = A.ρ g x - x := by
      simp [Rep.sub_hom, Rep.applyAsHom]
    simp [LinearMap.mem_ker, hbridge, sub_eq_zero]
  rw [← h1', ← h4]
  omega

theorem finrank_h2_add_finrank
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A] :
    finrank k (groupCohomology A 2) + finrank k A
      = finrank k (LinearMap.ker A.norm.hom.toLinearMap)
        + finrank k A.ρ.invariants := by
  classical
  let πlin := ConcreteCategory.hom (groupCohomologyπEven A g hg 2 even_two)
  have hπsurj : Function.Surjective πlin := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  have hπker : LinearMap.ker πlin =
      Submodule.comap (LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap).subtype
        (LinearMap.range A.norm.hom.toLinearMap) := by
    ext x
    have h__af := groupCohomologyπEven_eq_zero_iff A g hg 2 even_two x
    simp [LinearMap.mem_ker] at h__af
    exact h__af
  have h4 : LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap = A.ρ.invariants := by
    ext x
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x]
    have hbridge : (A.applyAsHom g - 𝟙 A).hom.toLinearMap x = A.ρ g x - x := by
      simp [Rep.sub_hom, Rep.applyAsHom]
    simp [LinearMap.mem_ker, hbridge, sub_eq_zero]
  have hrange_le : LinearMap.range A.norm.hom.toLinearMap
      ≤ LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap := by
    rw [h4]
    rintro _ ⟨x, rfl⟩
    intro h
    exact Representation.self_norm_apply A.ρ h x
  have h2 : finrank k (LinearMap.ker πlin) =
      finrank k (LinearMap.range A.norm.hom.toLinearMap) := by
    rw [hπker]
    exact (Submodule.comapSubtypeEquivOfLe hrange_le).finrank_eq
  have h1 : finrank k (LinearMap.range πlin) + finrank k (LinearMap.ker πlin)
      = finrank k (LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h1' : finrank k (LinearMap.range πlin) = finrank k (groupCohomology A 2) := by
    rw [LinearMap.range_eq_top.2 hπsurj]
    exact finrank_top k _
  have h3 : finrank k (LinearMap.range A.norm.hom.toLinearMap)
      + finrank k (LinearMap.ker A.norm.hom.toLinearMap) = finrank k A :=
    LinearMap.finrank_range_add_finrank_ker _
  rw [← h1', ← h4]
  omega

theorem finrank_h2_eq_finrank_h1
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A] :
    finrank k (groupCohomology A 2) = finrank k (groupCohomology A 1) := by
  have e2 := finrank_h2_add_finrank A g hg
  have e1 := finrank_h1_add_finrank A g hg
  omega

theorem finiteDimensional_h2
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A] :
    FiniteDimensional k (groupCohomology A 2) := by
  let πlin := ConcreteCategory.hom (groupCohomologyπEven A g hg 2 even_two)
  have hπsurj : Function.Surjective πlin := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  exact Module.Finite.of_surjective πlin hπsurj

theorem subsingleton_h2_of_subsingleton_h1
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A]
    (h1 : Subsingleton (groupCohomology A 1)) : Subsingleton (groupCohomology A 2) := by
  have e := finrank_h2_eq_finrank_h1 A g hg
  rw [Module.finrank_zero_of_subsingleton (R := k) (M := groupCohomology A 1)] at e
  haveI := finiteDimensional_h2 A g hg
  exact Module.finrank_zero_iff.1 e

end Engine

theorem complexConjugation_apply_ne_of_sq_eq_neg_one
    (ι : AlgebraicClosure ℚ) (hι : ι ^ 2 = -1) : complexConjugation ι ≠ ι := by
  intro hfix
  have h1 := complexEmbedding_complexConjugation ι
  rw [hfix] at h1

  have him : (complexEmbedding ι).im = 0 := Complex.conj_eq_iff_im.1 h1.symm

  have h2 : (complexEmbedding ι) ^ 2 = -1 := by
    rw [← map_pow, hι, map_neg, map_one]
  have h3 := congrArg Complex.re h2
  simp only [sq, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.one_re] at h3
  nlinarith [mul_self_nonneg (complexEmbedding ι).re]

theorem complexConjugation_zpow (n : ℤ) :
    complexConjugation ^ n = 1 ∨ complexConjugation ^ n = complexConjugation := by
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, complexConjugation_mul_self, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, complexConjugation_mul_self, one_zpow, one_mul, zpow_one]

theorem isLevelConstant1_archimedean (S : Finset Nat.Primes) {X : Type*}
    (x : extArithLocalGroups S (Sum.inl ()) → X) :
    IsLevelConstant₁ (extArithLoc S (Sum.inl ())) x := by
  obtain ⟨ι, hι⟩ : ∃ ι : AlgebraicClosure ℚ, ι ^ 2 = -1 :=
    IsAlgClosed.exists_pow_nat_eq (-1) two_pos
  refine ⟨IntermediateField.adjoin ℚ {ι}, ?_, fun g s hs => ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ι)
  ·
    have hc : complexConjugation ∉ (IntermediateField.adjoin ℚ {ι}).fixingSubgroup := by
      intro hmem
      exact complexConjugation_apply_ne_of_sq_eq_neg_one ι hι
        ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem ι
          (IntermediateField.mem_adjoin_simple_self ℚ ι))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (Subtype.property (show ↥(Subgroup.zpowers complexConjugation) from s))
    have hs' : ((show ↥(Subgroup.zpowers complexConjugation) from s) :
        AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈
          (IntermediateField.adjoin ℚ {ι}).fixingSubgroup := hs
    rw [← hn] at hs'
    rcases complexConjugation_zpow n with h1 | h2
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show ((show ↥(Subgroup.zpowers complexConjugation) from s) :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1
        rw [← hn, h1]
      rw [hs1, mul_one]
    · rw [h2] at hs'
      exact absurd hs' hc

theorem subsingleton_continuousH2_archimedean {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    Subsingleton
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) := by
  classical

  have hfin : IsOfFinOrder complexConjugation :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, complexConjugation_sq⟩
  letI instFT : Fintype (extArithLocalGroups S (Sum.inl ())) :=
    Fintype.ofEquiv (Fin (orderOf complexConjugation))
      (finEquivZPowers hfin :
        Fin (orderOf complexConjugation) ≃ extArithLocalGroups S (Sum.inl ()))
  haveI : IsMulCommutative (extArithLocalGroups S (Sum.inl ())) :=
    (inferInstance : IsMulCommutative ↥(Subgroup.zpowers complexConjugation))
  letI instCG : CommGroup (extArithLocalGroups S (Sum.inl ())) :=
    { (inferInstance : Group (extArithLocalGroups S (Sum.inl ()))) with
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  haveI : FiniteDimensional k (Rep.res (extArithLoc S (Sum.inl ())) M) :=
    ‹FiniteDimensional k M›
  let g : extArithLocalGroups S (Sum.inl ()) :=
    (⟨complexConjugation, Subgroup.mem_zpowers complexConjugation⟩ :
      ↥(Subgroup.zpowers complexConjugation))
  have hg : ∀ x : extArithLocalGroups S (Sum.inl ()), x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (Subtype.property (show ↥(Subgroup.zpowers complexConjugation) from x))
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, Subtype.ext ((Subgroup.coe_zpow (Subgroup.zpowers complexConjugation)
        (show ↥(Subgroup.zpowers complexConjugation) from g) n).trans hn)⟩

  have h2 : Subsingleton (groupCohomology (Rep.res (extArithLoc S (Sum.inl ())) M) 2) :=
    subsingleton_h2_of_subsingleton_h1 (Rep.res (extArithLoc S (Sum.inl ())) M) g hg hinf

  refine ⟨fun a b => ?_⟩
  suffices h0 : ∀ a : continuousH2 (extArithLoc S (Sum.inl ()))
      (Rep.res (extArithLoc S (Sum.inl ())) M), a = 0 by rw [h0 a, h0 b]
  intro a
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  show continuousH2π _ _ f = 0
  rw [continuousH2π_eq_zero_iff, mem_levelCoboundaries₂_iff]
  have hf0 : H2π (Rep.res (extArithLoc S (Sum.inl ())) M) ⟨(f : _ → _), f.2.1⟩ = 0 :=
    Subsingleton.elim _ _
  rw [H2π_eq_zero_iff] at hf0
  obtain ⟨x, hx⟩ := hf0
  exact ⟨x, isLevelConstant1_archimedean S x, hx⟩

end WnumArchH2

theorem solution
    {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    finrank k
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) = 0 := by
  haveI := WnumArchH2.subsingleton_continuousH2_archimedean S M hinf
  exact Module.finrank_zero_of_subsingleton

end S_TWNum_finrank_continuousH2_extArithLoc_inl_eq_zero
end P2MW
export P2MW.S_TWNum_finrank_continuousH2_extArithLoc_inl_eq_zero (solution)
