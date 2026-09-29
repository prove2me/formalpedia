-- Prove2me | solution 1 for TWNum.subsingleton_H1_extArithLoc_inl_dualTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/93352042-d3c3-5de2-9453-49b7ed75cc3a

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

namespace WnumArchH1Dual

open Rep.FiniteCyclicGroup

section Engine

variable {k : Type} [Field k]

theorem finrank_h1_add_finrank
    {G : Type} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
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

theorem finiteDimensional_h1
    {G : Type} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A] :
    FiniteDimensional k (groupCohomology A 1) := by
  let πlin := ConcreteCategory.hom (groupCohomologyπOdd A g hg 1 odd_one)
  have hπsurj : Function.Surjective πlin := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  exact Module.Finite.of_surjective πlin hπsurj

theorem norm_eq_one_add {G : Type} [CommGroup G] [Fintype G] [DecidableEq G] (A : Rep k G) (g : G)
    (h1g : (1 : G) ≠ g) (huniv : (Finset.univ : Finset G) = {1, g}) :
    A.norm.hom.toLinearMap = 1 + A.ρ g := by
  apply LinearMap.ext
  intro x
  show Representation.norm A.ρ x = (1 + A.ρ g) x
  show (∑ h : G, A.ρ h) x = (1 + A.ρ g) x
  rw [huniv, Finset.sum_pair h1g, map_one]

theorem invariants_eq_ker {G : Type} [CommGroup G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    A.ρ.invariants = LinearMap.ker (A.ρ g - 1) := by
  ext x
  rw [Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x, LinearMap.mem_ker,
    LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem finrank_ker_dualMap_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (w : V →ₗ[k] V) :
    finrank k (LinearMap.ker w.dualMap) = finrank k (LinearMap.ker w) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker w.dualMap
  have h2 := LinearMap.finrank_range_add_finrank_ker w
  have h3 : finrank k (LinearMap.range w.dualMap) = finrank k (LinearMap.range w) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range w
  have h4 : finrank k (Module.Dual k V) = finrank k V := Subspace.dual_finrank_eq
  omega

end Engine

theorem complexConjugation_ne_one : complexConjugation ≠ 1 := by
  obtain ⟨ι, hι⟩ : ∃ ι : AlgebraicClosure ℚ, ι ^ 2 = -1 :=
    IsAlgClosed.exists_pow_nat_eq (-1) two_pos
  intro h
  have hfix : complexConjugation ι = ι := by rw [h]; rfl
  have h1 := complexEmbedding_complexConjugation ι
  rw [hfix] at h1
  have him : (complexEmbedding ι).im = 0 := Complex.conj_eq_iff_im.1 h1.symm
  have h2 : (complexEmbedding ι) ^ 2 = -1 := by rw [← map_pow, hι, map_neg, map_one]
  have h3 := congrArg Complex.re h2
  simp only [sq, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.one_re] at h3
  nlinarith [mul_self_nonneg (complexEmbedding ι).re]

set_option maxHeartbeats 1600000 in

theorem finrank_H1_dualTwist_eq {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ) :
    finrank k (H1 (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist χ)))
      = finrank k (H1 (Rep.res (extArithLoc S (Sum.inl ())) M)) := by
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
  let A : Rep k (extArithLocalGroups S (Sum.inl ())) := Rep.res (extArithLoc S (Sum.inl ())) M
  let A' : Rep k (extArithLocalGroups S (Sum.inl ())) :=
    Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist χ)
  haveI hFDA : FiniteDimensional k A := ‹FiniteDimensional k M›
  haveI hFDA' : FiniteDimensional k A' :=
    inferInstanceAs (FiniteDimensional k (Module.Dual k M))
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

  have h1g : (1 : extArithLocalGroups S (Sum.inl ())) ≠ g := by
    intro h
    apply complexConjugation_ne_one
    have := congrArg (Subtype.val : ↥(Subgroup.zpowers complexConjugation) → _) h
    exact this.symm
  have hcard : Fintype.card (extArithLocalGroups S (Sum.inl ())) = 2 := by
    have hc : Fintype.card (extArithLocalGroups S (Sum.inl ())) = orderOf complexConjugation :=
      (@Fintype.card_congr (Fin (orderOf complexConjugation)) (extArithLocalGroups S (Sum.inl ()))
        _ instFT (finEquivZPowers hfin)).symm.trans (Fintype.card_fin _)
    rw [hc]
    exact orderOf_eq_prime complexConjugation_sq complexConjugation_ne_one
  have huniv : (Finset.univ : Finset (extArithLocalGroups S (Sum.inl ()))) = {1, g} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair h1g, hcard]

  let u : M →ₗ[k] M := M.ρ complexConjugation
  have hε2 : ((χ complexConjugation : kˣ) : k) * ((χ complexConjugation : kˣ) : k) = 1 := by
    rw [← Units.val_mul, ← map_mul, complexConjugation_mul_self, map_one, Units.val_one]
  have hρ' : A'.ρ g = ((χ complexConjugation : kˣ) : k) • u.dualMap := by
    apply LinearMap.ext
    intro f
    show (M.dualTwist χ).ρ complexConjugation f = _
    rw [Rep.dualTwist_ρ_apply, complexConjugation_inv]
    rfl

  have eA := finrank_h1_add_finrank A g hg
  rw [norm_eq_one_add A g h1g huniv, invariants_eq_ker A g hg] at eA

  have eA2 : finrank k (groupCohomology A 1) + finrank k M
      = finrank k (LinearMap.ker ((1 : M →ₗ[k] M) + u)) + finrank k (LinearMap.ker (u - 1)) := eA
  have eA' := finrank_h1_add_finrank A' g hg
  rw [norm_eq_one_add A' g h1g huniv, invariants_eq_ker A' g hg, hρ'] at eA'
  have eA'2 : finrank k (groupCohomology A' 1) + finrank k (Module.Dual k M)
      = finrank k (LinearMap.ker ((1 : Module.Dual k M →ₗ[k] Module.Dual k M)
          + ((χ complexConjugation : kˣ) : k) • u.dualMap))
        + finrank k (LinearMap.ker (((χ complexConjugation : kˣ) : k) • u.dualMap - 1)) := eA'
  have hdual : finrank k (Module.Dual k M) = finrank k M := Subspace.dual_finrank_eq

  have t1 : (1 : Module.Dual k M →ₗ[k] Module.Dual k M) + u.dualMap = (1 + u).dualMap := by
    apply LinearMap.ext; intro f; apply LinearMap.ext; intro v
    simp [LinearMap.dualMap_apply]
  have t2 : u.dualMap - 1 = (u - 1).dualMap := by
    apply LinearMap.ext; intro f; apply LinearMap.ext; intro v
    simp [LinearMap.dualMap_apply]
  have t3 : (1 : Module.Dual k M →ₗ[k] Module.Dual k M) + (-1 : k) • u.dualMap
      = -((u - 1).dualMap) := by
    apply LinearMap.ext; intro f; apply LinearMap.ext; intro v
    simp [LinearMap.dualMap_apply]
    ring
  have t4 : (-1 : k) • u.dualMap - 1 = -((1 + u).dualMap) := by
    apply LinearMap.ext; intro f; apply LinearMap.ext; intro v
    simp [LinearMap.dualMap_apply]
    ring

  have dA' : finrank k (LinearMap.ker ((1 : Module.Dual k M →ₗ[k] Module.Dual k M)
          + ((χ complexConjugation : kˣ) : k) • u.dualMap))
        + finrank k (LinearMap.ker (((χ complexConjugation : kˣ) : k) • u.dualMap - 1))
      = finrank k (LinearMap.ker ((1 : M →ₗ[k] M) + u)) + finrank k (LinearMap.ker (u - 1)) := by
    rcases mul_self_eq_one_iff.mp hε2 with hε | hε
    · rw [hε, one_smul, t1, t2, finrank_ker_dualMap_eq, finrank_ker_dualMap_eq]
    · rw [hε, t3, t4, LinearMap.ker_neg, LinearMap.ker_neg, finrank_ker_dualMap_eq,
        finrank_ker_dualMap_eq, add_comm]
  rw [dA'] at eA'2
  show finrank k (groupCohomology A' 1) = finrank k (groupCohomology A 1)
  omega

end WnumArchH1Dual

open WnumArchH1Dual Rep.FiniteCyclicGroup in
theorem solution
    {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist χ))) := by
  classical
  have e := WnumArchH1Dual.finrank_H1_dualTwist_eq S M χ
  rw [Module.finrank_zero_of_subsingleton (R := k)
    (M := H1 (Rep.res (extArithLoc S (Sum.inl ())) M))] at e

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
  haveI : FiniteDimensional k (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist χ)) :=
    inferInstanceAs (FiniteDimensional k (Module.Dual k M))
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
  haveI := finiteDimensional_h1 (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist χ)) g hg
  exact Module.finrank_zero_iff.1 e

end S_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist
end P2MW
export P2MW.S_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist (solution)
