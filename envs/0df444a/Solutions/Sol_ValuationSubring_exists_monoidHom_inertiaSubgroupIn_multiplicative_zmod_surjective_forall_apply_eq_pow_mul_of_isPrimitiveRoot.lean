-- Prove2me | solution 1 for ValuationSubring.exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b5c03c9e-ae01-5a50-b90c-54454e14c442

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_rootsOfUnity_surjective_forall_apply_eq_mul_of_pow_eq_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open ValuationSubring in
theorem solution
    {r : ℕ} (hr : r.Prime) {m : ℕ} [NeZero m] (hrm : ¬ r ∣ m)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ m) :
    ∃ t : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod m),
      Function.Surjective t ∧
      ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (x : AlgebraicClosure ℚ), x ^ m = (r : AlgebraicClosure ℚ) →
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x = ζ ^ (Multiplicative.toAdd (t σ)).val * x := by
  classical
  obtain ⟨t, ht, hlaw⟩ :=
    ValuationSubring.exists_monoidHom_inertiaSubgroupIn_rootsOfUnity_surjective_forall_apply_eq_mul_of_pow_eq_of_not_dvd hr hrm A hA

  have hm0 : m ≠ 0 := NeZero.ne m
  let ζu : (AlgebraicClosure ℚ)ˣ := (hζ.isUnit hm0).unit
  have hζu : IsPrimitiveRoot ζu m := by
    rw [← IsPrimitiveRoot.coe_units_iff]; exact hζ

  let E₁ : ZMod m ≃+ Additive (Subgroup.zpowers ζu) := hζu.zmodEquivZPowers
  let F : Multiplicative (ZMod m) ≃* ↥(Subgroup.zpowers ζu) := AddEquiv.toMultiplicativeLeft E₁
  let E₂ : ↥(rootsOfUnity m (AlgebraicClosure ℚ)) ≃* ↥(Subgroup.zpowers ζu) := (MulEquiv.subgroupCongr hζu.zpowers_eq).symm
  let e : ↥(rootsOfUnity m (AlgebraicClosure ℚ)) ≃* Multiplicative (ZMod m) := E₂.trans F.symm

  have key : ∀ k : ZMod m, (((e.symm (Multiplicative.ofAdd k) : ↥(rootsOfUnity m (AlgebraicClosure ℚ))) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ζ ^ k.val := by
    intro k
    have h1 : e.symm (Multiplicative.ofAdd k) = E₂.symm (F (Multiplicative.ofAdd k)) := rfl
    have h2 : F (Multiplicative.ofAdd k) = Additive.toMul (E₁ k) := rfl
    have h3 : E₁ k = Additive.ofMul ⟨ζu ^ k.val, k.val, rfl⟩ := by
      conv_lhs => rw [← ZMod.natCast_zmod_val k]
      exact hζu.zmodEquivZPowers_apply_coe_nat k.val
    rw [h1, h2, h3]
    show (((⟨ζu ^ k.val, k.val, rfl⟩ : ↥(Subgroup.zpowers ζu)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ζ ^ k.val
    rw [Units.val_pow_eq_pow_val]
    rfl
  refine ⟨e.toMonoidHom.comp t, e.surjective.comp ht, fun σ x hx => ?_⟩
  rw [hlaw σ x hx]
  congr 1
  have hu : t σ = e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e (t σ)))) := by
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  conv_lhs => rw [hu]
  exact key _

end S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
end P2MW
export P2MW.S_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot (solution)
