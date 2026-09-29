-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5aa37a52-4ab5-51c2-8322-8b62667dc52b

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (s : AlgebraicClosure ℚ) (hs : s ^ 2 = (p : AlgebraicClosure ℚ)) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ ∧ τ s = -s := by
  haveI : Fact p.Prime := ⟨hp⟩

  have hA₀ : (padicPlace p).LiesOverPrime p := by
    change ((p : ℕ) : AlgebraicClosure ℚ) ∈ (padicPlace p).nonunits
    rw [padicPlace, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap]
    right
    change ¬ (padicEmbedding p ((p : AlgebraicClosure ℚ)⁻¹) ∈ padicIntegers p)
    rw [mem_padicIntegers_iff, map_inv₀, map_natCast, nnnorm_inv, not_le,
      ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, ← NNReal.coe_lt_coe, NNReal.coe_one, NNReal.coe_inv, coe_nnnorm]
    change 1 < ‖((p : ℚ_[p]) : PadicAlgCl p)‖⁻¹
    rw [PadicAlgCl.norm_extends, Padic.norm_p, inv_inv]
    exact_mod_cast hp.one_lt

  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp A (padicPlace p) hA hA₀

  have hgs : (g s) ^ 2 = (p : AlgebraicClosure ℚ) := by rw [← map_pow, hs, map_natCast]
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  obtain ⟨t, ht, hne⟩ := ExtCitation.LocalLevel.exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime p le_rfl hp2' hgs
  set τ₀ := localGaloisToGlobal p t with hτ₀
  have hneg : τ₀ (g s) = -(g s) := by
    have h2 : (τ₀ (g s)) ^ 2 = (g s) ^ 2 := by rw [← map_pow, hgs, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact absurd h hne
    · exact h
  refine ⟨g⁻¹ * τ₀ * g, ?_, ?_⟩
  · exact ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul A g (by rw [hg]; exact ht)
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hneg, map_neg, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime (solution)
