-- Prove2me | solution 1 for PadicAlgCl.exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/660e1175-0edd-5c14-8247-d09022a2f5b6

import Mathlib
import Theorems.Thm_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IntermediateField

namespace P2M
namespace FrobPow

variable (q : ℕ) [Fact q.Prime]

set_option hygiene false in
local notation "Ω" => PadicAlgCl q

lemma setOf_pow_eq_one_eq_rootSet {K : Type*} [Field K] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    {x : Ω | x ^ n = 1} = ((X ^ n - C 1 : K[X])).rootSet Ω := by
  ext x
  rw [Polynomial.mem_rootSet, Set.mem_setOf_eq, and_iff_right (X_pow_sub_C_ne_zero hn 1)]
  simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]

lemma finiteDimensional_adjoin_setOf_pow_eq_one {K : Type*} [Field K] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    FiniteDimensional K (IntermediateField.adjoin K {x : Ω | x ^ n = 1}) := by
  have hfin : ({x : Ω | x ^ n = 1} : Set Ω).Finite := by
    rw [setOf_pow_eq_one_eq_rootSet q (K := K) n hn]; exact Polynomial.rootSet_finite _ _
  haveI : Finite ({x : Ω | x ^ n = 1} : Set Ω) := hfin.to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp only [eval₂_sub, eval₂_X_pow, map_one, eval₂_one, sub_eq_zero]
  exact hx

lemma normal_adjoin_setOf_pow_eq_one {K : Type*} [Field K] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    Normal K (IntermediateField.adjoin K {x : Ω | x ^ n = 1}) := by
  rw [setOf_pow_eq_one_eq_rootSet q (K := K) n hn]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := (X ^ n - C 1 : K[X]))
    (IsAlgClosed.splits _)
  exact Normal.of_isSplittingField (X ^ n - C 1 : K[X])

lemma pow_apply_eq_pow_pow {K : Type*} [Field K] [Algebra K Ω] {E : IntermediateField K Ω}
    (φ : E ≃ₐ[K] E) (n e : ℕ) (hφ : ∀ x : E, (x : Ω) ^ n = 1 → (φ x : Ω) = (x : Ω) ^ e) (j : ℕ) :
    ∀ x : E, (x : Ω) ^ n = 1 → ((φ ^ j) x : Ω) = (x : Ω) ^ (e ^ j) := by
  induction j with
  | zero => intro x _; rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | succ j ih =>
    intro x hx
    have hx' : ((φ x : E) : Ω) ^ n = 1 := by rw [hφ x hx, ← pow_mul, mul_comm, pow_mul, hx, one_pow]
    rw [pow_succ, AlgEquiv.mul_apply, ih (φ x) hx', hφ x hx, ← pow_mul, ← pow_succ']

end P2M.FrobPow

open P2M.FrobPow in
theorem solution (q : ℕ) [Fact q.Prime]
    (m : ℕ) (hm : ¬ q ∣ m) (σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    ∃ k : ℕ, ∀ x : PadicAlgCl q, x ^ m = 1 → σ x = x ^ (q ^ k) := by
  classical
  have hqP : q.Prime := Fact.out
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero q))

  set N : ℕ := Nat.totient m with hNdef
  have hN : 0 < N := Nat.totient_pos.mpr hm0
  have hcop : Nat.Coprime q m := (Nat.Prime.coprime_iff_not_dvd hqP).mpr hm
  have hmN : m ∣ q ^ N - 1 := by
    have h := (Nat.ModEq.pow_totient hcop).symm
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hqP.pos)).mp h
  have hn0 : 0 < q ^ N - 1 := by
    have := Nat.one_lt_pow hN.ne' hqP.one_lt
    omega

  set K₀ : IntermediateField ℚ_[q] (PadicAlgCl q) := ⊥ with hK₀
  set S : Set (PadicAlgCl q) := {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} with hS
  set E₀ : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.adjoin K₀ S with hE₀
  haveI : FiniteDimensional K₀ E₀ := finiteDimensional_adjoin_setOf_pow_eq_one q (K := K₀) _ hn0
  haveI : Normal K₀ E₀ := normal_adjoin_setOf_pow_eq_one q (K := K₀) _ hn0
  obtain ⟨φ₀, hgen, a, -, hφ₀⟩ :=
    IntermediateField.exists_generator_frobenius_adjoin_rootsOfUnity_padic q K₀ N hN

  have hσK₀ : ∀ k : K₀, σ.toRingEquiv (algebraMap K₀ (PadicAlgCl q) k) = algebraMap K₀ (PadicAlgCl q) k := by
    intro k
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp k.2
    change σ (k : PadicAlgCl q) = (k : PadicAlgCl q)
    rw [← hx, AlgEquiv.commutes]
  set σ₀ : PadicAlgCl q ≃ₐ[K₀] PadicAlgCl q := AlgEquiv.ofRingEquiv hσK₀ with hσ₀
  have hσ₀apply : ∀ x : PadicAlgCl q, σ₀ x = σ x := fun x => rfl

  have hfin₀ : IsOfFinOrder φ₀ := isOfFinOrder_of_finite φ₀
  obtain ⟨j, hj⟩ := (hfin₀.mem_powers_iff_mem_zpowers).mpr (hgen (AlgEquiv.restrictNormalHom E₀ σ₀))
  refine ⟨a * j, fun x hx => ?_⟩
  have hxS : x ^ (q ^ N - 1) = 1 := by
    obtain ⟨c, hc⟩ := hmN
    rw [hc, pow_mul, hx, one_pow]
  have hxE : x ∈ E₀ := IntermediateField.subset_adjoin K₀ S hxS
  have hres : ((AlgEquiv.restrictNormalHom E₀ σ₀ ⟨x, hxE⟩ : E₀) : PadicAlgCl q) = σ₀ x :=
    AlgEquiv.restrictNormal_commutes σ₀ E₀ ⟨x, hxE⟩
  rw [← hσ₀apply, ← hres, ← hj, pow_mul]
  exact pow_apply_eq_pow_pow q φ₀ (q ^ N - 1) (q ^ a) hφ₀ j ⟨x, hxE⟩ hxS

end S_PadicAlgCl_exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd
end P2MW
export P2MW.S_PadicAlgCl_exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd (solution)
