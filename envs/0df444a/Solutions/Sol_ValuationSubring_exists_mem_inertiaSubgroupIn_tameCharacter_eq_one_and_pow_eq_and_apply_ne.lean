-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6d1e76ea-4ffb-5625-a397-bcbd010b03eb

import Mathlib
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
import Theorems.Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_tameCharacter_pow_left
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

namespace R1AF8Card2

theorem tameCharacter_eq_one_of_apply_eq (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτπ : τ π = π) :
    P.tameCharacter π τ = 1 := by
  have h1 : τ π / π = 1 := by rw [hτπ, div_self hπ0]
  unfold ValuationSubring.tameCharacter
  rw [dif_pos (by rw [h1]; exact P.one_mem)]
  have : (⟨τ π / π, by rw [h1]; exact P.one_mem⟩ : P) = 1 := Subtype.ext h1
  rw [this, map_one]

theorem tameCharacter_one (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0) : P.tameCharacter π 1 = 1 :=
  tameCharacter_eq_one_of_apply_eq P π hπ0 1 rfl

theorem tameCharacter_pow_right (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (k : ℕ) :
    P.tameCharacter π (σ ^ k) = P.tameCharacter π σ ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, tameCharacter_one P π hπ0]
  | succ k ih =>
      rw [pow_succ', ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P π hπ0 hσ, ih,
        ← pow_succ']

theorem not_dvd_mul_sq_sub_one {q lam : ℕ} (hq : q.Prime) (hlam : lam.Prime) (hqlam : q ≠ lam) :
    ¬ q ∣ lam * (q ^ 2 - 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h2
  · exact hqlam ((Nat.prime_dvd_prime_iff_eq hq hlam).1 h1)
  · have hq2 : q ∣ q ^ 2 := dvd_pow_self q two_ne_zero
    have h1le : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    have : q ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub hq2 h2
    rw [Nat.sub_sub_self h1le, Nat.dvd_one] at this
    exact hq.one_lt.ne' this

end R1AF8Card2

open R1AF8Card2 in
theorem solution
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π τ = 1 ∧
      ∃ r : AlgebraicClosure ℚ, r ^ lam = π ∧ τ r ≠ r := by
  have hq : q.Prime := Fact.out
  have hlam : lam.Prime := Fact.out

  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq π hlam.pos
  have hrq : r ^ (lam * (q ^ 2 - 1)) = (q : AlgebraicClosure ℚ) := by rw [pow_mul, hr, hπ]
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_pos hlam.pos (Nat.sub_pos_of_lt
      (by nlinarith [hq.two_le] : 1 < q ^ 2))).ne'] at hrq
    exact hq0 hrq.symm

  obtain ⟨σ, hσI, hprim⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter P hq hP
      (not_dvd_mul_sq_sub_one hq hlam hqlam) hrq
  refine ⟨σ ^ (q ^ 2 - 1), pow_mem hσI _, ?_, r, hr, ?_⟩
  ·
    rw [← hr, ValuationSubring.tameCharacter_pow_left, tameCharacter_pow_right P r hr0 hσI, ← pow_mul,
      mul_comm, hprim.pow_eq_one]
  ·
    intro hfix
    have h1 : P.tameCharacter r (σ ^ (q ^ 2 - 1)) = 1 :=
      tameCharacter_eq_one_of_apply_eq P r hr0 _ hfix
    rw [tameCharacter_pow_right P r hr0 hσI, hprim.pow_eq_one_iff_dvd] at h1
    have hpos : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith [hq.two_le] : 1 < q ^ 2)
    have hle : lam * (q ^ 2 - 1) ≤ 1 * (q ^ 2 - 1) := by
      rw [one_mul]; exact Nat.le_of_dvd hpos h1
    have : lam ≤ 1 := Nat.le_of_mul_le_mul_right hle hpos
    exact absurd this (not_le.2 hlam.one_lt)

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne (solution)
