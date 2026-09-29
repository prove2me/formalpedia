-- Prove2me | solution 1 for PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f5d21cde-8a54-5f00-8482-d1e1440b4041

import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped TensorProduct

namespace Ws47
namespace U1D

variable (p : ℕ) [Fact p.Prime]

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p]

theorem norm_natCast_p_pos : 0 < ‖((p : ℕ) : PadicAlgCl p)‖ := by
  rw [norm_natCast_p]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)

theorem norm_natCast_p_lt_one : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  rw [norm_natCast_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem exists_pow_mul_norm_le_one (x : PadicAlgCl p) :
    ∃ m : ℕ, ‖((p : ℕ) : PadicAlgCl p) ^ m * x‖ ≤ 1 := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < (‖x‖ + 1)⁻¹ from by positivity) (norm_natCast_p_lt_one p)
  refine ⟨m, ?_⟩
  rw [norm_mul, norm_pow]
  have hx : ‖x‖ < (‖x‖ + 1) := lt_add_one _
  by_cases h0 : ‖x‖ = 0
  · rw [h0, mul_zero]; exact zero_le_one
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    calc ‖((p : ℕ) : PadicAlgCl p)‖ ^ m * ‖x‖ ≤ (‖x‖ + 1)⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_right hm.le (norm_nonneg _)
      _ ≤ (‖x‖ + 1)⁻¹ * (‖x‖ + 1) := mul_le_mul_of_nonneg_left hx.le (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)

end Ws47.U1D

open Ws47.U1D in

theorem solution
    (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx0 : x ≠ 0)
    (hx : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι x = x) :
    ∃ n : ℤ, ‖x‖ = ‖(p : PadicAlgCl p)‖ ^ n := by
  classical
  obtain ⟨O, hOsub, hZp, hDVR, hirr, hnu, hiff, hfix⟩ :=
    PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p
  haveI : IsDiscreteValuationRing ↥O := hDVR

  obtain ⟨m, hm⟩ := exists_pow_mul_norm_le_one p x
  set y : PadicAlgCl p := ((p : ℕ) : PadicAlgCl p) ^ m * x with hy
  have hp0 : ((p : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hy0 : y ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hx0
  have hyint : y ∈ padicIntegers p := by
    rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]; exact hm
  have hyfix : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ y = y := by
    intro σ hσ
    rw [hy, map_mul, map_pow, map_natCast, hx σ hσ]
  have hyO : y ∈ O := hfix y hyint hyfix

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (show (⟨y, hyO⟩ : ↥O) ≠ 0 from fun h => hy0 (congrArg Subtype.val h)) hirr
  have hunorm : ‖((u : ↥O) : PadicAlgCl p)‖ = 1 := by
    have hle : ‖((u : ↥O) : PadicAlgCl p)‖ ≤ 1 := by
      have := hOsub (u : ↥O).2
      rw [SetLike.mem_coe, mem_padicIntegers_iff] at this
      exact_mod_cast this
    have hnlt : ¬ ‖((u : ↥O) : PadicAlgCl p)‖₊ < 1 := fun h => hnu _ h u.isUnit
    rw [not_lt, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm] at hnlt
    exact le_antisymm hle hnlt
  have hyval : y = ((u : ↥O) : PadicAlgCl p) * ((p : ℕ) : PadicAlgCl p) ^ n := by
    have := congrArg (Subtype.val : ↥O → PadicAlgCl p) hu
    simpa using this
  have hynorm : ‖y‖ = ‖((p : ℕ) : PadicAlgCl p)‖ ^ n := by
    rw [hyval, norm_mul, hunorm, one_mul, norm_pow]

  refine ⟨(n : ℤ) - m, ?_⟩
  have hpn : ‖((p : ℕ) : PadicAlgCl p)‖ ≠ 0 := (norm_natCast_p_pos p).ne'
  have : ‖x‖ = ‖y‖ / ‖((p : ℕ) : PadicAlgCl p)‖ ^ m := by
    rw [hy, norm_mul, norm_pow, mul_comm, mul_div_assoc, div_self (pow_ne_zero _ hpn), mul_one]
  rw [this, hynorm, zpow_sub₀ hpn, zpow_natCast, zpow_natCast]

end S_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
end P2MW
export P2MW.S_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self (solution)
