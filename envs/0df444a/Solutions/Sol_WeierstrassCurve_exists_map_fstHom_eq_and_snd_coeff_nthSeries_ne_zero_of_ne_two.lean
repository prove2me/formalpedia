-- Prove2me | solution 1 for WeierstrassCurve.exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/16eb9b4d-67d6-51a2-89f2-03ef6dbc99dc

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ G : FormalGroup (DualNumber k), G.toPowerSeries = E₁.formalGroupLawFixed →
        TrivSqZeroExt.snd (PowerSeries.coeff q (G.nthSeries q)) ≠ 0 := by
  classical
  obtain ⟨c, hc0, hF1⟩ := WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant q hq
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hqlt : q < q * q := by nlinarith

  have hck : (c : k) ≠ 0 := fun h =>
    hc0 ((ZMod.intCast_zmod_eq_zero_iff_dvd c q).mpr ((CharP.intCast_eq_zero_iff k q c).mp h))

  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance
  obtain ⟨u₀, hu₀, hq0⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) E₀.formalGroup q).mp hE₀
  have hH0 : E₀.hasseInvariant q = 0 := by
    have h1 := hF1 k E₀ E₀.isUnit_Δ E₀.formalGroup rfl
    rw [hq0, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hqlt)] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hck
  haveI : CharP (DualNumber k) q :=
    charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q

  obtain ⟨E₁, hE₁, hsnd⟩ := WeierstrassCurve.exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero q hq k E₀ hH0
  refine ⟨E₁, hE₁, fun G hG h => hsnd ?_⟩
  have hΔ₁ : IsUnit E₁.Δ := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    have : TrivSqZeroExt.fst E₁.Δ = E₀.Δ := by
      rw [← hE₁, WeierstrassCurve.map_Δ]; rfl
    rw [this]; exact E₀.isUnit_Δ
  have h2 := hF1 (DualNumber k) E₁ hΔ₁ G hG
  rw [h2] at h
  have : TrivSqZeroExt.snd ((c : DualNumber k) * E₁.hasseInvariant q) = (c : k) * TrivSqZeroExt.snd (E₁.hasseInvariant q) := by
    rw [TrivSqZeroExt.snd_mul]
    simp [TrivSqZeroExt.snd_intCast, TrivSqZeroExt.fst_intCast]
  rw [this] at h
  exact (mul_eq_zero.mp h).resolve_left hck

end S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero_of_ne_two (solution)
