-- Prove2me | solution 1 for WeierstrassCurve.mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/635b3ece-1914-5f8b-a978-e0c68493f691

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_WeierstrassCurve_natDegree_hasseInvariant_jFamily
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero.WeierstrassCurve ModularCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ map map_b₂ b₂ twoTorsionPolynomial coe_Δ' map_b₆ b₆ b₈ Δ c₄ j b₄ hasseInvariant natDegree_hasseInvariant_jFamily hasseInvariant_pow_mul_delta_pow_eq_of_j_eq"
namespace DKfam
p2m_open "WeierstrassCurve"

variable {R S : Type*} [CommRing R] [CommRing S]

theorem hasseInvariant_map (q : ℕ) (W : WeierstrassCurve R) (φ : R →+* S) :
    (W.map φ).hasseInvariant q = φ (W.hasseInvariant q) := by
  unfold hasseInvariant
  have h : (W.map φ).twoTorsionPolynomial.toPoly = W.twoTorsionPolynomial.toPoly.map φ := by
    rw [← Cubic.map_toPoly]
    simp only [twoTorsionPolynomial, Cubic.map, map_b₂, map_b₄, map_b₆, map_ofNat, map_mul]
  rw [h, ← Polynomial.map_pow, Polynomial.coeff_map]

theorem jFamily_map_eval {k : Type*} [Field k] (t₀ : k) :
    (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k)).map (Polynomial.evalRingHom t₀) =
      (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) := by
  simp [WeierstrassCurve.map]

theorem eval_hasse_jFamily {k : Type*} [Field k] (q : ℕ) (t₀ : k) :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval t₀ =
      WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) := by
  rw [← Polynomial.coe_evalRingHom, ← hasseInvariant_map, jFamily_map_eval]

theorem c₄_fibre {k : Type*} [Field k] (t₀ : k) :
    (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k).c₄ = 1 + 1728 * t₀ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

theorem Δ_fibre {k : Type*} [Field k] (t₀ : k) :
    (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k).Δ = t₀ * (1 + 1728 * t₀) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

theorem isElliptic_fibre {k : Type*} [Field k] {t₀ : k} (h0 : t₀ ≠ 0) (hc : 1 + 1728 * t₀ ≠ 0) :
    (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k).IsElliptic :=
  ⟨by rw [Δ_fibre]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero h0 (pow_ne_zero 2 hc))⟩

theorem j_fibre {k : Type*} [Field k] {t₀ : k} (h0 : t₀ ≠ 0) (hc : 1 + 1728 * t₀ ≠ 0) :
    @WeierstrassCurve.j _ _ (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) (isElliptic_fibre h0 hc) = 1728 + t₀⁻¹ := by
  letI := isElliptic_fibre h0 hc
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', Δ_fibre, c₄_fibre]
  field_simp
  ring

end WeierstrassCurve.DKfam

open WeierstrassCurve.DKfam in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (t₀ : k) (h : (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval t₀ = 0)
    (hc : 1 + 1728 * t₀ ≠ 0) :
    t₀ ≠ 0 ∧ 1728 + t₀⁻¹ ∈ ssJSet q k := by
  have hp : q.Prime := Fact.out

  have h0 : t₀ ≠ 0 := by
    rintro rfl
    rw [← Polynomial.coeff_zero_eq_eval_zero, (WeierstrassCurve.natDegree_hasseInvariant_jFamily q hq k).2] at h
    exact one_ne_zero h
  refine ⟨h0, ?_⟩

  letI hE := isElliptic_fibre h0 hc
  have hH : WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) = 0 := by
    rw [← eval_hasse_jFamily]; exact h
  have hj := j_fibre h0 hc

  rw [ssJSet_eq_ssJSetHasse q (by omega) k]
  intro W' _ hW'
  have hcmp := WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq q
    (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) W' (hj.trans hW'.symm)
  rw [hH, zero_pow (by norm_num), zero_mul] at hcmp
  have hΔ : (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k).Δ ≠ 0 := by
    rw [Δ_fibre]; exact mul_ne_zero h0 (pow_ne_zero 2 hc)
  rcases mul_eq_zero.mp hcmp.symm with h12 | hΔ0
  · exact pow_eq_zero_iff (by norm_num) |>.mp h12
  · exact absurd (pow_eq_zero_iff (by omega) |>.mp hΔ0) hΔ

end S_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_mem_ssJSet_of_eval_hasseInvariant_jFamily_eq_zero (solution)
