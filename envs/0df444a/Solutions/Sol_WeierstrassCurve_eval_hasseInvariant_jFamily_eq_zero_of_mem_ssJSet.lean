-- Prove2me | solution 1 for WeierstrassCurve.eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bca1ec28-2210-560d-a167-df034ab72a16

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet.WeierstrassCurve ModularCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ map map_b₂ b₂ twoTorsionPolynomial coe_Δ' map_b₆ b₆ b₈ Δ c₄ j b₄ hasseInvariant"
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

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ map map_b₂ b₂ twoTorsionPolynomial coe_Δ' map_b₆ b₆ b₈ Δ c₄ j b₄ hasseInvariant"
namespace DK2a
p2m_open "WeierstrassCurve"

theorem hasse_cusp (q : ℕ) (hp : q.Prime) (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q]
    (t₀ : k) (hc : 1 + 1728 * t₀ = 0) :
    WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) = 0 := by
  set n := (q - 1) / 2 with hn
  have hqn : q - 1 = 2 * n := by obtain ⟨r, hr⟩ := hp.even_sub_one (by omega); omega
  have hf : (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k).twoTorsionPolynomial.toPoly =
      C (4 : k) * (Polynomial.X + C (-144 * t₀)) ^ 3 := by
    simp only [twoTorsionPolynomial, Cubic.toPoly, b₂, b₄, b₆]
    have hc' : 1 + 1728 * C t₀ = (0 : Polynomial k) := by
      rw [← map_ofNat C 1728, ← map_mul, ← map_one C, ← map_add, hc, map_zero]
    simp only [map_mul, map_neg, map_ofNat, map_add, map_pow, map_one, map_zero]
    linear_combination (Polynomial.X ^ 2 - 144 * C t₀ * Polynomial.X - 4 * C t₀ * (1 - 1728 * C t₀)) * hc'
  unfold hasseInvariant
  rw [hf, hqn, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), mul_pow, ← map_pow, Polynomial.coeff_C_mul, ← pow_mul,
    Polynomial.coeff_X_add_C_pow]

  have hdvd : q ∣ (3 * n).choose (2 * n) := by
    have hle : 2 * n ≤ 3 * n := by omega
    have hprod := Nat.choose_mul_factorial_mul_factorial hle
    have h3 : q ∣ (3 * n).factorial := hp.dvd_factorial.mpr (by omega)
    rw [← hprod, show 3 * n - 2 * n = n by omega] at h3
    rcases hp.dvd_mul.mp h3 with h12 | hn'
    · rcases hp.dvd_mul.mp h12 with hC | h2n
      · exact hC
      · exact absurd (hp.dvd_factorial.mp h2n) (by omega)
    · exact absurd (hp.dvd_factorial.mp hn') (by omega)
  rw [show 3 * n = 3 * n from rfl, (CharP.cast_eq_zero_iff k q _).mpr hdvd, mul_zero, mul_zero]

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h1728 : a ≠ 1728) :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval
      (a - 1728)⁻¹ = 0 := by
  have hp : q.Prime := Fact.out
  set t₀ := (a - 1728)⁻¹ with ht₀
  have hsub : a - 1728 ≠ 0 := sub_ne_zero.mpr h1728
  rw [DKfam.eval_hasse_jFamily]
  by_cases ha0 : a = 0
  ·
    have h1728' : (1728 : k) ≠ 0 := by
      intro h; apply hsub; rw [ha0, h, sub_zero]
    apply hasse_cusp q hp hq k t₀
    rw [ht₀, ha0, zero_sub, inv_neg, mul_neg, mul_inv_cancel₀ h1728', add_neg_cancel]
  ·
    have h0 : t₀ ≠ 0 := inv_ne_zero hsub
    have hc : 1 + 1728 * t₀ ≠ 0 := by
      rw [ht₀]
      intro h
      apply ha0
      have := congrArg (· * (a - 1728)) h
      simp only [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hsub, mul_one, zero_mul] at this
      linear_combination this
    letI hE := DKfam.isElliptic_fibre h0 hc
    have hj : WeierstrassCurve.j (⟨1, 0, 0, -36 * t₀, -t₀⟩ : WeierstrassCurve k) = a := by
      rw [DKfam.j_fibre h0 hc, ht₀, inv_inv]; ring
    rw [ssJSet_eq_ssJSetHasse q (by omega) k] at ha
    exact ha _ hj

end WeierstrassCurve.DK2a

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ModularCurve.ssJSet q k) (h1728 : a ≠ 1728) :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).eval (a - 1728)⁻¹ = 0 :=
  WeierstrassCurve.DK2a.main q hq k a ha h1728

end S_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet
end P2MW
export P2MW.S_WeierstrassCurve_eval_hasseInvariant_jFamily_eq_zero_of_mem_ssJSet (solution)
