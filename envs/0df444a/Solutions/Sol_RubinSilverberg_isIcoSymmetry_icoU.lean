-- Prove2me | solution 1 for RubinSilverberg.isIcoSymmetry_icoU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/55db59f9-1d0f-5e52-9484-3a53477b1122

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Theorems.Thm_RubinSilverberg_kleinVHom_atomsU
import Theorems.Thm_RubinSilverberg_kleinHHom_atomsU
import Theorems.Thm_RubinSilverberg_kleinTHom_atomsU
import Theorems.Thm_RubinSilverberg_icoU_datumG
import Theorems.Thm_RubinSilverberg_icoU_datumGam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_isIcoSymmetry_icoU

p2m_open "RubinSilverberg P2MW.S_RubinSilverberg_isIcoSymmetry_icoU.RubinSilverberg"

namespace RubinSilverberg
p2m_export "RubinSilverberg" "kleinV kleinT kleinVHom kleinHHom kleinTHom rsBeta rsGamma moeb moebDen sqrtFive icoU IsIcoSymmetry kleinVHom_atomsU kleinHHom_atomsU kleinTHom_atomsU icoU_datumG icoU_datumGam"
p2m_open "RubinSilverberg"
section icoU_pack
variable {K : Type*} [Field K]

private theorem pk_atom_relations (ζ : K) (hζ : IsPrimitiveRoot ζ 5) :
    (ζ - ζ ^ 4) * (ζ ^ 2 - ζ ^ 3) = -sqrtFive ζ ∧
    2 * (ζ - ζ ^ 4) ^ 2 = -5 - sqrtFive ζ ∧
    2 * (ζ ^ 2 - ζ ^ 3) ^ 2 = sqrtFive ζ - 5 ∧
    sqrtFive ζ ^ 2 = 5 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using this
  unfold sqrtFive
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination ((-1 : K)*ζ + (1 : K)*ζ^2) * h5
  · linear_combination ((-4 : K) + (2 : K)*ζ^3) * h5 + (1 : K) * hΦ
  · linear_combination ((-4 : K) + (2 : K)*ζ) * h5 + (1 : K) * hΦ
  · linear_combination ((4 : K) + (-1 : K)*ζ + (-2 : K)*ζ^2 + (1 : K)*ζ^3) * h5 + (-1 : K) * hΦ

private theorem pk_sqrtFive_sq (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : sqrtFive ζ ^ 2 = 5 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hs : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    simpa [Finset.sum_range_succ] using hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
  unfold sqrtFive
  linear_combination (ζ ^ 3 - 2 * ζ ^ 2 - ζ + 4) * h5 - hs

private theorem pk_icoU_det [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : (icoU ζ).det = 1 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hs : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    simpa [Finset.sum_range_succ] using hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
  have hM : Matrix.det !![-(ζ - ζ ^ 4), ζ ^ 2 - ζ ^ 3; ζ ^ 2 - ζ ^ 3, ζ - ζ ^ 4] = 5 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (4 - ζ - ζ ^ 3) * h5 - hs
  have hsq := pk_sqrtFive_sq ζ hζ
  have hs0 : sqrtFive ζ ≠ 0 := by
    intro h0; rw [h0] at hsq; norm_num at hsq
  unfold icoU
  rw [Matrix.det_smul, hM, Fintype.card_fin]
  field_simp
  linear_combination -hsq

private theorem pk_kleinVHom_smul (c n d : K) : kleinVHom (c * n) (c * d) = c ^ 12 * kleinVHom n d := by
  unfold kleinVHom; ring

private theorem pk_kleinHHom_smul (c n d : K) : kleinHHom (c * n) (c * d) = c ^ 20 * kleinHHom n d := by
  unfold kleinHHom; ring

private theorem pk_kleinTHom_smul (c n d : K) : kleinTHom (c * n) (c * d) = c ^ 30 * kleinTHom n d := by
  unfold kleinTHom; ring

private theorem pk_kleinVHom_one (n : K) : kleinVHom n 1 = kleinV n := by
  unfold kleinVHom kleinV; ring

private theorem pk_kleinTHom_one (n : K) : kleinTHom n 1 = kleinT n := by
  unfold kleinTHom kleinT; ring

private theorem pk_reduce_beta [CharZero K] (u N D cT cV cG a b : K)
    (hD : D ≠ 0) (hVu : kleinV u ≠ 0) (hcV : cV ≠ 0)
    (hT : kleinTHom N D = cT * kleinT u)
    (hV : kleinVHom N D = cV * kleinV u)
    (hG : (57 * N ^ 15 - 247 * N ^ 10 * D ^ 5 - 171 * N ^ 5 * D ^ 10 - D ^ 15) * D ^ 4
      = cG * (a * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1)
          + b * (u ^ 4 * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57))))
    (hc : cT * cG = cV ^ 4) :
    D * rsBeta (N / D) = a * rsBeta u + b * rsGamma u := by
  have h144 : (144 : K) ≠ 0 := by norm_num
  have eVu : kleinV u = u * (u ^ 10 + 11 * u ^ 5 - 1) := by unfold kleinV; ring
  have eVND : kleinVHom N D = N * D * (N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10) := by unfold kleinVHom; ring
  have hu : u ≠ 0 ∧ u ^ 10 + 11 * u ^ 5 - 1 ≠ 0 := mul_ne_zero_iff.mp (eVu ▸ hVu)
  have hVN : N * D * (N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10) ≠ 0 := by
    rw [← eVND, hV]; exact mul_ne_zero hcV hVu
  have hN : N ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hVN).1).1
  have hF : N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10 ≠ 0 := (mul_ne_zero_iff.mp hVN).2
  have E8 : N * D * (N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10) = cV * (u * (u ^ 10 + 11 * u ^ 5 - 1)) := by
    rw [← eVND, ← eVu]; exact hV
  have E4 : kleinT (N / D) * D ^ 30 = cT * kleinT u := by
    rw [← hT]; unfold kleinT kleinTHom; field_simp
  have E5 : (57 * (N / D) ^ 15 - 247 * (N / D) ^ 10 - 171 * (N / D) ^ 5 - 1) * D ^ 15
      = 57 * N ^ 15 - 247 * N ^ 10 * D ^ 5 - 171 * N ^ 5 * D ^ 10 - D ^ 15 := by
    field_simp
  have E6 : ((N / D) ^ 10 + 11 * (N / D) ^ 5 - 1) * D ^ 10 = N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10 := by
    field_simp
  have E7 : N / D * D = N := div_mul_cancel₀ N hD
  set w := N / D with hw
  have hw0 : w ≠ 0 := div_ne_zero hN hD
  have hfw : w ^ 10 + 11 * w ^ 5 - 1 ≠ 0 := by
    intro h; apply hF; rw [← E6, h, zero_mul]
  have E1 : rsBeta u * (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)
      = kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1) := by
    unfold rsBeta
    exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h144 (pow_ne_zero _ hu.1)) (pow_ne_zero _ hu.2))
  have E2 : rsGamma u * (144 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)
      = kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) := by
    unfold rsGamma
    exact div_mul_cancel₀ _ (mul_ne_zero h144 (pow_ne_zero _ hu.2))
  have E3 : rsBeta w * (144 * w ^ 4 * (w ^ 10 + 11 * w ^ 5 - 1) ^ 4)
      = kleinT w * (57 * w ^ 15 - 247 * w ^ 10 - 171 * w ^ 5 - 1) := by
    unfold rsBeta
    exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h144 (pow_ne_zero _ hw0)) (pow_ne_zero _ hfw))
  have hM : 144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4 * cV ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h144 (pow_ne_zero _ hu.1)) (pow_ne_zero _ hu.2))
      (pow_ne_zero _ hcV)
  apply mul_right_cancel₀ hM
  linear_combination ((144 : K)*(rsBeta w)*D*cV^3*u^3 + (-4752 : K)*(rsBeta w)*D*cV^3*u^8 + (51840 : K)*(rsBeta w)*D*cV^3*u^13 + (-182160 : K)*(rsBeta w)*D*cV^3*u^18 + (-51840 : K)*(rsBeta w)*D*cV^3*u^23 + (-4752 : K)*(rsBeta w)*D*cV^3*u^28 + (-144 : K)*(rsBeta w)*D*cV^3*u^33 + (144 : K)*(rsBeta w)*N*D^12*cV^2*u^2 + (-3168 : K)*(rsBeta w)*N*D^12*cV^2*u^7 + (17136 : K)*(rsBeta w)*N*D^12*cV^2*u^12 + (3168 : K)*(rsBeta w)*N*D^12*cV^2*u^17 + (144 : K)*(rsBeta w)*N*D^12*cV^2*u^22 + (144 : K)*(rsBeta w)*N^2*D^23*cV*u + (-1584 : K)*(rsBeta w)*N^2*D^23*cV*u^6 + (-144 : K)*(rsBeta w)*N^2*D^23*cV*u^11 + (144 : K)*(rsBeta w)*N^3*D^34 + (-1584 : K)*(rsBeta w)*N^6*D^7*cV^2*u^2 + (34848 : K)*(rsBeta w)*N^6*D^7*cV^2*u^7 + (-188496 : K)*(rsBeta w)*N^6*D^7*cV^2*u^12 + (-34848 : K)*(rsBeta w)*N^6*D^7*cV^2*u^17 + (-1584 : K)*(rsBeta w)*N^6*D^7*cV^2*u^22 + (-3168 : K)*(rsBeta w)*N^7*D^18*cV*u + (34848 : K)*(rsBeta w)*N^7*D^18*cV*u^6 + (3168 : K)*(rsBeta w)*N^7*D^18*cV*u^11 + (-4752 : K)*(rsBeta w)*N^8*D^29 + (-144 : K)*(rsBeta w)*N^11*D^2*cV^2*u^2 + (3168 : K)*(rsBeta w)*N^11*D^2*cV^2*u^7 + (-17136 : K)*(rsBeta w)*N^11*D^2*cV^2*u^12 + (-3168 : K)*(rsBeta w)*N^11*D^2*cV^2*u^17 + (-144 : K)*(rsBeta w)*N^11*D^2*cV^2*u^22 + (17136 : K)*(rsBeta w)*N^12*D^13*cV*u + (-188496 : K)*(rsBeta w)*N^12*D^13*cV*u^6 + (-17136 : K)*(rsBeta w)*N^12*D^13*cV*u^11 + (51840 : K)*(rsBeta w)*N^13*D^24 + (3168 : K)*(rsBeta w)*N^17*D^8*cV*u + (-34848 : K)*(rsBeta w)*N^17*D^8*cV*u^6 + (-3168 : K)*(rsBeta w)*N^17*D^8*cV*u^11 + (-182160 : K)*(rsBeta w)*N^18*D^19 + (144 : K)*(rsBeta w)*N^22*D^3*cV*u + (-1584 : K)*(rsBeta w)*N^22*D^3*cV*u^6 + (-144 : K)*(rsBeta w)*N^22*D^3*cV*u^11 + (-51840 : K)*(rsBeta w)*N^23*D^14 + (-4752 : K)*(rsBeta w)*N^28*D^9 + (-144 : K)*(rsBeta w)*N^33*D^4) * E8 + ((-144 : K)*(rsBeta w)*N^3*D^45 + (6336 : K)*(rsBeta w)*N^8*D^40 + (-103968 : K)*(rsBeta w)*N^13*D^35 + (747648 : K)*(rsBeta w)*N^18*D^30 + (-1900080 : K)*(rsBeta w)*N^23*D^25 + (-747648 : K)*(rsBeta w)*N^28*D^20 + (-103968 : K)*(rsBeta w)*N^33*D^15 + (-6336 : K)*(rsBeta w)*N^38*D^10 + (-144 : K)*(rsBeta w)*N^43*D^5 + (-144 : K)*(rsBeta w)*w*N^2*D^46 + (6336 : K)*(rsBeta w)*w*N^7*D^41 + (-103968 : K)*(rsBeta w)*w*N^12*D^36 + (747648 : K)*(rsBeta w)*w*N^17*D^31 + (-1900080 : K)*(rsBeta w)*w*N^22*D^26 + (-747648 : K)*(rsBeta w)*w*N^27*D^21 + (-103968 : K)*(rsBeta w)*w*N^32*D^16 + (-6336 : K)*(rsBeta w)*w*N^37*D^11 + (-144 : K)*(rsBeta w)*w*N^42*D^6 + (-144 : K)*(rsBeta w)*w^2*N*D^47 + (6336 : K)*(rsBeta w)*w^2*N^6*D^42 + (-103968 : K)*(rsBeta w)*w^2*N^11*D^37 + (747648 : K)*(rsBeta w)*w^2*N^16*D^32 + (-1900080 : K)*(rsBeta w)*w^2*N^21*D^27 + (-747648 : K)*(rsBeta w)*w^2*N^26*D^22 + (-103968 : K)*(rsBeta w)*w^2*N^31*D^17 + (-6336 : K)*(rsBeta w)*w^2*N^36*D^12 + (-144 : K)*(rsBeta w)*w^2*N^41*D^7 + (-144 : K)*(rsBeta w)*w^3*D^48 + (6336 : K)*(rsBeta w)*w^3*N^5*D^43 + (-103968 : K)*(rsBeta w)*w^3*N^10*D^38 + (747648 : K)*(rsBeta w)*w^3*N^15*D^33 + (-1900080 : K)*(rsBeta w)*w^3*N^20*D^28 + (-747648 : K)*(rsBeta w)*w^3*N^25*D^23 + (-103968 : K)*(rsBeta w)*w^3*N^30*D^18 + (-6336 : K)*(rsBeta w)*w^3*N^35*D^13 + (-144 : K)*(rsBeta w)*w^3*N^40*D^8) * E7 + ((576 : K)*(rsBeta w)*w^4*D^39 + (-9504 : K)*(rsBeta w)*w^4*N^5*D^34 + (68832 : K)*(rsBeta w)*w^4*N^10*D^29 + (-178992 : K)*(rsBeta w)*w^4*N^15*D^24 + (-51696 : K)*(rsBeta w)*w^4*N^20*D^19 + (-4752 : K)*(rsBeta w)*w^4*N^25*D^14 + (-144 : K)*(rsBeta w)*w^4*N^30*D^9 + (-9504 : K)*(rsBeta w)*w^9*D^39 + (69696 : K)*(rsBeta w)*w^9*N^5*D^34 + (-185328 : K)*(rsBeta w)*w^9*N^10*D^29 + (-34848 : K)*(rsBeta w)*w^9*N^15*D^24 + (-1584 : K)*(rsBeta w)*w^9*N^20*D^19 + (68832 : K)*(rsBeta w)*w^14*D^39 + (-185328 : K)*(rsBeta w)*w^14*N^5*D^34 + (-34272 : K)*(rsBeta w)*w^14*N^10*D^29 + (-3168 : K)*(rsBeta w)*w^14*N^15*D^24 + (-144 : K)*(rsBeta w)*w^14*N^20*D^19 + (-178992 : K)*(rsBeta w)*w^19*D^39 + (-34848 : K)*(rsBeta w)*w^19*N^5*D^34 + (-3168 : K)*(rsBeta w)*w^19*N^10*D^29 + (-51696 : K)*(rsBeta w)*w^24*D^39 + (-1584 : K)*(rsBeta w)*w^24*N^5*D^34 + (-144 : K)*(rsBeta w)*w^24*N^10*D^29 + (-4752 : K)*(rsBeta w)*w^29*D^39 + (-144 : K)*(rsBeta w)*w^34*D^39) * E6 + ((1 : K)*D^49) * E3 + ((-1 : K)*D^19 + (-171 : K)*w^5*D^19 + (-247 : K)*w^10*D^19 + (57 : K)*w^15*D^19) * E4 + ((1 : K)*(kleinT u)*D^4*cT) * E5 + ((1 : K)*(kleinT u)*cT) * hG + ((57 : K)*(kleinT u)*b*u^4 + (247 : K)*(kleinT u)*b*u^9 + (-171 : K)*(kleinT u)*b*u^14 + (1 : K)*(kleinT u)*b*u^19 + (-1 : K)*(kleinT u)*a + (-171 : K)*(kleinT u)*a*u^5 + (-247 : K)*(kleinT u)*a*u^10 + (57 : K)*(kleinT u)*a*u^15) * hc + ((-1 : K)*cV^4*a) * E1 + ((-1 : K)*cV^4*b*u^4) * E2

private theorem pk_reduce_gamma [CharZero K] (u N D cT cV cG a b : K)
    (hD : D ≠ 0) (hVu : kleinV u ≠ 0) (hcV : cV ≠ 0)
    (hT : kleinTHom N D = cT * kleinT u)
    (hV : kleinVHom N D = cV * kleinV u)
    (hG : (N ^ 15 - 171 * N ^ 10 * D ^ 5 + 247 * N ^ 5 * D ^ 10 + 57 * D ^ 15) * N ^ 4
      = cG * (a * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1)
          + b * (u ^ 4 * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57))))
    (hc : cT * cG = cV ^ 4) :
    D * rsGamma (N / D) = a * rsBeta u + b * rsGamma u := by
  have h144 : (144 : K) ≠ 0 := by norm_num
  have eVu : kleinV u = u * (u ^ 10 + 11 * u ^ 5 - 1) := by unfold kleinV; ring
  have eVND : kleinVHom N D = N * D * (N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10) := by unfold kleinVHom; ring
  have hu : u ≠ 0 ∧ u ^ 10 + 11 * u ^ 5 - 1 ≠ 0 := mul_ne_zero_iff.mp (eVu ▸ hVu)
  have hVN : N * D * (N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10) ≠ 0 := by
    rw [← eVND, hV]; exact mul_ne_zero hcV hVu
  have hN : N ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hVN).1).1
  have hF : N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10 ≠ 0 := (mul_ne_zero_iff.mp hVN).2
  have E8 : N * D * (N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10) = cV * (u * (u ^ 10 + 11 * u ^ 5 - 1)) := by
    rw [← eVND, ← eVu]; exact hV
  have E4 : kleinT (N / D) * D ^ 30 = cT * kleinT u := by
    rw [← hT]; unfold kleinT kleinTHom; field_simp
  have E5 : ((N / D) ^ 15 - 171 * (N / D) ^ 10 + 247 * (N / D) ^ 5 + 57) * D ^ 15
      = N ^ 15 - 171 * N ^ 10 * D ^ 5 + 247 * N ^ 5 * D ^ 10 + 57 * D ^ 15 := by
    field_simp
  have E6 : ((N / D) ^ 10 + 11 * (N / D) ^ 5 - 1) * D ^ 10 = N ^ 10 + 11 * N ^ 5 * D ^ 5 - D ^ 10 := by
    field_simp
  have E7 : N / D * D = N := div_mul_cancel₀ N hD
  set w := N / D with hw
  have hw0 : w ≠ 0 := div_ne_zero hN hD
  have hfw : w ^ 10 + 11 * w ^ 5 - 1 ≠ 0 := by
    intro h; apply hF; rw [← E6, h, zero_mul]
  have E1 : rsBeta u * (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)
      = kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1) := by
    unfold rsBeta
    exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h144 (pow_ne_zero _ hu.1)) (pow_ne_zero _ hu.2))
  have E2 : rsGamma u * (144 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)
      = kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) := by
    unfold rsGamma
    exact div_mul_cancel₀ _ (mul_ne_zero h144 (pow_ne_zero _ hu.2))
  have E3 : rsGamma w * (144 * (w ^ 10 + 11 * w ^ 5 - 1) ^ 4)
      = kleinT w * (w ^ 15 - 171 * w ^ 10 + 247 * w ^ 5 + 57) := by
    unfold rsGamma
    exact div_mul_cancel₀ _ (mul_ne_zero h144 (pow_ne_zero _ hfw))
  have hM : 144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4 * cV ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h144 (pow_ne_zero _ hu.1)) (pow_ne_zero _ hu.2))
      (pow_ne_zero _ hcV)
  apply mul_right_cancel₀ hM
  linear_combination ((144 : K)*(rsGamma w)*D*cV^3*u^3 + (-4752 : K)*(rsGamma w)*D*cV^3*u^8 + (51840 : K)*(rsGamma w)*D*cV^3*u^13 + (-182160 : K)*(rsGamma w)*D*cV^3*u^18 + (-51840 : K)*(rsGamma w)*D*cV^3*u^23 + (-4752 : K)*(rsGamma w)*D*cV^3*u^28 + (-144 : K)*(rsGamma w)*D*cV^3*u^33 + (144 : K)*(rsGamma w)*N*D^12*cV^2*u^2 + (-3168 : K)*(rsGamma w)*N*D^12*cV^2*u^7 + (17136 : K)*(rsGamma w)*N*D^12*cV^2*u^12 + (3168 : K)*(rsGamma w)*N*D^12*cV^2*u^17 + (144 : K)*(rsGamma w)*N*D^12*cV^2*u^22 + (144 : K)*(rsGamma w)*N^2*D^23*cV*u + (-1584 : K)*(rsGamma w)*N^2*D^23*cV*u^6 + (-144 : K)*(rsGamma w)*N^2*D^23*cV*u^11 + (144 : K)*(rsGamma w)*N^3*D^34 + (-1584 : K)*(rsGamma w)*N^6*D^7*cV^2*u^2 + (34848 : K)*(rsGamma w)*N^6*D^7*cV^2*u^7 + (-188496 : K)*(rsGamma w)*N^6*D^7*cV^2*u^12 + (-34848 : K)*(rsGamma w)*N^6*D^7*cV^2*u^17 + (-1584 : K)*(rsGamma w)*N^6*D^7*cV^2*u^22 + (-3168 : K)*(rsGamma w)*N^7*D^18*cV*u + (34848 : K)*(rsGamma w)*N^7*D^18*cV*u^6 + (3168 : K)*(rsGamma w)*N^7*D^18*cV*u^11 + (-4752 : K)*(rsGamma w)*N^8*D^29 + (-144 : K)*(rsGamma w)*N^11*D^2*cV^2*u^2 + (3168 : K)*(rsGamma w)*N^11*D^2*cV^2*u^7 + (-17136 : K)*(rsGamma w)*N^11*D^2*cV^2*u^12 + (-3168 : K)*(rsGamma w)*N^11*D^2*cV^2*u^17 + (-144 : K)*(rsGamma w)*N^11*D^2*cV^2*u^22 + (17136 : K)*(rsGamma w)*N^12*D^13*cV*u + (-188496 : K)*(rsGamma w)*N^12*D^13*cV*u^6 + (-17136 : K)*(rsGamma w)*N^12*D^13*cV*u^11 + (51840 : K)*(rsGamma w)*N^13*D^24 + (3168 : K)*(rsGamma w)*N^17*D^8*cV*u + (-34848 : K)*(rsGamma w)*N^17*D^8*cV*u^6 + (-3168 : K)*(rsGamma w)*N^17*D^8*cV*u^11 + (-182160 : K)*(rsGamma w)*N^18*D^19 + (144 : K)*(rsGamma w)*N^22*D^3*cV*u + (-1584 : K)*(rsGamma w)*N^22*D^3*cV*u^6 + (-144 : K)*(rsGamma w)*N^22*D^3*cV*u^11 + (-51840 : K)*(rsGamma w)*N^23*D^14 + (-4752 : K)*(rsGamma w)*N^28*D^9 + (-144 : K)*(rsGamma w)*N^33*D^4) * E8 + ((57 : K)*(kleinT u)*N^3*D^15*cT + (247 : K)*(kleinT u)*N^8*D^10*cT + (-171 : K)*(kleinT u)*N^13*D^5*cT + (1 : K)*(kleinT u)*N^18*cT + (57 : K)*(kleinT u)*w*N^2*D^16*cT + (247 : K)*(kleinT u)*w*N^7*D^11*cT + (-171 : K)*(kleinT u)*w*N^12*D^6*cT + (1 : K)*(kleinT u)*w*N^17*D*cT + (57 : K)*(kleinT u)*w^2*N*D^17*cT + (247 : K)*(kleinT u)*w^2*N^6*D^12*cT + (-171 : K)*(kleinT u)*w^2*N^11*D^7*cT + (1 : K)*(kleinT u)*w^2*N^16*D^2*cT + (57 : K)*(kleinT u)*w^3*D^18*cT + (247 : K)*(kleinT u)*w^3*N^5*D^13*cT + (-171 : K)*(kleinT u)*w^3*N^10*D^8*cT + (1 : K)*(kleinT u)*w^3*N^15*D^3*cT + (-144 : K)*(rsGamma w)*N^3*D^45 + (6336 : K)*(rsGamma w)*N^8*D^40 + (-103968 : K)*(rsGamma w)*N^13*D^35 + (747648 : K)*(rsGamma w)*N^18*D^30 + (-1900080 : K)*(rsGamma w)*N^23*D^25 + (-747648 : K)*(rsGamma w)*N^28*D^20 + (-103968 : K)*(rsGamma w)*N^33*D^15 + (-6336 : K)*(rsGamma w)*N^38*D^10 + (-144 : K)*(rsGamma w)*N^43*D^5 + (-144 : K)*(rsGamma w)*w*N^2*D^46 + (6336 : K)*(rsGamma w)*w*N^7*D^41 + (-103968 : K)*(rsGamma w)*w*N^12*D^36 + (747648 : K)*(rsGamma w)*w*N^17*D^31 + (-1900080 : K)*(rsGamma w)*w*N^22*D^26 + (-747648 : K)*(rsGamma w)*w*N^27*D^21 + (-103968 : K)*(rsGamma w)*w*N^32*D^16 + (-6336 : K)*(rsGamma w)*w*N^37*D^11 + (-144 : K)*(rsGamma w)*w*N^42*D^6 + (-144 : K)*(rsGamma w)*w^2*N*D^47 + (6336 : K)*(rsGamma w)*w^2*N^6*D^42 + (-103968 : K)*(rsGamma w)*w^2*N^11*D^37 + (747648 : K)*(rsGamma w)*w^2*N^16*D^32 + (-1900080 : K)*(rsGamma w)*w^2*N^21*D^27 + (-747648 : K)*(rsGamma w)*w^2*N^26*D^22 + (-103968 : K)*(rsGamma w)*w^2*N^31*D^17 + (-6336 : K)*(rsGamma w)*w^2*N^36*D^12 + (-144 : K)*(rsGamma w)*w^2*N^41*D^7 + (-144 : K)*(rsGamma w)*w^3*D^48 + (6336 : K)*(rsGamma w)*w^3*N^5*D^43 + (-103968 : K)*(rsGamma w)*w^3*N^10*D^38 + (747648 : K)*(rsGamma w)*w^3*N^15*D^33 + (-1900080 : K)*(rsGamma w)*w^3*N^20*D^28 + (-747648 : K)*(rsGamma w)*w^3*N^25*D^23 + (-103968 : K)*(rsGamma w)*w^3*N^30*D^18 + (-6336 : K)*(rsGamma w)*w^3*N^35*D^13 + (-144 : K)*(rsGamma w)*w^3*N^40*D^8) * E7 + ((576 : K)*(rsGamma w)*w^4*D^39 + (-9504 : K)*(rsGamma w)*w^4*N^5*D^34 + (68832 : K)*(rsGamma w)*w^4*N^10*D^29 + (-178992 : K)*(rsGamma w)*w^4*N^15*D^24 + (-51696 : K)*(rsGamma w)*w^4*N^20*D^19 + (-4752 : K)*(rsGamma w)*w^4*N^25*D^14 + (-144 : K)*(rsGamma w)*w^4*N^30*D^9 + (-9504 : K)*(rsGamma w)*w^9*D^39 + (69696 : K)*(rsGamma w)*w^9*N^5*D^34 + (-185328 : K)*(rsGamma w)*w^9*N^10*D^29 + (-34848 : K)*(rsGamma w)*w^9*N^15*D^24 + (-1584 : K)*(rsGamma w)*w^9*N^20*D^19 + (68832 : K)*(rsGamma w)*w^14*D^39 + (-185328 : K)*(rsGamma w)*w^14*N^5*D^34 + (-34272 : K)*(rsGamma w)*w^14*N^10*D^29 + (-3168 : K)*(rsGamma w)*w^14*N^15*D^24 + (-144 : K)*(rsGamma w)*w^14*N^20*D^19 + (-178992 : K)*(rsGamma w)*w^19*D^39 + (-34848 : K)*(rsGamma w)*w^19*N^5*D^34 + (-3168 : K)*(rsGamma w)*w^19*N^10*D^29 + (-51696 : K)*(rsGamma w)*w^24*D^39 + (-1584 : K)*(rsGamma w)*w^24*N^5*D^34 + (-144 : K)*(rsGamma w)*w^24*N^10*D^29 + (-4752 : K)*(rsGamma w)*w^29*D^39 + (-144 : K)*(rsGamma w)*w^34*D^39) * E6 + ((1 : K)*w^4*D^49) * E3 + ((57 : K)*w^4*D^19 + (247 : K)*w^9*D^19 + (-171 : K)*w^14*D^19 + (1 : K)*w^19*D^19) * E4 + ((1 : K)*(kleinT u)*w^4*D^4*cT) * E5 + ((1 : K)*(kleinT u)*cT) * hG + ((57 : K)*(kleinT u)*b*u^4 + (247 : K)*(kleinT u)*b*u^9 + (-171 : K)*(kleinT u)*b*u^14 + (1 : K)*(kleinT u)*b*u^19 + (-1 : K)*(kleinT u)*a + (-171 : K)*(kleinT u)*a*u^5 + (-247 : K)*(kleinT u)*a*u^10 + (57 : K)*(kleinT u)*a*u^15) * hc + ((-1 : K)*cV^4*a) * E1 + ((-1 : K)*cV^4*b*u^4) * E2

end icoU_pack
end RubinSilverberg

theorem solution {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) :
    IsIcoSymmetry (icoU ζ) := by
  obtain ⟨h1, h2, h3, h4⟩ := pk_atom_relations ζ hζ
  have hdet := pk_icoU_det ζ hζ
  set α := ζ - ζ ^ 4 with hα
  set β := ζ ^ 2 - ζ ^ 3 with hβ
  set s := sqrtFive ζ with hs
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at h4; norm_num at h4
  have e00 : icoU ζ 0 0 = s⁻¹ * -α := by rw [hs, hα]; simp [icoU]
  have e01 : icoU ζ 0 1 = s⁻¹ * β := by rw [hs, hβ]; simp [icoU]
  have e10 : icoU ζ 1 0 = s⁻¹ * β := by rw [hs, hβ]; simp [icoU]
  have e11 : icoU ζ 1 1 = s⁻¹ * α := by rw [hs, hα]; simp [icoU]
  refine ⟨hdet, ?_, ?_, ?_, ?_⟩
  ·
    intro n d
    rw [e00, e01, e10, e11]
    have key := RubinSilverberg.kleinVHom_atomsU α β s (s⁻¹ * n) (s⁻¹ * d) h1 h2 h3 h4
    have hom := pk_kleinVHom_smul s⁻¹ n d
    calc kleinVHom (s⁻¹ * -α * n + s⁻¹ * β * d) (s⁻¹ * β * n + s⁻¹ * α * d)
        = kleinVHom (-α * (s⁻¹ * n) + β * (s⁻¹ * d)) (β * (s⁻¹ * n) + α * (s⁻¹ * d)) := by
          congr 1 <;> ring
      _ = s ^ 12 * kleinVHom (s⁻¹ * n) (s⁻¹ * d) := key
      _ = s ^ 12 * (s⁻¹ ^ 12 * kleinVHom n d) := by rw [hom]
      _ = kleinVHom n d := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, one_mul]
  ·
    intro n d
    rw [e00, e01, e10, e11]
    have key := RubinSilverberg.kleinHHom_atomsU α β s (s⁻¹ * n) (s⁻¹ * d) h1 h2 h3 h4
    have hom := pk_kleinHHom_smul s⁻¹ n d
    calc kleinHHom (s⁻¹ * -α * n + s⁻¹ * β * d) (s⁻¹ * β * n + s⁻¹ * α * d)
        = kleinHHom (-α * (s⁻¹ * n) + β * (s⁻¹ * d)) (β * (s⁻¹ * n) + α * (s⁻¹ * d)) := by
          congr 1 <;> ring
      _ = s ^ 20 * kleinHHom (s⁻¹ * n) (s⁻¹ * d) := key
      _ = s ^ 20 * (s⁻¹ ^ 20 * kleinHHom n d) := by rw [hom]
      _ = kleinHHom n d := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, one_mul]
  ·
    intro n d
    rw [e00, e01, e10, e11]
    have key := RubinSilverberg.kleinTHom_atomsU α β s (s⁻¹ * n) (s⁻¹ * d) h1 h2 h3 h4
    have hom := pk_kleinTHom_smul s⁻¹ n d
    calc kleinTHom (s⁻¹ * -α * n + s⁻¹ * β * d) (s⁻¹ * β * n + s⁻¹ * α * d)
        = kleinTHom (-α * (s⁻¹ * n) + β * (s⁻¹ * d)) (β * (s⁻¹ * n) + α * (s⁻¹ * d)) := by
          congr 1 <;> ring
      _ = s ^ 30 * kleinTHom (s⁻¹ * n) (s⁻¹ * d) := key
      _ = s ^ 30 * (s⁻¹ ^ 30 * kleinTHom n d) := by rw [hom]
      _ = kleinTHom n d := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, one_mul]
  ·
    intro u hV hden
    have hmD : moebDen (icoU ζ) u = s⁻¹ * (β * u + α) := by
      unfold moebDen; rw [e10, e11]; ring
    have hD : β * u + α ≠ 0 := by
      rw [hmD] at hden; exact (mul_ne_zero_iff.mp hden).2
    have hm : moeb (icoU ζ) u = (-α * u + β) / (β * u + α) := by
      unfold moeb
      rw [e00, e01, e10, e11,
        show s⁻¹ * -α * u + s⁻¹ * β = s⁻¹ * (-α * u + β) by ring,
        show s⁻¹ * β * u + s⁻¹ * α = s⁻¹ * (β * u + α) by ring]
      exact mul_div_mul_left _ _ (inv_ne_zero hs0)
    have hT : kleinTHom (-α * u + β) (β * u + α) = s ^ 30 * kleinT u := by
      have := RubinSilverberg.kleinTHom_atomsU α β s u 1 h1 h2 h3 h4
      simpa only [mul_one, pk_kleinTHom_one] using this
    have hVc : kleinVHom (-α * u + β) (β * u + α) = s ^ 12 * kleinV u := by
      have := RubinSilverberg.kleinVHom_atomsU α β s u 1 h1 h2 h3 h4
      simpa only [mul_one, pk_kleinVHom_one] using this
    have hG := RubinSilverberg.icoU_datumG α β s u h1 h2 h3 h4
    have hGam := RubinSilverberg.icoU_datumGam α β s u h1 h2 h3 h4
    have hc : s ^ 30 * s ^ 18 = (s ^ 12) ^ 4 := by ring
    have hcV : s ^ 12 ≠ 0 := pow_ne_zero _ hs0
    have kβ := pk_reduce_beta u (-α * u + β) (β * u + α) (s ^ 30) (s ^ 12) (s ^ 18) (-α) β
      hD hV hcV hT hVc hG hc
    have kγ := pk_reduce_gamma u (-α * u + β) (β * u + α) (s ^ 30) (s ^ 12) (s ^ 18) β α
      hD hV hcV hT hVc hGam hc
    rw [hmD, hm, e00, e01, e10, e11]
    constructor
    · linear_combination s⁻¹ * kβ
    · linear_combination s⁻¹ * kγ

end S_RubinSilverberg_isIcoSymmetry_icoU
end P2MW
export P2MW.S_RubinSilverberg_isIcoSymmetry_icoU (solution)
