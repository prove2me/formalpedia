-- Prove2me | solution 1 for PositivityTheory.CW.EigenGainPolynomial.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:10.676752+00:00
-- url     : https://prove2.me/submissions/46768626-5fde-4e3e-b433-2061cdbb521a

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain
import Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_phi_lb
import Theorems.Thm_PositivityTheory_CW_EigenGainPolynomial_fc_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenGainPolynomial
namespace PositivityTheory.CW.EigenGainPolynomial
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (hid : fc b μ (fun x => x) = casimirK ε E)
    (κ c : ℝ) (s : ℕ) (c0 C cs ν : ℝ) (hc0 : 0 < c0) (hC : 0 ≤ C) (hcs0 : 0 ≤ cs)
    (hsC : c + 1 ≤ (s : ℝ) ^ 2 * c0 / 4 - s * C)
    (hν0 : 0 ≤ ν) (hνc : cs * C ≤ ν) (v : V) (hv : Eig ε E ν v)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - cs * y ^ 4 ≤ ((1 + y) ^ s)⁻¹)
    (hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2)
    (h8 : c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2)
    (h9a : ‖∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)‖ ≤ C * (1 + ν) * ‖v‖ ^ 2)
    (h9b : ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ C * (1 + ν) ^ 3 * ‖v‖ ^ 2) :
    ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have ha : 0 < ((1 + ν) ^ s)⁻¹ := by positivity
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hT : ∀ u, fc b μ (fun x => x - ν) u = casimirK ε E u - (ν : ℂ) • u := by
    intro u
    have hf : (fun x : ℝ => x - ν) = fun x => x + -ν := by funext x; ring
    rw [hf, hadd (fun x => x) (fun _ => -ν), hid, hconst]
    simp [sub_eq_add_neg]
  have hTE : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (E p.1 p.2 v) = Z ε E p.1 p.2 v := by
    intro p
    rw [hT, Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hTZ : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (Z ε E p.1 p.2 v) =
      (casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v := by
    intro p
    rw [hT, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hp : ∀ p ∈ nc ε,
      ((1 + ν) ^ s)⁻¹ * ‖E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)).re
        + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ‖Z ε E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4))
          * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ (inner ℂ (E p.1 p.2 v) (fc b μ (fun x => ((1 + x) ^ s)⁻¹) (E p.1 p.2 v))).re := by
    intro p _
    have := hmono (fun x => ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν))))
      (fun x => ((1 + x) ^ s)⁻¹) (fun x hx => phi_lb s cs ν x hν0 hx hA) (E p.1 p.2 v)
    rw [fc_poly hsym hadd hmul hconst, hTE, hTZ] at this
    exact this
  unfold beta
  rw [Complex.re_sum]
  refine le_trans ?_ (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum, hE]
  have hN : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hR := le_trans (Complex.re_le_norm _) h9a
  have hk1 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * s / (1 + ν) := by positivity
    linarith
  have hk2 : 0 ≤ ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) := by positivity
  have hk4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4 := by positivity
    linarith
  have i2 := mul_le_mul_of_nonpos_left hR hk1
  have i3 := mul_le_mul_of_nonneg_left h8 hk2
  have i4 := mul_le_mul_of_nonpos_left h9b hk4
  have e2 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) * (C * (1 + ν) * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (s * C) * ‖v‖ ^ 2) := by
    field_simp
  have e3 : ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) * (c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2)
      = ((1 + ν) ^ s)⁻¹ * ((s : ℝ) ^ 2 * c0 / 4) * ‖v‖ ^ 2 := by
    field_simp
  have e4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) * (C * (1 + ν) ^ 3 * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (cs * C / (1 + ν)) * ‖v‖ ^ 2) := by
    field_simp
  rw [e2] at i2
  rw [e3] at i3
  rw [e4] at i4
  have b4 : cs * C / (1 + ν) ≤ 1 := (div_le_one h1).2 (by linarith)
  have hb4 := mul_le_mul_of_nonneg_left b4 (mul_nonneg ha.le hN)
  have hs := mul_le_mul_of_nonneg_left hsC (mul_nonneg ha.le hN)
  nlinarith
end PositivityTheory.CW.EigenGainPolynomial
