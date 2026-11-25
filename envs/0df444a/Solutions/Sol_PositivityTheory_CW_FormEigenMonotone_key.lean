-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:13.065787+00:00
-- url     : https://prove2.me/submissions/a539c5ef-8210-4207-9583-b4eb92ad8c9c

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_nonneg
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_zero
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_le_one
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_phi_eq
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_beta_add
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_re_inner_smul_self
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_beta_const_re
import Theorems.Thm_PositivityTheory_CW_FormEigenMonotone_beta_mono

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
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
namespace PositivityTheory.CW.FormEigenMonotone
theorem _root_.solution {κ c x₀ R : ℝ} {s : ℕ}
    (hA0 : ∀ w, ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1)
    (hA12 : ∀ ν v, x₀ ≤ ν → Eig ε E ν v →
      ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re)
    (hc : 0 ≤ c) (hR : 0 < R) (ν : ℝ) (hν : 0 ≤ ν) (h : V) (hh : Eig ε E ν h) :
    phiR s R ν * (ν - κ + c) * ‖h‖ ^ 2 - (if ν < x₀ then x₀ + |κ| + c else 0) * ‖h‖ ^ 2 ≤
      (beta ε E (fc b μ (phiR s R)) h h).re := by
  have hN : ∀ w, 0 ≤ (beta ε E (fc b μ (phiR s R)) w w).re := by
    intro w
    have h0 := beta_mono (ε := ε) (E := E) hmono (fun _ => (0:ℝ)) (phiR s R)
      (fun x _ => phi_nonneg s R x) w
    rw [hconst 0, beta_const_re] at h0
    simpa using h0
  have hd0 : (0:ℝ) ≤ ((1 + R) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) _)
  have hS : ∑ p ∈ nc ε, ‖E p.1 p.2 h‖ ^ 2 = (ν - κ) * ‖h‖ ^ 2 := by
    rw [hA0 h, show casimirK ε E h = (ν : ℂ) • h from hh, re_inner_smul_self]
    ring
  have hlow : (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) h h).re - ((1 + R) ^ s)⁻¹ * ((ν - κ) * ‖h‖ ^ 2)
      ≤ (beta ε E (fc b μ (phiR s R)) h h).re := by
    have e : fc b μ (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
        = fc b μ (fun x => ((1 + x) ^ s)⁻¹) + fc b μ (fun _ => -((1 + R) ^ s)⁻¹) := hadd _ _
    have h1 := beta_mono (ε := ε) (E := E) hmono (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
      (phiR s R) (fun x _ => by
        simp only [phiR]
        linarith [le_max_left (((1 + x) ^ s)⁻¹ - ((1 + R) ^ s)⁻¹) 0]) h
    rw [e, beta_add, hconst (-((1 + R) ^ s)⁻¹), Complex.add_re, beta_const_re, hS] at h1
    linarith
  have hn : 0 ≤ ‖h‖ ^ 2 := by positivity
  by_cases hx : ν < x₀
  · rw [if_pos hx]
    have hp0 := phi_nonneg s R ν
    have hp1 := phi_le_one (s := s) hR hν
    have hbd : phiR s R ν * (ν - κ + c) ≤ x₀ + |κ| + c := by
      rcases le_total 0 (ν - κ + c) with h0 | h0
      · nlinarith [neg_le_abs κ, mul_le_mul_of_nonneg_right hp1 h0]
      · nlinarith [abs_nonneg κ, mul_nonpos_of_nonneg_of_nonpos hp0 h0]
    have := mul_le_mul_of_nonneg_right hbd hn
    linarith [hN h]
  · rw [if_neg hx]
    have hA := hA12 ν h (not_lt.mp hx) hh
    by_cases hνR : ν < R
    · rw [phi_eq hν hνR]
      nlinarith [hlow, mul_nonneg (mul_nonneg hd0 hc) hn]
    · rw [phi_zero hR (not_lt.mp hνR)]
      simpa using hN h
end PositivityTheory.CW.FormEigenMonotone
