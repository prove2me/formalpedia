-- Prove2me | solution 1 for QuarticPairing.amendedMain_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:36:53.675551+00:00
-- url     : https://prove2.me/submissions/288a04ac-2414-4d61-94cb-9098fe1b229f

module
public import Definitions.Def_QuarticPairing_Inconsistency
public import Definitions.Def_QuarticPairing_Amended
public import Theorems.Thm_QuarticPairing_mul_conj_self_eq_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {κ : ℂ} (hκ : ‖κ‖ = 1) (b : ℂ) (X : ℕ) (ℓ : ℤ) :
    amendedMain κ b X (1 - ℓ) = -κ * starRingEnd ℂ (amendedMain κ b X ℓ) := by
  have hκκ := mul_conj_self_eq_one hκ
  unfold amendedMain
  by_cases h0 : ℓ = 0
  · subst h0
    simp [Complex.conj_ofReal]
    ring
  by_cases h1 : ℓ = 1
  · subst h1
    simp only [sub_self, ite_true, one_ne_zero, ite_false, map_mul, map_neg, Complex.conj_conj,
      Complex.conj_ofReal]
    linear_combination (-(b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ))) * hκκ
  · have h2 : (1 - ℓ) ≠ 0 := by omega
    have h3 : (1 - ℓ) ≠ 1 := by omega
    simp [h0, h1, h2, h3]
end QuarticPairing
