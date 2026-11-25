-- Prove2me | solution 1 for QuarticPairing.not_conjecture12_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:36:19.404352+00:00
-- url     : https://prove2.me/submissions/3f25b1c1-2ce9-4067-b812-6ba189821164

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
public import Theorems.Thm_QuarticPairing_eq_zero_of_isBigO

set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    (hS : (fun X : ℕ => ‖twistedSum g Λ β X 1‖) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8)) →
      (fun X : ℕ => twistedSum g Λ β X 0) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8))) :
    ¬ Conjecture12 g Λ β := by
  rintro ⟨b, hb, hconj⟩
  have hε : (0 : ℝ) < 1 / 8 := by norm_num
  have h0 := hconj (1 / 8) hε 0
  have h1 := hconj (1 / 8) hε 1
  simp only [ite_true, one_ne_zero, ite_false, sub_zero] at h0 h1
  have he : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
  rw [he] at h0 h1
  exact hb (eq_zero_of_isBigO (((hS h1.norm_left).sub h0).congr_left fun X => by ring))
end QuarticPairing
