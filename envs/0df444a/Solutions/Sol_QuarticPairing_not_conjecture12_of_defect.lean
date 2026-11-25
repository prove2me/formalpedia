-- Prove2me | solution 1 for QuarticPairing.not_conjecture12_of_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:18.821379+00:00
-- url     : https://prove2.me/submissions/13e8ca8a-4ab0-4d45-85d4-fab85f1e4e75

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency
public import Theorems.Thm_QuarticPairing_not_conjecture12_aux
public import Theorems.Thm_QuarticPairing_twistedSum_one_sub


set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β := by
  refine not_conjecture12_aux g Λ β fun h1 => ?_
  have hD := hE (1 / 8) (by norm_num)
  rw [show (1 : ℝ) / 2 + 1 / 8 = 5 / 8 by norm_num] at hD
  have hsum : (fun X : ℕ => ‖twistedSum g Λ β X 1‖ + 2 * defectSum g Λ β E X) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8)) := h1.add (hD.const_mul_left 2)
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun X => ?_)) hsum
  have hb := twistedSum_one_sub g Λ β hκ E h12 X
  have hD0 : 0 ≤ defectSum g Λ β E X :=
    sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hn : ‖twistedSum g Λ β X 0‖ = ‖κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ := by
    rw [norm_mul, hκ, one_mul, Complex.norm_conj]
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hn]
  calc ‖κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖
      = ‖(twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)) -
          twistedSum g Λ β X 1‖ := by ring_nf
    _ ≤ ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ +
          ‖twistedSum g Λ β X 1‖ := norm_sub_le _ _
    _ ≤ ‖twistedSum g Λ β X 1‖ + 2 * defectSum g Λ β E X := by linarith
end QuarticPairing
