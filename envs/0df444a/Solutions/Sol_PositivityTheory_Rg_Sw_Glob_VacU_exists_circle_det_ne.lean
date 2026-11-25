-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.VacU.exists_circle_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:39.127284+00:00
-- url     : https://prove2.me/submissions/34988f8f-7168-458b-8e7b-ffb76e2025c2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_ExistsCircleDetNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacU
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.Glob.VacU
theorem _root_.solution (W : Matrix (Fin n) (Fin n) ℂ) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ (W + lam • 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set p := (-W).charpoly with hp
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hev : ∀ x : ℂ, p.eval x = (W + x • 1).det := by
    intro x
    rw [hp, Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, sub_neg_eq_add, add_comm, Matrix.smul_one_eq_diagonal]
  let r : Fin (n + 1) → ℝ := fun k => (k : ℝ) / ((n : ℝ) + 1)
  let f : Fin (n + 1) → ℂ := fun k => cexp (I * (r k : ℂ))
  have hr0 : ∀ k, 0 ≤ r k := fun k => by simp only [r]; positivity
  have hr1 : ∀ k, r k < 1 := fun k => by
    simp only [r]; rw [div_lt_one (by positivity)]; exact_mod_cast k.2
  have hf : Function.Injective f := by
    intro k k' h
    obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have hre : r k = r k' + z * (2 * Real.pi) := by
      have := congrArg Complex.im hz
      simpa [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im] using this
    have hz0 : z = 0 := by
      by_contra hz0
      have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz0
      have habs : |(z : ℝ) * (2 * Real.pi)| < 1 := by
        rw [abs_lt]; constructor <;> linarith [hr0 k, hr0 k', hr1 k, hr1 k']
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
      nlinarith [Real.pi_gt_three]
    rw [hz0] at hre
    simp only [Int.cast_zero, zero_mul, add_zero, r] at hre
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : (k : ℝ) = k' := by
      field_simp at hre; linarith
    exact Fin.ext (by exact_mod_cast this)
  have hroot : ∀ k, f k ∈ p.roots.toFinset := by
    intro k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, hev]
    apply hcon
    simp only [f]
    rw [Complex.norm_exp]
    simp
  have hcard : (Finset.univ.image f).card ≤ p.roots.toFinset.card :=
    Finset.card_le_card (fun x hx => by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx; exact hroot k)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  have h2 : p.natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  omega
end PositivityTheory.Rg.Sw.Glob.VacU
