-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mixedDiscriminant_pos_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:59.907643+00:00
-- url     : https://prove2.me/submissions/3902a26b-5a31-4dbc-b92a-d57645467a90

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pmWt_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_exists_gram_add_of_posDef
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_mdisc_of_gram
import Theorems.Thm_ReciprocityTheory_AnForm_mdisc_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosDef) : (mdisc A).im = 0 ∧ 0 < (mdisc A).re := by
  obtain _ | n := D
  · rw [mdisc_zero]; simp
  choose r hr v hv using fun k => pm_exists_gram_add_of_posDef (hA k)
  let w : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1)) → Fin (n + 1) → ℂ := fun k =>
    Sum.elim (v k) (fun s x => if x = s then ((Real.sqrt (r k) : ℝ) : ℂ) else 0)
  have hc : ∀ k, ((Real.sqrt (r k) : ℝ) : ℂ) * star ((Real.sqrt (r k) : ℝ) : ℂ) = (r k : ℂ) := by
    intro k
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr k).le]
  have hw : ∀ k a b, A k a b = ∑ s, w k s a * star (w k s b) := by
    intro k a b
    rw [hv, Fintype.sum_sum_type]
    congr 1
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, Finset.sum_eq_single a (fun s _ hs => by simp [w, Ne.symm hs]) (by simp)]
      simp only [w, Sum.elim_inr]
      exact (hc k).symm
    · rw [if_neg hab]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      by_cases has : a = s
      · subst has; simp [w, Ne.symm hab]
      · simp [w, has]
  rw [pm_mdisc_of_gram A w hw]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  refine div_pos ?_ (by positivity)
  let g₀ : Fin (n + 1) → Fin (n + 1) × (Fin (n + 1) ⊕ Fin (n + 1)) := fun a => (a, Sum.inr a)
  refine Finset.sum_pos' (fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _))
    ⟨g₀, Finset.mem_univ _, ?_⟩
  have h1 : pmWt g₀ = 1 := by
    unfold pmWt
    rw [if_pos]
    ext x; simp [g₀]
  have h2 : pmGmat w g₀ = diagonal fun a => ((Real.sqrt (r a) : ℝ) : ℂ) := by
    ext x a
    by_cases h : x = a
    · subst h; simp [pmGmat, w, g₀]
    · simp [pmGmat, w, g₀, h]
  rw [h1, one_mul, h2, det_diagonal, Complex.normSq_pos]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (hr a)).ne'
end ReciprocityTheory.AnForm.A
