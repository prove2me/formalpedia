-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mixedDiscriminant_re_mono_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:43.234466+00:00
-- url     : https://prove2.me/submissions/20394e7f-8db9-44db-a381-0835dcf300dc

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pmWt_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_exists_gram_of_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_mdisc_of_gram

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
theorem _root_.solution (A B : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ k, (A k).PosSemidef)
    (hAB : ∀ k, (B k - A k).PosSemidef) : (mdisc A).re ≤ (mdisc B).re := by
  choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)
  choose u hu using fun k => pm_exists_gram_of_posSemidef (hAB k)
  let w : Fin D → (Fin D ⊕ Fin D) → Fin D → ℂ := fun k => Sum.elim (v k) (u k)
  have hw : ∀ k a b, B k a b = ∑ s, w k s a * star (w k s b) := by
    intro k a b
    have e : B k a b = A k a b + (B k - A k) a b := by simp
    rw [e, hv, hu, Fintype.sum_sum_type]
    rfl
  rw [pm_mdisc_of_gram A v hv, pm_mdisc_of_gram B w hw, Complex.ofReal_re, Complex.ofReal_re]
  gcongr
  let φ : (Fin D → Fin D × Fin D) → (Fin D → Fin D × (Fin D ⊕ Fin D)) :=
    fun g a => ((g a).1, Sum.inl (g a).2)
  have hφ : Function.Injective φ := by
    intro g h e
    funext a
    have := congrFun e a
    simp only [φ, Prod.mk.injEq, Sum.inl.injEq] at this
    exact Prod.ext this.1 this.2
  calc ∑ g : Fin D → Fin D × Fin D, pmWt g * Complex.normSq (pmGmat v g).det
      = ∑ g : Fin D → Fin D × Fin D, pmWt (φ g) * Complex.normSq (pmGmat w (φ g)).det :=
        Finset.sum_congr rfl fun g _ => rfl
    _ = ∑ g ∈ univ.image φ, pmWt g * Complex.normSq (pmGmat w g).det :=
        (Finset.sum_image (f := fun g => pmWt g * Complex.normSq (pmGmat w g).det)
          fun x _ y _ h => hφ h).symm
    _ ≤ ∑ g, pmWt g * Complex.normSq (pmGmat w g).det :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun g _ _ =>
          mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)
end ReciprocityTheory.AnForm.A
