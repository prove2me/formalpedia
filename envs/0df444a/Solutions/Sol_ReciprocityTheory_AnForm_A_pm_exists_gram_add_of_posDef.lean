-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_exists_gram_add_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:45.571282+00:00
-- url     : https://prove2.me/submissions/54422d06-50c2-49df-b59e-1baa26a24bf2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_exists_gram_of_posSemidef

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
open scoped MatrixOrder
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution [Nonempty (Fin D)] {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosDef) : ∃ r : ℝ, 0 < r ∧ ∃ v : Fin D → Fin D → ℂ,
      ∀ a b, A a b = ∑ s, v s a * star (v s b) + if a = b then (r : ℂ) else 0 := by
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin D) (Fin D) ℂ)
    hA.isStrictlyPositive.isSelfAdjoint).2 fun x hx => hA.isStrictlyPositive.spectrum_pos hx
  obtain ⟨v, hv⟩ := pm_exists_gram_of_posSemidef (Matrix.le_iff.mp hle)
  refine ⟨r, hr, v, fun a b => ?_⟩
  rw [← hv]
  simp [Matrix.algebraMap_matrix_apply]
end ReciprocityTheory.AnForm.A
