-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_exists_gram_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:35.404559+00:00
-- url     : https://prove2.me/submissions/21f7c6e1-88f8-4693-b70a-c4a6ddf77234

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos

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
theorem _root_.solution {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef) :
    ∃ v : Fin D → Fin D → ℂ, ∀ a b, A a b = ∑ r, v r a * star (v r b) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun r a => star (B r a), fun a b => ?_⟩
  rw [hB, star_eq_conjTranspose, mul_apply]
  simp [conjTranspose_apply]
end ReciprocityTheory.AnForm.A
