-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.res_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:17:23.857597+00:00
-- url     : https://prove2.me/submissions/dc84a564-307d-4330-98ae-00024a8bedd0

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Theorems.Thm_ReciprocityTheory_AnForm_R_germ_mem_nonZeroDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {W : Scheme.{0}} {V O : W.Opens} (h : O ≤ V) (hV : IsAffineOpen V)
    {a : Γ(W, V)} (ha : a ∈ nonZeroDivisors Γ(W, V)) :
    W.presheaf.map (homOfLE h).op a ∈ nonZeroDivisors Γ(W, O) := by
  have key : ∀ x : Γ(W, O), x * W.presheaf.map (homOfLE h).op a = 0 → x = 0 := by
    intro x hx
    refine TopCat.Presheaf.section_ext W.sheaf O x 0 (fun w hw => ?_)
    have hg := germ_mem_nonZeroDivisors hV ha w (h hw)
    have h1 : W.presheaf.germ O w hw x * W.presheaf.germ V w (h hw) a = 0 := by
      rw [← W.presheaf.germ_res_apply (homOfLE h) w hw a, ← map_mul, hx, map_zero]
    change W.presheaf.germ O w hw x = W.presheaf.germ O w hw 0
    rw [(mem_nonZeroDivisors_iff.mp hg).2 _ h1, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩
end ReciprocityTheory.AnForm.R
