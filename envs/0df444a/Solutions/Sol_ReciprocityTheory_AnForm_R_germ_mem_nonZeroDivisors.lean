-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.germ_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:57.942264+00:00
-- url     : https://prove2.me/submissions/3c2d8d8b-fa8f-4c7c-a742-a23c26a2b58b

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA

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
theorem _root_.solution {W : Scheme.{0}} {V : W.Opens} (hV : IsAffineOpen V) {a : Γ(W, V)}
    (ha : a ∈ nonZeroDivisors Γ(W, V)) (w : W) (hw : w ∈ V) :
    W.presheaf.germ V w hw a ∈ nonZeroDivisors (W.presheaf.stalk w) := by
  let := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨w, hw⟩
  have := hV.isLocalization_stalk ⟨w, hw⟩
  have h := IsLocalization.map_nonZeroDivisors_le (hV.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl
    (W.presheaf.stalk w) (Submonoid.mem_map_of_mem (algebraMap Γ(W, V) (W.presheaf.stalk w)) ha)
  exact h
end ReciprocityTheory.AnForm.R
