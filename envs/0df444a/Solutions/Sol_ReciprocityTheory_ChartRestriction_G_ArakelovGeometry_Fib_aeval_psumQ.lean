-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_psumQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:58.775614+00:00
-- url     : https://prove2.me/submissions/1fb7f0aa-d523-4209-9a11-439efe436c40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (δ k : ℕ) :
    aeval (fun i : Fin δ => esymm (Fin δ) ℤ (i + 1)) (psumQ δ k) = psum (Fin δ) ℤ k := by
  have h := (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose_spec
  have h2 := congrArg Subtype.val h
  first
  | (rw [esymmAlgHom_apply] at h2; exact h2)
  | exact h2
  | simpa [psumQ, esymmAlgHom_apply] using h2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
