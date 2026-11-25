-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.sum_pow_eq_aeval_psumQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:52.136289+00:00
-- url     : https://prove2.me/submissions/19e64fb2-8da2-4dde-b7ad-5f1aee686f76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_aeval_psumQ

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
theorem _root_.solution {S : Type*} [CommRing S] {δ : ℕ} (f : Fin δ → S) (k : ℕ) :
    ∑ i, f i ^ k =
      aeval (fun i : Fin δ => (Finset.univ.val.map f).esymm (i + 1)) (psumQ δ k) := by
  have h := congrArg (aeval f) (aeval_psumQ δ k)
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  simp [MvPolynomial.psum]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
