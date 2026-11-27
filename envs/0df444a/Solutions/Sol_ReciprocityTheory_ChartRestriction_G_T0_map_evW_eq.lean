-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.map_evW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:16:05.195232+00:00
-- url     : https://prove2.me/submissions/e0be9e26-e082-411d-a3e5-57a17006e37b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K S : Type*} [Field K] [CommRing S] [Algebra K S] {D N : ℕ} (P : S →+* ℂ)
    (sg : K →+* ℂ) (hP : P.comp (algebraMap K S) = sg) (y : Fin (N + 1) → S)
    (R : MvPolynomial (UXVar D N) K) :
    MvPolynomial.map P (evW (R := K) y R) = Ey (fun j => P (y j)) (MvPolynomial.map sg R) := by
  have h : (MvPolynomial.map P).comp (evW (R := K) (D := D) y).toRingHom =
      (Ey (D := D) (fun j => P (y j))).toRingHom.comp (MvPolynomial.map sg) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evW, Ey, ← hP]
    · intro i
      cases i <;> simp [evW, Ey]
  exact RingHom.congr_fun h R
end ReciprocityTheory.ChartRestriction.G.T0
