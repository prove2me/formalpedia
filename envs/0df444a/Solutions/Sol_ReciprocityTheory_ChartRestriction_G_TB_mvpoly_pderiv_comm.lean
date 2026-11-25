-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.mvpoly_pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:49.410519+00:00
-- url     : https://prove2.me/submissions/de5e2c14-10cb-4c6f-83f5-a9bfc1f1f536

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution {k σ : Type} [CommRing k] (i j : σ) (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅(MvPolynomial.pderiv i : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)), MvPolynomial.pderiv j⁆ =
      (0 : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X, Pi.single_apply,
      Pi.single_apply]
    split_ifs <;> simp
  have h' := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h'
  exact sub_eq_zero.mp h'
end ReciprocityTheory.ChartRestriction.G.TB
