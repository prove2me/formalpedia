-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.chord_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:05.255703+00:00
-- url     : https://prove2.me/submissions/b584dc8b-ad0a-40b7-abea-b4de9b4259af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorClose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {C : Type} [Field C] (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0)
    (h3 : W.a₃ = 0) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0) (hs : A + B ≠ 0)
    (hd : A - B ≠ 0) :
    (px W A - px W B) ^ 2 * (px W (A + B) - px W (A - B)) = -4 * py W A * py W B := by
  rw [sub_eq_add_neg A B]
  rcases A with _ | ⟨xA, yA, hA'⟩
  · exact absurd rfl hA
  rcases B with _ | ⟨xB, yB, hB'⟩
  · exact absurd rfl hB
  by_cases hx : xA = xB
  · exfalso
    subst hx
    have e1 := (WeierstrassCurve.Affine.equation_iff _ _).1 hA'.1
    have e2 := (WeierstrassCurve.Affine.equation_iff _ _).1 hB'.1
    have hm : (yA - yB) * (yA + yB) = 0 := by
      linear_combination e1 - e2 - xA * (yA - yB) * h1 - (yA - yB) * h3
    rcases mul_eq_zero.1 hm with h | h
    · have hy : yA = yB := sub_eq_zero.1 h
      subst hy
      exact hd (sub_self _)
    · have hy : yA = W.toAffine.negY xA yB := by
        rw [WeierstrassCurve.Affine.negY]
        linear_combination h + xA * h1 + h3
      exact hs (WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy)
  · have hx' : xA - xB ≠ 0 := sub_ne_zero.2 hx
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx,
      WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    simp only [px, py, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx,
      WeierstrassCurve.Affine.negY, h1, h2, h3]
    field_simp
    ring
end ReciprocityTheory.ChartRestriction.L1
