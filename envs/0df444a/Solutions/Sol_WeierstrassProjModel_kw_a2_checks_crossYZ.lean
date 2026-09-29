-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_checks_crossYZ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d37e626a-89bf-5363-b509-90d81a19a58b

import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_checks_crossYZ

open WeierstrassProjModel WeierstrassCurve MvPolynomial

set_option autoImplicit false
set_option Elab.async false

noncomputable section

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "W_F" => (W.baseChange F).toProjective

section Coeff

theorem kw_lrApt_WF_a₁ : (W_F).a₁ = algebraMap R F W.a₁ := rfl
theorem kw_lrApt_WF_a₂ : (W_F).a₂ = algebraMap R F W.a₂ := rfl
theorem kw_lrApt_WF_a₃ : (W_F).a₃ = algebraMap R F W.a₃ := rfl
theorem kw_lrApt_WF_a₄ : (W_F).a₄ = algebraMap R F W.a₄ := rfl
theorem kw_lrApt_WF_a₆ : (W_F).a₆ = algebraMap R F W.a₆ := rfl

end Coeff

section Check2b

set_option maxHeartbeats 0 in

theorem kw_lrApt_aeval_lrSym_cross_YZ {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval (Sum.elim P P) (kw_lrSym_Y W) * (W_F).dblZ P
      = aeval (Sum.elim P P) (kw_lrSym_Z W) * (W_F).dblY P := by
  have heq := (Projective.equation_iff P).mp hP
  simp only [kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄,
    kw_lrApt_WF_a₆] at heq
  rw [show (W_F).dblY P
      = -(W_F).negDblY P - (W_F).a₁ * (W_F).dblX P - (W_F).a₃ * (W_F).dblZ P from
    (W_F).negY_eq _ _ _]
  linear_combination (norm :=
    (simp only [kw_lrSym_Y, kw_lrSym_Z, Projective.dblZ, Projective.dblX, Projective.negDblY,
      Projective.negY,
      kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄, kw_lrApt_WF_a₆,
      map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
      Sum.elim_inl, Sum.elim_inr]; ring1))
    ((-(6:F)) * P 0 ^ 5 * (algebraMap R F W.a₁) ^ 5
        - ((36:F)) * P 0 ^ 5 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂)
        - ((54:F)) * P 0 ^ 5 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2
        - ((18:F)) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₁) ^ 4
        - ((90:F)) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂)
        + (54:F) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃)
        - ((108:F)) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₂) ^ 2
        - ((2:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 7
        - ((18:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 5 * (algebraMap R F W.a₂)
        - ((12:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃)
        - ((52:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂) ^ 2
        - ((6:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₄)
        - ((72:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((48:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 3
        - ((54:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (54:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2
        + (162:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₆)
        - ((54:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃)
        - ((12:F)) * P 0 ^ 3 * P 1 ^ 2 * (algebraMap R F W.a₁) ^ 3
        - ((36:F)) * P 0 ^ 3 * P 1 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂)
        + (108:F) * P 0 ^ 3 * P 1 ^ 2 * (algebraMap R F W.a₃)
        - ((8:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 6
        - ((62:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₂)
        + (6:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃)
        - ((144:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) ^ 2
        - ((36:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((96:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₂) ^ 3
        - ((108:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (162:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₃) ^ 2
        + (324:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₆)
        - ((8:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 6 * (algebraMap R F W.a₃)
        - ((8:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 5 * (algebraMap R F W.a₄)
        - ((56:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((50:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (6:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 2
        + (72:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₆)
        - ((108:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃)
        - ((54:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        - ((72:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₄)
        + (18:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        + (162:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₆)
        - ((54:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₄) ^ 2
        - ((48:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₂) ^ 3 * (algebraMap R F W.a₃)
        - ((54:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (54:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₃) ^ 3
        + (162:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        + (6:F) * P 0 ^ 2 * P 1 ^ 3 * (algebraMap R F W.a₁) ^ 2
        - ((12:F)) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) ^ 5
        - ((72:F)) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂)
        + (72:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃)
        - ((96:F)) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2
        + (18:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₄)
        + (108:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((24:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 5 * (algebraMap R F W.a₃)
        - ((24:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₄)
        - ((138:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((132:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (108:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 2
        + (216:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₆)
        - ((168:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃)
        - ((36:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        - ((144:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₄)
        + (162:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        + (324:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₆)
        - ((108:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₄) ^ 2
        - ((12:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 5 * (algebraMap R F W.a₃) ^ 2
        - ((24:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        - ((60:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        - ((12:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₄) ^ 2
        - ((102:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (30:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 3
        + (108:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        - ((60:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃) ^ 2
        - ((36:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₄) ^ 2
        - ((36:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        - ((72:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (54:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 3
        + (162:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        - ((54:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 2
        + (18:F) * P 0 * P 1 ^ 4 * (algebraMap R F W.a₁)
        - ((10:F)) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₁) ^ 4
        - ((48:F)) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂)
        + (84:F) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃)
        - ((32:F)) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₂) ^ 2
        - ((12:F)) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₄)
        - ((24:F)) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃)
        - ((18:F)) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₄)
        - ((108:F)) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((72:F)) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (180:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2
        + (162:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₆)
        - ((48:F)) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃)
        + (90:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        - ((24:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃) ^ 2
        - ((48:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        - ((90:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        - ((30:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₄) ^ 2
        - ((144:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (126:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 3
        + (216:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        - ((24:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃) ^ 2
        - ((72:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄) ^ 2
        + (72:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        - ((8:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃) ^ 3
        - ((24:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        - ((24:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 3
        - ((24:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 2
        - ((54:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        + (24:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 4
        + (54:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₆)
        - ((6:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₄) ^ 3
        - ((4:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃) ^ 3
        - ((36:F)) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 2
        + (12:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₃) ^ 3 * (algebraMap R F W.a₄)
        + (12:F) * P 1 ^ 5
        - ((4:F)) * P 1 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 3
        - ((16:F)) * P 1 ^ 4 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂)
        + (66:F) * P 1 ^ 4 * P 2 * (algebraMap R F W.a₃)
        - ((10:F)) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃)
        - ((4:F)) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₄)
        - ((40:F)) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        - ((16:F)) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (102:F) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₃) ^ 2
        + (36:F) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₆)
        - ((12:F)) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 2
        - ((18:F)) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        - ((36:F)) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        - ((12:F)) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₄) ^ 2
        - ((24:F)) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (96:F) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₃) ^ 3
        + (162:F) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        - ((8:F)) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 3
        - ((24:F)) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        - ((14:F)) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 3
        - ((30:F)) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 2
        - ((12:F)) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        + (42:F) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₃) ^ 4
        + (108:F) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₆)
        - ((12:F)) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₄) ^ 3
        - ((2:F)) * P 2 ^ 5 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 4
        - ((8:F)) * P 2 ^ 5 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 3 * (algebraMap R F W.a₄)
        - ((2:F)) * P 2 ^ 5 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 4
        - ((12:F)) * P 2 ^ 5 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄) ^ 2
        - ((2:F)) * P 2 ^ 5 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 3 * (algebraMap R F W.a₄)
        + (6:F) * P 2 ^ 5 * (algebraMap R F W.a₃) ^ 5
        + (18:F) * P 2 ^ 5 * (algebraMap R F W.a₃) ^ 3 * (algebraMap R F W.a₆)
        - ((6:F)) * P 2 ^ 5 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 3) * heq

end Check2b

end

set_option maxHeartbeats 6400000 in
theorem solution.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P : Fin 3 → F, ((W.baseChange F).toProjective).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Y W) * ((W.baseChange F).toProjective).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * ((W.baseChange F).toProjective).dblY P) :=
  fun P hP => kw_lrApt_aeval_lrSym_cross_YZ W F (P := P) hP

end S_WeierstrassProjModel_kw_a2_checks_crossYZ
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_checks_crossYZ (solution)
