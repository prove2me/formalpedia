-- Prove2me | solution 1 for WeierstrassProjModel.kw_a2_checks_addXYZ_crossXZ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/527581cb-0d48-53f0-9e77-23901e66a916

import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ

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
section Check1

local macro "simp_check1" : tactic =>
  `(tactic| simp only [kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z, kw_lrAdd_starX,
      kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₁₂, kw_lrAdd_c₂₁,
      Projective.addX, Projective.addY, Projective.addZ, Projective.negAddY, Projective.negY,
      kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄, kw_lrApt_WF_a₆,
      map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one])

theorem kw_lrApt_aeval_lrAdd_X (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_X W) = -(W_F).addX P Q := by
  simp_check1
  ring

theorem kw_lrApt_aeval_lrAdd_Y (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -(W_F).addY P Q := by
  rw [show (W_F).addY P Q
      = -(W_F).negAddY P Q - (W_F).a₁ * (W_F).addX P Q - (W_F).a₃ * (W_F).addZ P Q from
    (W_F).negY_eq _ _ _]
  simp only [kw_lrAdd_Y, kw_lrAdd_starY, kw_lrAdd_starX, kw_lrAdd_starZ,
    kw_lrAdd_c₁₂, kw_lrAdd_c₂₁, Projective.negAddY, Projective.addX, Projective.addZ,
    kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄, kw_lrApt_WF_a₆,
    map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
    Sum.elim_inl, Sum.elim_inr]
  ring

theorem kw_lrApt_aeval_lrAdd_Z (P Q : Fin 3 → F) :
    aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -(W_F).addZ P Q := by
  simp_check1
  ring

end Check1
section Check2b

set_option maxHeartbeats 0 in

theorem kw_lrApt_aeval_lrSym_cross_XZ {P : Fin 3 → F} (hP : (W_F).Equation P) :
    aeval (Sum.elim P P) (kw_lrSym_X W) * (W_F).dblZ P
      = aeval (Sum.elim P P) (kw_lrSym_Z W) * (W_F).dblX P := by
  have heq := (Projective.equation_iff P).mp hP
  simp only [kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄,
    kw_lrApt_WF_a₆] at heq
  linear_combination (norm :=
    (simp only [kw_lrSym_X, kw_lrSym_Z, Projective.dblZ, Projective.dblX, Projective.negY,
      kw_lrApt_WF_a₁, kw_lrApt_WF_a₂, kw_lrApt_WF_a₃, kw_lrApt_WF_a₄, kw_lrApt_WF_a₆,
      map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C,
      Sum.elim_inl, Sum.elim_inr]; ring1))
    ((6:F) * P 0 ^ 5 * (algebraMap R F W.a₁) ^ 4
        + (18:F) * P 0 ^ 5 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂)
        + (54:F) * P 0 ^ 5 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃)
        + (30:F) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₁) ^ 3
        + (72:F) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂)
        + (108:F) * P 0 ^ 4 * P 1 * (algebraMap R F W.a₃)
        + (2:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 6
        + (14:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₂)
        + (24:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃)
        + (24:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) ^ 2
        - ((18:F)) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₄)
        + (90:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        + (54:F) * P 0 ^ 4 * P 2 * (algebraMap R F W.a₃) ^ 2
        + (54:F) * P 0 ^ 3 * P 1 ^ 2 * (algebraMap R F W.a₁) ^ 2
        + (72:F) * P 0 ^ 3 * P 1 ^ 2 * (algebraMap R F W.a₂)
        + (10:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 5
        + (64:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂)
        + (72:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃)
        + (96:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2
        - ((72:F)) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₄)
        + (180:F) * P 0 ^ 3 * P 1 * P 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        + (8:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 5 * (algebraMap R F W.a₃)
        + (6:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₄)
        + (44:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        + (24:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (36:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 2
        - ((54:F)) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₆)
        + (48:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃)
        + (18:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (72:F) * P 0 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        + (48:F) * P 0 ^ 2 * P 1 ^ 3 * (algebraMap R F W.a₁)
        + (18:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) ^ 4
        + (96:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂)
        + (90:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃)
        + (96:F) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₂) ^ 2
        - ((72:F)) * P 0 ^ 2 * P 1 ^ 2 * P 2 * (algebraMap R F W.a₄)
        + (30:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃)
        + (24:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₄)
        + (144:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        + (96:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (54:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2
        - ((216:F)) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₆)
        + (96:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃)
        + (36:F) * P 0 ^ 2 * P 1 * P 2 ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (12:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 4 * (algebraMap R F W.a₃) ^ 2
        + (18:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (48:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        + (6:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₄) ^ 2
        + (48:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (24:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 3
        - ((54:F)) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        + (24:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₂) ^ 2 * (algebraMap R F W.a₃) ^ 2
        + (36:F) * P 0 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        + (24:F) * P 0 * P 1 ^ 4
        + (16:F) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₁) ^ 3
        + (64:F) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂)
        + (84:F) * P 0 * P 1 ^ 3 * P 2 * (algebraMap R F W.a₃)
        + (36:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃)
        + (24:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₄)
        + (144:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        + (96:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₄)
        + (36:F) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₃) ^ 2
        - ((216:F)) * P 0 * P 1 ^ 2 * P 2 ^ 2 * (algebraMap R F W.a₆)
        + (30:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 2
        + (48:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (96:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        + (24:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₄) ^ 2
        + (96:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (12:F) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₃) ^ 3
        - ((108:F)) * P 0 * P 1 * P 2 ^ 3 * (algebraMap R F W.a₃) * (algebraMap R F W.a₆)
        + (8:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 3 * (algebraMap R F W.a₃) ^ 3
        + (18:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        + (20:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 3
        + (12:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 2
        + (24:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        + (6:F) * P 0 * P 2 ^ 4 * (algebraMap R F W.a₃) ^ 4
        + (8:F) * P 1 ^ 4 * P 2 * (algebraMap R F W.a₁) ^ 2
        + (32:F) * P 1 ^ 4 * P 2 * (algebraMap R F W.a₂)
        + (16:F) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃)
        + (64:F) * P 1 ^ 3 * P 2 ^ 2 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃)
        + (18:F) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 2
        + (24:F) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) * (algebraMap R F W.a₄)
        + (48:F) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 2
        + (24:F) * P 1 ^ 2 * P 2 ^ 3 * (algebraMap R F W.a₄) ^ 2
        + (10:F) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 3
        + (24:F) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄)
        + (16:F) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 3
        + (24:F) * P 1 * P 2 ^ 4 * (algebraMap R F W.a₃) * (algebraMap R F W.a₄) ^ 2
        + (2:F) * P 2 ^ 5 * (algebraMap R F W.a₁) ^ 2 * (algebraMap R F W.a₃) ^ 4
        + (6:F) * P 2 ^ 5 * (algebraMap R F W.a₁) * (algebraMap R F W.a₃) ^ 3 * (algebraMap R F W.a₄)
        + (2:F) * P 2 ^ 5 * (algebraMap R F W.a₂) * (algebraMap R F W.a₃) ^ 4
        + (6:F) * P 2 ^ 5 * (algebraMap R F W.a₃) ^ 2 * (algebraMap R F W.a₄) ^ 2) * heq

end Check2b

end

set_option maxHeartbeats 6400000 in
theorem solution.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_X W) = -((W.baseChange F).toProjective).addX P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Y W) = -((W.baseChange F).toProjective).addY P Q)
    ∧ (∀ P Q : Fin 3 → F, MvPolynomial.aeval (Sum.elim P Q) (kw_lrAdd_Z W) = -((W.baseChange F).toProjective).addZ P Q)
    ∧ (∀ P : Fin 3 → F, ((W.baseChange F).toProjective).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_X W) * ((W.baseChange F).toProjective).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * ((W.baseChange F).toProjective).dblX P) :=
  ⟨fun P Q => kw_lrApt_aeval_lrAdd_X W F P Q,
   fun P Q => kw_lrApt_aeval_lrAdd_Y W F P Q,
   fun P Q => kw_lrApt_aeval_lrAdd_Z W F P Q,
   fun P hP => kw_lrApt_aeval_lrSym_cross_XZ W F (P := P) hP⟩

end S_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ
end P2MW
export P2MW.S_WeierstrassProjModel_kw_a2_checks_addXYZ_crossXZ (solution)
