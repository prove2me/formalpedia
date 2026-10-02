-- Prove2me | solution 1 for OPG37364.lps13Graph_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T14:46:11.340873+00:00
-- url     : https://prove2.me/submissions/17d1aacb-02ab-4336-aef2-de1ef5553289

import Definitions.Def_opg37364_lps13
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false

namespace OPG37364

variable {q : ℕ} [Fact q.Prime]

/-- The quadratic character of the determinant on GL₂. -/
noncomputable def lps13GLDetChar :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod q) →* ℤ :=
  (quadraticChar (ZMod q)).toMonoidHom.comp
    ((Units.coeHom (ZMod q)).comp Matrix.GeneralLinearGroup.det)

/-- Scalar matrices have square determinant, so their character is trivial. -/
theorem lps13GLDetChar_scalar (r : (ZMod q)ˣ) :
    lps13GLDetChar (Matrix.GeneralLinearGroup.scalar (Fin 2) r) = 1 := by
  change quadraticChar (ZMod q) ((Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin 2) r) : (ZMod q)ˣ) : ZMod q) = 1
  simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
    Units.val_pow_eq_pow_val] using quadraticChar_sq_one' r.ne_zero

/-- Determinant square class on PGL₂, with values +1 and -1. -/
noncomputable def lps13DetChar :
    Matrix.ProjGenLinGroup (Fin 2) (ZMod q) →* ℤ :=
  Matrix.ProjGenLinGroup.lift lps13GLDetChar (by
    ext r
    exact lps13GLDetChar_scalar r)

theorem lps13DetChar_mk (v : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
    lps13DetChar (Matrix.ProjGenLinGroup.mk v) =
      quadraticChar (ZMod q) (v.det : ZMod q) := rfl

theorem lps13DetChar_dichotomy (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    lps13DetChar v = 1 ∨ lps13DetChar v = -1 := by
  induction v using Matrix.ProjGenLinGroup.induction_on with
  | mk v => exact quadraticChar_dichotomy v.det.ne_zero

theorem lps13DetChar_ne_zero (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    lps13DetChar v ≠ 0 := by
  rcases lps13DetChar_dichotomy v with h | h <;> simp [h]

/-- True is the square-determinant class; false is the nonsquare class. -/
noncomputable def lps13Side (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) : Bool :=
  decide (lps13DetChar v = 1)

theorem lps13Side_mk_eq_true_iff (v : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
    lps13Side (Matrix.ProjGenLinGroup.mk v) = true ↔ IsSquare (v.det : ZMod q) := by
  change decide (quadraticChar (ZMod q) (v.det : ZMod q) = 1) = true ↔ _
  rw [decide_eq_true_eq]
  exact quadraticChar_one_iff_isSquare v.det.ne_zero

variable (hq : 13 < q) (i : LPS13Root q)

/-- Reuse the norm/determinant certificates in the published Stage 7 definitions. -/
theorem lps13GL_det_val (a : Fin 14) :
    ((lps13GL hq i a).det : ZMod q) = 13 := by
  change (lps13Matrix i a).det = 13
  rw [lps13Matrix, lps13QuaternionMatrix_det, lps13Quaternion_norm]
  norm_num

theorem lps13DetChar_generator (a : Fin 14) :
    lps13DetChar (lps13Generator hq i a) = legendreSym q 13 := by
  rw [lps13Generator, lps13DetChar_mk, lps13GL_det_val]
  simp [legendreSym]

theorem lps13Side_mul_generator (hnr : legendreSym q 13 = -1)
    (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) (a : Fin 14) :
    lps13Side (v * lps13Generator hq i a) ≠ lps13Side v := by
  rcases lps13DetChar_dichotomy v with hv | hv <;>
    simp [lps13Side, map_mul, lps13DetChar_generator, hnr, hv]

/-- The fixed-p=13 PGL Cayley graph is bipartite when 13 is a nonresidue modulo q. -/
theorem _root_.solution (hnr : legendreSym q 13 = -1) :
    IsBipartite (lps13Graph hq i) := by
  classical
  refine ⟨lps13Side, ?_⟩
  intro u v huv
  obtain ⟨_, s, hs, hmul⟩ := (SimpleGraph.mulCayley_adj' _ u v).mp huv
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  rcases hmul with hmul | hmul
  · subst v
    exact (lps13Side_mul_generator hq i hnr u a).symm
  · subst u
    exact lps13Side_mul_generator hq i hnr v a

end OPG37364
