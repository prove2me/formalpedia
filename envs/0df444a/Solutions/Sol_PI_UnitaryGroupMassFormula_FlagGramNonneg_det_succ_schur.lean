-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.det_succ_schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:16.571978+00:00
-- url     : https://prove2.me/submissions/70083324-bf92-47c2-b319-a48d07cd45f5

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_NatAddZeroFinOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det) :
    Z.det = (Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z (Fin.last r) (Fin.last r) - (fun b => Z (Fin.last r) (Fin.castSucc b)) ⬝ᵥ
        ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ (fun a => Z (Fin.castSucc a) (Fin.last r)))) := by
  haveI : Invertible (Z.submatrix Fin.castSucc Fin.castSucc) := Matrix.invertibleOfIsUnitDet _ h
  have hZ : Z.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks
      (Z.submatrix Fin.castSucc Fin.castSucc) (Matrix.of fun a (_ : Fin 1) => Z (Fin.castSucc a) (Fin.last r))
      (Matrix.of fun (_ : Fin 1) b => Z (Fin.last r) (Fin.castSucc b))
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => Z (Fin.last r) (Fin.last r)) := by
    ext (i | i) (j | j)
    · rfl
    · rw [Fin.fin_one_eq_zero j]
      rfl
    · rw [Fin.fin_one_eq_zero i]
      rfl
    · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      rfl
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv Z, hZ, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Fin 1)]
  congr 1
  rw [Matrix.sub_apply, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] <;> rfl
end PI.UnitaryGroupMassFormula.FlagGramNonneg
