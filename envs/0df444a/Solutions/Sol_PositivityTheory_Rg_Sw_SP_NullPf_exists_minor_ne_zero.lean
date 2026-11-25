-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.NullPf.exists_minor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:05.348586+00:00
-- url     : https://prove2.me/submissions/dc6177dc-1188-45e3-bf2c-a646f5e080cd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetEqZeroOfRankLt
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_NullPf_exists_rows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.NullPf
variable {K : Type*} [Field K]
namespace PositivityTheory.Rg.Sw.SP.NullPf
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I J : Fin k ↪ Fin n, (M.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows M hk
  set R : Matrix (Fin k) (Fin n) K := M.submatrix I id with hR
  have hRrank : R.rank = k := by
    have : LinearIndependent K R.row := hI
    simpa using this.rank_matrix
  have hRt : k ≤ Rᵀ.rank := by rw [rank_transpose, hRrank]
  obtain ⟨J, hJ⟩ := exists_rows Rᵀ hRt
  refine ⟨I, J, ?_⟩
  set T : Matrix (Fin k) (Fin k) K := Rᵀ.submatrix J id with hT
  have hTu : IsUnit T := by
    rw [← linearIndependent_rows_iff_isUnit]
    exact hJ
  have hTeq : T = (M.submatrix I J)ᵀ := by
    ext p q
    simp [T, R, transpose_apply, submatrix_apply]
  have := (Matrix.isUnit_iff_isUnit_det T).1 hTu
  rw [hTeq, det_transpose] at this
  exact this.ne_zero
end PositivityTheory.Rg.Sw.SP.NullPf
