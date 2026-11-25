-- Prove2me | solution 1 for PositivityTheory.Sph.M2.GenA.dg_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:54.669799+00:00
-- url     : https://prove2.me/submissions/30771c79-6765-4703-8e7f-8bef697a42bd

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_conj_eq
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_dg_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace PositivityTheory.Sph.M2.GenA
theorem _root_.solution (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) (σ : Equiv.Perm n) (D : n → Kˣ) :
    ψ (dg D) = ψ (dg fun i => D (σ i)) := by
  have hd : ((1 : Matrix n n K).submatrix σ id).det ≠ 0 := by
    rw [det_permute, det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
  refine conj_eq ψ hpos (g := GeneralLinearGroup.mkOfDetNeZero _ hd) ?_
  ext a b
  rw [Units.val_mul, Units.val_mul, dg_val, dg_val, diagonal_mul, mul_diagonal]
  show ((1 : Matrix n n K).submatrix σ id) a b * _ = _ * ((1 : Matrix n n K).submatrix σ id) a b
  simp only [submatrix_apply, id, Matrix.one_apply]
  split_ifs with e
  · simp [e]
  · simp
end PositivityTheory.Sph.M2.GenA
