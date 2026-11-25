-- Prove2me | solution 1 for PIQnLT.exp_Lz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:40.752589+00:00
-- url     : https://prove2.me/submissions/db0eea8e-7e56-4bcd-bb72-d4607b7306a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Theorems.Thm_P2M_PIQnLT__Lev_eq_d6fc93f29a45
import Theorems.Thm_PIQnLT_LzL_apply
import Theorems.Thm_PIQnLT_Lz_one
import Theorems.Thm_PIQnLT_Lz_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
set_option backward.isDefEq.respectTransparency false
namespace PIQnLT
theorem _root_.solution (hL : LevHom) (Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    NormedSpace.exp (Lz k i r' Y) = ιLev k i r' (NormedSpace.exp Y) := by
  have h0 : ιLev k i r' 0 = 1 - Lz k i r' 1 := by
    rw [← Lz_one (k := k) (i := i) (r' := r') hL]
    abel
  letI : NormedRing (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Lz k i r' Y)
  have hc : Continuous (LzL k i r') := (LzL k i r').continuous_of_finiteDimensional
  have h2 := h1.map (LzL k i r') hc
  have hfun : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n) =
      (fun n : ℕ => (LzL k i r') (((n.factorial : ℂ)⁻¹) • Y ^ n) +
        (if n = 0 then (1 - Lz k i r' 1) else 0)) := by
    funext n
    cases n with
    | zero => simp [LzL_apply]
    | succ m =>
      have hm : m + 1 ≠ 0 := by omega
      rw [if_neg hm, add_zero, LinearMap.map_smul, LzL_apply, Lz_pow hL]
  have h5 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n)
      (LzL k i r' (NormedSpace.exp Y) + (1 - Lz k i r' 1)) := by
    rw [hfun]
    exact h2.add (hasSum_ite_eq 0 (1 - Lz k i r' 1))
  have e := h3.unique h5
  refine e.trans ?_
  rw [ιLev_eq, h0]
  rfl
end PIQnLT
