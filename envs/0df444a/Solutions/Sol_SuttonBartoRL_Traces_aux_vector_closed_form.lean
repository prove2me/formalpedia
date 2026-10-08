-- Prove2me | solution 1 for SuttonBartoRL.Traces.aux_vector_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:55:05.832233+00:00
-- url     : https://prove2.me/submissions/26bb0e03-0060-41bf-8ab7-50217d36ec5b

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

open Matrix in
theorem d2e9d15f_fade_mulVec {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) (v : Fin d → ℝ) :
    SuttonBartoRL.Traces.fadingMatrix α x t *ᵥ v = v - (α * (x t ⬝ᵥ v)) • x t := by
  rw [SuttonBartoRL.Traces.fadingMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  ring

namespace SuttonBartoRL.Traces

open Matrix

theorem d2e9d15f_main {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (t : ℕ) :
    auxVec α x w₀ t = fadeProd α x 0 t *ᵥ w₀ := by
  induction t with
  | zero => simp [auxVec, fadeProd, d2e9d15f_fade_mulVec]
  | succ n ih =>
    rw [auxVec, fadeProd, if_pos (Nat.zero_le _), ← Matrix.mulVec_mulVec, ← ih,
      d2e9d15f_fade_mulVec]

end SuttonBartoRL.Traces

open Matrix SuttonBartoRL.Traces in
theorem solution {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (t : ℕ) :
    auxVec α x w₀ t = fadeProd α x 0 t *ᵥ w₀ := by
  exact SuttonBartoRL.Traces.d2e9d15f_main α x w₀ t

