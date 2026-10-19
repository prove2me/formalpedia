-- Prove2me | solution 1 for QAlgorithms.Nannicini.exp_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:06:58.631799+00:00
-- url     : https://prove2.me/submissions/fbd55616-1406-4664-ad13-a96c759c360c

import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms

set_option autoImplicit false

theorem solution {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (H : Matrix (Qubits n) (Qubits n) ℂ)
    (_hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • (U * H * star U)) =
      U * NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * star U := by
  let u : (Matrix (Qubits n) (Qubits n) ℂ)ˣ :=
    ⟨U, star U, Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩
  simpa only [u, Units.val_mk, Units.inv_mk,
    Matrix.mul_smul, Matrix.smul_mul] using
    Matrix.exp_units_conj u ((Complex.I * (t : ℂ)) • H)
