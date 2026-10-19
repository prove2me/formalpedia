-- Prove2me | solution 2 for QAlgorithms.Nannicini.exp_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-17T21:21:12.175997+00:00
-- url     : https://prove2.me/submissions/0f21fd8e-257a-41ec-a2ed-a07fd118a083

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

set_option autoImplicit false
open QAlgorithms

theorem solution {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (H : Matrix (Qubits n) (Qubits n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • (U * H * star U)) =
      U * NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * star U := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  let u : (Matrix (Qubits n) (Qubits n) ℂ)ˣ := ⟨U, star U, h1, h2⟩
  have key := Matrix.exp_units_conj u ((Complex.I * (t : ℂ)) • H)
  have e : (Complex.I * (t : ℂ)) • (U * H * star U) =
      U * ((Complex.I * (t : ℂ)) • H) * star U := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact key
