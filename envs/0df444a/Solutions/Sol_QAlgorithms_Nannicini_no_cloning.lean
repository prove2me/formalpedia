-- Prove2me | solution 1 for QAlgorithms.Nannicini.no_cloning
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:02:33.745622+00:00
-- url     : https://prove2.me/submissions/ee542af1-8bdf-400c-9a40-f9c83c7bb0da

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false
open QAlgorithms

theorem solution (q : ℕ) :
    ¬ ∃ U : Matrix (Qubits q × Qubits q) (Qubits q × Qubits q) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits q × Qubits q) ℂ ∧
      ∀ ψ : EuclideanSpace ℂ (Qubits q), IsState ψ →
        act U (tensorVec ψ (zeroKet q)) = tensorVec ψ ψ := by
  rintro ⟨U, _, h⟩
  have he : IsState (zeroKet q) := by
    unfold IsState zeroKet ket
    simp
  have hφ : IsState (Complex.I • zeroKet q) := by
    unfold IsState
    rw [norm_smul]
    have := he
    unfold IsState at this
    simp [this]
  have h1 := h _ he
  have h2 := h _ hφ
  have e1 : tensorVec (Complex.I • zeroKet q) (zeroKet q) = Complex.I • tensorVec (zeroKet q) (zeroKet q) := by
    ext p
    simp [tensorVec, mul_assoc]
  have e2 : act U (Complex.I • tensorVec (zeroKet q) (zeroKet q)) = Complex.I • act U (tensorVec (zeroKet q) (zeroKet q)) := by
    ext p
    simp [act, Matrix.mulVec_smul]
  rw [e1, e2, h1] at h2
  have h3 := congrArg (fun w => w ((fun _ : Fin q => false), (fun _ : Fin q => false))) h2
  simp [tensorVec, zeroKet, ket] at h3
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h4 : Complex.I = Complex.I * Complex.I := by simpa using h3
  rw [this] at h4
  have := congrArg Complex.im h4
  simp at this
