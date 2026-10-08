-- Prove2me | solution 1 for VBSDP.Potential.phi_formula_55
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:45:07.599632+00:00
-- url     : https://prove2.me/submissions/ad784781-8b3f-47dd-a1d7-68a14d2590ea

import Mathlib
import Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
import Definitions.Def_VBSDP_Potential_phi
open VBSDP.Potential
theorem solution {m n : ℕ} [NeZero n] (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (h : IsStrictlyFeasiblePair c F₀ F x Z) :
    phi ν F₀ F x Z =
      (n + ν * Real.sqrt n) * Real.log (VBSDP.Duality.lmi F₀ F x * Z).trace -
      Real.log (VBSDP.Duality.lmi F₀ F x).det - Real.log Z.det - n * Real.log n := by
  have hA := h.1.det_pos
  have hZ := h.2.1.det_pos
  unfold phi psi
  rw [Matrix.det_mul, Real.log_mul hA.ne' hZ.ne']
  ring


#print axioms solution
