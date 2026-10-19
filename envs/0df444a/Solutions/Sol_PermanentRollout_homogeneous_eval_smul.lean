-- Prove2me | solution 1 for PermanentRollout.homogeneous_eval_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/b7f3d78b-9550-4de2-8869-ac62ea9df8d7

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_linearCoordinatePolynomial_isHomogeneous
import Theorems.Thm_PermanentRollout_eval_aeval_linearCoordinatePolynomial
import Theorems.Thm_PermanentRollout_homogeneous_fin_one_eval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m e : ℕ}
    (f : MvPolynomial (Fin m) ℂ) (hf : f.IsHomogeneous e)
    (a : ℂ) (v : Fin m → ℂ) :
    MvPolynomial.eval (a • v) f = a ^ e * MvPolynomial.eval v f := by
  let W := oneDimensionalInputSlice v
  have hg :
      (MvPolynomial.aeval
        (fun row => linearCoordinatePolynomial W row) f).IsHomogeneous e := by
    simpa only [one_mul] using
      hf.aeval (fun row => linearCoordinatePolynomial W row)
        (fun row => linearCoordinatePolynomial_isHomogeneous W row)
  have hline := homogeneous_fin_one_eval hg (fun _ : Fin 1 => a)
  change
    MvPolynomial.eval (fun _ : Fin 1 => a)
        (MvPolynomial.aeval
          (fun row => linearCoordinatePolynomial W row) f) =
      a ^ e *
        MvPolynomial.eval (fun _ : Fin 1 => 1)
          (MvPolynomial.aeval
            (fun row => linearCoordinatePolynomial W row) f) at hline
  rw [eval_aeval_linearCoordinatePolynomial,
    eval_aeval_linearCoordinatePolynomial] at hline
  simpa [W, oneDimensionalInputSlice] using hline
end PermanentRollout
