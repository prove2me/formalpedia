-- Prove2me | solution 1 for PhosphorylationSharpness.DensePositive.scaled_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:55.750806+00:00
-- url     : https://prove2.me/submissions/25bdb363-9da5-4b14-a859-25306a50e7f2

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_DensePositive_degree_eq

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
namespace DensePositive
theorem _root_.solution {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    Tendsto (fun r : ℝ => p.eval r / r^m) atTop (𝓝 (p.coeff m)) := by
  have hp0 : p ≠ 0 := by
    intro h
    have := hp.1 0 (by omega)
    simp [h] at this
  have hd : p.degree = (X^m : ℝ[X]).degree := by
    rw [degree_eq_natDegree hp0, hp.degree_eq, degree_X_pow]
  have h := p.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (X^m) hd
  simpa [leadingCoeff, hp.degree_eq] using h
end DensePositive
end PhosphorylationSharpness
