-- Prove2me | solution 1 for PhosphorylationSharpness.dense_inventory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:52.582718+00:00
-- url     : https://prove2.me/submissions/92d4db37-3b61-4e37-ac44-59d4551ffad4

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
import Theorems.Thm_PhosphorylationSharpness_DensePositive_degree_eq


set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) (u : ℝ) :
    inventory (fun i : Fin (m+1) => p.coeff i) u=p.eval u := by
  rw [eval_eq_sum_range' (show p.natDegree < m+1 by rw [hp.degree_eq]; omega)]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i*u^i) (m+1)
end PhosphorylationSharpness
