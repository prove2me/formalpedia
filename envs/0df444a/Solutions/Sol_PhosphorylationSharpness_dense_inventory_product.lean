-- Prove2me | solution 1 for PhosphorylationSharpness.dense_inventory_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:30.713826+00:00
-- url     : https://prove2.me/submissions/ffa1a1ae-d34f-4e14-8493-15031e6a217d

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
import Definitions.Def_proofs_PhosphorylationSharpness_Assembly
import Theorems.Thm_PhosphorylationSharpness_dense_step


set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    DensePositive ((1+X)*p) (m+1) := by
  have h := dense_step hp hp 1 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [add_mul] using h
end PhosphorylationSharpness
