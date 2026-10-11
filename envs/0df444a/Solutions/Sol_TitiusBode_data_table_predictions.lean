-- Prove2me | solution 1 for TitiusBode.data_table_predictions
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:32.441809+00:00
-- url     : https://prove2.me/submissions/e00ee3ef-87a8-4519-95fb-6db13c3eb1b5

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution :
    tbAU ⊥ = 0.4 ∧ tbAU ((0 : ℕ) : WithBot ℕ) = 0.7 ∧ tbAU ((1 : ℕ) : WithBot ℕ) = 1.0 ∧
    tbAU ((2 : ℕ) : WithBot ℕ) = 1.6 ∧ tbAU ((3 : ℕ) : WithBot ℕ) = 2.8 ∧
    tbAU ((4 : ℕ) : WithBot ℕ) = 5.2 ∧ tbAU ((5 : ℕ) : WithBot ℕ) = 10.0 ∧
    tbAU ((6 : ℕ) : WithBot ℕ) = 19.6 ∧ tbAU ((7 : ℕ) : WithBot ℕ) = 38.8 ∧
    tbAU ((8 : ℕ) : WithBot ℕ) = 77.2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [tbAU, twoPowExt]
