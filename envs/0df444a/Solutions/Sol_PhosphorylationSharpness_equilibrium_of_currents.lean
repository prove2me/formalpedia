-- Prove2me | solution 1 for PhosphorylationSharpness.equilibrium_of_currents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:03.161029+00:00
-- url     : https://prove2.me/submissions/95cc2dee-1668-4d31-801e-84342580a2b7

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Source

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open scoped BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {n : ℕ} (k : Rates n) (x : State n)
    (hE : ∀ i, kinaseNet k x i=k.c i*x.C i)
    (hF : ∀ i, phosphataseNet k x i=k.gamma i*x.D i)
    (hC : ∀ i, k.c i*x.C i=k.gamma i*x.D i) : Equilibrium k x := by
  simp [Equilibrium, field, hE, hF, hC]
end PhosphorylationSharpness
