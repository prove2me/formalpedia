-- Prove2me | solution 1 for OpenQuantumProblem35.isConstantConfig_constantConfig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:10.298356+00:00
-- url     : https://prove2.me/submissions/a4a4c42a-21ab-4105-aad0-7d1f84d35985

module
public import Mathlib
public import Definitions.Def_AME125_Defs

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {m d : ℕ} (a : Fin d) :
    IsConstantConfig (constantConfig (m := m) (d := d) a) := by
  intro i j
  rfl
end OpenQuantumProblem35
