-- Prove2me | solution 1 for SizeRamsey.Plan.isC4Map_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:22.652541+00:00
-- url     : https://prove2.me/submissions/051e0cec-8e29-4ef9-bc53-5f65b98f4e0e

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : IsC4Map G ![a, b, c, d] := by
  refine ⟨?_, hab, hbc, hcd, hda⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [hab.ne, hbc.ne, hcd.ne, hda.ne, hab.ne.symm,
    hbc.ne.symm, hcd.ne.symm, hda.ne.symm, hac.symm, hbd.symm]
end SizeRamsey.Plan
