-- Prove2me | solution 1 for ReciprocityTheory.Aut.mem_maxIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:57.537706+00:00
-- url     : https://prove2.me/submissions/b82d4970-d3f0-4587-bdd8-e62c6d63aedb

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace ReciprocityTheory.Aut
theorem _root_.solution (x : v.adicCompletionIntegers F) :
    x ∈ maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 := by
  have hint := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  constructor
  · intro hx
    exact lt_of_le_of_ne hle (fun h => hx ((hint.isUnit_iff_valuation_eq_one (x := x)).mpr h))
  · intro hx hu
    exact (ne_of_lt hx) ((hint.isUnit_iff_valuation_eq_one (x := x)).mp hu)
end ReciprocityTheory.Aut
