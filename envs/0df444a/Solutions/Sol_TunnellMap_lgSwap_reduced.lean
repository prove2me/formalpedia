-- Prove2me | solution 1 for TunnellMap.lgSwap_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:51:03.938654+00:00
-- url     : https://prove2.me/submissions/5a30565c-fdff-4616-b53b-51dcec08efcd

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_dot_negTriple_self
import Theorems.Thm_TunnellMap_dot_comm


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution {uv : Triple × Triple} (h : IsReducedPair uv)
    (heq : dot uv.1 uv.1 = dot uv.2 uv.2) : IsReducedPair (lgSwap uv) := by
  obtain ⟨h₁, -⟩ := h
  refine ⟨?_, ?_⟩
  · show |2 * dot uv.2 (negTriple uv.1)| ≤ dot uv.2 uv.2
    rw [dot_negTriple_right, dot_comm uv.2 uv.1, ← heq, mul_neg, abs_neg]
    exact h₁
  · show dot uv.2 uv.2 ≤ dot (negTriple uv.1) (negTriple uv.1)
    rw [dot_negTriple_self]
    exact le_of_eq heq.symm
end TunnellMap
