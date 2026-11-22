-- Prove2me | solution 1 for TopGroupoid.TopologicalGroupoid.isClosedEmbedding_unit_and_isQuotientMap_src_tgt
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:45:40.224622+00:00
-- url     : https://prove2.me/submissions/e68beac1-9fb0-4760-9457-f9875506ed95

import Definitions.Def_TopGroupoid_TopologicalGroupoid
import Theorems.Thm_CGWH_isClosedEmbedding_and_isQuotientMap_of_leftInverse

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open TopGroupoid

theorem solution
    {X R : Type u} [TopologicalSpace X] [TopologicalSpace R] (G : TopologicalGroupoid X R) :
    IsClosedEmbedding G.unit ∧ IsQuotientMap G.src ∧ IsQuotientMap G.tgt := by
  haveI := G.compactlyGeneratedSpace_arr
  haveI := G.weaklyHausdorffSpace_arr
  have h1 := CGWH.isClosedEmbedding_and_isQuotientMap_of_leftInverse G.continuous_src
    G.continuous_unit (fun x => G.src_unit x)
  have h2 := CGWH.isClosedEmbedding_and_isQuotientMap_of_leftInverse G.continuous_tgt
    G.continuous_unit (fun x => G.tgt_unit x)
  exact ⟨h1.1, h1.2, h2.2⟩
