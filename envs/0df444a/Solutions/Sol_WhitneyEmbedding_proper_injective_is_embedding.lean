-- Prove2me | solution 1 for WhitneyEmbedding.proper_injective_is_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T12:16:26.828105+00:00
-- url     : https://prove2.me/submissions/5b1ab6d3-39de-4618-a434-337638ba9eaa

import Mathlib
open Function Filter Module Set Topology

theorem solution {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    {f : X → Y} (hf_proper : IsProperMap f) (hf_inj : Injective f) :
    IsEmbedding f :=
  (IsClosedEmbedding.of_continuous_injective_isClosedMap hf_proper.continuous hf_inj
    hf_proper.isClosedMap).isEmbedding
