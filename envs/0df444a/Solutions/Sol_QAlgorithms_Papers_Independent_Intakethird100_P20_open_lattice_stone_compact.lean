-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.open_lattice_stone_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:53:55.266744+00:00
-- url     : https://prove2.me/submissions/9b5dc352-c836-4972-8869-1d725317c7b7

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_heyting_stone_compact
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Corollary 3.4; de Groote, Observables I, PDF p./pp. 56.
-/
theorem solution {M : Type u} [TopologicalSpace M] : CompactSpace (StoneSpectrum (Opens M)) := by
  exact heyting_stone_compact (L := Opens M)
