-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.commutant_antitone_double_triple
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:23:47.201831+00:00
-- url     : https://prove2.me/submissions/3c2a4342-a4a9-45f1-8b5a-f6f9559715d3

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_commutation_symmetric_iff_orthomodular
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 2.1; de Groote, Observables I, PDF pp. 23.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L]
    (perp : L → L) (horth : IsOrthomodular perp) (S T : Set L) :
    (S ⊆ T → latticeCommutant perp T ⊆ latticeCommutant perp S) ∧
    S ⊆ latticeCommutant perp (latticeCommutant perp S) ∧
    latticeCommutant perp S =
      latticeCommutant perp (latticeCommutant perp (latticeCommutant perp S)) := by
  have hsym := (commutation_symmetric_iff_orthomodular perp horth.1).mpr horth
  have hanti {U V : Set L} (hUV : U ⊆ V) :
      latticeCommutant perp V ⊆ latticeCommutant perp U := by
    intro b hb a ha
    exact hb a (hUV ha)
  have hdouble (U : Set L) : U ⊆ latticeCommutant perp (latticeCommutant perp U) := by
    intro a ha b hb
    exact hsym a b (hb a ha)
  refine ⟨fun h => hanti h, hdouble S, ?_⟩
  exact Set.Subset.antisymm (hdouble (latticeCommutant perp S)) (hanti (hdouble S))
