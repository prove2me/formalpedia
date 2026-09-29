-- Prove2me | solution 1 for Problem97.K4_delete_of_indeg_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T02:21:43.401334+00:00
-- url     : https://prove2.me/submissions/ccd3e607-fb46-47de-a493-c7a12670e50b

import Definitions.Def_Problem97_IsWitnessSystem
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Theorems.Thm_Problem97_card_ge_five_of_K4

open scoped EuclideanGeometry
open Finset

open Problem97

namespace WitnessDeletionSupport

lemma convexIndep_erase {A : Finset ℝ²}
    (hconv : Problem97.ConvexIndep A)
    (x : ℝ²) : Problem97.ConvexIndep (A.erase x) := by
  classical
  intro a ha hm
  exact hconv a (erase_subset x A ha)
    (convexHull_mono (Set.sdiff_subset_sdiff_left
      (coe_subset.mpr (erase_subset x A))) hm)

end WitnessDeletionSupport

theorem solution {A : Finset ℝ²} (hne : A.Nonempty)
    (hconv : ConvexIndep A) (hK4 : HasNEquidistantProperty 4 A)
    {S : ℝ² → Finset ℝ²} (hS : IsWitnessSystem A S)
    {x : ℝ²} (hxA : x ∈ A) (hindeg0 : ∀ y ∈ A, x ∉ S y) :
    (A.erase x).Nonempty ∧ ConvexIndep (A.erase x) ∧
      HasNEquidistantProperty 4 (A.erase x) := by
  have h5 : 5 ≤ A.card := card_ge_five_of_K4 hne hK4
  have herase : (A.erase x).card = A.card - 1 := Finset.card_erase_of_mem hxA
  refine ⟨Finset.card_pos.mp (by omega), WitnessDeletionSupport.convexIndep_erase hconv x, ?_⟩
  intro y hy
  obtain ⟨hyx, hyA⟩ := Finset.mem_erase.mp hy
  obtain ⟨hSsub, hScard, r, hrpos, hSr⟩ := hS y hyA
  refine ⟨r, hrpos, ?_⟩
  have hSsub' : S y ⊆ (A.erase x).filter (fun q => dist y q = r) := by
    intro q hq
    have hqx : q ≠ x := by
      rintro rfl
      exact hindeg0 y hyA hq
    have hqA : q ∈ A := (Finset.mem_erase.mp (hSsub hq)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hqx, hqA⟩, hSr q hq⟩
  exact hScard.trans (Finset.card_le_card hSsub')
