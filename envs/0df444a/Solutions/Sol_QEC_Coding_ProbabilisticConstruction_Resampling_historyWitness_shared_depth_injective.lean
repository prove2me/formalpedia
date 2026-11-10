-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_shared_depth_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:22:05.442134+00:00
-- url     : https://prove2.me/submissions/9518bfc8-f4f1-458f-ae49-517e7fd3ecd7

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_depth_time

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L : List I)
    (p q : List I) (hp : p ∈ historyWitness (supportGraph vars) root L)
    (hq : q ∈ historyWitness (supportGraph vars) root L)
    (v : V) (hpv : v ∈ vars (pathLabel root p)) (hqv : v ∈ vars (pathLabel root q))
    (hd : p.length = q.length) : p = q := by
  rw [← timedHistoryWitness_paths (supportGraph vars) root 0 L] at hp hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  have hforward := timedHistoryWitness_depth_time vars root 0 L a b ha hb v hpv hqv
  have hback := timedHistoryWitness_depth_time vars root 0 L b a hb ha v hqv hpv
  have ht : a.2 = b.2 := by omega
  exact congrArg Prod.fst (timedHistoryWitness_time_injective (supportGraph vars) root 0 L ha hb ht)
end QEC.Coding.ProbabilisticConstruction.Resampling
