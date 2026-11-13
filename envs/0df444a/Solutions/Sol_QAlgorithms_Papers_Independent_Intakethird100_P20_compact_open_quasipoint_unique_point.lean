-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.compact_open_quasipoint_unique_point
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:29:27.820313+00:00
-- url     : https://prove2.me/submissions/6016a1aa-b35b-4994-bd61-6f9cbbab70e0

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_quasipoint_cluster_characterization
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {M : Type*} [TopologicalSpace M]
    [CompactSpace M] [T2Space M] (B : StoneSpectrum (Opens M)) :
    ∃! x : M, LiesOver B x := by
  classical
  letI : Nonempty {U : Opens M // U ∈ B.val} := by
    obtain ⟨U, hU⟩ := B.property.1.1
    exact ⟨⟨U, hU⟩⟩
  let T := fun U : {U : Opens M // U ∈ B.val} => closure (U.val : Set M)
  have hdir : Directed (· ⊇ ·) T := by
    intro U V
    obtain ⟨W, hW, hWU, hWV⟩ := B.property.1.2.2 U.val U.property V.val V.property
    exact ⟨⟨W, hW⟩, closure_mono hWU, closure_mono hWV⟩
  have hne (U : {U : Opens M // U ∈ B.val}) : (T U).Nonempty := by
    apply Set.Nonempty.closure
    apply (Opens.ne_bot_iff_nonempty U.val).mp
    intro hz
    exact B.property.1.2.1 (hz ▸ U.property)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hdir hne (fun _ => isClosed_closure.isCompact) (fun _ => isClosed_closure)
  have hlie : LiesOver B x := (open_quasipoint_cluster_characterization B x).1.mpr hx
  refine ⟨x, hlie, ?_⟩
  intro y hy
  have hyI := (open_quasipoint_cluster_characterization B y).1.mp hy
  change (⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M)) = {x} at hlie
  rw [hlie] at hyI
  exact hyI
