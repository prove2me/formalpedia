-- Prove2me | solution 1 for WilliamsonShmoys.retained_component_treewidth_from_band_induced_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:36:36.165805+00:00
-- url     : https://prove2.me/submissions/f642e64f-5a45-4ed0-89ed-7d5bd01b4588

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE


theorem solution {V : Type} [DecidableEq V] (G : SimpleGraph V) (R B : Set V) (Q : {x : V // x ∈ R} → Prop) (hQB : ∀ x : {x : V // x ∈ R}, Q x → (x : V) ∈ B) (w : Nat) : RobertsonSeymour1986.GM5.TreewidthLE (G.induce B) w → RobertsonSeymour1986.GM5.TreewidthLE ((G.induce R).induce Q) w := by
  classical
  rintro ⟨T, hT, t, X, ⟨htree, hcov, hedge, hpath⟩, hcard⟩
  let ι : {y : {x : V // x ∈ R} // Q y} → {x : V // x ∈ B} := fun y => ⟨y.1.1, hQB y.1 y.2⟩
  have hι : Function.Injective ι := by
    intro y z h
    apply Subtype.ext; apply Subtype.ext
    simpa [ι] using congrArg Subtype.val h
  refine ⟨T, hT, t, fun s => (X s).preimage ι hι.injOn, ⟨htree, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    obtain ⟨s, hs⟩ := hcov (ι v)
    exact ⟨s, by simpa using hs⟩
  · intro x y hxy
    obtain ⟨s, hx, hy⟩ := hedge (ι x) (ι y) (by simpa [ι] using hxy)
    exact ⟨s, by simpa using hx, by simpa using hy⟩
  · intro s s' s'' p hp hs' y hy
    simp only [Finset.mem_inter, Finset.mem_preimage] at hy ⊢
    exact hpath s s' s'' p hp hs' (Finset.mem_inter.2 hy)
  · intro s
    exact (Finset.card_le_card_of_injOn ι (fun y hy => by simpa using hy) hι.injOn).trans (hcard s)
