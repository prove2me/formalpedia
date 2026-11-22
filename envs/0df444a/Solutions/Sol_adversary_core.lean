-- Prove2me | solution 1 for adversary_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:09.332869+00:00
-- url     : https://prove2.me/submissions/360c6514-130d-494a-acd7-084d40006657

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X : Type}
    (L : OnlineLearner X Bool) (s : L.State)
    {C : ConceptClass X Bool} {n : ℕ}
    (T : LTree X n) (hT : T.isShattered C) (hne : C.Nonempty) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧
      L.mistakesFrom s c seq = n := by
  induction n generalizing C s with
  | zero =>
    obtain ⟨c₀, hc₀⟩ := hne
    exact ⟨[], c₀, hc₀, rfl⟩
  | succ k ih =>
    match T, hT with
    | .branch x l r, ⟨⟨ct, hct, hctx⟩, ⟨cf, hcf, hcfx⟩, hsl, hsr⟩ =>
      by_cases hpred : L.predict s x = true
      · have hne_f : ({c ∈ C | c x = false}).Nonempty := ⟨cf, hcf, hcfx⟩
        obtain ⟨seq', c', hc'mem, hcount⟩ :=
          ih (L.update s x false) r hsr hne_f
        refine ⟨x :: seq', c', hc'mem.1, ?_⟩
        simp only [OnlineLearner.mistakesFrom, hc'mem.2, hpred]
        simp [hcount]; omega
      · have hpf : L.predict s x = false := by
          cases h : L.predict s x <;> simp_all
        have hne_t : ({c ∈ C | c x = true}).Nonempty := ⟨ct, hct, hctx⟩
        obtain ⟨seq', c', hc'mem, hcount⟩ :=
          ih (L.update s x true) l hsl hne_t
        refine ⟨x :: seq', c', hc'mem.1, ?_⟩
        simp only [OnlineLearner.mistakesFrom, hc'mem.2, hpf]
        simp [hcount]; omega
