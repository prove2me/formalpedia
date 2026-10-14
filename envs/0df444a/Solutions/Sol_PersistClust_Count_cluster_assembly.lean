-- Prove2me | solution 1 for PersistClust.Count.cluster_assembly
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T05:05:39.989675+00:00
-- url     : https://prove2.me/submissions/60327e89-b0ec-4a2e-b362-a10df75a9861

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

/-- T5 lane tool (ORCH mission 2026-10-13): generic Hall-style cluster assembly. The
finite demand set `s` (with real "birth" values `bth`) counts into its fiber union via the
window inequality `hwin` and the net cover `hnet` applied ONCE at the FULL window
`[bth m, bth M]` spanned by the minimal and maximal birth values of `s`: no cluster chop
is needed, because `hnet`'s side condition ("every `s`-member whose birth is above the
window bottom stays below the window top") is witnessed by the maximal birth itself, and
`hwin` swallows all of `s` since the full window contains every birth. `hcone` (cone
inclusions) and `hdisj` (2ε-separation of fibers) record the cluster geometry for the
downstream `hqcB` site; the count itself does not need them. -/
theorem solution {X Q : Type}
    (ε : ℝ) (hε : 0 ≤ ε) (bth : X → ℝ) (s : Set X) (hs : s.Finite)
    (fib : X → Set Q) (supply : ℝ → ℝ → Set Q)
    (hwin : ∀ L R : ℝ, L ≤ R → {x : X | L ≤ bth x ∧ bth x ≤ R}.encard ≤ (supply L R).encard)
    (hcone : ∀ (L R : ℝ), L ≤ R → ∀ x ∈ s, L ≤ bth x → bth x ≤ R → fib x ⊆ supply L R)
    (hnet : ∀ (L R : ℝ), L ≤ R → (∀ x ∈ s, L ≤ bth x → bth x ≤ R) → supply L R ⊆ ⋃ x ∈ s, fib x)
    (hdisj : ∀ x ∈ s, ∀ x' ∈ s, ∀ t : ℝ, bth x ≤ t → t + 2 * ε < bth x' → fib x ∩ fib x' = ∅) :
    s.encard ≤ (⋃ x ∈ s, fib x).encard := by
  rcases s.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · subst h
    exact (le_of_eq Set.encard_empty).trans zero_le
  · obtain ⟨m, _, hmin⟩ := s.exists_min_image bth hs ⟨x₀, hx₀⟩
    obtain ⟨M, hMs, hmax⟩ := s.exists_max_image bth hs ⟨x₀, hx₀⟩
    have hmM : bth m ≤ bth M := hmin M hMs
    have hsub : s ⊆ {x : X | bth m ≤ bth x ∧ bth x ≤ bth M} :=
      fun x hx ↦ ⟨hmin x hx, hmax x hx⟩
    have hnetm : supply (bth m) (bth M) ⊆ ⋃ x ∈ s, fib x :=
      hnet _ _ hmM (fun x hx _ ↦ hmax x hx)
    calc s.encard ≤ {x : X | bth m ≤ bth x ∧ bth x ≤ bth M}.encard :=
          Set.encard_le_encard hsub
      _ ≤ (supply (bth m) (bth M)).encard := hwin _ _ hmM
      _ ≤ (⋃ x ∈ s, fib x).encard := Set.encard_le_encard hnetm
