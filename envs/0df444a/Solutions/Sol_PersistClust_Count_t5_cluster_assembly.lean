-- Prove2me | solution 1 for PersistClust.Count.t5_cluster_assembly
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T11:44:59.17353+00:00
-- url     : https://prove2.me/submissions/9b06fe27-cd37-4eeb-9641-8792f2260a56

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

/-- Cluster assembly (generic, level-free): a finite point set s with a birth
map bth, per-point fiber sets fib, and a windowed supply family supply
satisfies |s| <= |union of the fibers| whenever four conditions hold:
every birth-window count is bounded by the supply on that window (hwin),
each in-window point's fiber lies inside the supply (hcone), the
full-span supply is covered by the fibers (hnet, instantiable when the
whole set spans the window), and fibers of birth-remote points (cut at
any t leaving a gap of more than 2*eps) are disjoint (hdisj). Proof:
the min/max window carries all of s; hwin bounds that window's count
by the supply; hcone and hnet sandwich the supply between the
in-window fibers and the full fiber union; encard monotonicity closes
the chain. -/
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
