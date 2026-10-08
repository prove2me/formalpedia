-- Prove2me | solution 1 for PhilipponMultiplicity.prime_nsmul_range_has_nonempty_interior
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T11:04:34.398913+00:00
-- url     : https://prove2.me/submissions/ece0518f-7202-47f7-a739-771e2dc9378b

import Theorems.Thm_PhilipponMultiplicity_prime_nsmul_range_is_constructible
import Theorems.Thm_PhilipponMultiplicity_prime_nsmul_range_closure_has_nonempty_interior
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Topology.Constructible

section

set_option autoImplicit false

namespace PhilipponMultiplicity.ConstructibleInterior
open Set Topology

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- Finite Boolean combinations of open sets have nowhere-dense boundary. -/
theorem frontier_interior_empty (hs : IsConstructible s) :
    interior (frontier s) = ∅ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    rw [← frontier_compl U]
    exact interior_frontier hU.isClosed_compl
  | union s hs t ht ihs iht =>
    apply Set.subset_empty_iff.mp
    calc
      interior (frontier (s ∪ t)) ⊆ interior (frontier s ∪ frontier t) :=
        interior_mono ((frontier_union_subset s t).trans
          (union_subset_union inter_subset_left inter_subset_right))
      _ = ∅ := by rw [interior_union_isClosed_of_interior_empty isClosed_frontier iht, ihs]
  | compl s hs ih => simpa only [frontier_compl] using ih

theorem dense_frontier_compl (hs : IsConstructible s) : Dense (frontier s)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (frontier_interior_empty hs)

/-- Removing the boundary does not change the interior of the closure. -/
theorem interior_closure_eq (hs : IsConstructible s) :
    interior (closure s) = interior (closure (interior s)) := by
  apply Set.Subset.antisymm
  · calc
      interior (closure s) ⊆ interior (closure (interior s) ∪ frontier s) := by
        apply interior_mono
        rw [closure_eq_interior_union_frontier s]
        exact union_subset_union_left _ subset_closure
      _ = interior (closure (interior s)) :=
        interior_union_isClosed_of_interior_empty isClosed_closure (frontier_interior_empty hs)
  · exact interior_mono (closure_mono interior_subset)

theorem interior_closure_empty_iff (hs : IsConstructible s) :
    interior (closure s) = ∅ ↔ interior s = ∅ := by
  constructor
  · intro h
    apply Set.subset_empty_iff.mp
    exact (interior_mono subset_closure).trans (by rw [h])
  · intro h
    rw [closure_eq_interior_union_frontier s, h, empty_union]
    exact frontier_interior_empty hs

theorem nonempty_interior_of_closure (hs : IsConstructible s)
    (h : (interior (closure s)).Nonempty) : (interior s).Nonempty := by
  by_contra hn
  have hs0 : interior s = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  have hc0 := (interior_closure_empty_iff hs).mpr hs0
  simpa only [hc0, Set.not_nonempty_empty] using h

theorem dense_interior (hs : IsConstructible s) (hd : Dense s) :
    Dense (interior s) := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_iff_forall.mpr
  intro x
  apply interior_subset
  rw [← interior_closure_eq hs, hd.closure_eq, interior_univ]
  exact Set.mem_univ x

end PhilipponMultiplicity.ConstructibleInterior
end

section

set_option autoImplicit false

namespace PhilipponMultiplicity

theorem prime_multiplication_interior_of_constructible_and_closure
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (p : ℕ) (hp : p.Prime)
    (hconstructible : @Topology.IsConstructible G.Point G.zariskiTopology (Set.range (fun x : G.Point => p • x)))
    (hclosure : (@interior _ G.zariskiTopology
      (@closure _ G.zariskiTopology (Set.range (fun x : G.Point => p • x)))).Nonempty) :
    (@interior _ G.zariskiTopology (Set.range (fun x : G.Point => p • x))).Nonempty := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact ConstructibleInterior.nonempty_interior_of_closure hconstructible hclosure

end PhilipponMultiplicity
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (p : ℕ) (hp : p.Prime) :
    (@interior _ G.zariskiTopology (Set.range (fun x : G.Point => p • x))).Nonempty := by
  exact prime_multiplication_interior_of_constructible_and_closure K hK G p hp
    (prime_nsmul_range_is_constructible K hK G p hp)
    (prime_nsmul_range_closure_has_nonempty_interior K hK G p hp)
