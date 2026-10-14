-- Prove2me | solution 1 for StabilityConjecture.periodic_hyperbolic_of_hyperbolic_nonwandering
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T20:11:41.472993+00:00
-- url     : https://prove2.me/submissions/7e3441e8-232a-40d1-b925-e405076d2707

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open StabilityConjecture ClosingLemma

namespace SC_B

/-- The forward orbit of a periodic point is finite. -/
theorem orbit_finite {α : Type*} (F : α → α) (p : α) (hp : p ∈ Function.periodicPts F) :
    (Set.range fun k : ℕ => F^[k] p).Finite := by
  obtain ⟨m, hm, hpm⟩ := Function.mem_periodicPts.mp hp
  have hEq : (Set.range fun k : ℕ => F^[k] p) = (fun k : ℕ => F^[k] p) '' Set.Iio m := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k % m, Set.mem_Iio.mpr (Nat.mod_lt _ hm), hpm.iterate_mod_apply k⟩
    · rintro ⟨k, _, rfl⟩
      exact ⟨k, rfl⟩
  rw [hEq]
  exact (Set.finite_Iio m).image _

/-- The forward orbit of a periodic point is invariant: `F '' O = O`. -/
theorem orbit_image {α : Type*} (F : α → α) (p : α) (hp : p ∈ Function.periodicPts F) :
    F '' (Set.range fun k : ℕ => F^[k] p) = Set.range fun k : ℕ => F^[k] p := by
  obtain ⟨m, hm, hpm⟩ := Function.mem_periodicPts.mp hp
  ext x
  constructor
  · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
    exact ⟨k + 1, Function.iterate_succ_apply' F k p⟩
  · rintro ⟨k, rfl⟩
    refine ⟨F^[k + m - 1] p, ⟨k + m - 1, rfl⟩, ?_⟩
    have h1 : k + m - 1 + 1 = k + m := by omega
    show F (F^[k + m - 1] p) = F^[k] p
    rw [← Function.iterate_succ_apply' F (k + m - 1) p, Nat.succ_eq_add_one, h1,
      Function.iterate_add_apply, hpm.eq]

/-- A periodic point is nonwandering. -/
theorem periodic_nonwandering {X : Type*} [TopologicalSpace X] (F : X → X) (q : X)
    (hq : q ∈ Function.periodicPts F) : q ∈ PughClosingLemma.nonwanderingSet F := by
  obtain ⟨m, hm, hqm⟩ := Function.mem_periodicPts.mp hq
  intro U hU
  have hqU : q ∈ U := mem_of_mem_nhds hU
  exact ⟨m, hm, q, ⟨q, hqU, hqm.eq⟩, hqU⟩

/-- The forward orbit of a periodic point lies in the nonwandering set. -/
theorem orbit_subset_nonwandering {X : Type*} [TopologicalSpace X] (F : X → X) (p : X)
    (hp : p ∈ Function.periodicPts F) :
    (Set.range fun k : ℕ => F^[k] p) ⊆ PughClosingLemma.nonwanderingSet F := by
  obtain ⟨m, hm, hpm⟩ := Function.mem_periodicPts.mp hp
  rintro x ⟨k, rfl⟩
  exact periodic_nonwandering F _ (Function.mem_periodicPts.mpr ⟨m, hm, hpm.apply_iterate k⟩)

end SC_B

theorem solution {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {r : ℕ} (f : Diff n M r) (hΩ : IsHyperbolicSet f (PughClosingLemma.nonwanderingSet f)) :
    ∀ p ∈ Function.periodicPts f, IsHyperbolicPeriodicPt f p := by
  intro p hp
  obtain ⟨_, _, g, Es, Eu, C, lam, hC, hlam0, hlam1, hx⟩ := hΩ
  exact ⟨hp, (SC_B.orbit_finite _ p hp).isCompact, SC_B.orbit_image _ p hp,
    g, Es, Eu, C, lam, hC, hlam0, hlam1,
    fun x hxO => hx x (SC_B.orbit_subset_nonwandering _ p hp hxO)⟩
