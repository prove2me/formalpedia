-- Prove2me | solution 1 for PhilipponMultiplicity.contact_order_condition_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:03:54.898117+00:00
-- url     : https://prove2.me/submissions/c7fb3434-d957-401e-8636-733278f92a1b

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false

open PhilipponMultiplicity in
theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (T : ℕ) (D : G.FactorIndex → ℕ)
    (s : ℕ)
    (R : Submodule K G.CoordinateRing)
    (hR : ∀ P : G.CoordinateRing, P ∈ R → IsMultihomogeneousOfDegree G P D)
    (sample : Finset G.Point)
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ sample.card * Nat.choose (T + s) s)
    (E : R →ₗ[K] (ι → K))
    (hE : ∀ P : R, E P = 0 →
      ∀ g ∈ sample, ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A (P : G.CoordinateRing) g) :
    Module.finrank K (LinearMap.range E) ≤ sample.card * Nat.choose (T + s) s := by
  have h1 : Module.finrank K (LinearMap.range E) ≤ Module.finrank K (ι → K) :=
    Submodule.finrank_le _
  rw [Module.finrank_fintype_fun_eq_card] at h1
  exact h1.trans hι
