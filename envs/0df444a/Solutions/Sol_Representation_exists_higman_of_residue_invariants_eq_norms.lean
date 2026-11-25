-- Prove2me | solution 1 for Representation.exists_higman_of_residue_invariants_eq_norms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:33:18.367883+00:00
-- url     : https://prove2.me/submissions/cc2faac1-29ac-4154-af2c-365f16285ce0

import Mathlib
import Definitions.Def_RPLib_F2_025

set_option autoImplicit false

open TensorProduct

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    {G : Type} [Group G] [Fintype G]
    {P : Type} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    (ρ : Representation R G P) (S : Subgroup G) [Fintype S] (hS : IsPGroup p S)
    (hindex : ¬ p ∣ S.index)
    (hN : ∀ x : IsLocalRing.ResidueField R ⊗[R] P,
      (∀ s : S, (ρ s).baseChange (IsLocalRing.ResidueField R) x = x) →
        ∃ y : IsLocalRing.ResidueField R ⊗[R] P,
          x = ∑ s : S, (ρ s).baseChange (IsLocalRing.ResidueField R) y) :
    ∃ E : P →ₗ[R] P, ∑ g : G, ρ g ∘ₗ E ∘ₗ ρ g⁻¹ = LinearMap.id := by
  exact RamanujanPetersson.HattoriStallings.isProj_of_sylow (ρ := ρ) p S hS hindex hN
