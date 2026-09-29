-- Prove2me | solution 1 for ResidualGaloisRep.exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/63f5064d-f9e3-5f6a-8b61-73d009d619c7

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped TensorProduct

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (χ : primeLocalGaloisGroup (pPrime p) →* Multiplicative (ZMod ℓ)) (hχ : Function.Surjective χ) :
    ∃ (a : primeLocalGaloisGroup (pPrime p) → k)
      (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))),
      (∀ σ, (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ =
          a σ • (1 : Module.End k ρbar.V)) ∧
      (∃ σ, a σ ≠ 0) ∧ (∀ σ τ, a (σ * τ) = a σ + a τ) ∧
      ∃ π : (ZMod ℓ → ρbar.V) →+ ρbar.V × ρbar.V, Function.Surjective π ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (F : ZMod ℓ → ρbar.V),
          π (fun i => ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (F (i - Multiplicative.toAdd (χ σ)))) =
            ρbar.dualLiftModuleActAd p c σ (π F) := by
  classical

  let ι : ZMod ℓ →+* k := ZMod.castHom (dvd_refl ℓ) k
  let a : primeLocalGaloisGroup (pPrime p) → k := fun σ => ι (Multiplicative.toAdd (χ σ))
  have ha_mul : ∀ σ τ, a (σ * τ) = a σ + a τ := by
    intro σ τ
    simp only [a, map_mul, toAdd_mul, map_add]

  let A := Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)
  have hfix : ∀ (g : primeLocalGaloisGroup (pPrime p)) (t : k),
      A.ρ g (t • (1 : Module.End k ρbar.V)) = t • (1 : Module.End k ρbar.V) := by
    intro g t
    rw [map_smul]
    congr 1
    change ρbar.adRep (primeLocalToGlobal (pPrime p) g) (1 : Module.End k ρbar.V) = 1
    rw [ResidualGaloisRep.adRep_apply, mul_one, ← map_mul, mul_inv_cancel, map_one]

  let cf : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V := fun σ => a σ • 1
  have hcf : cf ∈ cocycles₁ A := by
    rw [mem_cocycles₁_iff]
    intro g h
    change a (g * h) • (1 : Module.End k ρbar.V) = A.ρ g (a h • (1 : Module.End k ρbar.V)) + a g • 1
    rw [hfix, ha_mul, add_smul, add_comm]
  let c : cocycles₁ A := ⟨cf, hcf⟩
  have hcσ : ∀ σ, (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ = a σ • 1 :=
    fun σ => rfl

  have ha_ne : ∃ σ, a σ ≠ 0 := by
    obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd 1)
    refine ⟨σ, ?_⟩
    simp only [a, hσ, toAdd_ofAdd, map_one]
    exact one_ne_zero

  let π : (ZMod ℓ → ρbar.V) →+ ρbar.V × ρbar.V :=
    { toFun := fun F => (∑ i, F i, ∑ i, ι i • F i)
      map_zero' := by simp
      map_add' := fun F F' => by
        simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, Prod.mk_add_mk] }
  have hπ_apply : ∀ F, π F = (∑ i, F i, ∑ i, ι i • F i) := fun F => rfl

  have hsum_single : ∀ (j : ZMod ℓ) (x : ρbar.V), ∑ i, (Pi.single j x : ZMod ℓ → ρbar.V) i = x := by
    intro j x
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp
  have hsum_single' : ∀ (j : ZMod ℓ) (x : ρbar.V),
      ∑ i, ι i • (Pi.single j x : ZMod ℓ → ρbar.V) i = ι j • x := by
    intro j x
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp
  have hπ_surj : Function.Surjective π := by
    rintro ⟨v, w⟩
    refine ⟨Pi.single 0 (v - w) + Pi.single 1 w, ?_⟩
    rw [map_add, hπ_apply, hπ_apply, hsum_single, hsum_single, hsum_single', hsum_single',
      Prod.mk_add_mk, map_zero, map_one, zero_smul, one_smul, zero_add, sub_add_cancel]
  refine ⟨a, c, hcσ, ha_ne, ha_mul, π, hπ_surj, ?_⟩
  intro σ F
  set s : ZMod ℓ := Multiplicative.toAdd (χ σ) with hs
  set R : Module.End k ρbar.V := ρbar.ρ (primeLocalToGlobal (pPrime p) σ) with hR

  have h1 : ∑ i, R (F (i - s)) = R (∑ i, F i) := by
    rw [map_sum]
    exact Equiv.sum_comp (Equiv.subRight s) (fun i => R (F i))
  have h2 : ∑ i, ι i • R (F (i - s)) = R (∑ i, ι i • F i) + a σ • R (∑ i, F i) := by
    have : ∑ i, ι i • R (F (i - s)) = ∑ j, ι (j + s) • R (F j) := by
      rw [← Equiv.sum_comp (Equiv.addRight s) (fun i => ι i • R (F (i - s)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Equiv.coe_addRight, add_sub_cancel_right]
    rw [this]
    simp only [map_add, add_smul, Finset.sum_add_distrib, map_sum, map_smul, Finset.smul_sum]
    rfl
  rw [hπ_apply, hπ_apply, h1, h2]

  change _ = (R (∑ i, F i), ((c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ) (R (∑ i, F i))
      + R (∑ i, ι i • F i))
  rw [hcσ, LinearMap.smul_apply, Module.End.one_apply, add_comm (a σ • _)]

end S_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
end P2MW
export P2MW.S_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd (solution)
