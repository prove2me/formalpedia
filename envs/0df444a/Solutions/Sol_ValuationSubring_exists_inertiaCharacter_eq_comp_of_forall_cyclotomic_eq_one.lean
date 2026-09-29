-- Prove2me | solution 1 for ValuationSubring.exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4b6918e4-bdd8-5608-92a6-e783ea643919

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_Deformations_TameDescent
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Theorems.Thm_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one

set_option autoImplicit false

open IsLocalRing

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] {q : ℕ} (hq : q.Prime) {p : ℕ} (hp : p.Prime)
    (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {k : ℕ} (hk : ¬ p ^ (k + 1) ∣ q - 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hone : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (ξ σ : R) - 1 ∈ IsLocalRing.maximalIdeal R)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    (hker : ∀ σ ∈ P.inertiaSubgroupIn ℚ, cyc σ = 1 → ξ σ = 1)
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k))) (hπΔ : Function.Surjective πΔ) :
    ∃ χ : Multiplicative (ZMod (p ^ k)) →* Rˣ, ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ = χ (πΔ (cyc σ)) := by
  classical
  set I := P.inertiaSubgroupIn ℚ with hI

  have hsurjI : ∀ u : (ZMod q)ˣ, ∃ σ ∈ I, cyc σ = u := by
    intro u
    obtain ⟨σ, hσ, hσμ⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow P hq hP u
    haveI : NeZero (q : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    haveI : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) q
    refine ⟨σ, hσ, Units.ext (ZMod.val_injective q ?_)⟩
    have h1 := hcyc σ ζ hζ.pow_eq_one
    have h2 := hσμ ζ hζ.pow_eq_one
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2)

  have hξ1 : ξ 1 = 1 := hker 1 (Subgroup.one_mem _) (map_one cyc)
  have hξinv : ∀ σ ∈ I, ξ σ⁻¹ = (ξ σ)⁻¹ := by
    intro σ hσ
    have h := hmul σ⁻¹ (Subgroup.inv_mem _ hσ) σ hσ
    rw [inv_mul_cancel, hξ1] at h
    exact (eq_inv_of_mul_eq_one_left h.symm)

  have hwd : ∀ σ ∈ I, ∀ τ ∈ I, cyc σ = cyc τ → ξ σ = ξ τ := by
    intro σ hσ τ hτ hc
    have hmem : σ * τ⁻¹ ∈ I := Subgroup.mul_mem _ hσ (Subgroup.inv_mem _ hτ)
    have hc1 : cyc (σ * τ⁻¹) = 1 := by rw [map_mul, map_inv, hc, mul_inv_cancel]
    have h := hmul (σ * τ⁻¹) hmem τ hτ
    rw [inv_mul_cancel_right, hker _ hmem hc1, one_mul] at h
    exact h

  let s : (ZMod q)ˣ → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := fun u => (hsurjI u).choose
  have hs : ∀ u, s u ∈ I ∧ cyc (s u) = u := fun u => (hsurjI u).choose_spec
  let ξ' : (ZMod q)ˣ →* Rˣ :=
    { toFun := fun u => ξ (s u)
      map_one' := hker _ (hs 1).1 (hs 1).2
      map_mul' := fun u v => by
        have hmem : s u * s v ∈ I := Subgroup.mul_mem _ (hs u).1 (hs v).1
        rw [← hmul _ (hs u).1 _ (hs v).1]
        exact hwd _ (hs (u * v)).1 _ hmem (by rw [(hs (u * v)).2, map_mul, (hs u).2, (hs v).2]) }
  have hξ'I : ∀ σ ∈ I, ξ σ = ξ' (cyc σ) := fun σ hσ =>
    hwd σ hσ _ (hs (cyc σ)).1 (hs (cyc σ)).2.symm

  haveI : Fact q.Prime := ⟨hq⟩
  have hcardG : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
  have hcardΔ : Nat.card (Multiplicative (ZMod (p ^ k))) = p ^ k := by
    haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hidx : πΔ.ker.index = p ^ k := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπΔ, Subgroup.card_top, hcardΔ]
  have hker_card : Nat.card πΔ.ker * p ^ k = q - 1 := by
    have h := Subgroup.card_mul_index πΔ.ker
    rw [hidx, hcardG] at h
    exact h
  have hcop : (Nat.card πΔ.ker).Coprime p := by
    rw [Nat.Coprime, Nat.gcd_comm]
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    rintro ⟨m, hm⟩
    apply hk
    refine ⟨m, ?_⟩
    rw [← hker_card, hm]; ring
  have hone' : ∀ u, (ξ' u : R) - 1 ∈ maximalIdeal R := fun u => hone _ (hs u).1
  obtain ⟨χ, hχ⟩ := MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker
    πΔ hπΔ hpR hcop ξ' hone'
  exact ⟨χ, fun σ hσ => by rw [hξ'I σ hσ, hχ]⟩

end S_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one
end P2MW
export P2MW.S_ValuationSubring_exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one (solution)
