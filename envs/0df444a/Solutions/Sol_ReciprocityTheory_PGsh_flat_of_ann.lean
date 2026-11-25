-- Prove2me | solution 1 for ReciprocityTheory.PGsh.flat_of_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:45:31.960364+00:00
-- url     : https://prove2.me/submissions/ce9bb721-7abd-4d62-bdb3-be70f93aeb63

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_ZmodTrichotomy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open WittVector Ideal TensorProduct
namespace ReciprocityTheory.PGsh
section Principal
variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
private lemma principal_inj (g : S)
    (h : ∀ m : M, g • m = 0 → (⟨g, mem_span_singleton_self g⟩ : span {g}) ⊗ₜ[S] m = 0) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul S M).comp (span {g}).subtype)) := by
  rw [injective_iff_map_eq_zero]
  have ex : ∀ t : span {g} ⊗[S] M,
      ∃ m : M, t = (⟨g, mem_span_singleton_self g⟩ : span {g}) ⊗ₜ[S] m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (tmul_zero _ _).symm⟩
    | tmul i m =>
      obtain ⟨i, hi⟩ := i
      obtain ⟨r, rfl⟩ := mem_span_singleton'.1 hi
      refine ⟨r • m, ?_⟩
      rw [← smul_tmul]
      congr 1
    | add x y hx hy =>
      obtain ⟨m₁, rfl⟩ := hx
      obtain ⟨m₂, rfl⟩ := hy
      exact ⟨m₁ + m₂, (tmul_add _ _ _).symm⟩
  intro t ht
  obtain ⟨m, rfl⟩ := ex t
  rw [lift.tmul] at ht
  exact h m ht
end Principal
section ZModSq
variable (p : ℕ) [hp : Fact p.Prime]
private lemma p_sq_zero : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]
private lemma zmod_trichotomy (g : ZMod (p ^ 2)) :
    IsUnit g ∨ (∃ u : ZMod (p ^ 2), IsUnit u ∧ g = (p : ZMod (p ^ 2)) * u) ∨ g = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hg : g = ((g.val : ℕ) : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val g).symm
  have unit_of : ∀ k : ℕ, ¬ p ∣ k → IsUnit ((k : ℕ) : ZMod (p ^ 2)) := by
    intro k hk
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk))
  by_cases h1 : p ∣ g.val
  · obtain ⟨k, hk⟩ := h1
    by_cases h2 : p ∣ k
    · right; right
      obtain ⟨l, hl⟩ := h2
      rw [hg, hk, hl, Nat.cast_mul, Nat.cast_mul, ← mul_assoc, ← sq, p_sq_zero, zero_mul]
    · right; left
      exact ⟨k, unit_of k h2, by rw [hg, hk, Nat.cast_mul]⟩
  · left
    rw [hg]; exact unit_of _ h1
private lemma zmod_ideal (J : Ideal (ZMod (p ^ 2))) :
    J = span {0} ∨ J = span {(p : ZMod (p ^ 2))} ∨ J = span {1} := by
  by_cases hu : ∃ g ∈ J, IsUnit g
  · right; right
    obtain ⟨g, hgJ, hg⟩ := hu
    rw [span_singleton_one]
    exact eq_top_of_isUnit_mem J hgJ hg
  · by_cases hz : ∀ g ∈ J, g = 0
    · left
      rw [span_singleton_eq_bot.2 rfl]
      exact eq_bot_iff.2 (fun g hg => (mem_bot).2 (hz g hg))
    · right; left
      push Not at hz
      obtain ⟨g, hgJ, hg0⟩ := hz
      apply le_antisymm
      · intro x hx
        rcases zmod_trichotomy p x with h | ⟨u, _, rfl⟩ | rfl
        · exact absurd ⟨x, hx, h⟩ hu
        · exact mem_span_singleton'.2 ⟨u, mul_comm _ _⟩
        · exact zero_mem _
      · rw [span_singleton_le_iff_mem]
        rcases zmod_trichotomy p g with h | ⟨u, hu', rfl⟩ | rfl
        · exact absurd ⟨g, hgJ, h⟩ hu
        · have : (p : ZMod (p ^ 2)) = p * u * ↑hu'.unit⁻¹ := by
            rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
          rw [this]
          exact J.mul_mem_right _ hgJ
        · exact absurd rfl hg0
end ZModSq
section Main
variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Main
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable (p : ℕ) [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ 2)) M]
    (h : ∀ m : M, (p : ZMod (p ^ 2)) • m = 0 → ∃ y : M, m = (p : ZMod (p ^ 2)) • y) :
    Module.Flat (ZMod (p ^ 2)) M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro J _
  rcases zmod_ideal p J with rfl | rfl | rfl
  · apply principal_inj
    intro m _
    have : (⟨0, mem_span_singleton_self 0⟩ : span {(0 : ZMod (p ^ 2))}) = 0 := rfl
    rw [this, zero_tmul]
  · apply principal_inj
    intro m hm
    obtain ⟨y, rfl⟩ := h m hm
    rw [← smul_tmul]
    have : (p : ZMod (p ^ 2)) • (⟨p, mem_span_singleton_self _⟩ : span {(p : ZMod (p ^ 2))}) = 0 := by
      apply Subtype.ext
      show (p : ZMod (p ^ 2)) * p = 0
      rw [← sq, p_sq_zero]
    rw [this, zero_tmul]
  · apply principal_inj
    intro m hm
    rw [one_smul] at hm
    rw [hm, tmul_zero]
end ReciprocityTheory.PGsh
