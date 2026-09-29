-- Prove2me | solution 1 for Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/618f0557-6a8a-5937-96f8-b3cdb58bbb2c

import Mathlib
import Theorems.Thm_exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one
import Theorems.Thm_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
import Theorems.Thm_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible
import Theorems.Thm_Rep_exists_isIrreducible_trace_eq_sum_of_card_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace ArtIndDETcore

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

lemma nontrivial_of_isIrreducible {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply le_antisymm bot_le
    intro v _
    rw [Subsingleton.elim v 0]
    exact (⊥ : Subrepresentation ρ).toSubmodule.zero_mem
  exact h.bot_ne_top this

lemma finrank_end_pos (T : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) T] (hT : T.ρ.IsIrreducible) :
    0 < Module.finrank (ZMod p) (T ⟶ T) := by
  haveI := nontrivial_of_isIrreducible T.ρ hT
  haveI : Module.Finite (ZMod p) (T ⟶ T) := Module.Finite.equiv (Representation.linHom.invariantsEquivRepHom T T)
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨𝟙 T, fun h0 => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : T)
  have : (𝟙 T : T ⟶ T).hom x = (0 : T ⟶ T).hom x := by rw [h0]
  exact hx (by simpa using this)

variable [Finite G]

lemma forall_dvd {r : ℕ} (S : Fin r → Rep.{0} (ZMod p) G) [∀ i, FiniteDimensional (ZMod p) (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (n : Fin r → ℤ)
    (h : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
        ∑ i, n i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0) :
    ∀ i, (p : ℤ) ∣ n i := by

  have hreg : ∀ g : G, (orderOf g).Coprime p →
      ∑ i, (n i : ZMod p) * LinearMap.trace (ZMod p) (S i) ((S i).ρ g) = 0 := by
    intro g hg
    let H : Subgroup G := Subgroup.zpowers g
    haveI : IsCyclic H := inferInstance
    have hcop : (Nat.card H).Coprime p := by rwa [Nat.card_zpowers]
    obtain ⟨s, T, hT, hTij, hdec⟩ := Rep.exists_isIrreducible_trace_eq_sum_of_card_coprime (H := H) hcop
    haveI : ∀ j, FiniteDimensional (ZMod p) (T j) := fun j => (hT j).1
    have hfd : ∀ i, FiniteDimensional (ZMod p) (Rep.res H.subtype (S i)) := fun i => ‹∀ i, FiniteDimensional (ZMod p) (S i)› i
    choose m hm htr using fun i => hdec (Rep.res H.subtype (S i)) (hfd i)

    have hsum : ∀ j, ∑ i, n i * (m i j : ℤ) = 0 := by
      intro j
      have hj := h H inferInstance hcop (T j) inferInstance
      have hej : (Module.finrank (ZMod p) (T j ⟶ T j) : ℤ) ≠ 0 := by exact_mod_cast (finrank_end_pos (T j) (hT j).2).ne'
      have : (∑ i, n i * (m i j : ℤ)) * (Module.finrank (ZMod p) (T j ⟶ T j) : ℤ) = 0 := by
        rw [Finset.sum_mul, ← hj]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm i j]; push_cast; ring
      exact (mul_eq_zero.1 this).resolve_right hej

    have hg' : ∀ i, LinearMap.trace (ZMod p) (S i) ((S i).ρ g) =
        ∑ j, (m i j : ZMod p) * LinearMap.trace (ZMod p) (T j) ((T j).ρ ⟨g, Subgroup.mem_zpowers g⟩) :=
      fun i => htr i ⟨g, Subgroup.mem_zpowers g⟩
    calc ∑ i, (n i : ZMod p) * LinearMap.trace (ZMod p) (S i) ((S i).ρ g)
        = ∑ j, (∑ i, (n i : ZMod p) * (m i j : ZMod p)) *
            LinearMap.trace (ZMod p) (T j) ((T j).ρ ⟨g, Subgroup.mem_zpowers g⟩) := by
          simp_rw [hg', Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          have : (∑ i, (n i : ZMod p) * (m i j : ZMod p)) = ((∑ i, n i * (m i j : ℤ) : ℤ) : ZMod p) := by
            push_cast; rfl
          rw [this, hsum j, Int.cast_zero, zero_mul]

  have hall : ∀ g : G, ∑ i, (n i : ZMod p) * LinearMap.trace (ZMod p) (S i) ((S i).ρ g) = 0 := by
    intro g
    obtain ⟨g', u, hgu, hcomm, hg', ⟨a, hu⟩, -, -⟩ :=
      exists_commute_mul_eq_orderOf_coprime_pow_prime_pow_eq_one p g
    rw [← hgu]
    have : ∀ i, LinearMap.trace (ZMod p) (S i) ((S i).ρ (g' * u)) = LinearMap.trace (ZMod p) (S i) ((S i).ρ g') :=
      fun i => Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one (S i).ρ g' u hcomm a hu
    simp_rw [this]
    exact hreg g' hg'

  have hc := Rep.forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible S hS hij (fun i => (n i : ZMod p)) hall
  intro i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n i) p).1 (hc i)

end ArtIndDETcore

open ArtIndDETcore in
theorem solution
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {r : ℕ} (S : Fin r → Rep.{0} (ZMod p) G) [∀ i, FiniteDimensional (ZMod p) (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (n : Fin r → ℤ)
    (h : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
        ∑ i, n i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0) :
    n = 0 := by

  suffices key : ∀ (N : ℕ) (n : Fin r → ℤ), ∑ i, (n i).natAbs = N →
      (∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
        ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
          ∑ i, n i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0) → n = 0 from
    key _ n rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n hN hn
    by_contra hne
    have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hdvd := forall_dvd S hS hij n hn
    choose n' hn' using hdvd
    have hn'hyp : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
        ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
          ∑ i, n' i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0 := by
      intro H hH hcop T hT
      have := hn H hH hcop T hT
      have e : ∑ i, n i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) =
          (p : ℤ) * ∑ i, n' i * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hn' i]; ring
      rw [e] at this
      exact (mul_eq_zero.1 this).resolve_left hp

    have hlt : ∑ i, (n' i).natAbs < N := by
      rw [← hN]
      have hle : ∀ i, (n' i).natAbs ≤ (n i).natAbs := fun i => by
        rw [hn' i, Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.le_mul_of_pos_left _ (Fact.out : p.Prime).pos
      obtain ⟨i0, hi0⟩ : ∃ i, n i ≠ 0 := not_forall.1 fun hall => hne (funext hall)
      have hi0' : n' i0 ≠ 0 := fun h0 => hi0 (by rw [hn' i0, h0, mul_zero])
      have hlt0 : (n' i0).natAbs < (n i0).natAbs := by
        rw [hn' i0, Int.natAbs_mul, Int.natAbs_natCast]
        have hpos : 0 < (n' i0).natAbs := Int.natAbs_pos.2 hi0'
        calc (n' i0).natAbs = 1 * (n' i0).natAbs := (one_mul _).symm
          _ < p * (n' i0).natAbs := Nat.mul_lt_mul_of_pos_right (Fact.out : p.Prime).one_lt hpos
      exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, Finset.mem_univ _, hlt0⟩
    have := ih _ hlt n' rfl hn'hyp
    apply hne
    funext i
    rw [hn' i, this]; simp

end S_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
end P2MW
export P2MW.S_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero (solution)
