-- Prove2me | solution 1 for Plasticity.SetTheory.exists_bijective_of_rank_assignment
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:12.101667+00:00
-- url     : https://prove2.me/submissions/4d2696ee-79f1-4ae3-9f24-8f9dddde049e

import Mathlib.SetTheory.Cardinal.Basic

universe u v

namespace Sol_Plasticity_SetTheory_exists_bijective_of_rank_assignment
end Sol_Plasticity_SetTheory_exists_bijective_of_rank_assignment

theorem solution {P : Type v} {T K : Type u} [Nonempty T]
    (Φ : (ℕ × K → T) → P → T) (r : P → ℕ) (ρ : T → ℕ)
    (hdep : ∀ y y' p, (∀ m k, m < r p → y (m, k) = y' (m, k)) → Φ y p = Φ y' p)
    (hrank : ∀ y p, ρ (Φ y p) = r p)
    (hinj : ∀ y, Function.Injective (Φ y))
    (hcard : ∀ y n, Cardinal.mk ↥({t | ρ t = n} \ Φ y '' {p | r p = n}) = Cardinal.mk K) :
    ∃ y : ℕ × K → T, Function.Bijective (Sum.elim (Φ y) y) := by
  classical
  obtain ⟨t0⟩ := ‹Nonempty T›
  have e : ∀ y n, K ≃ ↥({t | ρ t = n} \ Φ y '' {p | r p = n}) :=
    fun y n => (Cardinal.eq.1 (hcard y n)).some.symm
  let z : ℕ → K → T := Nat.strongRec (motive := fun _ => K → T)
    (fun n ih k => (e (fun q => if h : q.1 < n then ih q.1 h q.2 else t0) n k).1)
  have hz : ∀ n k, z n k = (e (fun q => if h : q.1 < n then z q.1 q.2 else t0) n k).1 := by
    intro n k
    simp only [z]
    rw [Nat.strongRec_eq]
  set ys : ℕ → ℕ × K → T := fun n q => if h : q.1 < n then z q.1 q.2 else t0 with hys
  set y : ℕ × K → T := fun q => z q.1 q.2 with hy
  have hag : ∀ p, Φ y p = Φ (ys (r p)) p := by
    intro p
    apply hdep
    intro m k hm
    simp [hys, hy, hm]
  have hmem : ∀ n k, ρ (z n k) = n ∧ z n k ∉ Φ (ys n) '' {p | r p = n} := by
    intro n k
    have := (e (ys n) n k).2
    rw [hz n k]
    exact this
  have hnot : ∀ n k p, r p = n → Φ y p ≠ z n k := by
    intro n k p hp h
    apply (hmem n k).2
    refine ⟨p, hp, ?_⟩
    rw [← h, hag p, hp]
  refine ⟨y, ?_, ?_⟩
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (hinj y hab)
    · exact (hnot b.1 b.2 a (by have := congrArg ρ hab; simp [hy, hrank, (hmem b.1 b.2).1] at this; exact this) hab).elim
    · exact (hnot a.1 a.2 b (by have := congrArg ρ hab; simp [hy, hrank, (hmem a.1 a.2).1] at this; exact this.symm) hab.symm).elim
    · simp only [Sum.elim_inr, hy] at hab
      have h1 : a.1 = b.1 := by
        have := congrArg ρ hab
        rwa [(hmem a.1 a.2).1, (hmem b.1 b.2).1] at this
      obtain ⟨n, k⟩ := a
      obtain ⟨n', k'⟩ := b
      simp only at h1
      subst h1
      have := (e (ys n) n).injective (Subtype.ext ((hz n k).symm.trans (hab.trans (hz n k'))))
      rw [this]
  · intro t
    by_cases h : t ∈ Φ (ys (ρ t)) '' {p | r p = ρ t}
    · obtain ⟨p, hp, hpt⟩ := h
      exact ⟨Sum.inl p, by simp only [Sum.elim_inl]; rw [hag, hp]; exact hpt⟩
    · obtain ⟨k, hk⟩ := (e (ys (ρ t)) (ρ t)).surjective ⟨t, rfl, h⟩
      refine ⟨Sum.inr (ρ t, k), ?_⟩
      simp only [Sum.elim_inr, hy]
      rw [hz, hk]
