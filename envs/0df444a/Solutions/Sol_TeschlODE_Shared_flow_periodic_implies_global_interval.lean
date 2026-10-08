-- Prove2me | solution 1 for TeschlODE.Shared.flow_periodic_implies_global_interval
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:32:08.01139+00:00
-- url     : https://prove2.me/submissions/7db5c8ac-73e7-4f17-8d9f-a314b4c5712f

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

set_option autoImplicit false

namespace P86e07d27

open TeschlODE.Shared

lemma shift_down {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (S : ℝ)
    (hSI : S ∈ I x) (hper : Φ S x = x) :
    ∀ s : ℝ, s + S ∈ I x → s ∈ I x := by
  obtain ⟨⟨hopen, hord, hmem, hder⟩, _h0, _hΦ0, huniq⟩ := hΦ x hx
  have key := huniq ((fun s => s + S) ⁻¹' I x) (fun s => Φ (s + S) x) ?_ ?_ ?_
  · intro s hs
    exact key.1 hs
  · refine ⟨hopen.preimage (continuous_id.add continuous_const), ?_, ?_, ?_⟩
    · refine ⟨fun a ha b hb c hc => ?_⟩
      have := hord.out ha hb
      exact this ⟨by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.1],
        by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.2]⟩
    · intro t ht
      exact hmem _ ht
    · intro t ht
      have h := hder _ ht
      exact h.comp_add_const t S
  · simpa using hSI
  · simpa using hper

end P86e07d27

open TeschlODE.Shared in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (T : ℝ)
    (hT0 : 0 < T) (hTI : T ∈ I x) (hper : Φ T x = x) :
    I x = Set.univ := by
  obtain ⟨⟨_hopen, hord, _hmem, _hder⟩, h0, hΦ0, huniq⟩ := hΦ x hx
  have down := P86e07d27.shift_down f M I Φ hΦ x hx T hTI hper
  have hmT : -T ∈ I x := down (-T) (by simpa using h0)
  have hmTper : Φ (-T) x = x := by
    have := (huniq ((fun s => s + T) ⁻¹' I x) (fun s => Φ (s + T) x) ?_ ?_ ?_).2 (-T) ?_
    · simpa [hΦ0] using this.symm
    · obtain ⟨⟨hopen, hord, hmem, hder⟩, _, _, _⟩ := hΦ x hx
      refine ⟨hopen.preimage (continuous_id.add continuous_const), ?_, ?_, ?_⟩
      · refine ⟨fun a ha b hb c hc => ?_⟩
        have := hord.out ha hb
        exact this ⟨by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.1],
          by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.2]⟩
      · intro t ht
        exact hmem _ ht
      · intro t ht
        exact (hder _ ht).comp_add_const t T
    · simpa using hTI
    · simpa using hper
    · simpa using h0
  have up := P86e07d27.shift_down f M I Φ hΦ x hx (-T) hmT hmTper
  have hk : ∀ k : ℕ, (k : ℝ) * T ∈ I x ∧ -((k : ℝ) * T) ∈ I x := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      refine ⟨up _ ?_, down _ ?_⟩
      · have : ((k + 1 : ℕ) : ℝ) * T + -T = (k : ℝ) * T := by push_cast; ring
        rw [this]; exact ih.1
      · have : -(((k + 1 : ℕ) : ℝ) * T) + T = -((k : ℝ) * T) := by push_cast; ring
        rw [this]; exact ih.2
  ext y
  simp only [Set.mem_univ, iff_true]
  obtain ⟨k, hk'⟩ := Archimedean.arch |y| hT0
  have hy := hk k
  rw [nsmul_eq_mul] at hk'
  exact hord.out hy.2 hy.1 ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
