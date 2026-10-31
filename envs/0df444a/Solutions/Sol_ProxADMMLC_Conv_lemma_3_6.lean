-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T10:53:06.701409+00:00
-- url     : https://prove2.me/submissions/b10dab20-79bd-43e1-9b07-33873c9d6042

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

set_option autoImplicit false

namespace L36Aux

theorem coord {xi gi li ui c : ℝ} (hc : 0 < c) (hlu : li < ui)
    (h : xi = if xi - c * gi < li then li else if xi - c * gi ≤ ui then xi - c * gi else ui) :
    (li ≤ xi ∧ xi ≤ ui) ∧ max gi 0 * (li - xi) = 0 ∧ max (-gi) 0 * (xi - ui) = 0 := by
  split_ifs at h with h1 h2
  · have h3 : 0 < c * gi := by linarith
    have hg : 0 < gi := pos_of_mul_pos_right h3 hc.le
    refine ⟨⟨by linarith, by linarith⟩, by rw [h]; ring, ?_⟩
    rw [max_eq_right (by linarith)]; ring
  · have h3 : c * gi = 0 := by linarith
    have hg : gi = 0 := (mul_eq_zero.mp h3).resolve_left hc.ne'
    subst hg
    refine ⟨⟨by linarith, by linarith⟩, by simp, by simp⟩
  · have h3 : c * gi < 0 := by linarith
    have hg : gi < 0 := neg_of_mul_neg_right h3 hc.le
    refine ⟨⟨by linarith, by linarith⟩, ?_, by rw [h]; ring⟩
    rw [max_eq_right hg.le]; ring

end L36Aux

open ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (Γ p c α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    ∀ (x z : E n) (y : E m), yPlus A b α x y = y → xPlus f A b ℓ u Γ p c α x z y = x →
      zPlus f A b ℓ u Γ p c α β x z y = z → (x, y) ∈ Wset f A b ℓ u := by
  intro x z y hy hx hz
  have hAx : A x = b := by
    have h : α • (A x - b) = 0 := by
      unfold yPlus at hy
      simpa using hy
    rcases smul_eq_zero.mp h with h | h
    · exact absurd h hα.ne'
    · exact sub_eq_zero.mp h
  have hxz : x = z := by
    have h : β • (x - z) = 0 := by
      unfold zPlus at hz
      rw [hx] at hz
      simpa using hz
    rcases smul_eq_zero.mp h with h | h
    · exact absurd h hβ.ne'
    · exact sub_eq_zero.mp h
  subst hxz
  unfold xPlus at hx
  rw [hy] at hx
  have hG : gradK f A b Γ p x x y
      = gradient f x + (ContinuousLinearMap.adjoint A) y := by
    unfold gradK
    simp [hAx]
  rw [hG] at hx
  set g := gradient f x + (ContinuousLinearMap.adjoint A) y with hg
  have hcoord : ∀ i, x i = (if x i - c * g i < ℓ i then ℓ i
      else if x i - c * g i ≤ u i then x i - c * g i else u i) := by
    intro i
    have h := congrArg (fun v : E n => v i) hx
    simp only [boxProj, PiLp.toLp_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hk := fun i => L36Aux.coord hc (hℓu i) (hcoord i)
  refine ⟨WithLp.toLp 2 (fun i => max (g i) 0), WithLp.toLp 2 (fun i => max (-g i) 0),
    ?_, hAx, fun i => (hk i).1, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply]
    have := max_zero_sub_max_neg_zero_eq_self (g i)
    have hgi : g i = (gradient f x) i + ((ContinuousLinearMap.adjoint A) y) i := by
      rw [hg]; rfl
    linarith
  · exact le_max_right _ _
  · exact le_max_right _ _
  · exact (hk i).2.1
  · exact (hk i).2.2
