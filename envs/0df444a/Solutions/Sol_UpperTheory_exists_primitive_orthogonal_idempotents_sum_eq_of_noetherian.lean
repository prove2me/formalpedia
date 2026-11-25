-- Prove2me | solution 1 for UpperTheory.exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:47.454047+00:00
-- url     : https://prove2.me/submissions/69cfb969-8335-417c-8abb-e866aa2573dd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem idem_lt {R : Type} [CommRing R] {e x : R} (he : e * e = e)
    (hxe : x * e = x) (hne : x ≠ e) :
    Ideal.span ({1 - e} : Set R) < Ideal.span ({1 - x} : Set R) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨1 - e, by linear_combination (-1 : R) * hxe⟩
  · intro h
    have h1 : (1 - x) ∈ Ideal.span ({1 - e} : Set R) := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    apply hne
    linear_combination e * hc + c * he - hxe
private theorem idem_absorb {R : Type} [CommRing R] {s : ℕ} (g : Fin s → R)
    (h1 : ∀ i, g i * g i = g i) (h2 : ∀ i j, i ≠ j → g i * g j = 0) (i : Fin s) :
    g i * ∑ j, g j = g i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact h1 i
  · intro j _ hj
    exact h2 i j (Ne.symm hj)
  · intro h
    exact absurd (Finset.mem_univ i) h
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (e : R), e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e := by
  intro R _ _
  suffices H : ∀ I : Ideal R, ∀ e : R, Ideal.span ({1 - e} : Set R) = I → e * e = e →
      ∃ (s : ℕ) (g : Fin s → R), (∀ i, g i * g i = g i ∧ g i ≠ 0 ∧ ∀ x, x * x = x → x * g i = x → x = 0 ∨ x = g i) ∧
        (∀ i j, i ≠ j → g i * g j = 0) ∧ ∑ i, g i = e from fun e he => H _ e rfl he
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
  intro e hI he
  subst hI
  by_cases h0 : e = 0
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp [h0]⟩
  by_cases hp : ∀ x : R, x * x = x → x * e = x → x = 0 ∨ x = e
  · refine ⟨1, fun _ => e, fun _ => ⟨he, h0, hp⟩, ?_, by simp⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  push Not at hp
  obtain ⟨x, hx, hxe, hx0, hxne⟩ := hp
  have hy : (e - x) * (e - x) = e - x := by linear_combination he + hx - 2 * hxe
  have hye : (e - x) * e = e - x := by linear_combination he - hxe
  have hyne : e - x ≠ e := fun h => hx0 (by linear_combination -h)
  have hxy : x * (e - x) = 0 := by linear_combination hxe - hx
  obtain ⟨s, g, hg1, hg2, hg3⟩ := ih _ (idem_lt he hxe hxne) x rfl hx
  obtain ⟨t, k, hk1, hk2, hk3⟩ := ih _ (idem_lt he hye hyne) (e - x) rfl hy
  have hcross : ∀ i j, g i * k j = 0 := by
    intro i j
    have a := idem_absorb g (fun i => (hg1 i).1) hg2 i
    have b := idem_absorb k (fun i => (hk1 i).1) hk2 j
    rw [hg3] at a
    rw [hk3] at b
    calc g i * k j = (g i * x) * (k j * (e - x)) := by rw [a, b]
      _ = g i * k j * (x * (e - x)) := by ring
      _ = 0 := by rw [hxy, mul_zero]
  refine ⟨s + t, Fin.append g k, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [Fin.append_left] using hg1 i
    | right i => simpa only [Fin.append_right] using hk1 i
  · intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        exact hg2 i j (fun h => hij (by rw [h]))
      | right j =>
        simp only [Fin.append_left, Fin.append_right]
        exact hcross i j
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.append_left, Fin.append_right]
        rw [mul_comm]; exact hcross j i
      | right j =>
        simp only [Fin.append_right]
        exact hk2 i j (fun h => hij (by rw [h]))
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hg3, hk3]; ring
end UpperTheory
