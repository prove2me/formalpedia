-- Prove2me | solution 1 for SecretaryWD.DiscUpper.opt_first_class_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:58:30.437033+00:00
-- url     : https://prove2.me/submissions/e3bb6436-d07f-4199-bd6e-8c125d3a9cd3

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

set_option autoImplicit false

namespace C2e17c7b
open SecretaryWD.DiscUpper

lemma card_fiber (n : ℕ) (t e e' : Fin n) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e)).card =
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e')).card := by
  apply Finset.card_bij (fun π _ => Equiv.swap e e' * π)
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    simp [Equiv.Perm.mul_apply, hπ]
  · intro a _ b _ h
    exact mul_left_cancel h
  · intro b hb
    refine ⟨Equiv.swap e e' * b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp [Equiv.Perm.mul_apply, hb]
    · exact Equiv.swap_mul_self_mul e e' b

lemma card_fiber_mul (n : ℕ) (t e : Fin n) :
    (n : ℝ) * ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e)).card : ℝ)
      = (n.factorial : ℝ) := by
  have h1 : (Finset.univ : Finset (Equiv.Perm (Fin n))).card =
      ∑ e' ∈ (Finset.univ : Finset (Fin n)),
        (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e')).card :=
    Finset.card_eq_sum_card_fiberwise (fun π _ => Finset.mem_univ (π t))
  have h2 : ∑ e' ∈ (Finset.univ : Finset (Fin n)),
        (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e')).card
      = n * (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e)).card := by
    rw [Finset.sum_congr rfl (fun e' _ => card_fiber n t e' e)]
    simp
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  rw [h1, h2]
  push_cast
  ring

lemma exists_optTime {n : ℕ} (hn : 1 ≤ n) (d v : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ∃ t0, IsOptTime d v π t0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f : Fin n → ℝ := fun s => d s * v (π s) with hf
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  let S := Finset.univ.filter (fun t => ∀ s, f s ≤ f t)
  have hS : S.Nonempty := ⟨m, by simp [S]; exact fun s => hm s (Finset.mem_univ s)⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have := S.min'_mem hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  · intro s hs
    have hmem := S.min'_mem hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases lt_or_eq_of_le (hmem s) with h | h
    · exact h
    · exfalso
      have hsS : s ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        intro r; rw [h]; exact hmem r
      exact absurd (S.min'_le s hsS) (not_le.mpr hs)

end C2e17c7b

open C2e17c7b in
open SecretaryWD.DiscUpper in
theorem solution (n : ℕ) (hn : 1 ≤ n) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) :
    vmax v * dmax d / n ≤ optClass d v 1 := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ts, hts⟩ := exists_eq_ciSup_of_finite (f := d)
  obtain ⟨es, hes⟩ := exists_eq_ciSup_of_finite (f := v)
  have hdle : ∀ t, d t ≤ dmax d := fun t => le_ciSup (Finite.bddAbove_range d) t
  have hvle : ∀ e, v e ≤ vmax v := fun e => le_ciSup (Finite.bddAbove_range v) e
  have hdm : d ts = dmax d := hts
  have hvm : v es = vmax v := hes
  set g : Equiv.Perm (Fin n) → ℝ := fun π =>
    ∑ t ∈ discountClass d 1, if IsOptTime d v π t then d t * v (π t) else 0 with hg
  have gnn : ∀ π, 0 ≤ g π := by
    intro π
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact mul_nonneg (hd t) (hv _)
    · exact le_refl 0
  have gkey : ∀ π : Equiv.Perm (Fin n), π ts = es → dmax d * vmax v ≤ g π := by
    intro π hπ
    have hD0 : 0 ≤ dmax d := hdm ▸ hd ts
    have hV0 : 0 ≤ vmax v := hvm ▸ hv es
    rcases eq_or_lt_of_le (mul_nonneg hD0 hV0) with h0 | hpos
    · rw [← h0]; exact gnn π
    have hDp : 0 < dmax d := lt_of_le_of_ne hD0 (fun h => by rw [← h] at hpos; simp at hpos)
    have hVp : 0 < vmax v := lt_of_le_of_ne hV0 (fun h => by rw [← h] at hpos; simp at hpos)
    obtain ⟨t0, ht0⟩ := exists_optTime hn d v π
    have hbig : dmax d * vmax v ≤ d t0 * v (π t0) := by
      have := ht0.1 ts
      rw [hπ, hdm, hvm] at this
      exact this
    have hmem : t0 ∈ discountClass d 1 := by
      simp only [discountClass, Finset.mem_filter, Finset.mem_univ, true_and, pow_one]
      refine ⟨?_, by linarith [hdle t0]⟩
      by_contra hc
      push_neg at hc
      have h1 : d t0 * v (π t0) ≤ (dmax d / 2) * vmax v :=
        mul_le_mul hc (hvle _) (hv _) (by linarith)
      nlinarith
    have hsingle : (if IsOptTime d v π t0 then d t0 * v (π t0) else 0) ≤ g π := by
      apply Finset.single_le_sum (f := fun t => if IsOptTime d v π t then d t * v (π t) else 0)
        _ hmem
      intro t _
      split_ifs
      · exact mul_nonneg (hd t) (hv _)
      · exact le_refl 0
    rw [if_pos ht0] at hsingle
    linarith
  -- sum bound
  set F := Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π ts = es) with hF
  have hsum1 : ∑ π ∈ F, g π ≤ ∑ π, g π :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun π _ _ => gnn π)
  have hsum2 : (F.card : ℝ) * (dmax d * vmax v) ≤ ∑ π ∈ F, g π := by
    have := Finset.card_nsmul_le_sum F g (dmax d * vmax v) (fun π hπ => by
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      exact gkey π hπ)
    simpa [nsmul_eq_mul] using this
  have hcard := card_fiber_mul n ts es
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  show vmax v * dmax d / n ≤ uniformAvg g
  unfold uniformAvg
  rw [div_le_iff₀ hnpos]
  have hS : (F.card : ℝ) * (dmax d * vmax v) ≤ ∑ π, g π := le_trans hsum2 hsum1
  have : (n : ℝ) * (1 / (n.factorial : ℝ) * ∑ π, g π) =
      (n : ℝ) * (∑ π, g π) / (n.factorial : ℝ) := by field_simp
  rw [mul_comm _ (n : ℝ), this, le_div_iff₀ hfpos]
  rw [← hcard]
  nlinarith [mul_le_mul_of_nonneg_left hS (le_of_lt hnpos)]
