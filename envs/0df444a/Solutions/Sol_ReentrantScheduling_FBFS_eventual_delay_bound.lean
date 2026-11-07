-- Prove2me | solution 1 for ReentrantScheduling.FBFS.eventual_delay_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:18:46.833524+00:00
-- url     : https://prove2.me/submissions/fc095603-5c1b-4507-a4dc-aa22f7be5afa

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants
import Theorems.Thm_ReentrantScheduling_FBFS_buffer_delay_bound

open ReentrantScheduling.FBFS Finset

theorem solution
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    ∃ T : ℝ, ∀ p : R.Part, ¬ R.initial p → T < R.α p →
      R.exit p ≤ ((R.α p + ∑ j : Fin L.l, (L.Gamma lam γ j + L.τ j) : ℝ) : WithTop ℝ) := by
  obtain ⟨T, hT⟩ := buffer_delay_bound L lam γ hlam hγ hload R hR harr
  refine ⟨∑ j : Fin L.l, |T j|, fun p hp hαp => ?_⟩
  have hTj : ∀ j : Fin L.l, T j < R.α p := fun j =>
    lt_of_le_of_lt (le_trans (le_abs_self _)
      (single_le_sum (f := fun j => |T j|) (fun _ _ => abs_nonneg _) (mem_univ j))) hαp
  have hentry : R.entry p = ⟨0, L.l_pos⟩ := R.entry_released p hp
  set D : Fin L.l → ℝ := fun j => L.Gamma lam γ j + L.τ j with hD
  -- induction along the route
  have main : ∀ k : ℕ, ∀ hk : k < L.l, ∃ a s : ℝ, R.arrive p ⟨k, hk⟩ = (a : WithTop ℝ) ∧
      R.start p ⟨k, hk⟩ = (s : WithTop ℝ) ∧ R.α p ≤ a ∧ a ≤ s ∧
      s + L.τ ⟨k, hk⟩ ≤ R.α p + ∑ j ∈ univ.filter (fun j : Fin L.l => j.val ≤ k), D j := by
    intro k
    induction k with
    | zero =>
      intro hk
      have ha : R.arrive p ⟨0, hk⟩ = ((R.α p : ℝ) : WithTop ℝ) := by
        unfold Run.arrive; rw [if_pos (by rw [hentry])]
      have hle : R.entry p ≤ ⟨0, hk⟩ := by rw [hentry]
      have hb := hT ⟨0, hk⟩ p hle (by rw [ha]; exact_mod_cast hTj _)
      rw [ha] at hb
      have hprec := hR.precedence p ⟨0, hk⟩ hle
      rcases hprec with hprec | hprec
      swap; · exact absurd hprec.1 hp
      rw [ha] at hprec
      cases hs : R.start p ⟨0, hk⟩ with
      | top => rw [hs] at hb; simp at hb
      | coe s =>
        rw [hs] at hb hprec
        refine ⟨R.α p, s, ha, rfl, le_refl _, by exact_mod_cast hprec, ?_⟩
        have hb' : s + L.τ ⟨0, hk⟩ ≤ R.α p + (L.Gamma lam γ ⟨0, hk⟩ + L.τ ⟨0, hk⟩) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add] at hb; exact_mod_cast hb
        have : ∑ j ∈ univ.filter (fun j : Fin L.l => j.val ≤ 0), D j = D ⟨0, hk⟩ := by
          rw [sum_eq_single_of_mem (⟨0, hk⟩ : Fin L.l) (by simp)]
          intro b hb hne
          simp only [mem_filter, mem_univ, true_and, Nat.le_zero] at hb
          exact absurd (Fin.ext hb) hne
        rw [this]; simpa [hD] using hb'
    | succ k ih =>
      intro hk
      obtain ⟨a, s, ha, hs, hαa, has, hsb⟩ := ih (by omega)
      have hlt : R.entry p < ⟨k + 1, hk⟩ := by rw [hentry]; simp [Fin.lt_def]
      have ha' : R.arrive p ⟨k + 1, hk⟩ = ((s + L.τ ⟨k, by omega⟩ : ℝ) : WithTop ℝ) := by
        unfold Run.arrive
        rw [if_neg (ne_of_lt hlt).symm, if_pos hlt]
        simp only [Nat.add_sub_cancel]
        rw [hs, WithTop.coe_add]
      have hτk := L.τ_pos ⟨k, by omega⟩
      have hle : R.entry p ≤ ⟨k + 1, hk⟩ := le_of_lt hlt
      have hb := hT ⟨k + 1, hk⟩ p hle (by rw [ha']; exact_mod_cast (by linarith [hTj ⟨k+1, hk⟩]))
      rw [ha'] at hb
      have hprec := hR.precedence p ⟨k + 1, hk⟩ hle
      rcases hprec with hprec | hprec
      swap; · exact absurd hprec.1 hp
      rw [ha'] at hprec
      cases hs' : R.start p ⟨k + 1, hk⟩ with
      | top => rw [hs'] at hb; simp at hb
      | coe s' =>
        rw [hs'] at hb hprec
        refine ⟨s + L.τ ⟨k, by omega⟩, s', ha', rfl, by linarith, by exact_mod_cast hprec, ?_⟩
        have hb' : s' + L.τ ⟨k + 1, hk⟩ ≤
            s + L.τ ⟨k, by omega⟩ + (L.Gamma lam γ ⟨k + 1, hk⟩ + L.τ ⟨k + 1, hk⟩) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add] at hb; exact_mod_cast hb
        have hsplit : ∑ j ∈ univ.filter (fun j : Fin L.l => j.val ≤ k + 1), D j =
            ∑ j ∈ univ.filter (fun j : Fin L.l => j.val ≤ k), D j + D ⟨k + 1, hk⟩ := by
          have : univ.filter (fun j : Fin L.l => j.val ≤ k + 1) =
              insert ⟨k + 1, hk⟩ (univ.filter (fun j : Fin L.l => j.val ≤ k)) := by
            ext j; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
          rw [this, sum_insert (by simp), add_comm]
        rw [hsplit]
        simp only [hD] at hsb ⊢
        linarith
  obtain ⟨a, s, ha, hs, -, -, hsb⟩ := main (L.l - 1) (by have := L.l_pos; omega)
  have hsum : ∑ j ∈ univ.filter (fun j : Fin L.l => j.val ≤ L.l - 1), D j =
      ∑ j : Fin L.l, D j := by
    congr 1; ext j; simp only [mem_filter, mem_univ, true_and, iff_true]; omega
  rw [hsum] at hsb
  unfold Run.exit
  rw [hs, ← WithTop.coe_add]
  exact_mod_cast hsb
