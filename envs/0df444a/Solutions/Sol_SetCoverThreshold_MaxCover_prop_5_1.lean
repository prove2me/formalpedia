-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.prop_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:44:12.028095+00:00
-- url     : https://prove2.me/submissions/713bf47d-93a6-4ab9-9247-9f6a4b485b11

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Instance

namespace SetCoverThreshold.MaxCover

/-- The points covered after the first `t` greedy steps. -/
def aux_mc51_C (I : Instance) (run : Fin I.k → Fin I.sets.length) (t : ℕ) : Finset (Fin I.n) :=
  coverOf I ((Finset.univ.filter (fun s : Fin I.k => s.val < t)).image run)

theorem aux_mc51_C_zero (I : Instance) (run : Fin I.k → Fin I.sets.length) :
    aux_mc51_C I run 0 = ∅ := by
  simp [aux_mc51_C, coverOf]

theorem aux_mc51_C_k (I : Instance) (run : Fin I.k → Fin I.sets.length) :
    aux_mc51_C I run I.k = coverOf I (Finset.univ.image run) := by
  simp [aux_mc51_C]

theorem aux_mc51_C_succ (I : Instance) (run : Fin I.k → Fin I.sets.length) (t : ℕ)
    (ht : t < I.k) :
    aux_mc51_C I run (t+1) = I.sets.get (run ⟨t, ht⟩) ∪ aux_mc51_C I run t := by
  unfold aux_mc51_C coverOf
  have : (Finset.univ.filter (fun s : Fin I.k => s.val < t + 1)) =
      insert ⟨t, ht⟩ (Finset.univ.filter (fun s : Fin I.k => s.val < t)) := by
    ext s
    simp [Fin.ext_iff]
    omega
  rw [this, Finset.image_insert, Finset.biUnion_insert]

theorem aux_mc51_C_fin (I : Instance) (run : Fin I.k → Fin I.sets.length) (t : Fin I.k) :
    coverOf I ((Finset.univ.filter (· < t)).image run) = aux_mc51_C I run t.val := by
  unfold aux_mc51_C
  congr 2

theorem aux_mc51_step (I : Instance) (run : Fin I.k → Fin I.sets.length)
    (hrun : IsGreedyRun I run) (t : ℕ) (ht : t < I.k) :
    opt I ≤ (aux_mc51_C I run t).card +
      I.k * (I.sets.get (run ⟨t, ht⟩) \ aux_mc51_C I run t).card := by
  unfold opt
  apply Finset.sup_le
  intro T hT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  have hg : ∀ i : Fin I.sets.length, (I.sets.get i \ aux_mc51_C I run t).card ≤
      (I.sets.get (run ⟨t, ht⟩) \ aux_mc51_C I run t).card := by
    intro i
    have := hrun ⟨t, ht⟩ i
    rw [aux_mc51_C_fin] at this
    exact this
  set C := aux_mc51_C I run t
  set g := (I.sets.get (run ⟨t, ht⟩) \ C).card
  have h1 : coverOf I T ⊆ (T.biUnion (fun i => I.sets.get i \ C)) ∪ C := by
    intro x hx
    unfold coverOf at hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    by_cases hxC : x ∈ C
    · exact Finset.mem_union_right _ hxC
    · exact Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨hxi, hxC⟩⟩)
  have h2 : (T.biUnion (fun i => I.sets.get i \ C)).card ≤ T.card * g := by
    calc (T.biUnion (fun i => I.sets.get i \ C)).card
        ≤ ∑ i ∈ T, (I.sets.get i \ C).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ T, g := by
          apply Finset.sum_le_sum
          intro i _
          exact hg i
      _ = T.card * g := by simp
  have h3 : T.card * g ≤ I.k * g := Nat.mul_le_mul_right g hT
  calc (coverOf I T).card ≤ ((T.biUnion (fun i => I.sets.get i \ C)) ∪ C).card :=
        Finset.card_le_card h1
    _ ≤ (T.biUnion (fun i => I.sets.get i \ C)).card + C.card := Finset.card_union_le _ _
    _ ≤ C.card + I.k * g := by omega

theorem aux_mc51_bound (I : Instance) (run : Fin I.k → Fin I.sets.length)
    (hrun : IsGreedyRun I run) (hk : 0 < I.k) (t : ℕ) (ht : t ≤ I.k) :
    (opt I : ℝ) - (aux_mc51_C I run t).card ≤ (1 - 1 / (I.k : ℝ)) ^ t * opt I := by
  induction t with
  | zero => simp [aux_mc51_C_zero]
  | succ t ih =>
    have ht' : t < I.k := by omega
    have ih := ih (by omega)
    have hstep := aux_mc51_step I run hrun t ht'
    have hsucc := aux_mc51_C_succ I run t ht'
    have hcard : (aux_mc51_C I run (t+1)).card = (aux_mc51_C I run t).card +
        (I.sets.get (run ⟨t, ht'⟩) \ aux_mc51_C I run t).card := by
      rw [hsucc, ← Finset.card_sdiff_add_card]; ring
    rw [hcard]
    set c := (aux_mc51_C I run t).card
    set g := (I.sets.get (run ⟨t, ht'⟩) \ aux_mc51_C I run t).card
    have hkR : (0:ℝ) < I.k := by exact_mod_cast hk
    have hstepR : (opt I : ℝ) ≤ c + I.k * g := by exact_mod_cast hstep
    have hq : 0 ≤ 1 - 1 / (I.k : ℝ) := by
      rw [sub_nonneg, div_le_one hkR]; exact_mod_cast hk
    have key : (opt I : ℝ) - ((c + g : ℕ) : ℝ) ≤
        (1 - 1 / (I.k : ℝ)) * ((opt I : ℝ) - c) := by
      push_cast
      have h4 : ((opt I : ℝ) - c) / I.k ≤ g := by
        rw [div_le_iff₀ hkR]; linarith
      have e : (1 - 1 / (I.k : ℝ)) * ((opt I : ℝ) - c) =
          ((opt I : ℝ) - c) - ((opt I : ℝ) - c) / I.k := by
        field_simp
      rw [e]; linarith
    calc (opt I : ℝ) - ((c + g : ℕ) : ℝ) ≤ (1 - 1 / (I.k : ℝ)) * ((opt I : ℝ) - c) := key
      _ ≤ (1 - 1 / (I.k : ℝ)) * ((1 - 1 / (I.k : ℝ)) ^ t * opt I) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = (1 - 1 / (I.k : ℝ)) ^ (t+1) * opt I := by ring

theorem aux_mc51_opt_zero (I : Instance) (hk : I.k = 0) : opt I = 0 := by
  unfold opt
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro T hT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hk, Nat.le_zero,
    Finset.card_eq_zero] at hT
  subst hT
  simp [coverOf]

theorem aux_mc51_pow (k : ℕ) (hk : 0 < k) : (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-1) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have h0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hkR]; exact_mod_cast hk
  have h1 : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / k)) := by
    have := Real.add_one_le_exp (-(1 / (k:ℝ)))
    linarith
  calc (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-(1 / k)) ^ k := pow_le_pow_left₀ h0 h1 k
    _ = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

end SetCoverThreshold.MaxCover

open SetCoverThreshold.MaxCover

theorem solution (I : Instance) (run : Fin I.k → Fin I.sets.length) (hrun : IsGreedyRun I run) :
    (1 - Real.exp (-1)) * (opt I : ℝ) ≤ (coverOf I (Finset.univ.image run)).card := by
  rcases Nat.eq_zero_or_pos I.k with hk | hk
  · rw [aux_mc51_opt_zero I hk]; simp
  · have h := aux_mc51_bound I run hrun hk I.k le_rfl
    rw [aux_mc51_C_k] at h
    have hp := aux_mc51_pow I.k hk
    have hopt : (0:ℝ) ≤ opt I := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hp hopt]
