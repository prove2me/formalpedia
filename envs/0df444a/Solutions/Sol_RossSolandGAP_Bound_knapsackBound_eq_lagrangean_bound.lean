-- Prove2me | solution 1 for RossSolandGAP.Bound.knapsackBound_eq_lagrangean_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:54:37.742424+00:00
-- url     : https://prove2.me/submissions/19b2ac25-970e-4a1e-971d-471c5d0911b3

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model

open RossSolandGAP.Bound Finset in
theorem solution {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 < b i) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin n → Fin m) (ha : IsCheapest c a) (ystar : Fin m → Fin n → ℝ)
    (hystar : ∀ i ∈ Iprime r b a, IsOptPK hm c r b a i (ystar i)) :
    (∀ x, FeasibleLag r b x → LB hm c r b a ystar ≤ lagObj c (c2 hm c a) x) ∧
    (∃ x, FeasibleLag r b x ∧ lagObj c (c2 hm c a) x = LB hm c r b a ystar) ∧
    (∀ x, FeasibleP r b x → LB hm c r b a ystar ≤ cost c x) := by
  have _ := hb
  have hc2le : ∀ j, ∀ k, k ≠ a j → c2 hm c a j ≤ c k j := by
    intro j k hk
    unfold c2
    exact Finset.inf'_le (fun k => c k j) (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩)
  have hpen : ∀ j, pen hm c a j = c2 hm c a j - c (a j) j := by
    intro j
    apply le_antisymm
    · obtain ⟨k, hk, hkeq⟩ :=
        Finset.exists_mem_eq_inf' (others_nonempty hm (a j)) (fun k => c k j)
      have h1 : pen hm c a j ≤ c k j - c (a j) j := by
        unfold pen
        exact Finset.inf'_le (fun k => c k j - c (a j) j) hk
      have h2 : c2 hm c a j = c k j := by unfold c2; exact hkeq
      rw [h2]; exact h1
    · unfold pen
      apply Finset.le_inf'
      intro k hk
      have := hc2le j k (Finset.ne_of_mem_erase hk)
      linarith
  have hpen0 : ∀ j, 0 ≤ pen hm c a j := by
    intro j
    unfold pen
    apply Finset.le_inf'
    intro k _
    have := ha j k
    linarith
  have hfib : ∀ F : Fin m → Fin n → ℝ, ∑ i, ∑ j ∈ Jset a i, F i j = ∑ j, F (a j) j := by
    intro F
    have hc : ∀ i, ∑ j ∈ Jset a i, F i j = ∑ j ∈ Jset a i, F (a j) j := by
      intro i
      apply Finset.sum_congr rfl
      intro j hj
      have : a j = i := (Finset.mem_filter.mp hj).2
      rw [this]
    rw [Finset.sum_congr rfl (fun i _ => hc i)]
    unfold Jset
    exact Finset.sum_fiberwise Finset.univ a (fun j => F (a j) j)
  have hlag : ∀ x : Fin m → Fin n → ℝ, lagObj c (c2 hm c a) x =
      ∑ j, (c2 hm c a j + ∑ i, (c i j - c2 hm c a j) * x i j) := by
    intro x
    unfold lagObj cost
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hbin01 : ∀ (x : Fin m → Fin n → ℝ), IsBinary x → ∀ i j, 0 ≤ x i j ∧ x i j ≤ 1 := by
    intro x hx i j
    rcases hx i j with h | h <;> rw [h] <;> norm_num
  have hlow : ∀ x : Fin m → Fin n → ℝ, IsBinary x →
      Z c a + ∑ j, pen hm c a j * (1 - x (a j) j) ≤ lagObj c (c2 hm c a) x := by
    intro x hx
    rw [hlag]
    unfold Z
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (a j))]
    have hnn : 0 ≤ ∑ i ∈ Finset.univ.erase (a j), (c i j - c2 hm c a j) * x i j := by
      apply Finset.sum_nonneg
      intro i hi
      have h1 := hc2le j i (Finset.ne_of_mem_erase hi)
      have h2 := (hbin01 x hx i j).1
      exact mul_nonneg (by linarith) h2
    rw [hpen j]
    linarith
  have hclaim1 : ∀ x, FeasibleLag r b x → LB hm c r b a ystar ≤ lagObj c (c2 hm c a) x := by
    intro x hx
    obtain ⟨hxb, hxr⟩ := hx
    have hmain : ∑ i ∈ Iprime r b a, pkObj hm c a i (ystar i)
        ≤ ∑ j, pen hm c a j * (1 - x (a j) j) := by
      calc ∑ i ∈ Iprime r b a, pkObj hm c a i (ystar i)
          ≤ ∑ i ∈ Iprime r b a, ∑ j ∈ Jset a i, pen hm c a j * (1 - x i j) := by
            apply Finset.sum_le_sum
            intro i hi
            have hfe : FeasiblePK r b a i (fun j => 1 - x i j) := by
              constructor
              · intro j _
                rcases hxb i j with h | h <;> simp [h]
              · unfold dgap load
                have hsub : ∑ j ∈ Jset a i, r i j * x i j ≤ ∑ j, r i j * x i j :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                    (fun j _ _ => mul_nonneg (hr i j) (hbin01 x hxb i j).1)
                have hsplit : ∑ j ∈ Jset a i, r i j * (1 - x i j) =
                    ∑ j ∈ Jset a i, r i j - ∑ j ∈ Jset a i, r i j * x i j := by
                  rw [← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
                rw [hsplit]
                linarith [hxr i]
            exact (hystar i hi).2 _ hfe
        _ ≤ ∑ i, ∑ j ∈ Jset a i, pen hm c a j * (1 - x i j) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro i _ _
            apply Finset.sum_nonneg
            intro j _
            exact mul_nonneg (hpen0 j) (by linarith [(hbin01 x hxb i j).2])
        _ = ∑ j, pen hm c a j * (1 - x (a j) j) :=
            hfib (fun i j => pen hm c a j * (1 - x i j))
    have := hlow x hxb
    unfold LB
    linarith
  have hLB : LB hm c r b a ystar = Z c a +
      ∑ j, (if a j ∈ Iprime r b a then pen hm c a j * ystar (a j) j else 0) := by
    unfold LB pkObj
    congr 1
    rw [← hfib (fun i j => if i ∈ Iprime r b a then pen hm c a j * ystar i j else 0)]
    have hc : ∀ i, (∑ j ∈ Jset a i, if i ∈ Iprime r b a then pen hm c a j * ystar i j else 0)
        = if i ∈ Iprime r b a then ∑ j ∈ Jset a i, pen hm c a j * ystar i j else 0 := by
      intro i
      split_ifs <;> simp
    simp only [hc]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine ⟨hclaim1, ?_, ?_⟩
  · refine ⟨fun i j => if a j = i then (if i ∈ Iprime r b a then 1 - ystar i j else 1) else 0,
      ⟨?_, ?_⟩, ?_⟩
    · intro i j
      by_cases h : a j = i
      · by_cases hi : i ∈ Iprime r b a
        · have hj : j ∈ Jset a i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          rcases (hystar i hi).1.1 j hj with hy | hy <;> simp [h, hi, hy]
        · simp [h, hi]
      · simp [h]
    · intro i
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      change ∑ j ∈ Jset a i, (if i ∈ Iprime r b a then r i j * (1 - ystar i j) else r i j * 1)
        ≤ b i
      by_cases hi : i ∈ Iprime r b a
      · simp only [hi, if_true]
        have hk := (hystar i hi).1.2
        unfold dgap load at hk
        have hsplit : ∑ j ∈ Jset a i, r i j * (1 - ystar i j) =
            ∑ j ∈ Jset a i, r i j - ∑ j ∈ Jset a i, r i j * ystar i j := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hsplit]
        linarith
      · simp only [hi, if_false, mul_one]
        have : ¬ (b i < load r a i) := by
          intro hlt
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        unfold load at this
        linarith
    · rw [hlag, hLB]
      unfold Z
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [hpen j]
      by_cases h : a j ∈ Iprime r b a
      · simp only [h, if_true]
        ring
      · simp only [h, if_false]
        ring
  · intro x hx
    have h1 := hclaim1 x ⟨hx.1, hx.2.1⟩
    have h2 : lagObj c (c2 hm c a) x = cost c x := by
      unfold lagObj
      simp [hx.2.2]
    linarith
