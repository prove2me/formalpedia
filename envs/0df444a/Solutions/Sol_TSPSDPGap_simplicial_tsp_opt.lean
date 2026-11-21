-- Prove2me | solution 1 for TSPSDPGap.simplicial_tsp_opt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:11:45.528803+00:00
-- url     : https://prove2.me/submissions/5b067afc-b4e7-4b20-a8c5-44ef08b803e6

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_TSPSDPGap_simplicialCostExt

namespace TSPSDPGap

namespace Aux_STO

def grpF (g n : ℕ) (s : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  Fin.insertNth (α := fun _ => ℕ) s 0 (fun i : Fin n => (i : ℕ) / (n / g))

lemma cost_eq (g n : ℕ) (s u v : Fin (n + 1)) :
    simplicialCostExt g n s u v = if grpF g n s u = grpF g n s v then 0 else 1 := rfl

lemma grp_s (g n : ℕ) (s : Fin (n + 1)) : grpF g n s s = 0 := by
  unfold grpF; exact Fin.insertNth_apply_same _ _ _

lemma grp_sa (g n : ℕ) (s : Fin (n + 1)) (i : Fin n) :
    grpF g n s (s.succAbove i) = (i : ℕ) / (n / g) := by
  unfold grpF; exact Fin.insertNth_apply_succAbove _ _ _ _

lemma metric (g n : ℕ) (s : Fin (n + 1)) : MetricTSP.IsMetricCost (simplicialCostExt g n s) := by
  refine ⟨fun u v => ?_, fun v => ?_, fun u v w => ?_⟩
  · rw [cost_eq, cost_eq]
    by_cases h : grpF g n s u = grpF g n s v
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rw [cost_eq, if_pos rfl]
  · rw [cost_eq, cost_eq, cost_eq]
    split_ifs <;> (try norm_num) <;> omega

end Aux_STO

end TSPSDPGap

open Fin.NatCast in
open TSPSDPGap TSPSDPGap.Aux_STO in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n)
    (s : Fin (n + 1)) :
    MetricTSP.IsMetricCost (simplicialCostExt g n s) ∧
      MetricTSP.tspOpt (simplicialCostExt g n s) = g := by
  refine ⟨metric g n s, ?_⟩
  obtain ⟨q, hq⟩ := hgn
  have hg0 : 0 < g := by omega
  have hqdef : n / g = q := by rw [hq, Nat.mul_div_cancel_left _ hg0]
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  have hqn : q < n := by
    rw [hq]
    have : 1 * q < g * q := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    simpa using this
  -- lower bound for every tour
  have hlower : ∀ π : Equiv.Perm (Fin (n + 1)),
      (g : ℝ) ≤ MetricTSP.tourCost (simplicialCostExt g n s) π := by
    intro π
    have hentry : ∀ k : Fin g, ∃ i : Fin (n + 1),
        grpF g n s (π i) ≠ (k : ℕ) ∧ grpF g n s (π (i + 1)) = (k : ℕ) := by
      intro k
      have hk := k.isLt
      obtain ⟨u, hu⟩ : ∃ u : Fin (n + 1), grpF g n s u = (k : ℕ) := by
        by_cases hk0 : (k : ℕ) = 0
        · exact ⟨s, by rw [grp_s, hk0]⟩
        · have hlt' : (k : ℕ) * q < n := by
            rw [hq]
            exact Nat.mul_lt_mul_of_pos_right hk (by omega)
          refine ⟨s.succAbove ⟨(k : ℕ) * q, hlt'⟩, ?_⟩
          rw [grp_sa, hqdef]
          exact Nat.mul_div_cancel _ (by omega)
      obtain ⟨w, hw⟩ : ∃ w : Fin (n + 1), grpF g n s w ≠ (k : ℕ) := by
        by_cases hk0 : (k : ℕ) = 0
        · refine ⟨s.succAbove ⟨q, hqn⟩, ?_⟩
          rw [grp_sa, hqdef]
          simp only
          rw [Nat.div_self (by omega)]
          omega
        · exact ⟨s, by rw [grp_s]; omega⟩
      by_contra hcon
      push_neg at hcon
      have hi0 : grpF g n s (π (π.symm u)) = (k : ℕ) := by simp [hu]
      have hall : ∀ d : ℕ, grpF g n s (π (π.symm u - (d : Fin (n + 1)))) = (k : ℕ) := by
        intro d
        induction d with
        | zero => simpa using hi0
        | succ d ih =>
          by_contra hne
          have h2 := hcon _ hne
          apply h2
          rw [show π.symm u - ((d + 1 : ℕ) : Fin (n + 1)) + 1 = π.symm u - (d : Fin (n + 1)) by
            rw [Nat.cast_succ]; abel]
          exact ih
      have h3 := hall ((π.symm u - π.symm w : Fin (n + 1)) : ℕ)
      simp only [Fin.cast_val_eq_self, sub_sub_cancel] at h3
      exact hw (by simpa using h3)
    choose f hf using hentry
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 := (hf a).2
      have h2 := (hf b).2
      rw [hab] at h1
      exact Fin.ext (by omega)
    unfold MetricTSP.tourCost
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ simplicialCostExt g n s (π i) (π (finRotate (n + 1) i)) := by
      intro i _
      rw [cost_eq]; split_ifs <;> norm_num
    calc (g : ℝ) = ∑ k : Fin g, (1 : ℝ) := by simp
      _ = ∑ k : Fin g, simplicialCostExt g n s (π (f k)) (π (finRotate (n + 1) (f k))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [cost_eq, finRotate_succ_apply, if_neg]
          rw [(hf k).2]
          exact fun h => (hf k).1 h
      _ = ∑ i ∈ Finset.univ.image f, simplicialCostExt g n s (π i) (π (finRotate (n + 1) i)) := by
          rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      _ ≤ ∑ i, simplicialCostExt g n s (π i) (π (finRotate (n + 1) i)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i hi _ => hnn i hi)
  -- an optimal tour
  obtain ⟨π0, hπ0⟩ : ∃ π0 : Equiv.Perm (Fin (n + 1)),
      π0 = (finSuccEquiv n).trans (finSuccEquiv' s).symm := ⟨_, rfl⟩
  have hπ0_zero : π0 0 = s := by
    rw [hπ0, Equiv.trans_apply, finSuccEquiv_zero, finSuccEquiv'_symm_none]
  have hπ0_succ : ∀ j : Fin n, π0 j.succ = s.succAbove j := by
    intro j
    rw [hπ0, Equiv.trans_apply, finSuccEquiv_succ, finSuccEquiv'_symm_some]
  -- class of the k-th visited city
  have hcls : ∀ (k : ℕ) (hk : k < n + 1),
      grpF g n s (π0 ⟨k, hk⟩) = if k = 0 then 0 else (k - 1) / q := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, show (⟨0, hk⟩ : Fin (n + 1)) = 0 from Fin.ext (by simp), hπ0_zero, grp_s]
    · rw [if_neg hk0, show (⟨k, hk⟩ : Fin (n + 1)) = Fin.succ ⟨k - 1, by omega⟩ from
        Fin.ext (by simp; omega), hπ0_succ, grp_sa, hqdef]
  obtain ⟨cl, hcl⟩ : ∃ cl : ℕ → ℕ, cl = fun k => if k = 0 then 0 else (k - 1) / q := ⟨_, rfl⟩
  have hcost : ∀ i : Fin (n + 1),
      simplicialCostExt g n s (π0 i) (π0 (finRotate (n + 1) i))
        = (fun k : ℕ => if cl k = cl (if k = n then 0 else k + 1) then (0:ℝ) else 1) (i : ℕ) := by
    intro i
    have h1 : π0 i = π0 ⟨(i : ℕ), i.isLt⟩ := rfl
    have hrot : finRotate (n + 1) i = ⟨if (i : ℕ) = n then 0 else (i : ℕ) + 1, by
        split_ifs <;> omega⟩ := by
      apply Fin.ext
      rw [finRotate_succ_apply, Fin.val_add_one]
      simp only [Fin.ext_iff, Fin.val_last]
    rw [cost_eq, h1, hrot, hcls, hcls, hcl]
  have hdiff : ∀ k : ℕ, k < n →
      (if cl k = cl (if k = n then 0 else k + 1) then (0:ℝ) else 1)
        = (cl (k + 1) : ℝ) - (cl k : ℝ) := by
    intro k hk
    have e1 : (if k = n then 0 else k + 1) = k + 1 := if_neg (by omega)
    have hrel : cl (k + 1) = cl k ∨ cl (k + 1) = cl k + 1 := by
      rw [hcl]
      simp only
      by_cases hk0 : k = 0
      · subst hk0; left; simp
      · rw [if_neg hk0, if_neg (by omega : ¬ k + 1 = 0), show k + 1 - 1 = k by omega]
        have := @Nat.succ_div (k - 1) q
        rw [show k - 1 + 1 = k by omega] at this
        rw [this]
        split_ifs <;> simp
    rw [e1]
    rcases hrel with h | h
    · rw [h, if_pos rfl]; simp
    · rw [h, if_neg (by omega)]; push_cast; ring
  have hcln : cl n = g - 1 := by
    rw [hcl]
    simp only [show n ≠ 0 by omega, ↓reduceIte]
    have hle : q ≤ g * q := Nat.le_mul_of_pos_left q hg0
    have e : n - 1 = (q - 1) + (g - 1) * q := by
      rw [Nat.sub_one_mul, hq]; omega
    rw [e, Nat.add_mul_div_right _ _ (by omega : 0 < q), Nat.div_eq_of_lt (by omega), zero_add]
  have hcl0 : cl 0 = 0 := by rw [hcl]; simp
  have hupper : MetricTSP.tourCost (simplicialCostExt g n s) π0 = g := by
    unfold MetricTSP.tourCost
    have hsum : ∑ i : Fin (n + 1), simplicialCostExt g n s (π0 i) (π0 (finRotate (n + 1) i))
        = ∑ k ∈ Finset.range (n + 1),
          (if cl k = cl (if k = n then 0 else k + 1) then (0:ℝ) else 1) := by
      rw [Finset.sum_congr rfl (fun i _ => hcost i)]
      exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        if cl k = cl (if k = n then 0 else k + 1) then (0:ℝ) else 1) (n + 1)
    have htel : ∑ k ∈ Finset.range n, ((cl (k + 1) : ℝ) - (cl k : ℝ)) = (cl n : ℝ) - (cl 0 : ℝ) :=
      Finset.sum_range_sub (fun k => (cl k : ℝ)) n
    rw [hsum, Finset.sum_range_succ,
      Finset.sum_congr rfl (fun k hk => hdiff k (Finset.mem_range.mp hk)), htel]
    rw [if_pos rfl, hcln, hcl0, if_neg (by omega : ¬ g - 1 = 0)]
    rw [Nat.cast_sub (by omega : 1 ≤ g)]
    push_cast
    ring
  unfold MetricTSP.tspOpt
  apply le_antisymm
  · rw [← hupper]
    apply csInf_le
    · exact ⟨0, fun t ⟨π, hπ⟩ => by rw [hπ]; exact le_trans (by positivity) (hlower π)⟩
    · exact ⟨π0, rfl⟩
  · apply le_csInf
    · exact ⟨_, π0, rfl⟩
    · rintro t ⟨π, rfl⟩
      exact hlower π
