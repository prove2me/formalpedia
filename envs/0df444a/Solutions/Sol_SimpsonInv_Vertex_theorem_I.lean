-- Prove2me | solution 1 for SimpsonInv.Vertex.theorem_I
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:45:37.879046+00:00
-- url     : https://prove2.me/submissions/ca2bd015-014c-48e7-b467-c216a7bcbfef

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

set_option autoImplicit false

namespace SimpsonInvVertexE051

open SimpsonInv.Vertex

theorem extVec_comb {m : ℕ} (S0 Sn a b : ℝ) (hab : a + b = 1) (y z : Fin m → ℝ) (i : ℕ) :
    extVec S0 Sn (a • y + b • z) i = a * extVec S0 Sn y i + b * extVec S0 Sn z i := by
  unfold extVec
  by_cases h0 : i = 0
  · simp only [h0, dite_true]
    linear_combination (-S0) * hab
  · by_cases h : i ≤ m
    · simp only [h0, h, dite_true, dite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · simp only [h0, h, dite_false]
      linear_combination (-Sn) * hab

theorem radicand_comb {m : ℕ} (T : ℕ → ℝ) (S0 Sn a b : ℝ) (hab : a + b = 1)
    (y z : Fin m → ℝ) (i : ℕ) :
    radicand T S0 Sn (a • y + b • z) i
      = a * radicand T S0 Sn y i + b * radicand T S0 Sn z i := by
  unfold radicand
  rw [extVec_comb S0 Sn a b hab, extVec_comb S0 Sn a b hab]
  linear_combination (-T i) * hab

theorem sqrt_conc (u v a b : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * Real.sqrt u + b * Real.sqrt v ≤ Real.sqrt (a * u + b * v) := by
  have := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv) ha hb hab
  simpa [smul_eq_mul] using this

theorem cost_conc {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) {y z : Fin m → ℝ}
    (hy : y ∈ dom (m := m) T S0 Sn) (hz : z ∈ dom (m := m) T S0 Sn) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * cost c r T S0 Sn y + b * cost c r T S0 Sn z ≤ cost c r T S0 Sn (a • y + b • z) := by
  have key : ∀ i ∈ Finset.Icc 1 (m + 1),
      a * (r i * Real.sqrt (radicand T S0 Sn y i)) + b * (r i * Real.sqrt (radicand T S0 Sn z i))
        ≤ r i * Real.sqrt (radicand T S0 Sn (a • y + b • z) i) := by
    intro i hi
    rw [radicand_comb T S0 Sn a b hab]
    have h := sqrt_conc _ _ a b (hy.2 i hi) (hz.2 i hi) ha hb hab
    calc a * (r i * Real.sqrt (radicand T S0 Sn y i)) + b * (r i * Real.sqrt (radicand T S0 Sn z i))
        = r i * (a * Real.sqrt (radicand T S0 Sn y i) + b * Real.sqrt (radicand T S0 Sn z i)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (hr i hi).le
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  unfold cost
  linear_combination hs + c * hab

theorem extVec_zero {m : ℕ} (S0 Sn : ℝ) (S : Fin m → ℝ) : extVec S0 Sn S 0 = S0 := by
  simp [extVec]

theorem extVec_succ {m : ℕ} (S0 Sn : ℝ) (S : Fin m → ℝ) (k : ℕ) (hk : k < m) :
    extVec S0 Sn S (k + 1) = S ⟨k, hk⟩ := by
  unfold extVec
  rw [dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel]

theorem step_le {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) {S : Fin m → ℝ}
    (hS : S ∈ dom (m := m) T S0 Sn) (k : ℕ) (hk : k < m) :
    S ⟨k, hk⟩ ≤ extVec S0 Sn S k + T (k + 1) := by
  have h := hS.2 (k + 1) (by simp only [Finset.mem_Icc]; omega)
  unfold radicand at h
  rw [extVec_succ S0 Sn S k hk] at h
  simp only [Nat.add_sub_cancel] at h
  linarith

theorem coord_le {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) {S : Fin m → ℝ}
    (hS : S ∈ dom (m := m) T S0 Sn) :
    ∀ k (hk : k < m), S ⟨k, hk⟩ ≤ |S0| + ∑ i ∈ Finset.range (k + 2), |T i| := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h := step_le T S0 Sn hS 0 hk
    rw [extVec_zero] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have h1 := le_abs_self S0
    have h2 := le_abs_self (T 1)
    have h3 := abs_nonneg (T 0)
    simp only [zero_add] at h
    linarith
  | succ k ih =>
    intro hk
    have h := step_le T S0 Sn hS (k + 1) hk
    rw [extVec_succ S0 Sn S k (by omega)] at h
    have h' := ih (by omega)
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_range_succ]
    have h2 := le_abs_self (T (k + 1 + 1))
    linarith

theorem cont_extVec {m : ℕ} (S0 Sn : ℝ) (i : ℕ) :
    Continuous (fun S : Fin m → ℝ => extVec S0 Sn S i) := by
  unfold extVec
  by_cases h0 : i = 0
  · simp only [h0, dite_true]
    exact continuous_const
  · by_cases h : i ≤ m
    · simp only [h0, h, dite_true, dite_false]
      exact continuous_apply _
    · simp only [h0, h, dite_false]
      exact continuous_const

theorem cont_radicand {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (i : ℕ) :
    Continuous (fun S : Fin m → ℝ => radicand T S0 Sn S i) := by
  unfold radicand
  exact ((cont_extVec S0 Sn (i - 1)).sub (cont_extVec S0 Sn i)).add continuous_const

theorem cont_cost {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) :
    Continuous (cost (m := m) c r T S0 Sn) := by
  unfold cost
  exact continuous_const.add (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Real.continuous_sqrt.comp (cont_radicand T S0 Sn i)))

theorem dom_compact {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) :
    IsCompact (dom (m := m) T S0 Sn) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have e : dom (m := m) T S0 Sn = (⋂ j, {S : Fin m → ℝ | 0 ≤ S j}) ∩
        ⋂ i ∈ Finset.Icc 1 (m + 1), {S : Fin m → ℝ | 0 ≤ radicand T S0 Sn S i} := by
      ext S
      simp [dom]
    rw [e]
    exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_biInter fun i _ => isClosed_le continuous_const (cont_radicand T S0 Sn i))
  · set C : ℝ := |S0| + ∑ i ∈ Finset.range (m + 2), |T i| with hC
    have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨C, fun S hS => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hC0]
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have h1 := coord_le T S0 Sn hS j.1 j.2
    have h2 : ∑ i ∈ Finset.range (j.1 + 2), |T i| ≤ ∑ i ∈ Finset.range (m + 2), |T i| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => abs_nonneg _)
    have h3 := hS.1 j
    constructor
    · linarith
    · have : S ⟨j.1, j.2⟩ = S j := rfl
      linarith

end SimpsonInvVertexE051

open SimpsonInv.Vertex in
theorem solution {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (dom (m := m) T S0 Sn),
      IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by
  have hK := SimpsonInvVertexE051.dom_compact (m := m) T S0 Sn
  have hcont := SimpsonInvVertexE051.cont_cost (m := m) c S0 Sn r T
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hD hcont.continuousOn
  have hmin' := isMinOn_iff.mp hmin
  set A : Set (Fin m → ℝ) :=
    dom (m := m) T S0 Sn ∩ cost c r T S0 Sn ⁻¹' {cost c r T S0 Sn x0} with hA
  have hAc : IsCompact A := hK.inter_right (isClosed_singleton.preimage hcont)
  have hAext : IsExtreme ℝ (dom (m := m) T S0 Sn) A := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro x hx y hy z hz hzs
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzs
    have hc := SimpsonInvVertexE051.cost_conc c S0 Sn r T hr hx hy ha.le hb.le hab
    have hzv : cost c r T S0 Sn (a • x + b • y) = cost c r T S0 Sn x0 := hz.2
    have h1 := hmin' x hx
    have h2 := hmin' y hy
    refine ⟨hx, ?_⟩
    show cost c r T S0 Sn x = cost c r T S0 Sn x0
    apply le_antisymm _ h1
    by_contra hne
    have hne' : cost c r T S0 Sn x0 < cost c r T S0 Sn x := lt_of_not_ge hne
    have e : a * cost c r T S0 Sn x0 + b * cost c r T S0 Sn x0 = cost c r T S0 Sn x0 := by
      rw [← add_mul, hab, one_mul]
    have p1 := mul_lt_mul_of_pos_left hne' ha
    have p2 := mul_le_mul_of_nonneg_left h2 hb.le
    linarith
  obtain ⟨v, hv⟩ := hAc.extremePoints_nonempty ⟨x0, hx0, rfl⟩
  refine ⟨v, hAext.extremePoints_subset_extremePoints hv, ?_⟩
  have hvA : v ∈ A := hv.1
  rw [isMinOn_iff]
  intro y hy
  have hv2 : cost c r T S0 Sn v = cost c r T S0 Sn x0 := hvA.2
  rw [hv2]
  exact hmin' y hy
