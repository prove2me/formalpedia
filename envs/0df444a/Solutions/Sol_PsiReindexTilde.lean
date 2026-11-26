-- Prove2me | solution 1 for PsiReindexTilde
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:41.348589+00:00
-- url     : https://prove2.me/submissions/e8ea80d9-eb3b-4104-9708-3fa37896d5fd

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_PsiReindex
import Definitions.Def_Tablet_PsiReindexTilde
import Theorems.Thm_CurveRestrictTotAgrees
import Theorems.Thm_PsiReindex


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (m l : ℕ) (hm : 0 < m) (hl : 0 < l)
    (Q : Finset E) (ε C : ℝ) (γ : Curve E) (hlen : γ.len = (l : ℝ)) :
    psiTilde (m * l) Q ε C γ
      = ∑ j ∈ Finset.Icc 1 l, psiTilde m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) := by
-- BODY
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hlR : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
  have hlne : (l:ℝ) ≠ 0 := ne_of_gt hlR
  -- `Finset.Icc 1 n = Finset.Ioc 0 n` in `ℕ`
  have hIcc : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := by
    intro n; rw [← Finset.Icc_add_one_left_eq_Ioc]; norm_num
  -- shifting a block of `m` consecutive indices
  have shiftsum : ∀ (c : ℕ) (G : ℕ → ℝ),
      ∑ i ∈ Finset.Ioc c (c+m), G i = ∑ k ∈ Finset.Icc 1 m, G (c+k) := by
    intro c G
    rw [← Finset.Icc_add_one_left_eq_Ioc, ← Finset.map_add_left_Icc, Finset.sum_map]
    rfl
  -- the reindexing `i = (j-1)*m + k` as an identity of `ℕ`-indexed sums
  have reindex : ∀ (G : ℕ → ℝ) (l' : ℕ),
      ∑ i ∈ Finset.Icc 1 (m*l'), G i
        = ∑ j ∈ Finset.Icc 1 l', ∑ k ∈ Finset.Icc 1 m, G ((j-1)*m + k) := by
    intro G l'
    induction l' with
    | zero => simp
    | succ n ih =>
      rw [hIcc, Nat.mul_succ,
        ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (m*n)) (Nat.le_add_right (m*n) m),
        ← hIcc, ih, hIcc (n+1), Finset.sum_Ioc_succ_top (Nat.zero_le n), ← hIcc, shiftsum]
      simp [Nat.mul_comm]
  -- the common summand function
  set F : ℝ → ℝ := fun t => min (2 * C)
      (ε + 2 * C * Metric.infDist (γ.toFun t) (Q : Set E)) with hFdef
  -- Step A : unwinding the left-hand side
  have hA : psiTilde (m*l) Q ε C γ
      = C / (m:ℝ) * (∑ x ∈ Finset.Icc 1 (m*l), F ((x:ℝ)/(m:ℝ))) + 2 * C^2 * (l:ℝ) / (m:ℝ) := by
    have hsum : ∀ x ∈ Finset.Icc 1 (m*l),
        min (2*C)
          (ε + 2*C*Metric.infDist (γ.toFun ((x:ℝ)*(l:ℝ)/((m:ℝ)*(l:ℝ)))) (Q:Set E))
        = F ((x:ℝ)/(m:ℝ)) := by
      intro x _
      have e1 : (x:ℝ)*(l:ℝ)/((m:ℝ)*(l:ℝ)) = (x:ℝ)/(m:ℝ) := by field_simp
      rw [e1]
    unfold psiTilde
    push_cast
    rw [hlen, Finset.sum_congr rfl hsum]
    field_simp
    ring
  -- Step B : unwinding each right-hand summand
  have hB : ∀ j ∈ Finset.Icc 1 l, psiTilde m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ))
      = C / (m:ℝ) * (∑ k ∈ Finset.Icc 1 m, F (((j:ℝ) - 1) + (k:ℝ)/(m:ℝ))) + 2 * C^2 / (m:ℝ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hj1R : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj1
    have hj2R : (j:ℝ) ≤ (l:ℝ) := by exact_mod_cast hj2
    have ha : (0:ℝ) ≤ (j:ℝ) - 1 := by linarith
    have hab : (j:ℝ) - 1 ≤ (j:ℝ) := by linarith
    have hb : (j:ℝ) ≤ γ.len := by rw [hlen]; exact hj2R
    rw [CurveRestrictTotAgrees γ _ _ ha hab hb]
    set δ := curveRestrict γ ((j:ℝ)-1) (j:ℝ) ha hab hb with hδdef
    have hlen1 : δ.len = 1 := by
      show (j:ℝ) - ((j:ℝ) - 1) = 1
      ring
    have htf : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → δ.toFun u = γ.toFun (((j:ℝ)-1) + u) := by
      intro u hu0 hu1
      show γ.toFun (((j:ℝ)-1) + min ((j:ℝ) - ((j:ℝ)-1)) (max 0 u)) = _
      rw [max_eq_right hu0, min_eq_right (by linarith)]
    have hsum : ∀ k ∈ Finset.Icc 1 m,
        min (2*C)
          (ε + 2*C*Metric.infDist (δ.toFun ((k:ℝ)*(1:ℝ)/(m:ℝ))) (Q:Set E))
        = F (((j:ℝ) - 1) + (k:ℝ)/(m:ℝ)) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      obtain ⟨hk1, hk2⟩ := hk
      have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
      have hk2R : (k:ℝ) ≤ (m:ℝ) := by exact_mod_cast hk2
      have e1 : (k:ℝ)*(1:ℝ)/(m:ℝ) = (k:ℝ)/(m:ℝ) := by ring
      rw [e1, htf _ (by positivity) (by rw [div_le_one hmR]; exact hk2R)]
    unfold psiTilde
    rw [hlen1, Finset.sum_congr rfl hsum]
    ring
  -- Step C : matching the two sides
  rw [Finset.sum_congr rfl hB, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Nat.card_Icc, hA]
  have hre : ∑ x ∈ Finset.Icc 1 (m*l), F ((x:ℝ)/(m:ℝ))
      = ∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Icc 1 m, F (((j:ℝ) - 1) + (k:ℝ)/(m:ℝ)) := by
    rw [reindex (fun n => F ((n:ℝ)/(m:ℝ))) l]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine Finset.sum_congr rfl ?_
    intro k _
    congr 1
    have : (((j-1)*m + k : ℕ) : ℝ) = ((j:ℝ) - 1)*(m:ℝ) + (k:ℝ) := by
      push_cast [Nat.cast_sub hj.1]
      ring
    rw [this]
    field_simp
  rw [hre]
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  ring
