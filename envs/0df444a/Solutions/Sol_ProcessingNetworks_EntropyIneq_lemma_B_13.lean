-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.lemma_B_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:58:03.489756+00:00
-- url     : https://prove2.me/submissions/e447be40-84cb-408e-88a5-14dd4e3fd8df

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions
import Definitions.Def_ProcessingNetworks_EntropyIneq_outflow
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Theorems.Thm_ProcessingNetworks_EntropyIneq_lemma_B_10
import Theorems.Thm_SinkhornHall_lemma_1_1

open Matrix ProcessingNetworks.EntropyIneq

private lemma log_le_sub_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have h := Real.log_le_log hx (by linarith [Real.add_one_le_exp (x - 1)] : x ≤ Real.exp (x - 1))
  rwa [Real.log_exp] at h

theorem solution {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ)
    (hB4 : SectionB4Assumptions lam P) (hsub : ∀ i, ∑ j, P i j ≤ 1)
    (d : Fin I → ℝ) (hd : ∀ i, 0 < d i) :
    let α := traffic lam P
    let a := lam + Pᵀ *ᵥ d
    (1 / 2 : ℝ) * (1 / (∑ i, d i + ∑ i, lam i)) *
        (∑ i, lam i * |1 - d i / α i| +
          ∑ i, α i * |d i / α i - (∑ j, P i j * (d j / α j) + outflow P i)|) ^ 2 ≤
      ∑ i, (d i - a i) * Real.log (d i / α i) := by
  intro α a
  have : Nonempty (Fin I) := Fin.pos_iff_nonempty.mp hB4.pos_I
  have hα_pos : ∀ i, 0 < α i := hB4.traffic_pos
  have hr_pos : ∀ i, 0 < d i / α i := fun i => div_pos (hd i) (hα_pos i)
  have hout_nonneg : ∀ i, 0 ≤ outflow P i := by
    intro i
    unfold outflow
    linarith [hsub i]
  let W : Fin I → ℝ := fun i => ∑ j, P i j * (d j / α j) + outflow P i
  have hW_pos : ∀ i, 0 < W i := by
    intro i
    have hW_nonneg : 0 ≤ W i :=
      add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hB4.P_nonneg i j) (hr_pos j).le)
        (hout_nonneg i)
    rcases eq_or_lt_of_le hW_nonneg with h0 | hpos
    · exfalso
      have hout0 : outflow P i = 0 := by
        have hsum_nn : 0 ≤ ∑ j, P i j * (d j / α j) :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hB4.P_nonneg i j) (hr_pos j).le
        dsimp [W] at h0
        linarith [hout_nonneg i]
      have hPsum1 : ∑ j, P i j = 1 := by
        unfold outflow at hout0
        linarith
      have hsum0 : ∑ j, P i j * (d j / α j) = 0 := by
        dsimp [W] at h0
        linarith
      have hP0 : ∀ j, P i j = 0 := by
        intro j
        have hj0 : P i j * (d j / α j) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
            mul_nonneg (hB4.P_nonneg i k) (hr_pos k).le).mp hsum0 j (Finset.mem_univ j)
        rcases mul_eq_zero.mp hj0 with hpz | hrz
        · exact hpz
        · exact absurd hrz (hr_pos j).ne'
      simp [hP0] at hPsum1
    · exact hpos
  let u : Fin I ⊕ Fin I → ℝ := Sum.elim lam d
  let v : Fin I ⊕ Fin I → ℝ :=
    Sum.elim (fun i => d i * (lam i / α i)) (fun i => α i * W i)
  have hu_nn : ∀ x, 0 ≤ u x := by
    rintro (i | i)
    · exact hB4.lam_nonneg i
    · exact (hd i).le
  have hv_nn : ∀ x, 0 ≤ v x := by
    rintro (i | i)
    · exact mul_nonneg (hd i).le (div_nonneg (hB4.lam_nonneg i) (hα_pos i).le)
    · exact mul_nonneg (hα_pos i).le (hW_pos i).le
  have hu_sum : ∑ x, u x = ∑ i, d i + ∑ i, lam i := by
    rw [Fintype.sum_sum_type]
    simp only [u, Sum.elim_inl, Sum.elim_inr]
    ring
  have hv_sum : ∑ x, v x = ∑ i, d i + ∑ i, lam i := by
    rw [Fintype.sum_sum_type]
    simp only [v, Sum.elim_inl, Sum.elim_inr]
    have hb10 := lemma_B_10 lam P hB4 d
    dsimp [W, α]
    linarith
  have huv_sum : ∑ x, u x = ∑ x, v x := hu_sum.trans hv_sum.symm
  have hpinsker := SinkhornHall.lemma_1_1 u v hu_nn hv_nn huv_sum
  have hno_top : ¬ ∃ x, v x = 0 ∧ 0 < u x := by
    rintro ⟨i | i, hv0, hu0⟩
    · simp only [v, u, Sum.elim_inl] at hv0 hu0
      have hpos : 0 < d i * (lam i / α i) := mul_pos (hd i) (div_pos hu0 (hα_pos i))
      linarith
    · simp only [v, Sum.elim_inr] at hv0
      have hpos : 0 < α i * W i := mul_pos (hα_pos i) (hW_pos i)
      linarith
  rw [SinkhornHall.klDiv, if_neg hno_top, EReal.coe_le_coe_iff] at hpinsker
  have hl1 : ∑ x, |u x - v x| =
      ∑ i, lam i * |1 - d i / α i| +
        ∑ i, α i * |d i / α i - (∑ j, P i j * (d j / α j) + outflow P i)| := by
    rw [Fintype.sum_sum_type]
    simp only [u, v, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have heq : lam i - d i * (lam i / α i) = lam i * (1 - d i / α i) := by ring
      rw [heq, abs_mul, abs_of_nonneg (hB4.lam_nonneg i)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hαne : α i ≠ 0 := (hα_pos i).ne'
      have heq : d i - α i * W i = α i * (d i / α i - W i) := by
        field_simp [hαne]
      rw [heq, abs_mul, abs_of_pos (hα_pos i)]
  have hkl_inl : ∀ i : Fin I,
      u (Sum.inl i) * Real.log (u (Sum.inl i) / v (Sum.inl i)) =
        -lam i * Real.log (d i / α i) := by
    intro i
    simp only [u, v, Sum.elim_inl]
    by_cases hli : lam i = 0
    · simp [hli]
    · have hαne : α i ≠ 0 := (hα_pos i).ne'
      have hdne : d i ≠ 0 := (hd i).ne'
      have hdiv : lam i / (d i * (lam i / α i)) = (d i / α i)⁻¹ := by
        field_simp [hli, hαne, hdne]
      rw [hdiv, Real.log_inv]
      ring
  have hjensen : ∀ i : Fin I,
      ∑ j, P i j * Real.log (d j / α j) ≤ Real.log (W i) := by
    intro i
    have hWne : W i ≠ 0 := (hW_pos i).ne'
    have hpt : ∀ j : Fin I, P i j * (Real.log (d j / α j) - Real.log (W i)) ≤
        P i j * ((d j / α j) / W i - 1) := by
      intro j
      rw [← Real.log_div (hr_pos j).ne' hWne]
      exact mul_le_mul_of_nonneg_left (log_le_sub_one (div_pos (hr_pos j) (hW_pos i)))
        (hB4.P_nonneg i j)
    have hpt0 : outflow P i * (-Real.log (W i)) ≤ outflow P i * (1 / W i - 1) := by
      have hlog1 : -Real.log (W i) = Real.log (1 / W i) := by
        rw [one_div, Real.log_inv]
      rw [hlog1]
      exact mul_le_mul_of_nonneg_left (log_le_sub_one (div_pos zero_lt_one (hW_pos i)))
        (hout_nonneg i)
    have hsum_pt := add_le_add (Finset.sum_le_sum (s := Finset.univ) fun j _ => hpt j) hpt0
    have hLHS : (∑ j, P i j * (Real.log (d j / α j) - Real.log (W i))) +
        outflow P i * (-Real.log (W i)) =
        (∑ j, P i j * Real.log (d j / α j)) - Real.log (W i) := by
      have hw1 : (∑ j, P i j) + outflow P i = 1 := by unfold outflow; ring
      have hsub_sum : ∑ j, P i j * (Real.log (d j / α j) - Real.log (W i)) =
          (∑ j, P i j * Real.log (d j / α j)) - (∑ j, P i j) * Real.log (W i) := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hsub_sum]
      calc (∑ j, P i j * Real.log (d j / α j)) - (∑ j, P i j) * Real.log (W i) +
            outflow P i * (-Real.log (W i))
          = (∑ j, P i j * Real.log (d j / α j)) -
            ((∑ j, P i j) + outflow P i) * Real.log (W i) := by ring
        _ = (∑ j, P i j * Real.log (d j / α j)) - Real.log (W i) := by rw [hw1, one_mul]
    have hRHS : (∑ j, P i j * ((d j / α j) / W i - 1)) + outflow P i * (1 / W i - 1) = 0 := by
      have hw1 : (∑ j, P i j) + outflow P i = 1 := by unfold outflow; ring
      have h1 : ∑ j, P i j * ((d j / α j) / W i - 1) =
          (∑ j, P i j * (d j / α j)) / W i - ∑ j, P i j := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl fun j _ => (mul_div_assoc (P i j) _ (W i)).symm
      have h2 : outflow P i * (1 / W i - 1) = outflow P i / W i - outflow P i := by ring
      rw [h1, h2]
      calc (∑ j, P i j * (d j / α j)) / W i - ∑ j, P i j + (outflow P i / W i - outflow P i)
          = ((∑ j, P i j * (d j / α j)) + outflow P i) / W i - ((∑ j, P i j) + outflow P i) := by
              rw [add_div]; ring
        _ = W i / W i - 1 := by rw [hw1]
        _ = 0 := by rw [div_self hWne, sub_self]
    linarith
  have hkl_inr : ∀ i : Fin I,
      u (Sum.inr i) * Real.log (u (Sum.inr i) / v (Sum.inr i)) ≤
        d i * Real.log (d i / α i) - ∑ j, d i * P i j * Real.log (d j / α j) := by
    intro i
    simp only [u, v, Sum.elim_inr]
    have hαne : α i ≠ 0 := (hα_pos i).ne'
    have hdiv : d i / (α i * W i) = (d i / α i) / W i := by
      field_simp [hαne]
    rw [hdiv, Real.log_div (hr_pos i).ne' (hW_pos i).ne', mul_sub]
    have hmul := mul_le_mul_of_nonneg_left (hjensen i) (hd i).le
    rw [Finset.mul_sum] at hmul
    have hsum_eq : ∑ j, d i * (P i j * Real.log (d j / α j)) =
        ∑ j, d i * P i j * Real.log (d j / α j) :=
      Finset.sum_congr rfl fun j _ => (mul_assoc (d i) (P i j) _).symm
    linarith
  have hkl_bound : ∑ x, u x * Real.log (u x / v x) ≤
      ∑ i, (d i - a i) * Real.log (d i / α i) := by
    rw [Fintype.sum_sum_type]
    have hL : ∑ i, u (Sum.inl i) * Real.log (u (Sum.inl i) / v (Sum.inl i)) =
        ∑ i, -lam i * Real.log (d i / α i) :=
      Finset.sum_congr rfl fun i _ => hkl_inl i
    have hR : ∑ i, u (Sum.inr i) * Real.log (u (Sum.inr i) / v (Sum.inr i)) ≤
        ∑ i, (d i * Real.log (d i / α i) - ∑ j, d i * P i j * Real.log (d j / α j)) :=
      Finset.sum_le_sum fun i _ => hkl_inr i
    have hident : ∑ i, -lam i * Real.log (d i / α i) +
        ∑ i, (d i * Real.log (d i / α i) - ∑ j, d i * P i j * Real.log (d j / α j)) =
        ∑ i, (d i - a i) * Real.log (d i / α i) := by
      rw [Finset.sum_sub_distrib]
      have hswap : ∑ i, ∑ j, d i * P i j * Real.log (d j / α j) =
          ∑ i, ((Pᵀ *ᵥ d) i) * Real.log (d i / α i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hswap]
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [a]
      ring
    linarith
  rw [hl1, hu_sum] at hpinsker
  have hden_pos : 0 < ∑ i, d i + ∑ i, lam i := by
    have hd_sum_pos : 0 < ∑ i, d i :=
      Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
    have hlam_sum_nn : 0 ≤ ∑ i, lam i :=
      Finset.sum_nonneg fun i _ => hB4.lam_nonneg i
    linarith
  have hrew : (1 / 2 : ℝ) * (1 / (∑ i, d i + ∑ i, lam i)) *
      (∑ i, lam i * |1 - d i / α i| +
        ∑ i, α i * |d i / α i - (∑ j, P i j * (d j / α j) + outflow P i)|) ^ 2 =
      (∑ i, lam i * |1 - d i / α i| +
        ∑ i, α i * |d i / α i - (∑ j, P i j * (d j / α j) + outflow P i)|) ^ 2 /
        (2 * (∑ i, d i + ∑ i, lam i)) := by
    have hden_ne : ∑ i, d i + ∑ i, lam i ≠ 0 := hden_pos.ne'
    field_simp [hden_ne]
  rw [hrew]
  exact hpinsker.trans hkl_bound
