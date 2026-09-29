-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_magnon_density
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T20:31:06.82875+00:00
-- url     : https://prove2.me/submissions/b7e9f51e-4a61-4178-a150-505e82cc6ade

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

private lemma sum_first_rows (m L : ℕ) (h : m ≤ L) (v : ℝ) :
    (∑ r : Fin L, if (r : ℕ) < m then v else 0) = (m : ℝ) * v := by
  induction L with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    simp
  | succ L ih =>
    by_cases hm : m ≤ L
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih hm]
      simp [Nat.not_lt.mpr hm]
    · have hm' : m = L + 1 := by omega
      subst m
      have heq : (fun r : Fin (L + 1) => if (r : ℕ) < L + 1 then v else 0) =
          (fun _ : Fin (L + 1) => v) := by
        funext r
        exact if_pos r.isLt
      rw [heq]
      simp

theorem solution (b : ℝ) (hb : 0 < b) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ L > N,
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ∃ s ∈ switchMagnonSpectrum L b, |x - s| ≤ δ := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (2 * b))
  have hb2 : 0 < 2 * b := by positivity
  have hmprod : 1 < (m : ℝ) * (2 * b) := (div_lt_iff₀ hb2).mp hm
  let A : ℝ := (m : ℝ) * (2 * b)
  have hA1 : 1 < A := hmprod
  have hA : 0 < A := by linarith
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (A * Real.pi / δ)
  refine ⟨max m N, ?_⟩
  intro L hL x hx
  have hmL : m ≤ L := by have := le_max_left m N; omega
  have hNL : N < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hLp : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLp
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLr
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := ne_of_gt hπ
  have herror : A * Real.pi / (L : ℝ) < δ := by
    have hlarge : A * Real.pi / δ < (L : ℝ) :=
      lt_trans hN (by exact_mod_cast hNL)
    apply (div_lt_iff₀ hLr).mpr
    have := (div_lt_iff₀ hδ).mp hlarge
    nlinarith
  have hxdiv0 : 0 ≤ x / A := div_nonneg hx.1 hA.le
  have hxdiv1 : x / A ≤ 1 := (div_le_one hA).mpr (by linarith [hx.2])
  let θ := Real.arccos (1 - x / A)
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hcos : Real.cos θ = 1 - x / A :=
    Real.cos_arccos (by linarith) (by linarith)
  let q : ℝ := θ * (L : ℝ) / Real.pi
  have hq : 0 ≤ q := div_nonneg (mul_nonneg hθ0 hLr.le) hπ.le
  have hqL : q < (L : ℝ) := by
    apply (div_lt_iff₀ hπ).mpr
    nlinarith
  let k : ℕ := ⌊q⌋₊
  have hkL : k < L := (Nat.floor_lt hq).mpr hqL
  let kf : Fin L := ⟨k, hkL⟩
  let t : ℝ := Real.pi * (k : ℝ) / (L : ℝ)
  have hstep : 0 ≤ Real.pi / (L : ℝ) := (div_pos hπ hLr).le
  have hang : |θ - t| ≤ Real.pi / (L : ℝ) := by
    have hid : θ - t = (q - (k : ℝ)) * (Real.pi / (L : ℝ)) := by
      dsimp [t, q]
      field_simp
      <;> ring
    rw [hid, abs_mul, abs_of_nonneg hstep]
    exact (mul_le_mul_of_nonneg_right (Nat.abs_sub_floor_le hq) hstep).trans_eq
      (one_mul _)
  let ks : Fin L → Fin L := fun r => if (r : ℕ) < m then kf else ⟨0, hLp⟩
  let v : ℝ := 2 * b * (1 - Real.cos t)
  have hsum : (∑ r : Fin L,
      2 * b * (1 - Real.cos (Real.pi * (ks r : ℝ) / (L : ℝ)))) = (m : ℝ) * v := by
    calc
      _ = ∑ r : Fin L, if (r : ℕ) < m then v else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [ks]
        split_ifs <;> simp [v, t, kf]
      _ = _ := sum_first_rows m L hmL v
  refine ⟨(m : ℝ) * v, ⟨ks, hsum.symm⟩, ?_⟩
  have hxcos : x = A * (1 - Real.cos θ) := by
    rw [hcos]
    field_simp
    <;> ring
  have hid : x - (m : ℝ) * v = A * (Real.cos t - Real.cos θ) := by
    rw [hxcos]
    dsimp [A, v]
    ring
  rw [hid, abs_mul, abs_of_pos hA]
  have hcosdist : |Real.cos t - Real.cos θ| ≤ Real.pi / (L : ℝ) :=
    (Real.abs_cos_sub_cos_le t θ).trans (by simpa only [abs_sub_comm] using hang)
  calc
    _ ≤ A * (Real.pi / (L : ℝ)) := mul_le_mul_of_nonneg_left hcosdist hA.le
    _ = A * Real.pi / (L : ℝ) := by ring
    _ ≤ δ := herror.le
