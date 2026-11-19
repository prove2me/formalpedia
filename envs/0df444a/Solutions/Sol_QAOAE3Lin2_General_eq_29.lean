-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:50:17.348614+00:00
-- url     : https://prove2.me/submissions/9b5f5626-4681-4847-b629-96021b1e3d51

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

open QAOAE3Lin2.General

private lemma spin_sq' {n : ℕ} (x : QAlgorithms.Qubits n) (q : Fin n) :
    spin x q * spin x q = 1 := by
  simp only [spin]
  cases x q <;> norm_num

private lemma avgZ_const'' {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_nonneg {n : ℕ} {f : QAlgorithms.Qubits n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ avgZ f := by
  simp only [avgZ]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => hf x)

private lemma avgZ_mono'' {n : ℕ} {f g : QAlgorithms.Qubits n → ℝ} (h : ∀ x, f x ≤ g x) :
    avgZ f ≤ avgZ g := by
  simp only [avgZ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma avgZ_split {n : ℕ} (f : QAlgorithms.Qubits (n + 1) → ℝ) :
    avgZ f = (1 / 2 : ℝ) * avgZ (fun x : QAlgorithms.Qubits n =>
      f (Fin.snoc x false) + f (Fin.snoc x true)) := by
  let e : QAlgorithms.Qubits (n + 1) ≃ QAlgorithms.Qubits n × Bool :=
    { toFun := fun x => (Fin.init x, x (Fin.last n))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := fun x => Fin.snoc_init_self x
      right_inv := fun p => by ext <;> simp [Fin.init, Fin.snoc] }
  have hsum : ∑ x : QAlgorithms.Qubits (n + 1), f x =
      ∑ x : QAlgorithms.Qubits n, (f (Fin.snoc x false) + f (Fin.snoc x true)) := by
    rw [Fintype.sum_equiv e _ (fun p => f (Fin.snoc p.1 p.2)) (fun x => by simp [e])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [add_comm]
  have hcard : (Fintype.card (QAlgorithms.Qubits (n + 1)) : ℝ) =
      2 * (Fintype.card (QAlgorithms.Qubits n) : ℝ) := by
    simp only [QAlgorithms.Qubits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_succ]
    push_cast
    ring
  simp only [avgZ, hsum, hcard]
  ring

private lemma poly_factor_id (p : ℕ) (hp : 3 ≤ p) (u : ℝ) :
    2 * ((p : ℝ) - 1) * (1 - u) * (1 + u ^ p) -
      (1 - u ^ (p - 1)) * ((1 + u) ^ 2 + ((p : ℝ) - 1) * (1 - u) ^ 2) =
    (1 - u) ^ 3 * ∑ j ∈ Finset.range (p - 1),
      (((p : ℝ) - 2) + 2 * (j : ℝ) * ((p : ℝ) - 2 - (j : ℝ))) * u ^ j := by
  let c : ℕ → ℝ := fun j => ((p : ℝ) - 2) + 2 * (j : ℝ) * ((p : ℝ) - 2 - (j : ℝ))
  have hc0 : c 0 = (p : ℝ) - 2 := by simp [c]
  have hcp : c (p - 2) = (p : ℝ) - 2 := by
    simp only [c]
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    ring
  -- Telescope (1 - u) * ∑_{j < p - 1} c j * u^j
  have hstep1 : (1 - u) * ∑ j ∈ Finset.range (p - 1), c j * u ^ j =
      c 0 - c (p - 2) * u ^ (p - 1) +
        ∑ j ∈ Finset.Ico 1 (p - 1), (c j - c (j - 1)) * u ^ j := by
    have h1 : (∑ j ∈ Finset.range (p - 1), c j * u ^ j) -
        ∑ j ∈ Finset.range (p - 1), c j * u ^ (j + 1) =
        c 0 - c (p - 2) * u ^ (p - 1) +
          ∑ j ∈ Finset.Ico 1 (p - 1), (c j - c (j - 1)) * u ^ j := by
      have hr1 : Finset.range (p - 1) = insert 0 (Finset.Ico 1 (p - 1)) := by
        ext j; simp; omega
      have hr2 : Finset.range (p - 1) = insert (p - 2) (Finset.range (p - 2)) := by
        rw [← Finset.range_add_one]
        congr 1; omega
      nth_rw 1 [hr1]
      rw [Finset.sum_insert (by simp)]
      nth_rw 1 [hr2]
      rw [Finset.sum_insert (by simp)]
      have hshift : ∑ j ∈ Finset.range (p - 2), c j * u ^ (j + 1) =
          ∑ j ∈ Finset.Ico 1 (p - 1), c (j - 1) * u ^ j := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        refine Finset.sum_congr (by congr 1) fun j _ => by ring
      rw [hshift]
      have hsub : p - 2 + 1 = p - 1 := by omega
      rw [hsub]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      simp only [pow_zero, mul_one]
      ring
    calc (1 - u) * ∑ j ∈ Finset.range (p - 1), c j * u ^ j
        = (∑ j ∈ Finset.range (p - 1), c j * u ^ j) -
            ∑ j ∈ Finset.range (p - 1), c j * u ^ (j + 1) := by
          rw [sub_mul, one_mul, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = _ := h1
  have hdiff : ∀ j ∈ Finset.Ico 1 (p - 1),
      c j - c (j - 1) = 2 * ((p : ℝ) - 1) - 4 * (j : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    simp only [c, Nat.cast_sub hj1, Nat.cast_one]
    ring
  have hstep2 : (1 - u) * ((p - 2 : ℝ) - (p - 2 : ℝ) * u ^ (p - 1) +
      ∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) =
      (p - 2 : ℝ) + ((p : ℝ) - 4) * u + ((p : ℝ) - 4) * u ^ (p - 1) +
        ((p : ℝ) - 2) * u ^ p - 4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j := by
    have hmul : (1 - u) * ∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j =
        (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) -
        (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ (j + 1)) := by
      rw [sub_mul, one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have hsum_eq : (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) -
        (∑ j ∈ Finset.Ico 1 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ (j + 1)) =
        (2 * ((p : ℝ) - 1) - 4) * u - (2 * ((p : ℝ) - 1) - 4 * ((p - 2 : ℕ) : ℝ)) * u ^ (p - 1) -
          4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j := by
      have hIco1 : Finset.Ico 1 (p - 1) = insert 1 (Finset.Ico 2 (p - 1)) := by
        ext j; simp; omega
      have hIco2 : Finset.Ico 1 (p - 1) = insert (p - 2) (Finset.Ico 1 (p - 2)) := by
        ext j; simp; omega
      nth_rw 1 [hIco1]
      rw [Finset.sum_insert (by simp)]
      nth_rw 1 [hIco2]
      rw [Finset.sum_insert (by simp)]
      have hsh : ∑ j ∈ Finset.Ico 1 (p - 2), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ (j + 1) =
          ∑ j ∈ Finset.Ico 2 (p - 1), (2 * ((p : ℝ) - 1) - 4 * ((j : ℝ) - 1)) * u ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        have hrg : p - 2 - 1 = p - 1 - 2 := by omega
        rw [hrg]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        rw [show 1 + j + 1 = 2 + j by omega]
        ring
      rw [hsh]
      have hsub : p - 2 + 1 = p - 1 := by omega
      rw [hsub]
      have hsub_sum : (∑ j ∈ Finset.Ico 2 (p - 1), (2 * ((p : ℝ) - 1) - 4 * (j : ℝ)) * u ^ j) -
          (∑ j ∈ Finset.Ico 2 (p - 1), (2 * ((p : ℝ) - 1) - 4 * ((j : ℝ) - 1)) * u ^ j) =
          -4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp only [Nat.cast_one, pow_one]
      linear_combination hsub_sum
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hp_split : u ^ p = u * u ^ (p - 1) := by
      rw [← pow_succ', show p - 1 + 1 = p by omega]
    rw [mul_add, hmul, hsum_eq, hcast, hp_split]
    ring
  have hgeom : (1 - u) * (4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j) =
      4 * u ^ 2 - 4 * u ^ (p - 1) := by
    by_cases hp3 : p = 3
    · subst hp3; simp
    · have hp4 : 4 ≤ p := by omega
      have htel : (1 - u) * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j = u ^ 2 - u ^ (p - 1) := by
        rw [sub_mul, one_mul, Finset.mul_sum]
        have hI1 : Finset.Ico 2 (p - 1) = insert 2 (Finset.Ico 3 (p - 1)) := by
          ext j; simp; omega
        have hI2 : Finset.Ico 2 (p - 1) = insert (p - 2) (Finset.Ico 2 (p - 2)) := by
          ext j; simp; omega
        nth_rw 1 [hI1]
        rw [Finset.sum_insert (by simp)]
        nth_rw 1 [hI2]
        rw [Finset.sum_insert (by simp)]
        have hsh : ∑ j ∈ Finset.Ico 2 (p - 2), u * u ^ j = ∑ j ∈ Finset.Ico 3 (p - 1), u ^ j := by
          rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
          have hrg : p - 2 - 2 = p - 1 - 3 := by omega
          rw [hrg]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show 3 + j = (2 + j) + 1 by omega, pow_succ']
        rw [hsh, ← pow_succ', show p - 2 + 1 = p - 1 by omega]
        ring
      rw [← mul_assoc, mul_comm (1 - u) 4, mul_assoc, htel]
      ring
  have hstep3 : (1 - u) * ((p - 2 : ℝ) + ((p : ℝ) - 4) * u + ((p : ℝ) - 4) * u ^ (p - 1) +
      ((p : ℝ) - 2) * u ^ p - 4 * ∑ j ∈ Finset.Ico 2 (p - 1), u ^ j) =
      2 * ((p : ℝ) - 1) * (1 - u) * (1 + u ^ p) -
        (1 - u ^ (p - 1)) * ((1 + u) ^ 2 + ((p : ℝ) - 1) * (1 - u) ^ 2) := by
    have hp_split : u ^ p = u * u ^ (p - 1) := by
      rw [← pow_succ', show p - 1 + 1 = p by omega]
    rw [mul_sub, hgeom, hp_split]
    ring
  rw [show (1 - u) ^ 3 * ∑ j ∈ Finset.range (p - 1), c j * u ^ j =
      (1 - u) * ((1 - u) * ((1 - u) * ∑ j ∈ Finset.range (p - 1), c j * u ^ j)) by ring]
  rw [hstep1, Finset.sum_congr rfl fun j hj => by rw [hdiff j hj], hc0, hcp, hstep2, hstep3]

private lemma two_point_bonami_unit (p : ℕ) (hp : 2 ≤ p) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 + t) ^ p + (1 - t) ^ p) / 2 ≤ (1 + ((p : ℝ) - 1) * t ^ 2) ^ ((p : ℝ) / 2) := by
  by_cases hp2 : p = 2
  · subst hp2
    norm_num
    linarith
  have hp3 : 3 ≤ p := by omega
  let f : ℝ → ℝ := fun s =>
    Real.log (((1 + s) ^ p + (1 - s) ^ p) / 2) -
      ((p : ℝ) / 2) * Real.log (1 + ((p : ℝ) - 1) * s ^ 2)
  have hpos_num : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < ((1 + s) ^ p + (1 - s) ^ p) / 2 := by
    intro s hs
    have h1 : 0 < (1 + s) ^ p := pow_pos (by linarith [hs.1]) p
    have h2 : 0 ≤ (1 - s) ^ p := pow_nonneg (by linarith [hs.2]) p
    linarith
  have hpos_den : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + ((p : ℝ) - 1) * s ^ 2 := by
    intro s _
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have hf_cont : ContinuousOn f (Set.Icc 0 1) := by
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.log ?_ (fun s hs => (hpos_num s hs).ne')
      exact (((continuous_const.add continuous_id).pow p).add
        ((continuous_const.sub continuous_id).pow p)).div_const 2 |>.continuousOn
    · refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.log ?_ (fun s hs => (hpos_den s hs).ne')
      exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).continuousOn
  let f' : ℝ → ℝ := fun s =>
    ((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) /
      (((1 + s) ^ p + (1 - s) ^ p) / 2) -
      ((p : ℝ) / 2) * (2 * ((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2))
  have hf_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' s) s ∧ f' s ≤ 0 := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := hs.2
    have hnum_pos : 0 < ((1 + s) ^ p + (1 - s) ^ p) / 2 := hpos_num s ⟨hs0.le, hs1.le⟩
    have hden_pos : 0 < 1 + ((p : ℝ) - 1) * s ^ 2 := hpos_den s ⟨hs0.le, hs1.le⟩
    have hd1 : HasDerivAt (fun x => ((1 + x) ^ p + (1 - x) ^ p) / 2)
        ((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) s := by
      have ha : HasDerivAt (fun x => (1 + x) ^ p) ((p : ℝ) * (1 + s) ^ (p - 1) * 1) s :=
        ((hasDerivAt_id s).const_add 1).pow p
      have hb : HasDerivAt (fun x => (1 - x) ^ p) ((p : ℝ) * (1 - s) ^ (p - 1) * (-1)) s :=
        ((hasDerivAt_id s).const_sub 1).pow p
      exact ((ha.add hb).div_const 2).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun x => 1 + ((p : ℝ) - 1) * x ^ 2)
        (2 * ((p : ℝ) - 1) * s) s := by
      have hx2 : HasDerivAt (fun x => x ^ 2) (2 * s) s :=
        ((hasDerivAt_id s).pow 2).congr_deriv (by simp)
      exact ((hasDerivAt_const s 1).add (hx2.const_mul ((p : ℝ) - 1))).congr_deriv (by ring)
    have hd_f : HasDerivAt f
        (((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) /
          (((1 + s) ^ p + (1 - s) ^ p) / 2) -
          ((p : ℝ) / 2) * (2 * ((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2))) s :=
      (hd1.log hnum_pos.ne').sub ((hd2.log hden_pos.ne').const_mul ((p : ℝ) / 2))
    refine ⟨hd_f, ?_⟩
    rw [sub_nonpos]
    have hsimp1 : ((p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / 2) /
        (((1 + s) ^ p + (1 - s) ^ p) / 2) =
        (p : ℝ) * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) / ((1 + s) ^ p + (1 - s) ^ p) := by
      field_simp
    have hsimp2 : ((p : ℝ) / 2) * (2 * ((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2)) =
        (p : ℝ) * (((p : ℝ) - 1) * s / (1 + ((p : ℝ) - 1) * s ^ 2)) := by
      ring
    have hsum_pos : 0 < (1 + s) ^ p + (1 - s) ^ p := by linarith
    rw [hsimp1, hsimp2, ← mul_div_assoc, div_le_div_iff₀ hsum_pos hden_pos,
      mul_assoc, mul_assoc, mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < p)]
    -- Reduce to u = (1 - s) / (1 + s) ∈ (0, 1)
    let u : ℝ := (1 - s) / (1 + s)
    have h1s_pos : 0 < 1 + s := by linarith
    have hu_pos : 0 < u := div_pos (by linarith) h1s_pos
    have hu_lt1 : u < 1 := by rw [div_lt_one h1s_pos]; linarith
    have hs_eq : s = (1 - u) / (1 + u) := by
      simp only [u]; field_simp [h1s_pos.ne']; ring
    have h1s_eq : 1 + s = 2 / (1 + u) := by
      simp only [u]; field_simp [h1s_pos.ne']; ring
    have h1ms_eq : 1 - s = 2 * u / (1 + u) := by
      simp only [u]; field_simp [h1s_pos.ne']; ring
    have hpoly := poly_factor_id p hp3 u
    have hpoly_nonneg : 0 ≤ (1 - u) ^ 3 * ∑ j ∈ Finset.range (p - 1),
        (((p : ℝ) - 2) + 2 * (j : ℝ) * ((p : ℝ) - 2 - (j : ℝ))) * u ^ j := by
      refine mul_nonneg (pow_nonneg (by linarith) 3) (Finset.sum_nonneg fun j hj => ?_)
      have hjp : j < p - 1 := Finset.mem_range.mp hj
      have hj_le : (j : ℝ) ≤ (p : ℝ) - 2 := by
        have hsub : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
        rw [← hsub]
        exact_mod_cast (by omega : j ≤ p - 2)
      have hp2_ge : (0 : ℝ) ≤ (p : ℝ) - 2 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp
        linarith
      refine mul_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) j]) (pow_nonneg hu_pos.le j)
    rw [← hpoly] at hpoly_nonneg
    have h1u_pos : 0 < 1 + u := by linarith
    have hscale : ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1)) * (1 + ((p : ℝ) - 1) * s ^ 2) =
        (2 ^ (p - 1) / (1 + u) ^ (p + 1)) *
          ((1 - u ^ (p - 1)) * ((1 + u) ^ 2 + ((p : ℝ) - 1) * (1 - u) ^ 2)) := by
      rw [h1s_eq, h1ms_eq, hs_eq]
      rw [div_pow, div_pow, mul_pow]
      have hpow1 : (1 + u) ^ (p - 1) * (1 + u) ^ 2 = (1 + u) ^ (p + 1) := by
        rw [← pow_add]; congr 1; omega
      field_simp [h1u_pos.ne']
      rw [← hpow1]
      ring
    have hscale2 : ((p : ℝ) - 1) * s * ((1 + s) ^ p + (1 - s) ^ p) =
        (2 ^ (p - 1) / (1 + u) ^ (p + 1)) * (2 * ((p : ℝ) - 1) * (1 - u) * (1 + u ^ p)) := by
      rw [h1s_eq, h1ms_eq, hs_eq, div_pow, div_pow, mul_pow]
      have h2p : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ', show p - 1 + 1 = p by omega]
      have h1up : (1 + u) * (1 + u) ^ p = (1 + u) ^ (p + 1) := by
        rw [← pow_succ']
      field_simp [h1u_pos.ne']
      rw [h2p, ← h1up]
      ring
    rw [hscale, hscale2]
    refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hf_anti : AntitoneOn f (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc 0 1) hf_cont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      exact (hf_deriv s hs).1.hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hf_deriv s hs).2
  have hf_le : f t ≤ f 0 := hf_anti (Set.left_mem_Icc.mpr zero_le_one) ⟨ht0, ht1⟩ ht0
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hf_le
  dsimp only [f] at hf_le
  have hlog_le : Real.log (((1 + t) ^ p + (1 - t) ^ p) / 2) ≤
      Real.log ((1 + ((p : ℝ) - 1) * t ^ 2) ^ ((p : ℝ) / 2)) := by
    rw [Real.log_rpow (hpos_den t ⟨ht0, ht1⟩)]
    linarith
  exact (Real.log_le_log_iff (hpos_num t ⟨ht0, ht1⟩)
    (Real.rpow_pos_of_pos (hpos_den t ⟨ht0, ht1⟩) _)).mp hlog_le

private lemma two_point_bonami (p : ℕ) (hp : 2 ≤ p) (A B : ℝ) :
    (|A + B| ^ p + |A - B| ^ p) / 2 ≤ (A ^ 2 + ((p : ℝ) - 1) * B ^ 2) ^ ((p : ℝ) / 2) := by
  wlog hAB : |B| ≤ |A|
  · push Not at hAB
    have h1 : (|B + A| ^ p + |B - A| ^ p) / 2 ≤
        (B ^ 2 + ((p : ℝ) - 1) * A ^ 2) ^ ((p : ℝ) / 2) := this p hp B A hAB.le
    have heq : |B + A| ^ p + |B - A| ^ p = |A + B| ^ p + |A - B| ^ p := by
      rw [add_comm B A, abs_sub_comm B A]
    rw [heq] at h1
    have hp1_nn : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    refine h1.trans (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
    have hsq : A ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg A, abs_nonneg B, sq_abs A, sq_abs B]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  wlog hA : 0 ≤ A
  · push Not at hA
    have h1 := this p hp (-A) (-B) (by simpa using hAB) (by linarith)
    have hneg : |(-A) + (-B)| ^ p + |(-A) - (-B)| ^ p = |A + B| ^ p + |A - B| ^ p := by
      rw [show (-A) + (-B) = -(A + B) by ring, show (-A) - (-B) = -(A - B) by ring,
        abs_neg, abs_neg]
    rw [hneg] at h1
    simpa only [neg_sq] using h1
  wlog hB : 0 ≤ B
  · push Not at hB
    have h1 := this p hp A (-B) (by simpa using hAB) hA (by linarith)
    have hneg : |A + (-B)| ^ p + |A - (-B)| ^ p = |A + B| ^ p + |A - B| ^ p := by
      rw [show A + (-B) = A - B by ring, show A - (-B) = A + B by ring, add_comm]
    rw [hneg] at h1
    simpa only [neg_sq] using h1
  by_cases hA0 : A = 0
  · subst hA0
    have hB0 : B = 0 := by
      rw [abs_zero] at hAB
      exact le_antisymm (abs_le.mp hAB).2 hB
    subst hB0
    simp [show p ≠ 0 by omega, show (p : ℝ) / 2 ≠ 0 by positivity]
  have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  let t := B / A
  have ht0 : 0 ≤ t := div_nonneg hB hA_pos.le
  have ht1 : t ≤ 1 := by
    rw [div_le_one hA_pos]
    simpa [abs_of_nonneg hA, abs_of_nonneg hB] using hAB
  have hu := two_point_bonami_unit p hp t ht0 ht1
  have hL : (|A + B| ^ p + |A - B| ^ p) / 2 = A ^ p * (((1 + t) ^ p + (1 - t) ^ p) / 2) := by
    have h1 : |A + B| = A * (1 + t) := by
      rw [abs_of_nonneg (by linarith)]
      simp only [t]; field_simp [hA_pos.ne']
    have h2 : |A - B| = A * (1 - t) := by
      have hBA : B ≤ A := by simpa [abs_of_nonneg hA, abs_of_nonneg hB] using hAB
      rw [abs_of_nonneg (by linarith)]
      simp only [t]; field_simp [hA_pos.ne']
    rw [h1, h2, mul_pow, mul_pow]
    ring
  have hR : (A ^ 2 + ((p : ℝ) - 1) * B ^ 2) ^ ((p : ℝ) / 2) =
      A ^ p * (1 + ((p : ℝ) - 1) * t ^ 2) ^ ((p : ℝ) / 2) := by
    have hB_eq : B = A * t := by simp only [t]; field_simp [hA_pos.ne']
    rw [hB_eq, mul_pow]
    have hfac : A ^ 2 + ((p : ℝ) - 1) * (A ^ 2 * t ^ 2) =
        A ^ 2 * (1 + ((p : ℝ) - 1) * t ^ 2) := by ring
    have hp1_nn : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    rw [hfac, Real.mul_rpow (sq_nonneg A) (add_nonneg zero_le_one (mul_nonneg hp1_nn (sq_nonneg t)))]
    congr 1
    rw [← Real.rpow_natCast A p, ← Real.rpow_two A, ← Real.rpow_mul hA_pos.le]
    congr 1
    ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left hu (pow_nonneg hA_pos.le p)

private lemma bonami_avgZ_step {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (A B : QAlgorithms.Qubits n → ℝ) :
    (avgZ (fun x => (|A x + B x| ^ p + |A x - B x| ^ p) / 2)) ^ (2 / (p : ℝ)) ≤
      (avgZ (fun x => |A x| ^ p)) ^ (2 / (p : ℝ)) +
        ((p : ℝ) - 1) * (avgZ (fun x => |B x| ^ p)) ^ (2 / (p : ℝ)) := by
  have hp_pos : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hq : 1 ≤ (p : ℝ) / 2 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hpt : ∀ x, (|A x + B x| ^ p + |A x - B x| ^ p) / 2 ≤
      (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2) :=
    fun x => two_point_bonami p hp (A x) (B x)
  have hmono : avgZ (fun x => (|A x + B x| ^ p + |A x - B x| ^ p) / 2) ≤
      avgZ (fun x => (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2)) :=
    avgZ_mono'' hpt
  have hrpow1 : (avgZ (fun x => (|A x + B x| ^ p + |A x - B x| ^ p) / 2)) ^ (2 / (p : ℝ)) ≤
      (avgZ (fun x => (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2))) ^ (2 / (p : ℝ)) :=
    Real.rpow_le_rpow (avgZ_nonneg fun x => by positivity) hmono (by positivity)
  refine hrpow1.trans ?_
  let N : ℝ := Fintype.card (QAlgorithms.Qubits n)
  have hN_pos : 0 < N := by
    simp only [N, QAlgorithms.Qubits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    positivity
  have hmink := Real.Lp_add_le (Finset.univ : Finset (QAlgorithms.Qubits n))
    (fun x => A x ^ 2) (fun x => ((p : ℝ) - 1) * B x ^ 2) hq
  have h1q : 1 / ((p : ℝ) / 2) = 2 / (p : ℝ) := by ring
  rw [h1q] at hmink
  have hA_abs : ∀ x, |A x ^ 2| ^ ((p : ℝ) / 2) = |A x| ^ p := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (A x), ← Real.rpow_natCast (|A x|) p,
      ← Real.rpow_natCast (|A x|) 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; ring
  have hB_abs : ∀ x, |((p : ℝ) - 1) * B x ^ 2| ^ ((p : ℝ) / 2) =
      ((p : ℝ) - 1) ^ ((p : ℝ) / 2) * |B x| ^ p := by
    intro x
    rw [abs_mul, abs_of_nonneg hp1, abs_of_nonneg (sq_nonneg _),
      Real.mul_rpow hp1 (sq_nonneg _), ← sq_abs (B x), ← Real.rpow_natCast (|B x|) p,
      ← Real.rpow_natCast (|B x|) 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 2; ring
  have hAB_abs : ∀ x, |A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2| ^ ((p : ℝ) / 2) =
      (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2) := by
    intro x
    rw [abs_of_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hp1 (sq_nonneg _)))]
  simp_rw [hAB_abs, hA_abs, hB_abs] at hmink
  have havg_eq : ∀ f : QAlgorithms.Qubits n → ℝ, (∀ x, 0 ≤ f x) →
      (avgZ f) ^ (2 / (p : ℝ)) = N ^ (-(2 / (p : ℝ))) * (∑ x, f x) ^ (2 / (p : ℝ)) := by
    intro f hf
    simp only [avgZ]
    rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun x _ => hf x)]
    congr 1
    rw [← Real.rpow_neg_one N, ← Real.rpow_mul hN_pos.le]
    congr 1; ring
  rw [havg_eq _ (fun x => Real.rpow_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hp1 (sq_nonneg _))) _),
    havg_eq _ (fun x => pow_nonneg (abs_nonneg _) _),
    havg_eq _ (fun x => pow_nonneg (abs_nonneg _) _)]
  have hB_factor : (∑ x, ((p : ℝ) - 1) ^ ((p : ℝ) / 2) * |B x| ^ p) ^ (2 / (p : ℝ)) =
      ((p : ℝ) - 1) * (∑ x, |B x| ^ p) ^ (2 / (p : ℝ)) := by
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hp1 _) (Finset.sum_nonneg fun x _ => by positivity),
      ← Real.rpow_mul hp1, show ((p : ℝ) / 2) * (2 / (p : ℝ)) = 1 by field_simp [hp_pos.ne'],
      Real.rpow_one]
  rw [hB_factor] at hmink
  calc N ^ (-(2 / (p : ℝ))) * (∑ x, (A x ^ 2 + ((p : ℝ) - 1) * B x ^ 2) ^ ((p : ℝ) / 2)) ^ (2 / (p : ℝ))
      ≤ N ^ (-(2 / (p : ℝ))) * ((∑ x, |A x| ^ p) ^ (2 / (p : ℝ)) +
          ((p : ℝ) - 1) * (∑ x, |B x| ^ p) ^ (2 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hmink (by positivity)
    _ = N ^ (-(2 / (p : ℝ))) * (∑ x, |A x| ^ p) ^ (2 / (p : ℝ)) +
          ((p : ℝ) - 1) * (N ^ (-(2 / (p : ℝ))) * (∑ x, |B x| ^ p) ^ (2 / (p : ℝ))) := by
        ring

private lemma bonami_deg1 (n k : ℕ) (b₀ : ℝ) (b₁ : Fin n → ℝ) :
    (avgZ (fun x : QAlgorithms.Qubits n => |b₀ + ∑ v, b₁ v * spin x v| ^ (k + 2))) ^
        (2 / ((k + 2 : ℕ) : ℝ)) ≤
      ((k : ℝ) + 1) * avgZ (fun x : QAlgorithms.Qubits n => (b₀ + ∑ v, b₁ v * spin x v) ^ 2) := by
  induction n generalizing b₀ with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, avgZ_const'']
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    rw [← sq_abs b₀, ← Real.rpow_natCast (|b₀|) (k + 2), ← Real.rpow_mul (abs_nonneg _)]
    have hexp : ((k + 2 : ℕ) : ℝ) * (2 / ((k + 2 : ℕ) : ℝ)) = 2 := by
      have : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hexp, Real.rpow_two]
    nlinarith [sq_nonneg b₀]
  | succ n ih =>
    let A : QAlgorithms.Qubits n → ℝ := fun x => b₀ + ∑ v : Fin n, b₁ v.castSucc * spin x v
    let B : QAlgorithms.Qubits n → ℝ := fun _ => b₁ (Fin.last n)
    have hsplit_g : ∀ (x : QAlgorithms.Qubits n) (b : Bool),
        (b₀ + ∑ v : Fin (n + 1), b₁ v * spin (Fin.snoc x b) v) =
        A x + (if b = false then B x else -B x) := by
      intro x b
      rw [Fin.sum_univ_castSucc]
      have hcast : ∀ v : Fin n, spin (Fin.snoc x b) v.castSucc = spin x v := by
        intro v; simp [spin, Fin.snoc]
      have hlast : spin (Fin.snoc x b) (Fin.last n) = if b = false then 1 else -1 := by
        simp [spin, Fin.snoc]
        cases b <;> simp
      simp_rw [hcast, hlast]
      dsimp only [A, B]
      cases b <;> simp <;> ring
    have havg_p : avgZ (fun x : QAlgorithms.Qubits (n + 1) =>
        |b₀ + ∑ v, b₁ v * spin x v| ^ (k + 2)) =
        avgZ (fun x : QAlgorithms.Qubits n => (|A x + B x| ^ (k + 2) + |A x - B x| ^ (k + 2)) / 2) := by
      rw [avgZ_split]
      simp_rw [hsplit_g]
      simp only [↓reduceIte, Bool.true_eq_false, ← sub_eq_add_neg]
      simp only [avgZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have havg_2 : avgZ (fun x : QAlgorithms.Qubits (n + 1) =>
        (b₀ + ∑ v, b₁ v * spin x v) ^ 2) =
        avgZ (fun x : QAlgorithms.Qubits n => A x ^ 2) + b₁ (Fin.last n) ^ 2 := by
      rw [avgZ_split]
      simp_rw [hsplit_g]
      have hsq : ∀ x : QAlgorithms.Qubits n,
          (A x + B x) ^ 2 + (A x + -B x) ^ 2 = 2 * (A x ^ 2 + b₁ (Fin.last n) ^ 2) := by
        intro x; dsimp only [B]; ring
      simp only [↓reduceIte, Bool.true_eq_false]
      simp_rw [hsq]
      have hre : avgZ (fun x : QAlgorithms.Qubits n => 2 * (A x ^ 2 + b₁ (Fin.last n) ^ 2)) =
          2 * (avgZ (fun x => A x ^ 2) + b₁ (Fin.last n) ^ 2) := by
        simp only [avgZ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
        have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        field_simp
      rw [hre]
      ring
    rw [havg_p, havg_2]
    have hstep := bonami_avgZ_step (k + 2) (by omega) A B
    have ihA := ih b₀ (fun v => b₁ v.castSucc)
    have hB_eq : (avgZ (fun x : QAlgorithms.Qubits n => |B x| ^ (k + 2))) ^ (2 / ((k + 2 : ℕ) : ℝ)) =
        b₁ (Fin.last n) ^ 2 := by
      simp only [B, avgZ_const'']
      rw [← Real.rpow_natCast (|b₁ (Fin.last n)|) (k + 2), ← Real.rpow_mul (abs_nonneg _)]
      have hexp : ((k + 2 : ℕ) : ℝ) * (2 / ((k + 2 : ℕ) : ℝ)) = 2 := by
        have : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [hexp, Real.rpow_two, sq_abs]
    have hk_eq : ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 := by push_cast; ring
    rw [hk_eq] at hstep
    rw [hB_eq] at hstep
    nlinarith [ihA]

theorem solution (n k : ℕ) (a₀ : ℝ) (a₁ : Fin n → ℝ) (a₂ : Fin n → Fin n → ℝ) :
    let c : QAlgorithms.Qubits n → ℝ := fun x =>
      a₀ + ∑ v, a₁ v * spin x v +
        ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)
    avgZ (fun x => |c x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (avgZ (fun x => c x ^ 2)) ^ (k + 2) := by
  intro c
  have hmain : ∀ (m : ℕ) (a₀ : ℝ) (a₁ : Fin m → ℝ) (a₂ : Fin m → Fin m → ℝ),
      (avgZ (fun x : QAlgorithms.Qubits m =>
        |a₀ + ∑ v, a₁ v * spin x v +
          ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)| ^ (k + 2))) ^
          (2 / ((k + 2 : ℕ) : ℝ)) ≤
        ((k : ℝ) + 1) ^ 2 * avgZ (fun x : QAlgorithms.Qubits m =>
          (a₀ + ∑ v, a₁ v * spin x v +
            ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)) ^ 2) := by
    intro m
    induction m with
    | zero =>
      intro a₀ a₁ a₂
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, avgZ_const'']
      rw [← Real.rpow_natCast (|a₀|) (k + 2), ← Real.rpow_mul (abs_nonneg _)]
      have hexp : ((k + 2 : ℕ) : ℝ) * (2 / ((k + 2 : ℕ) : ℝ)) = 2 := by
        have : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [hexp, Real.rpow_two, sq_abs]
      have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      nlinarith [sq_nonneg a₀]
    | succ m ih =>
      intro a₀ a₁ a₂
      let A : QAlgorithms.Qubits m → ℝ := fun x =>
        a₀ + ∑ v : Fin m, a₁ v.castSucc * spin x v +
          ∑ u : Fin m, ∑ v : Fin m,
            (if u < v then a₂ u.castSucc v.castSucc * spin x u * spin x v else 0)
      let B : QAlgorithms.Qubits m → ℝ := fun x =>
        a₁ (Fin.last m) + ∑ u : Fin m, a₂ u.castSucc (Fin.last m) * spin x u
      have hsplit_c : ∀ (x : QAlgorithms.Qubits m) (b : Bool),
          (a₀ + ∑ v : Fin (m + 1), a₁ v * spin (Fin.snoc x b) v +
            ∑ u : Fin (m + 1), ∑ v : Fin (m + 1),
              (if u < v then a₂ u v * spin (Fin.snoc x b) u * spin (Fin.snoc x b) v else 0)) =
          A x + (if b = false then B x else -B x) := by
        intro x b
        have hcast : ∀ v : Fin m, spin (Fin.snoc x b) v.castSucc = spin x v := by
          intro v; simp [spin, Fin.snoc]
        have hlast : spin (Fin.snoc x b) (Fin.last m) = if b = false then 1 else -1 := by
          simp [spin, Fin.snoc]
          cases b <;> simp
        rw [Fin.sum_univ_castSucc]
        have hdouble : (∑ u : Fin (m + 1), ∑ v : Fin (m + 1),
            (if u < v then a₂ u v * spin (Fin.snoc x b) u * spin (Fin.snoc x b) v else 0)) =
            (∑ u : Fin m, ∑ v : Fin m,
              (if u < v then a₂ u.castSucc v.castSucc * spin x u * spin x v else 0)) +
            (∑ u : Fin m, a₂ u.castSucc (Fin.last m) * spin x u) * (if b = false then 1 else -1) := by
          rw [Fin.sum_univ_castSucc]
          have hlast_u : (∑ v : Fin (m + 1),
              (if Fin.last m < v then a₂ (Fin.last m) v * spin (Fin.snoc x b) (Fin.last m) *
                spin (Fin.snoc x b) v else 0)) = 0 := by
            refine Finset.sum_eq_zero fun v _ => ?_
            have hv : ¬ Fin.last m < v := not_lt.mpr (Fin.le_last v)
            simp [hv]
          rw [hlast_u, add_zero]
          have hinner : ∀ u : Fin m,
              (∑ v : Fin (m + 1),
                (if u.castSucc < v then a₂ u.castSucc v * spin (Fin.snoc x b) u.castSucc *
                  spin (Fin.snoc x b) v else 0)) =
              (∑ v : Fin m,
                (if u < v then a₂ u.castSucc v.castSucc * spin x u * spin x v else 0)) +
              a₂ u.castSucc (Fin.last m) * spin x u * (if b = false then 1 else -1) := by
            intro u
            rw [Fin.sum_univ_castSucc]
            congr 1
            · refine Finset.sum_congr rfl fun v _ => ?_
              have hlt : (u.castSucc < v.castSucc) ↔ u < v := Iff.rfl
              simp [hlt, hcast]
            · have hlt : u.castSucc < Fin.last m := Fin.castSucc_lt_last u
              simp [hlt, hcast, hlast]
          simp_rw [hinner, Finset.sum_add_distrib, Finset.sum_mul]
        rw [hdouble]
        simp_rw [hcast, hlast]
        dsimp only [A, B]
        cases b <;> simp <;> ring
      have havg_p : avgZ (fun x : QAlgorithms.Qubits (m + 1) =>
          |a₀ + ∑ v, a₁ v * spin x v +
            ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)| ^ (k + 2)) =
          avgZ (fun x : QAlgorithms.Qubits m => (|A x + B x| ^ (k + 2) + |A x - B x| ^ (k + 2)) / 2) := by
        rw [avgZ_split]
        simp_rw [hsplit_c]
        simp only [↓reduceIte, Bool.true_eq_false, ← sub_eq_add_neg]
        simp only [avgZ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      have havg_2 : avgZ (fun x : QAlgorithms.Qubits (m + 1) =>
          (a₀ + ∑ v, a₁ v * spin x v +
            ∑ u, ∑ v, (if u < v then a₂ u v * spin x u * spin x v else 0)) ^ 2) =
          avgZ (fun x : QAlgorithms.Qubits m => A x ^ 2) +
            avgZ (fun x : QAlgorithms.Qubits m => B x ^ 2) := by
        rw [avgZ_split]
        simp_rw [hsplit_c]
        have hsq : ∀ x : QAlgorithms.Qubits m,
            (A x + B x) ^ 2 + (A x + -B x) ^ 2 = 2 * (A x ^ 2 + B x ^ 2) := by
          intro x; ring
        simp only [↓reduceIte, Bool.true_eq_false]
        simp_rw [hsq]
        have hre : avgZ (fun x : QAlgorithms.Qubits m => 2 * (A x ^ 2 + B x ^ 2)) =
            2 * (avgZ (fun x => A x ^ 2) + avgZ (fun x => B x ^ 2)) := by
          simp only [avgZ, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        rw [hre]
        ring
      rw [havg_p, havg_2]
      have hstep := bonami_avgZ_step (k + 2) (by omega) A B
      have hk_eq : ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 := by push_cast; ring
      rw [hk_eq] at hstep
      have ihA := ih a₀ (fun v => a₁ v.castSucc) (fun u v => a₂ u.castSucc v.castSucc)
      have ihB := bonami_deg1 m k (a₁ (Fin.last m)) (fun u => a₂ u.castSucc (Fin.last m))
      have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      nlinarith
  have h0 := hmain n a₀ a₁ a₂
  have hk2_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg (avgZ_nonneg fun x => by positivity) _)
    h0 (by positivity : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) / 2)
  rw [← Real.rpow_mul (avgZ_nonneg fun x => by positivity)] at hrpow
  have hexp : (2 / ((k + 2 : ℕ) : ℝ)) * (((k + 2 : ℕ) : ℝ) / 2) = 1 := by
    field_simp [hk2_pos.ne']
  rw [hexp, Real.rpow_one] at hrpow
  refine hrpow.trans_eq ?_
  have hk1_nn : (0 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have havg2_nn : 0 ≤ avgZ (fun x => c x ^ 2) := avgZ_nonneg fun x => sq_nonneg _
  rw [Real.mul_rpow (sq_nonneg _) havg2_nn]
  have hpow1 : (((k : ℝ) + 1) ^ 2) ^ (((k + 2 : ℕ) : ℝ) / 2) = ((k : ℝ) + 1) ^ (k + 2) := by
    rw [← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_mul hk1_nn,
      show ((2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) / 2) = ((k + 2 : ℕ) : ℝ) by norm_num; ring,
      Real.rpow_natCast]
  have hpow2 : (avgZ (fun x => c x ^ 2)) ^ (((k + 2 : ℕ) : ℝ) / 2) =
      Real.sqrt (avgZ (fun x => c x ^ 2)) ^ (k + 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ (k + 2), ← Real.rpow_mul havg2_nn]
    congr 1; ring
  rw [hpow1, hpow2]
