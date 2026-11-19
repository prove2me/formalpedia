-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:56:27.875541+00:00
-- url     : https://prove2.me/submissions/ef215eb5-7ea4-40f4-8923-d0b0c31ad217

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

open QAOAE3Lin2.General



private lemma iteratedDeriv_sin_eq (m : ℕ) :
    iteratedDeriv m Real.sin = fun x =>
      if m % 4 = 0 then Real.sin x
      else if m % 4 = 1 then Real.cos x
      else if m % 4 = 2 then -Real.sin x
      else -Real.cos x := by
  induction m with
  | zero =>
    ext x
    simp [iteratedDeriv_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    have h0 : deriv (fun y => Real.sin y) x = Real.cos x := by simp
    have h1 : deriv (fun y => Real.cos y) x = -Real.sin x := by simp
    have h2 : deriv (fun y => -Real.sin y) x = -Real.cos x := by simp
    have h3 : deriv (fun y => -Real.cos y) x = Real.sin x := by simp
    rcases Nat.mod_lt m (by norm_num : 0 < 4) with _
    have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm with h | h | h | h
    · have hm1 : (m + 1) % 4 = 1 := by omega
      simp [h, hm1, h0]
    · have hm1 : (m + 1) % 4 = 2 := by omega
      simp [h, hm1, h1]
    · have hm1 : (m + 1) % 4 = 3 := by omega
      simp [h, hm1, h2]
    · have hm1 : (m + 1) % 4 = 0 := by omega
      simp [h, hm1, h3]

private lemma norm_iteratedDeriv_sin_le (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m Real.sin x‖ ≤ 1 := by
  rw [iteratedDeriv_sin_eq m, Real.norm_eq_abs]
  split_ifs
  · exact Real.abs_sin_le_one x
  · exact Real.abs_cos_le_one x
  · rw [abs_neg]; exact Real.abs_sin_le_one x
  · rw [abs_neg]; exact Real.abs_cos_le_one x

private lemma iteratedDeriv_sin_zero (j : ℕ) :
    iteratedDeriv j Real.sin 0 = if Odd j then (-1 : ℝ) ^ ((j - 1) / 2) else 0 := by
  rw [iteratedDeriv_sin_eq j]
  have hj : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases hj with h | h | h | h
  · have hne : ¬ Odd j := by rw [Nat.not_odd_iff_even]; exact Nat.even_iff.mpr (by omega)
    simp [h, hne]
  · have ho : Odd j := Nat.odd_iff.mpr (by omega)
    have hev : Even ((j - 1) / 2) := Nat.even_iff.mpr (by omega)
    simp [h, ho, hev.neg_one_pow]
  · have hne : ¬ Odd j := by rw [Nat.not_odd_iff_even]; exact Nat.even_iff.mpr (by omega)
    simp [h, hne]
  · have ho : Odd j := Nat.odd_iff.mpr (by omega)
    have hodd : Odd ((j - 1) / 2) := Nat.odd_iff.mpr (by omega)
    simp [h, ho, hodd.neg_one_pow]

private lemma sin_taylor_bound (k : ℕ) (hk : Odd k) (t : ℝ) :
    |Real.sin t - ∑ j ∈ (Finset.range (k + 1)).filter Odd,
      t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)| ≤
      |t| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
  by_cases ht : t = 0
  · subst ht
    have hsum0 : (∑ j ∈ (Finset.range (k + 1)).filter Odd,
        (0 : ℝ) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_odd : Odd j := (Finset.mem_filter.mp hj).2
      have hj_pos : j ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hj_odd
      simp [zero_pow hj_pos]
    simp [hsum0]
  have hne : (0 : ℝ) ≠ t := Ne.symm ht
  have hcont : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) Real.sin (Set.uIcc 0 t) :=
    Real.contDiff_sin.contDiffOn
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin (k + 1) Real.sin (Set.uIcc 0 t))
      (Set.uIoo 0 t) := by
    have hud : UniqueDiffOn ℝ (Set.uIcc 0 t) :=
      uniqueDiffOn_Icc (by rcases lt_or_gt_of_ne ht with h | h <;> simp [h])
    have heq : Set.EqOn (iteratedDerivWithin (k + 1) Real.sin (Set.uIcc 0 t))
        (iteratedDeriv (k + 1) Real.sin) (Set.uIoo 0 t) := by
      intro y hy
      exact iteratedDerivWithin_eq_iteratedDeriv hud (Real.contDiff_sin.contDiffAt)
        (Set.Ioo_subset_Icc_self hy)
    exact (((Real.contDiff_sin (n := ⊤)).differentiable_iteratedDeriv (k + 1)
      (by simp)).differentiableOn).congr heq
  -- Wait: differentiable_iteratedDeriv needs ENat order, let's check!
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange hne hcont hdiff
  have hud : UniqueDiffOn ℝ (Set.uIcc 0 t) :=
    uniqueDiffOn_Icc (by rcases lt_or_gt_of_ne ht with h | h <;> simp [h])
  have hwithin : ∀ j : ℕ, iteratedDerivWithin j Real.sin (Set.uIcc 0 t) 0 =
      iteratedDeriv j Real.sin 0 := fun j =>
    iteratedDerivWithin_eq_iteratedDeriv hud Real.contDiff_sin.contDiffAt
      Set.left_mem_uIcc
  have hwithin_x' : iteratedDerivWithin (k + 2) Real.sin (Set.uIcc 0 t) x' =
      iteratedDeriv (k + 2) Real.sin x' :=
    iteratedDerivWithin_eq_iteratedDeriv hud Real.contDiff_sin.contDiffAt
      (Set.Ioo_subset_Icc_self hx')
  have htay : taylorWithinEval Real.sin (k + 1) (Set.uIcc 0 t) 0 t =
      ∑ j ∈ (Finset.range (k + 1)).filter Odd,
        t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) := by
    simp [taylorWithinEval, taylorWithin, taylorCoeffWithin, hwithin, iteratedDeriv_sin_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun j _ => by ring
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    have hk_even : ¬ Odd (k + 1) := by
      rw [← Nat.not_even_iff_odd]
      simpa [Nat.even_add_one] using hk
    constructor
    · rintro ⟨hj1, hj2⟩
      have hj_ne : j ≠ k + 1 := by rintro rfl; exact hk_even hj2
      exact ⟨by omega, hj2⟩
    · rintro ⟨hj1, hj2⟩
      exact ⟨by omega, hj2⟩
  rw [← htay, hrem, hwithin_x', abs_div, abs_mul, sub_zero, abs_pow, Nat.abs_cast]
  have hbound : |iteratedDeriv (k + 2) Real.sin x'| ≤ 1 := by
    simpa [Real.norm_eq_abs] using norm_iteratedDeriv_sin_le (k + 2) x'
  have hfac_pos : (0 : ℝ) < ((k + 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg (abs_nonneg t) _) hbound)
    hfac_pos.le

private lemma abs_avgZ_le {n : ℕ} (f : QAlgorithms.Qubits n → ℝ) :
    |avgZ f| ≤ avgZ (fun x => |f x|) := by
  simp only [avgZ, abs_mul, abs_inv, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

private lemma avgZ_const' {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_add' {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x + g x) = avgZ f + avgZ g := by
  simp only [avgZ, Finset.sum_add_distrib, mul_add]

private lemma avgZ_smul' {n : ℕ} (c : ℝ) (f : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => c * f x) = c * avgZ f := by
  simp only [avgZ, ← Finset.mul_sum]
  ring

private lemma avgZ_sum' {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, avgZ (f j) := by
  simp only [avgZ, Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]

private lemma avgZ_sub' {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x - g x) = avgZ f - avgZ g := by
  simp only [avgZ, Finset.sum_sub_distrib, mul_sub]

private lemma avgZ_mono' {n : ℕ} {f g : QAlgorithms.Qubits n → ℝ} (h : ∀ x, f x ≤ g x) :
    avgZ f ≤ avgZ g := by
  simp only [avgZ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma eq_28_helper {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (k : ℕ) (hk : Odd k) (γ : ℝ) :
    |Rk tri rhs i k γ| ≤ (1 / 8) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ) *
      avgZ (fun x =>
        let d := sgn rhs i
        let c₁ := cPoly tri rhs i 0 x
        let c₂ := cPoly tri rhs i 1 x
        let c₃ := cPoly tri rhs i 2 x
        |d + c₁ + c₂ + c₃| ^ (k + 2) + |d + c₁ - c₂ - c₃| ^ (k + 2) +
          |d - c₁ + c₂ - c₃| ^ (k + 2) + |d - c₁ - c₂ + c₃| ^ (k + 2)) := by
  let S : ℝ → ℝ := fun t => ∑ j ∈ (Finset.range (k + 1)).filter Odd,
    t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)
  let u₁ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i + cPoly tri rhs i 0 x + cPoly tri rhs i 1 x + cPoly tri rhs i 2 x
  let u₂ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i + cPoly tri rhs i 0 x - cPoly tri rhs i 1 x - cPoly tri rhs i 2 x
  let u₃ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i - cPoly tri rhs i 0 x + cPoly tri rhs i 1 x - cPoly tri rhs i 2 x
  let u₄ : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i - cPoly tri rhs i 0 x - cPoly tri rhs i 1 x + cPoly tri rhs i 2 x
  have hlin : (1 / 2 : ℝ) * sgn rhs i ^ 2 * γ =
      (1 / 8 : ℝ) * sgn rhs i * avgZ (fun x => γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) := by
    have hu : ∀ x, γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x = 4 * sgn rhs i * γ := by
      intro x; simp only [u₁, u₂, u₃, u₄]; ring
    simp_rw [hu, avgZ_const']
    ring
  have hPk : (1 / 2 : ℝ) * sgn rhs i ^ 2 * γ + Pk tri rhs i k γ =
      (1 / 8 : ℝ) * sgn rhs i *
        avgZ (fun x => S (γ * u₁ x) + S (γ * u₂ x) + S (γ * u₃ x) + S (γ * u₄ x)) := by
    rw [hlin, Pk]
    have hsplit : (Finset.range (k + 1)).filter Odd =
        insert 1 ((Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      have hk1 : 1 < k + 1 := by
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (fun h => Nat.not_odd_zero (h ▸ hk))
        omega
      constructor
      · rintro ⟨hj1, hj2⟩
        by_cases hj_eq : j = 1
        · exact Or.inl hj_eq
        · right
          have hj_ne0 : j ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hj2
          have hj_ne2 : j ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hj2
          exact ⟨hj1, by omega, hj2⟩
      · rintro (rfl | ⟨hj1, _, hj3⟩)
        · exact ⟨hk1, by decide⟩
        · exact ⟨hj1, hj3⟩
    have h1_not : (1 : ℕ) ∉ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j) := by
      simp
    have hS_split : ∀ t : ℝ, S t = t + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
        t ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) := by
      intro t
      dsimp only [S]
      rw [hsplit, Finset.sum_insert h1_not]
      simp
    have havg_S : avgZ (fun x => S (γ * u₁ x) + S (γ * u₂ x) + S (γ * u₃ x) + S (γ * u₄ x)) =
        avgZ (fun x => γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) +
        ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
          γ ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) *
            avgZ (fun x => u₁ x ^ j + u₂ x ^ j + u₃ x ^ j + u₄ x ^ j) := by
      simp_rw [hS_split]
      have hre : (fun x =>
          (γ * u₁ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₁ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
          (γ * u₂ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₂ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
          (γ * u₃ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₃ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
          (γ * u₄ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            (γ * u₄ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ))) =
          fun x => (γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) +
            ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) *
                (u₁ x ^ j + u₂ x ^ j + u₃ x ^ j + u₄ x ^ j) := by
        ext x
        have hrearr :
            (γ * u₁ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₁ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
            (γ * u₂ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₂ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
            (γ * u₃ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₃ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
            (γ * u₄ x + ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₄ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) =
            (γ * u₁ x + γ * u₂ x + γ * u₃ x + γ * u₄ x) +
            ((∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₁ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
             (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₂ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
             (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₃ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ)) +
             (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
              (γ * u₄ x) ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ))) := by ring
        rw [hrearr, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, mul_pow, mul_pow, mul_pow]; ring
      rw [hre, avgZ_add', avgZ_sum']
      simp_rw [avgZ_smul']
    rw [havg_S, mul_add]
  have hRk : Rk tri rhs i k γ = (1 / 8 : ℝ) * sgn rhs i *
      avgZ (fun x =>
        (Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
        (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
        (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
        (Real.sin (γ * u₄ x) - S (γ * u₄ x))) := by
    rw [Rk, sub_sub, hPk, clauseSin]
    have hre : (fun x =>
        (Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
        (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
        (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
        (Real.sin (γ * u₄ x) - S (γ * u₄ x))) =
        fun x => (Real.sin (γ * u₁ x) + Real.sin (γ * u₂ x) + Real.sin (γ * u₃ x) +
          Real.sin (γ * u₄ x)) - (S (γ * u₁ x) + S (γ * u₂ x) + S (γ * u₃ x) + S (γ * u₄ x)) := by
      ext x; ring
    rw [hre, avgZ_sub']
    dsimp only [u₁, u₂, u₃, u₄]
    ring
  rw [hRk, abs_mul, abs_mul]
  have hsgn_abs : |sgn rhs i| = 1 := by
    simp only [sgn]; cases rhs i <;> norm_num
  rw [hsgn_abs, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  refine (mul_le_mul_of_nonneg_left (abs_avgZ_le _) (by norm_num)).trans ?_
  have hpt : ∀ x,
      |(Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
       (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
       (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
       (Real.sin (γ * u₄ x) - S (γ * u₄ x))| ≤
      (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
        (|u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by
    intro x
    have b1 : |Real.sin (γ * u₁ x) - S (γ * u₁ x)| ≤
        |γ| ^ (k + 2) * |u₁ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₁ x) - S (γ * u₁ x)|
          ≤ |γ * u₁ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₁ x)
        _ = |γ| ^ (k + 2) * |u₁ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    have b2 : |Real.sin (γ * u₂ x) - S (γ * u₂ x)| ≤
        |γ| ^ (k + 2) * |u₂ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₂ x) - S (γ * u₂ x)|
          ≤ |γ * u₂ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₂ x)
        _ = |γ| ^ (k + 2) * |u₂ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    have b3 : |Real.sin (γ * u₃ x) - S (γ * u₃ x)| ≤
        |γ| ^ (k + 2) * |u₃ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₃ x) - S (γ * u₃ x)|
          ≤ |γ * u₃ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₃ x)
        _ = |γ| ^ (k + 2) * |u₃ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    have b4 : |Real.sin (γ * u₄ x) - S (γ * u₄ x)| ≤
        |γ| ^ (k + 2) * |u₄ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
      calc |Real.sin (γ * u₄ x) - S (γ * u₄ x)|
          ≤ |γ * u₄ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := sin_taylor_bound k hk (γ * u₄ x)
        _ = |γ| ^ (k + 2) * |u₄ x| ^ (k + 2) / ((k + 2).factorial : ℝ) := by rw [abs_mul, mul_pow]
    calc |(Real.sin (γ * u₁ x) - S (γ * u₁ x)) +
           (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
           (Real.sin (γ * u₃ x) - S (γ * u₃ x)) +
           (Real.sin (γ * u₄ x) - S (γ * u₄ x))|
        ≤ |Real.sin (γ * u₁ x) - S (γ * u₁ x)| + |Real.sin (γ * u₂ x) - S (γ * u₂ x)| +
          |Real.sin (γ * u₃ x) - S (γ * u₃ x)| + |Real.sin (γ * u₄ x) - S (γ * u₄ x)| := by
          linarith [abs_add_le (Real.sin (γ * u₁ x) - S (γ * u₁ x) +
            (Real.sin (γ * u₂ x) - S (γ * u₂ x)) + (Real.sin (γ * u₃ x) - S (γ * u₃ x)))
            (Real.sin (γ * u₄ x) - S (γ * u₄ x)),
            abs_add_le (Real.sin (γ * u₁ x) - S (γ * u₁ x) +
            (Real.sin (γ * u₂ x) - S (γ * u₂ x))) (Real.sin (γ * u₃ x) - S (γ * u₃ x)),
            abs_add_le (Real.sin (γ * u₁ x) - S (γ * u₁ x)) (Real.sin (γ * u₂ x) - S (γ * u₂ x))]
      _ ≤ |γ| ^ (k + 2) * |u₁ x| ^ (k + 2) / ↑(k + 2).factorial +
          |γ| ^ (k + 2) * |u₂ x| ^ (k + 2) / ↑(k + 2).factorial +
          |γ| ^ (k + 2) * |u₃ x| ^ (k + 2) / ↑(k + 2).factorial +
          |γ| ^ (k + 2) * |u₄ x| ^ (k + 2) / ↑(k + 2).factorial := by linarith
      _ = (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
            (|u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by ring
  have hmono := avgZ_mono' hpt
  have hsmul : avgZ (fun x => (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
      (|u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2))) =
      (|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
        avgZ (fun x => |u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by
    simp only [avgZ, ← Finset.mul_sum]
    ring
  rw [hsmul] at hmono
  calc (1 / 8 : ℝ) * avgZ (fun x =>
        |(Real.sin (γ * u₁ x) - S (γ * u₁ x)) + (Real.sin (γ * u₂ x) - S (γ * u₂ x)) +
         (Real.sin (γ * u₃ x) - S (γ * u₃ x)) + (Real.sin (γ * u₄ x) - S (γ * u₄ x))|)
      ≤ (1 / 8 : ℝ) * ((|γ| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
          avgZ (fun x => |u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2))) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = (1 / 8) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ) *
          avgZ (fun x => |u₁ x| ^ (k + 2) + |u₂ x| ^ (k + 2) + |u₃ x| ^ (k + 2) + |u₄ x| ^ (k + 2)) := by
        ring



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

private lemma eq_29_helper (n k : ℕ) (a₀ : ℝ) (a₁ : Fin n → ℝ) (a₂ : Fin n → Fin n → ℝ) :
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



private lemma spin_sq {n : ℕ} (x : QAlgorithms.Qubits n) (q : Fin n) : spin x q * spin x q = 1 := by
  simp only [spin]
  cases x q <;> norm_num

private lemma avgZ_const {n : ℕ} (c : ℝ) : avgZ (fun _ : QAlgorithms.Qubits n => c) = c := by
  simp only [avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

private lemma avgZ_add {n : ℕ} (f g : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => f x + g x) = avgZ f + avgZ g := by
  simp only [avgZ, Finset.sum_add_distrib, mul_add]

private lemma avgZ_smul {n : ℕ} (c : ℝ) (f : QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => c * f x) = c * avgZ f := by
  simp only [avgZ, ← Finset.mul_sum]
  ring

private lemma avgZ_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → QAlgorithms.Qubits n → ℝ) :
    avgZ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, avgZ (f j) := by
  simp only [avgZ, Finset.sum_comm (s := Finset.univ) (t := s), Finset.mul_sum]

private lemma prod_spin_symmDiff {n : ℕ} (A B : Finset (Fin n)) (x : QAlgorithms.Qubits n) :
    (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q) = ∏ q ∈ symmDiff A B, spin x q := by
  have hA : A = (A \ B) ∪ (A ∩ B) := by ext q; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hB : B = (B \ A) ∪ (A ∩ B) := by ext q; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hdA : Disjoint (A \ B) (A ∩ B) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
  have hdB : Disjoint (B \ A) (A ∩ B) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1
  have hAB : symmDiff A B = (A \ B) ∪ (B \ A) := by
    ext q; simp [Finset.mem_symmDiff, Finset.mem_sdiff]
  have hdAB : Disjoint (A \ B) (B \ A) := Finset.disjoint_left.mpr fun q h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  have hAB_prod : (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q) =
      (∏ q ∈ (A \ B) ∪ (A ∩ B), spin x q) * (∏ q ∈ (B \ A) ∪ (A ∩ B), spin x q) := by
    rw [← hA, ← hB]
  rw [hAB_prod, Finset.prod_union hdA, Finset.prod_union hdB]
  have hsq : (∏ q ∈ A ∩ B, spin x q) * (∏ q ∈ A ∩ B, spin x q) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun q _ => spin_sq x q
  calc ((∏ q ∈ A \ B, spin x q) * ∏ q ∈ A ∩ B, spin x q) *
        ((∏ q ∈ B \ A, spin x q) * ∏ q ∈ A ∩ B, spin x q)
      = (∏ q ∈ A \ B, spin x q) * (∏ q ∈ B \ A, spin x q) *
          ((∏ q ∈ A ∩ B, spin x q) * ∏ q ∈ A ∩ B, spin x q) := by ring
    _ = (∏ q ∈ A \ B, spin x q) * (∏ q ∈ B \ A, spin x q) := by rw [hsq, mul_one]
    _ = ∏ q ∈ symmDiff A B, spin x q := by rw [hAB, Finset.prod_union hdAB]

private lemma avgZ_prod_spin {n : ℕ} (T : Finset (Fin n)) :
    avgZ (fun x => ∏ q ∈ T, spin x q) = if T = ∅ then 1 else 0 := by
  by_cases hT : T = ∅
  · subst hT
    simp only [Finset.prod_empty, ↓reduceIte]
    exact avgZ_const 1
  · simp only [if_neg hT]
    obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    let flip : QAlgorithms.Qubits n → QAlgorithms.Qubits n := fun x q =>
      if q = q₀ then !(x q₀) else x q
    have hflip_inv : Function.Involutive flip := by
      intro x; ext q
      by_cases h : q = q₀ <;> simp [flip, h]
    have hflip_neg : ∀ x : QAlgorithms.Qubits n,
        (∏ q ∈ T, spin (flip x) q) = -(∏ q ∈ T, spin x q) := by
      intro x
      rw [← Finset.mul_prod_erase T _ hq₀, ← Finset.mul_prod_erase T _ hq₀]
      have h0 : spin (flip x) q₀ = -spin x q₀ := by
        simp only [spin, flip, ↓reduceIte]
        cases x q₀ <;> norm_num
      have hrest : ∏ q ∈ T.erase q₀, spin (flip x) q = ∏ q ∈ T.erase q₀, spin x q := by
        refine Finset.prod_congr rfl fun q hq => ?_
        have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
        simp [spin, flip, hne]
      rw [h0, hrest, neg_mul]
    have hsum_eq : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin (flip x) q) =
        ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) :=
      Fintype.sum_equiv hflip_inv.toPerm _ _ fun _ => rfl
    have hsum_neg : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin (flip x) q) =
        -∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) := by
      simp_rw [hflip_neg, Finset.sum_neg_distrib]
    have hsum0 : ∑ x : QAlgorithms.Qubits n, (∏ q ∈ T, spin x q) = 0 := by linarith
    simp [avgZ, hsum0]

private lemma avgZ_prod_spin_mul {n : ℕ} (A B : Finset (Fin n)) :
    avgZ (fun x => (∏ q ∈ A, spin x q) * (∏ q ∈ B, spin x q)) = if A = B then 1 else 0 := by
  simp_rw [prod_spin_symmDiff, avgZ_prod_spin]
  by_cases h : A = B
  · subst h; simp
  · have hs : symmDiff A B ≠ ∅ := by
      intro heq
      exact h (Finset.symmDiff_eq_empty.mp heq)
    simp [h, hs]

private def tripleSet {n : ℕ} (t : Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {t.1, t.2.1, t.2.2}

private lemma mem_tripleSet_iff {n : ℕ} (t : Fin n × Fin n × Fin n) (v : Fin n) :
    v ∈ tripleSet t ↔ onTriple t v := by
  simp [tripleSet, onTriple, Finset.mem_insert, Finset.mem_singleton]

private lemma tripleSet_inj {n : ℕ} (t₁ t₂ : Fin n × Fin n × Fin n)
    (ht₁ : t₁.1 < t₁.2.1 ∧ t₁.2.1 < t₁.2.2)
    (ht₂ : t₂.1 < t₂.2.1 ∧ t₂.2.1 < t₂.2.2)
    (heq : tripleSet t₁ = tripleSet t₂) : t₁ = t₂ := by
  have h12 : ∀ v, v ∈ tripleSet t₁ ↔ v ∈ tripleSet t₂ := fun v => by rw [heq]
  have ha1 : t₁.1 ∈ tripleSet t₂ := (h12 t₁.1).mp (by simp [tripleSet])
  have hb1 : t₂.1 ∈ tripleSet t₁ := (h12 t₂.1).mpr (by simp [tripleSet])
  have ha1_le : t₂.1 ≤ t₁.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha1
    rcases ha1 with h | h | h <;> omega
  have hb1_le : t₁.1 ≤ t₂.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hb1
    rcases hb1 with h | h | h <;> omega
  have hfst : t₁.1 = t₂.1 := le_antisymm hb1_le ha1_le
  have ha2 : t₁.2.1 ∈ tripleSet t₂ := (h12 t₁.2.1).mp (by simp [tripleSet])
  have hb2 : t₂.2.1 ∈ tripleSet t₁ := (h12 t₂.2.1).mpr (by simp [tripleSet])
  have ha2_le : t₂.2.1 ≤ t₁.2.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha2
    rcases ha2 with h | h | h <;> omega
  have hb2_le : t₁.2.1 ≤ t₂.2.1 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hb2
    rcases hb2 with h | h | h <;> omega
  have hsnd : t₁.2.1 = t₂.2.1 := le_antisymm hb2_le ha2_le
  have ha3 : t₁.2.2 ∈ tripleSet t₂ := (h12 t₁.2.2).mp (by simp [tripleSet])
  have hb3 : t₂.2.2 ∈ tripleSet t₁ := (h12 t₂.2.2).mpr (by simp [tripleSet])
  have ha3_eq : t₁.2.2 = t₂.2.2 := by
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at ha3 hb3
    rcases ha3 with h | h | h <;> rcases hb3 with g | g | g <;> omega
  ext <;> simp [hfst, hsnd, ha3_eq]

private lemma prod_tripleSet_mul_spin {n : ℕ} (t : Fin n × Fin n × Fin n)
    (ht : t.1 < t.2.1 ∧ t.2.1 < t.2.2) (v : Fin n) (hv : onTriple t v) (x : QAlgorithms.Qubits n) :
    spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x v =
      ∏ q ∈ (tripleSet t).erase v, spin x q := by
  have h12 : t.1 ≠ t.2.1 := ne_of_lt ht.1
  have h13 : t.1 ≠ t.2.2 := ne_of_lt (ht.1.trans ht.2)
  have h23 : t.2.1 ≠ t.2.2 := ne_of_lt ht.2
  have hprod : ∏ q ∈ tripleSet t, spin x q = spin x t.1 * spin x t.2.1 * spin x t.2.2 := by
    rw [tripleSet, Finset.prod_insert (by simp [h12, h13]), Finset.prod_insert (by simp [h23]),
      Finset.prod_singleton]
    ring
  have hv_mem : v ∈ tripleSet t := (mem_tripleSet_iff t v).mpr hv
  rw [← hprod, ← Finset.mul_prod_erase (tripleSet t) _ hv_mem]
  calc (spin x v * ∏ q ∈ (tripleSet t).erase v, spin x q) * spin x v
      = (spin x v * spin x v) * ∏ q ∈ (tripleSet t).erase v, spin x q := by ring
    _ = ∏ q ∈ (tripleSet t).erase v, spin x q := by rw [spin_sq, one_mul]

private lemma roleBit_onTriple {n : ℕ} (t : Fin n × Fin n × Fin n) (r : Fin 3) :
    onTriple t (roleBit t r) := by
  fin_cases r <;> simp [roleBit, onTriple]

private lemma eq_31_helper {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m) (r : Fin 3) :
    avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) ∧
      termCount tri i r ≤ D := by
  let v := roleBit (tri i) r
  let S : Finset (Fin m) := Finset.univ.filter (fun j => sharesOnly tri i j r)
  have hcard : S.card = termCount tri i r := by
    simp only [termCount, S]
  have hcPoly : ∀ x, cPoly tri rhs i r x =
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := by
    intro x
    simp only [cPoly, Finset.sum_filter, S]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [prod_tripleSet_mul_spin (tri j) (htri.1 j) v hj.2.1 x]
    · rfl
  have hpart1 : avgZ (fun x => cPoly tri rhs i r x ^ 2) = (termCount tri i r : ℝ) := by
    have hsq : ∀ x, cPoly tri rhs i r x ^ 2 =
        ∑ j₁ ∈ S, ∑ j₂ ∈ S,
          (sgn rhs j₁ * sgn rhs j₂) *
            ((∏ q ∈ (tripleSet (tri j₁)).erase v, spin x q) *
              (∏ q ∈ (tripleSet (tri j₂)).erase v, spin x q)) := by
      intro x
      rw [hcPoly x, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      ring
    simp_rw [hsq, avgZ_sum, avgZ_smul, avgZ_prod_spin_mul]
    rw [← hcard]
    have hdiag : ∀ j₁ ∈ S,
        (∑ j₂ ∈ S, (sgn rhs j₁ * sgn rhs j₂) *
          if (tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v then (1 : ℝ) else 0) = 1 := by
      intro j₁ hj₁
      have hv₁ : v ∈ tripleSet (tri j₁) :=
        (mem_tripleSet_iff (tri j₁) v).mpr (Finset.mem_filter.mp hj₁).2.2.1
      have huniq : ∀ j₂ ∈ S,
          ((tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v) ↔ j₁ = j₂ := by
        intro j₂ hj₂
        constructor
        · intro heq
          have hv₂ : v ∈ tripleSet (tri j₂) :=
            (mem_tripleSet_iff (tri j₂) v).mpr (Finset.mem_filter.mp hj₂).2.2.1
          have hset : tripleSet (tri j₁) = tripleSet (tri j₂) := by
            rw [← Finset.insert_erase hv₁, ← Finset.insert_erase hv₂, heq]
          exact htri.2 (tripleSet_inj (tri j₁) (tri j₂) (htri.1 j₁) (htri.1 j₂) hset)
        · rintro rfl; rfl
      have hterm : ∀ j₂ ∈ S,
          (sgn rhs j₁ * sgn rhs j₂) *
            (if (tripleSet (tri j₁)).erase v = (tripleSet (tri j₂)).erase v then (1 : ℝ) else 0) =
          if j₂ = j₁ then 1 else 0 := by
        intro j₂ hj₂
        simp_rw [huniq j₂ hj₂]
        by_cases heq : j₂ = j₁
        · subst heq
          simp only [↓reduceIte, mul_one]
          simp only [sgn]
          cases rhs j₂ <;> norm_num
        · have heq' : j₁ ≠ j₂ := Ne.symm heq
          simp [heq, heq']
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hj₁]
    rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine ⟨hpart1, ?_⟩
  let A : Finset (Fin m) := Finset.univ.filter (fun j => onTriple (tri j) v)
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, roleBit_onTriple (tri i) r⟩
  have hsub : S ⊆ A.erase i := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_erase.mpr ⟨hj'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj'.2.1⟩⟩
  have hA_le : A.card ≤ D + 1 := by
    simpa [A] using hocc v
  have hS_le : S.card ≤ A.card - 1 := by
    calc S.card ≤ (A.erase i).card := Finset.card_le_card hsub
      _ = A.card - 1 := Finset.card_erase_of_mem hiA
  rw [← hcard]
  omega

private lemma avgZ_mono {n : ℕ} {f g : QAlgorithms.Qubits n → ℝ} (h : ∀ x, f x ≤ g x) :
    avgZ f ≤ avgZ g := by
  simp only [avgZ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma avgZ_cPoly_eq_zero {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (htri : IsTripleFamily tri) (i : Fin m) (r : Fin 3) :
    avgZ (cPoly tri rhs i r) = 0 := by
  let v := roleBit (tri i) r
  let S : Finset (Fin m) := Finset.univ.filter (fun j => sharesOnly tri i j r)
  have hcPoly : ∀ x, cPoly tri rhs i r x =
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := by
    intro x
    simp only [cPoly, Finset.sum_filter, S]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [prod_tripleSet_mul_spin (tri j) (htri.1 j) v hj.2.1 x]
    · rfl
  have hfun : cPoly tri rhs i r = fun x =>
      ∑ j ∈ S, sgn rhs j * ∏ q ∈ (tripleSet (tri j)).erase v, spin x q := funext hcPoly
  rw [hfun, avgZ_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [avgZ_smul, avgZ_prod_spin]
  have hne : (tripleSet (tri j)).erase v ≠ ∅ := by
    have h12 : (tri j).1 ≠ (tri j).2.1 := ne_of_lt (htri.1 j).1
    have h13 : (tri j).1 ≠ (tri j).2.2 := ne_of_lt ((htri.1 j).1.trans (htri.1 j).2)
    have h23 : (tri j).2.1 ≠ (tri j).2.2 := ne_of_lt (htri.1 j).2
    have hcard3 : (tripleSet (tri j)).card = 3 := by
      rw [tripleSet, Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    have hv : v ∈ tripleSet (tri j) :=
      (mem_tripleSet_iff (tri j) v).mpr (Finset.mem_filter.mp hj).2.2.1
    have hcard2 : ((tripleSet (tri j)).erase v).card = 2 := by
      rw [Finset.card_erase_of_mem hv, hcard3]
    intro h0
    rw [h0, Finset.card_empty] at hcard2
    omega
  simp [hne]

private lemma eq_32_helper {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (i : Fin m)
    (ε : Fin 3 → ℝ) (hε : ∀ r, ε r = 1 ∨ ε r = -1) :
    avgZ (fun x => (sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x) ^ 2) ≤ 1 + 9 * (D : ℝ) := by
  have hpt : ∀ x,
      (sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
        ε 2 * cPoly tri rhs i 2 x) ^ 2 ≤
      sgn rhs i ^ 2 +
        2 * sgn rhs i * (ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
          ε 2 * cPoly tri rhs i 2 x) +
        3 * ((ε 0 * cPoly tri rhs i 0 x) ^ 2 + (ε 1 * cPoly tri rhs i 1 x) ^ 2 +
          (ε 2 * cPoly tri rhs i 2 x) ^ 2) := by
    intro x
    nlinarith [sq_nonneg (ε 0 * cPoly tri rhs i 0 x - ε 1 * cPoly tri rhs i 1 x),
      sq_nonneg (ε 1 * cPoly tri rhs i 1 x - ε 2 * cPoly tri rhs i 2 x),
      sq_nonneg (ε 2 * cPoly tri rhs i 2 x - ε 0 * cPoly tri rhs i 0 x)]
  refine (avgZ_mono hpt).trans ?_
  simp_rw [avgZ_add, avgZ_smul, avgZ_const]
  have hsgn_sq : sgn rhs i ^ 2 = 1 := by
    simp only [sgn]
    cases rhs i <;> norm_num
  have hε_sq : ∀ r : Fin 3, ε r ^ 2 = 1 := by
    intro r
    rcases hε r with h | h <;> rw [h] <;> norm_num
  have h0 : avgZ (cPoly tri rhs i 0) = 0 := avgZ_cPoly_eq_zero tri rhs htri i 0
  have h1 : avgZ (cPoly tri rhs i 1) = 0 := avgZ_cPoly_eq_zero tri rhs htri i 1
  have h2 : avgZ (cPoly tri rhs i 2) = 0 := avgZ_cPoly_eq_zero tri rhs htri i 2
  have hsq_eq : ∀ r : Fin 3,
      avgZ (fun x => (ε r * cPoly tri rhs i r x) ^ 2) = (termCount tri i r : ℝ) := by
    intro r
    have heq : (fun x => (ε r * cPoly tri rhs i r x) ^ 2) =
        fun x => ε r ^ 2 * (cPoly tri rhs i r x ^ 2) := by
      funext x; ring
    rw [heq, avgZ_smul, hε_sq r, one_mul]
    exact (eq_31_helper tri rhs D htri hocc i r).1
  have htc0 : (termCount tri i 0 : ℝ) ≤ D :=
    Nat.cast_le.mpr (eq_31_helper tri rhs D htri hocc i 0).2
  have htc1 : (termCount tri i 1 : ℝ) ≤ D :=
    Nat.cast_le.mpr (eq_31_helper tri rhs D htri hocc i 1).2
  have htc2 : (termCount tri i 2 : ℝ) ≤ D :=
    Nat.cast_le.mpr (eq_31_helper tri rhs D htri hocc i 2).2
  have hlin : avgZ (fun x => ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x) = 0 := by
    rw [avgZ_add, avgZ_add, avgZ_smul, avgZ_smul, avgZ_smul, h0, h1, h2]
    ring
  have hsq_sum : avgZ (fun x => (ε 0 * cPoly tri rhs i 0 x) ^ 2 +
      (ε 1 * cPoly tri rhs i 1 x) ^ 2 + (ε 2 * cPoly tri rhs i 2 x) ^ 2) =
      (termCount tri i 0 : ℝ) + (termCount tri i 1 : ℝ) + (termCount tri i 2 : ℝ) := by
    rw [avgZ_add, avgZ_add, hsq_eq 0, hsq_eq 1, hsq_eq 2]
  rw [hsgn_sq, hlin, hsq_sum]
  linarith

private lemma pairOfTriple_eq {n : ℕ} (t : Fin n × Fin n × Fin n) (ht : t.1 < t.2.1 ∧ t.2.1 < t.2.2)
    (v : Fin n) (hv : onTriple t v) :
    ∃ p q : Fin n, p < q ∧
      ∀ x : QAlgorithms.Qubits n,
        spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x v = spin x p * spin x q := by
  rcases hv with rfl | rfl | rfl
  · refine ⟨t.2.1, t.2.2, ht.2, fun x => ?_⟩
    calc spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x t.1
        = (spin x t.1 * spin x t.1) * (spin x t.2.1 * spin x t.2.2) := by ring
      _ = spin x t.2.1 * spin x t.2.2 := by rw [spin_sq, one_mul]
  · refine ⟨t.1, t.2.2, ht.1.trans ht.2, fun x => ?_⟩
    calc spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x t.2.1
        = (spin x t.2.1 * spin x t.2.1) * (spin x t.1 * spin x t.2.2) := by ring
      _ = spin x t.1 * spin x t.2.2 := by rw [spin_sq, one_mul]
  · refine ⟨t.1, t.2.1, ht.1, fun x => ?_⟩
    calc spin x t.1 * spin x t.2.1 * spin x t.2.2 * spin x t.2.2
        = (spin x t.2.2 * spin x t.2.2) * (spin x t.1 * spin x t.2.1) := by ring
      _ = spin x t.1 * spin x t.2.1 := by rw [spin_sq, one_mul]

private lemma u_avgZ_pow_le {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (D : ℕ) (htri : IsTripleFamily tri)
    (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D) (i : Fin m) (k : ℕ)
    (ε : Fin 3 → ℝ) (hε : ∀ r, ε r = 1 ∨ ε r = -1) :
    avgZ (fun x => |sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (10 * (D : ℝ)) ^ (k + 2) := by
  have hpair : ∀ (r : Fin 3) (j : Fin m),
      ∃ p q : Fin n, (sharesOnly tri i j r → p < q) ∧
        ∀ x : QAlgorithms.Qubits n,
          (if sharesOnly tri i j r then
            sgn rhs j * (spin x (tri j).1 * spin x (tri j).2.1 * spin x (tri j).2.2 *
              spin x (roleBit (tri i) r))
          else 0) =
          if sharesOnly tri i j r then sgn rhs j * spin x p * spin x q else 0 := by
    intro r j
    by_cases hj : sharesOnly tri i j r
    · obtain ⟨p, q, hpq, hspin⟩ := pairOfTriple_eq (tri j) (htri.1 j) (roleBit (tri i) r) hj.2.1
      refine ⟨p, q, fun _ => hpq, fun x => ?_⟩
      simp only [hj, ↓reduceIte, hspin x]
      ring
    · refine ⟨(tri j).1, (tri j).1, fun h => absurd h hj, fun x => ?_⟩
      simp [hj]
  choose p q hpq hterm using hpair
  let a₂ : Fin n → Fin n → ℝ := fun u v =>
    ∑ r : Fin 3, ε r * ∑ j : Fin m,
      if sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then sgn rhs j else 0
  let u_fn : QAlgorithms.Qubits n → ℝ := fun x =>
    sgn rhs i + ε 0 * cPoly tri rhs i 0 x + ε 1 * cPoly tri rhs i 1 x +
      ε 2 * cPoly tri rhs i 2 x
  have hu_eq : ∀ x, u_fn x =
      sgn rhs i + ∑ v : Fin n, (0 : ℝ) * spin x v +
        ∑ u : Fin n, ∑ v : Fin n, (if u < v then a₂ u v * spin x u * spin x v else 0) := by
    intro x
    have hsum_uv : (∑ u : Fin n, ∑ v : Fin n,
        (if u < v then a₂ u v * spin x u * spin x v else 0)) =
        ∑ r : Fin 3, ε r * cPoly tri rhs i r x := by
      have hre : ∀ u v : Fin n,
          (if u < v then a₂ u v * spin x u * spin x v else 0) =
          ∑ r : Fin 3, ε r * ∑ j : Fin m,
            if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
              sgn rhs j * spin x u * spin x v
            else 0 := by
        intro u v
        by_cases huv : u < v
        · simp only [huv, ↓reduceIte, a₂, Finset.sum_mul, true_and]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
        · simp [huv]
      simp_rw [hre]
      calc (∑ u : Fin n, ∑ v : Fin n, ∑ r : Fin 3, ε r * ∑ j : Fin m,
            if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
              sgn rhs j * spin x u * spin x v
            else 0)
          = ∑ u : Fin n, ∑ r : Fin 3, ∑ v : Fin n, ε r * ∑ j : Fin m,
              if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                sgn rhs j * spin x u * spin x v
              else 0 := Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ r : Fin 3, ∑ u : Fin n, ∑ v : Fin n, ε r * ∑ j : Fin m,
              if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                sgn rhs j * spin x u * spin x v
              else 0 := Finset.sum_comm
        _ = ∑ r : Fin 3, ε r * cPoly tri rhs i r x := by
            refine Finset.sum_congr rfl fun r _ => ?_
            have hpull : (∑ u : Fin n, ∑ v : Fin n, ε r * ∑ j : Fin m,
                if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                  sgn rhs j * spin x u * spin x v
                else 0) =
                ε r * ∑ u : Fin n, ∑ v : Fin n, ∑ j : Fin m,
                  if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                    sgn rhs j * spin x u * spin x v
                  else 0 := by
              simp_rw [← Finset.mul_sum]
            rw [hpull]
            congr 1
            have hswap_vj : ∀ u : Fin n,
                (∑ v : Fin n, ∑ j : Fin m,
                  if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                    sgn rhs j * spin x u * spin x v
                  else 0) =
                ∑ j : Fin m, ∑ v : Fin n,
                  if u < v ∧ sharesOnly tri i j r ∧ p r j = u ∧ q r j = v then
                    sgn rhs j * spin x u * spin x v
                  else 0 := fun u => Finset.sum_comm
            simp_rw [hswap_vj]
            rw [Finset.sum_comm]
            simp only [cPoly]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hterm r j x]
            by_cases hj : sharesOnly tri i j r
            · have hpqj : p r j < q r j := hpq r j hj
              rw [if_pos hj]
              rw [Finset.sum_eq_single (p r j)]
              · rw [Finset.sum_eq_single (q r j)]
                · simp [hpqj, hj]
                · intro v _ hv; simp [Ne.symm hv]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro u _ hu
                refine Finset.sum_eq_zero fun v _ => ?_
                simp [Ne.symm hu]
              · intro h; exact absurd (Finset.mem_univ _) h
            · simp [hj]
    rw [hsum_uv]
    simp only [Fin.sum_univ_three, zero_mul, Finset.sum_const_zero, add_zero]
    dsimp only [u_fn]
    ring
  have hbon := eq_29_helper n k (sgn rhs i) (fun _ => 0) a₂
  dsimp only at hbon
  have hbon' : avgZ (fun x => |u_fn x| ^ (k + 2)) ≤
      ((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (avgZ (fun x => u_fn x ^ 2)) ^ (k + 2) := by
    simpa only [← hu_eq] using hbon
  have h32 := eq_32_helper tri rhs D htri hocc i ε hε
  have hle10 : avgZ (fun x => u_fn x ^ 2) ≤ 10 * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hsqrt_le : Real.sqrt (avgZ (fun x => u_fn x ^ 2)) ≤ Real.sqrt (10 * (D : ℝ)) :=
    Real.sqrt_le_sqrt hle10
  have hpow_le : Real.sqrt (avgZ (fun x => u_fn x ^ 2)) ^ (k + 2) ≤
      Real.sqrt (10 * (D : ℝ)) ^ (k + 2) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le (k + 2)
  exact hbon'.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))

private lemma exp_one_lt : Real.exp 1 < 272 / 100 := by
  have hb := Real.exp_bound (x := (1 : ℝ)) (n := 4) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.factorial, Nat.cast_one, div_one, abs_one, one_pow, one_mul] at hb
  norm_num at hb
  linarith [(abs_le.mp hb).2]

private lemma coeff_bound_eq_34 (k : ℕ) :
    ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2) ≤ 9 ^ (k + 2) := by
  have hfac_ge : ((k : ℝ) + 1) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ Real.exp ((k : ℝ) + 1) := by
    have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity) (k + 2)
    have hmem : k + 1 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum
      (f := fun m : ℕ => ((k : ℝ) + 1) ^ m / (m.factorial : ℝ))
      (fun m _ => div_nonneg (pow_nonneg (by positivity) m) (Nat.cast_nonneg m.factorial)) hmem
    exact hsingle.trans hs
  have hratio : ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ Real.exp 1 ^ (k + 2) := by
    have h1 : ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) =
        (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (((k : ℝ) + 1) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
      have hfac : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac, pow_succ]
      field_simp
    have h2 : (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hexp_pow : Real.exp ((k : ℝ) + 1) = Real.exp 1 ^ (k + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexp_le : Real.exp 1 ^ (k + 1) ≤ Real.exp 1 ^ (k + 2) := by
      have he1 : 1 ≤ Real.exp 1 := by simpa using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
      exact pow_le_pow_right₀ he1 (by omega)
    rw [h1]
    calc (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (((k : ℝ) + 1) ^ (k + 1) / ((k + 1).factorial : ℝ))
        ≤ 1 * Real.exp ((k : ℝ) + 1) :=
          mul_le_mul h2 hfac_ge (by positivity) (by positivity)
      _ = Real.exp 1 ^ (k + 1) := by rw [one_mul, hexp_pow]
      _ ≤ Real.exp 1 ^ (k + 2) := hexp_le
  have hsqrt10 : Real.sqrt 10 < 317 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hprod : Real.exp 1 * Real.sqrt 10 ≤ 9 := by
    have h1 := exp_one_lt.le
    have h2 := hsqrt10.le
    nlinarith [Real.exp_pos 1, Real.sqrt_nonneg 10]
  calc ((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)
      ≤ Real.exp 1 ^ (k + 2) * Real.sqrt 10 ^ (k + 2) :=
        mul_le_mul_of_nonneg_right hratio (pow_nonneg (Real.sqrt_nonneg 10) _)
    _ = (Real.exp 1 * Real.sqrt 10) ^ (k + 2) := (mul_pow _ _ _).symm
    _ ≤ 9 ^ (k + 2) := pow_le_pow_left₀ (by positivity) hprod _

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D)
    (k : ℕ) (hk : Odd k) (i : Fin m) (γ : ℝ) :
    |Rk tri rhs i k γ| ≤ (9 * Real.sqrt D * |γ|) ^ (k + 2) := by
  have h28 := eq_28_helper tri rhs i k hk γ
  have hb1 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => 1 | 1 => 1 | 2 => 1)
    (fun r => by fin_cases r <;> simp)
  have hb2 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => 1 | 1 => -1 | 2 => -1)
    (fun r => by fin_cases r <;> simp)
  have hb3 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => -1 | 1 => 1 | 2 => -1)
    (fun r => by fin_cases r <;> simp)
  have hb4 := u_avgZ_pow_le tri rhs D htri hocc hD i k (fun | 0 => -1 | 1 => -1 | 2 => 1)
    (fun r => by fin_cases r <;> simp)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hb1 hb2 hb3 hb4
  have havg_sum : avgZ (fun x =>
      let d := sgn rhs i
      let c₁ := cPoly tri rhs i 0 x
      let c₂ := cPoly tri rhs i 1 x
      let c₃ := cPoly tri rhs i 2 x
      |d + c₁ + c₂ + c₃| ^ (k + 2) + |d + c₁ - c₂ - c₃| ^ (k + 2) +
        |d - c₁ + c₂ - c₃| ^ (k + 2) + |d - c₁ - c₂ + c₃| ^ (k + 2)) ≤
      4 * (((k : ℝ) + 1) ^ (k + 2) * Real.sqrt (10 * (D : ℝ)) ^ (k + 2)) := by
    simp only [avgZ_add]
    linarith
  have hstep1 : |Rk tri rhs i k γ| ≤
      (1 / 2 : ℝ) * |γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) *
        Real.sqrt D ^ (k + 2) := by
    have hmul := mul_le_mul_of_nonneg_left havg_sum
      (by positivity : 0 ≤ (1 / 8 : ℝ) * |γ| ^ (k + 2) / ((k + 2).factorial : ℝ))
    have hsqrt10D : Real.sqrt (10 * (D : ℝ)) = Real.sqrt 10 * Real.sqrt D :=
      Real.sqrt_mul (by norm_num) (D : ℝ)
    rw [hsqrt10D, mul_pow] at hmul
    refine h28.trans (hmul.trans_eq ?_)
    ring
  have hstep2 : (1 / 2 : ℝ) * |γ| ^ (k + 2) *
      (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) *
      Real.sqrt D ^ (k + 2) ≤
      (9 * Real.sqrt D * |γ|) ^ (k + 2) := by
    have hcb := coeff_bound_eq_34 k
    have hmul1 : |γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) ≤
        |γ| ^ (k + 2) * 9 ^ (k + 2) :=
      mul_le_mul_of_nonneg_left hcb (by positivity)
    have hmul2 : (1 / 2 : ℝ) * (|γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2))) *
        Real.sqrt D ^ (k + 2) ≤
        9 ^ (k + 2) * |γ| ^ (k + 2) * Real.sqrt D ^ (k + 2) := by
      have ha : (1 / 2 : ℝ) * (|γ| ^ (k + 2) *
          (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2))) ≤
          1 * (|γ| ^ (k + 2) * 9 ^ (k + 2)) := by
        refine mul_le_mul (by norm_num) hmul1 (by positivity) (by norm_num)
      have hb := mul_le_mul_of_nonneg_right ha (pow_nonneg (Real.sqrt_nonneg D) (k + 2))
      linarith
    have hlin_eq : (1 / 2 : ℝ) * |γ| ^ (k + 2) *
        (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2)) *
        Real.sqrt D ^ (k + 2) =
        (1 / 2 : ℝ) * (|γ| ^ (k + 2) *
          (((k : ℝ) + 1) ^ (k + 2) / ((k + 2).factorial : ℝ) * Real.sqrt 10 ^ (k + 2))) *
        Real.sqrt D ^ (k + 2) := by ring
    rw [hlin_eq]
    exact hmul2.trans_eq (by rw [mul_pow, mul_pow]; ring)
  exact hstep1.trans hstep2
