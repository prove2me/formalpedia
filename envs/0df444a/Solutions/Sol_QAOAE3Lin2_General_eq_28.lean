-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:35:33.323216+00:00
-- url     : https://prove2.me/submissions/bdc024a7-18f0-4072-8fa6-0566e54f28e2

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

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
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
