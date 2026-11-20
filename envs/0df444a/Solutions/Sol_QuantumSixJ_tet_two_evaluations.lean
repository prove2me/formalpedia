-- Prove2me | solution 1 for QuantumSixJ.tet_two_evaluations
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T09:21:12.180895+00:00
-- url     : https://prove2.me/submissions/5434592e-3018-406b-893e-7c40f7fd3c0b

import Theorems.Thm_QuantumSixJ_scalar_foundations

open QuantumSixJ
open scoped BigOperators QuantumSixJ

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

open QuantumSixJ
open scoped QuantumSixJ

private theorem qFactorial_inv_shift (n : ℤ) : (⟬n - 1⟭!)⁻¹ = ⟬n⟭ * (⟬n⟭!)⁻¹ := by
  by_cases hn : n ≤ 0
  · rcases lt_or_eq_of_le hn with hneg | hzero
    · have hprev : n - 1 < 0 := by omega
      simp [qFactorial, hneg, hprev]
    · subst n
      norm_num [qFactorial, qInt]
  · have hn0 : 0 ≤ n := by omega
    have hp0 : 0 ≤ n - 1 := by omega
    have hset : Finset.Icc (1 : ℤ) n = insert n (Finset.Icc 1 (n - 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnmem : n ∉ Finset.Icc (1 : ℤ) (n - 1) := by
      intro hmem
      have := (Finset.mem_Icc.mp hmem).2
      omega
    have hstep : ⟬n⟭! = ⟬n⟭ * ⟬n - 1⟭! := by
      simp only [qFactorial, if_neg (not_lt.mpr hn0), if_neg (not_lt.mpr hp0)]
      rw [hset, Finset.prod_insert hnmem]
    rw [← div_eq_mul_inv, eq_div_iff (qFactorial_ne_zero n hn0), hstep]
    field_simp [qFactorial_ne_zero (n - 1) hp0]

namespace TetSupport

/-- The diagonal Appendix sum has at most two surviving terms. -/
lemma diagonal_support (a b l S : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hab : Admissible a b l) (hS : tetSummand a a b b l 2 S ≠ 0) :
    S = (a + b + l) / 2 ∨ S = (a + b + l) / 2 + 1 := by
  let s := (a + b + l) / 2
  have har := hab
  rcases har with ⟨ha0, hb0, hl, hat, hbt, hlt, hp⟩
  have hj : hAdmissible a a b b l := ⟨hab, hab⟩
  have hv : vAdmissible a a b b 2 := by
    constructor <;> dsimp [Admissible] <;> omega
  have hA : tetA a a b b l 2 = ![s, s, a + 1, b + 1] := by
    ext i
    fin_cases i <;> simp [tetA] <;> (try dsimp [s]) <;> omega
  have hB : tetB a a b b l 2 = ![s + 1, s + 1, a + b] := by
    ext i
    fin_cases i <;> simp [tetB] <;> (try dsimp [s]) <;> omega
  have hr := (tet_summand_support_bounds a a b b l 2 S hj hv).mp hS
  simp only [hA, hB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.head_fin_const, max_le_iff, le_min_iff] at hr
  dsimp [s] at hr
  omega

lemma diagonal_sum_two (a b l : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hab : Admissible a b l) :
    (∑ S ∈ Finset.Icc 0 (a + a + b + b + l + 2), tetSummand a a b b l 2 S) =
      tetSummand a a b b l 2 ((a + b + l) / 2) +
        tetSummand a a b b l 2 ((a + b + l) / 2 + 1) := by
  let s := (a + b + l) / 2
  have har := hab
  rcases har with ⟨ha0, hb0, hl, hat, hbt, hlt, hp⟩
  have hsubset : ({s, s + 1} : Finset ℤ) ⊆ Finset.Icc 0 (a + a + b + b + l + 2) := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    simp only [Finset.mem_Icc]
    rcases hS with rfl | rfl <;> dsimp [s] <;> omega
  calc
    _ = ∑ S ∈ ({s, s + 1} : Finset ℤ), tetSummand a a b b l 2 S := by
      symm
      apply Finset.sum_subset hsubset
      intro S _ hnot
      by_contra hne
      rcases diagonal_support a b l S ha hb hab hne with h | h
      · have heq : S = s := h
        rw [heq] at hnot
        simp at hnot
      · have heq : S = s + 1 := h
        rw [heq] at hnot
        simp at hnot
    _ = _ := by simp [show s ≠ s + 1 by omega, s]

/-- The adjacent Appendix sum has exactly one possible support index. -/
lemma adjacent_support (a d j S : ℤ) (ha : 0 < a)
    (hj : Admissible a d j) (hj2 : Admissible a d (j + 2))
    (hS : tetSummand a a (j + 2) j d 2 S ≠ 0) :
    S = (a + d + j) / 2 + 1 := by
  let s := (a + d + j) / 2
  have har := hj
  have har2 := hj2
  rcases har with ⟨ha0, hd, hj0, h1, h2, h3, hp⟩
  rcases har2 with ⟨_, _, _, h4, h5, h6, hp2⟩
  have hh : hAdmissible a a (j + 2) j d := by
    constructor <;> dsimp [Admissible] <;> omega
  have hv : vAdmissible a a (j + 2) j 2 := by
    constructor <;> dsimp [Admissible] <;> omega
  have hA : tetA a a (j + 2) j d 2 = ![s, s + 1, a + 1, j + 2] := by
    ext i
    fin_cases i <;> simp [tetA] <;> (try dsimp [s]) <;> omega
  have hB : tetB a a (j + 2) j d 2 = ![s + 1, s + 2, a + j + 1] := by
    ext i
    fin_cases i <;> simp [tetB] <;> (try dsimp [s]) <;> omega
  have hr := (tet_summand_support_bounds a a (j + 2) j d 2 S hh hv).mp hS
  simp only [hA, hB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.head_fin_const, max_le_iff, le_min_iff] at hr
  dsimp [s] at hr
  omega

lemma adjacent_sum_single (a d j : ℤ) (ha : 0 < a)
    (hj : Admissible a d j) (hj2 : Admissible a d (j + 2)) :
    (∑ S ∈ Finset.Icc 0 (a + a + (j + 2) + j + d + 2),
      tetSummand a a (j + 2) j d 2 S) =
        tetSummand a a (j + 2) j d 2 ((a + d + j) / 2 + 1) := by
  apply Finset.sum_eq_single ((a + d + j) / 2 + 1)
  · intro S _ hne
    by_contra hS
    exact hne (adjacent_support a d j S ha hj hj2 hS)
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_Icc]
    rcases hj with ⟨ha0, hd, hj0, h1, h2, h3, hp⟩
    constructor <;> omega

/-- Swapping the middle external labels with equal first two labels only
permutes the A and B factors in each individual Appendix summand. -/
lemma summand_swap_cd (a c d j l S : ℤ) :
    tetSummand a a d c j l S = tetSummand a a c d j l S := by
  have hA : tetA a a d c j l = ![(tetA a a c d j l) 1, (tetA a a c d j l) 0,
      (tetA a a c d j l) 2, (tetA a a c d j l) 3] := by
    ext i
    fin_cases i <;> simp [tetA] <;> congr 1 <;> ring
  have hB : tetB a a d c j l = ![(tetB a a c d j l) 1, (tetB a a c d j l) 0,
      (tetB a a c d j l) 2] := by
    ext i
    fin_cases i <;> simp [tetB] <;> congr 1 <;> ring
  simp only [tetSummand, hA, hB, Fin.prod_univ_succ]
  simp
  ring

lemma adjacent_reverse_sum_single (a d j : ℤ) (ha : 0 < a)
    (hj : Admissible a d j) (hj2 : Admissible a d (j + 2)) :
    (∑ S ∈ Finset.Icc 0 (a + a + j + (j + 2) + d + 2),
      tetSummand a a j (j + 2) d 2 S) =
        tetSummand a a j (j + 2) d 2 ((a + d + j) / 2 + 1) := by
  rw [show a + a + j + (j + 2) + d + 2 = a + a + (j + 2) + j + d + 2 by ring]
  simp_rw [summand_swap_cd a (j + 2) j d 2]
  exact adjacent_sum_single a d j ha hj hj2

end TetSupport
open QuantumSixJ
open scoped QuantumSixJ BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace TetSpecialProof

private lemma fzero : ⟬(0 : ℤ)⟭! = 1 := by norm_num [qFactorial]

private lemma qone : ⟬(1 : ℤ)⟭ = 1 := by
  simpa [qInt] using div_self q_denominator_ne_zero

private lemma fone : ⟬(1 : ℤ)⟭! = 1 := by simp [qFactorial, qone]

private lemma ftwo : ⟬(2 : ℤ)⟭! = ⟬(2 : ℤ)⟭ := by
  have hi : Finset.Icc (1 : ℤ) 2 = {1, 2} := by decide
  simp [qFactorial, hi, qone]

private lemma fstep (n : ℤ) (hn : 0 ≤ n) : ⟬n + 1⟭! = ⟬n + 1⟭ * ⟬n⟭! := by
  have hset : Finset.Icc (1 : ℤ) (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc (1 : ℤ) n := by
    intro hk
    have := (Finset.mem_Icc.mp hk).2
    omega
  simp only [qFactorial, if_neg (show ¬n + 1 < 0 by omega), if_neg (not_lt.mpr hn)]
  rw [hset, Finset.prod_insert hnot]

private lemma fprev (n : ℤ) (hn : 0 < n) : ⟬n⟭! = ⟬n⟭ * ⟬n - 1⟭! := by
  simpa using fstep (n - 1) (by omega)

private lemma adm_swap (a b c : ℤ) (h : Admissible a b c) : Admissible b a c := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  dsimp [Admissible]
  omega

private lemma adm_cycle (a b c : ℤ) (h : Admissible a b c) : Admissible c a b := by
  rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩
  dsimp [Admissible]
  omega

lemma diagonal (a b l : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : Admissible a b l) :
    ⟬a⟭ * ⟬b⟭ * tetSum a a b b l 2 = θ a b l * Λ a b l := by
  let s := (a + b + l) / 2
  have har := hab
  rcases har with ⟨ha0, hb0, hl, hat, hbt, hlt, hp⟩
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hx : 0 ≤ s - a := by dsimp [s]; omega
  have hy : 0 ≤ s - b := by dsimp [s]; omega
  have hz : 0 ≤ a + b - s := by dsimp [s]; omega
  have hsl : s - l = a + b - s := by dsimp [s]; omega
  have hla : (a - b + l) / 2 = s - b := by dsimp [s]; omega
  have hlb : (-a + b + l) / 2 = s - a := by dsimp [s]; omega
  have hlc : (a + b - l) / 2 = a + b - s := by dsimp [s]; omega
  have hj : hAdmissible a a b b l := ⟨hab, hab⟩
  have hv : vAdmissible a a b b 2 := by
    constructor <;> dsimp [Admissible] <;> omega
  have hA : tetA a a b b l 2 = ![s, s, a + 1, b + 1] := by
    ext i
    fin_cases i <;> simp [tetA] <;> (try dsimp [s]) <;> omega
  have hB : tetB a a b b l 2 = ![s + 1, s + 1, a + b] := by
    ext i
    fin_cases i <;> simp [tetB] <;> (try dsimp [s]) <;> omega
  have support (S : ℤ) (hS : tetSummand a a b b l 2 S ≠ 0) : S = s ∨ S = s + 1 := by
    have hr := (tet_summand_support_bounds a a b b l 2 S hj hv).mp hS
    simp only [hA, hB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.head_fin_const, max_le_iff, le_min_iff] at hr
    omega
  have hsubset : ({s, s + 1} : Finset ℤ) ⊆ Finset.Icc 0 (a + a + b + b + l + 2) := by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    simp only [Finset.mem_Icc]
    rcases hS with rfl | rfl <;> omega
  have hsum : (∑ S ∈ Finset.Icc 0 (a + a + b + b + l + 2), tetSummand a a b b l 2 S) =
      tetSummand a a b b l 2 s + tetSummand a a b b l 2 (s + 1) := by
    calc
      _ = ∑ S ∈ ({s, s + 1} : Finset ℤ), tetSummand a a b b l 2 S := by
        symm
        apply Finset.sum_subset hsubset
        intro S _ hnot
        by_contra hne
        rcases support S hne with rfl | rfl <;> simp at hnot
      _ = _ := by simp [show s ≠ s + 1 by omega]
  have hidx1 : s - (a + 1) = (s - a) - 1 := by omega
  have hidx2 : s - (b + 1) = (s - b) - 1 := by omega
  have hidx3 : a + b - (s + 1) = (a + b - s) - 1 := by omega
  have hsign : (-1 : Scalar) ^ (s + 1) = -((-1 : Scalar) ^ s) := by
    rw [zpow_add₀ (by norm_num : (-1 : Scalar) ≠ 0)]
    simp
  rw [tetSum, if_pos ⟨hj, hv⟩, hsum]
  simp [tetSummand, hA, hB, Fin.prod_univ_succ, fzero, fone]
  rw [θ, if_pos hab, Λ, if_pos hab]
  change _ = ((-1 : Scalar) ^ s * ⟬s + 1⟭! * ⟬s - a⟭! * ⟬s - b⟭! * ⟬s - l⟭! /
    (⟬a⟭! * ⟬b⟭! * ⟬l⟭!)) *
    ((⟬(a - b + l) / 2⟭ * ⟬(-a + b + l) / 2⟭ -
      ⟬(a + b - l) / 2⟭ * ⟬s + 2⟭) / ⟬2⟭)
  rw [hsl, hla, hlb, hlc]
  simp only [hidx1, hidx2, hidx3, show s + 1 + 1 = s + 2 by omega,
    div_eq_mul_inv, mul_inv_rev]
  rw [qFactorial_inv_shift (s - a), qFactorial_inv_shift (s - b),
    qFactorial_inv_shift (a + b - s)]
  have hfs : ⟬s + 2⟭! = ⟬s + 2⟭ * ⟬s + 1⟭! := by
    simpa [add_assoc] using fstep (s + 1) (by omega)
  rw [fprev a ha, fprev b hb, hfs, ftwo, hsign]
  field_simp [qInt_ne_zero a (by omega), qInt_ne_zero b (by omega), qInt_ne_zero 2 (by omega),
    qFactorial_ne_zero (a - 1) (by omega), qFactorial_ne_zero (b - 1) (by omega),
    qFactorial_ne_zero l hl, qFactorial_ne_zero (s - a) hx,
    qFactorial_ne_zero (s - b) hy, qFactorial_ne_zero (a + b - s) hz]
  <;> ring

lemma neighboring (a d j : ℤ) (ha : 0 < a) (hj : Admissible a d j)
    (hj2 : Admissible a d (j + 2)) :
    ⟬a⟭ * tetSum a a (j + 2) j d 2 = ⟬(a + d - j) / 2⟭ * θ (j + 2) a d := by
  let s := (a + d + j) / 2
  have har := hj
  have har2 := hj2
  rcases har with ⟨ha0, hd, hj0, h1, h2, h3, hp⟩
  rcases har2 with ⟨_, _, _, h4, h5, h6, hp2⟩
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hx : 0 ≤ s - a := by dsimp [s]; omega
  have hy : 0 ≤ s - j - 1 := by dsimp [s]; omega
  have hz : 0 ≤ a + j - s := by dsimp [s]; omega
  have htheta : Admissible (j + 2) a d := adm_cycle a d (j + 2) hj2
  have hh : hAdmissible a a (j + 2) j d := by
    constructor <;> dsimp [Admissible] <;> omega
  have hv : vAdmissible a a (j + 2) j 2 := by
    constructor <;> dsimp [Admissible] <;> omega
  have hA : tetA a a (j + 2) j d 2 = ![s, s + 1, a + 1, j + 2] := by
    ext i
    fin_cases i <;> simp [tetA] <;> (try dsimp [s]) <;> omega
  have hB : tetB a a (j + 2) j d 2 = ![s + 1, s + 2, a + j + 1] := by
    ext i
    fin_cases i <;> simp [tetB] <;> (try dsimp [s]) <;> omega
  have support (S : ℤ) (hS : tetSummand a a (j + 2) j d 2 S ≠ 0) : S = s + 1 := by
    have hr := (tet_summand_support_bounds a a (j + 2) j d 2 S hh hv).mp hS
    simp only [hA, hB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.head_fin_const, max_le_iff, le_min_iff] at hr
    omega
  have hsum : (∑ S ∈ Finset.Icc 0 (a + a + (j + 2) + j + d + 2),
      tetSummand a a (j + 2) j d 2 S) = tetSummand a a (j + 2) j d 2 (s + 1) := by
    apply Finset.sum_eq_single (s + 1)
    · intro S _ hne
      by_contra hS
      exact hne (support S hS)
    · intro hnot
      exfalso
      apply hnot
      simp only [Finset.mem_Icc]
      constructor <;> dsimp [s] <;> omega
  have hhalf : (j + 2 + a + d) / 2 = s + 1 := by dsimp [s]; omega
  have heigen : (a + d - j) / 2 = s - j := by dsimp [s]; omega
  have hsd : s + 1 - d = a + j - s + 1 := by dsimp [s]; omega
  have hidx : s + 1 - (j + 2) = s - j - 1 := by omega
  have hidx2 : s + 2 - (j + 2) = s - j := by omega
  have hidx3 : a + j + 1 - (a + 1) = j := by omega
  have hidx4 : a + j + 1 - (j + 2) = a - 1 := by omega
  have hidx5 : s + 2 - (a + 1) = s - a + 1 := by omega
  have hidx6 : a + j + 1 - (s + 1) = a + j - s := by omega
  have hidx7 : a + j + 1 - s = a + j - s + 1 := by omega
  have hidx8 : s + 1 - a = s - a + 1 := by omega
  rw [tetSum, if_pos ⟨hh, hv⟩, hsum, θ, if_pos htheta, heigen, hhalf]
  simp [tetSummand, hA, hB, Fin.prod_univ_succ, fzero, fone]
  simp only [hsd, hidx, hidx2, hidx3, hidx4, hidx5, hidx6, hidx7, hidx8]
  have hfa : ⟬a⟭! = ⟬a⟭ * ⟬a - 1⟭! := fprev a ha
  have hfy : ⟬s - j⟭! = ⟬s - j⟭ * ⟬s - j - 1⟭! := fprev (s - j) (by omega)
  rw [hfa, hfy]
  field_simp [qInt_ne_zero a (by omega), qFactorial_ne_zero (a - 1) (by omega),
    qFactorial_ne_zero (j + 2) (by omega), qFactorial_ne_zero j hj0,
    qFactorial_ne_zero d hd, qFactorial_ne_zero (s - a) hx,
    qFactorial_ne_zero (s - j - 1) hy, qFactorial_ne_zero (a + j - s) hz,
    qFactorial_ne_zero 2 (by omega)]
  <;> ring

end TetSpecialProof


private lemma swap_admissible {a b c : ℤ} (h : Admissible a b c) :
    Admissible b a c := by
  dsimp [Admissible] at *
  omega

private lemma off_tet_swap_cd_aux (a c d j l : ℤ) : tetSum a a c d j l = tetSum a a d c j l := by
  have hadm : (hAdmissible a a c d j ∧ vAdmissible a a c d l) ↔
      (hAdmissible a a d c j ∧ vAdmissible a a d c l) := by
    constructor
    · rintro ⟨⟨had, hac⟩, ⟨haal, hcdl⟩⟩
      exact ⟨⟨hac, had⟩, ⟨haal, swap_admissible hcdl⟩⟩
    · rintro ⟨⟨hac, had⟩, ⟨haal, hdc⟩⟩
      exact ⟨⟨had, hac⟩, ⟨haal, swap_admissible hdc⟩⟩
  have hA : tetA a a d c j l = ![(tetA a a c d j l) 1, (tetA a a c d j l) 0,
      (tetA a a c d j l) 2, (tetA a a c d j l) 3] := by
    ext i
    fin_cases i <;> simp [tetA] <;> congr 1 <;> ring
  have hB : tetB a a d c j l = ![(tetB a a c d j l) 1, (tetB a a c d j l) 0,
      (tetB a a c d j l) 2] := by
    ext i
    fin_cases i <;> simp [tetB] <;> congr 1 <;> ring
  have hs (S : ℤ) : tetSummand a a d c j l S = tetSummand a a c d j l S := by
    simp only [tetSummand, hA, hB, Fin.prod_univ_succ]
    simp
    ring
  by_cases h : hAdmissible a a c d j ∧ vAdmissible a a c d l
  · rw [tetSum, if_pos h, tetSum, if_pos (hadm.mp h)]
    simp_rw [hs]
    rw [show a + a + d + c + j + l = a + a + c + d + j + l by ring]
    have f41 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := by decide
    have f42 : (Fin.succ (Fin.succ (0 : Fin 2)) : Fin 4) = 2 := by decide
    have f43 : (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))) : Fin 4) = 3 := by decide
    have f42' : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := by decide
    have f43' : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := by decide
    have f31 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
    have f32 : (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3) = 2 := by decide
    simp only [hA, hB, Fin.prod_univ_succ, f41, f42, f43, f42', f43', f31, f32,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    ring
  · rw [tetSum, if_neg h, tetSum, if_neg]
    exact fun h' => h (hadm.mpr h')

theorem solution :
    (∀ u v k : ℤ, 0 < u → 0 < v → Admissible u v k →
      let m := (u + v + k) / 2
      (∀ z : ℤ, tetSummand u u v v k 2 z ≠ 0 → z = m ∨ z = m + 1) ∧
      (∑ z ∈ Finset.Icc 0 (2 * u + 2 * v + k + 2), tetSummand u u v v k 2 z) =
        tetSummand u u v v k 2 m + tetSummand u u v v k 2 (m + 1)) ∧
    (∀ u r s k : ℤ, 0 < u → Admissible u r k → Admissible u s k →
      (r = s + 2 ∨ s = r + 2) →
      let m := (u + min r s + k) / 2
      (∀ z : ℤ, tetSummand u u r s k 2 z ≠ 0 → z = m + 1) ∧
      (∑ z ∈ Finset.Icc 0 (2 * u + r + s + k + 2), tetSummand u u r s k 2 z) =
        tetSummand u u r s k 2 (m + 1)) ∧
    (∀ u v k : ℤ, 0 < u → 0 < v → Admissible u v k →
      ⟬u⟭ * ⟬v⟭ * tetSum u u v v k 2 = θ u v k * Λ u v k) ∧
    (∀ u r s k : ℤ, 0 < u → Admissible u r k → Admissible u s k →
      (r = s + 2 ∨ s = r + 2) →
      ⟬u⟭ * tetSum u u r s k 2 = ⟬(u + k - min r s) / 2⟭ * θ (max r s) u k) ∧
    (∀ u r s k : ℤ,
      (¬ Admissible u u 2 ∨ ¬ Admissible r s 2 ∨
        ¬ Admissible u r k ∨ ¬ Admissible u s k) → tetSum u u r s k 2 = 0) := by
  refine ⟨?_, ?_, TetSpecialProof.diagonal, ?_, ?_⟩
  · intro u v k hu hv hk
    dsimp only
    constructor
    · exact fun z hz => TetSupport.diagonal_support u v k z hu hv hk hz
    · convert TetSupport.diagonal_sum_two u v k hu hv hk using 1 <;> congr 2 <;> ring
  · intro u r s k hu hr hs hstep
    have hsr : Admissible u k s := by dsimp [Admissible] at *; omega
    have hrr : Admissible u k r := by dsimp [Admissible] at *; omega
    rcases hstep with he | he
    · subst r
      simp only [min_eq_right (show s ≤ s + 2 by omega)]
      constructor
      · intro z hz
        simpa only [add_comm, add_left_comm, add_assoc] using
          TetSupport.adjacent_support u k s z hu hsr hrr hz
      · convert TetSupport.adjacent_sum_single u k s hu hsr hrr using 1 <;> congr 2 <;> ring
    · subst s
      simp only [min_eq_left (show r ≤ r + 2 by omega)]
      constructor
      · intro z hz
        rw [TetSupport.summand_swap_cd u (r + 2) r k 2 z] at hz
        simpa only [add_comm, add_left_comm, add_assoc] using
          TetSupport.adjacent_support u k r z hu hrr hsr hz
      · convert TetSupport.adjacent_reverse_sum_single u k r hu hrr hsr using 1 <;> congr 2 <;> ring
  · intro u r s k hu hr hs hstep
    have hsr : Admissible u k s := by dsimp [Admissible] at *; omega
    have hrr : Admissible u k r := by dsimp [Admissible] at *; omega
    rcases hstep with he | he
    · subst r
      simp only [min_eq_right (show s ≤ s + 2 by omega), max_eq_left (show s ≤ s + 2 by omega)]
      exact TetSpecialProof.neighboring u k s hu hsr hrr
    · subst s
      simp only [min_eq_left (show r ≤ r + 2 by omega), max_eq_right (show r ≤ r + 2 by omega)]
      rw [off_tet_swap_cd_aux u r (r + 2) k 2]
      exact TetSpecialProof.neighboring u k r hu hrr hsr
  · intro u r s k hbad
    apply if_neg
    rintro ⟨⟨hus, hur⟩, ⟨huu, hrs⟩⟩
    rcases hbad with hbad | hbad | hbad | hbad
    · exact hbad huu
    · exact hbad hrs
    · apply hbad; dsimp [Admissible] at *; omega
    · apply hbad; dsimp [Admissible] at *; omega
