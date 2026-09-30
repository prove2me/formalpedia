-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_chart_cubic_relation_ideals
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T22:09:18.437398+00:00
-- url     : https://prove2.me/submissions/70dec0e1-1954-4787-a285-283d7832404c

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_relation_ideal
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic
import Definitions.Def_WeierstrassEllipticZeta_CubicChartBase


noncomputable section
open MvPolynomial
namespace WeierstrassEllipticZeta

private lemma polynomial_clear_denominator
    (d : MvPolynomial (Fin 4) ℂ) (a : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (P : MvPolynomial (Fin 4) ℂ) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin 4) ℂ), ∀ v : Fin 4 → ℂ,
      eval v d ≠ 0 → eval v Q = (eval v d) ^ k *
        eval (fun i => eval v (a i) / eval v d) P := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, by simp⟩
  | add P R hP hR =>
    obtain ⟨k, Q, hQ⟩ := hP
    obtain ⟨l, T, hT⟩ := hR
    refine ⟨k + l, d ^ l * Q + d ^ k * T, ?_⟩
    intro v hv
    simp only [map_add, map_mul, map_pow, hQ v hv, hT v hv, pow_add]
    ring
  | mul_X P i hP =>
    obtain ⟨k, Q, hQ⟩ := hP
    refine ⟨k + 1, Q * a i, ?_⟩
    intro v hv
    simp only [map_mul, eval_X, hQ v hv, pow_succ]
    field_simp

/-- Clear the denominator in the transition from the first chart to the second. -/
theorem first_to_second_chart_clearing (P : MvPolynomial (Fin 4) ℂ) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin 4) ℂ), ∀ t x y u : ℂ, y ≠ 0 →
      eval ![t, x, y, u] Q = y ^ k * eval ![t, 1 / y, x / y, u + 2 * x ^ 2 / y] P := by
  obtain ⟨k, Q, hQ⟩ := polynomial_clear_denominator (X 2)
    (![X 0 * X 2, 1, X 1, X 2 * X 3 + C 2 * X 1 ^ 2]) P
  refine ⟨k, Q, ?_⟩
  intro t x y u hy
  have h := hQ ![t, x, y, u] (by simpa using hy)
  have hv : (fun i => eval ![t, x, y, u]
      (![X 0 * X 2, 1, X 1, X 2 * X 3 + C 2 * X 1 ^ 2] i) /
        eval ![t, x, y, u] (X 2)) = ![t, 1 / y, x / y, u + 2 * x ^ 2 / y] := by
    ext i
    fin_cases i <;> simp [hy] <;> field_simp <;> ring
  rw [hv] at h
  simpa using h

private lemma second_to_first_chart_clearing (H : MvPolynomial (Fin 4) ℂ) :
    ∃ (m : ℕ) (R : MvPolynomial (Fin 4) ℂ), ∀ t a b h : ℂ, a ≠ 0 →
      eval ![t, a, b, h] R = a ^ m * eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a] H := by
  obtain ⟨m, R, hR⟩ := polynomial_clear_denominator (X 1)
    (![X 0 * X 1, X 2, 1, X 1 * X 3 - C 2 * X 2 ^ 2]) H
  refine ⟨m, R, ?_⟩
  intro t a b h ha
  have he := hR ![t, a, b, h] (by simpa using ha)
  have hv : (fun i => eval ![t, a, b, h]
      (![X 0 * X 1, X 2, 1, X 1 * X 3 - C 2 * X 2 ^ 2] i) /
        eval ![t, a, b, h] (X 1)) = ![t, b / a, 1 / a, h - 2 * b ^ 2 / a] := by
    ext i
    fin_cases i <;> simp [ha] <;> field_simp <;> ring
  rw [hv] at he
  simpa using he

private lemma second_cubic_saturated (g₂ g₃ : ℂ) (P : MvPolynomial (Fin 4) ℂ)
    (n : ℕ) (hP : extensionChartCubic g₂ g₃ 1 ∣ X 1 ^ n * P) :
    extensionChartCubic g₂ g₃ 1 ∣ P := by
  have hnot : ¬ (X 1 : MvPolynomial (Fin 4) ℂ) ∣ extensionChartCubic g₂ g₃ 1 := by
    rintro ⟨Q, hQ⟩
    have h := congrArg (eval (![0, 0, 1, 0] : Fin 4 → ℂ)) hQ
    norm_num [extensionChartCubic] at h
    exact one_ne_zero (show (1 : ℂ) = 0 from h)
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    rw [pow_succ', mul_assoc, dvd_X_mul_iff] at hP
    exact ih (hP.resolve_right (fun h => hnot h.1))

/-- A relation transferred to the first chart comes from the second cubic;
the factor in the overlap denominator can be removed without radicalizing. -/
theorem second_cubic_membership_of_first (g₂ g₃ : ℂ)
    (P Q : MvPolynomial (Fin 4) ℂ) (k : ℕ)
    (hQ : ∀ t x y u : ℂ, y ≠ 0 →
      eval ![t, x, y, u] Q = y ^ k * eval ![t, 1 / y, x / y, u + 2 * x ^ 2 / y] P)
    (hfirst : X 2 * Q ∈ Ideal.span {extensionChartCubic g₂ g₃ 0}) :
    P ∈ Ideal.span {extensionChartCubic g₂ g₃ 1} := by
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp hfirst
  obtain ⟨m, R, hR⟩ := second_to_first_chart_clearing H
  have hpoint (t a b h : ℂ) (ha : a ≠ 0) :
      a ^ (m + 3) * eval ![t, a, b, h] P =
        a ^ (k + 1) * eval ![t, a, b, h] (extensionChartCubic g₂ g₃ 1) *
          eval ![t, a, b, h] R := by
    have he := congrArg (eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a]) hH
    have hq := hQ t (b / a) (1 / a) (h - 2 * b ^ 2 / a) (one_div_ne_zero ha)
    have hback : ![t, 1 / (1 / a), (b / a) / (1 / a),
        (h - 2 * b ^ 2 / a) + 2 * (b / a) ^ 2 / (1 / a)] = ![t, a, b, h] := by
      ext i
      fin_cases i <;> simp <;> field_simp <;> ring
    rw [hback] at hq
    have hf : eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a]
        (extensionChartCubic g₂ g₃ 0) =
          eval ![t, a, b, h] (extensionChartCubic g₂ g₃ 1) / a ^ 3 := by
      simp [extensionChartCubic]
      field_simp <;> ring
    simp only [map_mul, eval_X] at he
    change (1 / a) * eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a] Q =
      eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a] (extensionChartCubic g₂ g₃ 0) *
        eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a] H at he
    rw [hq, hf] at he
    have hr := hR t a b h ha
    rw [← mul_left_inj' (pow_ne_zero (k + 1) ha)] at hr
    generalize eval ![t, b / a, 1 / a, h - 2 * b ^ 2 / a] H = Hval at he hr
    generalize eval ![t, a, b, h] P = Pval at he ⊢
    generalize eval ![t, a, b, h] (extensionChartCubic g₂ g₃ 1) = Fval at he ⊢
    generalize eval ![t, a, b, h] R = Rval at hr ⊢
    simp only [pow_add, pow_one, one_div_pow] at he hr ⊢
    field_simp at he
    linear_combination a ^ m * a * he - Fval * hr
  have hpoly : X 1 ^ (m + 3) * P = X 1 ^ (k + 1) * extensionChartCubic g₂ g₃ 1 * R := by
    have hz : X 1 * (X 1 ^ (m + 3) * P -
        X 1 ^ (k + 1) * extensionChartCubic g₂ g₃ 1 * R) = (0 : MvPolynomial (Fin 4) ℂ) := by
      apply MvPolynomial.funext
      intro v
      simp only [map_mul, map_sub, map_pow, eval_X, map_zero]
      by_cases hv : v 1 = 0
      · simp [hv]
      · have h := hpoint (v 0) (v 1) (v 2) (v 3) hv
        have hvvec : ![v 0, v 1, v 2, v 3] = v := by ext i; fin_cases i <;> rfl
        rw [hvvec] at h
        rw [h, sub_self, mul_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (X_ne_zero 1))
  apply Ideal.mem_span_singleton.mpr
  apply second_cubic_saturated g₂ g₃ P (m + 3)
  rw [hpoly]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end WeierstrassEllipticZeta


noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private lemma coordinate_relations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    (∀ w, S 0 w * S 4 w - S 2 w * S 3 w - 2 * S 1 w ^ 2 = 0) ∧
    (∀ w, S 2 w ^ 2 * S 0 w - 4 * S 1 w ^ 3 +
      L.g₂ * S 1 w * S 0 w ^ 2 + L.g₃ * S 0 w ^ 3 = 0) := by
  have ha (j : Fin 5) (w : ℂ) : AnalyticAt ℂ (S j) w := hS j w trivial
  constructor
  · have heq : (fun w => S 0 w * S 4 w - S 2 w * S 3 w - 2 * S 1 w ^ 2) =
        (0 : ℂ → ℂ) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (show AnalyticOnNhd ℂ _ Set.univ from fun w _ => by fun_prop)
        (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
        (z₀ := L.ω₁ / 2)
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
        L.ω₁_div_two_notMem_lattice] with u hu
      simp [hS_value u hu]
      ring
    intro w
    exact congrFun heq w
  · have heq : (fun w => S 2 w ^ 2 * S 0 w - 4 * S 1 w ^ 3 +
        L.g₂ * S 1 w * S 0 w ^ 2 + L.g₃ * S 0 w ^ 3) = (0 : ℂ → ℂ) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (show AnalyticOnNhd ℂ _ Set.univ from fun w _ => by fun_prop)
        (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
        (z₀ := L.ω₁ / 2)
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
        L.ω₁_div_two_notMem_lattice] with u hu
      have hc := L.derivWeierstrassP_sq u hu
      simp [hS_value u hu]
      linear_combination D.sigma u ^ 9 * hc
    intro w
    exact congrFun heq w



end WeierstrassEllipticZeta

open TranscendenceTheory WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    (∀ c : Fin 2, extensionGlobalChartKernel S c = Ideal.span {extensionChartCubic L.g₂ L.g₃ c}) ∧
      ∀ (Q : MvPolynomial (Fin 7) ℂ) (c : Fin 2),
        extensionCubicChartBaseIdeal L Q c = extensionFirstCubicChartBaseIdeal L S Q c := by
  classical
  have hfirst := (elliptic_first_chart_relation_ideal L D S hS hS_value hS_ne).1
  obtain ⟨hquad, hcubic⟩ := coordinate_relations L D S hS hS_value
  have hsecond : extensionGlobalChartKernel S 1 = Ideal.span {extensionChartCubic L.g₂ L.g₃ 1} := by
    apply le_antisymm
    · intro P hP
      obtain ⟨k, Q, hQ⟩ := first_to_second_chart_clearing P
      have hQmem : X 2 * Q ∈ extensionGlobalChartKernel S 0 := by
        simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker]
        intro z hz
        have hz0 : S 0 z ≠ 0 := hz
        by_cases hz2 : S 2 z = 0
        · simp [map_mul, extensionChartCoordinates, hz2]
        · have htransition :
              ![z, 1 / (S 2 z / S 0 z), (S 1 z / S 0 z) / (S 2 z / S 0 z),
                S 3 z / S 0 z + 2 * (S 1 z / S 0 z) ^ 2 / (S 2 z / S 0 z)] =
                extensionChartCoordinates S 1 z := by
            have hq := hquad z
            ext i
            fin_cases i <;> simp [extensionChartCoordinates]
            all_goals field_simp
            linear_combination -hq
          have hp : eval (extensionChartCoordinates S 1 z) P = 0 := by
            have hh := hP
            simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker] at hh
            exact hh z hz2
          have he := hQ z (S 1 z / S 0 z) (S 2 z / S 0 z) (S 3 z / S 0 z)
            (div_ne_zero hz2 hz0)
          rw [htransition, hp, mul_zero] at he
          simpa [extensionChartCoordinates, he] using
            (show S 2 z / S 0 z * eval ![z, S 1 z / S 0 z, S 2 z / S 0 z, S 3 z / S 0 z] Q = 0 by
              rw [he, mul_zero])
      rw [hfirst] at hQmem
      exact second_cubic_membership_of_first L.g₂ L.g₃ P Q k hQ hQmem
    · apply Ideal.span_le.mpr
      rintro P rfl
      change extensionChartCubic L.g₂ L.g₃ 1 ∈ extensionGlobalChartKernel S 1
      simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker]
      intro z hz
      have hz2 : S 2 z ≠ 0 := hz
      have hc := hcubic z
      simp [extensionChartCoordinates, extensionChartCubic]
      field_simp
      linear_combination hc
  refine ⟨?_, ?_⟩
  · intro c
    fin_cases c
    · exact hfirst
    · exact hsecond
  · intro Q c
    fin_cases c
    · simp [extensionCubicChartBaseIdeal, extensionFirstCubicChartBaseIdeal]
    · simp [extensionCubicChartBaseIdeal, extensionFirstCubicChartBaseIdeal, hsecond]
