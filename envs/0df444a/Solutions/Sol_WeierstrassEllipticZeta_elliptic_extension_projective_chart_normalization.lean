-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_chart_normalization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T19:59:31.552847+00:00
-- url     : https://prove2.me/submissions/0a7ed427-0f90-40ef-8519-d4c8ef8ef932

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open Filter MvPolynomial
open scoped Topology
open WeierstrassEllipticZeta

private lemma substitution_degree (c : Fin 2) (i : Fin 7) :
    (extensionChartSubstitution c i).totalDegree ≤ ![1, 1, 2, 2, 2, 2, 2] i := by
  have hm (a b : Fin 4) : (X a * X b : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 := by
    simpa using totalDegree_mul (X a : MvPolynomial (Fin 4) ℂ) (X b)
  have hp (a : Fin 4) : (C (2 : ℂ) * X a ^ 2).totalDegree ≤ 2 := by
    exact (totalDegree_mul _ _).trans (by
      simp)
  have hn (p : MvPolynomial (Fin 4) ℂ) : (-p).totalDegree = p.totalDegree := by
    simp [totalDegree]
  fin_cases c <;> fin_cases i <;> simp [extensionChartSubstitution]
  · exact (totalDegree_add _ _).trans (max_le (hm 2 3) (hp 1))
  · rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans (max_le (hm 1 3) (by simpa [hn] using hp 2))

private lemma normalization_degree (c : Fin 2) (m n : ℕ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (extensionChartNormalize c Q).totalDegree ≤ m + 2 * n := by
  classical
  rw [Q.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  change (aeval (extensionChartSubstitution c) (monomial d (coeff d Q))).totalDegree ≤ _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  calc
    _ ≤ ∑ i : Fin 7, (extensionChartSubstitution c i ^ d i).totalDegree := by
      exact (totalDegree_mul _ _).trans (by
        simpa using totalDegree_finsetProd Finset.univ
          (fun i : Fin 7 => extensionChartSubstitution c i ^ d i))
    _ ≤ ∑ i : Fin 7, d i * ![1, 1, 2, 2, 2, 2, 2] i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (substitution_degree c i))
    _ = m + 2 * n := by
      obtain ⟨hm, hn⟩ := hQ d hd
      simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
      change d 0 + (d 1 + (d 2 * 2 + (d 3 * 2 + (d 4 * 2 +
        (d 5 * 2 + d 6 * 2))))) = m + 2 * n
      omega

private lemma normalization_eval (c : Fin 2) (t : ℂ) (v : Fin 5 → ℂ)
    (hquad : v 0 * v 4 - v 2 * v 3 - 2 * v 1 ^ 2 = 0)
    (hv : v (extensionChartDenominator c) ≠ 0) (Q : MvPolynomial (Fin 7) ℂ) :
    eval (extensionChartCoordinates (fun j _ => v j) c t) (extensionChartNormalize c Q) =
      eval ![1, t, v 0 / v (extensionChartDenominator c),
        v 1 / v (extensionChartDenominator c), v 2 / v (extensionChartDenominator c),
        v 3 / v (extensionChartDenominator c), v 4 / v (extensionChartDenominator c)] Q := by
  have heval (f : Fin 4 → ℂ) :
      eval f (extensionChartNormalize c Q) =
        eval (fun i => eval f (extensionChartSubstitution c i)) Q := by
    exact comp_aeval_apply (extensionChartSubstitution c) (aeval f) Q
  rw [heval]
  apply congrArg (fun f : Fin 7 → ℂ => eval f Q)
  funext i
  fin_cases c
  · have hv0 : v 0 ≠ 0 := hv
    have hlast : v 2 / v 0 * (v 3 / v 0) + 2 * (v 1 / v 0) ^ 2 = v 4 / v 0 := by
      field_simp
      linear_combination -hquad
    fin_cases i <;> simp [extensionChartSubstitution, extensionChartCoordinates,
      extensionChartDenominator, hv0, hlast]
  · have hv2 : v 2 ≠ 0 := hv
    have hthird : v 0 / v 2 * (v 4 / v 2) - 2 * (v 1 / v 2) ^ 2 = v 3 / v 2 := by
      field_simp
      linear_combination hquad
    fin_cases i <;> simp [extensionChartSubstitution, extensionChartCoordinates,
      extensionChartDenominator, hv2, hthird]

theorem solution
    (g₂ g₃ : ℂ) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (R : ℂ → ProjectiveExtensionChartLocus g₂ g₃)
    (hR : ∀ z : ℂ, ∃ hv : (fun j : Fin 5 => S j z) ≠ 0,
      (R z).val.val = Projectivization.mk ℂ (fun j => S j z) hv)
    (hjets : ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (k : ℕ),
      ((extensionChartDerivation g₂ g₃ c)^[k] p).totalDegree ≤ p.totalDegree + k ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv k (fun w => eval (extensionChartCoordinates S c w) p) z =
          eval (extensionChartCoordinates S c z) ((extensionChartDerivation g₂ g₃ c)^[k] p) ∧
        ((k : ℕ∞) ≤ analyticOrderAt
            (fun w => eval (extensionChartCoordinates S c w) p) z ↔
          ∀ l < k, eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[l] p) = 0)) :
    (∀ (z : ℂ) (j : Fin 5), (R z).val.val.rep j ≠ 0 ↔ S j z ≠ 0) ∧
    ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧
        d 2 + d 3 + d 4 + d 5 + d 6 = n) →
      ∀ (c : Fin 2) (k : ℕ),
        ((extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
          m + 2 * n + k ∧
        ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
          iteratedDeriv k (fun w => eval
            ![1, w, (R w).val.val.rep 0 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 1 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 2 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 3 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 4 / (R w).val.val.rep (extensionChartDenominator c)] Q) z =
            eval (extensionChartCoordinates S c z)
              ((extensionChartDerivation g₂ g₃ c)^[k] (extensionChartNormalize c Q)) ∧
          ((k : ℕ∞) ≤ analyticOrderAt (fun w => eval
            ![1, w, (R w).val.val.rep 0 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 1 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 2 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 3 / (R w).val.val.rep (extensionChartDenominator c),
              (R w).val.val.rep 4 / (R w).val.val.rep (extensionChartDenominator c)] Q) z ↔
            ∀ l < k, eval (extensionChartCoordinates S c z)
              ((extensionChartDerivation g₂ g₃ c)^[l] (extensionChartNormalize c Q)) = 0) := by
  have hrep (z : ℂ) : ∃ a : ℂ, a ≠ 0 ∧
      (R z).val.val.rep = fun j => a * S j z := by
    obtain ⟨hv, h⟩ := hR z
    rw [h]
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (fun j => S j z) hv
    refine ⟨a, a.ne_zero, ?_⟩
    rw [← ha]
    rfl
  have hratio (z : ℂ) (i j : Fin 5) :
      (R z).val.val.rep i / (R z).val.val.rep j = S i z / S j z := by
    obtain ⟨a, ha, h⟩ := hrep z
    rw [h]
    exact mul_div_mul_left _ _ ha
  have hquad (z : ℂ) : S 0 z * S 4 z - S 2 z * S 3 z - 2 * S 1 z ^ 2 = 0 := by
    obtain ⟨a, ha, h⟩ := hrep z
    have hq := (R z).val.property.1
    simp only [extensionQuadric, map_sub, map_mul, map_pow, eval_X, eval_C, h] at hq
    apply (mul_eq_zero.mp (show a ^ 2 *
      (S 0 z * S 4 z - S 2 z * S 3 z - 2 * S 1 z ^ 2) = 0 by
        linear_combination hq)).resolve_left (pow_ne_zero _ ha)
  refine ⟨?_, ?_⟩
  · intro z j
    obtain ⟨a, ha, h⟩ := hrep z
    rw [h]
    exact mul_ne_zero_iff.trans (and_iff_right ha)
  · intro m n Q hQ c k
    refine ⟨(hjets c _ k).1.trans (Nat.add_le_add_right (normalization_degree c m n Q hQ) k), ?_⟩
    intro z hz
    have hlocal :
        (fun w => eval
          ![1, w, (R w).val.val.rep 0 / (R w).val.val.rep (extensionChartDenominator c),
            (R w).val.val.rep 1 / (R w).val.val.rep (extensionChartDenominator c),
            (R w).val.val.rep 2 / (R w).val.val.rep (extensionChartDenominator c),
            (R w).val.val.rep 3 / (R w).val.val.rep (extensionChartDenominator c),
            (R w).val.val.rep 4 / (R w).val.val.rep (extensionChartDenominator c)] Q)
        =ᶠ[𝓝 z] (fun w => eval (extensionChartCoordinates S c w) (extensionChartNormalize c Q)) := by
      have hU : IsOpen {w : ℂ | S (extensionChartDenominator c) w ≠ 0} :=
        (hS _).continuous.isOpen_preimage _ isOpen_ne
      filter_upwards [hU.mem_nhds hz] with w hw
      simp only [hratio]
      exact (normalization_eval c w (fun j => S j w) (hquad w) hw Q).symm
    exact ⟨(hlocal.iteratedDeriv_eq k).trans ((hjets c _ k).2 z hz).1,
      (by rw [analyticOrderAt_congr hlocal]; exact ((hjets c _ k).2 z hz).2)⟩

