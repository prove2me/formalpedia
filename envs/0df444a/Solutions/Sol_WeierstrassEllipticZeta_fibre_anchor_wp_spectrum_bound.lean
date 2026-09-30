-- Prove2me | solution 1 for WeierstrassEllipticZeta.fibre_anchor_wp_spectrum_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T00:51:10.867714+00:00
-- url     : https://prove2.me/submissions/7a2f61a2-41ca-4658-bf48-3b6632b9c2e0

import Definitions.Def_WeierstrassEllipticZeta_TightCubicSections
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Theorems.Thm_WeierstrassEllipticZeta_finite_elementary_locus_vanishing
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial
open scoped Classical Topology
variable {A : Type*} [CommRing A] [Algebra ℂ A]

private theorem tight_weighted_monomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n i j k l : ℕ) (hi : i ≤ m) (hl : l ≤ n) (hw : 2 * j + 3 * k + l ≤ 4 * n) :
    t ^ i * x ^ j * y ^ k * u ^ l ∈ tightCubicSectionSpan t x y u m n := by
  induction k using Nat.twoStepInduction generalizing j with
  | zero =>
    exact Submodule.subset_span ⟨(⟨i, by omega⟩,
      ⟨⟨l, by omega⟩, ⟨0, ⟨j, by dsimp; omega⟩⟩⟩), rfl⟩
  | one =>
    exact Submodule.subset_span ⟨(⟨i, by omega⟩,
      ⟨⟨l, by omega⟩, ⟨1, ⟨j, by dsimp; omega⟩⟩⟩), rfl⟩
  | more k ih _ =>
    have h₀ := ih (j + 3) (by omega)
    have h₁ := ih (j + 1) (by omega)
    have h₂ := ih j (by omega)
    have heq : t ^ i * x ^ j * y ^ (k + 2) * u ^ l =
        (4 : ℂ) • (t ^ i * x ^ (j + 3) * y ^ k * u ^ l) -
          g₂ • (t ^ i * x ^ (j + 1) * y ^ k * u ^ l) -
          g₃ • (t ^ i * x ^ j * y ^ k * u ^ l) := by
      rw [pow_add, hy]
      simp only [Algebra.smul_def, map_ofNat, pow_add]
      ring
    rw [heq]
    exact (tightCubicSectionSpan t x y u m n).sub_mem
      ((tightCubicSectionSpan t x y u m n).sub_mem
        ((tightCubicSectionSpan t x y u m n).smul_mem 4 h₀)
        ((tightCubicSectionSpan t x y u m n).smul_mem g₂ h₁))
      ((tightCubicSectionSpan t x y u m n).smul_mem g₃ h₂)

private theorem tight_normalized_monomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n : ℕ) (d : Fin 7 →₀ ℕ) (a : ℂ)
    (hm : d 0 + d 1 = m) (hn : d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] (monomial d a) ∈
      tightCubicSectionSpan t x y u m n := by
  classical
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.prod_empty, one_pow, one_mul, mul_one]
  change algebraMap ℂ A a * (t ^ d 1 * (x ^ d 3 * (y ^ d 4 *
    (u ^ d 5 * (y * u + 2 * x ^ 2) ^ d 6)))) ∈ _
  rw [add_pow]
  simp only [Finset.mul_sum]
  apply (tightCubicSectionSpan t x y u m n).sum_mem
  intro r hr
  have hrn : r ≤ d 6 := by simpa using hr
  have hmem := tight_weighted_monomial_mem g₂ g₃ t x y u hy m n
    (d 1) (d 3 + 2 * (d 6 - r)) (d 4 + r) (d 5 + r) (by omega) (by omega) (by omega)
  have hs := (tightCubicSectionSpan t x y u m n).smul_mem
    (a * 2 ^ (d 6 - r) * (Nat.choose (d 6) r : ℂ)) hmem
  convert hs using 1 <;>
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat, map_natCast,
      pow_add, mul_pow, pow_mul] <;> ring

private theorem tight_normalized_polynomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q ∈
      tightCubicSectionSpan t x y u m n := by
  rw [Q.as_sum, map_sum]
  apply (tightCubicSectionSpan t x y u m n).sum_mem
  intro d hd
  exact tight_normalized_monomial_mem g₂ g₃ t x y u hy m n d (coeff d Q) (hQ d hd).1 (hQ d hd).2


private theorem constant_fibre_normal_form (g₂ g₃ t u : ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hn : 1 ≤ n)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    ∃ A B : Polynomial ℂ, A.natDegree ≤ 2 * n ∧ B.natDegree ≤ 2 * n - 2 ∧
      ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃ →
        eval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q =
          A.eval x + y * B.eval x := by
  let V := {p : ℂ × ℂ // p.2 ^ 2 = 4 * p.1 ^ 3 - g₂ * p.1 - g₃}
  let tx : V → ℂ := fun _ => t
  let ux : V → ℂ := fun _ => u
  let x : V → ℂ := fun p => p.val.1
  let y : V → ℂ := fun p => p.val.2
  have hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ (V → ℂ) g₂ * x -
      algebraMap ℂ (V → ℂ) g₃ := by
    funext p
    exact p.property
  have hp := tight_normalized_polynomial_mem g₂ g₃ tx x y ux hy m n Q hQ
  have hspan : ∀ f ∈ tightCubicSectionSpan tx x y ux m n,
      ∃ A B : Polynomial ℂ, A.natDegree ≤ 2 * n ∧ B.natDegree ≤ 2 * n - 2 ∧
        ∀ p : V, f p = A.eval p.val.1 + p.val.2 * B.eval p.val.1 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      rcases a with ⟨i, c, b, j⟩
      let P : Polynomial ℂ := Polynomial.C (t ^ i.val * u ^ c.val) * Polynomial.X ^ j.val
      have hP : P.natDegree ≤ j.val := by
        calc
          _ ≤ (Polynomial.C (t ^ i.val * u ^ c.val)).natDegree +
              (Polynomial.X ^ j.val : Polynomial ℂ).natDegree := Polynomial.natDegree_mul_le
          _ = j.val := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
      have hj := j.isLt
      have hc := c.isLt
      fin_cases b
      · refine ⟨P, 0, hP.trans ?_, by simp, ?_⟩
        · dsimp at hj
          omega
        · intro p
          simp [tightCubicSectionFamily, tx, ux, x, y, P]
          ring
      · refine ⟨0, P, by simp, hP.trans ?_, ?_⟩
        · dsimp at hj
          omega
        · intro p
          simp [tightCubicSectionFamily, tx, ux, x, y, P]
          ring
    | zero => exact ⟨0, 0, by simp, by simp, by simp⟩
    | add f g hf hg ihf ihg =>
      obtain ⟨Af, Bf, hAf, hBf, heF⟩ := ihf
      obtain ⟨Ag, Bg, hAg, hBg, heG⟩ := ihg
      refine ⟨Af + Ag, Bf + Bg,
        Polynomial.natDegree_add_le_of_degree_le hAf hAg,
        Polynomial.natDegree_add_le_of_degree_le hBf hBg, ?_⟩
      intro p
      simp only [Pi.add_apply, Polynomial.eval_add, heF, heG]
      ring
    | smul a f hf ih =>
      obtain ⟨Af, Bf, hAf, hBf, heF⟩ := ih
      refine ⟨a • Af, a • Bf, (Polynomial.natDegree_smul_le a Af).trans hAf,
        (Polynomial.natDegree_smul_le a Bf).trans hBf, ?_⟩
      intro p
      simp only [Pi.smul_apply, smul_eq_mul, Polynomial.eval_smul, heF]
      ring
  obtain ⟨A, B, hA, hB, heq⟩ := hspan _ hp
  refine ⟨A, B, hA, hB, ?_⟩
  intro x₀ y₀ hxy
  have h := heq ⟨(x₀, y₀), hxy⟩
  change _ = A.eval x₀ + y₀ * B.eval x₀ at h
  let ev := Pi.evalAlgHom ℂ (fun _ : V => ℂ) ⟨(x₀, y₀), hxy⟩
  change ev (aeval ![1, tx, 1, x, y, ux, y * ux + 2 * x ^ 2] Q) = _ at h
  rw [comp_aeval_apply] at h
  have hvec : (fun i => ev (![1, tx, 1, x, y, ux, y * ux + 2 * x ^ 2] i)) =
      ![1, t, 1, x₀, y₀, u, y₀ * u + 2 * x₀ ^ 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec] at h
  exact h

private theorem cubic_norm_polynomial (g₂ g₃ : ℂ) (A B : Polynomial ℂ)
    (hAB : A ≠ 0 ∨ B ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 2 * n - 2) :
    ∃ H : Polynomial ℂ, H ≠ 0 ∧ H.natDegree ≤ 4 * n ∧
      ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃ →
        A.eval x + y * B.eval x = 0 → H.eval x = 0 := by
  let F : Polynomial ℂ := Polynomial.C 4 * Polynomial.X ^ 3 -
    Polynomial.C g₂ * Polynomial.X - Polynomial.C g₃
  have hFdeg : F.natDegree = 3 := by
    dsimp [F]
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · have hsmall : (Polynomial.C g₂ * Polynomial.X).natDegree ≤ 1 := by
        calc
          _ ≤ (Polynomial.C g₂).natDegree + (Polynomial.X : Polynomial ℂ).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 1 := by simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add]
      simpa using lt_of_le_of_lt hsmall (by norm_num : (1 : ℕ) < 3)
  have hF : F ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hFdeg
    omega
  let H := A ^ 2 - F * B ^ 2
  have hH : H ≠ 0 := by
    intro hzero
    have heq : A ^ 2 = F * B ^ 2 := sub_eq_zero.mp hzero
    by_cases hB0 : B = 0
    · have hA0 : A = 0 := by simpa [hB0] using heq
      exact hAB.elim (fun h => h hA0) (fun h => h hB0)
    · have hdeg := congrArg Polynomial.natDegree heq
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_mul hF (pow_ne_zero 2 hB0),
        Polynomial.natDegree_pow, hFdeg] at hdeg
      omega
  refine ⟨H, hH, ?_, ?_⟩
  · have hpowA : (A ^ 2).natDegree ≤ 4 * n := by
      rw [Polynomial.natDegree_pow]
      omega
    have hpowB : (F * B ^ 2).natDegree ≤ 4 * n := by
      apply Polynomial.natDegree_mul_le.trans
      rw [hFdeg, Polynomial.natDegree_pow]
      omega
    simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hpowA hpowB
  · intro x y hxy hzero
    simp only [H, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul]
    have hFx : F.eval x = y ^ 2 := by simpa [F] using hxy.symm
    rw [hFx]
    linear_combination (A.eval x - y * B.eval x) * hzero

private lemma last_block_scaling (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → ℂ) (r : ℂ) :
    eval ![x 0, x 1, r * x 2, r * x 3, r * x 4, r * x 5, r * x 6] Q =
      r ^ n * eval x Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private lemma normalize_regular_eval (Q : MvPolynomial (Fin 7) ℂ)
    (t x y u : ℂ) :
    eval ![t, x, y, u] (extensionChartNormalize 0 Q) =
      eval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q := by
  change (aeval ![t, x, y, u]) ((aeval (extensionChartSubstitution 0)) Q) = _
  rw [comp_aeval_apply]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  funext i
  fin_cases i <;> simp [extensionChartSubstitution]

/-- A nonzero entire projective pullback is already nonzero on the regular
affine chart. Thus dehomogenization supplies the properness witness required by
the analytic subgroup criterion, including when the original nonzero value was
at a lattice point. -/
private theorem fibre_regular_witness
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0) :
    ∃ z : ℂ, z ∉ L.lattice ∧
      eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z] (extensionChartNormalize 0 Q) ≠ 0 := by
  classical
  by_contra! hzero
  apply hne
  have hF : AnalyticOnNhd ℂ (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) Set.univ := by
    intro z _
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
    · exact hS 0 z (Set.mem_univ z)
    · exact hS 1 z (Set.mem_univ z)
    · exact hS 2 z (Set.mem_univ z)
    · exact hS 3 z (Set.mem_univ z)
    · exact hS 4 z (Set.mem_univ z)
  apply AnalyticOnNhd.eq_of_eventuallyEq hF
    (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
    (z₀ := L.ω₁ / 2)
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds L.ω₁_div_two_notMem_lattice]
    with z hz
  change eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q = 0
  have he := last_block_scaling Q n hQ
    ![1, z, 1, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z,
      L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2]
    (D.sigma z ^ 3)
  rw [← normalize_regular_eval] at he
  simpa [hS_value z hz, hzero z hz] using he




end WeierstrassEllipticZeta
open WeierstrassEllipticZeta MvPolynomial

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hn : 1 ≤ n)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0) :
    ∃ H : Polynomial ℂ, H ≠ 0 ∧ H.natDegree ≤ 4 * n ∧
      H.roots.toFinset.card ≤ 4 * n ∧
      ∀ b : ℂ, b ∉ L.lattice → () ∈ fibreAnchorChoices S Q m n b →
        L.weierstrassP b ∈ H.roots.toFinset := by
  obtain ⟨z₀, hz₀, hnonzero⟩ := fibre_regular_witness L D S hS hS_value
    Q n (fun d hd => (hQ d hd).2) hne
  rw [normalize_regular_eval] at hnonzero
  obtain ⟨A, B, hA, hB, hpair⟩ := constant_fibre_normal_form
    L.g₂ L.g₃ z₀ (weierstrassZeta L z₀) Q m n hn hQ
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra! h
    apply hnonzero
    rw [hpair _ _ (L.derivWeierstrassP_sq z₀ hz₀), h.1, h.2]
    simp
  obtain ⟨H, hH, hdeg, hroot⟩ := cubic_norm_polynomial L.g₂ L.g₃ A B hAB n hn hA hB
  refine ⟨H, hH, hdeg,
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' H).trans hdeg), ?_⟩
  intro b hb hanchor
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hH).mpr
  apply hroot _ (L.derivWeierstrassP b) (L.derivWeierstrassP_sq b hb)
  rw [← hpair _ _ (L.derivWeierstrassP_sq b hb)]
  have hsig : D.sigma b ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := hS_ne b
    exact hj (by simp [hS_value b hb, h])
  have hall := ((finite_elementary_locus_vanishing S Q m n hQ .fibre ![0, b, 0]).2.2).mpr
    (Finset.mem_filter.mp hanchor).2
  have hw := hall ![z₀, b, weierstrassZeta L z₀ - weierstrassZeta L b] (by
    refine ⟨![z₀, 0, weierstrassZeta L z₀ - weierstrassZeta L b],
      by simp [elementaryDirections], ?_⟩
    ext i
    fin_cases i <;> simp)
  have hs := last_block_scaling Q n (fun d hd => (hQ d hd).2)
    ![1, z₀, 1, L.weierstrassP b, L.derivWeierstrassP b, weierstrassZeta L z₀,
      L.derivWeierstrassP b * weierstrassZeta L z₀ + 2 * L.weierstrassP b ^ 2]
    (D.sigma b ^ 3)
  have hz : eval ![1, z₀, D.sigma b ^ 3 * 1,
      D.sigma b ^ 3 * L.weierstrassP b, D.sigma b ^ 3 * L.derivWeierstrassP b,
      D.sigma b ^ 3 * weierstrassZeta L z₀,
      D.sigma b ^ 3 * (L.derivWeierstrassP b * weierstrassZeta L z₀ +
        2 * L.weierstrassP b ^ 2)] Q = 0 := by
    convert hw using 1
    apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
    ext i
    fin_cases i <;> simp [hS_value b hb] <;> ring
  have hzero : (D.sigma b ^ 3) ^ n *
      eval ![1, z₀, 1, L.weierstrassP b, L.derivWeierstrassP b, weierstrassZeta L z₀,
        L.derivWeierstrassP b * weierstrassZeta L z₀ + 2 * L.weierstrassP b ^ 2] Q = 0 := by
    exact hs.symm.trans (by simpa using hz)
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero n (pow_ne_zero 3 hsig))
