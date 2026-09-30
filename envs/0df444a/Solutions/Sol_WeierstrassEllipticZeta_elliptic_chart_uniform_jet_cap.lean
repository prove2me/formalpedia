-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_chart_uniform_jet_cap
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T23:42:54.961784+00:00
-- url     : https://prove2.me/submissions/c7041de9-2435-4357-95f4-d5553cd510d8

import Definitions.Def_WeierstrassEllipticZeta_FiniteChartJets
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_WeierstrassEllipticZeta_CappedChartJets


noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial

private lemma finite_polynomial_family_span {σ : Type*} [Finite σ]
    (p : ℕ → MvPolynomial σ ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ k, p k ∈ Ideal.span (p '' Set.Iio N) := by
  let J : ℕ →o Ideal (MvPolynomial σ ℂ) :=
    ⟨fun n => Ideal.span (p '' Set.Iio n), fun _ _ h =>
      Ideal.span_mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi h))⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) J
  refine ⟨N + 1, by omega, ?_⟩
  intro k
  change p k ∈ J (N + 1)
  rw [← hN (N + 1) (by omega), hN (max (N + 1) (k + 1)) (by omega)]
  exact Ideal.subset_span ⟨k, by simp only [Set.mem_Iio]; omega, rfl⟩

/-- Universal coefficient variables give one ideal-membership cutoff for a
whole bounded-degree vector space, before specialization at any coefficients. -/
theorem polynomial_linear_sequence_uniform_span
    (T : ℕ → Module.End ℂ (MvPolynomial (Fin 4) ℂ)) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : MvPolynomial (Fin 4) ℂ, p.totalDegree ≤ d →
      ∀ k, T k p ∈ Ideal.span ((fun j => T j p) '' Set.Iio N) := by
  classical
  let V := restrictTotalDegree (Fin 4) ℂ d
  let ι := Fin (Module.finrank ℂ V)
  let b : Module.Basis ι ℂ V := Module.finBasis ℂ V
  let q (k : ℕ) : MvPolynomial (ι ⊕ Fin 4) ℂ :=
    ∑ i : ι, X (Sum.inl i) * rename Sum.inr (T k (b i).val)
  obtain ⟨N, hNpos, hN⟩ := finite_polynomial_family_span q
  refine ⟨N, hNpos, ?_⟩
  intro p hp k
  let pV : V := ⟨p, (mem_restrictTotalDegree (Fin 4) d p).mpr hp⟩
  let a : ι → ℂ := fun i => b.repr pV i
  let φ : MvPolynomial (ι ⊕ Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    aeval (Sum.elim (fun i => C (a i)) X)
  have hrepr : ∑ i : ι, a i • (b i).val = p := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using
      congrArg V.subtype (b.sum_repr pV)
  have hφ (j : ℕ) : φ (q j) = T j p := by
    calc
      _ = ∑ i : ι, C (a i) * T j (b i).val := by
        simp only [φ, q, map_sum, map_mul, aeval_X, aeval_rename,
          Function.comp_def, Sum.elim_inl, Sum.elim_inr, aeval_X_left_apply]
      _ = T j (∑ i : ι, a i • (b i).val) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [smul_eq_C_mul] using ((T j).map_smul (a i) (b i).val).symm
      _ = T j p := by rw [hrepr]
  have hspan : Ideal.span (q '' Set.Iio N) ≤
      (Ideal.span ((fun j => T j p) '' Set.Iio N)).comap φ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change φ (q j) ∈ Ideal.span ((fun j => T j p) '' Set.Iio N)
    rw [hφ]
    exact Ideal.subset_span ⟨j, hj, rfl⟩
  have hmem := hspan (hN k)
  change φ (q k) ∈ Ideal.span ((fun j => T j p) '' Set.Iio N) at hmem
  simpa only [hφ] using hmem

theorem chart_uniform_jet_span (g₂ g₃ : ℂ) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ d, 0 < B d) ∧
      ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
        ∀ k, (extensionChartDerivation g₂ g₃ c)^[k] p ∈
          Ideal.span ((fun j => (extensionChartDerivation g₂ g₃ c)^[j] p) '' Set.Iio (B d)) := by
  choose N hNpos hN using fun (c : Fin 2) (d : ℕ) =>
    polynomial_linear_sequence_uniform_span
      (fun k => (extensionChartDerivation g₂ g₃ c).toLinearMap ^ k) d
  let B (d : ℕ) := (Finset.range (d + 1)).sup (fun e => max (N 0 e) (N 1 e))
  have hNB (c : Fin 2) (d : ℕ) : N c d ≤ B d := by
    apply le_trans (b := max (N 0 d) (N 1 d))
    · fin_cases c <;> simp
    · exact Finset.le_sup (f := fun e => max (N 0 e) (N 1 e)) (by simp)
  refine ⟨B, (fun _ _ h => Finset.sup_mono (Finset.range_mono
    (Nat.add_le_add_right h 1))), (fun d => lt_of_lt_of_le (hNpos 0 d) (hNB 0 d)), ?_⟩
  intro d c p hp k
  have hmem := hN c d p hp k
  simp only [Module.End.pow_apply] at hmem
  exact Ideal.span_mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi (hNB c d))) hmem

end WeierstrassEllipticZeta


noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial

private lemma pderiv_degree {σ : Type} (p : MvPolynomial σ ℂ) (i : σ)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, heq⟩ := (pderiv i p).support.exists_mem_eq_sup
    (by simpa using h) (fun m => m.sum fun _ e => e)
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have := mem_support_iff.mp hm
    rw [coeff_pderiv] at this
    exact (mul_ne_zero_iff.mp this).1
  have hle := le_totalDegree (mem_support_iff.mpr hcoeff)
  simpa [totalDegree, heq, Finsupp.sum_add_index'] using hle

private lemma derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (p : MvPolynomial σ ℂ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma derivation_degree {σ : Type} [Fintype σ]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2) (p : MvPolynomial σ ℂ) :
    (D p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  have hrepr : D = ∑ i, D (X i) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ i, D (X i) * pderiv i p := by
    conv_lhs => rw [hrepr]
    simp [derivation_sum_apply]
  rw [hvalue]
  apply totalDegree_finsetSum_le
  intro i _
  by_cases hi : pderiv i p = 0
  · simp [hi]
  have hp := pderiv_degree p i hi
  have hmul := totalDegree_mul (D (X i)) (pderiv i p)
  have := hD i
  omega

private theorem chart_derivation_degree (g₂ g₃ : ℂ) (c : Fin 2) (i : Fin 4) :
    (extensionChartDerivation g₂ g₃ c (X i)).totalDegree ≤ 2 := by
  have hsub (p q : MvPolynomial (Fin 4) ℂ) (hp : p.totalDegree ≤ 2)
      (hq : q.totalDegree ≤ 2) : (p - q).totalDegree ≤ 2 := by
    have hh := totalDegree_add p (-q)
    simpa [totalDegree, sub_eq_add_neg] using hh.trans (max_le hp (by simpa [totalDegree] using hq))
  have hadd (p q : MvPolynomial (Fin 4) ℂ) (hp : p.totalDegree ≤ 2)
      (hq : q.totalDegree ≤ 2) : (p + q).totalDegree ≤ 2 :=
    (totalDegree_add p q).trans (max_le hp hq)
  have hs (a : ℂ) (j : Fin 4) : (C a * X j ^ 2).totalDegree ≤ 2 := by
    apply (totalDegree_mul (C a) (X j ^ 2)).trans
    simpa using totalDegree_pow (X j : MvPolynomial (Fin 4) ℂ) 2
  have hm (a : ℂ) (j k : Fin 4) : (C a * X j * X k).totalDegree ≤ 2 := by
    have h₁ := totalDegree_mul (C a * X j) (X k)
    have h₂ := totalDegree_mul (C a) (X j)
    simp only [totalDegree_C, totalDegree_X, zero_add] at h₁ h₂
    omega
  fin_cases c <;> fin_cases i <;> simp [extensionChartDerivation]
  · exact hsub _ _ (hs 6 1) (by simp)
  · exact hadd _ _ (by simpa only [map_neg, neg_mul] using hs (-6) 2) (hs (g₂ / 2) 1)
  · exact hsub _ _ (hsub _ _ (by simp) (hm g₂ 1 2)) (hs (3 * g₃ / 2) 1)
  · exact hsub _ _ (by simpa only [map_mul, map_neg, neg_mul] using hs (-2 * g₂) 2)
      (by simpa only [map_mul] using hm (3 * g₃) 1 2)

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

theorem chart_cubic_derivation_zero (g₂ g₃ : ℂ) (c : Fin 2) :
    extensionChartDerivation g₂ g₃ c (extensionChartCubic g₂ g₃ c) = 0 := by
  apply MvPolynomial.funext
  intro v
  fin_cases c <;> simp [extensionChartDerivation, extensionChartCubic,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] <;> ring

theorem chart_normalized_jet_degree (L : PeriodPair) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (c : Fin 2) (k : ℕ) :
    ((extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
      m + 2 * n + k := by
  induction k with
  | zero => simpa using normalization_degree c m n Q hQ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (derivation_degree _ (chart_derivation_degree L.g₂ L.g₃ c) _).trans (by omega)

theorem chart_cubic_degree (g₂ g₃ : ℂ) (c : Fin 2) :
    (extensionChartCubic g₂ g₃ c).totalDegree ≤ 3 := by
  have hadd (p q : MvPolynomial (Fin 4) ℂ) (hp : p.totalDegree ≤ 3)
      (hq : q.totalDegree ≤ 3) : (p + q).totalDegree ≤ 3 :=
    (totalDegree_add p q).trans (max_le hp hq)
  have hsub (p q : MvPolynomial (Fin 4) ℂ) (hp : p.totalDegree ≤ 3)
      (hq : q.totalDegree ≤ 3) : (p - q).totalDegree ≤ 3 :=
    (totalDegree_sub p q).trans (max_le hp hq)
  have hp (a : ℂ) (i : Fin 4) (n : ℕ) (hn : n ≤ 3) :
      (C a * X i ^ n).totalDegree ≤ 3 :=
    (totalDegree_mul _ _).trans (by simpa using hn)
  have hm (a : ℂ) (i j : Fin 4) : (C a * X i ^ 2 * X j).totalDegree ≤ 3 := by
    have h := totalDegree_mul (C a * X i ^ 2) (X j)
    have h' := totalDegree_mul (C a : MvPolynomial (Fin 4) ℂ) (X i ^ 2)
    simp only [totalDegree_C, totalDegree_X_pow, totalDegree_X, zero_add] at h h'
    omega
  fin_cases c <;> simp only [extensionChartCubic, ↓reduceIte]
  · exact hadd _ _ (hadd _ _ (hsub _ _ (by simp) (hp 4 1 3 le_rfl))
      (by simpa using hp g₂ 1 1 (by omega))) (by simp)
  · exact hadd _ _ (hadd _ _ (hsub _ _ (by simp) (hp 4 2 3 le_rfl))
      (hm g₂ 1 2)) (hp g₃ 1 3 le_rfl)

end WeierstrassEllipticZeta


namespace WeierstrassEllipticZeta
open MvPolynomial

private theorem chart_jet_ideal_mono (L : PeriodPair) (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2) {a b : ℕ} (hab : a ≤ b) :
    extensionChartJetIdeal L Q c a ≤ extensionChartJetIdeal L Q c b := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine Fin.cases ?_ (fun k => ?_) j
  · exact Ideal.subset_span ⟨0, rfl⟩
  · exact Ideal.subset_span ⟨(⟨k.val, by have := k.isLt; omega⟩ : Fin (b + 1)).succ, rfl⟩

private theorem chart_jet_ideal_cutoff (L : PeriodPair) (Q : MvPolynomial (Fin 7) ℂ)
    (c : Fin 2) (N : ℕ)
    (hN : ∀ k, (extensionChartDerivation L.g₂ L.g₃ c)^[k] (extensionChartNormalize c Q) ∈
      Ideal.span ((fun j => (extensionChartDerivation L.g₂ L.g₃ c)^[j]
        (extensionChartNormalize c Q)) '' Set.Iio N)) (T : ℕ) :
    extensionChartJetIdeal L Q c T = extensionChartJetIdeal L Q c (min T N) := by
  by_cases hTN : T ≤ N
  · rw [min_eq_left hTN]
  rw [min_eq_right (by omega : N ≤ T)]
  apply le_antisymm
  · have hspan : Ideal.span ((fun j => (extensionChartDerivation L.g₂ L.g₃ c)^[j]
        (extensionChartNormalize c Q)) '' Set.Iio N) ≤ extensionChartJetIdeal L Q c N := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      exact Ideal.subset_span ⟨(⟨j, by have : j < N := hj; omega⟩ : Fin (N + 1)).succ, rfl⟩
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact hspan (hN k.val)
  · exact chart_jet_ideal_mono L Q c (by omega)


end WeierstrassEllipticZeta

open TranscendenceTheory WeierstrassEllipticZeta

theorem solution (L : PeriodPair) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ d, 0 < B d) ∧
      ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        ∀ (c : Fin 2) (T : ℕ),
          extensionChartJetIdeal L Q c T =
            extensionChartJetIdeal L Q c (min T (B (m + 2 * n))) ∧
          ∀ j : Fin (min T (B (m + 2 * n)) + 2),
            (extensionChartJetGenerator L Q c (min T (B (m + 2 * n))) j).totalDegree ≤
              max 3 (m + 2 * n + B (m + 2 * n)) := by
  obtain ⟨B, hmono, hpos, hspan⟩ := chart_uniform_jet_span L.g₂ L.g₃
  refine ⟨B, hmono, hpos, ?_⟩
  intro m n Q hQ c T
  have hdeg : (extensionChartNormalize c Q).totalDegree ≤ m + 2 * n := by
    simpa using chart_normalized_jet_degree L Q m n hQ c 0
  refine ⟨chart_jet_ideal_cutoff L Q c (B (m + 2 * n))
    (hspan (m + 2 * n) c (extensionChartNormalize c Q) hdeg) T, ?_⟩
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact (chart_cubic_degree L.g₂ L.g₃ c).trans (le_max_left _ _)
  · exact (chart_normalized_jet_degree L Q m n hQ c k.val).trans
      ((by have := k.isLt; have := min_le_right T (B (m + 2 * n)); omega :
        m + 2 * n + k.val ≤ m + 2 * n + B (m + 2 * n)).trans (le_max_right _ _))
