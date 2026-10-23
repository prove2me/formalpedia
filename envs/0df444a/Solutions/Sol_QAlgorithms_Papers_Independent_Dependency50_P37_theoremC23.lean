-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.theoremC23
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:39.731429+00:00
-- url     : https://prove2.me/submissions/2b70baa2-2a3e-462d-abb4-8f6f81970008

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

open scoped BigOperators Matrix ComplexOrder
open Filter Topology

namespace X7Q10M

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P37
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

variable {d : ℕ}

lemma X7_two_step (s : ℕ → ℂ) (q : ℂ) (hq : ‖q‖ < 1) (hs : ∀ n, s (n + 2) = q * s n) :
    Tendsto s atTop (𝓝 0) := by
  set M := ‖s 0‖ + ‖s 1‖
  have hb : ∀ n, ‖s n‖ ≤ ‖q‖ ^ (n / 2) * M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | n
      · simp [M]
      · simp [M]
      · rw [hs, norm_mul, show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]
        have := ih n (by omega)
        calc ‖q‖ * ‖s n‖ ≤ ‖q‖ * (‖q‖ ^ (n / 2) * M) := by gcongr
          _ = ‖q‖ ^ (n / 2) * ‖q‖ * M := by ring
  have hgeo : Tendsto (fun n : ℕ => ‖q‖ ^ (n / 2) * M) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
      (tendsto_atTop_atTop.2 fun b => ⟨b * 2, fun a ha => (Nat.le_div_iff_mul_le two_pos).2 ha⟩ :
        Tendsto (fun n : ℕ => n / 2) atTop atTop)
    simpa using this.mul_const M
  exact squeeze_zero_norm hb hgeo

lemma X7_diag_iter (Φ : Dynamics d) (A : Operator d)
    (hdiag : ∀ Y : Operator d, ∀ i, Φ Y i i = ∑ k, A i k * Y k k) (n : ℕ) (X : Operator d) (i : Fin d) :
    (Nat.iterate Φ n X) i i = ((A ^ n) *ᵥ fun k => X k k) i := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hdiag, pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct] at ih ⊢
    exact Finset.sum_congr rfl fun k _ => by rw [ih k]

lemma X7_kraus_cs {m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (a b i j : Fin d) :
    ‖krausApply E (Matrix.single a b 1) i j‖ ^ 2 ≤
      (krausApply E (Matrix.single a a 1) i i).re * (krausApply E (Matrix.single b b 1) j j).re := by
  have hent : ∀ a b i j, krausApply E (Matrix.single a b 1) i j = ∑ k, E k i a * star (E k j b) := by
    intro a b i j
    simp only [krausApply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, ite_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [hent, hent, hent]
  have h1 : ∀ x : ℂ, (x * star x).re = ‖x‖ ^ 2 := fun x => by
    rw [Complex.star_def, Complex.mul_conj']; norm_cast
  simp only [Complex.re_sum, h1]
  calc ‖∑ k, E k i a * star (E k j b)‖ ^ 2 ≤ (∑ k, ‖E k i a‖ * ‖E k j b‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, norm_star]
    _ ≤ (∑ k, ‖E k i a‖ ^ 2) * ∑ k, ‖E k j b‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma X7_col_unit {A : Operator d} (hA : ColumnStochastic A) {a b : Fin d} (h : (A a b).re = 1) :
    A *ᵥ Pi.single b 1 = Pi.single a 1 := by
  funext c
  simp only [Matrix.mulVec_single, mul_one]
  by_cases hc : c = a
  · subst hc; apply Complex.ext <;> simp [h, (hA.1 c b).1]
  · rw [Pi.single_apply, if_neg hc]
    have hsum : (∑ x, A x b).re = 1 := by rw [hA.2 b]; simp
    rw [Complex.re_sum] at hsum
    have hle : ∑ x ∈ ({c, a} : Finset (Fin d)), (A x b).re ≤ ∑ x, (A x b).re :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => (hA.1 x b).2
    rw [Finset.sum_pair hc, h, hsum] at hle
    have : (A c b).re = 0 := le_antisymm (by linarith) (hA.1 c b).2
    apply Complex.ext <;> simp [this, (hA.1 c b).1]

lemma X7_entry_le_one {A : Operator d} (hA : ColumnStochastic A) (a b : Fin d) : (A a b).re ≤ 1 := by
  have hsum : (∑ x, A x b).re = 1 := by rw [hA.2 b]; simp
  rw [Complex.re_sum] at hsum
  rw [← hsum]
  exact Finset.single_le_sum (f := fun x => (A x b).re) (fun x _ => (hA.1 x b).2) (Finset.mem_univ a)

lemma X7_single_ne {i j : Fin d} (hij : i ≠ j) : (Pi.single i (1 : ℂ) : Fin d → ℂ) ≠ Pi.single j 1 := by
  intro h
  have := congrFun h i
  simp [Pi.single_apply, hij] at this

/-- generic mixing transfer -/
theorem X7_mixing_iff (Φ : Dynamics d) (A : Operator d) (q : Fin d → Fin d → ℂ)
    (hdiag : ∀ Y : Operator d, ∀ i, Φ Y i i = ∑ k, A i k * Y k k)
    (htwo : ∀ Y : Operator d, ∀ i j, i ≠ j → Φ (Φ Y) i j = q i j * Y i j)
    (hq : MatrixMixing A → ∀ i j, i ≠ j → ‖q i j‖ < 1) :
    Mixing Φ ↔ MatrixMixing A := by
  constructor
  · rintro ⟨ρ, hρ, hlim⟩
    refine ⟨fun i => ρ i i, fun i => ?_, ?_, fun x => ?_⟩
    · have h := hρ.1.diag_nonneg (i := i)
      exact ⟨(Complex.nonneg_iff.1 h).2.symm, (Complex.nonneg_iff.1 h).1⟩
    · have := hρ.2; simpa [Matrix.trace] using this
    · have h := hlim (Matrix.diagonal x)
      rw [tendsto_pi_nhds]
      intro i
      have h2 := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) i
      simp only [X7_diag_iter Φ A hdiag] at h2
      simpa [Matrix.trace, Matrix.diagonal] using h2
  · intro hmix
    have hq' := hq hmix
    obtain ⟨v, hv, hv1, hlim⟩ := hmix
    refine ⟨Matrix.diagonal v, ⟨?_, ?_⟩, fun X => ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact Complex.nonneg_iff.2 ⟨(hv i).2, (hv i).1.symm⟩
    · simpa [Matrix.trace] using hv1
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      by_cases hij : i = j
      · subst hij
        simp only [X7_diag_iter Φ A hdiag]
        have := tendsto_pi_nhds.1 (hlim fun k => X k k) i
        simpa [Matrix.trace, Matrix.diagonal] using this
      · have : Tendsto (fun n => (Nat.iterate Φ n X) i j) atTop (𝓝 0) := by
          refine X7_two_step _ (q i j) (hq' i j hij) fun n => ?_
          rw [show n + 2 = (n + 1) + 1 by rfl, Function.iterate_succ_apply',
            Function.iterate_succ_apply', htwo _ i j hij]
        simpa [Matrix.diagonal, hij] using this

lemma X7_fixed_contra {A : Operator d} (hmix : MatrixMixing A) {i j : Fin d} (hij : i ≠ j)
    (hi : A *ᵥ Pi.single i 1 = Pi.single i 1) (hj : A *ᵥ Pi.single j 1 = Pi.single j 1) : False := by
  obtain ⟨v, -, -, hlim⟩ := hmix
  have key : ∀ a : Fin d, A *ᵥ Pi.single a 1 = Pi.single a 1 → (Pi.single a 1 : Fin d → ℂ) = v := by
    intro a ha
    have hp : ∀ n, (A ^ n) *ᵥ Pi.single a 1 = Pi.single a 1 := by
      intro n; induction n with
      | zero => rw [pow_zero, Matrix.one_mulVec]
      | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, ha, ih]
    have h := hlim (Pi.single a 1)
    simp only [hp] at h
    have h2 : (∑ x, (Pi.single a (1 : ℂ) : Fin d → ℂ) x) = 1 := by simp
    rw [h2, one_smul] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  exact X7_single_ne hij ((key i hi).trans (key j hj).symm)

lemma X7_swap_contra {A : Operator d} (hmix : MatrixMixing A) {i j : Fin d} (hij : i ≠ j)
    (hi : A *ᵥ Pi.single i 1 = Pi.single j 1) (hj : A *ᵥ Pi.single j 1 = Pi.single i 1) : False := by
  obtain ⟨v, -, -, hlim⟩ := hmix
  have hp : ∀ n, (A ^ (2 * n)) *ᵥ Pi.single i 1 = Pi.single i 1 ∧
      (A ^ (2 * n + 1)) *ᵥ Pi.single i 1 = Pi.single j 1 := by
    intro n; induction n with
    | zero => exact ⟨by rw [Nat.mul_zero, pow_zero, Matrix.one_mulVec],
        by rw [Nat.mul_zero, zero_add, pow_one, hi]⟩
    | succ n ih =>
      have e1 : A ^ (2 * (n + 1)) = A * A ^ (2 * n + 1) := by rw [← pow_succ']; ring_nf
      have e2 : A ^ (2 * (n + 1) + 1) = A * A ^ (2 * (n + 1)) := by rw [← pow_succ']
      refine ⟨?_, ?_⟩
      · rw [e1, ← Matrix.mulVec_mulVec, ih.2, hj]
      · rw [e2, ← Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, ih.2, hj, hi]
  have h := hlim (Pi.single i 1)
  have h2 : (∑ x, (Pi.single i (1 : ℂ) : Fin d → ℂ) x) = 1 := by simp
  rw [h2, one_smul] at h
  have ha : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have hb : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have h3 := h.comp ha
  have h4 := h.comp hb
  have e3 : ((fun n => A ^ n *ᵥ Pi.single i 1) ∘ fun n : ℕ => 2 * n) = fun _ => Pi.single i 1 := by
    funext n; exact (hp n).1
  have e4 : ((fun n => A ^ n *ᵥ Pi.single i 1) ∘ fun n : ℕ => 2 * n + 1) = fun _ => Pi.single j 1 := by
    funext n; exact (hp n).2
  rw [e3] at h3
  rw [e4] at h4
  exact X7_single_ne hij ((tendsto_nhds_unique tendsto_const_nhds h3).trans
    (tendsto_nhds_unique tendsto_const_nhds h4).symm)

lemma X7_prod_lt_one {A : Operator d} (hA : ColumnStochastic A) (a b c e : Fin d)
    (h : ¬ ((A a b).re = 1 ∧ (A c e).re = 1)) : (A a b).re * (A c e).re < 1 := by
  have h1 := X7_entry_le_one hA a b
  have h2 := X7_entry_le_one hA c e
  have h0 := (hA.1 a b).2
  have h0' := (hA.1 c e).2
  by_contra hc
  push Not at hc
  apply h
  constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h2), mul_nonneg h0' (sub_nonneg.2 h1)]

theorem X7_cduc_mixing {A B : Operator d} (hA : ColumnStochastic A) (hch : IsChannel (cduc A B)) :
    Mixing (cduc A B) ↔ MatrixMixing A := by
  obtain ⟨m, E, -, hE⟩ := hch
  refine X7_mixing_iff (cduc A B) A (fun i j => B i j * B i j) (fun Y i => by simp [cduc])
    (fun Y i j hij => by simp [cduc, hij]; ring) ?_
  intro hmix i j hij
  have hcs := X7_kraus_cs E i j i j
  simp only [← hE] at hcs
  have e1 : cduc A B (Matrix.single i j 1) i j = B i j := by simp [cduc, hij]
  have e2 : ∀ a, cduc A B (Matrix.single a a 1) a a = A a a := fun a => by
    simp [cduc, Matrix.single_apply]
  rw [e1, e2, e2] at hcs
  have hlt : (A i i).re * (A j j).re < 1 := by
    refine X7_prod_lt_one hA i i j j fun ⟨h1, h2⟩ => ?_
    exact X7_fixed_contra hmix hij (X7_col_unit hA h1) (X7_col_unit hA h2)
  rw [norm_mul, ← sq]
  exact lt_of_le_of_lt hcs hlt

theorem X7_duc_mixing {A C : Operator d} (hA : ColumnStochastic A) (hch : IsChannel (duc A C)) :
    Mixing (duc A C) ↔ MatrixMixing A := by
  obtain ⟨m, E, -, hE⟩ := hch
  refine X7_mixing_iff (duc A C) A (fun i j => C i j * C j i) (fun Y i => by simp [duc])
    (fun Y i j hij => by simp [duc, hij, Ne.symm hij]; ring) ?_
  intro hmix i j hij
  have e1 : ∀ a b, a ≠ b → duc A C (Matrix.single b a 1) a b = C a b := fun a b hab => by
    simp [duc, hab]
  have e2 : ∀ a b, duc A C (Matrix.single b b 1) a a = A a b := fun a b => by
    simp [duc, Matrix.single_apply]
  have hcs1 := X7_kraus_cs E j i i j
  have hcs2 := X7_kraus_cs E i j j i
  simp only [← hE] at hcs1 hcs2
  rw [e1 i j hij, e2, e2] at hcs1
  rw [e1 j i (Ne.symm hij), e2, e2] at hcs2
  set P := (A i j).re * (A j i).re
  have hP0 : 0 ≤ P := mul_nonneg (hA.1 i j).2 (hA.1 j i).2
  have hlt : P < 1 := by
    refine X7_prod_lt_one hA i j j i fun ⟨h1, h2⟩ => ?_
    exact X7_swap_contra hmix hij (X7_col_unit hA h2) (X7_col_unit hA h1)
  have hsq : ‖C i j * C j i‖ ^ 2 ≤ P ^ 2 := by
    rw [norm_mul, mul_pow, sq P]
    have : (A j i).re * (A i j).re = P := by simp only [P]; ring
    rw [this] at hcs2
    exact mul_le_mul hcs1 hcs2 (sq_nonneg _) hP0
  have : ‖C i j * C j i‖ ≤ P := (pow_le_pow_iff_left₀ (norm_nonneg _) hP0 two_ne_zero).1 hsq
  exact lt_of_le_of_lt this hlt

end X7Q10M

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)
open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)
open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P37 X7Q10M in
theorem solution {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : ColumnStochastic A) :
    (∀ B : Operator d, IsChannel (cduc A B) → (Mixing (cduc A B) ↔ MatrixMixing A)) ∧
    (∀ C : Operator d, IsChannel (duc A C) → (Mixing (duc A C) ↔ MatrixMixing A)) :=
  ⟨fun _ hch => X7_cduc_mixing hA hch, fun _ hch => X7_duc_mixing hA hch⟩
