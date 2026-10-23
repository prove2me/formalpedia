-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.coherence_iff_positive_advantage
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T01:07:37.877006+00:00
-- url     : https://prove2.me/submissions/655c8380-4a69-4261-a3e4-853ebb5439c1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

set_option autoImplicit false

noncomputable section

namespace P38Aux

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38
open scoped ComplexConjugate Matrix ComplexOrder

lemma ee_conj {d : ℕ} (E : Fin d → ℝ) (U Y : Matrix (Fin d) (Fin d) ℂ) :
    energyExpectation E (U * Y * Uᴴ) =
      ∑ k, E k * (∑ m, ∑ l, U k l * Y l m * star (U k m)).re := by
  simp [energyExpectation, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

lemma orbit_lb {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    -(∑ k, |E k| * ∑ m, ∑ l, ‖Y l m‖) ≤ energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * Y *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  rw [ee_conj, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hU := U.2
  have hz : ‖∑ m, ∑ l, (U : Matrix (Fin d) (Fin d) ℂ) k l * Y l m *
      star ((U : Matrix (Fin d) (Fin d) ℂ) k m)‖ ≤ ∑ m, ∑ l, ‖Y l m‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
    have h1 := entry_norm_bound_of_unitary hU k l
    have h2 := entry_norm_bound_of_unitary hU k m
    calc ‖(U : Matrix (Fin d) (Fin d) ℂ) k l‖ * ‖Y l m‖ * ‖(U : Matrix (Fin d) (Fin d) ℂ) k m‖
        ≤ 1 * ‖Y l m‖ * 1 := by gcongr
      _ = ‖Y l m‖ := by ring
  set z := ∑ m, ∑ l, (U : Matrix (Fin d) (Fin d) ℂ) k l * Y l m *
      star ((U : Matrix (Fin d) (Fin d) ℂ) k m)
  have hre : |z.re| ≤ ∑ m, ∑ l, ‖Y l m‖ := (Complex.abs_re_le_norm z).trans hz
  have := neg_abs_le (E k * z.re)
  rw [abs_mul] at this
  have h5 := mul_le_mul_of_nonneg_left hre (abs_nonneg (E k))
  linarith

lemma orbit_bdd {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    BddBelow {r | ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      r = energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * Y *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)} := by
  refine ⟨-(∑ k, |E k| * ∑ m, ∑ l, ‖Y l m‖), ?_⟩
  rintro r ⟨U, rfl⟩
  exact orbit_lb E Y U

lemma passive_ge {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    -(∑ k, |E k| * ∑ m, ∑ l, ‖Y l m‖) ≤ passiveEnergy E Y := by
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro r ⟨U, rfl⟩
  exact orbit_lb E Y U

lemma passive_le {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    passiveEnergy E Y ≤ energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * Y *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) :=
  csInf_le (orbit_bdd E Y) ⟨U, rfl⟩

lemma ee_diag {d : ℕ} (E : Fin d → ℝ) (U Y : Matrix (Fin d) (Fin d) ℂ)
    (hY : ∀ l m, l ≠ m → Y l m = 0) :
    energyExpectation E (U * Y * Uᴴ) = ∑ k, E k * ∑ l, ‖U k l‖ ^ 2 * (Y l l).re := by
  rw [ee_conj]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Finset.sum_comm]
  have : ∀ l, ∑ m, U k l * Y l m * star (U k m) = U k l * Y l l * star (U k l) := by
    intro l
    rw [Finset.sum_eq_single l]
    · intro m _ hm; rw [hY l m (Ne.symm hm)]; simp
    · simp
  simp_rw [this]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : U k l * Y l l * star (U k l) = Y l l * ((‖U k l‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [RCLike.star_def]
    ring
  rw [this, Complex.re_mul_ofReal]
  ring

lemma unistoch {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun k l => ‖(U : Matrix (Fin d) (Fin d) ℂ) k l‖ ^ 2) ∈
      doublyStochastic ℝ (Fin d) := by
  rw [mem_doublyStochastic_iff_sum]
  have h1 : (U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have h2 : star (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  refine ⟨fun i j => by simp, fun k => ?_, fun l => ?_⟩
  · have := congrFun (congrFun h1 k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at this
    have h' : ∑ x, (((‖(U : Matrix (Fin d) (Fin d) ℂ) k x‖ ^ 2 : ℝ)) : ℂ) = 1 := by
      rw [← this]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      simp
    simp only [Matrix.of_apply]
    exact_mod_cast h'
  · have := congrFun (congrFun h2 l) l
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at this
    have h' : ∑ x, (((‖(U : Matrix (Fin d) (Fin d) ℂ) x l‖ ^ 2 : ℝ)) : ℂ) = 1 := by
      rw [← this]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      simp [mul_comm]
    simp only [Matrix.of_apply]
    exact_mod_cast h'

lemma perm_unitary {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

lemma perm_normsq {d : ℕ} (σ : Equiv.Perm (Fin d)) (k l : Fin d) :
    ‖σ.permMatrix ℂ k l‖ ^ 2 = σ.permMatrix ℝ k l := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

lemma diag_off {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hI : measurementIncoherent M)
    (u : Fin n) (l m : Fin d) (h : l ≠ m) : M u l m = 0 := by
  have := congrFun (congrFun (hI u) l) m
  rw [← this]
  simp [energyDephasing, Matrix.diagonal_apply_ne _ h]

lemma diag_real {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) (u : Fin n)
    (k : Fin d) : M u k k = (((M u k k).re : ℝ) : ℂ) ∧ 0 ≤ (M u k k).re := by
  have h := (hM.1 u).diag_nonneg (i := k)
  obtain ⟨h1, h2⟩ := Complex.le_def.mp h
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  exact ⟨Complex.ext (by simp) (by simpa using h2.symm), h1⟩

lemma adv_elem {d n : ℕ} (E : Fin d → ℝ) (M : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    observationalErgotropy E M X - incoherentErgotropy E X =
      passiveEnergy E (energyDephasing X) - passiveEnergy E (ergotropicCoarseGraining M X) := by
  have : energyExpectation E (energyDephasing X) = energyExpectation E X := by
    simp [energyExpectation, energyDephasing]
  simp only [observationalErgotropy, incoherentErgotropy, this]
  ring

lemma incoh_le {d n : ℕ} (E : Fin d → ℝ) {M : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hM : IsPOVM M) (hI : measurementIncoherent M) (X : Matrix (Fin d) (Fin d) ℂ) :
    passiveEnergy E (energyDephasing X) ≤ passiveEnergy E (ergotropicCoarseGraining M X) := by
  classical
  set m : Fin n → Fin d → ℝ := fun u k => (M u k k).re with hm
  set tr : Fin n → ℝ := fun u => ∑ k, m u k with htr
  set q : Fin d → ℝ := fun k => (X k k).re with hq
  set T : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun l k =>
    ∑ u, if tr u = 0 then 0 else m u l * m u k / tr u with hT
  have hMr : ∀ u k, M u k k = ((m u k : ℝ) : ℂ) := fun u k => (diag_real hM u k).1
  have hm0 : ∀ u k, 0 ≤ m u k := fun u k => (diag_real hM u k).2
  have htr0 : ∀ u, 0 ≤ tr u := fun u => Finset.sum_nonneg fun k _ => hm0 u k
  have htrace : ∀ u, (M u).trace = ((tr u : ℝ) : ℂ) := by
    intro u
    simp only [Matrix.trace, Matrix.diag, htr, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => hMr u k
  have hz : ∀ u, tr u = 0 → ∀ k, m u k = 0 := by
    intro u h k
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hm0 u k)).mp h k (Finset.mem_univ _)
  have hsum1 : ∀ l, ∑ u, m u l = 1 := by
    intro l
    have := congrFun (congrFun hM.2 l) l
    rw [Matrix.sum_apply, Matrix.one_apply_eq] at this
    have h2 := congrArg Complex.re this
    simpa [Complex.re_sum] using h2
  have hTsymm : ∀ l k, T l k = T k l := by
    intro l k
    simp only [hT, Matrix.of_apply]
    exact Finset.sum_congr rfl fun u _ => by rw [mul_comm (m u l)]
  have hTrow : ∀ l, ∑ k, T l k = 1 := by
    intro l
    simp only [hT, Matrix.of_apply]
    rw [Finset.sum_comm, ← hsum1 l]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : tr u = 0
    · simp [h, hz u h l]
    · simp only [h, if_false]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      change m u l * tr u / tr u = m u l
      field_simp
  have hTds : T ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun l k => ?_, hTrow, fun k => ?_⟩
    · simp only [hT, Matrix.of_apply]
      refine Finset.sum_nonneg fun u _ => ?_
      split_ifs
      · exact le_refl _
      · exact div_nonneg (mul_nonneg (hm0 u l) (hm0 u k)) (htr0 u)
    · rw [← hTrow k]
      exact Finset.sum_congr rfl fun l _ => hTsymm l k
  have hCoff : ∀ l k, l ≠ k → ergotropicCoarseGraining M X l k = 0 := by
    intro l k hlk
    simp only [ergotropicCoarseGraining, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs <;> simp [diag_off hI u l k hlk]
  have htrMX : ∀ u, (M u * X).trace = ∑ k, ((m u k : ℝ) : ℂ) * X k k := by
    intro u
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [hMr]
    · intro j _ hj
      rw [diag_off hI u k j (Ne.symm hj)]
      simp
    · simp
  have hCdiag : ∀ l, (ergotropicCoarseGraining M X l l).re = ∑ k, T l k * q k := by
    intro l
    simp only [ergotropicCoarseGraining, Matrix.sum_apply, Complex.re_sum, hT, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [htrace u]
    by_cases h : tr u = 0
    · simp [h]
    · have h' : ((tr u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
      simp only [h', h, if_false, Matrix.smul_apply, smul_eq_mul, htrMX]
      rw [hMr u l]
      have : (∑ k, ((m u k : ℝ) : ℂ) * X k k) / ((tr u : ℝ) : ℂ) * ((m u l : ℝ) : ℂ) =
          ((m u l / tr u : ℝ) : ℂ) * ∑ k, ((m u k : ℝ) : ℂ) * X k k := by
        push_cast
        ring
      rw [this, Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.re_ofReal_mul]
      simp only [hq]
      ring
  set F : Matrix (Fin d) (Fin d) ℝ → ℝ := fun D => ∑ k, E k * (D *ᵥ q) k with hF
  have hFlin : IsLinearMap ℝ F := by
    constructor
    · intro A B
      simp only [hF, Matrix.add_mulVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · intro c A
      simp only [hF, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
  have hdeltaoff : ∀ l k, l ≠ k → energyDephasing X l k = 0 := fun l k h => by
    simp [energyDephasing, Matrix.diagonal_apply_ne _ h]
  have hperm : ∀ σ : Equiv.Perm (Fin d),
      passiveEnergy E (energyDephasing X) ≤ F (σ.permMatrix ℝ) := by
    intro σ
    have := passive_le E (energyDephasing X) ⟨σ.permMatrix ℂ, perm_unitary σ⟩
    refine this.trans (le_of_eq ?_)
    rw [ee_diag E _ _ hdeltaoff]
    simp only [hF, Matrix.mulVec, dotProduct, perm_normsq, energyDephasing,
      Matrix.diagonal_apply_eq, hq]
  have hsub : (doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ)) ⊆
      {D | passiveEnergy E (energyDephasing X) ≤ F D} := by
    rw [doublyStochastic_eq_convexHull_permMatrix]
    refine convexHull_min ?_ (convex_halfSpace_ge hFlin _)
    rintro _ ⟨σ, rfl⟩
    exact hperm σ
  show passiveEnergy E (energyDephasing X) ≤ sInf _
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro r ⟨U, rfl⟩
  rw [ee_diag E _ _ hCoff]
  have hBT := hsub (Submonoid.mul_mem _ (unistoch U) hTds)
  simp only [Set.mem_ofPred_eq] at hBT
  refine hBT.trans (le_of_eq ?_)
  simp only [hF]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply, hCdiag, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

lemma forward {d n : ℕ} (E : Fin d → ℝ) {M : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hM : IsPOVM M) (hI : measurementIncoherent M) : observationalAdvantage E M ≤ 0 := by
  apply Real.sSup_nonpos
  rintro r ⟨X, _, rfl⟩
  rw [adv_elem]
  linarith [incoh_le E hM hI X]

/-! ## Linearity facts -/

lemma cg_add {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    ergotropicCoarseGraining M (A + B) =
      ergotropicCoarseGraining M A + ergotropicCoarseGraining M B := by
  simp only [ergotropicCoarseGraining, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs
  · simp
  · rw [Matrix.mul_add, Matrix.trace_add, add_div, add_smul]

lemma cg_smul {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (c : ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ergotropicCoarseGraining M (c • A) = c • ergotropicCoarseGraining M A := by
  simp only [ergotropicCoarseGraining, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs
  · simp
  · rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc, smul_smul]

lemma cg_one {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) :
    ergotropicCoarseGraining M 1 = 1 := by
  simp only [ergotropicCoarseGraining, Matrix.mul_one]
  rw [← hM.2]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs with h
  · exact (((hM.1 u).trace_eq_zero_iff).mp h).symm
  · rw [div_self h, one_smul]

lemma ee_add {d : ℕ} (E : Fin d → ℝ) (U A B : Matrix (Fin d) (Fin d) ℂ) :
    energyExpectation E (U * (A + B) * Uᴴ) =
      energyExpectation E (U * A * Uᴴ) + energyExpectation E (U * B * Uᴴ) := by
  simp only [Matrix.mul_add, Matrix.add_mul, energyExpectation, Matrix.add_apply, Complex.add_re,
    mul_add, Finset.sum_add_distrib]

lemma ee_smul {d : ℕ} (E : Fin d → ℝ) (U A : Matrix (Fin d) (Fin d) ℂ) (r : ℝ) :
    energyExpectation E (U * ((r : ℂ) • A) * Uᴴ) = r * energyExpectation E (U * A * Uᴴ) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, energyExpectation, Matrix.smul_apply, smul_eq_mul,
    Complex.re_ofReal_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma ee_one {d : ℕ} (E : Fin d → ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * 1 * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      ∑ k, E k := by
  have h1 : (U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose, h1]
  simp [energyExpectation]

/-! ## The test matrix K -/

def Kw {d : ℕ} (a b : Fin d) (w : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j k => (if j = a then (if k = b then w else 0) else 0) +
    (if j = b then (if k = a then star w else 0) else 0)

lemma Kw_neg {d : ℕ} (a b : Fin d) (w : ℂ) :
    Kw a b (-w) = (((-1 : ℝ) : ℂ)) • Kw a b w := by
  ext j k
  simp only [Kw, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp <;> ring

lemma Kw_diag {d : ℕ} {a b : Fin d} (hab : a ≠ b) (w : ℂ) (k : Fin d) : Kw a b w k k = 0 := by
  simp only [Kw, Matrix.of_apply]
  by_cases ha : k = a
  · subst ha; simp [hab]
  · by_cases hb : k = b
    · subst hb; simp [Ne.symm hab]
    · simp [ha, hb]

lemma trK {d : ℕ} {a b : Fin d} (hab : a ≠ b) (w : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    (A * Kw a b w).trace = A b a * w + A a b * star w := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Kw, Matrix.of_apply, mul_add, mul_ite,
    mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## The witness density matrix -/

def hv {d : ℕ} (a b : Fin d) (c s : ℂ) : Fin d → ℂ :=
  fun k => (if k = a then c else 0) + (if k = b then s else 0)

lemma hv_star {d : ℕ} (a b : Fin d) (c s : ℂ) (j : Fin d) :
    star (hv a b c s j) = hv a b (star c) (star s) j := by
  simp only [hv, star_add]
  split_ifs <;> simp

lemma one_add_Kw {d : ℕ} {a b : Fin d} (hab : a ≠ b) (w : ℂ) (hw : star w * w = 1) :
    1 + Kw a b w = Matrix.diagonal (fun j => if j = a then 0 else if j = b then 0 else 1) +
      Matrix.vecMulVec (hv a b 1 (star w)) (star (hv a b 1 (star w))) := by
  have hw' : (starRingEnd ℂ) w * w = 1 := hw
  ext j k
  simp only [Kw, hv, Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply, Matrix.of_apply, Pi.star_apply]
  by_cases hja : j = a <;> by_cases hjb : j = b <;> by_cases hka : k = a <;>
    by_cases hkb : k = b <;> (try simp_all [Ne.symm hab]) <;> (rintro rfl; simp_all)

lemma X_density {d : ℕ} {a b : Fin d} (hab : a ≠ b) (w : ℂ) (hw : star w * w = 1) :
    IsDensityMatrix ((((1 : ℝ) / d : ℝ) : ℂ) • (1 + Kw a b w)) := by
  have hd : (d : ℝ) ≠ 0 := by
    have : 0 < d := Fin.pos a
    exact_mod_cast this.ne'
  refine ⟨?_, ?_⟩
  · rw [one_add_Kw hab w hw]
    have h1 : (Matrix.diagonal (fun j : Fin d => if j = a then (0 : ℂ) else if j = b then 0 else 1) +
        Matrix.vecMulVec (hv a b 1 (star w)) (star (hv a b 1 (star w)))).PosSemidef := by
      refine Matrix.PosSemidef.add ?_ (Matrix.posSemidef_vecMulVec_self_star _)
      refine Matrix.PosSemidef.diagonal fun j => ?_
      simp only [Pi.zero_apply]
      split_ifs <;> simp
    refine h1.smul ?_
    have : (0 : ℝ) ≤ 1 / d := by positivity
    exact_mod_cast this
  · rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
    have : (Kw a b w).trace = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      exact Finset.sum_eq_zero fun k _ => Kw_diag hab w k
    rw [this, add_zero, smul_eq_mul]
    have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp

lemma p_const {d : ℕ} (E : Fin d → ℝ) (c : ℝ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (hY : ∀ l m, l ≠ m → Y l m = 0) (hYd : ∀ l, (Y l l).re = c) :
    c * ∑ k, E k ≤ passiveEnergy E Y := by
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro r ⟨U, rfl⟩
  rw [ee_diag E _ _ hY]
  have hrow := (mem_doublyStochastic_iff_sum.mp (unistoch U)).2.1
  have hr : ∀ k, ∑ l, ‖(U : Matrix (Fin d) (Fin d) ℂ) k l‖ ^ 2 = 1 := fun k => by
    simpa using hrow k
  rw [Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  simp only [hYd]
  rw [← Finset.sum_mul, hr k]
  ring

/-! ## Householder reflections -/

def hV {d : ℕ} (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  1 - (2 : ℂ) • Matrix.vecMulVec v (star v)

lemma hV_herm {d : ℕ} (v : Fin d → ℂ) : (hV v)ᴴ = hV v := by
  simp [hV, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]

lemma hV_unitary {d : ℕ} (v : Fin d → ℂ) (hv1 : star v ⬝ᵥ v = 1) :
    hV v ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hV_herm]
  have hPP : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec v (star v) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hv1, one_smul]
  simp only [hV, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hPP,
    smul_smul]
  module

lemma hV_entry {d : ℕ} (v : Fin d → ℂ) (Z : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    (hV v * Z * (hV v)ᴴ) k k = Z k k - 2 * (∑ j, v k * star (v j) * Z j k)
      - 2 * (∑ j, Z k j * (v j * star (v k)))
      + 4 * (∑ j, v k * star (v j) * ∑ i, Z j i * (v i * star (v k))) := by
  rw [hV_herm]
  set P := Matrix.vecMulVec v (star v) with hP
  have hexp : hV v * Z * hV v = Z - (2 : ℂ) • (P * Z) - (2 : ℂ) • (Z * P) +
      (4 : ℂ) • (P * (Z * P)) := by
    simp only [hV, ← hP, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]
    module
  rw [hexp]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    hP, Matrix.vecMulVec_apply, Pi.star_apply]

lemma hh_diff {d : ℕ} (E : Fin d → ℝ) (Z : Matrix (Fin d) (Fin d) ℂ) {a b : Fin d}
    (hab : a ≠ b) (c : ℝ) (t : ℂ) :
    energyExpectation E (hV (hv a b c t) * Z * (hV (hv a b c t))ᴴ) -
      energyExpectation E (hV (hv a b c (-t)) * Z * (hV (hv a b c (-t)))ᴴ) =
    E a * ((2 * c * (4 * c ^ 2 - 2) : ℂ) * (t * Z a b + star t * Z b a)).re +
      E b * ((2 * c * (4 * (t * star t) - 2) : ℂ) * (t * Z a b + star t * Z b a)).re := by
  have hA : (hV (hv a b c t) * Z * (hV (hv a b c t))ᴴ) a a -
      (hV (hv a b c (-t)) * Z * (hV (hv a b c (-t)))ᴴ) a a =
      (2 * c * (4 * c ^ 2 - 2) : ℂ) * (t * Z a b + star t * Z b a) := by
    rw [hV_entry, hV_entry]
    simp only [hv_star]
    simp only [hv, mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hab, Ne.symm hab, if_false, add_zero, zero_add,
      Complex.star_def, Complex.conj_ofReal, map_neg]
    ring
  have hB : (hV (hv a b c t) * Z * (hV (hv a b c t))ᴴ) b b -
      (hV (hv a b c (-t)) * Z * (hV (hv a b c (-t)))ᴴ) b b =
      (2 * c * (4 * (t * star t) - 2) : ℂ) * (t * Z a b + star t * Z b a) := by
    rw [hV_entry, hV_entry]
    simp only [hv_star]
    simp only [hv, mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hab, Ne.symm hab, if_false, add_zero, zero_add,
      Complex.star_def, Complex.conj_ofReal, map_neg]
    ring
  have hO : ∀ x, x ≠ a ∧ x ≠ b →
      E x * ((hV (hv a b c t) * Z * (hV (hv a b c t))ᴴ) x x -
        (hV (hv a b c (-t)) * Z * (hV (hv a b c (-t)))ᴴ) x x).re = 0 := by
    intro x hx
    rw [hV_entry, hV_entry]
    simp [hv, hx.1, hx.2]
  simp only [energyExpectation, ← Finset.sum_sub_distrib, ← mul_sub, ← Complex.sub_re]
  rw [Fintype.sum_eq_add a b hab hO, hA, hB]

lemma exists_V {d : ℕ} (E : Fin d → ℝ) (hE : Function.Injective E)
    (Z : Matrix (Fin d) (Fin d) ℂ) {a b : Fin d} (hab : a ≠ b) (w : ℂ) (hw : w * star w = 1)
    (hR : 0 < (star w * Z a b + w * Z b a).re) :
    ∃ V : Matrix.unitaryGroup (Fin d) ℂ, energyExpectation E
      ((V : Matrix (Fin d) (Fin d) ℂ) * Z * (V : Matrix (Fin d) (Fin d) ℂ)ᴴ) ≠ 0 := by
  set t : ℂ := (4 / 5 : ℂ) * star w with ht
  have htt : t * star t = 16 / 25 := by
    rw [ht, star_mul', star_star]
    have : (star (4 / 5 : ℂ)) = 4 / 5 := by
      rw [Complex.star_def, map_div₀, map_ofNat, map_ofNat]
    rw [this]
    linear_combination (16 / 25 : ℂ) * hw
  have hunit : ∀ s : ℂ, s * star s = 16 / 25 →
      star (hv a b ((3 / 5 : ℝ) : ℂ) s) ⬝ᵥ hv a b ((3 / 5 : ℝ) : ℂ) s = 1 := by
    intro s hs
    have hs' : (starRingEnd ℂ) s * s = 16 / 25 := by
      rw [mul_comm]
      exact hs
    simp only [dotProduct, Pi.star_apply, hv_star]
    simp only [hv, mul_add, add_mul, ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hab, Ne.symm hab, if_false, add_zero,
      zero_add, Complex.star_def, Complex.conj_ofReal, hs']
    push_cast
    norm_num
  by_contra hcon
  push Not at hcon
  have h1 : energyExpectation E (hV (hv a b ((3 / 5 : ℝ) : ℂ) t) * Z *
      (hV (hv a b ((3 / 5 : ℝ) : ℂ) t))ᴴ) = 0 := hcon ⟨_, hV_unitary _ (hunit t htt)⟩
  have h2 : energyExpectation E (hV (hv a b ((3 / 5 : ℝ) : ℂ) (-t)) * Z *
      (hV (hv a b ((3 / 5 : ℝ) : ℂ) (-t)))ᴴ) = 0 :=
    hcon ⟨_, hV_unitary _ (hunit (-t) (by rw [star_neg, neg_mul_neg]; exact htt))⟩
  have hd := hh_diff E Z hab (3 / 5) t
  rw [h1, h2, sub_self] at hd
  have hR' : t * Z a b + star t * Z b a = (4 / 5 : ℂ) * (star w * Z a b + w * Z b a) := by
    rw [ht, star_mul', star_star]
    have : (star (4 / 5 : ℂ)) = 4 / 5 := by
      rw [Complex.star_def, map_div₀, map_ofNat, map_ofNat]
    rw [this]
    ring
  rw [htt, hR'] at hd
  have e1 : ((2 * ((3 / 5 : ℝ) : ℂ) * (4 * ((3 / 5 : ℝ) : ℂ) ^ 2 - 2)) *
      ((4 / 5 : ℂ) * (star w * Z a b + w * Z b a))).re =
      (-336 / 625) * (star w * Z a b + w * Z b a).re := by
    have : (2 * ((3 / 5 : ℝ) : ℂ) * (4 * ((3 / 5 : ℝ) : ℂ) ^ 2 - 2)) * (4 / 5 : ℂ) =
        ((-336 / 625 : ℝ) : ℂ) := by
      push_cast
      norm_num
    rw [← mul_assoc, this, Complex.re_ofReal_mul]
  have e2 : ((2 * ((3 / 5 : ℝ) : ℂ) * (4 * (16 / 25 : ℂ) - 2)) *
      ((4 / 5 : ℂ) * (star w * Z a b + w * Z b a))).re =
      (336 / 625) * (star w * Z a b + w * Z b a).re := by
    have : (2 * ((3 / 5 : ℝ) : ℂ) * (4 * (16 / 25 : ℂ) - 2)) * (4 / 5 : ℂ) =
        ((336 / 625 : ℝ) : ℂ) := by
      push_cast
      norm_num
    rw [← mul_assoc, this, Complex.re_ofReal_mul]
  rw [e1, e2] at hd
  have hEab : E a ≠ E b := hE.ne hab
  have hprod : (E b - E a) * (star w * Z a b + w * Z b a).re = 0 := by linarith
  rcases mul_eq_zero.mp hprod with h | h
  · exact hEab (by linarith)
  · linarith

lemma trMX_le {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) (u : Fin n) :
    ‖(M u * X).trace‖ ≤ 1 := by
  have hnn : ∀ u, 0 ≤ (M u * X).trace := by
    intro u
    obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hM.1 u)
    rw [hv, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have : (Matrix.vecMulVec (v i) (star (v i)) * X).trace = star (v i) ⬝ᵥ (X *ᵥ v i) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact hX.1.dotProduct_mulVec_nonneg _
  have hsum : ∑ u, (M u * X).trace = 1 := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hM.2, Matrix.one_mul, hX.2]
  have hre : ∑ u, ((M u * X).trace).re = 1 := by
    rw [← Complex.re_sum, hsum, Complex.one_re]
  have hre0 : ∀ u, 0 ≤ ((M u * X).trace).re := fun u => (Complex.le_def.mp (hnn u)).1
  have him : ((M u * X).trace).im = 0 := by
    have := (Complex.le_def.mp (hnn u)).2
    simpa using this.symm
  have hle : ((M u * X).trace).re ≤ 1 := by
    rw [← hre]
    exact Finset.single_le_sum (fun i _ => hre0 i) (Finset.mem_univ u)
  have heq : (M u * X).trace = (((M u * X).trace).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hre0 u]

lemma adv_bdd {d n : ℕ} (E : Fin d → ℝ) {M : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hM : IsPOVM M) :
    BddAbove {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} := by
  refine ⟨(∑ k, |E k|) + ∑ k, |E k| *
    ∑ m, ∑ l, ∑ u, ‖M u l m‖ / ‖(M u).trace‖, ?_⟩
  rintro r ⟨X, hX, rfl⟩
  rw [adv_elem]
  -- upper bound for the dephased passive energy
  have hA : passiveEnergy E (energyDephasing X) ≤ ∑ k, |E k| := by
    have := passive_le E (energyDephasing X) 1
    refine this.trans ?_
    simp only [OneMemClass.coe_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    simp only [energyExpectation, energyDephasing, Matrix.diagonal_apply_eq]
    have hre0 : ∀ k, 0 ≤ (X k k).re := fun k => (Complex.le_def.mp (hX.1.diag_nonneg (i := k))).1
    have hre : ∑ k, (X k k).re = 1 := by
      have := congrArg Complex.re hX.2
      simpa [Matrix.trace, Complex.re_sum] using this
    refine Finset.sum_le_sum fun k _ => ?_
    have hle : (X k k).re ≤ 1 := by
      rw [← hre]
      exact Finset.single_le_sum (fun i _ => hre0 i) (Finset.mem_univ k)
    calc E k * (X k k).re ≤ |E k| * (X k k).re :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hre0 k)
      _ ≤ |E k| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = |E k| := mul_one _
  -- lower bound for the coarse-grained passive energy
  have hN : ∑ m, ∑ l, ‖ergotropicCoarseGraining M X l m‖ ≤
      ∑ m, ∑ l, ∑ u, ‖M u l m‖ / ‖(M u).trace‖ := by
    refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun l _ => ?_
    simp only [ergotropicCoarseGraining, Matrix.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    split_ifs with h
    · simp only [Matrix.zero_apply, norm_zero]
      positivity
    · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_div]
      have h1 := trMX_le hM hX u
      have h2 : 0 < ‖(M u).trace‖ := norm_pos_iff.mpr h
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (by nlinarith [norm_nonneg (M u l m), norm_nonneg ((M u * X).trace)]) h2.le
  have hB := passive_ge E (ergotropicCoarseGraining M X)
  have hB2 : ∑ k, |E k| * ∑ m, ∑ l, ‖ergotropicCoarseGraining M X l m‖ ≤
      ∑ k, |E k| * ∑ m, ∑ l, ∑ u, ‖M u l m‖ / ‖(M u).trace‖ :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left hN (abs_nonneg _)
  linarith

lemma R_pos {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) {u0 : Fin n}
    {a b : Fin d} (hab : a ≠ b) (w : ℂ) (hwdef : w = M u0 a b / ((‖M u0 a b‖ : ℝ) : ℂ))
    (hy : M u0 a b ≠ 0) :
    0 < (star w * ergotropicCoarseGraining M (Kw a b w) a b +
        w * ergotropicCoarseGraining M (Kw a b w) b a).re := by
  set tr : Fin n → ℝ := fun u => ∑ k, (M u k k).re with htr
  set ρ : Fin n → ℝ := fun u => 2 * (M u a b * star w).re with hρ
  have hMba : ∀ u, M u b a = star (M u a b) := fun u => by
    rw [← (hM.1 u).1.apply a b, star_star]
  have htrace : ∀ u, (M u).trace = ((tr u : ℝ) : ℂ) := by
    intro u
    simp only [Matrix.trace, Matrix.diag, htr, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => (diag_real hM u k).1
  have htr0 : ∀ u, 0 ≤ tr u := fun u => Finset.sum_nonneg fun k _ => (diag_real hM u k).2
  have hpair : ∀ u, star w * M u a b + w * star (M u a b) = ((ρ u : ℝ) : ℂ) := by
    intro u
    have : w * star (M u a b) = (starRingEnd ℂ) (M u a b * star w) := by
      simp [mul_comm]
    rw [this, mul_comm (star w), Complex.add_conj]
  have hτ : ∀ u, (M u * Kw a b w).trace = ((ρ u : ℝ) : ℂ) := by
    intro u
    rw [trK hab, hMba, ← hpair u]
    ring
  have hexp : star w * ergotropicCoarseGraining M (Kw a b w) a b +
      w * ergotropicCoarseGraining M (Kw a b w) b a =
      ∑ u, (((if tr u = 0 then 0 else (ρ u) ^ 2 / tr u : ℝ)) : ℂ) := by
    simp only [ergotropicCoarseGraining, Matrix.sum_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [htrace u, hτ u]
    by_cases h : tr u = 0
    · simp [h]
    · have h' : ((tr u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
      simp only [h', h, if_false, Matrix.smul_apply, smul_eq_mul]
      rw [hMba u]
      have hp := hpair u
      push_cast
      linear_combination ((ρ u : ℂ) / (tr u : ℂ)) * hp
  rw [hexp, Complex.re_sum]
  simp only [Complex.ofReal_re]
  apply Finset.sum_pos'
  · intro u _
    split_ifs
    · exact le_refl _
    · exact div_nonneg (sq_nonneg _) (htr0 u)
  · refine ⟨u0, Finset.mem_univ _, ?_⟩
    have htr_ne : tr u0 ≠ 0 := by
      intro h
      have h0 : (M u0).trace = 0 := by rw [htrace, h, Complex.ofReal_zero]
      have := ((hM.1 u0).trace_eq_zero_iff).mp h0
      exact hy (by rw [this, Matrix.zero_apply])
    have htrpos : 0 < tr u0 := lt_of_le_of_ne (htr0 u0) (Ne.symm htr_ne)
    have hny : 0 < ‖M u0 a b‖ := norm_pos_iff.mpr hy
    have hρ0 : ρ u0 = 2 * ‖M u0 a b‖ := by
      simp only [hρ, hwdef]
      have : M u0 a b * star (M u0 a b / ((‖M u0 a b‖ : ℝ) : ℂ)) = ((‖M u0 a b‖ : ℝ) : ℂ) := by
        rw [star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, mul_div_assoc',
          show star (M u0 a b) = (starRingEnd ℂ) (M u0 a b) from rfl, Complex.mul_conj']
        have : ((‖M u0 a b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
        field_simp
      rw [this, Complex.ofReal_re]
    rw [if_neg htr_ne, hρ0]
    positivity

end P38Aux

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : StrictMono E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    0 < observationalAdvantage E M ↔ ¬ measurementIncoherent M := by
  constructor
  · intro hpos hI
    linarith [P38Aux.forward E hM hI]
  · intro hnot
    obtain ⟨u0, hu0⟩ : ∃ u, energyDephasing (M u) ≠ M u := by
      by_contra h
      push Not at h
      exact hnot h
    obtain ⟨a, b, hne⟩ : ∃ a b, energyDephasing (M u0) a b ≠ M u0 a b := by
      by_contra h
      push Not at h
      exact hu0 (Matrix.ext h)
    have hab : a ≠ b := by
      rintro rfl
      simp [energyDephasing] at hne
    have hy : M u0 a b ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      simp [energyDephasing, Matrix.diagonal_apply_ne _ hab]
    set w : ℂ := M u0 a b / ((‖M u0 a b‖ : ℝ) : ℂ) with hwdef
    have hny : 0 < ‖M u0 a b‖ := norm_pos_iff.mpr hy
    have hnc : ((‖M u0 a b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
    have hw1 : w * star w = 1 := by
      rw [hwdef, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
      rw [div_mul_div_comm, show star (M u0 a b) = (starRingEnd ℂ) (M u0 a b) from rfl,
        Complex.mul_conj']
      field_simp
    have hw2 : star w * w = 1 := by rw [mul_comm]; exact hw1
    have hR := P38Aux.R_pos hM hab w hwdef hy
    obtain ⟨V, hV⟩ := P38Aux.exists_V E hE.injective _ hab w hw1 hR
    obtain ⟨w', hw', hneg⟩ : ∃ w' : ℂ, star w' * w' = 1 ∧
        energyExpectation E ((V : Matrix (Fin d) (Fin d) ℂ) *
          ergotropicCoarseGraining M (P38Aux.Kw a b w') * (V : Matrix (Fin d) (Fin d) ℂ).conjTranspose) < 0 := by
      rcases lt_or_gt_of_ne hV with h | h
      · exact ⟨w, hw2, h⟩
      · refine ⟨-w, by rw [star_neg, neg_mul_neg]; exact hw2, ?_⟩
        rw [P38Aux.Kw_neg, P38Aux.cg_smul, P38Aux.ee_smul]
        linarith
    set X := ((((1 : ℝ) / d : ℝ) : ℂ)) • (1 + P38Aux.Kw a b w') with hX
    have hXd : IsDensityMatrix X := P38Aux.X_density hab w' hw'
    have hmem : passiveEnergy E (energyDephasing X) -
        passiveEnergy E (ergotropicCoarseGraining M X) ∈
        {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
          r = observationalErgotropy E M X - incoherentErgotropy E X} :=
      ⟨X, hXd, (P38Aux.adv_elem E M X).symm⟩
    have h1 : ((1 : ℝ) / d) * ∑ k, E k ≤ passiveEnergy E (energyDephasing X) := by
      apply P38Aux.p_const
      · intro l m hlm
        simp [energyDephasing, Matrix.diagonal_apply_ne _ hlm]
      · intro l
        simp only [energyDephasing, Matrix.diagonal_apply_eq, hX, Matrix.smul_apply, smul_eq_mul,
          Matrix.add_apply, Matrix.one_apply_eq, P38Aux.Kw_diag hab, add_zero, mul_one,
          Complex.ofReal_re]
    have h2 : passiveEnergy E (ergotropicCoarseGraining M X) ≤
        ((1 : ℝ) / d) * ((∑ k, E k) + energyExpectation E ((V : Matrix (Fin d) (Fin d) ℂ) *
          ergotropicCoarseGraining M (P38Aux.Kw a b w') * (V : Matrix (Fin d) (Fin d) ℂ).conjTranspose)) := by
      refine (P38Aux.passive_le E _ V).trans (le_of_eq ?_)
      rw [hX, P38Aux.cg_smul, P38Aux.cg_add, P38Aux.cg_one hM, P38Aux.ee_smul, P38Aux.ee_add,
        P38Aux.ee_one]
    have hdpos : (0 : ℝ) < 1 / d := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    have hpos : 0 < passiveEnergy E (energyDephasing X) -
        passiveEnergy E (ergotropicCoarseGraining M X) := by
      have := mul_neg_of_pos_of_neg hdpos hneg
      nlinarith
    exact lt_of_lt_of_le hpos (le_csSup (P38Aux.adv_bdd E hM) hmem)
