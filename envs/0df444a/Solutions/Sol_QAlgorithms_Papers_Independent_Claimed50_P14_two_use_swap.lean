-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P14.two_use_swap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:24:13.679992+00:00
-- url     : https://prove2.me/submissions/8af05d93-bc53-435d-bf6b-dc8ec6797a4d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm


theorem p14_swapInput_swapInput {d : ℕ} (a : Labels d 2) : swapInput (swapInput a) = a := by
  ext n; simp [swapInput]

def p14_swapEquiv (d : ℕ) : Labels d 2 ≃ Labels d 2 :=
  ⟨swapInput, swapInput, p14_swapInput_swapInput, p14_swapInput_swapInput⟩

theorem p14_swapInput_inj {d : ℕ} {a b : Labels d 2} : swapInput a = swapInput b ↔ a = b :=
  (p14_swapEquiv d).injective.eq_iff

theorem p14_itp_swap {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (a b : Labels d 2) :
    inputTensorPower U (swapInput a) (swapInput b) = inputTensorPower U a b := by
  simp only [inputTensorPower, swapInput, Fin.prod_univ_two]
  simp [mul_comm]

theorem p14_rep_swapLearner {d : ℕ} (R : Branches d 2) (U : Matrix (Fin d) (Fin d) ℂ) :
    replicatedPOVM (swapLearner R) U = replicatedPOVM R U := by
  funext i t s
  simp only [replicatedPOVM, swapLearner]
  apply Fintype.sum_equiv (p14_swapEquiv d); intro j
  apply Fintype.sum_equiv (p14_swapEquiv d); intro a
  apply Fintype.sum_equiv (p14_swapEquiv d); intro b
  simp [p14_swapEquiv, p14_itp_swap]

theorem p14_swapAverage_apply {d : ℕ} (R : Branches d 2) (i : Fin d) (x y : TrainingWires d 2) :
    swapAverage R i x y = (1/2 : ℂ) * (R i x y + R i (x.1,(swapInput x.2.1,swapInput x.2.2))
      (y.1,(swapInput y.2.1,swapInput y.2.2))) := by
  simp [swapAverage, swapLearner]

theorem p14_rep_swapAverage {d : ℕ} (R : Branches d 2) :
    replicatedPOVM (swapAverage R) = replicatedPOVM R := by
  funext U i t s
  have h := congrFun (congrFun (congrFun (p14_rep_swapLearner R U) i) t) s
  have h2 : replicatedPOVM (swapAverage R) U i t s = (1/2 : ℂ) *
      (replicatedPOVM R U i t s + replicatedPOVM (swapLearner R) U i t s) := by
    simp only [replicatedPOVM, p14_swapAverage_apply, swapLearner, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h2, h]; ring

theorem p14_swapLearner_swapAverage {d : ℕ} (R : Branches d 2) :
    swapAverage R = swapLearner (swapAverage R) := by
  funext i x y
  simp only [swapLearner, p14_swapAverage_apply, p14_swapInput_swapInput]
  ring

theorem p14_cov_swap {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (x y : TrainingWires d 2) :
    covariantRepresentation U (x.1,(swapInput x.2.1,swapInput x.2.2))
      (y.1,(swapInput y.2.1,swapInput y.2.2)) = covariantRepresentation U x y := by
  simp [covariantRepresentation, p14_swapInput_inj, p14_itp_swap]

def p14_wireEquiv (d : ℕ) : TrainingWires d 2 ≃ TrainingWires d 2 :=
  (Equiv.refl _).prodCongr ((p14_swapEquiv d).prodCongr (p14_swapEquiv d))

theorem p14_swapLearner_sub {d : ℕ} (R : Branches d 2) (i : Fin d) :
    swapLearner R i = (R i).submatrix (p14_wireEquiv d) (p14_wireEquiv d) := by
  ext x y; rfl

theorem p14_cov_sub {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    (covariantRepresentation U : Matrix (TrainingWires d 2) (TrainingWires d 2) ℂ).submatrix
      (p14_wireEquiv d) (p14_wireEquiv d) = covariantRepresentation U := by
  ext x y; exact p14_cov_swap U x y

theorem p14_sym {d : ℕ} (R : Branches d 2) (hs : IsLearningSymmetric R) :
    IsLearningSymmetric (swapAverage R) := by
  obtain ⟨hdiag, hcov, hrel⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · funext i x y
    have h1 := congrFun (congrFun (congrFun hdiag i) x) y
    have h2 := congrFun (congrFun (congrFun hdiag i) (x.1,(swapInput x.2.1,swapInput x.2.2)))
      (y.1,(swapInput y.2.1,swapInput y.2.2))
    simp only [outcomeDephasing] at h1 h2 ⊢
    simp only [p14_swapInput_inj] at h2
    split_ifs at h1 h2 ⊢ with hxy
    · rfl
    · rw [p14_swapAverage_apply, h1, h2]; simp
  · intro U i
    have hL : swapLearner R i * covariantRepresentation (U : Matrix (Fin d) (Fin d) ℂ) =
        covariantRepresentation (U : Matrix (Fin d) (Fin d) ℂ) * swapLearner R i := by
      rw [p14_swapLearner_sub, ← p14_cov_sub (U : Matrix (Fin d) (Fin d) ℂ),
        Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcov U i]
    have hS : swapAverage R i = (1/2 : ℂ) • (R i + swapLearner R i) := rfl
    rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hcov U i, hL]
  · intro σ
    funext i x y
    have h1 := congrFun (congrFun (congrFun (hrel σ) i) x) y
    have h2 := congrFun (congrFun (congrFun (hrel σ) i) (x.1,(swapInput x.2.1,swapInput x.2.2)))
      (y.1,(swapInput y.2.1,swapInput y.2.2))
    simp only [relabelClassical, p14_swapAverage_apply] at h1 h2 ⊢
    rw [h1, h2]
    rfl


theorem p14_rho_comm {d : ℕ} (hd : 0 < d) (R : Branches d 2)
    (rho : Matrix (Labels d 2) (Labels d 2) ℂ) (hcov : IsLearningCovariant R)
    (hsum : ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then (if j = l then rho a b else 0) else 0)
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M ∈ Matrix.specialUnitaryGroup (Fin d) ℂ)
    (a b : Labels d 2) :
    ∑ e, rho a e * inputTensorPower M e b = ∑ e, inputTensorPower M a e * rho e b := by
  have hcomm : (∑ i, R i) * covariantRepresentation M =
      covariantRepresentation M * (∑ i, R i) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hcov ⟨M, hM⟩ i
  obtain ⟨t, s, hts⟩ : ∃ t s, M t s ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : M = 0 := by ext p q; exact h p q
    have h1 : M ∈ Matrix.unitaryGroup (Fin d) ℂ := hM.1
    rw [Matrix.mem_unitaryGroup_iff, h0] at h1
    have : (1 : Matrix (Fin d) (Fin d) ℂ) ⟨0, hd⟩ ⟨0, hd⟩ = 0 := by rw [← h1]; simp
    simp at this
  let j0 : Labels d 2 := fun _ => ⟨0, hd⟩
  have h := congrFun (congrFun hcomm (t,(j0,a))) (s,(j0,b))
  simp only [Matrix.mul_apply, Matrix.sum_apply, hsum, covariantRepresentation,
    Fintype.sum_prod_type] at h
  simp [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] at h
  have hc : (starRingEnd ℂ) (M t s) ≠ 0 := by simpa using hts
  simp only [mul_left_comm (rho a _), mul_assoc] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  exact mul_left_cancel₀ hc h

theorem p14_itp_mono {d : ℕ} (f : Fin d → Fin d) (g : Fin d → ℂ) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ p q, M p q = if f p = q then g p else 0) (a b : Labels d 2) :
    inputTensorPower M a b = if f ∘ a = b then g (a 0) * g (a 1) else 0 := by
  simp only [inputTensorPower, hM, Fin.prod_univ_two]
  by_cases h : f ∘ a = b
  · subst h; simp
  · have : f (a 0) ≠ b 0 ∨ f (a 1) ≠ b 1 := by
      by_contra hc
      push Not at hc
      apply h
      funext n; fin_cases n <;> simp [hc.1, hc.2]
    rcases this with h0 | h0 <;> simp [h, h0]

/-- invariance under transpositions -/
theorem p14_rho_perm {d : ℕ} (hd : 0 < d) (R : Branches d 2)
    (rho : Matrix (Labels d 2) (Labels d 2) ℂ) (hcov : IsLearningCovariant R)
    (hsum : ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then (if j = l then rho a b else 0) else 0)
    (x y : Fin d) (hxy : x ≠ y) (a b : Labels d 2) :
    rho (Equiv.swap x y ∘ a) (Equiv.swap x y ∘ b) = rho a b := by
  set τ := Equiv.swap x y with hτ
  set c : ℂ := Complex.exp (((Real.pi / d : ℝ) : ℂ) * Complex.I) with hcdef
  have hcn : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hcd : c ^ d = -1 := by
    rw [hcdef, ← Complex.exp_nat_mul]
    have : (d : ℂ) * (((Real.pi / d : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      push_cast; field_simp
    rw [this, Complex.exp_pi_mul_I]
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcn]; simp
  let M : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun p q => if τ p = q then c else 0
  have hMe : ∀ p q, M p q = if τ p = q then c else 0 := fun p q => rfl
  have hPe : ∀ p q, τ.permMatrix ℂ p q = if τ p = q then 1 else 0 := by
    intro p q; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  have hMP : M = c • τ.permMatrix ℂ := by
    ext p q; simp [hMe]
  have hM : M ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
    refine ⟨?_, ?_⟩
    · show M ∈ Matrix.unitaryGroup (Fin d) ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      ext p q
      simp only [Matrix.mul_apply, Matrix.star_apply, hMe, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq; simp [hcc]
      · have : τ p ≠ τ q := fun h => hpq (τ.injective h)
        simp [hpq, Ne.symm hpq]
    · show M.det = 1
      rw [hMP, Matrix.det_smul, Matrix.det_permutation, hτ, Equiv.Perm.sign_swap hxy]
      simp [hcd]
  have key := p14_rho_comm hd R rho hcov hsum M hM a (τ ∘ b)
  simp only [p14_itp_mono τ (fun _ => c) M hMe] at key
  have hττ : ∀ v : Labels d 2, τ ∘ (τ ∘ v) = v := by
    intro v; funext n; simp [hτ]
  have hiff : ∀ e : Labels d 2, (τ ∘ e = τ ∘ b) ↔ e = b := by
    intro e; constructor
    · intro h; have := congrArg (fun v => τ ∘ v) h; simpa [hττ] using this
    · intro h; rw [h]
  simp only [hiff, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at key
  have hc2 : c * c ≠ 0 := by
    have : c ≠ 0 := Complex.exp_ne_zero _
    exact mul_ne_zero this this
  exact mul_left_cancel₀ hc2 (key.symm.trans (mul_comm _ _))

theorem p14_rho_diag {d : ℕ} (hd : 0 < d) (R : Branches d 2)
    (rho : Matrix (Labels d 2) (Labels d 2) ℂ) (hcov : IsLearningCovariant R)
    (hsum : ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then (if j = l then rho a b else 0) else 0)
    (a b : Labels d 2) (hab : rho a b ≠ 0) (x y : Fin d) (hxy : x ≠ y) :
    ((if a 0 = x then 1 else 0) + (if a 1 = x then 1 else 0) - (if b 0 = x then 1 else 0)
      - (if b 1 = x then 1 else 0) : ℤ) =
    (if a 0 = y then 1 else 0) + (if a 1 = y then 1 else 0) - (if b 0 = y then 1 else 0)
      - (if b 1 = y then 1 else 0) := by
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (5 : ℕ)) with hωdef
  have hprim : IsPrimitiveRoot ω 5 := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hωn : ‖ω‖ = 1 := hprim.norm'_eq_one (by norm_num)
  let e : Fin d → ℤ := fun z => (if z = x then 1 else 0) - (if z = y then 1 else 0)
  let φ : Fin d → ℂ := fun z => (if z = x then ω else 1) * (if z = y then ω⁻¹ else 1)
  have hφ : ∀ z, φ z = ω ^ e z := by
    intro z
    by_cases h1 : z = x
    · subst h1; simp [φ, e, hxy]
    · by_cases h2 : z = y
      · subst h2; simp [φ, e, h1]
      · simp [φ, e, h1, h2]
  have hφn : ∀ z, φ z * (starRingEnd ℂ) (φ z) = 1 := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hφ, norm_zpow, hωn]; simp
  let D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal φ
  have hDe : ∀ p q, D p q = if id p = q then φ p else 0 := by
    intro p q; simp [D, Matrix.diagonal_apply]
  have hD : D ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
    refine ⟨?_, ?_⟩
    · show D ∈ Matrix.unitaryGroup (Fin d) ℂ
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext z; exact hφn z
    · show D.det = 1
      rw [Matrix.det_diagonal]
      simp only [φ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true,
        Finset.prod_const_one]
      exact mul_inv_cancel₀ hω0
  have key := p14_rho_comm hd R rho hcov hsum D hD a b
  simp only [p14_itp_mono id φ D hDe, Function.id_comp] at key
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at key
  have hpe : φ (b 0) * φ (b 1) = φ (a 0) * φ (a 1) := by
    have := key.trans (mul_comm _ _)
    exact mul_left_cancel₀ hab this
  rw [hφ, hφ, hφ, hφ, ← zpow_add₀ hω0, ← zpow_add₀ hω0] at hpe
  have h1 : ω ^ (e (b 0) + e (b 1) - (e (a 0) + e (a 1))) = 1 := by
    rw [zpow_sub₀ hω0, hpe, div_self (zpow_ne_zero _ hω0)]
  rw [hprim.zpow_eq_one_iff_dvd] at h1
  have hb : ∀ z, -1 ≤ e z ∧ e z ≤ 1 := by
    intro z; simp only [e]; split_ifs <;> omega
  have hb0 := hb (b 0); have hb1 := hb (b 1); have ha0 := hb (a 0); have ha1 := hb (a 1)
  have hz : e (b 0) + e (b 1) - (e (a 0) + e (a 1)) = 0 := by
    obtain ⟨k, hk⟩ := h1
    push_cast at hk
    omega
  simp only [e] at hz
  linear_combination -hz

theorem p14_comb {d : ℕ} (hd : 0 < d) (a b : Labels d 2)
    (h : ∀ x y : Fin d, x ≠ y →
      ((if a 0 = x then 1 else 0) + (if a 1 = x then 1 else 0) - (if b 0 = x then 1 else 0)
        - (if b 1 = x then 1 else 0) : ℤ) =
      (if a 0 = y then 1 else 0) + (if a 1 = y then 1 else 0) - (if b 0 = y then 1 else 0)
        - (if b 1 = y then 1 else 0)) :
    b = a ∨ b = swapInput a := by
  let c : Fin d → ℤ := fun z => (if a 0 = z then 1 else 0) + (if a 1 = z then 1 else 0) -
    (if b 0 = z then 1 else 0) - (if b 1 = z then 1 else 0)
  have hall : ∀ z, c z = c (a 0) := by
    intro z
    by_cases hz : z = a 0
    · rw [hz]
    · exact h z (a 0) hz
  have hs : ∑ z, c z = 0 := by
    simp only [c, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hall z)] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hca : c (a 0) = 0 := by
    rcases mul_eq_zero.mp hs with h' | h'
    · exfalso; have : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
      exact this h'
    · exact h'
  have h0 : ∀ z, c z = 0 := fun z => (hall z).trans hca
  have e1 := h0 (a 0); have e2 := h0 (a 1); have e3 := h0 (b 0); have e4 := h0 (b 1)
  simp only [c] at e1 e2 e3 e4
  suffices (b 0 = a 0 ∧ b 1 = a 1) ∨ (b 0 = a 1 ∧ b 1 = a 0) by
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; funext n; fin_cases n <;> simp [h1, h2]
    · right; funext n; fin_cases n <;> simp [swapInput, h1, h2]
  by_cases h1 : b 0 = a 0
  · left; refine ⟨h1, ?_⟩
    by_contra hn
    have hn' : a 1 ≠ b 1 := fun h => hn h.symm
    rw [h1] at e4
    simp [hn'] at e4 <;> (try split_ifs at e4) <;> omega
  · by_cases h2 : b 0 = a 1
    · right; refine ⟨h2, ?_⟩
      by_contra hn
      have hn' : a 0 ≠ b 1 := fun h => hn h.symm
      rw [h2] at e4
      simp [hn'] at e4 <;> (try split_ifs at e4) <;> omega
    · exfalso
      have h1' : a 0 ≠ b 0 := fun h => h1 h.symm
      have h2' : a 1 ≠ b 0 := fun h => h2 h.symm
      simp [h1', h2'] at e3 <;> (try split_ifs at e3) <;> omega

theorem p14_rho_swap {d : ℕ} (hd : 0 < d) (R : Branches d 2)
    (rho : Matrix (Labels d 2) (Labels d 2) ℂ) (hcov : IsLearningCovariant R)
    (hsum : ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then (if j = l then rho a b else 0) else 0)
    (a b : Labels d 2) : rho (swapInput a) (swapInput b) = rho a b := by
  have Z : ∀ a b : Labels d 2, ¬ (b = a ∨ b = swapInput a) → rho a b = 0 := by
    intro a b hn
    by_contra hne
    exact hn (p14_comb hd a b (fun x y hxy => p14_rho_diag hd R rho hcov hsum a b hne x y hxy))
  by_cases hm : b = a ∨ b = swapInput a
  · by_cases ha : a 0 = a 1
    · have hsa : swapInput a = a := by
        funext n; fin_cases n <;> simp [swapInput, ha]
      rcases hm with rfl | rfl <;> simp [hsa]
    · have := p14_rho_perm hd R rho hcov hsum (a 0) (a 1) ha a b
      have hτa : (Equiv.swap (a 0) (a 1) : Fin d → Fin d) ∘ a = swapInput a := by
        funext n; fin_cases n <;> simp [swapInput]
      have hτb : (Equiv.swap (a 0) (a 1) : Fin d → Fin d) ∘ b = swapInput b := by
        rcases hm with rfl | rfl
        · exact hτa
        · funext n; fin_cases n <;> simp [swapInput]
      rw [hτa, hτb] at this
      exact this
  · rw [Z a b hm, Z _ _ ?_]
    intro h
    apply hm
    rcases h with h | h
    · left; exact p14_swapInput_inj.mp h
    · right; exact p14_swapInput_inj.mp h


theorem p14_transfer {d : ℕ} (hd : 0 < d) (k : ℕ) (R : Branches d 2)
    (rho : Matrix (Labels d 2) (Labels d 2) ℂ)
    (hsum : ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then (if j = l then rho a b else 0) else 0)
    (hrs : ∀ a b, rho (swapInput a) (swapInput b) = rho a b)
    (hR : LearningInstrument k R) : LearningInstrument k (swapAverage R) := by
  obtain ⟨hpsd, A, hA, hAsum⟩ := hR
  have hA_eq : ∀ j a l b, A (j,a) (l,b) = if j = l then rho a b else 0 := by
    intro j a l b
    have := hAsum ⟨0, hd⟩ j a ⟨0, hd⟩ l b
    rw [hsum] at this
    simpa using this.symm
  refine ⟨fun i => ?_, A, hA, ?_⟩
  · have hS : swapAverage R i = (1/2 : ℂ) •
        (R i + (R i).submatrix (p14_wireEquiv d) (p14_wireEquiv d)) := by
      rw [← p14_swapLearner_sub]; rfl
    rw [hS]
    refine Matrix.PosSemidef.smul ((hpsd i).add ((hpsd i).submatrix _)) ?_
    rw [Complex.nonneg_iff]; norm_num
  · intro t j a s l b
    simp only [p14_swapAverage_apply, ← Finset.mul_sum, Finset.sum_add_distrib, hsum,
      p14_swapInput_inj, hrs, hA_eq]
    split_ifs <;> ring

theorem p14_main {d : ℕ} (hd : 2 ≤ d) (R : Branches d 2)
    (hR : LearningInstrument 2 R) (hs : IsLearningSymmetric R) :
    LearningInstrument 2 (swapAverage R) ∧ IsLearningSymmetric (swapAverage R) ∧
    swapAverage R = swapLearner (swapAverage R) ∧
    learningScore (swapAverage R) = learningScore R ∧
    (∀ j, ∑ i, outcomeBlocks (swapAverage R) i j = ∑ i, outcomeBlocks R i j) ∧
    (IsOptimal (by omega : 0 < d) R → IsOptimal (by omega : 0 < d) (swapAverage R)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨hpsd, A, hA, hAsum⟩ := hR
  have hA2 : A.PosSemidef ∧ ParallelTraining A := by
    simpa [CausalTraining] using hA
  obtain ⟨rho, -, -, hrho⟩ := hA2.2
  have hsum : ∀ t j a s l b, (∑ i, R i (t,(j,a)) (s,(l,b))) =
      if t = s then (if j = l then rho a b else 0) else 0 := by
    intro t j a s l b; rw [hAsum, hrho]
  have hrs := p14_rho_swap hd0 R rho hs.2.1 hsum
  refine ⟨p14_transfer hd0 2 R rho hsum hrs ⟨hpsd, A, hA, hAsum⟩, p14_sym R hs,
    p14_swapLearner_swapAverage R, ?_, ?_, ?_⟩
  · unfold learningScore; rw [p14_rep_swapAverage]
  · intro j
    ext x y
    simp only [Matrix.sum_apply, outcomeBlocks, p14_swapAverage_apply, ← Finset.mul_sum,
      Finset.sum_add_distrib, hsum, p14_swapInput_inj, hrs]
    ring
  · rintro ⟨h0, hopt⟩
    refine ⟨p14_transfer hd0 0 R rho hsum hrs h0, fun S hS => ?_⟩
    have : learningDistance hd0 (swapAverage R) = learningDistance hd0 R := by
      unfold learningDistance; rw [p14_rep_swapAverage]
    rw [this]
    exact hopt S hS


theorem solution {d : ℕ} (hd : 2 ≤ d) (R : Branches d 2)
    (hR : LearningInstrument 2 R) (hs : IsLearningSymmetric R) :
    LearningInstrument 2 (swapAverage R) ∧ IsLearningSymmetric (swapAverage R) ∧
    swapAverage R = swapLearner (swapAverage R) ∧
    learningScore (swapAverage R) = learningScore R ∧
    (∀ j, ∑ i, outcomeBlocks (swapAverage R) i j = ∑ i, outcomeBlocks R i j) ∧
    (IsOptimal (by omega : 0 < d) R → IsOptimal (by omega : 0 < d) (swapAverage R)) :=
  p14_main hd R hR hs

end
