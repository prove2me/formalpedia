-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P04.nonoptimal_le_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:46:32.235732+00:00
-- url     : https://prove2.me/submissions/f50bee8d-b162-4524-9ea7-997313198f02

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04
noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

end QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms
open QAlgorithms.Papers.Independent.Extend50.P04
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable

namespace S110P04

lemma count_fiber {d N : ℕ} (a : Fin N) (w : Fin N → Fin d) :
    (Finset.univ.filter (fun z : Fin N → Fin d => ∀ i, i ≠ a → w i = z i)).card = d := by
  have : Finset.univ.filter (fun z : Fin N → Fin d => ∀ i, i ≠ a → w i = z i) =
      Finset.univ.image (fun t : Fin d => Function.update w a t) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨z a, ?_⟩
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · rw [Function.update_of_ne hi]; exact h i hi
    · rintro ⟨t, rfl⟩ i hi
      rw [Function.update_of_ne hi]
  rw [this, Finset.card_image_of_injective _ (Function.update_injective w a)]
  simp

lemma bell_eq (d N : ℕ) (a : Fin N) :
    pbtBellProjector d N a =
      (Matrix.of fun (z : Fin N → Fin d) (x : Alice d N) =>
        if x.1 a = x.2 ∧ ∀ i, i ≠ a → x.1 i = z i then ((d : ℂ)⁻¹) else 0)ᴴ *
      (Matrix.of fun (z : Fin N → Fin d) (x : Alice d N) =>
        if x.1 a = x.2 ∧ ∀ i, i ≠ a → x.1 i = z i then ((d : ℂ)⁻¹) else 0) := by
  ext x y
  have hd : (d : ℂ) ≠ 0 := by
    have := (x.2).pos
    exact_mod_cast this.ne'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, pbtBellProjector]
  have key : ∀ z : Fin N → Fin d,
      star (if x.1 a = x.2 ∧ ∀ i, i ≠ a → x.1 i = z i then ((d : ℂ)⁻¹) else 0) *
        (if y.1 a = y.2 ∧ ∀ i, i ≠ a → y.1 i = z i then ((d : ℂ)⁻¹) else 0) =
      if x.1 a = x.2 ∧ y.1 a = y.2 ∧ ∀ i, i ≠ a → x.1 i = y.1 i then
        (if ∀ i, i ≠ a → x.1 i = z i then (d : ℂ)⁻¹ * (d : ℂ)⁻¹ else 0) else 0 := by
    intro z
    by_cases h1 : x.1 a = x.2 <;> by_cases h2 : y.1 a = y.2 <;> simp only [h1, h2, true_and, false_and, if_false, star_zero, zero_mul, mul_zero]
    by_cases h3 : ∀ i, i ≠ a → x.1 i = y.1 i
    · rw [if_pos h3]
      by_cases h4 : ∀ i, i ≠ a → x.1 i = z i
      · have h5 : ∀ i, i ≠ a → y.1 i = z i := fun i hi => (h3 i hi).symm.trans (h4 i hi)
        rw [if_pos h4, if_pos h5, if_pos h4]; simp
      · have h5 : ¬ ∀ i, i ≠ a → y.1 i = z i := fun h5 => h4 fun i hi => (h3 i hi).trans (h5 i hi)
        rw [if_neg h4, if_neg h5, if_neg h4]; simp
    · rw [if_neg h3]
      by_cases h4 : ∀ i, i ≠ a → x.1 i = z i
      · have h5 : ¬ ∀ i, i ≠ a → y.1 i = z i := fun h5 => h3 fun i hi => (h4 i hi).trans (h5 i hi).symm
        rw [if_pos h4, if_neg h5]; simp
      · rw [if_neg h4]; simp
  simp_rw [key]
  split_ifs with h
  · rw [← Finset.sum_filter, Finset.sum_const, count_fiber, nsmul_eq_mul]
    field_simp
  · simp


lemma signal_nonneg (d N : ℕ) (a : Fin N) : 0 ≤ pbtSignal d N a := by
  have h0 : (0 : Matrix (Alice d N) (Alice d N) ℂ) ≤ pbtBellProjector d N a := by
    rw [Matrix.nonneg_iff_posSemidef, bell_eq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hc : (0 : ℂ) ≤ ((d : ℂ) ^ (N - 1))⁻¹ := by
    have : ((d : ℂ) ^ (N - 1))⁻¹ = (((d : ℝ) ^ (N - 1))⁻¹ : ℝ) := by push_cast; rfl
    rw [this]; exact Complex.zero_le_real.mpr (by positivity)
  unfold pbtSignal
  exact smul_nonneg hc h0

lemma signalSum_nonneg (d N : ℕ) : 0 ≤ signalSum d N :=
  Finset.sum_nonneg fun a _ => signal_nonneg d N a

lemma inverseRoot_sa (d N : ℕ) : IsSelfAdjoint (inverseRoot d N) :=
  cfc_predicate _ _

lemma supportEffect_nonneg (d N : ℕ) (a : Fin N) : 0 ≤ supportEffect d N a := by
  have h := star_left_conjugate_nonneg (signal_nonneg d N a) (inverseRoot d N)
  rwa [(inverseRoot_sa d N).star_eq] at h

lemma sum_supportEffect (d N : ℕ) :
    ∑ a, supportEffect d N a =
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) (signalSum d N) := by
  have hS : IsSelfAdjoint (signalSum d N) := IsSelfAdjoint.of_nonneg (signalSum_nonneg d N)
  have hfin := (Matrix.finite_real_spectrum (A := signalSum d N))
  unfold supportEffect
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change inverseRoot d N * signalSum d N * inverseRoot d N = _
  unfold inverseRoot
  rw [cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _),
    cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ (signalSum d N) hS]

lemma complement_nonneg (d N : ℕ) : 0 ≤ pbtSupportComplement d N := by
  have hS : IsSelfAdjoint (signalSum d N) := IsSelfAdjoint.of_nonneg (signalSum_nonneg d N)
  have hfin := (Matrix.finite_real_spectrum (A := signalSum d N))
  unfold pbtSupportComplement
  rw [sum_supportEffect, ← cfc_one ℝ (signalSum d N),
    ← cfc_sub _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
  apply cfc_nonneg
  intro x _
  simp only [Pi.one_apply]
  rcases le_or_gt x 0 with hx | hx
  · rw [Real.sqrt_eq_zero'.mpr hx]; simp
  · have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    have : (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
      rw [mul_assoc, mul_comm x, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hx.le, inv_mul_cancel₀ hx.ne']
    rw [this]; simp

lemma fullEffect_nonneg (d n : ℕ) (a : Fin (n + 1)) : 0 ≤ fullEffect d (n + 1) a := by
  unfold fullEffect
  have hc : (0 : ℂ) ≤ ((n + 1 : ℕ) : ℂ)⁻¹ := by
    have : (((n + 1 : ℕ) : ℂ))⁻¹ = (((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) := by push_cast; rfl
    rw [this]; exact Complex.zero_le_real.mpr (by positivity)
  exact add_nonneg (supportEffect_nonneg _ _ a) (smul_nonneg hc (complement_nonneg _ _))

lemma sum_fullEffect (d n : ℕ) : ∑ a, fullEffect d (n + 1) a = 1 := by
  unfold fullEffect pbtSupportComplement
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n), one_smul]
  abel

lemma root_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : 0 ≤ A) :
    (positiveRoot A)ᴴ * positiveRoot A = A := by
  have hS : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hP : IsSelfAdjoint (positiveRoot A) := cfc_predicate _ _
  have hfin := (Matrix.finite_real_spectrum (A := A))
  rw [← Matrix.star_eq_conjTranspose, hP.star_eq]
  unfold positiveRoot
  rw [← cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
  conv_rhs => rw [← cfc_id' ℝ A hS]
  apply cfc_congr
  intro x hx
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hA hx)


lemma inner_act {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    inner ℂ (act K ψ) (act K ψ) = ((Kᴴ * K) *ᵥ (WithLp.ofLp ψ)) ⬝ᵥ star (WithLp.ofLp ψ) := by
  unfold act
  rw [EuclideanSpace.inner_toLp_toLp, Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, dotProduct_comm]

lemma branch_sum (d n : ℕ) (O : Matrix ((Fin (n + 1) → Fin d)) ((Fin (n + 1) → Fin d)) ℂ) :
    ∑ a, ‖pbtLuedersBranch d (n + 1) O a‖ ^ 2 = ‖initialState d (n + 1) O‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have hn : ∀ x : EuclideanSpace ℂ (Whole d (n + 1)), ((‖x‖ : ℝ) : ℂ) ^ 2 = inner ℂ x x := by
    intro x; rw [inner_self_eq_norm_sq_to_K]; rfl
  simp_rw [hn]
  unfold pbtLuedersBranch
  simp_rw [inner_act]
  rw [← sum_dotProduct, ← Matrix.sum_mulVec, EuclideanSpace.inner_eq_star_dotProduct]
  have : ∑ a, (Matrix.kronecker (positiveRoot (fullEffect d (n + 1) a)) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ))ᴴ *
      Matrix.kronecker (positiveRoot (fullEffect d (n + 1) a)) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ) = 1 := by
    have e : ∀ a, (Matrix.kronecker (positiveRoot (fullEffect d (n + 1) a)) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ))ᴴ *
        Matrix.kronecker (positiveRoot (fullEffect d (n + 1) a)) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ) =
        Matrix.kronecker (fullEffect d (n + 1) a) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ) := by
      intro a
      unfold Matrix.kronecker
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
        root_sq _ (fullEffect_nonneg d n _), Matrix.one_mul]
    simp_rw [e]
    have s2 : ∑ a, Matrix.kronecker (fullEffect d (n + 1) a) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ) =
        Matrix.kronecker (∑ a, fullEffect d (n + 1) a) (1 : Matrix (Alice d (n+1)) (Alice d (n+1)) ℂ) := by
      ext i j
      simp [Matrix.kronecker, Matrix.sum_apply, Finset.sum_mul]
    rw [s2, sum_fullEffect]
    unfold Matrix.kronecker
    exact Matrix.one_kronecker_one
  rw [this, Matrix.one_mulVec]


lemma initial_norm (d n : ℕ) (hd : 0 < d) :
    ‖initialState d (n + 1) (1 : Matrix ((Fin (n + 1) → Fin d)) ((Fin (n + 1) → Fin d)) ℂ)‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  have key : ∀ x : Whole d (n + 1),
      ‖(initialState d (n + 1) (1 : Matrix ((Fin (n + 1) → Fin d)) ((Fin (n + 1) → Fin d)) ℂ)) x‖ ^ 2 =
        if x.1 = x.2 then ((d : ℝ) ^ (n + 2))⁻¹ else 0 := by
    rintro ⟨⟨f, s⟩, ⟨g, t⟩⟩
    simp only [initialState, PiLp.toLp_apply, Prod.mk.injEq]
    by_cases h1 : f = g
    · subst h1
      by_cases h2 : s = t
      · subst h2
        simp only [if_true, and_self, Matrix.one_apply_eq, norm_div, norm_one, div_pow, one_pow]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity), one_div]
      · simp [h2]
    · simp [h1]
  rw [Fintype.sum_prod_type]
  simp_rw [key, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp
  ring


lemma count_removeNth {d n : ℕ} (a : Fin (n + 1)) (w : Fin n → Fin d) (c : ℝ) :
    ∑ g : Fin (n + 1) → Fin d, (if deletePort a g = w then c else 0) = d * c := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin d) a).sum_comp, Fintype.sum_prod_type]
  have : ∀ (t : Fin d) (v : Fin n → Fin d),
      deletePort a ((Fin.insertNthEquiv (fun _ => Fin d) a) (t, v)) = v := by
    intro t v
    funext i
    simp [deletePort, Fin.insertNthEquiv]
  simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

lemma ideal_norm (d n : ℕ) (hd : 0 < d) (a : Fin (n + 1)) :
    ‖idealState d n a (1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  have key : ∀ x : Whole d (n + 1),
      ‖(idealState d n a (1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)) x‖ ^ 2 =
        if x.1.1 a = x.1.2 then (if x.2.1 a = x.2.2 then
          (if deletePort a x.2.1 = deletePort a x.1.1 then ((d : ℝ) ^ (n + 2))⁻¹ else 0) else 0) else 0 := by
    rintro ⟨⟨f, s⟩, ⟨g, t⟩⟩
    by_cases h1 : f a = s
    · by_cases h2 : g a = t
      · by_cases h3 : deletePort a g = deletePort a f
        · simp [idealState, h1, h2, h3, Matrix.one_apply]
          rw [abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, inv_pow, Real.sq_sqrt (by positivity),
            pow_add, mul_inv]
        · have h3' : deletePort a f ≠ deletePort a g := fun h => h3 h.symm
          simp [idealState, h1, h2, h3, h3']
      · simp [idealState, h2]
    · simp [idealState, h1]
  rw [Fintype.sum_prod_type]
  simp_rw [key, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq]
  simp_rw [count_removeNth, Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp
  ring

end S110P04

theorem solution (d n : ℕ) (hd : 2 ≤ d) :
    QAlgorithms.Papers.Independent.Extend50.P04.nonoptimalFidelity d n ≤ 1 := by
  have hd0 : 0 < d := by omega
  unfold nonoptimalFidelity recyclingFidelity
  calc _ ≤ ∑ a : Fin (n + 1), ‖pbtLuedersBranch d (n + 1) 1 a‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_of_le_one_right (sq_nonneg _)
        refine (norm_inner_le_norm _ _).trans ?_
        have h1 : ‖idealState d n a (1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)‖ = 1 := by
          have := S110P04.ideal_norm d n hd0 a
          nlinarith [norm_nonneg (idealState d n a (1 : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ))]
        rw [h1, one_mul]
        unfold normalizedBranch
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        rcases (norm_nonneg (pbtLuedersBranch d (n + 1) 1 a)).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [inv_mul_cancel₀ h.ne']
    _ = 1 := by rw [S110P04.branch_sum, S110P04.initial_norm d n hd0]

end
