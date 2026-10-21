-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P30.su_two_different
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:17:35.07758+00:00
-- url     : https://prove2.me/submissions/31f04604-8eab-46d3-816b-cd4f9a60bf19

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30
noncomputable section
open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix Kronecker

/-- permutation-type matrix for a function τ -/
def g66d_P {ι : Type*} [DecidableEq ι] (τ : ι → ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y => if y = τ x then 1 else 0

theorem g66d_Pconj {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ι) (A : Matrix ι ι ℂ) (x y : ι) :
    (g66d_P τ * A * (g66d_P τ)ᴴ) x y = A (τ x) (τ y) := by
  simp only [g66d_P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]

theorem g66d_Punit {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    g66d_P σ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  simp only [g66d_P, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
  simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, σ.injective.ne hij, eq_comm]

theorem g66d_Pkron {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ι) :
    (g66d_P σ ⊗ₖ g66d_P σ) = g66d_P (fun u : ι × ι => (σ u.1, σ u.2)) := by
  ext u v
  simp only [Matrix.kroneckerMap_apply, g66d_P, Matrix.of_apply, Prod.ext_iff]
  split_ifs <;> simp_all <;> tauto

theorem g66d_fix (f T : ℂ) (hf : f ≠ 1) (h : f * T = T) : T = 0 := by
  have : (f - 1) * T = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hf
  · exact h1

/-- swap operator -/
def g66d_F (ι : Type*) [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun u v => if v = u.swap then 1 else 0

theorem g66d_F_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ) :
    (W ⊗ₖ W) * g66d_F ι = g66d_F ι * (W ⊗ₖ W) := by
  ext u z
  simp only [g66d_F, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one,
    mul_zero, ite_mul, one_mul, zero_mul]
  simp_rw [show ∀ j : ι × ι, (z = j.swap) ↔ (j = z.swap) from fun j =>
    ⟨fun h => by rw [h, Prod.swap_swap], fun h => by rw [h, Prod.swap_swap]⟩]
  rw [Finset.sum_ite_eq' Finset.univ z.swap, Finset.sum_ite_eq' Finset.univ u.swap]
  simp [Matrix.kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]

theorem g66d_inv_F {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (W ⊗ₖ W) * g66d_F ι * (W ⊗ₖ W)ᴴ = g66d_F ι := by
  have hK : (W ⊗ₖ W) ∈ Matrix.unitaryGroup (ι × ι) ℂ := Matrix.kronecker_mem_unitary hW hW
  have hK' := Matrix.mem_unitaryGroup_iff.mp hK
  rw [Matrix.star_eq_conjTranspose] at hK'
  rw [g66d_F_comm, Matrix.mul_assoc, hK', Matrix.mul_one]

theorem g66d_inv_one {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (W ⊗ₖ W) * 1 * (W ⊗ₖ W)ᴴ = 1 := by
  have hK : (W ⊗ₖ W) ∈ Matrix.unitaryGroup (ι × ι) ℂ := Matrix.kronecker_mem_unitary hW hW
  have hK' := Matrix.mem_unitaryGroup_iff.mp hK
  rw [Matrix.star_eq_conjTranspose] at hK'
  rw [Matrix.mul_one, hK']

theorem g66d_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix (ι × ι) (ι × ι) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup ι ℂ, (W ⊗ₖ W) * T * (W ⊗ₖ W)ᴴ = T)
    (p q r s : ι) (hn : ¬ ((p = r ∧ q = s) ∨ (p = s ∧ q = r))) : T (p, q) (r, s) = 0 := by
  have key : ∀ c : ι, (let w : ι → ℂ := fun k => if k = c then Complex.I else 1
      (w p * w q * star (w r * w s)) * T (p, q) (r, s) = T (p, q) (r, s)) := by
    intro c w
    have hW : Matrix.diagonal w ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k
      simp only [w, Pi.star_apply]; split_ifs <;> simp
    have := congrFun (congrFun (h _ hW) (p, q)) (r, s)
    rw [Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at this
    simp only [Pi.star_apply] at this
    linear_combination this
  have hI : Complex.I ≠ 1 := by intro h; simpa using congrArg Complex.im h
  have hII : Complex.I * Complex.I ≠ 1 := by rw [Complex.I_mul_I]; norm_num
  by_cases hA : p ≠ r ∧ p ≠ s
  · have k := key p
    simp only [if_pos rfl, if_neg (Ne.symm hA.1), if_neg (Ne.symm hA.2), star_one, mul_one] at k
    by_cases hq : q = p
    · simp only [if_pos hq] at k; exact g66d_fix _ _ hII k
    · simp only [if_neg hq, mul_one] at k; exact g66d_fix _ _ hI k
  · have k := key q
    simp only [if_pos rfl] at k
    have hIc : Complex.I * star Complex.I = 1 := by simp [Complex.I_mul_I]
    rcases not_and_or.mp hA with h1 | h1 <;> push_neg at h1
    · subst h1
      have hqs : s ≠ q := fun e => hn (Or.inl ⟨rfl, e.symm⟩)
      simp only [if_neg hqs, star_one, mul_one] at k
      by_cases hpq : p = q
      · simp only [if_pos hpq, ↓reduceIte] at k
        refine g66d_fix _ _ ?_ k
        rw [show Complex.I * Complex.I * star Complex.I = Complex.I * (Complex.I * star Complex.I) by ring, hIc,
          mul_one]; exact hI
      · simp only [if_neg hpq, one_mul, star_one, mul_one] at k; exact g66d_fix _ _ hI k
    · subst h1
      have hqr : r ≠ q := fun e => hn (Or.inr ⟨rfl, e.symm⟩)
      simp only [if_neg hqr, one_mul] at k
      by_cases hpq : p = q
      · simp only [if_pos hpq, ↓reduceIte] at k
        refine g66d_fix _ _ ?_ k
        rw [show Complex.I * Complex.I * star Complex.I = Complex.I * (Complex.I * star Complex.I) by ring, hIc,
          mul_one]; exact hI
      · simp only [if_neg hpq, one_mul, star_one, mul_one] at k; exact g66d_fix _ _ hI k

theorem g66d_perm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix (ι × ι) (ι × ι) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup ι ℂ, (W ⊗ₖ W) * T * (W ⊗ₖ W)ᴴ = T) (σ : Equiv.Perm ι)
    (p q r s : ι) : T (σ p, σ q) (σ r, σ s) = T (p, q) (r, s) := by
  have := congrFun (congrFun (h _ (g66d_Punit σ)) (p, q)) (r, s)
  rw [g66d_Pkron, g66d_Pconj] at this
  exact this

theorem g66d_two {ι : Type*} [DecidableEq ι] (a b p q : ι) (hab : a ≠ b) (hpq : p ≠ q) :
    ∃ σ : Equiv.Perm ι, σ a = p ∧ σ b = q := by
  set b' := Equiv.swap a p b
  have hb' : p ≠ b' := by
    intro e
    have : Equiv.swap a p b = Equiv.swap a p a := by rw [Equiv.swap_apply_left]; exact e.symm
    exact hab ((Equiv.swap a p).injective this).symm
  refine ⟨Equiv.swap b' q * Equiv.swap a p, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hb' hpq
  · simp only [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left b' q

theorem g66d_house {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (1 - (2 : ℂ) • Matrix.vecMulVec v (star v)) ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star]
  have hP : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) = Matrix.vecMulVec v (star v) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [hP]
  module

theorem g66d_commutant {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix (ι × ι) (ι × ι) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup ι ℂ, (W ⊗ₖ W) * T * (W ⊗ₖ W)ᴴ = T) (a b : ι) (hab : a ≠ b) :
    T = T (a, b) (a, b) • 1 + T (a, b) (b, a) • g66d_F ι := by
  set x := T (a, b) (a, b)
  set y := T (a, b) (b, a)
  set α := T (a, a) (a, a)
  have hx : ∀ p q, p ≠ q → T (p, q) (p, q) = x := by
    intro p q hpq
    obtain ⟨σ, h1, h2⟩ := g66d_two a b p q hab hpq
    rw [← h1, ← h2]; exact g66d_perm_inv T h σ a b a b
  have hy : ∀ p q, p ≠ q → T (p, q) (q, p) = y := by
    intro p q hpq
    obtain ⟨σ, h1, h2⟩ := g66d_two a b p q hab hpq
    rw [← h1, ← h2]; exact g66d_perm_inv T h σ a b b a
  have hα : ∀ p, T (p, p) (p, p) = α := by
    intro p
    have := g66d_perm_inv T h (Equiv.swap a p) a a a a
    simpa [Equiv.swap_apply_left] using this
  set S := T - x • (1 : Matrix (ι × ι) (ι × ι) ℂ) - y • g66d_F ι with hSdef
  set β := α - x - y
  have hSent : S = β • Matrix.diagonal (fun u : ι × ι => if u.1 = u.2 then (1 : ℂ) else 0) := by
    ext ⟨p, q⟩ ⟨r, s⟩
    simp only [hSdef, Matrix.sub_apply, Matrix.smul_apply, g66d_F, Matrix.of_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Prod.swap_prod_mk, Prod.mk.injEq, smul_eq_mul]
    by_cases h1 : p = r ∧ q = s
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases hpq : p = q
      · subst hpq; simp [hα, β]
      · simp [hpq, hx p q hpq, Ne.symm hpq]
    · by_cases h2 : p = s ∧ q = r
      · obtain ⟨rfl, rfl⟩ := h2
        have hpq : p ≠ q := fun e => h1 ⟨e, e.symm⟩
        simp [hpq, hy p q hpq, Ne.symm hpq]
      · rw [g66d_zero T h p q r s (by tauto)]
        have h3 : ¬ (r = q ∧ s = p) := fun e => h2 ⟨e.2.symm, e.1.symm⟩
        simp [h1, h3]
  have hSinv : ∀ W ∈ Matrix.unitaryGroup ι ℂ, (W ⊗ₖ W) * S * (W ⊗ₖ W)ᴴ = S := by
    intro W hW
    simp only [hSdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h W hW,
      g66d_inv_F W hW]
    rw [g66d_inv_one W hW]
  -- Householder
  set v : ι → ℂ := fun k => if k = a then 3/5 else if k = b then 4/5 else 0
  have hv : star v ⬝ᵥ v = 1 := by
    simp only [dotProduct, Pi.star_apply]
    rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab]
    · simp only [v, if_pos rfl, if_neg (Ne.symm hab)]; norm_num
    · intro c _ hc; simp [v, hc.1, hc.2]
  set W := 1 - (2 : ℂ) • Matrix.vecMulVec v (star v)
  have hW := g66d_house v hv
  have e := congrFun (congrFun (hSinv W hW) (a, a)) (a, a)
  rw [hSent, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul, ↓reduceIte, mul_one] at e
  have hWa : ∀ k, W a k = if k = a then 7/25 else if k = b then -24/25 else 0 := by
    intro k
    simp only [W, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      v, if_pos rfl, smul_eq_mul]
    by_cases hka : k = a
    · subst hka; simp; norm_num
    · by_cases hkb : k = b
      · subst hkb; simp [hka, Ne.symm hka]; norm_num
      · simp [hka, hkb, Ne.symm hka]
  have hsum : (∑ u : ι × ι, W a u.1 * W a u.2 * (if u.1 = u.2 then (1 : ℂ) else 0) *
      star (W a u.1 * W a u.2)) = 334177 / 390625 := by
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab]
    · rw [hWa, hWa, if_pos rfl, if_neg (Ne.symm hab), if_pos rfl]; norm_num
    · intro c _ hc; rw [hWa, if_neg hc.1, if_neg hc.2]; simp
  have e2 : β * (334177 / 390625) = β := by
    rw [← hsum]; convert e using 2
  have hβ : β = 0 := by
    have : β * (334177 / 390625 - 1) = 0 := by linear_combination e2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · norm_num at h0
  rw [hβ, zero_smul] at hSent
  rw [hSdef, sub_sub, sub_eq_zero] at hSent
  exact hSent

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

theorem g66d_FF {ι : Type*} [Fintype ι] [DecidableEq ι] : g66d_F ι * g66d_F ι = 1 := by
  ext u v
  simp only [g66d_F, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp_rw [show ∀ j : ι × ι, (v = j.swap) ↔ (j = v.swap) from fun j =>
    ⟨fun h => by rw [h, Prod.swap_swap], fun h => by rw [h, Prod.swap_swap]⟩]
  rw [Finset.sum_ite_eq' Finset.univ v.swap]
  simp only [Finset.mem_univ, if_true]
  by_cases h : u = v
  · subst h; simp
  · rw [if_neg h]
    rw [if_neg]
    intro e; apply h; rw [← Prod.swap_swap u, ← e, Prod.swap_swap]

theorem g66d_trF {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (g66d_F ι).trace = Fintype.card ι := by
  simp only [Matrix.trace, Matrix.diag, g66d_F, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp only [Prod.swap_prod_mk, Prod.mk.injEq]
  simp_rw [show ∀ p q : ι, (p = q ∧ q = p) ↔ (q = p) from fun p q => ⟨fun h => h.2, fun h => ⟨h.symm, h⟩⟩]
  simp [Finset.sum_ite_eq]

theorem g66d_KFK {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) : (W ⊗ₖ W)ᴴ * g66d_F ι * (W ⊗ₖ W) = g66d_F ι := by
  have hK : (W ⊗ₖ W) ∈ Matrix.unitaryGroup (ι × ι) ℂ := Matrix.kronecker_mem_unitary hW hW
  have hK' := Matrix.mem_unitaryGroup_iff'.mp hK
  rw [Matrix.star_eq_conjTranspose] at hK'
  rw [Matrix.mul_assoc, ← g66d_F_comm, ← Matrix.mul_assoc, hK', Matrix.one_mul]

theorem g66d_coe_cont {d : ℕ} (i j : Fin d) :
    Continuous (fun U : SU d => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g66d_root {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ c : ℂ, star c * c = 1 ∧ c • W ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  set w := W.det
  have hw : star w * w = 1 := by
    have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    exact this
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  set r : ℂ := w ^ ((d : ℂ)⁻¹)
  have hr : r ^ d = w := Complex.cpow_nat_inv_pow w (by omega)
  have hr0 : r ≠ 0 := by intro h0; rw [h0, zero_pow (by omega)] at hr; exact hw0 hr.symm
  have hrn : ‖r‖ = 1 := by
    have h2 : ‖w‖ = 1 := by
      have : ‖star w * w‖ = 1 := by rw [hw]; simp
      rw [norm_mul, norm_star] at this
      nlinarith [norm_nonneg w]
    rw [← hr, norm_pow] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg r) (by omega)).mp h2
  refine ⟨r⁻¹, ?_, ?_⟩
  · have : star r * r = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hrn]; simp
    rw [star_inv₀, ← mul_inv, this, inv_one]
  · rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hW ⊢
      rw [star_smul, smul_mul_smul_comm, hW]
      have : r⁻¹ * star r⁻¹ = 1 := by
        rw [star_inv₀, Complex.star_def, ← mul_inv, Complex.mul_conj', hrn]; simp
      rw [this, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hr]
      exact inv_mul_cancel₀ hw0

theorem g66d_PF_cont {d : ℕ} (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (u v : Fin d × Fin d) :
    Continuous (fun U : SU d => (((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) * X *
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) u v) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_finsetSum _ fun l _ => ((g66d_coe_cont _ _).mul (g66d_coe_cont _ _)).mul continuous_const).mul
      ((g66d_coe_cont _ _).mul (g66d_coe_cont _ _)).star

theorem g66d_tr_int {α ι : Type*} [MeasurableSpace α] [Fintype ι] (mu : Measure α)
    (f : α → Matrix ι ι ℂ) (hf : ∀ k l, Integrable (fun a => f a k l) mu) (C : Matrix ι ι ℂ) :
    ((Matrix.of fun k l => ∫ a, f a k l ∂mu) * C).trace = ∫ a, (f a * C).trace ∂mu := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hf k l).mul_const _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hf k l).mul_const _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_mul_const]

/-- Pair twirl over Haar SU(d). -/
theorem g66d_ptwirl {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SU d)) [mu.IsHaarMeasure]
    [IsProbabilityMeasure mu] (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (∀ u v, Integrable (fun U : SU d => (((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) * X *
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) u v) mu) ∧
    ∃ x y : ℂ, (Matrix.of fun u v => ∫ U : SU d, (((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) * X *
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) u v ∂mu) = x • 1 + y • g66d_F (Fin d) ∧
      x * d ^ 2 + y * d = X.trace ∧ x * d + y * d ^ 2 = (X * g66d_F (Fin d)).trace := by
  set K : SU d → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := fun U =>
    (U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ) with hKdef
  have hint : ∀ u v, Integrable (fun U : SU d => (K U * X * (K U)ᴴ) u v) mu := fun u v =>
    (g66d_PF_cont X u v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint, ?_⟩
  set T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := Matrix.of fun u v => ∫ U : SU d,
    (K U * X * (K U)ᴴ) u v ∂mu with hT
  have hSU : ∀ V : SU d, K V * T * (K V)ᴴ = T := by
    intro V
    ext a b
    have e1 : ∀ U : SU d, K (V * U) * X * (K (V * U))ᴴ = K V * (K U * X * (K U)ᴴ) * (K V)ᴴ := by
      intro U
      simp only [hKdef, Submonoid.coe_mul, Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    have e2 := integral_mul_left_eq_self (μ := mu) (fun U : SU d => (K U * X * (K U)ᴴ) a b) V
    simp only [e1] at e2
    rw [hT, Matrix.of_apply, ← e2]
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_mul_const, integral_finsetSum]
      · refine congrArg (· * _) (Finset.sum_congr rfl fun l _ => ?_)
        rw [integral_const_mul]
      · intro l _; exact (hint l k).const_mul _
    · intro k _
      exact (integrable_finsetSum _ fun l _ => (hint l k).const_mul _).mul_const _
  have hU : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, (W ⊗ₖ W) * T * (W ⊗ₖ W)ᴴ = T := by
    intro W hW
    obtain ⟨c, hc, hcW⟩ := g66d_root (by omega) W hW
    have := hSU ⟨c • W, hcW⟩
    simp only [hKdef, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul] at this
    rw [show star (c * c) * (c * c) = 1 by rw [star_mul']; linear_combination (star c * c + 1) * hc] at this
    rw [one_smul] at this
    exact this
  have a0 : Fin d := ⟨0, by omega⟩
  have hab : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℂ, T = x • 1 + y • g66d_F (Fin d) := ⟨_, _, g66d_commutant T hU _ _ hab⟩
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have htr : T.trace = X.trace := by
      simp only [Matrix.trace, Matrix.diag, hT, Matrix.of_apply]
      rw [← integral_finsetSum _ fun k _ => hint k k]
      have : ∀ U : SU d, ∑ k, (K U * X * (K U)ᴴ) k k = X.trace := by
        intro U
        have hK : (K U)ᴴ * K U = 1 := by
          have := Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary U.2.1 U.2.1)
          rw [Matrix.star_eq_conjTranspose] at this; exact this
        have := Matrix.trace_mul_cycle (K U) X (K U)ᴴ
        rw [hK, Matrix.one_mul] at this
        exact this
      simp only [this, integral_const, probReal_univ, one_smul]; rfl
    rw [← htr, hxy, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, g66d_trF]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul, Nat.cast_mul]; ring
  · have htr : (T * g66d_F (Fin d)).trace = (X * g66d_F (Fin d)).trace := by
      rw [hT, g66d_tr_int mu (fun U => K U * X * (K U)ᴴ) hint]
      have : ∀ U : SU d, (K U * X * (K U)ᴴ * g66d_F (Fin d)).trace =
          (X * g66d_F (Fin d)).trace := by
        intro U
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (K U)]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (K U)ᴴ, g66d_KFK _ U.2.1]
      simp only [this, integral_const, probReal_univ, one_smul]
    rw [← htr, hxy, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      g66d_FF, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, g66d_trF]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul, Nat.cast_mul]; ring
open scoped MatrixOrder InnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
section G66G
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem g66g_act_add (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    QAlgorithms.act M (x + y) = QAlgorithms.act M x + QAlgorithms.act M y := by
  ext a; simp [QAlgorithms.act, Matrix.mulVec_add]

theorem g66g_act_sub (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    QAlgorithms.act M (x - y) = QAlgorithms.act M x - QAlgorithms.act M y := by
  ext a; simp [QAlgorithms.act, Matrix.mulVec_sub]

theorem g66g_act_smul (M : Matrix ι ι ℂ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    QAlgorithms.act M (c • x) = c • QAlgorithms.act M x := by
  ext a; simp [QAlgorithms.act, Matrix.mulVec_smul]

theorem g66g_act_madd (M N : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    QAlgorithms.act (M + N) x = QAlgorithms.act M x + QAlgorithms.act N x := by
  ext a; simp [QAlgorithms.act, Matrix.add_mulVec]

theorem g66g_act_msub (M N : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    QAlgorithms.act (M - N) x = QAlgorithms.act M x - QAlgorithms.act N x := by
  ext a; simp [QAlgorithms.act, Matrix.sub_mulVec]

theorem g66g_act_msmul (M : Matrix ι ι ℂ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    QAlgorithms.act (c • M) x = c • QAlgorithms.act M x := by
  ext a; simp [QAlgorithms.act, Matrix.smul_mulVec]

theorem g66g_act_one (x : EuclideanSpace ℂ ι) : QAlgorithms.act (1 : Matrix ι ι ℂ) x = x := by
  ext a; simp [QAlgorithms.act]

theorem g66g_act_mul (M N : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    QAlgorithms.act (M * N) x = QAlgorithms.act M (QAlgorithms.act N x) := by
  ext a; simp [QAlgorithms.act, Matrix.mulVec_mulVec]

theorem g66g_tr_pure (M : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) :
    (M * QAlgorithms.pureDensity w).trace = inner ℂ w (QAlgorithms.act M w) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.pureDensity, Matrix.of_apply,
    QAlgorithms.act, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec,
    WithLp.ofLp_toLp, Pi.star_apply, RCLike.star_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem g66g_tr_pure' (w : EuclideanSpace ℂ ι) :
    (QAlgorithms.pureDensity w).trace = inner ℂ w w := by
  have := g66g_tr_pure (1 : Matrix ι ι ℂ) w
  rwa [Matrix.one_mul, g66g_act_one] at this

theorem g66g_act_pure (η v : EuclideanSpace ℂ ι) :
    QAlgorithms.act (QAlgorithms.pureDensity η) v = inner ℂ η v • η := by
  ext a
  simp only [QAlgorithms.act, QAlgorithms.pureDensity, Matrix.mulVec, dotProduct, Matrix.of_apply,
    EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul,
    Pi.star_apply, RCLike.star_def, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem g66g_conj_pure (M : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) :
    M * QAlgorithms.pureDensity w * Mᴴ = QAlgorithms.pureDensity (QAlgorithms.act M w) := by
  ext a b
  simp only [Matrix.mul_apply, QAlgorithms.pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply,
    QAlgorithms.act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, map_sum, map_mul, RCLike.star_def,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem g66g_pure_smul (c : ℂ) (w : EuclideanSpace ℂ ι) :
    QAlgorithms.pureDensity (c • w) = (c * conj c) • QAlgorithms.pureDensity w := by
  ext a b
  simp only [QAlgorithms.pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply,
    map_mul]
  ring

theorem g66g_comm (K : Matrix ι ι ℂ) (hK : Kᴴ * K = 1) (w : EuclideanSpace ℂ ι) (c : ℂ)
    (hc : c * conj c = 1) (hw : QAlgorithms.act K w = c • w) :
    K * QAlgorithms.pureDensity w = QAlgorithms.pureDensity w * K := by
  have h1 : K * QAlgorithms.pureDensity w * Kᴴ = QAlgorithms.pureDensity w := by
    rw [g66g_conj_pure, hw, g66g_pure_smul, hc, one_smul]
  calc K * QAlgorithms.pureDensity w = K * QAlgorithms.pureDensity w * (Kᴴ * K) := by
        rw [hK, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1]

theorem g66g_pure_psd (w : EuclideanSpace ℂ ι) : (QAlgorithms.pureDensity w).PosSemidef := by
  have : QAlgorithms.pureDensity w = Matrix.vecMulVec (WithLp.ofLp w) (star (WithLp.ofLp w)) := by
    ext a b; simp [QAlgorithms.pureDensity, Matrix.vecMulVec]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

theorem g66g_inner_self (w : EuclideanSpace ℂ ι) : inner ℂ w w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

theorem g66g_trBP (psi : EuclideanSpace ℂ ι) (hn : ‖psi‖ = 1)
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (B * QAlgorithms.pureDensity psi).trace.re ≤ B.trace.re := by
  set P := QAlgorithms.pureDensity psi
  have hs : inner ℂ psi psi = 1 := by rw [g66g_inner_self, hn]; simp
  have hPP : P * P = P := by
    have := g66g_act_pure psi psi
    ext a b
    have h2 := congrArg (fun v : EuclideanSpace ℂ ι => v a) this
    simp only [P, Matrix.mul_apply, QAlgorithms.pureDensity, Matrix.of_apply] at h2 ⊢
    simp only [QAlgorithms.act, Matrix.mulVec, dotProduct, QAlgorithms.pureDensity, Matrix.of_apply,
      WithLp.ofLp_toLp, hs, one_smul] at h2
    calc ∑ k, psi a * conj (psi k) * (psi k * conj (psi b))
        = (∑ k, psi a * conj (psi k) * psi k) * conj (psi b) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [h2]
  have hPh : Pᴴ = P := by
    ext a b
    simp [P, QAlgorithms.pureDensity, Matrix.conjTranspose_apply, mul_comm]
  set Q := 1 - P
  have hQh : Qᴴ = Q := by simp [Q, Matrix.conjTranspose_sub, hPh]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]; abel
  have hpsd := hB.conjTranspose_mul_mul_same Q
  rw [hQh] at hpsd
  have ht := hpsd.trace_nonneg
  have e : (Q * B * Q).trace = B.trace - (B * P).trace := by
    rw [Matrix.trace_mul_cycle, hQQ]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_mul_comm P B]
  rw [e] at ht
  have := (Complex.nonneg_iff.mp ht).1
  simp only [Complex.sub_re, Complex.zero_re] at this
  linarith

/-- L1: ⟨w|C|w⟩ ≤ ‖w‖² tr C. -/
theorem g66g_L1 (C : Matrix ι ι ℂ) (hC : C.PosSemidef) (w : EuclideanSpace ℂ ι) :
    (C * QAlgorithms.pureDensity w).trace.re ≤ ‖w‖ ^ 2 * C.trace.re := by
  by_cases hw : w = 0
  · subst hw
    have : QAlgorithms.pureDensity (0 : EuclideanSpace ℂ ι) = 0 := by
      ext a b; simp [QAlgorithms.pureDensity]
    rw [this]; simp
  · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    set u : EuclideanSpace ℂ ι := ((‖w‖⁻¹ : ℝ) : ℂ) • w
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      field_simp
    have hwu : w = ((‖w‖ : ℝ) : ℂ) • u := by
      simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
    have h := g66g_trBP u hu C hC
    rw [hwu, g66g_pure_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.conj_ofReal, ← Complex.ofReal_mul,
      smul_eq_mul, Complex.re_ofReal_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm, hu,
      mul_one]
    nlinarith [sq_nonneg ‖w‖]

theorem g66g_sqrt (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    ∃ S : Matrix ι ι ℂ, Sᴴ = S ∧ S * S = B := by
  refine ⟨cfc Real.sqrt B, ?_, ?_⟩
  · exact (Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg (fun t _ => Real.sqrt_nonneg t) :
      (0 : Matrix ι ι ℂ) ≤ cfc Real.sqrt B)).1.eq
  · have hnn : (0 : Matrix ι ι ℂ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
    rw [← cfc_mul Real.sqrt Real.sqrt B]
    conv_rhs => rw [← cfc_id ℝ B]
    apply cfc_congr
    intro t ht
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

theorem g66g_form (S : Matrix ι ι ℂ) (hS : Sᴴ = S) (w : EuclideanSpace ℂ ι) :
    (S * S * QAlgorithms.pureDensity w).trace.re = ‖QAlgorithms.act S w‖ ^ 2 := by
  have h := g66g_conj_pure S w
  rw [hS] at h
  rw [show (S * S * QAlgorithms.pureDensity w).trace = (S * QAlgorithms.pureDensity w * S).trace by
    rw [Matrix.trace_mul_comm (S * QAlgorithms.pureDensity w) S, Matrix.mul_assoc]]
  rw [h, g66g_tr_pure', g66g_inner_self]
  exact Complex.ofReal_re _

/-- density matrix bound -/
theorem g66g_L4 (Xi rho : Matrix ι ι ℂ) (hX : Xi.PosSemidef) (hr : QAlgorithms.IsDensityMatrix rho) :
    (Xi * rho).trace.re ≤ Xi.trace.re := by
  obtain ⟨R, hR, hRR⟩ := g66g_sqrt rho hr.1
  set c : ι → EuclideanSpace ℂ ι := fun k => WithLp.toLp 2 (fun a => R a k)
  have hdec : rho = ∑ k, QAlgorithms.pureDensity (c k) := by
    have hR' : ∀ i j, R i j = conj (R j i) := fun i j => by
      have := congrFun (congrFun hR i) j
      rw [Matrix.conjTranspose_apply] at this
      rw [← this]; rfl
    rw [← hRR]
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, c, QAlgorithms.pureDensity, Matrix.of_apply, WithLp.ofLp_toLp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hR' k b]
  have htr : ∑ k, ‖c k‖ ^ 2 = 1 := by
    have h1 := hr.2
    rw [hdec, Matrix.trace_sum] at h1
    simp only [g66g_tr_pure', g66g_inner_self] at h1
    exact_mod_cast h1
  rw [hdec, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  calc ∑ k, (Xi * QAlgorithms.pureDensity (c k)).trace.re
      ≤ ∑ k, ‖c k‖ ^ 2 * Xi.trace.re := Finset.sum_le_sum fun k _ => g66g_L1 Xi hX (c k)
    _ = Xi.trace.re := by rw [← Finset.sum_mul, htr, one_mul]

/-- sector bound -/
theorem g66g_L8 (B Pi : Matrix ι ι ℂ) (hB : B.PosSemidef) (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi)
    (w : EuclideanSpace ℂ ι) (hw : QAlgorithms.act Pi w = w) :
    (B * QAlgorithms.pureDensity w).trace.re ≤ ‖w‖ ^ 2 * (B * Pi).trace.re := by
  have hC : (Pi * B * Pi).PosSemidef := by
    have := hB.conjTranspose_mul_mul_same Pi; rwa [hPi] at this
  have h := g66g_L1 _ hC w
  have e1 : (Pi * B * Pi * QAlgorithms.pureDensity w).trace = (B * QAlgorithms.pureDensity w).trace := by
    have := g66g_conj_pure Pi w
    rw [hPi, hw] at this
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc Pi, this]
  have e2 : (Pi * B * Pi).trace = (B * Pi).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hPP]
  rw [e1, e2] at h; exact h

end G66G

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)
open QAlgorithms.Papers.Independent.Renew46.P30

theorem g66g_inner_tensor {d : ℕ} (a b c e : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (QAlgorithms.tensorVec a b) (QAlgorithms.tensorVec c e) = inner ℂ a c * inner ℂ b e := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, QAlgorithms.tensorVec, dotProduct, WithLp.ofLp_toLp,
    Pi.star_apply, RCLike.star_def, Fintype.sum_prod_type, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem g66g_F_tensor {d : ℕ} (a b : EuclideanSpace ℂ (Fin d)) :
    QAlgorithms.act (g66d_F (Fin d)) (QAlgorithms.tensorVec a b) = QAlgorithms.tensorVec b a := by
  ext u
  simp only [QAlgorithms.act, g66d_F, Matrix.mulVec, dotProduct, Matrix.of_apply, QAlgorithms.tensorVec,
    WithLp.ofLp_toLp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Prod.fst_swap, Prod.snd_swap]
  ring

theorem g66g_F_herm {ι : Type*} [Fintype ι] [DecidableEq ι] : (g66d_F ι)ᴴ = g66d_F ι := by
  ext u v
  simp only [g66d_F, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : u = v.swap
  · rw [if_pos h, if_pos (by rw [h, Prod.swap_swap])]; simp
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', Prod.swap_swap]))]; simp

theorem g66g_swapP {d : ℕ} (b : Bool) :
    swapProjector d b = (1 / 2 : ℂ) • (1 + (if b then 1 else -1 : ℂ) • g66d_F (Fin d)) := by
  ext x y
  simp only [swapProjector, g66d_F, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul]
  have : (y = x.swap) ↔ (x = (y.2, y.1)) := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; rw [h]; rfl
  by_cases h : x = (y.2, y.1)
  · rw [if_pos h, if_pos (this.mpr h)]; ring
  · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]; ring

theorem g66g_P_herm {d : ℕ} (σ : ℂ) (hσ : conj σ = σ) :
    ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d)))ᴴ = (1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d)) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, g66g_F_herm,
    Matrix.conjTranspose_one]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2, show star σ = σ from hσ]

theorem g66g_P_idem {d : ℕ} (σ : ℂ) (hσ : σ * σ = 1) :
    ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d))) * ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d))) =
      (1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d)) := by
  have e : (1 + σ • g66d_F (Fin d)) * (1 + σ • g66d_F (Fin d)) = (2 : ℂ) • (1 + σ • g66d_F (Fin d)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, g66d_FF, smul_smul, hσ, one_smul]
    module
  rw [Matrix.smul_mul, Matrix.mul_smul, e, smul_smul, smul_smul]
  congr 1; norm_num

theorem g66g_P_comm {d : ℕ} (σ : ℂ) (W : Matrix (Fin d) (Fin d) ℂ) :
    (W ⊗ₖ W) * ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d))) = ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d))) * (W ⊗ₖ W) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    g66d_F_comm]

theorem g66g_P_tr {d : ℕ} (σ : ℂ) (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (X * ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d)))).trace = (1 / 2 : ℂ) * (X.trace + σ * (X * g66d_F (Fin d)).trace) := by
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]

theorem g66g_normT {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SU d)) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    MatrixNormalized mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) X ↔
      (X.trace = (d : ℂ) ^ 2 ∧ (X * g66d_F (Fin d)).trace = d) := by
  obtain ⟨hint, x, y, hT, h1, h2⟩ := g66d_ptwirl hd mu X
  have hTe : ∀ u v, (∫ U : SU d, (((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) * X *
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) u v ∂mu) =
      (x • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + y • g66d_F (Fin d)) u v := by
    intro u v; rw [← hT, Matrix.of_apply]
  have i0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  constructor
  · intro hN
    have e1 := (hN (⟨0, by omega⟩, ⟨1, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩)).2
    have e2 := (hN (⟨0, by omega⟩, ⟨1, by omega⟩) (⟨1, by omega⟩, ⟨0, by omega⟩)).2
    simp only [pairAction] at e1 e2
    change (∫ U : SU d, (((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ)) * X *
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) _ _ ∂mu) = _ at e1 e2
    rw [hTe] at e1 e2
    simp [g66d_F, Matrix.one_apply, i0, i0.symm, Prod.ext_iff] at e1 e2
    subst e1; subst e2
    constructor
    · rw [← h1]; ring
    · rw [← h2]; ring
  · rintro ⟨t1, t2⟩
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hd1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
      intro h
      have : ((d ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; linear_combination h
      have := Nat.cast_injective this
      nlinarith
    have k1 : (x - 1) * d + y = 0 := by
      have : ((x - 1) * d + y) * d = 0 := by linear_combination h1 + t1
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hd0
    have k2 : (x - 1) + y * d = 0 := by
      have : ((x - 1) + y * d) * d = 0 := by linear_combination h2 + t2
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hd0
    have hx : x = 1 := by
      have : (x - 1) * ((d : ℂ) ^ 2 - 1) = 0 := by linear_combination d * k1 - k2
      rcases mul_eq_zero.mp this with h | h
      · linear_combination h
      · exact absurd h hd1
    have hy : y = 0 := by rw [hx] at k1; linear_combination k1
    intro u v
    refine ⟨hint u v, ?_⟩
    have := hTe u v
    rw [hx, hy, one_smul, zero_smul, add_zero] at this
    exact this

theorem g66g_basic {d : ℕ} (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    inner ℂ (QAlgorithms.tensorVec psi phi) (QAlgorithms.tensorVec psi phi) = 1 ∧
    inner ℂ (QAlgorithms.tensorVec phi psi) (QAlgorithms.tensorVec phi psi) = 1 ∧
    inner ℂ (QAlgorithms.tensorVec psi phi) (QAlgorithms.tensorVec phi psi) =
      ((Complex.normSq (inner ℂ psi phi) : ℝ) : ℂ) ∧
    inner ℂ (QAlgorithms.tensorVec phi psi) (QAlgorithms.tensorVec psi phi) =
      ((Complex.normSq (inner ℂ psi phi) : ℝ) : ℂ) ∧
    0 ≤ Complex.normSq (inner ℂ psi phi) ∧ Complex.normSq (inner ℂ psi phi) ≤ 1 := by
  have e1 : inner ℂ psi psi = 1 := by rw [g66g_inner_self, hpsi]; simp
  have e2 : inner ℂ phi phi = 1 := by rw [g66g_inner_self, hphi]; simp
  have e3 : inner ℂ phi psi = conj (inner ℂ psi phi) := (inner_conj_symm phi psi).symm
  refine ⟨by rw [g66g_inner_tensor, e1, e2, one_mul], by rw [g66g_inner_tensor, e1, e2, one_mul],
    by rw [g66g_inner_tensor, e3, Complex.mul_conj], by rw [g66g_inner_tensor, e3, mul_comm, Complex.mul_conj],
    Complex.normSq_nonneg _, ?_⟩
  rw [Complex.normSq_eq_norm_sq]
  have := norm_inner_le_norm (𝕜 := ℂ) psi phi
  rw [hpsi, hphi, mul_one] at this
  nlinarith [norm_nonneg (inner ℂ psi phi)]

theorem g66g_bound (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pairFormula d s ≤ (d : ℝ) ^ 2 := by
  unfold pairFormula
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set A := (d : ℝ) * (d + 1) / 2 * (1 + s) / 2
  set B := (d : ℝ) * (d - 1) / 2 * (1 - s) / 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by
    have : 0 ≤ (d : ℝ) - 1 := by linarith
    have : 0 ≤ 1 - s := by linarith
    positivity
  set x := Real.sqrt A
  set y := Real.sqrt B
  have hx2 : x ^ 2 = A := Real.sq_sqrt hA
  have hy2 : y ^ 2 = B := Real.sq_sqrt hB
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hR : 0 ≤ ((d : ℝ) ^ 2 - d * s) / 2 := by nlinarith
  have key : (2 * x * y) ^ 2 ≤ (((d : ℝ) ^ 2 - d * s) / 2) ^ 2 := by
    rw [mul_pow, mul_pow, hx2, hy2]
    simp only [A, B]
    nlinarith [sq_nonneg ((d : ℝ) * s - 1), sq_nonneg (d : ℝ)]
  have k2 : 2 * x * y ≤ ((d : ℝ) ^ 2 - d * s) / 2 := by
    exact (pow_le_pow_iff_left₀ (by positivity) hR two_ne_zero).mp key
  have hAB : A + B = ((d : ℝ) ^ 2 + d * s) / 2 := by simp only [A, B]; ring
  nlinarith [hx2, hy2, hAB, k2]

theorem g66g_sqfac (P u : ℝ) (hP : 0 ≤ P) (hu : 0 < u) :
    Real.sqrt P / Real.sqrt (2 * u) * u = Real.sqrt (P * u / 2) ∧
    (Real.sqrt P / Real.sqrt (2 * u)) ^ 2 * (2 * u) = P := by
  have h2u : 0 < 2 * u := by linarith
  have hs : Real.sqrt (2 * u) ^ 2 = 2 * u := Real.sq_sqrt h2u.le
  have hsp : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  have hpos : 0 < Real.sqrt (2 * u) := Real.sqrt_pos.mpr h2u
  constructor
  · have : P * u / 2 = (Real.sqrt P / Real.sqrt (2 * u) * u) ^ 2 := by
      rw [mul_pow, div_pow, hs, hsp]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  · rw [div_pow, hs, hsp]; field_simp

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

theorem g66g_opt {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SU d)) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1)
    (B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hB : B.PosSemidef)
    (hN : MatrixNormalized mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) B) :
    QAlgorithms.effectProb B (QAlgorithms.pureDensity (QAlgorithms.tensorVec psi phi)) ≤
      pairFormula d (Complex.normSq (inner ℂ psi phi)) := by
  obtain ⟨tB, tBF⟩ := (g66g_normT hd mu B).mp hN
  obtain ⟨htt, ht't', h1, h2, hs0, hs1⟩ := g66g_basic psi phi hpsi hphi
  set s := Complex.normSq (inner ℂ psi phi)
  set t := QAlgorithms.tensorVec psi phi
  set t' := QAlgorithms.tensorVec phi psi
  have hFt : QAlgorithms.act (g66d_F (Fin d)) t = t' := g66g_F_tensor psi phi
  have hFt' : QAlgorithms.act (g66d_F (Fin d)) t' = t := g66g_F_tensor phi psi
  obtain ⟨S, hS, hSS⟩ := g66g_sqrt B hB
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- sector bound
  have sector : ∀ (σ : ℂ) (w : EuclideanSpace ℂ (Fin d × Fin d)) (k : ℝ), σ * σ = 1 → conj σ = σ →
      QAlgorithms.act ((1 / 2 : ℂ) • (1 + σ • g66d_F (Fin d))) w = w →
      (((‖w‖ ^ 2 : ℝ)) : ℂ) = (k : ℂ) →
      ‖QAlgorithms.act S w‖ ^ 2 ≤ k * ((1 / 2 : ℂ) * ((d : ℂ) ^ 2 + σ * d)).re := by
    intro σ w k hσ hσc hw hk
    have := g66g_L8 B _ hB (g66g_P_herm σ hσc) (g66g_P_idem σ hσ) w hw
    rw [g66g_P_tr, tB, tBF] at this
    rw [← g66g_form S hS w, hSS]
    have hk' : ‖w‖ ^ 2 = k := by exact_mod_cast hk
    rwa [hk'] at this
  set vp : EuclideanSpace ℂ (Fin d × Fin d) := (1 / 2 : ℂ) • (t + t')
  set vm : EuclideanSpace ℂ (Fin d × Fin d) := (1 / 2 : ℂ) • (t - t')
  have hv : t = vp + vm := by simp only [vp, vm]; module
  have bp := sector 1 vp ((1 + s) / 2) (by ring) (by simp)
    (by simp only [vp, g66g_act_msmul, g66g_act_madd, g66g_act_one, g66g_act_smul, g66g_act_add, hFt, hFt'];
        module)
    (by rw [← g66g_inner_self]; simp only [vp, inner_smul_left, inner_smul_right, inner_add_left,
          inner_add_right, htt, ht't', h1, h2, map_div₀, map_one, map_ofNat]; push_cast; ring)
  have bm := sector (-1) vm ((1 - s) / 2) (by ring) (by simp)
    (by simp only [vm, g66g_act_msmul, g66g_act_madd, g66g_act_one, g66g_act_smul, g66g_act_sub, hFt, hFt'];
        module)
    (by rw [← g66g_inner_self]; simp only [vm, inner_smul_left, inner_smul_right, inner_sub_left,
          inner_sub_right, htt, ht't', h1, h2, map_div₀, map_one, map_ofNat]; push_cast; ring)
  have ep : ((1 / 2 : ℂ) * ((d : ℂ) ^ 2 + 1 * d)).re = ((d : ℝ) ^ 2 + d) / 2 := by
    rw [show ((1 / 2 : ℂ) * ((d : ℂ) ^ 2 + 1 * d)) = (((((d : ℝ) ^ 2 + d) / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have em : ((1 / 2 : ℂ) * ((d : ℂ) ^ 2 + -1 * d)).re = ((d : ℝ) ^ 2 - d) / 2 := by
    rw [show ((1 / 2 : ℂ) * ((d : ℂ) ^ 2 + -1 * d)) = (((((d : ℝ) ^ 2 - d) / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [ep] at bp
  rw [em] at bm
  have np : ‖QAlgorithms.act S vp‖ ≤ Real.sqrt ((d : ℝ) * (d + 1) / 2 * (1 + s) / 2) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  have nm : ‖QAlgorithms.act S vm‖ ≤ Real.sqrt ((d : ℝ) * (d - 1) / 2 * (1 - s) / 2) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hE : QAlgorithms.effectProb B (QAlgorithms.pureDensity t) = ‖QAlgorithms.act S t‖ ^ 2 := by
    unfold QAlgorithms.effectProb; rw [← hSS, g66g_form S hS]
  rw [hE]
  unfold pairFormula
  have := norm_add_le (QAlgorithms.act S vp) (QAlgorithms.act S vm)
  rw [← g66g_act_add, ← hv] at this
  exact pow_le_pow_left₀ (norm_nonneg _) (this.trans (add_le_add np nm)) 2

theorem g66g_alg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t t' : E) (s a b : ℝ)
    (htt : inner ℂ t t = 1) (ht't' : inner ℂ t' t' = 1) (h1 : inner ℂ t t' = (s : ℂ))
    (h2 : inner ℂ t' t = (s : ℂ)) :
    inner ℂ ((a : ℂ) • (t + t') + (b : ℂ) • (t - t')) ((a : ℂ) • (t + t') + (b : ℂ) • (t - t')) =
      ((a ^ 2 * (2 + 2 * s) + b ^ 2 * (2 - 2 * s) : ℝ) : ℂ) ∧
    inner ℂ ((a : ℂ) • (t + t') + (b : ℂ) • (t - t')) ((a : ℂ) • (t' + t) + (b : ℂ) • (t' - t)) =
      ((a ^ 2 * (2 + 2 * s) - b ^ 2 * (2 - 2 * s) : ℝ) : ℂ) ∧
    inner ℂ t ((a : ℂ) • (t + t') + (b : ℂ) • (t - t')) = ((a * (1 + s) + b * (1 - s) : ℝ) : ℂ) ∧
    inner ℂ ((a : ℂ) • (t + t') + (b : ℂ) • (t - t')) t = ((a * (1 + s) + b * (1 - s) : ℝ) : ℂ) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, htt, ht't', h1, h2, Complex.conj_ofReal]
  push_cast
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem g66g_eta {d : ℕ} (psi phi : EuclideanSpace ℂ (Fin d)) :
    pairEta d psi phi =
      ((Real.sqrt ((d : ℝ) * (d + 1) / 2) / Real.sqrt (2 * (1 + Complex.normSq (inner ℂ psi phi))) : ℝ) : ℂ) •
        (QAlgorithms.tensorVec psi phi + QAlgorithms.tensorVec phi psi) +
      ((if Complex.normSq (inner ℂ psi phi) = 1 then 0 else
        Real.sqrt ((d : ℝ) * (d - 1) / 2) / Real.sqrt (2 * (1 - Complex.normSq (inner ℂ psi phi))) : ℝ) : ℂ) •
        (QAlgorithms.tensorVec psi phi - QAlgorithms.tensorVec phi psi) := by
  simp only [pairEta]
  split_ifs <;> push_cast <;> simp

theorem g66g_re_d (d : ℕ) : ((d : ℂ) ^ 2).re = (d : ℝ) ^ 2 := by
  rw [show ((d : ℂ) ^ 2) = (((d : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]

theorem g66g_seed {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SU d)) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    MatrixMaximum mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) (QAlgorithms.tensorVec psi phi)
      (pairSeed d psi phi) (pairFormula d (Complex.normSq (inner ℂ psi phi))) := by
  obtain ⟨htt, ht't', h1, h2, hs0, hs1⟩ := g66g_basic psi phi hpsi hphi
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have heta := g66g_eta psi phi
  have hseed0 : pairSeed d psi phi = QAlgorithms.pureDensity (pairEta d psi phi) +
      if Complex.normSq (inner ℂ psi phi) = 1 then
        (1 / 2 : ℂ) • (1 + (-1 : ℂ) • g66d_F (Fin d)) else 0 := by
    unfold pairSeed; rw [g66g_swapP]; simp
  set s := Complex.normSq (inner ℂ psi phi) with hsdef
  set t := QAlgorithms.tensorVec psi phi
  set t' := QAlgorithms.tensorVec phi psi
  have hFt : QAlgorithms.act (g66d_F (Fin d)) t = t' := g66g_F_tensor psi phi
  have hFt' : QAlgorithms.act (g66d_F (Fin d)) t' = t := g66g_F_tensor phi psi
  have hu1 : 0 < 1 + s := by linarith
  obtain ⟨rva, ra⟩ := g66g_sqfac ((d : ℝ) * (d + 1) / 2) (1 + s) (by positivity) hu1
  set a : ℝ := Real.sqrt ((d : ℝ) * (d + 1) / 2) / Real.sqrt (2 * (1 + s)) with ha
  set b : ℝ := if s = 1 then 0 else
    Real.sqrt ((d : ℝ) * (d - 1) / 2) / Real.sqrt (2 * (1 - s)) with hb
  have hQ : 0 ≤ (d : ℝ) * (d - 1) / 2 := by
    have : (0 : ℝ) ≤ d - 1 := by linarith
    positivity
  have rb : b ^ 2 * (2 - 2 * s) = if s = 1 then 0 else (d : ℝ) * (d - 1) / 2 := by
    by_cases h : s = 1
    · rw [hb, if_pos h, if_pos h]; ring
    · rw [hb, if_neg h, if_neg h]
      have := (g66g_sqfac _ (1 - s) hQ (by
        rcases lt_or_eq_of_le hs1 with h' | h'
        · linarith
        · exact absurd h' h)).2
      rw [show (2 - 2 * s) = 2 * (1 - s) by ring]; exact this
  have rvb : b * (1 - s) = Real.sqrt ((d : ℝ) * (d - 1) / 2 * (1 - s) / 2) := by
    by_cases h : s = 1
    · rw [hb, if_pos h, h]; simp
    · rw [hb, if_neg h]
      exact (g66g_sqfac _ (1 - s) hQ (by
        rcases lt_or_eq_of_le hs1 with h' | h'
        · linarith
        · exact absurd h' h)).1
  have ra' : a ^ 2 * (2 + 2 * s) = (d : ℝ) * (d + 1) / 2 := by rw [← ra]; ring
  set η := (a : ℂ) • (t + t') + (b : ℂ) • (t - t') with hη
  obtain ⟨hηη, hηFη, htη, hηt⟩ := g66g_alg t t' s a b htt ht't' h1 h2
  have hFη : QAlgorithms.act (g66d_F (Fin d)) η = (a : ℂ) • (t' + t) + (b : ℂ) • (t' - t) := by
    simp only [hη, g66g_act_add, g66g_act_smul, g66g_act_sub, hFt, hFt']
  set Pm : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := (1 / 2 : ℂ) • (1 + (-1 : ℂ) • g66d_F (Fin d)) with hPm
  have hseed : pairSeed d psi phi = QAlgorithms.pureDensity η + if s = 1 then Pm else 0 := by
    rw [hseed0, heta]
  have hPmh : Pmᴴ = Pm := g66g_P_herm (-1) (by simp)
  have hPmi : Pm * Pm = Pm := g66g_P_idem (-1) (by ring)
  have hPmpsd : Pm.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Pm; rwa [hPmh, hPmi] at this
  have trPm : Pm.trace = (1 / 2 : ℂ) * ((d : ℂ) ^ 2 + (-1) * d) := by
    rw [show Pm.trace = (1 * Pm).trace by rw [Matrix.one_mul], hPm, g66g_P_tr, Matrix.one_mul,
      Matrix.trace_one, g66d_trF]
    simp [Fintype.card_prod]; ring
  have trPmF : (Pm * g66d_F (Fin d)).trace = (1 / 2 : ℂ) * ((d : ℂ) + (-1) * d ^ 2) := by
    rw [hPm, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, g66d_FF, Matrix.trace_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, g66d_trF]
    simp [Fintype.card_prod]; ring
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun B hB => g66g_opt hd mu psi phi hpsi hphi B hB.1 hB.2.1⟩
  · rw [hseed]
    split_ifs
    · exact (g66g_pure_psd η).add hPmpsd
    · simpa using g66g_pure_psd η
  · rw [g66g_normT hd mu, hseed]
    constructor
    · rw [Matrix.trace_add, g66g_tr_pure', hηη]
      split_ifs with h
      · rw [trPm]; rw [if_pos h] at rb
        rw [show a ^ 2 * (2 + 2 * s) + b ^ 2 * (2 - 2 * s) = (d : ℝ) * (d + 1) / 2 by rw [ra', rb]; ring]
        push_cast; ring
      · rw [if_neg h] at rb
        rw [show a ^ 2 * (2 + 2 * s) + b ^ 2 * (2 - 2 * s) = (d : ℝ) ^ 2 by rw [ra', rb]; ring]
        simp
    · rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_mul_comm, g66g_tr_pure, hFη, hηFη]
      split_ifs with h
      · rw [trPmF]; rw [if_pos h] at rb
        rw [show a ^ 2 * (2 + 2 * s) - b ^ 2 * (2 - 2 * s) = (d : ℝ) * (d + 1) / 2 by rw [ra', rb]; ring]
        push_cast; ring
      · rw [if_neg h] at rb
        rw [show a ^ 2 * (2 + 2 * s) - b ^ 2 * (2 - 2 * s) = (d : ℝ) by rw [ra', rb]; ring]
        simp
  · rintro g ⟨c, hc, hgc⟩
    set K : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := pairAction (g : Matrix (Fin d) (Fin d) ℂ) with hKdef
    have hK : Kᴴ * K = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary g.2.1 g.2.1)
      rw [Matrix.star_eq_conjTranspose] at this; exact this
    have hcc : c * conj c = 1 := by rw [Complex.mul_conj', hc]; simp
    have hKF : K * g66d_F (Fin d) = g66d_F (Fin d) * K := g66d_F_comm (g : Matrix (Fin d) (Fin d) ℂ)
    have hKt' : QAlgorithms.act K t' = c • t' := by
      rw [← hFt, ← g66g_act_mul, hKF, g66g_act_mul, hgc, g66g_act_smul]
    have hKη : QAlgorithms.act K η = c • η := by
      rw [hη, g66g_act_add, g66g_act_smul, g66g_act_smul, g66g_act_add, g66g_act_sub, hgc, hKt']
      module
    rw [hseed, Matrix.mul_add, Matrix.add_mul, g66g_comm K hK η c hcc hKη]
    congr 1
    split_ifs
    · exact g66g_P_comm (-1) (g : Matrix (Fin d) (Fin d) ℂ)
    · simp
  · unfold QAlgorithms.effectProb
    rw [hseed, Matrix.add_mul, Matrix.trace_add, Complex.add_re, g66g_tr_pure, g66g_act_pure,
      inner_smul_right, hηt, htη, ← Complex.ofReal_mul, Complex.ofReal_re, rva, rvb]
    unfold pairFormula
    split_ifs with h
    · rw [g66g_tr_pure, hPm, g66g_act_msmul, g66g_act_madd, g66g_act_one, g66g_act_msmul, hFt,
        inner_smul_right, inner_add_right, inner_smul_right, htt, h1, h]
      norm_num; ring
    · rw [Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, add_zero]; ring

theorem g66g_fact {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SU d)) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1)
    (hs : Complex.normSq (inner ℂ psi phi) = (d : ℝ)⁻¹) :
    MatrixMaximum mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) (QAlgorithms.tensorVec psi phi)
      ((d ^ 2 : ℂ) • Matrix.kronecker (QAlgorithms.pureDensity psi) (QAlgorithms.pureDensity phi))
      ((d : ℝ) ^ 2) := by
  obtain ⟨htt, -, h1, -, -, -⟩ := g66g_basic psi phi hpsi hphi
  set t := QAlgorithms.tensorVec psi phi
  have hkr : Matrix.kronecker (QAlgorithms.pureDensity psi) (QAlgorithms.pureDensity phi) =
      QAlgorithms.pureDensity t := by
    ext u v
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.pureDensity, Matrix.of_apply, t,
      QAlgorithms.tensorVec, map_mul]
    ring
  rw [hkr]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hFt : QAlgorithms.act (g66d_F (Fin d)) t = QAlgorithms.tensorVec phi psi := g66g_F_tensor psi phi
  have hn : ‖t‖ ^ 2 = 1 := by
    have := g66g_inner_self t; rw [htt] at this; exact_mod_cast this.symm
  refine ⟨⟨(g66g_pure_psd t).smul (by positivity), ?_, ?_⟩, ?_, ?_⟩
  · rw [g66g_normT hd mu]
    constructor
    · rw [Matrix.trace_smul, g66g_tr_pure', htt]; simp
    · rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm, g66g_tr_pure, hFt, h1, hs]
      push_cast; rw [smul_eq_mul]; field_simp
  · rintro g ⟨c, hc, hgc⟩
    have hK : (pairAction (g : Matrix (Fin d) (Fin d) ℂ))ᴴ * pairAction (g : Matrix (Fin d) (Fin d) ℂ) = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary g.2.1 g.2.1)
      rw [Matrix.star_eq_conjTranspose] at this; exact this
    have hcc : c * conj c = 1 := by rw [Complex.mul_conj', hc]; simp
    rw [Matrix.mul_smul, Matrix.smul_mul, g66g_comm _ hK t c hcc hgc]
  · unfold QAlgorithms.effectProb
    rw [Matrix.smul_mul, Matrix.trace_smul, g66g_tr_pure, g66g_act_pure, htt, one_smul, htt, smul_eq_mul,
      mul_one, g66g_re_d]
  · rintro B ⟨hB, hN, -⟩
    obtain ⟨tB, -⟩ := (g66g_normT hd mu B).mp hN
    have := g66g_L1 B hB t
    unfold QAlgorithms.effectProb
    rw [hn, one_mul, tB, g66g_re_d] at this
    exact this

theorem g66g_last {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SU d)) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (Xi : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hX : Xi.PosSemidef)
    (hN : MatrixNormalized mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) Xi) :
    (Matrix.trace Xi).re = (d : ℝ) ^ 2 ∧
      ∀ rho, QAlgorithms.IsDensityMatrix rho → QAlgorithms.effectProb Xi rho ≤ (d : ℝ) ^ 2 := by
  obtain ⟨tX, -⟩ := (g66g_normT hd mu Xi).mp hN
  have h : (Matrix.trace Xi).re = (d : ℝ) ^ 2 := by rw [tX, g66g_re_d]
  exact ⟨h, fun rho hr => h ▸ g66g_L4 Xi rho hX hr⟩

end

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P30

theorem solution (d : ℕ) (hd : 2 ≤ d) (mu : Measure (SU d))
    [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    let s2 := Complex.normSq (inner ℂ psi phi)
    MatrixMaximum mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) (QAlgorithms.tensorVec psi phi) (pairSeed d psi phi)
      (pairFormula d s2) ∧ pairFormula d s2 ≤ (d : ℝ) ^ 2 ∧
    (s2 = (d : ℝ)⁻¹ →
      MatrixMaximum mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) (QAlgorithms.tensorVec psi phi)
        ((d ^ 2 : ℂ) • Matrix.kronecker (QAlgorithms.pureDensity psi) (QAlgorithms.pureDensity phi))
        ((d : ℝ) ^ 2)) ∧
    (∀ Xi : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      Xi.PosSemidef → MatrixNormalized mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) Xi →
      (Matrix.trace Xi).re = (d : ℝ) ^ 2 ∧
      ∀ rho, QAlgorithms.IsDensityMatrix rho →
        QAlgorithms.effectProb Xi rho ≤ (d : ℝ) ^ 2) := by
  intro s2
  obtain ⟨-, -, -, -, hs0, hs1⟩ := g66g_basic psi phi hpsi hphi
  exact ⟨g66g_seed hd mu psi phi hpsi hphi, g66g_bound d (by omega) s2 hs0 hs1,
    fun hs => g66g_fact hd mu psi phi hpsi hphi hs, fun Xi hX hN => g66g_last hd mu Xi hX hN⟩
