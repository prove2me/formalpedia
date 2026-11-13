-- Prove2me | solution 1 for QAlgorithms.GottesmanThesis.erasure_achievable_one_sub_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:42:29.176547+00:00
-- url     : https://prove2.me/submissions/83bdaef6-a5d3-4bcf-81bb-e9fb9824f3c1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace EC74504552F

open QAlgorithms
open scoped ComplexConjugate Matrix

/-- Coordinate monogamy: for `u : R → R → R → ℂ` (registers reference, decoder-1 output,
decoder-2 output), `Σ_t |Σ_r u r r t|² + Σ_s |Σ_r u r s r|² ≤ (d + 1) ‖u‖²`, `d = |R|`.
This is `‖P₁ u‖² + ‖P₂ u‖² ≤ (1 + 1/d) ‖u‖²` for the two maximally entangled projectors, scaled by `d`. -/
theorem monogamy_coord {R : Type*} [Fintype R] [DecidableEq R] (u : R → R → R → ℂ) :
    (∑ t, ‖∑ r, u r r t‖ ^ 2 + ∑ s, ‖∑ r, u r s r‖ ^ 2) ≤
      ((Fintype.card R : ℝ) + 1) * ∑ r, ∑ s, ∑ t, ‖u r s t‖ ^ 2 := by
  classical
  set α : R → ℂ := fun t => ∑ r, u r r t with hα
  set β : R → ℂ := fun s => ∑ r, u r s r with hβ
  set S : ℝ := ∑ t, ‖α t‖ ^ 2 + ∑ s, ‖β s‖ ^ 2 with hS
  set U : ℝ := ∑ r, ∑ s, ∑ t, ‖u r s t‖ ^ 2 with hU
  let w : R → R → R → ℂ := fun r s t =>
    (if r = s then conj (α t) else 0) + (if r = t then conj (β s) else 0)
  have e1 : ∑ r, ∑ s, ∑ t, (if r = s then conj (α t) else 0) * u r s t
      = ∑ t, ((‖α t‖ ^ 2 : ℝ) : ℂ) := by
    have h : ∀ r, ∑ s, ∑ t, (if r = s then conj (α t) else 0) * u r s t
        = ∑ t, conj (α t) * u r r t := by
      intro r
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp [ite_mul]
    simp_rw [h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    show conj (α t) * α t = _
    rw [Complex.conj_mul']
    push_cast; rfl
  have e2 : ∑ r, ∑ s, ∑ t, (if r = t then conj (β s) else 0) * u r s t
      = ∑ s, ((‖β s‖ ^ 2 : ℝ) : ℂ) := by
    have h : ∀ r, ∑ s, ∑ t, (if r = t then conj (β s) else 0) * u r s t
        = ∑ s, conj (β s) * u r s r := by
      intro r
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [ite_mul]
    simp_rw [h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum]
    show conj (β s) * β s = _
    rw [Complex.conj_mul']
    push_cast; rfl
  have k1 : S = (∑ r, ∑ s, ∑ t, w r s t * u r s t).re := by
    simp only [w, add_mul, Finset.sum_add_distrib]
    rw [e1, e2, Complex.add_re, Complex.re_sum, Complex.re_sum]
    simp only [Complex.ofReal_re]
    exact hS
  -- pointwise bound on `‖w‖²`
  have pw : ∀ r s t, ‖w r s t‖ ^ 2 ≤ (if r = s then ‖α t‖ ^ 2 else 0) +
      (if r = t then ‖β s‖ ^ 2 else 0) +
      (if r = s ∧ r = t then ‖α t‖ ^ 2 + ‖β s‖ ^ 2 else 0) := by
    intro r s t
    by_cases h1 : r = s <;> by_cases h2 : r = t
    · subst h1; subst h2
      simp only [w, eq_self_iff_true, if_true, and_self]
      have := norm_add_le (conj (α r)) (conj (β r))
      simp only [Complex.norm_conj] at this ⊢
      nlinarith [norm_nonneg (conj (α r) + conj (β r)), norm_nonneg (α r), norm_nonneg (β r),
        sq_nonneg (‖α r‖ - ‖β r‖)]
    · subst h1; simp [w, h2]
    · subst h2; simp [w, h1]
    · simp [w, h1, h2]
  have sumw : ∑ r, ∑ s, ∑ t, ‖w r s t‖ ^ 2 ≤ ((Fintype.card R : ℝ) + 1) * S := by
    have hA : (∑ r : R, ∑ s : R, ∑ t : R, (if r = s then ‖α t‖ ^ 2 else 0) : ℝ)
        = (Fintype.card R : ℝ) * ∑ t, ‖α t‖ ^ 2 := by
      have : ∀ r : R, ∑ s : R, ∑ t : R, (if r = s then ‖α t‖ ^ 2 else (0 : ℝ)) = ∑ t, ‖α t‖ ^ 2 := by
        intro r
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp
      simp_rw [this]
      simp
    have hB : (∑ r : R, ∑ s : R, ∑ t : R, (if r = t then ‖β s‖ ^ 2 else 0) : ℝ)
        = (Fintype.card R : ℝ) * ∑ s, ‖β s‖ ^ 2 := by
      have : ∀ r : R, ∑ s : R, ∑ t : R, (if r = t then ‖β s‖ ^ 2 else (0 : ℝ)) = ∑ s, ‖β s‖ ^ 2 := by
        intro r
        refine Finset.sum_congr rfl fun s _ => ?_
        simp
      simp_rw [this]
      simp
    have hC : (∑ r : R, ∑ s : R, ∑ t : R, (if r = s ∧ r = t then ‖α t‖ ^ 2 + ‖β s‖ ^ 2 else 0) : ℝ) = S := by
      have : ∀ r : R, ∑ s : R, ∑ t : R, (if r = s ∧ r = t then ‖α t‖ ^ 2 + ‖β s‖ ^ 2 else (0 : ℝ))
          = ‖α r‖ ^ 2 + ‖β r‖ ^ 2 := by
        intro r
        rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single r]
          · simp
          · intro t _ ht; simp [Ne.symm ht]
          · simp
        · intro s _ hs
          refine Finset.sum_eq_zero fun t _ => ?_
          simp [Ne.symm hs]
        · simp
      simp_rw [this]
      rw [Finset.sum_add_distrib]
    calc ∑ r, ∑ s, ∑ t, ‖w r s t‖ ^ 2
        ≤ ∑ r, ∑ s, ∑ t, ((if r = s then ‖α t‖ ^ 2 else 0) +
            (if r = t then ‖β s‖ ^ 2 else 0) +
            (if r = s ∧ r = t then ‖α t‖ ^ 2 + ‖β s‖ ^ 2 else 0)) :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
            pw r s t
      _ = (Fintype.card R : ℝ) * S + S := by
          simp only [Finset.sum_add_distrib]
          rw [hA, hB, hC, hS]; ring
      _ = ((Fintype.card R : ℝ) + 1) * S := by ring
  -- Cauchy–Schwarz
  have cs : ∀ f g : R → R → R → ℝ,
      (∑ r, ∑ s, ∑ t, f r s t * g r s t) ^ 2 ≤
        (∑ r, ∑ s, ∑ t, f r s t ^ 2) * (∑ r, ∑ s, ∑ t, g r s t ^ 2) := by
    intro f g
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (R × R × R))
      (fun x => f x.1 x.2.1 x.2.2) (fun x => g x.1 x.2.1 x.2.2)
    simpa only [Fintype.sum_prod_type] using this
  have hSle : S ≤ ∑ r, ∑ s, ∑ t, ‖w r s t‖ * ‖u r s t‖ := by
    rw [k1, Complex.re_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [← norm_mul]
    exact Complex.re_le_norm _
  have hS0 : 0 ≤ S := by positivity
  have hU0 : 0 ≤ U := by positivity
  have hsq : S ^ 2 ≤ ((Fintype.card R : ℝ) + 1) * S * U := by
    have h1 : S ^ 2 ≤ (∑ r, ∑ s, ∑ t, ‖w r s t‖ * ‖u r s t‖) ^ 2 :=
      pow_le_pow_left₀ hS0 hSle 2
    have h2 := cs (fun r s t => ‖w r s t‖) (fun r s t => ‖u r s t‖)
    have h3 := mul_le_mul_of_nonneg_right sumw hU0
    calc S ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ ((Fintype.card R : ℝ) + 1) * S * U := h3
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have : S * S ≤ (((Fintype.card R : ℝ) + 1) * U) * S := by nlinarith
    exact le_of_mul_le_mul_right this h0

/-- General sandwich identity: for any vector `ψ` on `R × ι` and Kraus family `M`,
`⟨ψ|(id ⊗ Σ M·M†)(|ψ⟩⟨ψ|)|ψ⟩ = Σ_i |⟨ψ|(I ⊗ M_i)|ψ⟩|²`. -/
theorem sandwich_kraus {R ι : Type*} [Fintype R] [Fintype ι] {K : Type*} [Fintype K]
    (M : K → Matrix ι ι ℂ) (ψ : R × ι → ℂ) :
    (∑ a, ∑ b, conj (ψ a) *
      (idTensorSuperop (R := R) (krausApply M) (Matrix.of fun a b => ψ a * conj (ψ b))) a b *
        ψ b) = ∑ i, ((‖∑ a, ∑ x, conj (ψ a) * M i a.2 x * ψ (a.1, x)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  set f : K → R × ι → ℂ := fun i a => ∑ x, conj (ψ a) * M i a.2 x * ψ (a.1, x) with hf
  set g : K → R × ι → ℂ := fun i b => ∑ x', ψ b * conj (M i b.2 x') * conj (ψ (b.1, x')) with hg
  have hz : ∀ i, ((‖∑ a, ∑ x, conj (ψ a) * M i a.2 x * ψ (a.1, x)‖ ^ 2 : ℝ) : ℂ) =
      ∑ a, ∑ b, f i a * g i b := by
    intro i
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    simp only [hg, map_sum, map_mul, Complex.conj_conj]
  simp_rw [hz]
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [show (∑ i, ∑ a, ∑ b, f i a * g i b) = ∑ a, ∑ b, ∑ i, f i a * g i b from by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hf, hg, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [RCLike.star_def]
  ring


theorem maxEntangled_apply (k : ℕ) (a : Qubits k × Qubits k) :
    maxEntangled k a = if a.1 = a.2 then (((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℝ) : ℂ) else 0 := by
  simp [maxEntangled]

theorem sandwich_maxEntangled {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) :
    (∑ a : Qubits k × Qubits k, ∑ x, conj (maxEntangled k a) * M a.2 x * maxEntangled k (a.1, x))
      = (((2 : ℝ) ^ k)⁻¹ : ℝ) * M.trace := by
  simp_rw [maxEntangled_apply]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite (starRingEnd ℂ), map_zero, Complex.conj_ofReal, ite_mul, mul_ite, zero_mul,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hc : ((((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℝ) : ℂ)) * (((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℝ) : ℂ)
      = (((2 : ℝ) ^ k)⁻¹ : ℝ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.diag_apply]
  rw [← hc]; ring

/-- Entanglement fidelity of a Kraus map: `F = 4^{-k} Σ_i |tr M_i|²`. -/
theorem fid_kraus {k : ℕ} {K : Type*} [Fintype K] (M : K → Matrix (Qubits k) (Qubits k) ℂ) :
    entanglementFidelity (krausApply M) = (((2 : ℝ) ^ k)⁻¹) ^ 2 * ∑ i, ‖(M i).trace‖ ^ 2 := by
  unfold entanglementFidelity pureDensity
  rw [sandwich_kraus M (fun a => maxEntangled k a)]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  simp_rw [sandwich_maxEntangled, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  rw [Finset.mul_sum]


/-- Composition of Kraus maps is the Kraus map of the products. -/
theorem krausApply_comp {K1 K2 ι κ μ : Type*} [Fintype K1] [Fintype K2] [Fintype ι] [Fintype κ]
    (E : K1 → Matrix κ ι ℂ) (F : K2 → Matrix μ κ ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply F (krausApply E ρ) = krausApply (fun p : K2 × K1 => F p.1 * E p.2) ρ := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul,
    Fintype.sum_prod_type, Matrix.mul_assoc]

/-- Branch form of a coded channel: `F(Dec ∘ N ∘ Enc) = 4^{-k} Σ_{b,j,a} |tr(B_b N_j A_a)|²`. -/
theorem fid_comp {k n : ℕ} {Out J : Type*} [Fintype Out] [DecidableEq Out] [Fintype J]
    (Enc : Superop (Qubits k) (Qubits n)) (hE : IsChannel Enc)
    (Dec : Superop Out (Qubits k)) (hD : IsChannel Dec)
    (Nch : Superop (Qubits n) Out) (N : J → Matrix Out (Qubits n) ℂ)
    (hN : ∀ ρ, Nch ρ = krausApply N ρ) :
    ∃ (m m' : ℕ) (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ) (B : Fin m' → Matrix (Qubits k) Out ℂ),
      IsKrausFamily A ∧ IsKrausFamily B ∧
      entanglementFidelity (Dec ∘ Nch ∘ Enc) =
        (((2 : ℝ) ^ k)⁻¹) ^ 2 * ∑ b, ∑ j, ∑ a, ‖(B b * N j * A a).trace‖ ^ 2 := by
  obtain ⟨m, A, hA, hEnc⟩ := hE
  obtain ⟨m', B, hB, hDec⟩ := hD
  refine ⟨m, m', A, B, hA, hB, ?_⟩
  have h : Dec ∘ Nch ∘ Enc =
      krausApply (fun p : Fin m' × (J × Fin m) => B p.1 * (N p.2.1 * A p.2.2)) := by
    funext ρ
    simp only [Function.comp, hEnc, hN, hDec, krausApply_comp]
  rw [h, fid_kraus]
  simp only [Fintype.sum_prod_type, Matrix.mul_assoc]

/-- Branch form with GIVEN Kraus families for encoder and decoder. -/
theorem fid_comp_given {k n : ℕ} {Out J KA KB : Type*} [Fintype Out] [DecidableEq Out] [Fintype J]
    [Fintype KA] [Fintype KB]
    (A : KA → Matrix (Qubits n) (Qubits k) ℂ) (B : KB → Matrix (Qubits k) Out ℂ)
    (Nch : Superop (Qubits n) Out) (N : J → Matrix Out (Qubits n) ℂ)
    (hN : ∀ ρ, Nch ρ = krausApply N ρ) :
    entanglementFidelity (krausApply B ∘ Nch ∘ krausApply A) =
      (((2 : ℝ) ^ k)⁻¹) ^ 2 * ∑ b, ∑ j, ∑ a, ‖(B b * N j * A a).trace‖ ^ 2 := by
  have h : krausApply B ∘ Nch ∘ krausApply A =
      krausApply (fun p : KB × (J × KA) => B p.1 * (N p.2.1 * A p.2.2)) := by
    funext ρ
    simp only [Function.comp, hN, krausApply_comp]
  rw [h, fid_kraus]
  simp only [Fintype.sum_prod_type, Matrix.mul_assoc]

end EC74504552F

namespace EC74504552K

open QAlgorithms
open scoped ComplexConjugate Matrix

/-- Entry formula for a tensor-power Kraus map. -/
theorem prodKraus_apply {n : ℕ} {K α β : Type*} [Fintype K] [Fintype α] [Fintype β]
    (E : K → Matrix α β ℂ) (ρ : Matrix (Fin n → β) (Fin n → β) ℂ) (y y' : Fin n → α) :
    krausApply (fun j : Fin n → K =>
      (Matrix.of fun (y : Fin n → α) (z : Fin n → β) => ∏ q, E (j q) (y q) (z q))) ρ y y'
      = ∑ z, ∑ z', ρ z z' * ∏ q, ∑ k, E k (y q) (z q) * star (E k (y' q) (z' q)) := by
  classical
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply]
  simp_rw [Finset.sum_mul, star_prod]
  have h1 : ∀ (j : Fin n → K) (z z' : Fin n → β),
      (∏ q, E (j q) (y q) (z q)) * ρ z z' * ∏ q, star (E (j q) (y' q) (z' q))
        = ρ z z' * ∏ q, (E (j q) (y q) (z q) * star (E (j q) (y' q) (z' q))) := by
    intro j z z'
    rw [Finset.prod_mul_distrib]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.prod_sum]

/-- The single-qubit erasure kernel `Σ_k K_k(o,b) conj K_k(o',b')`. -/
noncomputable def erasureKernel (p : ℝ) (o o' : Bool × Bool) (b b' : Bool) : ℂ :=
  if o.2 = false ∧ o'.2 = false then (if o.1 = b ∧ o'.1 = b' then ((1 - p : ℝ) : ℂ) else 0)
  else if o.2 = true ∧ o'.2 = true then (if o.1 = o'.1 ∧ b = b' then ((p / 2 : ℝ) : ℂ) else 0)
  else 0

theorem erasureKraus_kernel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o o' : Bool × Bool) (b b' : Bool) :
    ∑ k, erasureKraus p k o b * star (erasureKraus p k o' b') = erasureKernel p o o' b b' := by
  have hA' : ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) = 1 - (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hB' : ((Real.sqrt p : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
      (((Real.sqrt p : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = (p : ℂ) / 2 := by
    rw [div_mul_div_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt hp0,
      Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  obtain ⟨a, f⟩ := o
  obtain ⟨a', f'⟩ := o'
  rw [Fin.sum_univ_five]
  cases a <;> cases f <;> cases a' <;> cases f' <;> cases b <;> cases b' <;>
    simp [erasureKraus, erasureKernel, hA', hB']

/-- Entry formula for the `n`-qubit erasure channel. -/
theorem erasureChannel_apply (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) (y y' : Fin n → Bool × Bool) :
    erasureChannel n p ρ y y' = ∑ z, ∑ z', ρ z z' * ∏ q, erasureKernel p (y q) (y' q) (z q) (z' q) := by
  unfold erasureChannel
  rw [prodKraus_apply]
  simp_rw [erasureKraus_kernel p hp0 hp1]

end EC74504552K

namespace EC74504552G

open QAlgorithms EC74504552F EC74504552K
open scoped ComplexConjugate Matrix

theorem cyc3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem perm4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ d, ∑ a, ∑ c, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  calc ∑ a, ∑ c, ∑ d, f a b c d = ∑ a, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, f a b c d := Finset.sum_comm

/-- Squared-norm sums as a Hermitian kernel. -/
theorem sq_sum_expand {X I : Type*} [Fintype X] [Fintype I] (M : X → ℂ) (P : I → X → ℂ) :
    ((∑ i, ‖∑ x, M x * P i x‖ ^ 2 : ℝ) : ℂ) =
      ∑ x1, ∑ x2, M x1 * conj (M x2) * ∑ i, P i x1 * conj (P i x2) := by
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x2 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Two families with the same kernel give the same squared-norm sums. -/
theorem sq_sum_transfer {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] (M : X → ℂ)
    (P : I → X → ℂ) (Q : J → X → ℂ)
    (h : ∀ x1 x2, ∑ i, P i x1 * conj (P i x2) = ∑ j, Q j x1 * conj (Q j x2)) :
    ∑ i, ‖∑ x, M x * P i x‖ ^ 2 = ∑ j, ‖∑ x, M x * Q j x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sq_sum_expand, sq_sum_expand]
  simp_rw [h]

/-- A normalized Kraus family preserves squared norms of vectors. -/
theorem kraus_collapse {I κ ι : Type*} [Fintype I] [Fintype κ] [Fintype ι] [DecidableEq ι]
    (K : I → Matrix κ ι ℂ) (hK : IsKrausFamily K) (v : ι → ℂ) :
    ∑ i, ∑ x, ‖∑ y, K i x y * v y‖ ^ 2 = ∑ y, ‖v y‖ ^ 2 := by
  have h1 : ∑ i, ∑ x, ‖∑ y, K i x y * v y‖ ^ 2 =
      ∑ p : I × κ, ‖∑ y, v y * K p.1 p.2 y‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_comm (K _ _ _)]
  apply Complex.ofReal_injective
  rw [h1, sq_sum_expand]
  have hk : ∀ y1 y2, ∑ p : I × κ, K p.1 p.2 y1 * conj (K p.1 p.2 y2) =
      if y1 = y2 then 1 else 0 := by
    intro y1 y2
    have := congrFun (congrFun hK y2) y1
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      RCLike.star_def] at this
    rw [Fintype.sum_prod_type]
    simp_rw [mul_comm (K _ _ y1)]
    rw [this]
    exact if_congr eq_comm rfl rfl
  simp_rw [hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  push_cast
  simp_rw [← Complex.mul_conj']

theorem transfer1 {O1 O2 Z L J : Type*} [Fintype O1] [Fintype O2] [Fintype Z] [Fintype L]
    [Fintype J] (M : O1 × Z → ℂ) (V : L → Matrix (O1 × O2) Z ℂ) (N : J → Matrix O1 Z ℂ)
    (h : ∀ x1 x2 : O1 × Z, ∑ p : L × O2, V p.1 (x1.1, p.2) x1.2 * conj (V p.1 (x2.1, p.2) x2.2)
        = ∑ j, N j x1.1 x1.2 * conj (N j x2.1 x2.2)) :
    ∑ p : L × O2, ‖∑ x : O1 × Z, M x * V p.1 (x.1, p.2) x.2‖ ^ 2 =
      ∑ j, ‖∑ x : O1 × Z, M x * N j x.1 x.2‖ ^ 2 :=
  by
  have := sq_sum_transfer M (fun (p : L × O2) (x : O1 × Z) => V p.1 (x.1, p.2) x.2)
    (fun (j : J) (x : O1 × Z) => N j x.1 x.2) h
  exact this

theorem transfer2 {O1 O2 Z L J : Type*} [Fintype O1] [Fintype O2] [Fintype Z] [Fintype L]
    [Fintype J] (M : O2 × Z → ℂ) (V : L → Matrix (O1 × O2) Z ℂ) (N : J → Matrix O2 Z ℂ)
    (h : ∀ x1 x2 : O2 × Z, ∑ p : L × O1, V p.1 (p.2, x1.1) x1.2 * conj (V p.1 (p.2, x2.1) x2.2)
        = ∑ j, N j x1.1 x1.2 * conj (N j x2.1 x2.2)) :
    ∑ p : L × O1, ‖∑ x : O2 × Z, M x * V p.1 (p.2, x.1) x.2‖ ^ 2 =
      ∑ j, ‖∑ x : O2 × Z, M x * N j x.1 x.2‖ ^ 2 :=
  by
  have := sq_sum_transfer M (fun (p : L × O1) (x : O2 × Z) => V p.1 (p.2, x.1) x.2)
    (fun (j : J) (x : O2 × Z) => N j x.1 x.2) h
  exact this

theorem trace_BNA {Rr Z O : Type*} [Fintype Rr] [Fintype Z] [Fintype O]
    (B : Matrix Rr O ℂ) (N : Matrix O Z ℂ) (A : Matrix Z Rr ℂ) :
    (B * N * A).trace = ∑ x : O × Z, (∑ r, B r x.1 * A x.2 r) * N x.1 x.2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  calc ∑ y, ∑ x, ∑ x_1, B x x_1 * N x_1 y * A y x = ∑ y, ∑ x_1, ∑ x, B x x_1 * N x_1 y * A y x :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ =>
          Finset.sum_congr rfl fun r _ => ?_
        ring

/-- Kernel of a product Kraus family with qubit-dependent factors. -/
theorem prod_kernel {n : ℕ} {K α β : Type*} [Fintype K] (E : Fin n → K → Matrix α β ℂ)
    (y1 y2 : Fin n → α) (z1 z2 : Fin n → β) :
    ∑ j : Fin n → K, (∏ q, E q (j q) (y1 q) (z1 q)) * conj (∏ q, E q (j q) (y2 q) (z2 q)) =
      ∏ q, ∑ k, E q k (y1 q) (z1 q) * conj (E q k (y2 q) (z2 q)) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib]

/-- Weighted kernel transfer. -/
theorem sq_sum_mix {X I E J : Type*} [Fintype X] [Fintype I] [Fintype E] [Fintype J]
    (M : X → ℂ) (P : I → X → ℂ) (w : E → ℝ) (Q : E → J → X → ℂ)
    (h : ∀ x1 x2, ∑ i, P i x1 * conj (P i x2) =
      ∑ e, (w e : ℂ) * ∑ j, Q e j x1 * conj (Q e j x2)) :
    ∑ i, ‖∑ x, M x * P i x‖ ^ 2 = ∑ e, w e * ∑ j, ‖∑ x, M x * Q e j x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sq_sum_expand, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, sq_sum_expand, h, Finset.mul_sum]
  conv_rhs => rw [cyc3]
  refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Erasure Kraus operators for a deterministic erasure pattern `e` (`true` = erased). -/
noncomputable def patKraus {n : ℕ} (e : Fin n → Bool) (j : Fin n → Fin 5) :
    Matrix (Fin n → Bool × Bool) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, erasureKraus (if e q then 1 else 0) (j q) (y q) (z q)

theorem erasureKernel_affine (p : ℝ) (o o' : Bool × Bool) (b b' : Bool) :
    erasureKernel p o o' b b' =
      ((1 - p : ℝ) : ℂ) * erasureKernel 0 o o' b b' + ((p : ℝ) : ℂ) * erasureKernel 1 o o' b b' := by
  unfold erasureKernel
  split_ifs <;> push_cast <;> ring

theorem erasure_kernel_conj (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (o o' : Bool × Bool) (b b' : Bool) :
    ∑ k, erasureKraus r k o b * conj (erasureKraus r k o' b') = erasureKernel r o o' b b' :=
  erasureKraus_kernel r h0 h1 o o' b b'

/-- The erasure channel's branch sums split over deterministic erasure patterns. -/
theorem erasure_split {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : (Fin n → Bool × Bool) × Qubits n → ℂ) :
    ∑ j : Fin n → Fin 5, ‖∑ x, M x * (∏ q, erasureKraus p (j q) (x.1 q) (x.2 q))‖ ^ 2 =
      ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) *
        ∑ j : Fin n → Fin 5, ‖∑ x, M x * patKraus e j x.1 x.2‖ ^ 2 := by
  have key := sq_sum_mix M
    (fun (j : Fin n → Fin 5) (x : (Fin n → Bool × Bool) × Qubits n) =>
      ∏ q, erasureKraus p (j q) (x.1 q) (x.2 q))
    (fun (e : Fin n → Bool) => ∏ q, if e q then p else 1 - p)
    (fun (e : Fin n → Bool) (j : Fin n → Fin 5) (x : (Fin n → Bool × Bool) × Qubits n) =>
      patKraus e j x.1 x.2)
  refine key ?_
  intro x1 x2
  beta_reduce
  have hpk : ∀ (e : Fin n → Bool) (j : Fin n → Fin 5) (y : Fin n → Bool × Bool) (z : Qubits n),
      patKraus e j y z = ∏ q, erasureKraus (if e q then 1 else 0) (j q) (y q) (z q) :=
    fun _ _ _ _ => rfl
  simp_rw [hpk]
  have hk1 := prod_kernel (fun _ => erasureKraus p) x1.1 x2.1 x1.2 x2.2
  beta_reduce at hk1
  rw [hk1]
  simp_rw [erasure_kernel_conj p hp0 hp1]
  have hsplit : ∀ q, erasureKernel p (x1.1 q) (x2.1 q) (x1.2 q) (x2.2 q) =
      ∑ c : Bool, (if c then ((p : ℝ) : ℂ) * erasureKernel 1 (x1.1 q) (x2.1 q) (x1.2 q) (x2.2 q)
        else ((1 - p : ℝ) : ℂ) * erasureKernel 0 (x1.1 q) (x2.1 q) (x1.2 q) (x2.2 q)) := by
    intro q
    rw [erasureKernel_affine p, Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring
  rw [Finset.prod_congr rfl fun q _ => hsplit q, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hk2 := prod_kernel (fun q => erasureKraus (if e q then 1 else 0)) x1.1 x2.1 x1.2 x2.2
  beta_reduce at hk2
  rw [hk2]
  have hpe : ∀ q, (0 : ℝ) ≤ (if e q then 1 else 0) ∧ (if e q then (1 : ℝ) else 0) ≤ 1 := by
    intro q; split_ifs <;> norm_num
  rw [Finset.prod_congr rfl fun q _ => erasure_kernel_conj _ (hpe q).1 (hpe q).2 _ _ _ _]
  rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  split_ifs <;> rfl


/-! ### Session 5: broadcast isometry, pattern fidelity, assembly of C2 -/

theorem fid_pattern_given {k n : ℕ} {KA KB : Type*} [Fintype KA] [Fintype KB] (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : KA → Matrix (Qubits n) (Qubits k) ℂ) (B : KB → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ) :
    entanglementFidelity (krausApply B ∘ erasureChannel n p ∘ krausApply A) =
        (((2 : ℝ) ^ k)⁻¹) ^ 2 * ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) *
          ∑ a, ∑ b, ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2 := by
  rw [fid_comp_given A B (erasureChannel n p)
    (fun j : Fin n → Fin 5 => Matrix.of fun (y : Fin n → Bool × Bool) (z : Qubits n) =>
      ∏ q, erasureKraus p (j q) (y q) (z q)) (fun ρ => rfl)]
  congr 1
  have hL : ∀ (a : KA) (b : KB),
      ∑ j : Fin n → Fin 5, ‖(B b * (Matrix.of fun (y : Fin n → Bool × Bool) (z : Qubits n) =>
        ∏ q, erasureKraus p (j q) (y q) (z q)) * A a).trace‖ ^ 2 =
      ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) *
        ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2 := by
    intro a b
    simp only [trace_BNA, Matrix.of_apply]
    exact erasure_split p hp0 hp1 _
  have hperm : ∀ F : KB → (Fin n → Fin 5) → KA → ℝ,
      ∑ b, ∑ j, ∑ a, F b j a = ∑ a, ∑ b, ∑ j, F b j a :=
    fun F => (cyc3 F).trans (cyc3 fun (j : Fin n → Fin 5) (a : KA) (b : KB) => F b j a)
  refine (hperm _).trans ?_
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hL a b).trans ?_
  simp_rw [Finset.mul_sum]
  exact (cyc3 _).trans (cyc3 _)

/-- Fidelity lower bound from a family of good branches per erasure pattern. -/
theorem fid_lower {k n : ℕ} {KA KB : Type*} [Fintype KA] [Fintype KB] (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1)
    (A : KA → Matrix (Qubits n) (Qubits k) ℂ) (B : KB → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ)
    (good : (Fin n → Bool) → Prop) [DecidablePred good]
    (T : (Fin n → Bool) → Finset (KA × KB × (Fin n → Fin 5)))
    (hT : ∀ e, good e →
      ∑ t ∈ T e, ‖(B t.2.1 * patKraus e t.2.2 * A t.1).trace‖ ^ 2 = ((2 : ℝ) ^ k) ^ 2) :
    ∑ e ∈ Finset.univ.filter good, (∏ q, if e q then p else 1 - p) ≤
      entanglementFidelity (krausApply B ∘ erasureChannel n p ∘ krausApply A) := by
  rw [fid_pattern_given p hp0 hp1 A B]
  have hpe : ∀ e : Fin n → Bool, 0 ≤ ∏ q, if e q then p else 1 - p := fun e =>
    Finset.prod_nonneg fun q _ => by split_ifs <;> linarith
  have hin : ∀ e, good e → ((2 : ℝ) ^ k) ^ 2 ≤
      ∑ a, ∑ b, ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2 := by
    intro e he
    rw [← hT e he]
    have hre : ∑ a, ∑ b, ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2 =
        ∑ t : KA × KB × (Fin n → Fin 5), ‖(B t.2.1 * patKraus e t.2.2 * A t.1).trace‖ ^ 2 := by
      simp only [Fintype.sum_prod_type]
    rw [hre]
    exact Finset.sum_le_univ_sum_of_nonneg fun t => by positivity
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  split_ifs with he
  · have h1 := mul_le_mul_of_nonneg_left (hin e he) (hpe e)
    calc (∏ q, if e q then p else 1 - p) = ((2 : ℝ) ^ k)⁻¹ ^ 2 *
          ((∏ q, if e q then p else 1 - p) * ((2 : ℝ) ^ k) ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact mul_nonneg (by positivity) (mul_nonneg (hpe e) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity))

end EC74504552G


/-! G1c for C1 (erasure achievability): counting random generator matrices over `ZMod 2`
that are bad for a fixed erased set `S`. Rows `0..a-1` span `C1`, rows `0..b-1` span `C2`. -/

namespace EC74504552C

open Finset

/-- A nonzero functional over `ZMod 2` has a kernel of exactly half the space. -/
theorem card_hyperplane {d : ℕ} (m : Fin d → ZMod 2) (hm : m ≠ 0) :
    2 * (univ.filter (fun v : Fin d → ZMod 2 => ∑ i, m i * v i = 0)).card = 2 ^ d := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i0, m i0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm (funext h)
  have hm1 : m i0 = 1 := by
    have key : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact key _ hi0
  set e : Fin d → ZMod 2 := Pi.single i0 1
  have hsum : ∀ v : Fin d → ZMod 2, ∑ i, m i * (v + e) i = (∑ i, m i * v i) + 1 := by
    intro v
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, e]
    congr 1
    rw [Finset.sum_eq_single i0]
    · simp [hm1]
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  have hee : ∀ v : Fin d → ZMod 2, v + e + e = v := by
    intro v
    rw [add_assoc]
    have : e + e = 0 := by
      funext j
      simp only [Pi.add_apply, Pi.zero_apply]
      have key : ∀ t : ZMod 2, t + t = 0 := by decide
      exact key _
    rw [this, add_zero]
  have h01 : ∀ s : ZMod 2, s + 1 = 0 ↔ s ≠ 0 := by
    decide
  have hcard : (univ.filter (fun v : Fin d → ZMod 2 => ∑ i, m i * v i = 0)).card
      = (univ.filter (fun v : Fin d → ZMod 2 => ¬ (∑ i, m i * v i = 0))).card := by
    refine Finset.card_bij' (fun v _ => v + e) (fun v _ => v + e) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      rw [hsum, hv]; decide
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      rw [hsum, h01]; exact hv
    · intro v _; exact hee v
    · intro v _; exact hee v
  have htot := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin d → ZMod 2))) (fun v : Fin d → ZMod 2 => ∑ i, m i * v i = 0)
  rw [← hcard] at htot
  rw [two_mul, htot, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The generator matrices for which a fixed nonzero message `m` encodes into a word
supported in `S`: count times `2^(n-|S|)` is everything. -/
theorem card_msg_in (a n : ℕ) (S : Finset (Fin n)) (m : Fin a → ZMod 2) (hm : m ≠ 0) :
    (univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        ∀ j, j ∉ S → ∑ i, m i * G i j = 0)).card * 2 ^ (n - S.card) = 2 ^ (a * n) := by
  classical
  let H : Finset (Fin a → ZMod 2) := univ.filter (fun v => ∑ i, m i * v i = 0)
  let t : Fin n → Finset (Fin a → ZMod 2) := fun j => if j ∈ S then univ else H
  let sw : (Fin a → Fin n → ZMod 2) ≃ (Fin n → Fin a → ZMod 2) :=
    { toFun := fun G j i => G i j, invFun := fun c i j => c j i,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have himg : (univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        ∀ j, j ∉ S → ∑ i, m i * G i j = 0)).card = (Fintype.piFinset t).card := by
    refine Finset.card_bij' (fun G _ => sw G) (fun c _ => sw.symm c) ?_ ?_ ?_ ?_
    · intro G hG
      simp only [mem_filter, mem_univ, true_and] at hG
      rw [Fintype.mem_piFinset]
      intro j
      by_cases hj : j ∈ S
      · simp [t, hj]
      · simp only [t, hj, if_false, H, mem_filter, mem_univ, true_and]
        exact hG j hj
    · intro c hc
      rw [Fintype.mem_piFinset] at hc
      simp only [mem_filter, mem_univ, true_and]
      intro j hj
      have := hc j
      simp only [t, hj, if_false, H, mem_filter, mem_univ, true_and] at this
      exact this
    · intro G _; rfl
    · intro c _; rfl
  rw [himg, Fintype.card_piFinset]
  have hc : ∀ j : Fin n, (t j).card * (if j ∈ S then 1 else 2) = 2 ^ a := by
    intro j
    by_cases hj : j ∈ S
    · simp [t, hj, Fintype.card_fun, ZMod.card]
    · simp only [t, hj, if_false]
      rw [mul_comm]
      exact card_hyperplane m hm
  have hp : ∏ j : Fin n, (if j ∈ S then 1 else 2) = 2 ^ (n - S.card) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun j => j ∈ S)
    rw [Finset.card_univ, Fintype.card_fin] at this
    have hS : (univ.filter (fun j : Fin n => j ∈ S)).card = S.card := by
      congr 1; ext j; simp
    omega
  rw [← hp, ← Finset.prod_mul_distrib]
  simp_rw [hc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- The generator matrices for which a fixed nonzero `z` is orthogonal to the first `b` rows. -/
theorem card_dual_in (a n b : ℕ) (hb : b ≤ a) (z : Fin n → ZMod 2) (hz : z ≠ 0) :
    (univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0)).card * 2 ^ b = 2 ^ (a * n) := by
  classical
  let H : Finset (Fin n → ZMod 2) := univ.filter (fun v => ∑ j, z j * v j = 0)
  let t : Fin a → Finset (Fin n → ZMod 2) := fun i => if i.val < b then H else univ
  have himg : (univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0)) = Fintype.piFinset t := by
    ext G
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hG i
      by_cases hi : i.val < b
      · simp only [t, hi, if_true, H, mem_filter, mem_univ, true_and]; exact hG i hi
      · simp [t, hi]
    · intro hG i hi
      have := hG i
      simp only [t, hi, if_true, H, mem_filter, mem_univ, true_and] at this
      exact this
  rw [himg, Fintype.card_piFinset]
  have hc : ∀ i : Fin a, (t i).card * (if i.val < b then 2 else 1) = 2 ^ n := by
    intro i
    by_cases hi : i.val < b
    · simp only [t, hi, if_true]
      rw [mul_comm]
      exact card_hyperplane z hz
    · simp [t, hi, Fintype.card_fun, ZMod.card]
  have hp : ∏ i : Fin a, (if i.val < b then 2 else 1) = 2 ^ b := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    have hS : (univ.filter (fun i : Fin a => i.val < b))
        = (univ : Finset (Fin b)).map (Fin.castLEEmb hb) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_map]
      constructor
      · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
      · rintro ⟨j, -, rfl⟩; exact j.2
    rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [← hp, ← Finset.prod_mul_distrib]
  simp_rw [hc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

/-- Words supported in `S`: at most `2^|S|`. -/
theorem card_supp_le (n : ℕ) (S : Finset (Fin n)) :
    (univ.filter (fun z : Fin n → ZMod 2 => z ≠ 0 ∧ ∀ j, j ∉ S → z j = 0)).card ≤ 2 ^ S.card := by
  classical
  let t : Fin n → Finset (ZMod 2) := fun j => if j ∈ S then univ else {0}
  have hsub : (univ.filter (fun z : Fin n → ZMod 2 => z ≠ 0 ∧ ∀ j, j ∉ S → z j = 0))
      ⊆ Fintype.piFinset t := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j ∈ S
    · simp [t, hj]
    · simp [t, hj, hz.2 j hj]
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  have hc : ∀ j, (t j).card = if j ∈ S then 2 else 1 := by
    intro j; by_cases hj : j ∈ S <;> simp [t, hj, ZMod.card]
  simp_rw [hc]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  congr 1; ext j; simp

/-- Union bound: the generator matrices bad for the erased set `S`. -/
theorem card_bad_le (a n b : ℕ) (hb : b ≤ a) (S : Finset (Fin n)) :
    ((univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        (∃ m : Fin a → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0) ∨
        (∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
          ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0))).card : ℝ)
      ≤ 2 ^ (a * n) * ((2 : ℝ) ^ a / 2 ^ (n - S.card) + (2 : ℝ) ^ S.card / 2 ^ b) := by
  classical
  let Ms : Finset (Fin a → ZMod 2) := univ.filter (fun m => m ≠ 0)
  let Zs : Finset (Fin n → ZMod 2) := univ.filter (fun z => z ≠ 0 ∧ ∀ j, j ∉ S → z j = 0)
  let A : (Fin a → ZMod 2) → Finset (Fin a → Fin n → ZMod 2) := fun m =>
    univ.filter (fun G => ∀ j, j ∉ S → ∑ i, m i * G i j = 0)
  let B : (Fin n → ZMod 2) → Finset (Fin a → Fin n → ZMod 2) := fun z =>
    univ.filter (fun G => ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0)
  have hsub : (univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        (∃ m : Fin a → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0) ∨
        (∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
          ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0)))
      ⊆ Ms.biUnion A ∪ Zs.biUnion B := by
    intro G hG
    simp only [mem_filter, mem_univ, true_and] at hG
    rcases hG with ⟨m, hm, h⟩ | ⟨z, hz, hS, h⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, ?_, ?_⟩)
      · simp [Ms, hm]
      · simp only [A, mem_filter, mem_univ, true_and]; exact h
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z, ?_, ?_⟩)
      · simp only [Zs, mem_filter, mem_univ, true_and]; exact ⟨hz, hS⟩
      · simp only [B, mem_filter, mem_univ, true_and]; exact h
  have hA : ∀ m ∈ Ms, ((A m).card : ℝ) = 2 ^ (a * n) / 2 ^ (n - S.card) := by
    intro m hm
    simp only [Ms, mem_filter, mem_univ, true_and] at hm
    have := card_msg_in a n S m hm
    rw [eq_div_iff (by positivity)]
    exact_mod_cast this
  have hB : ∀ z ∈ Zs, ((B z).card : ℝ) = 2 ^ (a * n) / 2 ^ b := by
    intro z hz
    simp only [Zs, mem_filter, mem_univ, true_and] at hz
    have := card_dual_in a n b hb z hz.1
    rw [eq_div_iff (by positivity)]
    exact_mod_cast this
  have hMs : (Ms.card : ℝ) ≤ 2 ^ a := by
    have : Ms.card ≤ 2 ^ a := by
      refine (Finset.card_le_univ _).trans (le_of_eq ?_)
      simp [Fintype.card_fun, ZMod.card]
    exact_mod_cast this
  have hZs : (Zs.card : ℝ) ≤ 2 ^ S.card := by exact_mod_cast card_supp_le n S
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Ms.biUnion A) (Zs.biUnion B)
  have h3 := Finset.card_biUnion_le (s := Ms) (t := A)
  have h4 := Finset.card_biUnion_le (s := Zs) (t := B)
  have hsum : ((univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        (∃ m : Fin a → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0) ∨
        (∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
          ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0))).card : ℝ)
      ≤ ∑ m ∈ Ms, ((A m).card : ℝ) + ∑ z ∈ Zs, ((B z).card : ℝ) := by
    have : (univ.filter (fun G : Fin a → Fin n → ZMod 2 =>
        (∃ m : Fin a → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0) ∨
        (∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
          ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0))).card
        ≤ ∑ m ∈ Ms, (A m).card + ∑ z ∈ Zs, (B z).card := by omega
    exact_mod_cast this
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  have e1 : (Ms.card : ℝ) * (2 ^ (a * n) / 2 ^ (n - S.card))
      ≤ 2 ^ (a * n) * ((2 : ℝ) ^ a / 2 ^ (n - S.card)) := by
    rw [mul_div_assoc', mul_div_assoc', mul_comm ((2:ℝ) ^ (a * n))]
    gcongr
  have e2 : (Zs.card : ℝ) * (2 ^ (a * n) / 2 ^ b)
      ≤ 2 ^ (a * n) * ((2 : ℝ) ^ S.card / 2 ^ b) := by
    rw [mul_div_assoc', mul_div_assoc', mul_comm ((2:ℝ) ^ (a * n))]
    gcongr
  rw [mul_add]
  exact add_le_add e1 e2

/-! G1d: Bernoulli patterns `e : Fin n → Bool`, weight `∏ q, if e q then p else 1 - p`
(the weight in `EC74504552G.erasure_split`), and the Chebyshev tail of the erased count. -/

/-- Pattern weight. -/
noncomputable def pw {n : ℕ} (p : ℝ) (e : Fin n → Bool) : ℝ := ∏ q, if e q then p else 1 - p

/-- Number of erased positions. -/
def ecount {n : ℕ} (e : Fin n → Bool) : ℕ := (univ.filter (fun q => e q = true)).card

theorem pattern_sum_card (n : ℕ) (p : ℝ) (g : ℕ → ℝ) :
    ∑ e : Fin n → Bool, pw p e * g (ecount e)
      = ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) * g k := by
  classical
  let eqv : (Fin n → Bool) ≃ Finset (Fin n) :=
    { toFun := fun e => univ.filter (fun q => e q = true)
      invFun := fun S q => decide (q ∈ S)
      left_inv := fun e => by funext q; simp
      right_inv := fun S => by ext q; simp }
  have hw : ∀ e : Fin n → Bool, pw p e * g (ecount e)
      = (fun S : Finset (Fin n) => p ^ S.card * (1 - p) ^ (n - S.card) * g S.card) (eqv e) := by
    intro e
    simp only [pw, ecount, eqv, Equiv.coe_fn_mk]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun q => e q = true)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [Fintype.sum_equiv eqv _
    (fun S : Finset (Fin n) => p ^ S.card * (1 - p) ^ (n - S.card) * g S.card) hw]
  rw [← Finset.powerset_univ]
  rw [Finset.sum_powerset_apply_card (fun k => p ^ k * (1 - p) ^ (n - k) * g k)]
  rw [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]; ring

theorem pattern_variance (n : ℕ) (p : ℝ) :
    ∑ e : Fin n → Bool, pw p e * ((ecount e : ℝ) - n * p) ^ 2 = n * p * (1 - p) := by
  rw [pattern_sum_card n p (fun k => ((k : ℝ) - n * p) ^ 2)]
  have hv := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ n)
  rw [Polynomial.eval_finsetSum] at hv
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_smul, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_one,
    nsmul_eq_mul] at hv
  rw [← hv]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pw_nonneg {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : Fin n → Bool) : 0 ≤ pw p e := by
  unfold pw
  refine Finset.prod_nonneg fun q _ => ?_
  split_ifs <;> linarith

/-- Chebyshev: the weight of patterns with at least `(p + η) n` erasures. -/
theorem tail_bound (n : ℕ) (p η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 < η) :
    η ^ 2 * (n : ℝ) ^ 2 * ∑ e ∈ univ.filter (fun e : Fin n → Bool => (p + η) * n ≤ ecount e),
      pw p e ≤ n * p * (1 - p) := by
  rw [← pattern_variance n p, Finset.mul_sum]
  calc ∑ e ∈ univ.filter (fun e : Fin n → Bool => (p + η) * n ≤ ecount e), η ^ 2 * (n : ℝ) ^ 2 * pw p e
      ≤ ∑ e ∈ univ.filter (fun e : Fin n → Bool => (p + η) * n ≤ ecount e),
          pw p e * ((ecount e : ℝ) - n * p) ^ 2 := by
        refine Finset.sum_le_sum fun e he => ?_
        simp only [mem_filter, mem_univ, true_and] at he
        have h0 := pw_nonneg p hp0 hp1 e
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have h1 : η * n ≤ (ecount e : ℝ) - n * p := by nlinarith
        have h2 : (η * n) ^ 2 ≤ ((ecount e : ℝ) - n * p) ^ 2 := by
          have : 0 ≤ η * n := by positivity
          nlinarith
        nlinarith
    _ ≤ ∑ e : Fin n → Bool, pw p e * ((ecount e : ℝ) - n * p) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun e _ _ => ?_
        exact mul_nonneg (pw_nonneg p hp0 hp1 e) (sq_nonneg _)

/-- Bad generator matrix for an erased set. -/
def Bad {a n : ℕ} (b : ℕ) (G : Fin a → Fin n → ZMod 2) (S : Finset (Fin n)) : Prop :=
  (∃ m : Fin a → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0) ∨
  (∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
    ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0)

/-- Erased set of a pattern. -/
def Sof {n : ℕ} (e : Fin n → Bool) : Finset (Fin n) := univ.filter (fun q => e q = true)

open Classical in
/-- Indicator of a bad pattern. -/
noncomputable def badI {a n : ℕ} (b : ℕ) (G : Fin a → Fin n → ZMod 2) (e : Fin n → Bool) : ℝ :=
  if Bad b G (Sof e) then 1 else 0

theorem badI_nonneg {a n : ℕ} (b : ℕ) (G : Fin a → Fin n → ZMod 2) (e : Fin n → Bool) :
    0 ≤ badI b G e := by
  unfold badI; split_ifs <;> norm_num

theorem badI_le_one {a n : ℕ} (b : ℕ) (G : Fin a → Fin n → ZMod 2) (e : Fin n → Bool) :
    badI b G e ≤ 1 := by
  unfold badI; split_ifs <;> norm_num

theorem sum_badI (a n b : ℕ) (hb : b ≤ a) (e : Fin n → Bool) :
    ∑ G : Fin a → Fin n → ZMod 2, badI b G e
      ≤ 2 ^ (a * n) * ((2 : ℝ) ^ a / 2 ^ (n - ecount e) + (2 : ℝ) ^ ecount e / 2 ^ b) := by
  classical
  have h := card_bad_le a n b hb (Sof e)
  have hc : ∑ G : Fin a → Fin n → ZMod 2, badI b G e
      = ((univ.filter (fun G : Fin a → Fin n → ZMod 2 => Bad b G (Sof e))).card : ℝ) := by
    unfold badI
    rw [Finset.sum_boole]
  rw [hc]
  convert h using 3
  all_goals first
    | rfl
    | (ext G; rw [Finset.mem_filter, Finset.mem_filter]; rfl)

theorem sum_badI_le_card (a n b : ℕ) (e : Fin n → Bool) :
    ∑ G : Fin a → Fin n → ZMod 2, badI b G e ≤ 2 ^ (a * n) := by
  calc ∑ G : Fin a → Fin n → ZMod 2, badI b G e ≤ ∑ G : Fin a → Fin n → ZMod 2, (1 : ℝ) :=
        Finset.sum_le_sum fun G _ => badI_le_one b G e
    _ = 2 ^ (a * n) := by
        simp [Finset.card_univ, ZMod.card, pow_mul]
        ring

theorem pw_sum_one (n : ℕ) (p : ℝ) : ∑ e : Fin n → Bool, pw p e = 1 := by
  unfold pw
  rw [← Fintype.prod_sum (fun (_ : Fin n) (t : Bool) => if t then p else 1 - p)]
  simp

/-- Averaging: some generator matrix has small bad mass. -/
theorem exists_good_G (a n b s0 : ℕ) (hb : b ≤ a) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ G : Fin a → Fin n → ZMod 2,
      ∑ e : Fin n → Bool, pw p e * badI b G e
        ≤ ∑ e ∈ univ.filter (fun e : Fin n → Bool => s0 < ecount e), pw p e
          + ((2 : ℝ) ^ a / 2 ^ (n - s0) + (2 : ℝ) ^ s0 / 2 ^ b) := by
  classical
  set T : ℝ := ∑ e ∈ univ.filter (fun e : Fin n → Bool => s0 < ecount e), pw p e
    + ((2 : ℝ) ^ a / 2 ^ (n - s0) + (2 : ℝ) ^ s0 / 2 ^ b) with hT
  set c : ℝ := (2 : ℝ) ^ a / 2 ^ (n - s0) + (2 : ℝ) ^ s0 / 2 ^ b with hc
  have hc0 : 0 ≤ c := by positivity
  have key : ∀ e : Fin n → Bool, pw p e * ∑ G : Fin a → Fin n → ZMod 2, badI b G e
      ≤ 2 ^ (a * n) * (pw p e * (if s0 < ecount e then 1 else 0) + pw p e * c) := by
    intro e
    have hpw := pw_nonneg p hp0 hp1 e
    by_cases hs : s0 < ecount e
    · rw [if_pos hs]
      have := mul_le_mul_of_nonneg_left (sum_badI_le_card a n b e) hpw
      nlinarith [mul_nonneg hpw hc0, (by positivity : (0:ℝ) ≤ 2 ^ (a * n))]
    · rw [if_neg hs]
      push Not at hs
      have h1 : (2 : ℝ) ^ a / 2 ^ (n - ecount e) ≤ (2 : ℝ) ^ a / 2 ^ (n - s0) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ ecount e / 2 ^ b ≤ (2 : ℝ) ^ s0 / 2 ^ b := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hs
      have h3 := mul_le_mul_of_nonneg_left (sum_badI a n b hb e) hpw
      have h4 : (2 : ℝ) ^ (a * n) * ((2 : ℝ) ^ a / 2 ^ (n - ecount e) + (2 : ℝ) ^ ecount e / 2 ^ b)
          ≤ 2 ^ (a * n) * c := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); rw [hc]; linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hpw
      nlinarith
  have hsum : ∑ G : Fin a → Fin n → ZMod 2, ∑ e : Fin n → Bool, pw p e * badI b G e
      ≤ ∑ G : Fin a → Fin n → ZMod 2, T := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc ∑ e : Fin n → Bool, pw p e * ∑ G : Fin a → Fin n → ZMod 2, badI b G e
        ≤ ∑ e : Fin n → Bool, 2 ^ (a * n) * (pw p e * (if s0 < ecount e then 1 else 0) + pw p e * c) :=
          Finset.sum_le_sum fun e _ => key e
      _ = ∑ G : Fin a → Fin n → ZMod 2, T := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, pw_sum_one, one_mul]
          rw [Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul]
          rw [hT, Finset.sum_filter]
          simp_rw [mul_ite, mul_one, mul_zero]
          push_cast; ring
  obtain ⟨G, -, hG⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨G, hG⟩

/-- Restriction map of the `C2` generator rows to the erased set. -/
noncomputable def Lres {a n b : ℕ} (hb : b ≤ a) (G : Fin a → Fin n → ZMod 2) (S : Finset (Fin n)) :
    (Fin b → ZMod 2) →ₗ[ZMod 2] (↥S → ZMod 2) :=
  (Matrix.of fun (s : ↥S) (i : Fin b) => G (Fin.castLE hb i) s).mulVecLin

/-- Second goodness condition gives surjectivity of the restriction map. -/
theorem Lres_surj {a n b : ℕ} (hb : b ≤ a) (G : Fin a → Fin n → ZMod 2) (S : Finset (Fin n))
    (hB : ¬ ∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
      ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0) :
    Function.Surjective (Lres hb G S) := by
  classical
  by_contra hns
  have hlt : LinearMap.range (Lres hb G S) < ⊤ :=
    lt_top_iff_ne_top.2 (fun h => hns (LinearMap.range_eq_top.1 h))
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  let z : Fin n → ZMod 2 := fun j =>
    if h : j ∈ S then f (fun t : ↥S => if (⟨j, h⟩ : ↥S) = t then 1 else 0) else 0
  have hfz : ∀ v : ↥S → ZMod 2, f v = ∑ j, z j * (∑ s : ↥S, if (s : Fin n) = j then v s else 0) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single (s : Fin n)]
    · simp [z, s.2, smul_eq_mul, mul_comm]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hf_ann : ∀ y, f (Lres hb G S y) = 0 := by
    intro y
    have : f (Lres hb G S y) ∈ Submodule.map f (LinearMap.range (Lres hb G S)) :=
      ⟨Lres hb G S y, ⟨y, rfl⟩, rfl⟩
    rw [hfmap] at this
    exact (Submodule.mem_bot _).1 this
  apply hB
  refine ⟨z, ?_, ?_, ?_⟩
  · intro hz
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hfz v, hz]
    simp
  · intro j hj
    simp [z, hj]
  · intro i hi
    have h1 := hf_ann (Pi.single ⟨i.val, hi⟩ 1)
    rw [hfz] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S
    · congr 1
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp only [if_true, Lres, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
          Matrix.of_apply]
        rw [Finset.sum_eq_single ⟨i.val, hi⟩]
        · have : Fin.castLE hb ⟨i.val, hi⟩ = i := Fin.ext rfl
          simp [this]
        · intro i' _ hi'; simp [Pi.single_apply, hi']
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        have : (s : Fin n) ≠ j := fun h => hs (Subtype.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [z, hj]

/-- Under the second goodness condition every fibre of the restriction map has `2^b / 2^|S|` points. -/
theorem fiber_card {a n b : ℕ} (hb : b ≤ a) (G : Fin a → Fin n → ZMod 2) (S : Finset (Fin n))
    (hB : ¬ ∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ S → z j = 0) ∧
      ∀ i : Fin a, i.val < b → ∑ j, z j * G i j = 0) (c : ↥S → ZMod 2) :
    (univ.filter (fun y : Fin b → ZMod 2 => Lres hb G S y = c)).card * 2 ^ S.card = 2 ^ b := by
  classical
  have hs := Lres_surj hb G S hB
  have heq : ∀ c' : ↥S → ZMod 2, (univ.filter (fun y : Fin b → ZMod 2 => Lres hb G S y = c')).card
      = (univ.filter (fun y : Fin b → ZMod 2 => Lres hb G S y = c)).card := by
    intro c'
    exact AddMonoidHom.card_fiber_eq_of_mem_range (Lres hb G S).toAddMonoidHom
      (hs c') (hs c)
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin b → ZMod 2)))
    (t := (univ : Finset (↥S → ZMod 2))) (f := fun y => Lres hb G S y) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Fintype.card_coe] at hsum
  rw [hsum, Finset.sum_congr rfl (fun c' _ => heq c'), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]
  simp [Fintype.card_fun, ZMod.card]

end EC74504552C


/-! G1b for C1 (erasure achievability): generic Kraus-completion algebra for the explicit decoder. -/

namespace EC74504552D

open QAlgorithms
open scoped ComplexConjugate Matrix

/-- A family of partial isometries with pairwise orthogonal row spaces sums to a projector. -/
theorem proj_of_partial {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq K]
    (D : K → Matrix κ ι ℂ)
    (horth : ∀ j j', j ≠ j' → D j * (D j')ᴴ = 0)
    (hpi : ∀ j, D j * (D j)ᴴ * D j = D j) :
    (∑ j, (D j)ᴴ * D j) * (∑ j, (D j)ᴴ * D j) = ∑ j, (D j)ᴴ * D j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.mul_assoc] at hpi ⊢
    rw [hpi]
  · intro j' _ hj'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (D j), horth j j' (Ne.symm hj'),
      Matrix.zero_mul, Matrix.mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Completing a projector-valued sub-family by `|z0⟩⟨u| (1 - P)`. -/
theorem kraus_complete {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (D : K → Matrix κ ι ℂ) (z0 : κ)
    (hP : (∑ j, (D j)ᴴ * D j) * (∑ j, (D j)ᴴ * D j) = ∑ j, (D j)ᴴ * D j) :
    IsKrausFamily (Sum.elim D (fun u : ι => Matrix.of fun (r : κ) (s : ι) =>
      if r = z0 then (1 - ∑ j, (D j)ᴴ * D j) u s else 0)) := by
  unfold IsKrausFamily
  set P : Matrix ι ι ℂ := ∑ j, (D j)ᴴ * D j with hPdef
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_sum]
    simp [Matrix.conjTranspose_mul]
  have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP]
    simp
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← hPdef]
  have hE : ∑ u : ι, (Matrix.of fun (r : κ) (s : ι) => if r = z0 then (1 - P) u s else 0)ᴴ *
      (Matrix.of fun (r : κ) (s : ι) => if r = z0 then (1 - P) u s else 0) = (1 - P)ᴴ * (1 - P) := by
    ext s s'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    simp_rw [apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hE, hQ]
  abel

end EC74504552D


/-! G1b for C1 (erasure achievability): the CSS-type code built from a generator matrix
`G : Fin (b + k) → Fin n → ZMod 2` (rows `< b` are the gauge part), its encoding isometry and the
two goodness facts (injectivity off the erased set, constant fibres on it). -/

namespace EC74504552E

open QAlgorithms Finset
open scoped Matrix ComplexConjugate

def ofB (v : Bool) : ZMod 2 := if v then 1 else 0

def toB (v : ZMod 2) : Bool := decide (v = 1)

theorem toB_ofB (v : Bool) : toB (ofB v) = v := by cases v <;> decide

theorem ofB_toB (v : ZMod 2) : ofB (toB v) = v := by fin_cases v <;> rfl

def msg {k b : ℕ} (x : Qubits k) (y : Fin b → ZMod 2) : Fin (b + k) → ZMod 2 :=
  Fin.append y (fun j => ofB (x j))

def cw {a n : ℕ} (G : Fin a → Fin n → ZMod 2) (m : Fin a → ZMod 2) : Fin n → ZMod 2 :=
  fun q => ∑ i, m i * G i q

def wB {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (x : Qubits k) (y : Fin b → ZMod 2) :
    Qubits n :=
  fun q => toB (cw G (msg x y) q)

theorem msg_inj {k b : ℕ} {x x' : Qubits k} {y y' : Fin b → ZMod 2} (h : msg x y = msg x' y') :
    x = x' ∧ y = y' := by
  constructor
  · funext j
    have h1 := congrFun h (Fin.natAdd b j)
    simp only [msg, Fin.append_right] at h1
    have h2 := congrArg toB h1
    simpa [toB_ofB] using h2
  · funext i
    have h1 := congrFun h (Fin.castAdd k i)
    simpa [msg, Fin.append_left] using h1

theorem cw_sub {a n : ℕ} (G : Fin a → Fin n → ZMod 2) (m m' : Fin a → ZMod 2) (q : Fin n) :
    cw G m q - cw G m' q = cw G (m - m') q := by
  simp only [cw, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- (H1) No nonzero `C1` word inside `S`: codewords are determined by their values off `S`. -/
theorem inj_off {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (S : Finset (Fin n))
    (hA : ¬ ∃ m : Fin (b + k) → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0)
    {x x' : Qubits k} {y y' : Fin b → ZMod 2}
    (h : ∀ q, q ∉ S → wB G x y q = wB G x' y' q) : x = x' ∧ y = y' := by
  apply msg_inj
  by_contra hne
  apply hA
  refine ⟨msg x y - msg x' y', sub_ne_zero.mpr hne, fun j hj => ?_⟩
  have h1 := h j hj
  simp only [wB] at h1
  have h2 : cw G (msg x y) j = cw G (msg x' y') j := by
    have h3 := congrArg ofB h1
    simpa [ofB_toB] using h3
  have h4 := cw_sub G (msg x y) (msg x' y') j
  rw [h2, sub_self] at h4
  simpa [cw] using h4.symm

theorem wB_inj {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (S : Finset (Fin n))
    (hA : ¬ ∃ m : Fin (b + k) → ZMod 2, m ≠ 0 ∧ ∀ j, j ∉ S → ∑ i, m i * G i j = 0) :
    ∀ x x' y y', wB G x y = wB G x' y' → x = x' ∧ y = y' :=
  fun _ _ _ _ h => inj_off G S hA fun q _ => congrFun h q

/-- Restriction map of the `C2` generator rows to the erased set (as in the counting file). -/
noncomputable def Lres {a n b : ℕ} (hb : b ≤ a) (G : Fin a → Fin n → ZMod 2) (S : Finset (Fin n)) :
    (Fin b → ZMod 2) →ₗ[ZMod 2] (↥S → ZMod 2) :=
  (Matrix.of fun (s : ↥S) (i : Fin b) => G (Fin.castLE hb i) s).mulVecLin

/-- (H2) Constant fibres: for every message `x` and pattern `c` on `S`, exactly `2^b / 2^|S|`
gauge vectors give a codeword equal to `c` on `S`. -/
theorem wB_fiber {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (S : Finset (Fin n))
    (hfib : ∀ c' : ↥S → ZMod 2,
      (univ.filter (fun y : Fin b → ZMod 2 => Lres (Nat.le_add_right b k) G S y = c')).card
        * 2 ^ S.card = 2 ^ b)
    (x : Qubits k) (c : Qubits n) :
    (univ.filter (fun y : Fin b → ZMod 2 => ∀ q ∈ S, wB G x y q = c q)).card * 2 ^ S.card
      = 2 ^ b := by
  classical
  set c' : ↥S → ZMod 2 := fun s => ofB (c s) - ∑ j : Fin k, ofB (x j) * G (Fin.natAdd b j) s
    with hc'
  have hc : ∀ i : Fin b, Fin.castLE (Nat.le_add_right b k) i = Fin.castAdd k i := fun _ => rfl
  have key : ∀ (y : Fin b → ZMod 2) (s : ↥S), Lres (Nat.le_add_right b k) G S y s =
      cw G (msg x y) s - ∑ j : Fin k, ofB (x j) * G (Fin.natAdd b j) s := by
    intro y s
    simp only [Lres, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, cw, msg,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, hc]
    rw [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hfe : univ.filter (fun y : Fin b → ZMod 2 => ∀ q ∈ S, wB G x y q = c q) =
      univ.filter (fun y : Fin b → ZMod 2 => Lres (Nat.le_add_right b k) G S y = c') := by
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      funext s
      rw [key y s, hc']
      simp only
      rw [← h s s.2]
      simp only [wB, ofB_toB]
    · intro h q hq
      have h1 := congrFun h ⟨q, hq⟩
      rw [key y ⟨q, hq⟩, hc'] at h1
      simp only at h1
      have h3 : cw G (msg x y) q = ofB (c q) := sub_left_inj.mp h1
      simp only [wB]
      rw [h3, toB_ofB]
  rw [hfe]
  exact hfib c'

/-- Real amplitudes of the encoding isometry `V|x⟩ = 2^{-b/2} Σ_y |w(x,y)⟩`. -/
noncomputable def vR {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (z : Qubits n) (x : Qubits k) :
    ℝ :=
  (Real.sqrt ((2 : ℝ) ^ b))⁻¹ * ∑ y : Fin b → ZMod 2, if z = wB G x y then (1 : ℝ) else 0

noncomputable def Venc {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) :
    Matrix (Qubits n) (Qubits k) ℂ :=
  Matrix.of fun z x => ((vR G z x : ℝ) : ℂ)

theorem card_gauge (b : ℕ) : (Fintype.card (Fin b → ZMod 2) : ℝ) = 2 ^ b := by
  simp [ZMod.card]

theorem vR_gram {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2)
    (hinj : ∀ x x' y y', wB G x y = wB G x' y' → x = x' ∧ y = y') (x x' : Qubits k) :
    ∑ z, vR G z x * vR G z x' = if x = x' then 1 else 0 := by
  set s : ℝ := (Real.sqrt ((2 : ℝ) ^ b))⁻¹ with hs
  have e1 : ∀ z, vR G z x * vR G z x' = s * s * ∑ y : Fin b → ZMod 2, ∑ y' : Fin b → ZMod 2,
      (if z = wB G x y then (1 : ℝ) else 0) * (if z = wB G x' y' then (1 : ℝ) else 0) := by
    intro z
    simp only [vR, ← hs]
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  simp_rw [e1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset (Qubits n)))]
  have e2 : ∀ y y' : Fin b → ZMod 2, ∑ z : Qubits n,
      (if z = wB G x y then (1 : ℝ) else 0) * (if z = wB G x' y' then (1 : ℝ) else 0) =
      if x = x' ∧ y = y' then 1 else 0 := by
    intro y y'
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : wB G x y = wB G x' y'
    · rw [if_pos h, if_pos (hinj _ _ _ _ h)]
    · rw [if_neg h, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  simp_rw [e2]
  have hss : s * s * (2 : ℝ) ^ b = 1 := by
    rw [hs, ← mul_inv, Real.mul_self_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by positivity)
  by_cases hx : x = x'
  · subst hx
    simp only [true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [card_gauge]
    simpa using hss
  · simp [hx]

theorem Venc_iso {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2)
    (hinj : ∀ x x' y y', wB G x y = wB G x' y' → x = x' ∧ y = y') :
    (Venc G)ᴴ * Venc G = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Venc, Matrix.of_apply,
    RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum, vR_gram G hinj x x', Matrix.one_apply]
  split_ifs <;> simp

/-- (copy of the C2 child definition) erasure Kraus operators for a deterministic pattern. -/
noncomputable def patKraus {n : ℕ} (e : Fin n → Bool) (j : Fin n → Fin 5) :
    Matrix (Fin n → Bool × Bool) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, erasureKraus (if e q then 1 else 0) (j q) (y q) (z q)

/-- (copy of the counting-file definition) number of erased qubits. -/
def ecount {n : ℕ} (e : Fin n → Bool) : ℕ := (univ.filter (fun q => e q = true)).card

def jq (eq aq cq : Bool) : Fin 5 :=
  if eq then (if aq then (if cq then 4 else 3) else (if cq then 2 else 1)) else 0

def jOf {n : ℕ} (e a c : Fin n → Bool) : Fin n → Fin 5 := fun q => jq (e q) (a q) (c q)

def outE {n : ℕ} (e a z : Fin n → Bool) : Fin n → Bool × Bool :=
  fun q => if e q then (a q, true) else (z q, false)

theorem ek_form (eq aq cq : Bool) (o : Bool × Bool) (zq : Bool) :
    erasureKraus (if eq then 1 else 0) (jq eq aq cq) o zq =
      (if eq then ((Real.sqrt (1 / 2) : ℝ) : ℂ) else 1) *
        (if (eq = true → zq = cq) ∧ o = (if eq then (aq, true) else (zq, false)) then 1 else 0) := by
  rcases o with ⟨o1, o2⟩
  cases eq <;> cases aq <;> cases cq <;> cases zq <;> cases o1 <;> cases o2 <;>
    simp [erasureKraus, jq]

theorem patK_form {n : ℕ} (e a c : Fin n → Bool) (o : Fin n → Bool × Bool) (z : Qubits n) :
    patKraus e (jOf e a c) o z =
      ((Real.sqrt (1 / 2) : ℝ) : ℂ) ^ ecount e *
        (if (∀ q, e q = true → z q = c q) ∧ o = outE e a z then 1 else 0) := by
  unfold patKraus
  simp only [Matrix.of_apply, jOf]
  rw [Finset.prod_congr rfl fun q _ => ek_form (e q) (a q) (c q) (o q) (z q)]
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rfl
  · by_cases h : (∀ q, e q = true → z q = c q) ∧ o = outE e a z
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro q _
      rw [if_pos]
      exact ⟨h.1 q, congrFun h.2 q⟩
    · rw [if_neg h]
      have hex : ∃ q, ¬ ((e q = true → z q = c q) ∧
          o q = if e q = true then (a q, true) else (z q, false)) := by
        by_contra hc
        push Not at hc
        exact h ⟨fun q => (hc q).1, funext fun q => (hc q).2⟩
      obtain ⟨q, hq⟩ := hex
      exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

theorem card_canon {n : ℕ} (e : Fin n → Bool) :
    (univ.filter (fun c : Fin n → Bool => ∀ q, e q = false → c q = false)).card = 2 ^ ecount e := by
  have hset : univ.filter (fun c : Fin n → Bool => ∀ q, e q = false → c q = false) =
      Fintype.piFinset (fun q => if e q then (univ : Finset Bool) else {false}) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h q
      cases hq : e q
      · simp [h q hq]
      · simp
    · intro h q hq
      have h1 := h q
      rw [hq] at h1
      simpa using h1
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_univ, Fintype.card_bool, Finset.card_singleton]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

/-- Core real sum of the decoder trace for one message: everything collapses onto the gauge
vectors whose codeword matches the pattern on the erased set. -/
theorem core_sum {Y Z O : Type*} [Fintype Y] [Fintype Z] [Fintype O] [DecidableEq Z]
    [DecidableEq O] [DecidableEq Y]
    (w : Y → Z) (out : Z → O) (Q : Z → Prop) [DecidablePred Q]
    (hinj : ∀ y y', out (w y) = out (w y') → y = y') :
    ∑ o, ∑ z, (∑ y, if Q (w y) ∧ o = out (w y) then (1 : ℝ) else 0) *
        (if Q z ∧ o = out z then (1 : ℝ) else 0) * (∑ y', if z = w y' then (1 : ℝ) else 0) =
      ((univ.filter fun y => Q (w y)).card : ℝ) := by
  have h1 : ∀ o, ∑ z, (if Q z ∧ o = out z then (1 : ℝ) else 0) *
      (∑ y', if z = w y' then (1 : ℝ) else 0) =
      ∑ y', if Q (w y') ∧ o = out (w y') then (1 : ℝ) else 0 := by
    intro o
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => ?_
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∀ y y', ∑ o, (if Q (w y) ∧ o = out (w y) then (1 : ℝ) else 0) *
      (if Q (w y') ∧ o = out (w y') then (1 : ℝ) else 0) =
      if Q (w y) ∧ y = y' then 1 else 0 := by
    intro y y'
    by_cases hy : Q (w y)
    · by_cases hyy : y = y'
      · subst hyy
        simp [hy, Finset.sum_ite_eq']
      · rw [if_neg (fun h => hyy h.2)]
        apply Finset.sum_eq_zero
        intro o _
        by_cases ho : o = out (w y)
        · have hn : ¬ (Q (w y') ∧ o = out (w y')) := fun h => hyy (hinj y y' (ho.symm.trans h.2))
          simp [hn]
        · simp [ho]
    · simp [hy]
  have h3 : ∀ o, ∑ z, (∑ y, if Q (w y) ∧ o = out (w y) then (1 : ℝ) else 0) *
      (if Q z ∧ o = out z then (1 : ℝ) else 0) * (∑ y', if z = w y' then (1 : ℝ) else 0) =
      (∑ y, if Q (w y) ∧ o = out (w y) then (1 : ℝ) else 0) *
        ∑ y', if Q (w y') ∧ o = out (w y') then (1 : ℝ) else 0 := by
    intro o
    rw [← h1 o, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => mul_assoc _ _ _
  simp_rw [h3, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  simp_rw [h2]
  by_cases hy : Q (w y) <;> simp [hy]

/-- Gauge-count normaliser `t = 2^b / 2^|S|`. -/
noncomputable def tN (b : ℕ) {n : ℕ} (e : Fin n → Bool) : ℝ := (2 : ℝ) ^ b / 2 ^ ecount e

/-- Canonical representative: zero off the erased set. -/
def canon {n : ℕ} (e c : Fin n → Bool) : Prop := ∀ q, e q = false → c q = false

/-- Real amplitude of the decoder branch `(e, c, a)`. -/
noncomputable def dR {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (e c a : Fin n → Bool)
    (x : Qubits k) (o : Fin n → Bool × Bool) : ℝ :=
  (Real.sqrt (tN b e))⁻¹ * ∑ y : Fin b → ZMod 2,
    if (∀ q, e q = true → wB G x y q = c q) ∧ o = outE e a (wB G x y) then (1 : ℝ) else 0

open Classical in
/-- Decoder Kraus operator for index `(e, c, a)` (zero unless `e` is good and `c, a` canonical). -/
noncomputable def Dk {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (good : (Fin n → Bool) → Prop)
    (j : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) :
    Matrix (Qubits k) (Fin n → Bool × Bool) ℂ :=
  Matrix.of fun x o => if good j.1 ∧ canon j.1 j.2.1 ∧ canon j.1 j.2.2 then
    ((dR G j.1 j.2.1 j.2.2 x o : ℝ) : ℂ) else 0

theorem const_eval (b S : ℕ) :
    (Real.sqrt ((2 : ℝ) ^ b / 2 ^ S))⁻¹ * Real.sqrt (1 / 2) ^ S * (Real.sqrt ((2 : ℝ) ^ b))⁻¹ *
      ((2 : ℝ) ^ b / 2 ^ S) = 1 / 2 ^ S := by
  have ht : (0 : ℝ) < (2 : ℝ) ^ b / 2 ^ S := by positivity
  have e1 : (Real.sqrt ((2 : ℝ) ^ b / 2 ^ S))⁻¹ * ((2 : ℝ) ^ b / 2 ^ S) =
      Real.sqrt ((2 : ℝ) ^ b / 2 ^ S) := by
    rw [inv_mul_eq_div, Real.div_sqrt]
  set v := Real.sqrt ((2 : ℝ) ^ b / 2 ^ S) * Real.sqrt (1 / 2) ^ S * (Real.sqrt ((2 : ℝ) ^ b))⁻¹
    with hv
  have hlhs : (Real.sqrt ((2 : ℝ) ^ b / 2 ^ S))⁻¹ * Real.sqrt (1 / 2) ^ S *
      (Real.sqrt ((2 : ℝ) ^ b))⁻¹ * ((2 : ℝ) ^ b / 2 ^ S) = v := by
    calc (Real.sqrt ((2 : ℝ) ^ b / 2 ^ S))⁻¹ * Real.sqrt (1 / 2) ^ S *
          (Real.sqrt ((2 : ℝ) ^ b))⁻¹ * ((2 : ℝ) ^ b / 2 ^ S)
        = ((Real.sqrt ((2 : ℝ) ^ b / 2 ^ S))⁻¹ * ((2 : ℝ) ^ b / 2 ^ S)) *
            (Real.sqrt (1 / 2) ^ S * (Real.sqrt ((2 : ℝ) ^ b))⁻¹) := by ring
      _ = v := by rw [e1, hv]; ring
  rw [hlhs]
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hsq : v ^ 2 = (1 / 2 ^ S) ^ 2 := by
    rw [hv, mul_pow, mul_pow, Real.sq_sqrt ht.le, ← pow_mul, mul_comm S 2, pow_mul,
      Real.sq_sqrt (by norm_num), inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
    rw [← mul_pow]
    norm_num
  rw [← Real.sqrt_sq hv0, hsq, Real.sqrt_sq (by positivity)]

/-- Trace of a good decoder branch against the matching erasure branch and the encoder. -/
theorem tr_good {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (good : (Fin n → Bool) → Prop)
    (e c a : Fin n → Bool) (hg : good e) (hc : canon e c) (ha : canon e a)
    (hH1 : ∀ x y y', (∀ q, e q = false → wB G x y q = wB G x y' q) → y = y')
    (hH2 : ∀ x, ((univ.filter (fun y : Fin b → ZMod 2 =>
      ∀ q, e q = true → wB G x y q = c q)).card : ℝ) = tN b e) :
    (Dk G good (e, c, a) * patKraus e (jOf e a c) * Venc G).trace =
      (((2 : ℝ) ^ k / 2 ^ ecount e : ℝ) : ℂ) := by
  have hD : ∀ x o, Dk G good (e, c, a) x o = ((dR G e c a x o : ℝ) : ℂ) := by
    intro x o
    simp only [Dk, Matrix.of_apply]
    rw [if_pos ⟨hg, hc, ha⟩]
  have hN : ∀ o z, patKraus e (jOf e a c) o z =
      ((Real.sqrt (1 / 2) ^ ecount e *
        (if (∀ q, e q = true → z q = c q) ∧ o = outE e a z then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    intro o z
    rw [patK_form]
    split_ifs <;> simp
  have hper : ∀ x : Qubits k, ∑ z, (∑ o, dR G e c a x o * (Real.sqrt (1 / 2) ^ ecount e *
      (if (∀ q, e q = true → z q = c q) ∧ o = outE e a z then (1 : ℝ) else 0))) * vR G z x
      = 1 / 2 ^ ecount e := by
    intro x
    have hinj : ∀ y y', outE e a (wB G x y) = outE e a (wB G x y') → y = y' := by
      intro y y' h
      apply hH1 x y y'
      intro q hq
      have h1 := congrFun h q
      simp only [outE, hq] at h1
      simpa using h1
    have hcore := core_sum (wB G x) (outE e a) (fun z => ∀ q, e q = true → z q = c q) hinj
    rw [hH2 x] at hcore
    have hL : ∑ z, (∑ o, dR G e c a x o * (Real.sqrt (1 / 2) ^ ecount e *
        (if (∀ q, e q = true → z q = c q) ∧ o = outE e a z then (1 : ℝ) else 0))) * vR G z x =
        ((Real.sqrt (tN b e))⁻¹ * Real.sqrt (1 / 2) ^ ecount e * (Real.sqrt ((2 : ℝ) ^ b))⁻¹) *
        ∑ o, ∑ z, (∑ y, if (∀ q, e q = true → wB G x y q = c q) ∧ o = outE e a (wB G x y)
            then (1 : ℝ) else 0) *
          (if (∀ q, e q = true → z q = c q) ∧ o = outE e a z then (1 : ℝ) else 0) *
          (∑ y', if z = wB G x y' then (1 : ℝ) else 0) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [dR, vR]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    rw [hL, hcore]
    exact const_eval b (ecount e)
  have htr : (Dk G good (e, c, a) * patKraus e (jOf e a c) * Venc G).trace =
      ((∑ x : Qubits k, ∑ z, (∑ o, dR G e c a x o * (Real.sqrt (1 / 2) ^ ecount e *
        (if (∀ q, e q = true → z q = c q) ∧ o = outE e a z then (1 : ℝ) else 0))) * vR G z x
        : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hD, hN, Venc, Matrix.of_apply]
    push_cast
    rfl
  rw [htr]
  congr 1
  simp_rw [hper]
  rw [Finset.sum_const, Finset.card_univ]
  simp
  ring

-- DECODER-SECTION
-- DK-SECTION
theorem dR_supp {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (e c a : Fin n → Bool)
    (x : Qubits k) (o : Fin n → Bool × Bool) (h : dR G e c a x o ≠ 0) :
    ∃ y, (∀ q, e q = true → wB G x y q = c q) ∧ o = outE e a (wB G x y) := by
  unfold dR at h
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
  refine ⟨y, ?_⟩
  by_contra hc
  exact hy (if_neg hc)

theorem Dk_supp {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (good : (Fin n → Bool) → Prop)
    (e c a : Fin n → Bool) (x : Qubits k) (o : Fin n → Bool × Bool)
    (h : Dk G good (e, c, a) x o ≠ 0) :
    good e ∧ canon e c ∧ canon e a ∧
      ∃ y, (∀ q, e q = true → wB G x y q = c q) ∧ o = outE e a (wB G x y) := by
  classical
  simp only [Dk, Matrix.of_apply] at h
  split_ifs at h with hc
  · refine ⟨hc.1, hc.2.1, hc.2.2, dR_supp G _ _ _ x o ?_⟩
    intro h0; apply h; rw [h0]; simp
  · exact absurd rfl h

theorem outE_det {n : ℕ} {e e' a a' z z' : Fin n → Bool} (ha : canon e a) (ha' : canon e' a')
    (h : outE e a z = outE e' a' z') : e = e' ∧ a = a' ∧ ∀ q, e q = false → z q = z' q := by
  have he : e = e' := by
    funext q
    have h2 := congrArg Prod.snd (congrFun h q)
    cases hq : e q <;> cases hq' : e' q <;> simp [outE, hq, hq'] at h2 ⊢
  subst he
  refine ⟨rfl, ?_, ?_⟩
  · funext q
    have h2 := congrFun h q
    cases hq : e q
    · rw [ha q hq, ha' q hq]
    · simpa [outE, hq] using h2
  · intro q hq
    have h2 := congrFun h q
    simpa [outE, hq] using h2

theorem Dk_orth {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (good : (Fin n → Bool) → Prop)
    (hH1 : ∀ e, good e → ∀ x x' y y',
      (∀ q, e q = false → wB G x y q = wB G x' y' q) → x = x' ∧ y = y')
    (j j' : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) (hne : j ≠ j') :
    Dk G good j * (Dk G good j')ᴴ = 0 := by
  obtain ⟨e, c, a⟩ := j
  obtain ⟨e', c', a'⟩ := j'
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun o _ => ?_
  by_contra hne0
  have h1 : Dk G good (e, c, a) x o ≠ 0 := left_ne_zero_of_mul hne0
  have h2 : Dk G good (e', c', a') x' o ≠ 0 := by
    intro h0; apply hne0; rw [h0, star_zero, mul_zero]
  obtain ⟨hg, hc, ha, y, hy, ho⟩ := Dk_supp G good e c a x o h1
  obtain ⟨-, hc', ha', y', hy', ho'⟩ := Dk_supp G good e' c' a' x' o h2
  obtain ⟨rfl, rfl, hoff⟩ := outE_det ha ha' (ho.symm.trans ho')
  obtain ⟨rfl, rfl⟩ := hH1 e hg x x' y y' hoff
  apply hne
  have hcc : c = c' := by
    funext q
    cases hq : e q
    · rw [hc q hq, hc' q hq]
    · rw [← hy q hq, ← hy' q hq]
  rw [hcc]

theorem Dk_gram {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (good : (Fin n → Bool) → Prop)
    (hH1 : ∀ e, good e → ∀ x x' y y',
      (∀ q, e q = false → wB G x y q = wB G x' y' q) → x = x' ∧ y = y')
    (hH2 : ∀ e, good e → ∀ (c : Fin n → Bool) (x : Qubits k), ((univ.filter (fun y : Fin b → ZMod 2 =>
      ∀ q, e q = true → wB G x y q = c q)).card : ℝ) = tN b e)
    (e c a : Fin n → Bool) (hg : good e) (hc : canon e c) (ha : canon e a) :
    Dk G good (e, c, a) * (Dk G good (e, c, a))ᴴ = 1 := by
  have hD : ∀ x o, Dk G good (e, c, a) x o = ((dR G e c a x o : ℝ) : ℂ) := by
    intro x o
    simp only [Dk, Matrix.of_apply]
    rw [if_pos ⟨hg, hc, ha⟩]
  have htN : 0 < tN b e := by unfold tN; positivity
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hxx : x = x'
  · subst hxx
    rw [if_pos rfl]
    simp only [hD, Complex.star_def, Complex.conj_ofReal]
    have hN : ∀ o, (∑ y : Fin b → ZMod 2, if (∀ q, e q = true → wB G x y q = c q) ∧
        o = outE e a (wB G x y) then (1 : ℝ) else 0) ^ 2 = ∑ y : Fin b → ZMod 2,
        if (∀ q, e q = true → wB G x y q = c q) ∧ o = outE e a (wB G x y) then (1 : ℝ) else 0 := by
      intro o
      rw [Finset.sum_boole]
      have hle : (univ.filter (fun y : Fin b → ZMod 2 => (∀ q, e q = true → wB G x y q = c q) ∧
          o = outE e a (wB G x y))).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro y hy y' hy'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
        exact (hH1 e hg x x y y' (outE_det ha ha (hy.2.symm.trans hy'.2)).2.2).2
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h0
      · rw [h0]; simp
      · rw [h0]; simp
    have hsum : ∑ o, ∑ y : Fin b → ZMod 2, (if (∀ q, e q = true → wB G x y q = c q) ∧
        o = outE e a (wB G x y) then (1 : ℝ) else 0) = tN b e := by
      rw [Finset.sum_comm, ← hH2 e hg c x, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : ∀ q, e q = true → wB G x y q = c q
      · rw [if_pos hy]
        simp only [eq_true hy, true_and]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true, Nat.cast_one]
      · simp [hy]
    have hdR : ∀ o, dR G e c a x o * dR G e c a x o = (tN b e)⁻¹ *
        ∑ y : Fin b → ZMod 2, (if (∀ q, e q = true → wB G x y q = c q) ∧
          o = outE e a (wB G x y) then (1 : ℝ) else 0) := by
      intro o
      simp only [dR]
      rw [show ∀ u v : ℝ, u * v * (u * v) = u ^ 2 * v ^ 2 from fun u v => by ring, hN o, inv_pow,
        Real.sq_sqrt htN.le]
    have hR : ∑ o, dR G e c a x o * dR G e c a x o = 1 := by
      simp_rw [hdR]
      rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ htN.ne']
    exact_mod_cast hR
  · rw [if_neg hxx]
    refine Finset.sum_eq_zero fun o _ => ?_
    by_contra hne0
    have h1 : Dk G good (e, c, a) x o ≠ 0 := left_ne_zero_of_mul hne0
    have h2 : Dk G good (e, c, a) x' o ≠ 0 := by
      intro h0; apply hne0; rw [h0, star_zero, mul_zero]
    obtain ⟨-, -, -, y, -, ho⟩ := Dk_supp G good e c a x o h1
    obtain ⟨-, -, -, y', -, ho'⟩ := Dk_supp G good e c a x' o h2
    exact hxx (hH1 e hg x x' y y' (outE_det ha ha (ho.symm.trans ho')).2.2).1

theorem Dk_pi {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2) (good : (Fin n → Bool) → Prop)
    (hH1 : ∀ e, good e → ∀ x x' y y',
      (∀ q, e q = false → wB G x y q = wB G x' y' q) → x = x' ∧ y = y')
    (hH2 : ∀ e, good e → ∀ (c : Fin n → Bool) (x : Qubits k), ((univ.filter (fun y : Fin b → ZMod 2 =>
      ∀ q, e q = true → wB G x y q = c q)).card : ℝ) = tN b e)
    (j : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) :
    Dk G good j * (Dk G good j)ᴴ * Dk G good j = Dk G good j := by
  classical
  obtain ⟨e, c, a⟩ := j
  by_cases h : good e ∧ canon e c ∧ canon e a
  · rw [Dk_gram G good hH1 hH2 e c a h.1 h.2.1 h.2.2, Matrix.one_mul]
  · have h0 : Dk G good (e, c, a) = 0 := by
      ext x o
      simp only [Dk, Matrix.of_apply, Matrix.zero_apply]
      exact if_neg h
    rw [h0]
    simp

end EC74504552E


namespace EC74504552H

open QAlgorithms
open scoped ComplexConjugate Matrix

theorem isChannel_of_kraus' {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) : IsChannel (krausApply E) := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun i => E (e.symm i), ?_, fun ρ => ?_⟩
  · unfold IsKrausFamily at *
    rw [← hE]
    exact Equiv.sum_comp e.symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp e.symm (fun j => E j * ρ * (E j)ᴴ)).symm

/-- Fidelity of the explicit CSS code: at least the probability of a good erasure pattern. -/
theorem code_fid {k b n : ℕ} (G : Fin (b + k) → Fin n → ZMod 2)
    (good : (Fin n → Bool) → Prop) [DecidablePred good]
    (hinj : ∀ x x' y y', EC74504552E.wB G x y = EC74504552E.wB G x' y' → x = x' ∧ y = y')
    (hH1 : ∀ e, good e → ∀ x x' y y',
      (∀ q, e q = false → EC74504552E.wB G x y q = EC74504552E.wB G x' y' q) → x = x' ∧ y = y')
    (hH2 : ∀ e, good e → ∀ (c : Fin n → Bool) (x : Qubits k),
      ((Finset.univ.filter (fun y : Fin b → ZMod 2 =>
        ∀ q, e q = true → EC74504552E.wB G x y q = c q)).card : ℝ) = EC74504552E.tN b e)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ Enc : Superop (Qubits k) (Qubits n), IsChannel Enc ∧
      ∃ Dec : Superop (Fin n → Bool × Bool) (Qubits k), IsChannel Dec ∧
        ∑ e ∈ Finset.univ.filter good, (∏ q, if e q then p else 1 - p) ≤
          entanglementFidelity (Dec ∘ erasureChannel n p ∘ Enc) := by
  classical
  let D := EC74504552E.Dk G good
  have horth : ∀ j j', j ≠ j' → D j * (D j')ᴴ = 0 := fun j j' h =>
    EC74504552E.Dk_orth G good hH1 j j' h
  have hpi : ∀ j, D j * (D j)ᴴ * D j = D j := fun j => EC74504552E.Dk_pi G good hH1 hH2 j
  have hP := EC74504552D.proj_of_partial D horth hpi
  let B := Sum.elim D (fun u : Fin n → Bool × Bool =>
    Matrix.of fun (r : Qubits k) (s : Fin n → Bool × Bool) =>
      if r = (fun _ => false) then (1 - ∑ j, (D j)ᴴ * D j) u s else 0)
  have hB : IsKrausFamily B := EC74504552D.kraus_complete D (fun _ => false) hP
  let A : Fin 1 → Matrix (Qubits n) (Qubits k) ℂ := fun _ => EC74504552E.Venc G
  have hA : IsKrausFamily A := by
    unfold IsKrausFamily
    rw [Fintype.sum_unique]
    exact EC74504552E.Venc_iso G hinj
  refine ⟨krausApply A, isChannel_of_kraus' A hA, krausApply B, isChannel_of_kraus' B hB, ?_⟩
  let Cs : (Fin n → Bool) → Finset (Fin n → Bool) := fun e =>
    Finset.univ.filter (fun c : Fin n → Bool => ∀ q, e q = false → c q = false)
  let T : (Fin n → Bool) → Finset (Fin 1 × (((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) ⊕
      (Fin n → Bool × Bool)) × (Fin n → Fin 5)) := fun e =>
    ((Cs e) ×ˢ (Cs e)).image
      (fun ca => ((0 : Fin 1), Sum.inl (e, ca.1, ca.2), EC74504552E.jOf e ca.2 ca.1))
  refine EC74504552G.fid_lower p hp0 hp1 A B good T ?_
  intro e he
  have hterm : ∀ ca ∈ (Cs e) ×ˢ (Cs e),
      ‖(B (Sum.inl (e, ca.1, ca.2)) * EC74504552G.patKraus e (EC74504552E.jOf e ca.2 ca.1)
        * A 0).trace‖ ^ 2 = ((2 : ℝ) ^ k / 2 ^ EC74504552E.ecount e) ^ 2 := by
    intro ca hca
    rw [Finset.mem_product] at hca
    have hc : EC74504552E.canon e ca.1 := (Finset.mem_filter.mp hca.1).2
    have ha : EC74504552E.canon e ca.2 := (Finset.mem_filter.mp hca.2).2
    have h := EC74504552E.tr_good G good e ca.1 ca.2 he hc ha
      (fun x y y' h => (hH1 e he x x y y' h).2) (fun x => hH2 e he ca.1 x)
    have hpk : EC74504552G.patKraus e (EC74504552E.jOf e ca.2 ca.1) =
        EC74504552E.patKraus e (EC74504552E.jOf e ca.2 ca.1) := rfl
    rw [hpk]
    change ‖(D (e, ca.1, ca.2) * EC74504552E.patKraus e (EC74504552E.jOf e ca.2 ca.1)
        * EC74504552E.Venc G).trace‖ ^ 2 = _
    rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_image]
  · rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    have hcard : (Cs e).card = 2 ^ EC74504552E.ecount e := EC74504552E.card_canon e
    rw [hcard]
    push_cast
    have h2 : (2 : ℝ) ^ EC74504552E.ecount e ≠ 0 := by positivity
    field_simp
  · intro x _ y _ hxy
    have := congrArg (fun t => t.2.1) hxy
    simp only [Sum.inl.injEq, Prod.mk.injEq, true_and] at this
    exact Prod.ext this.1 this.2

end EC74504552H


namespace EC74504552

open QAlgorithms
open scoped ComplexConjugate Matrix

/-- Any finite normalized Kraus family (any index type) gives a channel. -/
theorem isChannel_of_kraus {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) : IsChannel (krausApply E) := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun i => E (e.symm i), ?_, fun ρ => ?_⟩
  · unfold IsKrausFamily at *
    rw [← hE]
    exact Equiv.sum_comp e.symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp e.symm (fun j => E j * ρ * (E j)ᴴ)).symm

/-- A normalized Kraus map preserves the trace. -/
theorem trace_krausApply {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) (M : Matrix ι ι ℂ) :
    (krausApply E M).trace = M.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  have : ∀ j, (E j * M * (E j)ᴴ).trace = ((E j)ᴴ * E j * M).trace := by
    intro j
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hE
  rw [hE, Matrix.one_mul]

/-- Tensor powers of a normalized Kraus family are normalized. -/
theorem prodKraus_isKraus {n : ℕ} {K α β : Type*} [Fintype K] [Fintype α] [Fintype β]
    [DecidableEq β] (E : K → Matrix α β ℂ) (hE : IsKrausFamily E) :
    IsKrausFamily (fun j : Fin n → K =>
      (Matrix.of fun (y : Fin n → α) (z : Fin n → β) => ∏ q, E (j q) (y q) (z q))) := by
  classical
  unfold IsKrausFamily at *
  have h1 : ∀ a b : β, ∑ k, ∑ x, star (E k x a) * E k x b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hE a) b
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
  ext z z'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  have h2 : ∀ (j : Fin n → K) (y : Fin n → α),
      star (∏ q, E (j q) (y q) (z q)) * ∏ q, E (j q) (y q) (z' q)
        = ∏ q, (star (E (j q) (y q) (z q)) * E (j q) (y q) (z' q)) := by
    intro j y
    rw [star_prod, ← Finset.prod_mul_distrib]
  simp_rw [h2]
  have h3 : ∀ j : Fin n → K, ∑ y : Fin n → α, ∏ q, (star (E (j q) (y q) (z q)) * E (j q) (y q) (z' q))
      = ∏ q, ∑ x, (star (E (j q) x (z q)) * E (j q) x (z' q)) := by
    intro j
    rw [Fintype.prod_sum]
  simp_rw [h3]
  rw [← Fintype.prod_sum (fun q k => ∑ x, (star (E k x (z q)) * E k x (z' q)))]
  simp_rw [h1]
  rw [Finset.prod_boole]
  by_cases h : z = z'
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hall
    exact h (funext fun q => hall q (Finset.mem_univ q))

theorem erasure_isKraus (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsKrausFamily (fun j : Fin n → Fin 5 =>
      (Matrix.of fun (y : Fin n → Bool × Bool) (z : Qubits n) => ∏ q, erasureKraus p (j q) (y q) (z q))) :=
  prodKraus_isKraus (erasureKraus p) (erasureKraus_isKraus hp0 hp1)

theorem erasureChannel_isChannel (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsChannel (erasureChannel n p) :=
  isChannel_of_kraus _ (erasure_isKraus n p hp0 hp1)

theorem trace_erasureChannel (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : Matrix (Qubits n) (Qubits n) ℂ) : (erasureChannel n p M).trace = M.trace :=
  trace_krausApply _ (erasure_isKraus n p hp0 hp1) M

/-- Achievable rates are downward closed. -/
theorem achievable_mono {Out : ℕ → Type*} [∀ n, Fintype (Out n)] [∀ n, DecidableEq (Out n)]
    (Nch : (n : ℕ) → Superop (Qubits n) (Out n)) {R R' : ℝ} (h : IsAchievableQRate Nch R)
    (hR : R' ≤ R) : IsAchievableQRate Nch R' := by
  intro ε hε δ hδ
  obtain ⟨N₀, hN⟩ := h ε hε δ hδ
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨k, hk, rest⟩ := hN n hn
  refine ⟨k, le_trans ?_ hk, rest⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

/-- On zero qubits the entanglement fidelity of a map fixing the single entry is `1`. -/
theorem fid_zero (Φ : Superop (Qubits 0) (Qubits 0))
    (hΦ : ∀ M : Matrix (Qubits 0) (Qubits 0) ℂ, Φ M default default = M default default) :
    entanglementFidelity Φ = 1 := by
  unfold entanglementFidelity idTensorSuperop
  have hd : ∀ x : Qubits 0 × Qubits 0, x = (default, default) := fun x => Subsingleton.elim _ _
  rw [Fintype.sum_eq_single (default, default) (fun a ha => absurd (hd a) ha)]
  rw [Fintype.sum_eq_single (default, default) (fun a ha => absurd (hd a) ha)]
  simp only [Matrix.of_apply, hΦ]
  simp [maxEntangled, pureDensity]

theorem achievable_of_nonpos (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℝ) (hR : R ≤ 0) :
    IsAchievableQRate (fun n => erasureChannel n p) R := by
  classical
  intro ε hε δ hδ
  refine ⟨0, fun n _ => ⟨0, ?_, ?_⟩⟩
  · have : (R - δ) * (n : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg n)
    simpa using this
  · let v : Matrix (Qubits n) (Qubits 0) ℂ :=
      Matrix.of fun y _ => if y = (fun _ => false) then 1 else 0
    let w : (Fin n → Bool × Bool) → Matrix (Qubits 0) (Fin n → Bool × Bool) ℂ :=
      fun y => Matrix.of fun _ y' => if y' = y then 1 else 0
    have hv : IsKrausFamily (fun _ : Fin 1 => v) := by
      unfold IsKrausFamily
      ext a b
      have ha : a = b := Subsingleton.elim _ _
      subst ha
      simp [v, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hw : IsKrausFamily w := by
      unfold IsKrausFamily
      ext a b
      simp [w, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    refine ⟨krausApply (fun _ : Fin 1 => v), isChannel_of_kraus _ hv, krausApply w,
      isChannel_of_kraus _ hw, ?_⟩
    have hfid : entanglementFidelity
        (krausApply w ∘ (fun n => erasureChannel n p) n ∘ krausApply (fun _ : Fin 1 => v)) = 1 := by
      apply fid_zero
      intro M
      have htr : ∀ X : Matrix (Qubits 0) (Qubits 0) ℂ, X default default = X.trace := by
        intro X; rw [Matrix.trace, Fintype.sum_unique, Matrix.diag_apply]
        exact congr (congrArg X (Subsingleton.elim _ _)) (Subsingleton.elim _ _)
      simp only [Function.comp_apply]
      calc _ = (krausApply w (erasureChannel n p (krausApply (fun _ : Fin 1 => v) M))).trace :=
            htr _
        _ = M.trace := by
            rw [trace_krausApply _ hw, trace_erasureChannel n p hp0 hp1, trace_krausApply _ hv]
        _ = M default default := (htr M).symm
    rw [hfid]; linarith

end EC74504552

namespace EC74504552H

open QAlgorithms
open scoped ComplexConjugate Matrix

/-- The trivial zero-qubit code has entanglement fidelity `1`. -/
theorem zero_code (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ Enc : Superop (Qubits 0) (Qubits n), IsChannel Enc ∧
      ∃ Dec : Superop (Fin n → Bool × Bool) (Qubits 0), IsChannel Dec ∧
        entanglementFidelity (Dec ∘ erasureChannel n p ∘ Enc) = 1 := by
  classical
  let v : Matrix (Qubits n) (Qubits 0) ℂ :=
    Matrix.of fun y _ => if y = (fun _ => false) then 1 else 0
  let w : (Fin n → Bool × Bool) → Matrix (Qubits 0) (Fin n → Bool × Bool) ℂ :=
    fun y => Matrix.of fun _ y' => if y' = y then 1 else 0
  have hv : IsKrausFamily (fun _ : Fin 1 => v) := by
    unfold IsKrausFamily
    ext a b
    have ha : a = b := Subsingleton.elim _ _
    subst ha
    simp [v, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hw : IsKrausFamily w := by
    unfold IsKrausFamily
    ext a b
    simp [w, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  refine ⟨krausApply (fun _ : Fin 1 => v), EC74504552.isChannel_of_kraus _ hv, krausApply w,
    EC74504552.isChannel_of_kraus _ hw, ?_⟩
  apply EC74504552.fid_zero
  intro M
  have htr : ∀ X : Matrix (Qubits 0) (Qubits 0) ℂ, X default default = X.trace := by
    intro X; rw [Matrix.trace, Fintype.sum_unique, Matrix.diag_apply]
    exact congr (congrArg X (Subsingleton.elim _ _)) (Subsingleton.elim _ _)
  simp only [Function.comp_apply]
  calc _ = (krausApply w (erasureChannel n p (krausApply (fun _ : Fin 1 => v) M))).trace :=
        htr _
    _ = M.trace := by
        rw [EC74504552.trace_krausApply _ hw, EC74504552.trace_erasureChannel n p hp0 hp1,
          EC74504552.trace_krausApply _ hv]
    _ = M default default := (htr M).symm

/-- Achievability of the rate `1 - 2p` on the erasure channel (random CSS codes). -/
theorem achievability (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    IsAchievableQRate (fun n => erasureChannel n p) (1 - 2 * p) := by
  classical
  have hp1 : p ≤ 1 := by linarith
  intro ε hε δ hδ
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'2 : ε' ≤ ε := min_le_left _ _
  set η := δ / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε' / 3)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨N1, hN1⟩ := exists_nat_gt (3 / (ε' * η ^ 2))
  obtain ⟨N2, hN2⟩ := exists_nat_gt (4 * t / δ)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  have hnN1 : 3 / (ε' * η ^ 2) < n := lt_of_lt_of_le hN1 (by exact_mod_cast hn1)
  have hnN2 : 4 * t / δ < n := lt_of_lt_of_le hN2 (by exact_mod_cast hn2)
  have hδn : 4 * (t : ℝ) < δ * n := by
    rw [div_lt_iff₀ hδ] at hnN2; linarith
  set s0 := ⌊(p + η) * n⌋₊ with hs0
  have hpn : 0 ≤ (p + η) * n := by positivity
  have hs0le : (s0 : ℝ) ≤ (p + η) * n := Nat.floor_le hpn
  have hs0lt : (p + η) * n < s0 + 1 := Nat.lt_floor_add_one _
  by_cases hcase : 2 * s0 + 2 * t ≤ n
  · set k := n - 2 * s0 - 2 * t with hk
    have hkc : (k : ℝ) = n - 2 * s0 - 2 * t := by
      rw [hk]; push_cast [Nat.cast_sub (by omega : 2 * s0 ≤ n),
        Nat.cast_sub (by omega : 2 * t ≤ n - 2 * s0)]; ring
    refine ⟨k, ?_, ?_⟩
    · rw [hkc]; nlinarith
    obtain ⟨G, hG⟩ := EC74504552C.exists_good_G (s0 + t + k) n (s0 + t) s0 (Nat.le_add_right _ _)
      p hp0 hp1
    set good : (Fin n → Bool) → Prop := fun e => ¬ EC74504552C.Bad (s0 + t) G (EC74504552C.Sof e)
      with hgood
    -- the two exponent terms
    have hexp1 : (2 : ℝ) ^ (s0 + t + k) / 2 ^ (n - s0) = 1 / 2 ^ t := by
      have : n - s0 = (s0 + t + k) + t := by omega
      rw [this, pow_add (2 : ℝ) (s0 + t + k) t, div_mul_eq_div_div, div_self (by positivity)]
    have hexp2 : (2 : ℝ) ^ s0 / 2 ^ (s0 + t) = 1 / 2 ^ t := by
      rw [pow_add]; field_simp
    have ht' : 1 / (2 : ℝ) ^ t < ε' / 3 := by rw [← one_div_pow]; exact ht
    -- the tail
    set T' := ∑ e ∈ Finset.univ.filter (fun e : Fin n → Bool => (p + η) * n ≤ EC74504552C.ecount e),
      EC74504552C.pw p e with hT'
    have hsub : ∑ e ∈ Finset.univ.filter (fun e : Fin n → Bool => s0 < EC74504552C.ecount e),
        EC74504552C.pw p e ≤ T' := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        have : (s0 : ℝ) + 1 ≤ EC74504552C.ecount e := by exact_mod_cast he
        linarith
      · intro e _ _; exact EC74504552C.pw_nonneg p hp0 hp1 e
    have htail := EC74504552C.tail_bound n p η hp0 hp1 hη0
    have hT'0 : 0 ≤ T' := Finset.sum_nonneg fun e _ => EC74504552C.pw_nonneg p hp0 hp1 e
    have hT'le : η ^ 2 * n * T' ≤ 1 / 4 := by
      have h1 : (n : ℝ) * p * (1 - p) ≤ n * (1 / 4) := by nlinarith [mul_nonneg hnpos.le (sq_nonneg (p - 1 / 2))]
      have h2 : η ^ 2 * (n : ℝ) ^ 2 * T' = n * (η ^ 2 * n * T') := by ring
      have h3 : n * (η ^ 2 * n * T') ≤ n * (1 / 4) := by linarith
      exact le_of_mul_le_mul_left h3 hnpos
    have hbig : 3 < ε' * η ^ 2 * n := by
      rw [div_lt_iff₀ (by positivity)] at hnN1; linarith
    have hT'lt : T' < ε' / 3 := by
      have hq : 0 < η ^ 2 * (n : ℝ) := by positivity
      by_contra hc
      push_neg at hc
      have : η ^ 2 * n * (ε' / 3) ≤ η ^ 2 * n * T' := mul_le_mul_of_nonneg_left hc hq.le
      nlinarith
    -- the good mass
    have hsplit : ∑ e ∈ Finset.univ.filter good, EC74504552C.pw p e +
        ∑ e, EC74504552C.pw p e * EC74504552C.badI (s0 + t) G e = 1 := by
      rw [Finset.sum_filter, ← Finset.sum_add_distrib, ← EC74504552C.pw_sum_one n p]
      refine Finset.sum_congr rfl fun e _ => ?_
      unfold EC74504552C.badI
      by_cases hb : EC74504552C.Bad (s0 + t) G (EC74504552C.Sof e)
      · have : ¬ good e := fun h => h hb
        rw [if_neg this, if_pos hb]; ring
      · have : good e := hb
        rw [if_pos this, if_neg hb]; ring
    rw [hexp1, hexp2] at hG
    have hmass : 1 - ε' ≤ ∑ e ∈ Finset.univ.filter good, EC74504552C.pw p e := by linarith
    have hex : ∃ e, good e := by
      by_contra hne
      push_neg at hne
      have : Finset.univ.filter good = ∅ := Finset.filter_eq_empty_iff.mpr fun e _ => hne e
      rw [this, Finset.sum_empty] at hmass
      linarith
    obtain ⟨e0, he0⟩ := hex
    have hA : ∀ e, good e → ¬ ∃ m : Fin (s0 + t + k) → ZMod 2, m ≠ 0 ∧
        ∀ j, j ∉ EC74504552C.Sof e → ∑ i, m i * G i j = 0 := fun e he h => he (Or.inl h)
    have hB : ∀ e, good e → ¬ ∃ z : Fin n → ZMod 2, z ≠ 0 ∧ (∀ j, j ∉ EC74504552C.Sof e → z j = 0) ∧
        ∀ i : Fin (s0 + t + k), i.val < s0 + t → ∑ j, z j * G i j = 0 := fun e he h => he (Or.inr h)
    have hSof : ∀ (e : Fin n → Bool) q, q ∉ EC74504552C.Sof e ↔ e q = false := by
      intro e q; simp [EC74504552C.Sof]
    have hinj := EC74504552E.wB_inj G (EC74504552C.Sof e0) (hA e0 he0)
    have hH1 : ∀ e, good e → ∀ x x' y y',
        (∀ q, e q = false → EC74504552E.wB G x y q = EC74504552E.wB G x' y' q) →
          x = x' ∧ y = y' := fun e he x x' y y' h =>
      EC74504552E.inj_off G (EC74504552C.Sof e) (hA e he) fun q hq => h q ((hSof e q).mp hq)
    have hH2 : ∀ e, good e → ∀ (c : Fin n → Bool) (x : Qubits k),
        ((Finset.univ.filter (fun y : Fin (s0 + t) → ZMod 2 =>
          ∀ q, e q = true → EC74504552E.wB G x y q = c q)).card : ℝ) = EC74504552E.tN (s0 + t) e := by
      intro e he c x
      have hfib := EC74504552E.wB_fiber G (EC74504552C.Sof e)
        (fun c' => EC74504552C.fiber_card (Nat.le_add_right (s0 + t) k) G (EC74504552C.Sof e)
          (hB e he) c') x c
      have hfil : Finset.univ.filter (fun y : Fin (s0 + t) → ZMod 2 =>
          ∀ q, e q = true → EC74504552E.wB G x y q = c q) =
          Finset.univ.filter (fun y : Fin (s0 + t) → ZMod 2 =>
          ∀ q ∈ EC74504552C.Sof e, EC74504552E.wB G x y q = c q) := by
        apply Finset.filter_congr
        intro y _
        simp [EC74504552C.Sof]
      rw [hfil, EC74504552E.tN]
      have hcard : (EC74504552C.Sof e).card = EC74504552E.ecount e := rfl
      rw [← hcard, eq_div_iff (by positivity)]
      exact_mod_cast hfib
    obtain ⟨Enc, hEnc, Dec, hDec, hfid⟩ := code_fid G good hinj hH1 hH2 p hp0 hp1
    refine ⟨Enc, hEnc, Dec, hDec, ?_⟩
    have : ∑ e ∈ Finset.univ.filter good, EC74504552C.pw p e =
        ∑ e ∈ Finset.univ.filter good, (∏ q, if e q then p else 1 - p) := rfl
    linarith
  · refine ⟨0, ?_, ?_⟩
    · push_cast
      have : (n : ℝ) < 2 * s0 + 2 * t := by exact_mod_cast (not_le.mp hcase)
      nlinarith
    · obtain ⟨Enc, hEnc, Dec, hDec, hfid⟩ := zero_code n p hp0 hp1
      exact ⟨Enc, hEnc, Dec, hDec, by rw [hfid]; linarith⟩

end EC74504552H

open QAlgorithms in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    IsAchievableQRate (fun n => erasureChannel n p) (1 - 2 * p) := by
  exact EC74504552H.achievability p hp0 hp
