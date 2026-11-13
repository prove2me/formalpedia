-- Prove2me | solution 1 for QAlgorithms.GottesmanThesis.erasure_not_achievable_of_half_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:41:58.336057+00:00
-- url     : https://prove2.me/submissions/8b579292-cab9-499b-8c1d-e28358f8d7b3

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

set_option maxHeartbeats 1000000 in
/-- Abstract monogamy: two decoders acting on the two halves of a broadcast `V` whose marginal
kernels are `N1`, `N2` cannot both have high entanglement fidelity. -/
theorem monogamy_kraus {Rr Z O1 O2 L J1 J2 Ka Kb Kc : Type*} [Fintype Rr] [DecidableEq Rr]
    [Fintype Z] [DecidableEq Z] [Fintype O1] [DecidableEq O1] [Fintype O2] [DecidableEq O2]
    [Fintype L] [Fintype J1] [Fintype J2] [Fintype Ka] [Fintype Kb] [Fintype Kc]
    (A : Ka → Matrix Z Rr ℂ) (hA : IsKrausFamily A)
    (B : Kb → Matrix Rr O1 ℂ) (hB : IsKrausFamily B)
    (C : Kc → Matrix Rr O2 ℂ) (hC : IsKrausFamily C)
    (V : L → Matrix (O1 × O2) Z ℂ) (hV : IsKrausFamily V)
    (N1 : J1 → Matrix O1 Z ℂ) (N2 : J2 → Matrix O2 Z ℂ)
    (h1 : ∀ x1 x2 : O1 × Z, ∑ p : L × O2, V p.1 (x1.1, p.2) x1.2 * conj (V p.1 (x2.1, p.2) x2.2)
        = ∑ j, N1 j x1.1 x1.2 * conj (N1 j x2.1 x2.2))
    (h2 : ∀ x1 x2 : O2 × Z, ∑ p : L × O1, V p.1 (p.2, x1.1) x1.2 * conj (V p.1 (p.2, x2.1) x2.2)
        = ∑ j, N2 j x1.1 x1.2 * conj (N2 j x2.1 x2.2)) :
    (∑ a, ∑ b, ∑ j, ‖(B b * N1 j * A a).trace‖ ^ 2) +
      (∑ a, ∑ c, ∑ j, ‖(C c * N2 j * A a).trace‖ ^ 2)
      ≤ ((Fintype.card Rr : ℝ) + 1) * Fintype.card Rr := by
  classical
  let W : Ka → L → O1 × O2 → Rr → ℂ := fun a l y r => ∑ z, V l y z * A a z r
  let Y : Ka → L → Kb → Rr → Rr → O2 → ℂ := fun a l b r s y2 => ∑ y1, B b s y1 * W a l (y1, y2) r
  let u : Ka → L → Kb → Kc → Rr → Rr → Rr → ℂ := fun a l b c r s t =>
    ∑ y2, C c t y2 * Y a l b r s y2
  have hmono : ∀ a l b c, (∑ t, ‖∑ r, u a l b c r r t‖ ^ 2 + ∑ s, ‖∑ r, u a l b c r s r‖ ^ 2) ≤
      ((Fintype.card Rr : ℝ) + 1) * ∑ r, ∑ s, ∑ t, ‖u a l b c r s t‖ ^ 2 :=
    fun a l b c => monogamy_coord _
  -- T3
  have L3a : ∀ a l b r s, ∑ c, ∑ t, ‖u a l b c r s t‖ ^ 2 = ∑ y2, ‖Y a l b r s y2‖ ^ 2 :=
    fun a l b r s => kraus_collapse C hC _
  have L3b : ∀ a l r y2, ∑ b, ∑ s, ‖Y a l b r s y2‖ ^ 2 = ∑ y1, ‖W a l (y1, y2) r‖ ^ 2 :=
    fun a l r y2 => kraus_collapse B hB _
  have L3c : ∀ a r, ∑ l, ∑ y, ‖W a l y r‖ ^ 2 = ∑ z, ‖A a z r‖ ^ 2 :=
    fun a r => kraus_collapse V hV _
  have L3d : ∀ r, ∑ a, ∑ z, ‖A a z r‖ ^ 2 = 1 := by
    intro r
    have := kraus_collapse A hA (fun y => if y = r then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [this, Finset.sum_eq_single r (fun y _ hy => by simp [hy]) (by simp)]
    simp
  have T3al : ∀ a l, ∑ b, ∑ c, ∑ r, ∑ s, ∑ t, ‖u a l b c r s t‖ ^ 2 =
      ∑ r, ∑ y2, ∑ y1, ‖W a l (y1, y2) r‖ ^ 2 := by
    intro a l
    calc _ = ∑ b, ∑ r, ∑ s, ∑ c, ∑ t, ‖u a l b c r s t‖ ^ 2 :=
          Finset.sum_congr rfl fun b _ => cyc3 _
      _ = ∑ b, ∑ r, ∑ s, ∑ y2, ‖Y a l b r s y2‖ ^ 2 :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun r _ =>
            Finset.sum_congr rfl fun s _ => L3a a l b r s
      _ = ∑ r, ∑ y2, ∑ b, ∑ s, ‖Y a l b r s y2‖ ^ 2 := perm4 _
      _ = _ := Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun y2 _ => L3b a l r y2
  have T3 : ∑ a, ∑ l, ∑ b, ∑ c, ∑ r, ∑ s, ∑ t, ‖u a l b c r s t‖ ^ 2 = Fintype.card Rr := by
    calc _ = ∑ a, ∑ l, ∑ r, ∑ y2, ∑ y1, ‖W a l (y1, y2) r‖ ^ 2 :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => T3al a l
      _ = ∑ a, ∑ r, ∑ l, ∑ y : O1 × O2, ‖W a l y r‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = ∑ a, ∑ r, ∑ z, ‖A a z r‖ ^ 2 :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => L3c a r
      _ = ∑ r, ∑ a, ∑ z, ‖A a z r‖ ^ 2 := Finset.sum_comm
      _ = _ := by simp [L3d]
  -- T1
  let M1 : Ka → Kb → O1 × Z → ℂ := fun a b x => ∑ r, B b r x.1 * A a x.2 r
  have X1 : ∀ a l b y2, ∑ r, Y a l b r r y2 = ∑ x : O1 × Z, M1 a b x * V l (x.1, y2) x.2 := by
    intro a l b y2
    simp only [Y, W, M1, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    rw [cyc3]
    refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  have T1 : ∑ a, ∑ l, ∑ b, ∑ c, ∑ t, ‖∑ r, u a l b c r r t‖ ^ 2 =
      ∑ a, ∑ b, ∑ j, ‖(B b * N1 j * A a).trace‖ ^ 2 := by
    have e1 : ∀ a l b c t, ∑ r, u a l b c r r t = ∑ y2, C c t y2 * ∑ r, Y a l b r r y2 := by
      intro a l b c t
      simp only [u]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    calc _ = ∑ a, ∑ l, ∑ b, ∑ y2, ‖∑ r, Y a l b r r y2‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
            Finset.sum_congr rfl fun b _ => ?_
          simp_rw [e1]
          exact kraus_collapse C hC _
      _ = ∑ a, ∑ b, ∑ p : L × O2, ‖∑ x : O1 × Z, M1 a b x * V p.1 (x.1, p.2) x.2‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Fintype.sum_prod_type]
          simp_rw [X1]
      _ = ∑ a, ∑ b, ∑ j, ‖∑ x : O1 × Z, M1 a b x * N1 j x.1 x.2‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          exact transfer1 (M1 a b) V N1 h1
      _ = _ := by simp only [M1, trace_BNA]
  -- T2
  let M2 : Ka → Kc → O2 × Z → ℂ := fun a c x => ∑ r, C c r x.1 * A a x.2 r
  let X2 : Ka → L → Kc → O1 → ℂ := fun a l c y1 => ∑ r, ∑ y2, C c r y2 * W a l (y1, y2) r
  have e2 : ∀ a l b c s, ∑ r, u a l b c r s r = ∑ y1, B b s y1 * X2 a l c y1 := by
    intro a l b c s
    simp only [u, Y, X2, Finset.mul_sum]
    rw [← cyc3]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun y2 _ =>
      Finset.sum_congr rfl fun y1 _ => ?_
    ring
  have X2e : ∀ a l c y1, X2 a l c y1 = ∑ x : O2 × Z, M2 a c x * V l (y1, x.1) x.2 := by
    intro a l c y1
    simp only [X2, W, M2, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    rw [cyc3]
    refine Finset.sum_congr rfl fun y2 _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  have T2 : ∑ a, ∑ l, ∑ b, ∑ c, ∑ s, ‖∑ r, u a l b c r s r‖ ^ 2 =
      ∑ a, ∑ c, ∑ j, ‖(C c * N2 j * A a).trace‖ ^ 2 := by
    calc _ = ∑ a, ∑ l, ∑ c, ∑ y1, ‖X2 a l c y1‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp_rw [e2]
          exact kraus_collapse B hB _
      _ = ∑ a, ∑ c, ∑ p : L × O1, ‖∑ x : O2 × Z, M2 a c x * V p.1 (p.2, x.1) x.2‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Fintype.sum_prod_type]
          simp_rw [X2e]
      _ = ∑ a, ∑ c, ∑ j, ‖∑ x : O2 × Z, M2 a c x * N2 j x.1 x.2‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
          exact transfer2 (M2 a c) V N2 h2
      _ = _ := by simp only [M2, trace_BNA]
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) =>
    Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hmono a l b c
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [T1, T2, T3] at hsum
  exact hsum

/-- Marginal of a product weight on `Fin 3`-valued patterns under a recolouring `g`. -/
theorem marginal3 {n : ℕ} (c : Fin 3 → ℝ) (g : Fin 3 → Bool) (f : (Fin n → Bool) → ℝ) :
    ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * f (fun q => g (τ q)) =
      ∑ e : Fin n → Bool, (∏ q, ∑ i, if g i = e q then c i else 0) * f e := by
  classical
  simp_rw [Fintype.prod_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_eq_single (fun q => g (τ q))]
  · congr 1
    exact Finset.prod_congr rfl fun q _ => by simp
  · intro e _ he
    have : ∃ q, g (τ q) ≠ e q := by
      by_contra h
      push_neg at h
      exact he (funext fun q => (h q).symm)
    obtain ⟨q, hq⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq]), zero_mul]
  · simp

/-- Coupling for `p ≥ 1/2`: two `Bern(p)^n` erasure patterns whose unerased sets are disjoint.
If `f e + f e' ≤ C` whenever every position is erased in `e` or in `e'`, then `2 E[f] ≤ C`. -/
theorem coupling_half {n : ℕ} (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (f : (Fin n → Bool) → ℝ)
    (C : ℝ) (hf : ∀ e e' : Fin n → Bool, (∀ q, e q = true ∨ e' q = true) → f e + f e' ≤ C) :
    2 * ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) * f e ≤ C := by
  classical
  let c : Fin 3 → ℝ := ![1 - p, 1 - p, 2 * p - 1]
  let g1 : Fin 3 → Bool := ![true, false, true]
  let g2 : Fin 3 → Bool := ![false, true, true]
  have hw1 : ∀ b : Bool, (∑ i, if g1 i = b then c i else 0) = if b then p else 1 - p := by
    intro b; cases b <;> simp [Fin.sum_univ_three, c, g1] <;> ring
  have hw2 : ∀ b : Bool, (∑ i, if g2 i = b then c i else 0) = if b then p else 1 - p := by
    intro b; cases b <;> simp [Fin.sum_univ_three, c, g2] <;> ring
  have m1 := marginal3 c g1 f
  have m2 := marginal3 c g2 f
  simp only [hw1] at m1
  simp only [hw2] at m2
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i; fin_cases i <;> simp [c] <;> linarith
  have htot : ∑ τ : Fin n → Fin 3, ∏ q, c (τ q) = 1 := by
    rw [show (∑ τ : Fin n → Fin 3, ∏ q, c (τ q)) = ∏ _q : Fin n, ∑ i, c i from
      (Fintype.prod_sum (fun _ i => c i)).symm]
    have : ∑ i, c i = 1 := by simp [Fin.sum_univ_three, c]; ring
    simp [this]
  calc 2 * ∑ e, (∏ q, if e q then p else 1 - p) * f e
      = ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * (f (fun q => g1 (τ q)) + f (fun q => g2 (τ q))) := by
        rw [two_mul]
        nth_rewrite 1 [← m1]
        rw [← m2, ← Finset.sum_add_distrib]
        simp_rw [mul_add]
    _ ≤ ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * C := by
        refine Finset.sum_le_sum fun τ _ =>
          mul_le_mul_of_nonneg_left (hf _ _ ?_) (Finset.prod_nonneg fun q _ => hc0 _)
        intro q
        generalize τ q = i
        fin_cases i <;> simp [g1, g2]
    _ = C := by rw [← Finset.sum_mul, htot, one_mul]

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

theorem prod_sum2 {n : ℕ} {K A : Type*} [Fintype K] [Fintype A] (f : Fin n → K → A → ℂ) :
    ∑ p : (Fin n → K) × (Fin n → A), ∏ q, f q (p.1 q) (p.2 q) = ∏ q, ∑ k, ∑ a, f q k a := by
  rw [Fintype.sum_prod_type]
  have h : ∀ l : Fin n → K, ∑ x : Fin n → A, ∏ q, f q (l q) (x q) = ∏ q, ∑ a, f q (l q) a :=
    fun l => (Fintype.prod_sum (fun (q : Fin n) (a : A) => f q (l q) a)).symm
  simp_rw [h]
  exact (Fintype.prod_sum (fun (q : Fin n) (k : K) => ∑ a, f q k a)).symm

noncomputable def sAmp : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem sAmp_conj : conj sAmp = sAmp := Complex.conj_ofReal _

theorem conj_two' : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem sAmp_sq : sAmp * sAmp = 1 / 2 := by
  unfold sAmp
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Per-qubit broadcast: erased-in-1 / erased-in-2 / erased-in-both. -/
noncomputable def Vq (e1 e2 : Bool) (l : Bool × Bool × Bool) (o1 o2 : Bool × Bool) (z : Bool) : ℂ :=
  if e1 = true ∧ e2 = false then
    (if l.2 = (false, false) ∧ o1 = (l.1, true) ∧ o2 = (z, false) then sAmp else 0)
  else if e1 = false ∧ e2 = true then
    (if l.2 = (false, false) ∧ o1 = (z, false) ∧ o2 = (l.1, true) then sAmp else 0)
  else (if o1 = (l.1, true) ∧ o2 = (l.2.1, true) ∧ z = l.2.2 then 1 / 2 else 0)

theorem vq_marg1 (e1 e2 : Bool) (h : e1 = true ∨ e2 = true) (y1 y2 : Bool × Bool) (z1 z2 : Bool) :
    ∑ k : Bool × Bool × Bool, ∑ a : Bool × Bool, Vq e1 e2 k y1 a z1 * conj (Vq e1 e2 k y2 a z2) =
      erasureKernel (if e1 then 1 else 0) y1 y2 z1 z2 := by
  rcases y1 with ⟨a1, b1⟩
  rcases y2 with ⟨a2, b2⟩
  cases e1 <;> cases e2
  · exfalso; revert h; decide
  all_goals
    cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases z1 <;> cases z2 <;>
      simp [Vq, erasureKernel, Fintype.sum_prod_type, sAmp_conj, sAmp_sq, conj_two'] <;> norm_num

theorem vq_marg2 (e1 e2 : Bool) (h : e1 = true ∨ e2 = true) (y1 y2 : Bool × Bool) (z1 z2 : Bool) :
    ∑ k : Bool × Bool × Bool, ∑ a : Bool × Bool, Vq e1 e2 k a y1 z1 * conj (Vq e1 e2 k a y2 z2) =
      erasureKernel (if e2 then 1 else 0) y1 y2 z1 z2 := by
  rcases y1 with ⟨a1, b1⟩
  rcases y2 with ⟨a2, b2⟩
  cases e1 <;> cases e2
  · exfalso; revert h; decide
  all_goals
    cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases z1 <;> cases z2 <;>
      simp [Vq, erasureKernel, Fintype.sum_prod_type, sAmp_conj, sAmp_sq, conj_two'] <;> norm_num

noncomputable def bc (n : ℕ) (e e' : Fin n → Bool) (l : Fin n → Bool × Bool × Bool) :
    Matrix ((Fin n → Bool × Bool) × (Fin n → Bool × Bool)) (Qubits n) ℂ :=
  Matrix.of fun o z => ∏ q, Vq (e q) (e' q) (l q) (o.1 q) (o.2 q) (z q)

theorem bc_marg1 (n : ℕ) (e e' : Fin n → Bool) (hc : ∀ q, e q = true ∨ e' q = true)
    (x1 x2 : (Fin n → Bool × Bool) × Qubits n) :
    ∑ p : (Fin n → Bool × Bool × Bool) × (Fin n → Bool × Bool),
      bc n e e' p.1 (x1.1, p.2) x1.2 * conj (bc n e e' p.1 (x2.1, p.2) x2.2) =
    ∏ q, erasureKernel (if e q then 1 else 0) (x1.1 q) (x2.1 q) (x1.2 q) (x2.2 q) := by
  have hs := prod_sum2 (fun (q : Fin n) (k : Bool × Bool × Bool) (a : Bool × Bool) =>
    Vq (e q) (e' q) k (x1.1 q) a (x1.2 q) * conj (Vq (e q) (e' q) k (x2.1 q) a (x2.2 q)))
  beta_reduce at hs
  refine Eq.trans ?_ (hs.trans (Finset.prod_congr rfl fun q _ => vq_marg1 _ _ (hc q) _ _ _ _))
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [bc, Matrix.of_apply, map_prod, ← Finset.prod_mul_distrib]

theorem bc_marg2 (n : ℕ) (e e' : Fin n → Bool) (hc : ∀ q, e q = true ∨ e' q = true)
    (x1 x2 : (Fin n → Bool × Bool) × Qubits n) :
    ∑ p : (Fin n → Bool × Bool × Bool) × (Fin n → Bool × Bool),
      bc n e e' p.1 (p.2, x1.1) x1.2 * conj (bc n e e' p.1 (p.2, x2.1) x2.2) =
    ∏ q, erasureKernel (if e' q then 1 else 0) (x1.1 q) (x2.1 q) (x1.2 q) (x2.2 q) := by
  have hs := prod_sum2 (fun (q : Fin n) (k : Bool × Bool × Bool) (a : Bool × Bool) =>
    Vq (e q) (e' q) k a (x1.1 q) (x1.2 q) * conj (Vq (e q) (e' q) k a (x2.1 q) (x2.2 q)))
  beta_reduce at hs
  refine Eq.trans ?_ (hs.trans (Finset.prod_congr rfl fun q _ => vq_marg2 _ _ (hc q) _ _ _ _))
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [bc, Matrix.of_apply, map_prod, ← Finset.prod_mul_distrib]

theorem kraus_of_kernel {O1 O2 Z L : Type*} [Fintype O1] [Fintype O2] [Fintype Z] [DecidableEq Z]
    [Fintype L] (V : L → Matrix (O1 × O2) Z ℂ) (K : O1 → O1 → Z → Z → ℂ)
    (h1 : ∀ x1 x2 : O1 × Z, ∑ p : L × O2, V p.1 (x1.1, p.2) x1.2 * conj (V p.1 (x2.1, p.2) x2.2)
        = K x1.1 x2.1 x1.2 x2.2)
    (hK : ∀ z z', ∑ o, K o o z z' = if z = z' then 1 else 0) : IsKrausFamily V := by
  unfold IsKrausFamily
  ext z z'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have step : ∀ l, ∑ o : O1 × O2, star (V l o z) * V l o z' =
      ∑ o1, ∑ o2, V l (o1, o2) z' * conj (V l (o1, o2) z) := by
    intro l
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o1 _ => Finset.sum_congr rfl fun o2 _ => ?_
    rw [mul_comm]; rfl
  simp_rw [step]
  rw [Finset.sum_comm]
  have h2 : ∀ o1, ∑ l, ∑ o2, V l (o1, o2) z' * conj (V l (o1, o2) z) = K o1 o1 z' z := fun o1 => by
    rw [← h1 (o1, z') (o1, z)]
    exact (Fintype.sum_prod_type (fun p : L × O2 => V p.1 (o1, p.2) z' * conj (V p.1 (o1, p.2) z))).symm
  simp_rw [h2]
  rw [hK]
  by_cases h : z = z'
  · subst h; simp
  · simp [h, @eq_comm _ z' z]

theorem ker_diag (r : ℝ) (z z' : Bool) :
    ∑ o : Bool × Bool, erasureKernel r o o z z' = if z = z' then 1 else 0 := by
  cases z <;> cases z' <;> simp [erasureKernel, Fintype.sum_prod_type] <;> push_cast <;> ring

theorem patK_diag (n : ℕ) (r : Fin n → ℝ) (z z' : Qubits n) :
    ∑ y : Fin n → Bool × Bool, ∏ q, erasureKernel (r q) (y q) (y q) (z q) (z' q) =
      if z = z' then 1 else 0 := by
  refine Eq.trans (Fintype.prod_sum
    (fun (q : Fin n) (o : Bool × Bool) => erasureKernel (r q) o o (z q) (z' q))).symm ?_
  simp_rw [ker_diag]
  rw [Finset.prod_boole]
  by_cases hz : z = z'
  · subst hz; simp
  · rw [if_neg hz, if_neg]
    intro hall
    exact hz (funext fun q => hall q (Finset.mem_univ q))

theorem bc_kraus (n : ℕ) (e e' : Fin n → Bool) (hc : ∀ q, e q = true ∨ e' q = true) :
    IsKrausFamily (bc n e e') :=
  kraus_of_kernel (bc n e e')
    (fun (y y' : Fin n → Bool × Bool) (z z' : Qubits n) =>
      ∏ q, erasureKernel (if e q then 1 else 0) (y q) (y' q) (z q) (z' q))
    (bc_marg1 n e e' hc) (fun z z' => patK_diag n _ z z')

theorem pat_kernel {n : ℕ} (e : Fin n → Bool) (x1 x2 : (Fin n → Bool × Bool) × Qubits n) :
    ∑ j : Fin n → Fin 5, patKraus e j x1.1 x1.2 * conj (patKraus e j x2.1 x2.2) =
      ∏ q, erasureKernel (if e q then 1 else 0) (x1.1 q) (x2.1 q) (x1.2 q) (x2.2 q) := by
  have hk2 := prod_kernel (fun (q : Fin n) => erasureKraus (if e q then 1 else 0)) x1.1 x2.1 x1.2 x2.2
  beta_reduce at hk2
  have hpe : ∀ q, (0 : ℝ) ≤ (if e q then 1 else 0) ∧ (if e q then (1 : ℝ) else 0) ≤ 1 := by
    intro q; split_ifs <;> norm_num
  exact hk2.trans (Finset.prod_congr rfl fun q _ => erasure_kernel_conj _ (hpe q).1 (hpe q).2 _ _ _ _)

theorem fid_pattern {k n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Enc : Superop (Qubits k) (Qubits n)) (hE : IsChannel Enc)
    (Dec : Superop (Fin n → Bool × Bool) (Qubits k)) (hD : IsChannel Dec) :
    ∃ (m m' : ℕ) (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ)
      (B : Fin m' → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ),
      IsKrausFamily A ∧ IsKrausFamily B ∧
      entanglementFidelity (Dec ∘ erasureChannel n p ∘ Enc) =
        (((2 : ℝ) ^ k)⁻¹) ^ 2 * ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) *
          ∑ a, ∑ b, ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2 := by
  obtain ⟨m, m', A, B, hA, hB, hF⟩ := fid_comp Enc hE Dec hD (erasureChannel n p)
    (fun j : Fin n → Fin 5 => Matrix.of fun (y : Fin n → Bool × Bool) (z : Qubits n) =>
      ∏ q, erasureKraus p (j q) (y q) (z q)) (fun ρ => rfl)
  refine ⟨m, m', A, B, hA, hB, ?_⟩
  rw [hF]
  congr 1
  have hL : ∀ (a : Fin m) (b : Fin m'),
      ∑ j : Fin n → Fin 5, ‖(B b * (Matrix.of fun (y : Fin n → Bool × Bool) (z : Qubits n) =>
        ∏ q, erasureKraus p (j q) (y q) (z q)) * A a).trace‖ ^ 2 =
      ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) *
        ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2 := by
    intro a b
    simp only [trace_BNA, Matrix.of_apply]
    exact erasure_split p hp0 hp1 _
  have hperm : ∀ F : Fin m' → (Fin n → Fin 5) → Fin m → ℝ,
      ∑ b, ∑ j, ∑ a, F b j a = ∑ a, ∑ b, ∑ j, F b j a :=
    fun F => (cyc3 F).trans (cyc3 fun (j : Fin n → Fin 5) (a : Fin m) (b : Fin m') => F b j a)
  refine (hperm _).trans ?_
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hL a b).trans ?_
  simp_rw [Finset.mul_sum]
  exact (cyc3 _).trans (cyc3 _)

theorem card_qubits (k : ℕ) : (Fintype.card (Qubits k) : ℝ) = 2 ^ k := by
  simp [Qubits, Fintype.card_fun, Fintype.card_bool]

theorem erasure_not_achievable_of_half_le (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (R : ℝ) (hR : 0 < R) :
    ¬ IsAchievableQRate (fun n => erasureChannel n p) R := by
  intro h
  obtain ⟨N0, hN0⟩ := h (1 / 8) (by norm_num) (R / 2) (by linarith)
  obtain ⟨k, hk, Enc, hE, Dec, hD, hF⟩ := hN0 (max N0 1) (le_max_left _ _)
  have hn1 : (1 : ℝ) ≤ ((max N0 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N0 1
  have hkpos : (0 : ℝ) < k := by nlinarith
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [h0] at hkpos; simp at hkpos)
  have hD2 : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  obtain ⟨m, m', A, B, hA, hB, hfid⟩ := fid_pattern p (by linarith) hp1 Enc hE Dec hD
  have hpair : ∀ e e' : Fin (max N0 1) → Bool, (∀ q, e q = true ∨ e' q = true) →
      (∑ a, ∑ b, ∑ j : Fin (max N0 1) → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2) +
      (∑ a, ∑ b, ∑ j : Fin (max N0 1) → Fin 5, ‖(B b * patKraus e' j * A a).trace‖ ^ 2) ≤
      ((Fintype.card (Qubits k) : ℝ) + 1) * Fintype.card (Qubits k) := by
    intro e e' hc
    exact monogamy_kraus A hA B hB B hB (bc (max N0 1) e e') (bc_kraus (max N0 1) e e' hc)
      (patKraus e) (patKraus e')
      (fun x1 x2 => (bc_marg1 (max N0 1) e e' hc x1 x2).trans (pat_kernel e x1 x2).symm)
      (fun x1 x2 => (bc_marg2 (max N0 1) e e' hc x1 x2).trans (pat_kernel e' x1 x2).symm)
  have hcoup := coupling_half p hp hp1
    (fun e : Fin (max N0 1) → Bool =>
      ∑ a, ∑ b, ∑ j : Fin (max N0 1) → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2) _ hpair
  beta_reduce at hcoup hF
  rw [card_qubits] at hcoup
  rw [hfid] at hF
  have key : ∀ S : ℝ, ((2 : ℝ) ^ k)⁻¹ ^ 2 * S = S / ((2 : ℝ) ^ k) ^ 2 := fun S => by
    field_simp
  rw [key, le_div_iff₀ (by positivity)] at hF
  have hDpos : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hD2 hDpos.le]

end EC74504552G

open QAlgorithms in
theorem solution (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (R : ℝ) (hR : 0 < R) :
    ¬ IsAchievableQRate (fun n => erasureChannel n p) R := by
  exact EC74504552G.erasure_not_achievable_of_half_le p hp hp1 R hR
