-- Prove2me | solution 1 for QAlgorithms.GottesmanThesis.erasure_rate_le_one_sub_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:41:58.39919+00:00
-- url     : https://prove2.me/submissions/4895aac8-b0ec-43f8-b5d3-c56beb454c90

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace EC74504552F

open QAlgorithms
open scoped ComplexConjugate Matrix

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

end EC74504552G


namespace EC74504552M
open scoped ComplexConjugate

theorem nsq (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem cs_c {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ i ∈ s, f i * g i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * (∑ i ∈ s, ‖g i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  calc _ ≤ (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _

section perm
variable {A B C D E M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [AddCommMonoid M]

theorem push3 (h : A → B → C → M) :
    ∑ a, ∑ b, ∑ c, h a b c = ∑ b, ∑ c, ∑ a, h a b c :=
  Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

theorem push4 (h : A → B → C → D → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ b, ∑ c, ∑ d, ∑ a, h a b c d :=
  Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun b _ => push3 (fun a c d => h a b c d))

theorem push5 (h : A → B → C → D → E → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, h a b c d e = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, h a b c d e :=
  Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun b _ => push4 (fun a c d e => h a b c d e))

theorem flat3 (h : A → B → C → M) :
    ∑ a, ∑ b, ∑ c, h a b c = ∑ p : A × B × C, h p.1 p.2.1 p.2.2 := by
  simp only [Fintype.sum_prod_type]

theorem flat4 (h : A → B → C → D → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ p : A × B × C × D, h p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp only [Fintype.sum_prod_type]

end perm

theorem cs3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (f g : A → B → C → ℂ) :
    ‖∑ a, ∑ b, ∑ c, f a b c * g a b c‖ ^ 2 ≤
      (∑ a, ∑ b, ∑ c, ‖f a b c‖ ^ 2) * (∑ a, ∑ b, ∑ c, ‖g a b c‖ ^ 2) := by
  have h := cs_c (Finset.univ : Finset (A × B × C)) (fun p => f p.1 p.2.1 p.2.2)
    (fun p => g p.1 p.2.1 p.2.2)
  simpa only [Fintype.sum_prod_type] using h

theorem cs4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f g : A → B → C → D → ℂ) :
    ‖∑ a, ∑ b, ∑ c, ∑ d, f a b c d * g a b c d‖ ^ 2 ≤
      (∑ a, ∑ b, ∑ c, ∑ d, ‖f a b c d‖ ^ 2) * (∑ a, ∑ b, ∑ c, ∑ d, ‖g a b c d‖ ^ 2) := by
  have h := cs_c (Finset.univ : Finset (A × B × C × D)) (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p => g p.1 p.2.1 p.2.2.1 p.2.2.2)
  simpa only [Fintype.sum_prod_type] using h

theorem sum_ite_sq {OA : Type*} [Fintype OA] [DecidableEq OA] (a : OA) (z : ℂ) :
    ∑ a', ‖(if a' = a then z else 0)‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ a) h)]
  simp

/-- The transpose of a contraction is a contraction. -/
theorem tr_contr {P Q : Type*} [Fintype P] [Fintype Q] (T : Q → P → ℂ)
    (hT : ∀ u : P → ℂ, ∑ q, ‖∑ p, T q p * u p‖ ^ 2 ≤ ∑ p, ‖u p‖ ^ 2) (v : Q → ℂ) :
    ∑ p, ‖∑ q, T q p * v q‖ ^ 2 ≤ ∑ q, ‖v q‖ ^ 2 := by
  have hid : (((∑ p, ‖∑ q, T q p * v q‖ ^ 2 : ℝ)) : ℂ) =
      ∑ q, v q * ∑ p, T q p * conj (∑ q', T q' p * v q') := by
    rw [Complex.ofReal_sum]
    simp_rw [nsq, Finset.sum_mul, Finset.mul_sum]
    exact Eq.trans Finset.sum_comm
      (Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring)
  have hS0 : 0 ≤ ∑ p, ‖∑ q, T q p * v q‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV0 : 0 ≤ ∑ q, ‖v q‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∑ p, ‖∑ q, T q p * v q‖ ^ 2 =
      ‖∑ q, v q * ∑ p, T q p * conj (∑ q', T q' p * v q')‖ := by
    rw [← hid, Complex.norm_of_nonneg hS0]
  have h2 := cs_c Finset.univ v (fun q => ∑ p, T q p * conj (∑ q', T q' p * v q'))
  have h3 := hT (fun p => conj (∑ q', T q' p * v q'))
  simp only [RCLike.norm_conj] at h3
  rw [← h1] at h2
  have h4 := mul_le_mul_of_nonneg_left h3 hV0
  nlinarith

/-- Diagonal bound: `Σ ‖Σ_j K v‖² ≤ d Σ ‖v‖²`. -/
theorem side_diag {Rr X Y OA J : Type*} [Fintype Rr] [Fintype X] [Fintype Y] [Fintype OA]
    [Fintype J] (K : J → Rr → X → OA → ℂ)
    (hK : ∀ u : X → OA → ℂ, ∑ r, ∑ j, ‖∑ x, ∑ a, K j r x a * u x a‖ ^ 2 ≤ ∑ x, ∑ a, ‖u x a‖ ^ 2)
    (v : J → Y → ℂ) :
    ∑ r, ∑ x, ∑ y, ∑ a, ‖∑ j, K j r x a * v j y‖ ^ 2 ≤
      (Fintype.card Rr : ℝ) * ∑ j, ∑ y, ‖v j y‖ ^ 2 := by
  have hr : ∀ r y, ∑ x, ∑ a, ‖∑ j, K j r x a * v j y‖ ^ 2 ≤ ∑ j, ‖v j y‖ ^ 2 := by
    intro r y
    have ht := tr_contr (P := X × OA) (Q := J) (fun j p => K j r p.1 p.2) ?_ (fun j => v j y)
    · simpa only [Fintype.sum_prod_type] using ht
    · intro u
      have h1 := hK (fun x a => u (x, a))
      have h2 : ∑ j, ‖∑ x, ∑ a, K j r x a * u (x, a)‖ ^ 2 ≤
          ∑ r', ∑ j, ‖∑ x, ∑ a, K j r' x a * u (x, a)‖ ^ 2 :=
        Finset.single_le_sum (f := fun r' => ∑ j, ‖∑ x, ∑ a, K j r' x a * u (x, a)‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ r)
      simp only [Fintype.sum_prod_type]
      exact h2.trans h1
  calc ∑ r, ∑ x, ∑ y, ∑ a, ‖∑ j, K j r x a * v j y‖ ^ 2
      = ∑ r, ∑ y, ∑ x, ∑ a, ‖∑ j, K j r x a * v j y‖ ^ 2 :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ _r : Rr, ∑ y, ∑ j, ‖v j y‖ ^ 2 :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun y _ => hr r y
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]

/-- `Σ ‖α‖² = ⟨ψ, ξ₁⟩`. -/
theorem side_id {Rr X Y OA J : Type*} [Fintype Rr] [Fintype X] [Fintype Y] [Fintype OA]
    [Fintype J] (K : J → Rr → X → OA → ℂ) (ψ : Rr → X → Y → OA → ℂ) :
    (((∑ j, ∑ y, ‖∑ r, ∑ x, ∑ a, K j r x a * ψ r x y a‖ ^ 2 : ℝ)) : ℂ) =
      ∑ r, ∑ x, ∑ y, ∑ a, ψ r x y a *
        ∑ j, K j r x a * conj (∑ r', ∑ x', ∑ a', K j r' x' a' * ψ r' x' y a') := by
  simp_rw [Complex.ofReal_sum, nsq, Finset.sum_mul]
  refine ((push5 _).trans (push3 _)).trans ?_
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Cross term for a fixed shared value `a`. -/
theorem cross {Rr X Y OA J M : Type*} [Fintype Rr] [Fintype X] [Fintype Y] [Fintype OA]
    [DecidableEq OA] [Fintype J] [Fintype M]
    (K : J → Rr → X → OA → ℂ) (L : M → Rr → Y → OA → ℂ)
    (hK : ∀ u : X → OA → ℂ, ∑ r, ∑ j, ‖∑ x, ∑ a, K j r x a * u x a‖ ^ 2 ≤ ∑ x, ∑ a, ‖u x a‖ ^ 2)
    (hL : ∀ u : Y → OA → ℂ, ∑ r, ∑ m, ‖∑ y, ∑ a, L m r y a * u y a‖ ^ 2 ≤ ∑ y, ∑ a, ‖u y a‖ ^ 2)
    (α : J → Y → ℂ) (β : M → X → ℂ) (a : OA) :
    ‖∑ r, ∑ x, ∑ y, (∑ j, K j r x a * conj (α j y)) * conj (∑ m, L m r y a * conj (β m x))‖ ≤
      ((∑ j, ∑ y, ‖α j y‖ ^ 2) + (∑ m, ∑ x, ‖β m x‖ ^ 2)) / 2 := by
  have hre : ∑ r, ∑ x, ∑ y, (∑ j, K j r x a * conj (α j y)) * conj (∑ m, L m r y a * conj (β m x)) =
      ∑ r, ∑ j, ∑ m, (∑ x, K j r x a * β m x) * conj (∑ y, L m r y a * α j y) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [map_sum, Finset.sum_mul_sum]
    refine ((push4 _).trans (push4 _)).trans ?_
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        rw [map_mul, map_mul, Complex.conj_conj]; ring
  rw [hre]
  have hcs := cs3 (fun r j m => ∑ x, K j r x a * β m x) (fun r j m => conj (∑ y, L m r y a * α j y))
  simp only [RCLike.norm_conj] at hcs
  have hb : ∑ r, ∑ j, ∑ m, ‖∑ x, K j r x a * β m x‖ ^ 2 ≤ ∑ m, ∑ x, ‖β m x‖ ^ 2 := by
    rw [← push3]
    refine Finset.sum_le_sum fun m _ => ?_
    have h := hK (fun x a' => if a' = a then β m x else 0)
    simpa [mul_ite, Finset.sum_ite_eq', sum_ite_sq] using h
  have hc : ∑ r, ∑ j, ∑ m, ‖∑ y, L m r y a * α j y‖ ^ 2 ≤ ∑ j, ∑ y, ‖α j y‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := hL (fun y a' => if a' = a then α j y else 0)
    simpa [mul_ite, Finset.sum_ite_eq', sum_ite_sq] using h
  have hF1 : 0 ≤ ∑ j, ∑ y, ‖α j y‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF2 : 0 ≤ ∑ m, ∑ x, ‖β m x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP : 0 ≤ ∑ r, ∑ j, ∑ m, ‖∑ x, K j r x a * β m x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq := hcs.trans (mul_le_mul hb hc (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _) hF2)
  nlinarith [norm_nonneg (∑ r, ∑ j, ∑ m, (∑ x, K j r x a * β m x) * conj (∑ y, L m r y a * α j y)),
    sq_nonneg ((∑ j, ∑ y, ‖α j y‖ ^ 2) - (∑ m, ∑ x, ‖β m x‖ ^ 2))]

/-- Monogamy with a shared register of `|S|` states: `F₁ + F₂ ≤ (d + |S|) ‖ψ‖²`. -/
theorem mono_core {Rr X Y OA J M : Type*} [Fintype Rr] [Fintype X] [Fintype Y] [Fintype OA]
    [DecidableEq OA] [Fintype J] [Fintype M] (S : Finset OA)
    (K : J → Rr → X → OA → ℂ) (L : M → Rr → Y → OA → ℂ)
    (hK : ∀ u : X → OA → ℂ, ∑ r, ∑ j, ‖∑ x, ∑ a, K j r x a * u x a‖ ^ 2 ≤ ∑ x, ∑ a, ‖u x a‖ ^ 2)
    (hL : ∀ u : Y → OA → ℂ, ∑ r, ∑ m, ‖∑ y, ∑ a, L m r y a * u y a‖ ^ 2 ≤ ∑ y, ∑ a, ‖u y a‖ ^ 2)
    (ψ : Rr → X → Y → OA → ℂ) (hψ : ∀ r x y a, a ∉ S → ψ r x y a = 0) :
    (∑ j, ∑ y, ‖∑ r, ∑ x, ∑ a, K j r x a * ψ r x y a‖ ^ 2) +
      (∑ m, ∑ x, ‖∑ r, ∑ y, ∑ a, L m r y a * ψ r x y a‖ ^ 2) ≤
      ((Fintype.card Rr : ℝ) + S.card) * ∑ r, ∑ x, ∑ y, ∑ a, ‖ψ r x y a‖ ^ 2 := by
  classical
  set α : J → Y → ℂ := fun j y => ∑ r, ∑ x, ∑ a, K j r x a * ψ r x y a with hα
  set β : M → X → ℂ := fun m x => ∑ r, ∑ y, ∑ a, L m r y a * ψ r x y a with hβ
  set F1 := ∑ j, ∑ y, ‖α j y‖ ^ 2 with hF1d
  set F2 := ∑ m, ∑ x, ‖β m x‖ ^ 2 with hF2d
  set N := ∑ r, ∑ x, ∑ y, ∑ a, ‖ψ r x y a‖ ^ 2 with hNd
  set d : ℝ := (Fintype.card Rr : ℝ) with hd
  let ξ1 : Rr → X → Y → OA → ℂ := fun r x y a => ∑ j, K j r x a * conj (α j y)
  let ξ2 : Rr → X → Y → OA → ℂ := fun r x y a => ∑ m, L m r y a * conj (β m x)
  let ξ : Rr → X → Y → OA → ℂ := fun r x y a => if a ∈ S then ξ1 r x y a + ξ2 r x y a else 0
  have hid1 : ((F1 : ℝ) : ℂ) = ∑ r, ∑ x, ∑ y, ∑ a, ψ r x y a * ξ1 r x y a := side_id K ψ
  have hid2 : ((F2 : ℝ) : ℂ) = ∑ r, ∑ x, ∑ y, ∑ a, ψ r x y a * ξ2 r x y a := by
    have h := side_id (Y := X) (X := Y) L (fun r y x a => ψ r x y a)
    refine h.trans ?_
    exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hF10 : 0 ≤ F1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF20 : 0 ≤ F2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : (((F1 + F2 : ℝ)) : ℂ) = ∑ r, ∑ x, ∑ y, ∑ a, ψ r x y a * ξ r x y a := by
    rw [Complex.ofReal_add, hid1, hid2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ S
    · simp only [ξ, if_pos ha]; ring
    · simp only [ξ, if_neg ha, hψ r x y a ha]; ring
  have hnorm : F1 + F2 = ‖∑ r, ∑ x, ∑ y, ∑ a, ψ r x y a * ξ r x y a‖ := by
    rw [← hsum, Complex.norm_of_nonneg (add_nonneg hF10 hF20)]
  have hcs := cs4 ψ ξ
  rw [← hnorm] at hcs
  -- the norm of ξ
  have hpt : ∀ r x y a, ‖ξ r x y a‖ ^ 2 ≤ ‖ξ1 r x y a‖ ^ 2 + ‖ξ2 r x y a‖ ^ 2 +
      (if a ∈ S then 2 * (ξ1 r x y a * conj (ξ2 r x y a)).re else 0) := by
    intro r x y a
    by_cases ha : a ∈ S
    · simp only [ξ, if_pos ha]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_add]
    · simp only [ξ, if_neg ha, norm_zero]
      nlinarith [sq_nonneg ‖ξ1 r x y a‖, sq_nonneg ‖ξ2 r x y a‖]
  have hd1 : ∑ r, ∑ x, ∑ y, ∑ a, ‖ξ1 r x y a‖ ^ 2 ≤ d * F1 := by
    have h := side_diag K hK (fun j y => conj (α j y))
    simp only [RCLike.norm_conj] at h
    exact h
  have hd2 : ∑ r, ∑ x, ∑ y, ∑ a, ‖ξ2 r x y a‖ ^ 2 ≤ d * F2 := by
    have h := side_diag L hL (fun m x => conj (β m x))
    simp only [RCLike.norm_conj] at h
    refine le_trans (le_of_eq ?_) h
    exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hcr : ∑ r, ∑ x, ∑ y, ∑ a,
      (if a ∈ S then 2 * (ξ1 r x y a * conj (ξ2 r x y a)).re else 0) ≤ S.card * (F1 + F2) := by
    rw [← push4 (fun a r x y => (if a ∈ S then 2 * (ξ1 r x y a * conj (ξ2 r x y a)).re else 0))]
    have hc : ∀ a, (∑ r, ∑ x, ∑ y,
        (if a ∈ S then 2 * (ξ1 r x y a * conj (ξ2 r x y a)).re else 0)) ≤
        (if a ∈ S then F1 + F2 else 0) := by
      intro a
      by_cases ha : a ∈ S
      · simp only [if_pos ha]
        have hx := cross K L hK hL α β a
        have hre : ∑ r, ∑ x, ∑ y, 2 * (ξ1 r x y a * conj (ξ2 r x y a)).re =
            2 * (∑ r, ∑ x, ∑ y, ξ1 r x y a * conj (ξ2 r x y a)).re := by
          simp only [Complex.re_sum, Finset.mul_sum]
        rw [hre]
        have := Complex.re_le_norm (∑ r, ∑ x, ∑ y, ξ1 r x y a * conj (ξ2 r x y a))
        linarith
      · simp [ha]
    calc _ ≤ ∑ a : OA, (if a ∈ S then F1 + F2 else 0) := Finset.sum_le_sum fun a _ => hc a
      _ = S.card * (F1 + F2) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hxi : ∑ r, ∑ x, ∑ y, ∑ a, ‖ξ r x y a‖ ^ 2 ≤ (d + S.card) * (F1 + F2) := by
    have h1 : ∑ r, ∑ x, ∑ y, ∑ a, ‖ξ r x y a‖ ^ 2 ≤ ∑ r, ∑ x, ∑ y, ∑ a,
        (‖ξ1 r x y a‖ ^ 2 + ‖ξ2 r x y a‖ ^ 2 +
          (if a ∈ S then 2 * (ξ1 r x y a * conj (ξ2 r x y a)).re else 0)) :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        Finset.sum_le_sum fun a _ => hpt r x y a
    simp only [Finset.sum_add_distrib] at h1
    nlinarith
  have hfin : (F1 + F2) ^ 2 ≤ N * ((d + S.card) * (F1 + F2)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hxi hN0)
  have hS : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  show F1 + F2 ≤ (d + S.card) * N
  by_contra hcon0
  have hcon := not_le.mp hcon0
  have hpos : 0 < F1 + F2 := lt_of_le_of_lt (mul_nonneg (add_nonneg hd0 hS) hN0) hcon
  nlinarith

end EC74504552M

namespace EC74504552M
open QAlgorithms
open scoped ComplexConjugate Matrix

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


theorem side_tr {Rr Z O X Y OA L Ka Kb J : Type*} [Fintype Rr] [Fintype Z] [Fintype O] [Fintype X]
    [Fintype Y] [Fintype OA] [Fintype L] [Fintype Ka] [Fintype Kb] [Fintype J]
    (A : Ka → Matrix Z Rr ℂ) (B : Kb → Matrix Rr O ℂ) (V : L → Matrix (X × Y × OA) Z ℂ)
    (e : X × OA ≃ O) (N : J → Matrix O Z ℂ)
    (h : ∀ (x x' : X) (w w' : OA) (z z' : Z),
      ∑ p : L × Y, V p.1 (x, p.2, w) z * conj (V p.1 (x', p.2, w') z') =
        ∑ j, N j (e (x, w)) z * conj (N j (e (x', w')) z'))
    (a : Ka) (b : Kb) :
    ∑ j, ‖(B b * N j * A a).trace‖ ^ 2 =
      ∑ l, ∑ y, ‖∑ r, ∑ x, ∑ w, B b r (e (x, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2 := by
  have htr : ∀ j, (B b * N j * A a).trace =
      ∑ p : (X × OA) × Z, (∑ r, B b r (e p.1) * A a p.2 r) * N j (e p.1) p.2 := by
    intro j
    rw [trace_BNA]
    exact (Equiv.sum_comp (e.prodCongr (Equiv.refl Z))
      (fun x : O × Z => (∑ r, B b r x.1 * A a x.2 r) * N j x.1 x.2)).symm
  simp_rw [htr]
  rw [sq_sum_transfer (fun p : (X × OA) × Z => ∑ r, B b r (e p.1) * A a p.2 r)
    (fun (j : J) (p : (X × OA) × Z) => N j (e p.1) p.2)
    (fun (q : L × Y) (p : (X × OA) × Z) => V q.1 (p.1.1, q.2, p.1.2) p.2)
    (fun p1 p2 => (h p1.1.1 p2.1.1 p1.1.2 p2.1.2 p1.2 p2.2).symm)]
  refine (Fintype.sum_prod_type _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun y _ => ?_
  refine congrArg (fun t : ℂ => ‖t‖ ^ 2) ?_
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  refine Eq.trans ?_ (push4 _).symm
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun r _ => by ring

theorem contr_of_kraus {Rr O X W Kb : Type*} [Fintype Rr] [Fintype O] [DecidableEq O] [Fintype X]
    [Fintype W] [Fintype Kb] (B : Kb → Matrix Rr O ℂ) (hB : IsKrausFamily B) (e : X × W ≃ O)
    (u : X → W → ℂ) :
    ∑ r, ∑ b, ‖∑ x, ∑ w, B b r (e (x, w)) * u x w‖ ^ 2 ≤ ∑ x, ∑ w, ‖u x w‖ ^ 2 := by
  have h := kraus_collapse B hB (fun o => u (e.symm o).1 (e.symm o).2)
  have h2 : ∀ (f : O → ℂ), ∑ o, f o = ∑ x, ∑ w, f (e (x, w)) := fun f => by
    rw [← Equiv.sum_comp e f, Fintype.sum_prod_type]
  have h3 : ∀ (f : O → ℝ), ∑ o, f o = ∑ x, ∑ w, f (e (x, w)) := fun f => by
    rw [← Equiv.sum_comp e f, Fintype.sum_prod_type]
  simp only [h2, h3, Equiv.symm_apply_apply] at h
  rw [Finset.sum_comm]
  exact le_of_eq h

theorem norm_total {Rr Z X Y OA L Ka : Type*} [Fintype Rr] [DecidableEq Rr] [Fintype Z]
    [DecidableEq Z] [Fintype X] [Fintype Y] [Fintype OA] [Fintype L] [Fintype Ka]
    (A : Ka → Matrix Z Rr ℂ) (hA : IsKrausFamily A) (V : L → Matrix (X × Y × OA) Z ℂ)
    (hV : IsKrausFamily V) :
    ∑ a, ∑ l, ∑ r, ∑ x, ∑ y, ∑ w, ‖∑ z, V l (x, y, w) z * A a z r‖ ^ 2 =
      (Fintype.card Rr : ℝ) := by
  have hA1 : ∀ r, ∑ a, ∑ z, ‖A a z r‖ ^ 2 = 1 := by
    intro r
    have := kraus_collapse A hA (fun r' => if r' = r then (1 : ℂ) else 0)
    simpa [mul_ite, Finset.sum_ite_eq', sum_ite_sq] using this
  have hV1 : ∀ a r, ∑ l, ∑ x, ∑ y, ∑ w, ‖∑ z, V l (x, y, w) z * A a z r‖ ^ 2 =
      ∑ z, ‖A a z r‖ ^ 2 := by
    intro a r
    have := kraus_collapse V hV (fun z => A a z r)
    simpa only [Fintype.sum_prod_type] using this
  calc _ = ∑ a, ∑ r, ∑ l, ∑ x, ∑ y, ∑ w, ‖∑ z, V l (x, y, w) z * A a z r‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ r, ∑ z, ‖A a z r‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => hV1 a r
    _ = ∑ r : Rr, ∑ a, ∑ z, ‖A a z r‖ ^ 2 := Finset.sum_comm
    _ = ∑ _r : Rr, (1 : ℝ) := Finset.sum_congr rfl fun r _ => hA1 r
    _ = _ := by simp

/-- Monogamy for a broadcast with a shared register: Bob sees `(X, OA)`, Eve `(Y, OA)`. -/
theorem mono_kraus3 {Rr Z O X Y OA L Ka Kb J1 J2 : Type*} [Fintype Rr] [DecidableEq Rr]
    [Fintype Z] [DecidableEq Z] [Fintype O] [DecidableEq O] [Fintype X] [Fintype Y] [Fintype OA]
    [DecidableEq OA] [Fintype L] [Fintype Ka] [Fintype Kb] [Fintype J1] [Fintype J2]
    (A : Ka → Matrix Z Rr ℂ) (hA : IsKrausFamily A) (B : Kb → Matrix Rr O ℂ)
    (hB : IsKrausFamily B) (V : L → Matrix (X × Y × OA) Z ℂ) (hV : IsKrausFamily V)
    (S : Finset OA) (hS : ∀ l x y w z, w ∉ S → V l (x, y, w) z = 0)
    (eB : X × OA ≃ O) (eE : Y × OA ≃ O) (N1 : J1 → Matrix O Z ℂ) (N2 : J2 → Matrix O Z ℂ)
    (h1 : ∀ (x x' : X) (w w' : OA) (z z' : Z),
      ∑ p : L × Y, V p.1 (x, p.2, w) z * conj (V p.1 (x', p.2, w') z') =
        ∑ j, N1 j (eB (x, w)) z * conj (N1 j (eB (x', w')) z'))
    (h2 : ∀ (y y' : Y) (w w' : OA) (z z' : Z),
      ∑ p : L × X, V p.1 (p.2, y, w) z * conj (V p.1 (p.2, y', w') z') =
        ∑ j, N2 j (eE (y, w)) z * conj (N2 j (eE (y', w')) z')) :
    (∑ a, ∑ b, ∑ j, ‖(B b * N1 j * A a).trace‖ ^ 2) +
      (∑ a, ∑ b, ∑ j, ‖(B b * N2 j * A a).trace‖ ^ 2) ≤
      ((Fintype.card Rr : ℝ) + S.card) * Fintype.card Rr := by
  classical
  let V' : L → Matrix (Y × X × OA) Z ℂ := fun l => Matrix.of fun t z => V l (t.2.1, t.1, t.2.2) z
  have hb1 : ∀ a b, ∑ j, ‖(B b * N1 j * A a).trace‖ ^ 2 =
      ∑ l, ∑ y, ‖∑ r, ∑ x, ∑ w, B b r (eB (x, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2 :=
    fun a b => side_tr A B V eB N1 h1 a b
  have hb2 : ∀ a b, ∑ j, ‖(B b * N2 j * A a).trace‖ ^ 2 =
      ∑ l, ∑ x, ‖∑ r, ∑ y, ∑ w, B b r (eE (y, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2 :=
    fun a b => side_tr A B V' eE N2 (fun y y' w w' z z' => h2 y y' w w' z z') a b
  have hcore : ∀ a l,
      (∑ b, ∑ y, ‖∑ r, ∑ x, ∑ w, B b r (eB (x, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2) +
      (∑ b, ∑ x, ‖∑ r, ∑ y, ∑ w, B b r (eE (y, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2) ≤
      ((Fintype.card Rr : ℝ) + S.card) *
        ∑ r, ∑ x, ∑ y, ∑ w, ‖∑ z, V l (x, y, w) z * A a z r‖ ^ 2 := by
    intro a l
    refine mono_core S (fun b r x w => B b r (eB (x, w))) (fun b r y w => B b r (eE (y, w)))
      (fun u => contr_of_kraus B hB eB u) (fun u => contr_of_kraus B hB eE u)
      (fun r x y w => ∑ z, V l (x, y, w) z * A a z r) ?_
    intro r x y w hw
    simp [hS l x y w _ hw]
  calc _ = ∑ a, ∑ l,
        ((∑ b, ∑ y, ‖∑ r, ∑ x, ∑ w, B b r (eB (x, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2) +
        (∑ b, ∑ x, ‖∑ r, ∑ y, ∑ w, B b r (eE (y, w)) * ∑ z, V l (x, y, w) z * A a z r‖ ^ 2)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_add_distrib]
        congr 1
        · exact (Finset.sum_congr rfl fun b _ => hb1 a b).trans Finset.sum_comm
        · exact (Finset.sum_congr rfl fun b _ => hb2 a b).trans Finset.sum_comm
    _ ≤ ∑ a, ∑ l, ((Fintype.card Rr : ℝ) + S.card) *
        ∑ r, ∑ x, ∑ y, ∑ w, ‖∑ z, V l (x, y, w) z * A a z r‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun l _ => hcore a l
    _ = ((Fintype.card Rr : ℝ) + S.card) *
        ∑ a, ∑ l, ∑ r, ∑ x, ∑ y, ∑ w, ‖∑ z, V l (x, y, w) z * A a z r‖ ^ 2 := by
        simp only [Finset.mul_sum]
    _ = _ := by rw [norm_total A hA V hV]

end EC74504552M

namespace EC74504552T
open QAlgorithms EC74504552K EC74504552G
open scoped ComplexConjugate Matrix

theorem prod_sum2' {ι K A : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [Fintype A]
    (f : ι → K → A → ℂ) :
    ∑ p : (ι → K) × (ι → A), ∏ q, f q (p.1 q) (p.2 q) = ∏ q, ∑ k, ∑ a, f q k a := by
  rw [Fintype.sum_prod_type]
  have h : ∀ l : ι → K, ∑ x : ι → A, ∏ q, f q (l q) (x q) = ∏ q, ∑ a, f q (l q) a :=
    fun l => (Fintype.prod_sum (fun (q : ι) (a : A) => f q (l q) a)).symm
  simp_rw [h]
  exact (Fintype.prod_sum (fun (q : ι) (k : K) => ∑ a, f q k a)).symm

theorem ker0 (o o' : Bool × Bool) (b b' : Bool) :
    erasureKernel 0 o o' b b' =
      (if o = (b, false) then (1 : ℂ) else 0) * conj (if o' = (b', false) then (1 : ℂ) else 0) := by
  rcases o with ⟨o1, o2⟩
  rcases o' with ⟨o1', o2'⟩
  cases o1 <;> cases o2 <;> cases o1' <;> cases o2' <;> cases b <;> cases b' <;>
    simp [erasureKernel]

theorem kraus3 {X Y OA O Z L J : Type*} [Fintype X] [Fintype Y] [Fintype OA] [Fintype O]
    [Fintype Z] [DecidableEq Z] [Fintype L] [Fintype J]
    (V : L → Matrix (X × Y × OA) Z ℂ) (eB : X × OA ≃ O) (N : J → Matrix O Z ℂ)
    (h1 : ∀ (x x' : X) (w w' : OA) (z z' : Z),
      ∑ p : L × Y, V p.1 (x, p.2, w) z * conj (V p.1 (x', p.2, w') z') =
        ∑ j, N j (eB (x, w)) z * conj (N j (eB (x', w')) z'))
    (hN : ∀ z z', ∑ o, ∑ j, N j o z * conj (N j o z') = if z = z' then 1 else 0) :
    IsKrausFamily V := by
  unfold IsKrausFamily
  ext z z'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have step : ∀ l, ∑ t : X × Y × OA, star (V l t z) * V l t z' =
      ∑ x, ∑ w, ∑ y, V l (x, y, w) z' * conj (V l (x, y, w) z) := by
    intro l
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm]; rfl
  simp_rw [step]
  rw [Finset.sum_comm]
  have h3 : ∀ x, ∑ l, ∑ w, ∑ y, V l (x, y, w) z' * conj (V l (x, y, w) z) =
      ∑ w, ∑ j, N j (eB (x, w)) z' * conj (N j (eB (x, w)) z) := fun x => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← h1 x x w w z' z]
    exact (Fintype.sum_prod_type (fun p : L × Y => V p.1 (x, p.2, w) z' * conj (V p.1 (x, p.2, w) z))).symm
  simp_rw [h3]
  have h4 : ∑ x, ∑ w, ∑ j, N j (eB (x, w)) z' * conj (N j (eB (x, w)) z) =
      ∑ o, ∑ j, N j o z' * conj (N j o z) := by
    rw [← Equiv.sum_comp eB (fun o => ∑ j, N j o z' * conj (N j o z)), Fintype.sum_prod_type]
  rw [h4, hN]
  by_cases h : z = z'
  · subst h; simp
  · simp [h, @eq_comm _ z' z]

theorem patK_hN {n : ℕ} (e : Fin n → Bool) (z z' : Qubits n) :
    ∑ o, ∑ j, patKraus e j o z * conj (patKraus e j o z') = if z = z' then 1 else 0 := by
  rw [← patK_diag n (fun q => if e q then 1 else 0) z z']
  exact Finset.sum_congr rfl fun o _ => pat_kernel e (o, z) (o, z')

/-- Broadcast isometry for a 3-type partition `τ` (0 = shared, 1 = Eve erased, 2 = Bob erased). -/
noncomputable def tV {n : ℕ} (τ : Fin n → Fin 3) (l : {q // ¬ τ q = 0} → Bool × Bool × Bool) :
    Matrix (({q // ¬ τ q = 0} → Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool) ×
      ({q // τ q = 0} → Bool × Bool)) (Qubits n) ℂ :=
  Matrix.of fun t z =>
    (∏ q : {q // ¬ τ q = 0}, Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) (l q) (t.1 q) (t.2.1 q) (z q.1)) *
      ∏ q : {q // τ q = 0}, (if t.2.2 q = (z q.1, false) then (1 : ℂ) else 0)

def teB {n : ℕ} (τ : Fin n → Fin 3) :
    ({q // ¬ τ q = 0} → Bool × Bool) × ({q // τ q = 0} → Bool × Bool) ≃ (Fin n → Bool × Bool) :=
  (Equiv.prodComm _ _).trans (Equiv.piEquivPiSubtypeProd (fun q => τ q = 0) (fun _ => Bool × Bool)).symm

theorem teB_pos {n : ℕ} (τ : Fin n → Fin 3) (x : {q // ¬ τ q = 0} → Bool × Bool)
    (w : {q // τ q = 0} → Bool × Bool) (q : {q // τ q = 0}) : teB τ (x, w) q.1 = w q := by
  simp [teB, Equiv.piEquivPiSubtypeProd, q.2]

theorem teB_neg {n : ℕ} (τ : Fin n → Fin 3) (x : {q // ¬ τ q = 0} → Bool × Bool)
    (w : {q // τ q = 0} → Bool × Bool) (q : {q // ¬ τ q = 0}) : teB τ (x, w) q.1 = x q := by
  simp [teB, Equiv.piEquivPiSubtypeProd, q.2]

theorem cover3 : ∀ i : Fin 3, ¬ i = 0 → decide (i = 2) = true ∨ decide (i = 1) = true := by decide

theorem tV_h1 {n : ℕ} (τ : Fin n → Fin 3) (x x' : {q // ¬ τ q = 0} → Bool × Bool)
    (w w' : {q // τ q = 0} → Bool × Bool) (z z' : Qubits n) :
    ∑ p : ({q // ¬ τ q = 0} → Bool × Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool),
      tV τ p.1 (x, p.2, w) z * conj (tV τ p.1 (x', p.2, w') z') =
    ∑ j, patKraus (fun q => decide (τ q = 2)) j (teB τ (x, w)) z *
      conj (patKraus (fun q => decide (τ q = 2)) j (teB τ (x', w')) z') := by
  rw [pat_kernel (fun q => decide (τ q = 2)) (teB τ (x, w), z) (teB τ (x', w'), z')]
  dsimp only
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun q => τ q = 0)]
  have hs := prod_sum2' (fun (q : {q // ¬ τ q = 0}) (k : Bool × Bool × Bool) (a : Bool × Bool) =>
    Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) k (x q) a (z q.1) *
      conj (Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) k (x' q) a (z' q.1)))
  beta_reduce at hs
  have hL : ∑ p : ({q // ¬ τ q = 0} → Bool × Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool),
      tV τ p.1 (x, p.2, w) z * conj (tV τ p.1 (x', p.2, w') z') =
      (∑ p : ({q // ¬ τ q = 0} → Bool × Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool),
        ∏ q, Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) (p.1 q) (x q) (p.2 q) (z q.1) *
          conj (Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) (p.1 q) (x' q) (p.2 q) (z' q.1))) *
      ∏ q : {q // τ q = 0}, ((if w q = (z q.1, false) then (1 : ℂ) else 0) *
        conj (if w' q = (z' q.1, false) then (1 : ℂ) else 0)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [tV, Matrix.of_apply, map_mul, map_prod, Finset.prod_mul_distrib]
    ring
  rw [hL, hs, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    have h0 : decide (τ q.1 = 2) = false := by simp [q.2]
    simp only [h0, teB_pos, if_false, Bool.false_eq_true]
    rw [ker0]
  · refine Finset.prod_congr rfl fun q _ => ?_
    rw [teB_neg, teB_neg]
    exact vq_marg1 _ _ (cover3 _ q.2) _ _ _ _

theorem tV_h2 {n : ℕ} (τ : Fin n → Fin 3) (y y' : {q // ¬ τ q = 0} → Bool × Bool)
    (w w' : {q // τ q = 0} → Bool × Bool) (z z' : Qubits n) :
    ∑ p : ({q // ¬ τ q = 0} → Bool × Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool),
      tV τ p.1 (p.2, y, w) z * conj (tV τ p.1 (p.2, y', w') z') =
    ∑ j, patKraus (fun q => decide (τ q = 1)) j (teB τ (y, w)) z *
      conj (patKraus (fun q => decide (τ q = 1)) j (teB τ (y', w')) z') := by
  rw [pat_kernel (fun q => decide (τ q = 1)) (teB τ (y, w), z) (teB τ (y', w'), z')]
  dsimp only
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun q => τ q = 0)]
  have hs := prod_sum2' (fun (q : {q // ¬ τ q = 0}) (k : Bool × Bool × Bool) (a : Bool × Bool) =>
    Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) k a (y q) (z q.1) *
      conj (Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) k a (y' q) (z' q.1)))
  beta_reduce at hs
  have hL : ∑ p : ({q // ¬ τ q = 0} → Bool × Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool),
      tV τ p.1 (p.2, y, w) z * conj (tV τ p.1 (p.2, y', w') z') =
      (∑ p : ({q // ¬ τ q = 0} → Bool × Bool × Bool) × ({q // ¬ τ q = 0} → Bool × Bool),
        ∏ q, Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) (p.1 q) (p.2 q) (y q) (z q.1) *
          conj (Vq (decide (τ q.1 = 2)) (decide (τ q.1 = 1)) (p.1 q) (p.2 q) (y' q) (z' q.1))) *
      ∏ q : {q // τ q = 0}, ((if w q = (z q.1, false) then (1 : ℂ) else 0) *
        conj (if w' q = (z' q.1, false) then (1 : ℂ) else 0)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [tV, Matrix.of_apply, map_mul, map_prod, Finset.prod_mul_distrib]
    ring
  rw [hL, hs, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    have h0 : decide (τ q.1 = 1) = false := by simp [q.2]
    simp only [h0, teB_pos, if_false, Bool.false_eq_true]
    rw [ker0]
  · refine Finset.prod_congr rfl fun q _ => ?_
    rw [teB_neg, teB_neg]
    exact vq_marg2 _ _ (cover3 _ q.2) _ _ _ _

def tS {n : ℕ} (τ : Fin n → Fin 3) : Finset ({q // τ q = 0} → Bool × Bool) :=
  Finset.univ.image (fun b : {q // τ q = 0} → Bool => fun q => (b q, false))

theorem tV_supp {n : ℕ} (τ : Fin n → Fin 3) (l : {q // ¬ τ q = 0} → Bool × Bool × Bool)
    (x y : {q // ¬ τ q = 0} → Bool × Bool) (w : {q // τ q = 0} → Bool × Bool) (z : Qubits n)
    (hw : w ∉ tS τ) : tV τ l (x, y, w) z = 0 := by
  have : ∃ q : {q // τ q = 0}, w q ≠ (z q.1, false) := by
    by_contra h
    push Not at h
    exact hw (Finset.mem_image.mpr ⟨fun q => z q.1, Finset.mem_univ _, funext fun q => (h q).symm⟩)
  obtain ⟨q, hq⟩ := this
  simp only [tV, Matrix.of_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq), mul_zero]

theorem tS_card {n : ℕ} (τ : Fin n → Fin 3) :
    ((tS τ).card : ℝ) ≤ 2 ^ (Finset.univ.filter (fun q => τ q = 0)).card := by
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset ({q // τ q = 0} → Bool)))
    (f := fun b : {q // τ q = 0} → Bool => fun q => (b q, false))
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at h1
  exact_mod_cast h1

theorem tau_bound {k n m m' : ℕ} (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ) (hA : IsKrausFamily A)
    (B : Fin m' → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ) (hB : IsKrausFamily B)
    (τ : Fin n → Fin 3) :
    (∑ a, ∑ b, ∑ j : Fin n → Fin 5,
        ‖(B b * patKraus (fun q => decide (τ q = 2)) j * A a).trace‖ ^ 2) +
      (∑ a, ∑ b, ∑ j : Fin n → Fin 5,
        ‖(B b * patKraus (fun q => decide (τ q = 1)) j * A a).trace‖ ^ 2) ≤
      ((2 : ℝ) ^ k + 2 ^ (Finset.univ.filter (fun q => τ q = 0)).card) * 2 ^ k := by
  have hV : IsKrausFamily (tV τ) :=
    kraus3 (tV τ) (teB τ) (patKraus (fun q => decide (τ q = 2))) (tV_h1 τ)
      (patK_hN (fun q => decide (τ q = 2)))
  have h := EC74504552M.mono_kraus3 A hA B hB (tV τ) hV (tS τ)
    (fun l x y w z hw => tV_supp τ l x y w z hw) (teB τ) (teB τ)
    (patKraus (fun q => decide (τ q = 2))) (patKraus (fun q => decide (τ q = 1)))
    (tV_h1 τ) (tV_h2 τ)
  rw [card_qubits] at h
  refine h.trans ?_
  have := tS_card τ
  have hk : (0 : ℝ) ≤ 2 ^ k := by positivity
  nlinarith

end EC74504552T

namespace EC74504552C
open Finset

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


end EC74504552C

namespace EC74504552U
open QAlgorithms EC74504552K EC74504552G EC74504552T EC74504552C Finset
open scoped ComplexConjugate Matrix

noncomputable def Phi {k n m m' : ℕ} (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ)
    (B : Fin m' → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ) (e : Fin n → Bool) : ℝ :=
  ∑ a, ∑ b, ∑ j : Fin n → Fin 5, ‖(B b * patKraus e j * A a).trace‖ ^ 2

theorem Phi_nonneg {k n m m' : ℕ} (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ)
    (B : Fin m' → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ) (e : Fin n → Bool) :
    0 ≤ Phi A B e := by
  unfold Phi; positivity

theorem tau_bound' {k n m m' : ℕ} (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ) (hA : IsKrausFamily A)
    (B : Fin m' → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ) (hB : IsKrausFamily B)
    (τ : Fin n → Fin 3) :
    Phi A B (fun q => decide (τ q = 2)) + Phi A B (fun q => decide (τ q = 1)) ≤
      ((2 : ℝ) ^ k + 2 ^ (Finset.univ.filter (fun q => τ q = 0)).card) * 2 ^ k :=
  tau_bound A hA B hB τ

theorem Phi_cap {k n m m' : ℕ} (A : Fin m → Matrix (Qubits n) (Qubits k) ℂ) (hA : IsKrausFamily A)
    (B : Fin m' → Matrix (Qubits k) (Fin n → Bool × Bool) ℂ) (hB : IsKrausFamily B)
    (e : Fin n → Bool) : Phi A B e ≤ ((2 : ℝ) ^ k + 1) * 2 ^ k := by
  have h := tau_bound' A hA B hB (fun q => if e q then (2 : Fin 3) else 1)
  beta_reduce at h
  have h2 : (fun q => decide ((if e q then (2 : Fin 3) else 1) = 2)) = e := by
    funext q; cases e q <;> decide
  have h0 : (Finset.univ.filter (fun q => (if e q then (2 : Fin 3) else 1) = 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q _; cases e q <;> decide
  rw [h2, h0, pow_zero] at h
  have := Phi_nonneg A B (fun q => decide ((if e q then (2 : Fin 3) else 1) = 1))
  linarith

theorem mw2 (p : ℝ) (b : Bool) :
    (∑ i : Fin 3, if (fun i : Fin 3 => decide (i = 2)) i = b then (![1 - 2 * p, p, p] : Fin 3 → ℝ) i
      else 0) = if b then p else 1 - p := by
  cases b <;> simp [Fin.sum_univ_three] <;> ring

theorem mw1 (p : ℝ) (b : Bool) :
    (∑ i : Fin 3, if (fun i : Fin 3 => decide (i = 1)) i = b then (![1 - 2 * p, p, p] : Fin 3 → ℝ) i
      else 0) = if b then p else 1 - p := by
  cases b <;> simp [Fin.sum_univ_three] <;> ring

theorem mw0 (p : ℝ) (b : Bool) :
    (∑ i : Fin 3, if (fun i : Fin 3 => decide (i = 0)) i = b then (![1 - 2 * p, p, p] : Fin 3 → ℝ) i
      else 0) = if b then 1 - 2 * p else 1 - (1 - 2 * p) := by
  cases b <;> simp [Fin.sum_univ_three] <;> ring

theorem ecount_tau {n : ℕ} (τ : Fin n → Fin 3) :
    ecount (fun q => decide (τ q = 0)) = (Finset.univ.filter (fun q => τ q = 0)).card := by
  simp [ecount]

set_option maxHeartbeats 1000000 in
theorem erasure_rate_le (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) (R : ℝ)
    (h : IsAchievableQRate (fun n => erasureChannel n p) R) : R ≤ 1 - 2 * p := by
  by_contra hR
  push Not at hR
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ R - δ = 1 - 2 * p + 2 * δ :=
    ⟨(R - (1 - 2 * p)) / 3, by linarith, by ring⟩
  obtain ⟨N0, hN0⟩ := h (1 / 8) (by norm_num) δ hδ0
  obtain ⟨n, hnN0, hnbig⟩ : ∃ n : ℕ, N0 ≤ n ∧ 16 / δ ^ 2 + 2 / δ ≤ (n : ℝ) :=
    ⟨max N0 (⌈16 / δ ^ 2 + 2 / δ⌉₊), le_max_left _ _,
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)⟩
  obtain ⟨k, hk, Enc, hE, Dec, hD, hF⟩ := hN0 n hnN0
  rw [hδ] at hk
  have hd16 : 0 ≤ 16 / δ ^ 2 := by positivity
  have hd2 : 0 ≤ 2 / δ := by positivity
  have hn16 : 16 ≤ δ ^ 2 * n := by
    have h1 : 16 / δ ^ 2 ≤ n := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at h1
  have hn2 : 2 ≤ δ * n := by
    have h1 : 2 / δ ≤ n := by linarith
    rwa [div_le_iff₀ hδ0, mul_comm] at h1
  have hnpos : (0 : ℝ) < n := by
    have : 0 < 16 / δ ^ 2 := by positivity
    linarith
  have hk4 : (4 : ℝ) ≤ k := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * p) hnpos.le
    linarith
  obtain ⟨m, m', A, B, hA, hB, hfid⟩ := fid_pattern p hp0 (by linarith) Enc hE Dec hD
  rw [hfid] at hF
  have hF' : 1 - 1 / 8 ≤ ((2 : ℝ) ^ k)⁻¹ ^ 2 *
      ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) * Phi A B e := hF
  set d : ℝ := 2 ^ k with hd
  have hd0 : 0 < d := by positivity
  have hdge : (2 : ℝ) ≤ d := by
    have hk1 : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  set c : Fin 3 → ℝ := ![1 - 2 * p, p, p] with hc
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i; fin_cases i <;> simp [hc] <;> linarith
  have hw0 : ∀ τ : Fin n → Fin 3, 0 ≤ ∏ q, c (τ q) := fun τ => Finset.prod_nonneg fun q _ => hc0 _
  have hw1 : ∑ τ : Fin n → Fin 3, ∏ q, c (τ q) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (i : Fin 3) => c i)]
    have : ∑ i : Fin 3, c i = 1 := by simp [hc, Fin.sum_univ_three]; ring
    simp [this]
  have hBm : ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * Phi A B (fun q => decide (τ q = 2)) =
      ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) * Phi A B e := by
    refine (marginal3 c (fun i => decide (i = 2)) (Phi A B)).trans ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun q _ => mw2 p (e q)
  have hEm : ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * Phi A B (fun q => decide (τ q = 1)) =
      ∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) * Phi A B e := by
    refine (marginal3 c (fun i => decide (i = 1)) (Phi A B)).trans ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun q _ => mw1 p (e q)
  let ind : (Fin n → Bool) → ℝ := fun e => if (1 - 2 * p + δ) * n ≤ ecount e then 1 else 0
  have hAm : ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * ind (fun q => decide (τ q = 0)) =
      ∑ e ∈ univ.filter (fun e : Fin n → Bool => (1 - 2 * p + δ) * n ≤ ecount e), pw (1 - 2 * p) e := by
    refine (marginal3 c (fun i => decide (i = 0)) ind).trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hpw : (∏ q, ∑ i : Fin 3, if (fun i : Fin 3 => decide (i = 0)) i = e q then c i else 0)
        = pw (1 - 2 * p) e := by
      unfold pw
      exact Finset.prod_congr rfl fun q _ => mw0 p (e q)
    rw [hpw]
    simp only [ind]
    split_ifs <;> simp
  have htail := tail_bound n (1 - 2 * p) δ (by linarith) (by linarith) hδ0
  set P := ∑ e ∈ univ.filter (fun e : Fin n → Bool => (1 - 2 * p + δ) * n ≤ ecount e),
    pw (1 - 2 * p) e with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun e _ => pw_nonneg _ (by linarith) (by linarith) e
  have hP16 : 16 * P ≤ 1 := by
    have h1 : (n : ℝ) * (1 - 2 * p) * (1 - (1 - 2 * p)) ≤ n := by
      have : (1 - 2 * p) * (1 - (1 - 2 * p)) ≤ 1 := mul_le_one₀ (by linarith) (by linarith) (by linarith)
      have := mul_le_mul_of_nonneg_left this hnpos.le
      linarith
    have h2 : (n : ℝ) * (δ ^ 2 * n * P) ≤ n * 1 := by linarith
    have h3 : δ ^ 2 * n * P ≤ 1 := le_of_mul_le_mul_left h2 hnpos
    have := mul_le_mul_of_nonneg_right hn16 hP0
    linarith
  have hpt : ∀ τ : Fin n → Fin 3,
      Phi A B (fun q => decide (τ q = 2)) + Phi A B (fun q => decide (τ q = 1)) ≤
        5 / 4 * d ^ 2 + 3 * d ^ 2 * ind (fun q => decide (τ q = 0)) := by
    intro τ
    by_cases hb : (1 - 2 * p + δ) * n ≤ ecount (fun q => decide (τ q = 0))
    · have hi : ind (fun q => decide (τ q = 0)) = 1 := if_pos hb
      rw [hi]
      have h1 := Phi_cap A hA B hB (fun q => decide (τ q = 2))
      have h2 := Phi_cap A hA B hB (fun q => decide (τ q = 1))
      rw [← hd] at h1 h2
      have := mul_le_mul_of_nonneg_left hdge hd0.le
      linarith
    · have hi : ind (fun q => decide (τ q = 0)) = 0 := if_neg hb
      rw [hi]
      push Not at hb
      rw [ecount_tau] at hb
      have hA2 : (Finset.univ.filter (fun q => τ q = 0)).card + 2 ≤ k := by
        have : ((Finset.univ.filter (fun q => τ q = 0)).card : ℝ) + 2 ≤ k := by linarith
        exact_mod_cast this
      have hpow : (2 : ℝ) ^ (Finset.univ.filter (fun q => τ q = 0)).card * 4 ≤ d := by
        rw [hd, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hA2
      have h1 := tau_bound' A hA B hB τ
      rw [← hd] at h1
      have := mul_le_mul_of_nonneg_right hpow hd0.le
      linarith
  have hsum : ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) *
      (Phi A B (fun q => decide (τ q = 2)) + Phi A B (fun q => decide (τ q = 1))) ≤
      ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * (5 / 4 * d ^ 2 + 3 * d ^ 2 * ind (fun q => decide (τ q = 0))) :=
    Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hpt τ) (hw0 τ)
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  rw [hBm, hEm] at hsum
  have hR2 : ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * (5 / 4 * d ^ 2) = 5 / 4 * d ^ 2 := by
    rw [← Finset.sum_mul, hw1, one_mul]
  have hR3 : ∑ τ : Fin n → Fin 3, (∏ q, c (τ q)) * (3 * d ^ 2 * ind (fun q => decide (τ q = 0))) =
      3 * d ^ 2 * P := by
    rw [← hAm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hR2, hR3] at hsum
  have key : ((2 : ℝ) ^ k)⁻¹ ^ 2 * (∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) * Phi A B e) =
      (∑ e : Fin n → Bool, (∏ q, if e q then p else 1 - p) * Phi A B e) / d ^ 2 := by
    rw [hd]; field_simp
  rw [key, le_div_iff₀ (by positivity)] at hF'
  have := mul_le_mul_of_nonneg_left hP16 (sq_nonneg d)
  have := pow_pos hd0 2
  linarith

end EC74504552U

open QAlgorithms in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) (R : ℝ)
    (h : IsAchievableQRate (fun n => erasureChannel n p) R) : R ≤ 1 - 2 * p := by
  exact EC74504552U.erasure_rate_le p hp0 hp R h
