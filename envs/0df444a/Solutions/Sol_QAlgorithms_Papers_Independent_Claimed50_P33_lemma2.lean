-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:26:48.826326+00:00
-- url     : https://prove2.me/submissions/323effe6-0476-455a-b56c-f638f9d42f93

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open Matrix Polynomial

namespace X8P33
open QAlgorithms

theorem x8_pow {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℂ)
    (h : A = W * diagonal d * Wᴴ) (n : ℕ) : A ^ n = W * diagonal (d ^ n) * Wᴴ := by
  induction n with
  | zero => simp [hW2]
  | succ n ih =>
    rw [pow_succ, ih, h]
    have : W * diagonal (d ^ n) * Wᴴ * (W * diagonal d * Wᴴ) =
        W * (diagonal (d ^ n) * (Wᴴ * W) * diagonal d) * Wᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hW1, Matrix.mul_one, diagonal_mul_diagonal, pow_succ]
    rfl

theorem x8_aeval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (p : ℝ[X]) :
    aeval A p = W * diagonal (fun k => ((p.eval (d k) : ℝ) : ℂ)) * Wᴴ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3; ext k; simp
  | monomial n c =>
    rw [aeval_monomial, x8_pow A W hW1 hW2 _ h n]
    simp only [eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← diagonal_smul]
    congr 3; ext k; simp [Pi.pow_apply]

theorem x8_trace_cfc {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (W : Matrix ι κ ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (d : κ → ℝ)
    (h : A = W * diagonal (fun k => (d k : ℂ)) * Wᴴ) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ k, ((f (d k) : ℝ) : ℂ) := by
  classical
  let S : Finset ℝ := Finset.univ.image d ∪ Finset.univ.image hA.eigenvalues
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A := by
    apply cfc_congr
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))).symm
  rw [h1, cfc_polynomial p A, x8_aeval A W hW1 hW2 d h p, Matrix.trace_mul_cycle, hW1,
    Matrix.one_mul, trace_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]


theorem x8_spec {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun k => ((hA.eigenvalues k : ℝ) : ℂ)) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem x8_U1 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix α α ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem x8_U2 {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix α α ℂ) * (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ = 1 :=
  Unitary.coe_mul_star_self _

theorem x8_ent_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    vnEntropy A = -∑ k, hA.eigenvalues k * Real.logb 2 (hA.eigenvalues k) := by
  unfold vnEntropy
  rw [x8_trace_cfc A hA _ (x8_U1 hA) (x8_U2 hA) _ (x8_spec hA)]
  simp [Complex.re_sum]

theorem x8_sum_eig {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α ℂ} (hA : A.IsHermitian)
    (ht : A.trace = 1) : ∑ k, hA.eigenvalues k = 1 := by
  have := hA.trace_eq_sum_eigenvalues
  rw [ht] at this
  have h2 := congrArg Complex.re this
  simpa [Complex.re_sum] using h2.symm

theorem x8_flog (x y : ℝ) : x * y * Real.logb 2 (x * y) =
    x * (y * Real.logb 2 y) + y * (x * Real.logb 2 x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [Real.logb_mul hx hy]; ring

theorem x8_ent_kron {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1)
    (e : γ ≃ α × β) :
    vnEntropy ((A ⊗ₖ B).submatrix e e) = vnEntropy A + vnEntropy B := by
  set U := (hA.eigenvectorUnitary : Matrix α α ℂ) with hU
  set V := (hB.eigenvectorUnitary : Matrix β β ℂ) with hV
  set W : Matrix γ (α × β) ℂ := (U ⊗ₖ V).submatrix e (Equiv.refl _) with hWd
  have hWc : Wᴴ = (U ⊗ₖ V)ᴴ.submatrix (Equiv.refl _) e := by
    rw [hWd, conjTranspose_submatrix]
  have hUV1 : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hV, x8_U1, x8_U1, one_kronecker_one]
  have hUV2 : (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hV, x8_U2, x8_U2, one_kronecker_one]
  have hW1 : Wᴴ * W = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hUV1, submatrix_one_equiv]
  have hW2 : W * Wᴴ = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hUV2, submatrix_one_equiv]
  set D := diagonal (fun k : α × β => ((hA.eigenvalues k.1 * hB.eigenvalues k.2 : ℝ) : ℂ)) with hD
  have hM : (A ⊗ₖ B).submatrix e e = W * D * Wᴴ := by
    have hk : A ⊗ₖ B = (U ⊗ₖ V) * D * (U ⊗ₖ V)ᴴ := by
      conv_lhs => rw [x8_spec hA, x8_spec hB]
      rw [hD, conjTranspose_kronecker, mul_kronecker_mul, mul_kronecker_mul,
        diagonal_kronecker_diagonal]
      congr 3; ext k; push_cast; rfl
    rw [hk, hWc, hWd, ← submatrix_mul_equiv _ _ e (Equiv.refl (α × β)) e,
      ← submatrix_mul_equiv _ _ e (Equiv.refl (α × β)) (Equiv.refl (α × β))]
    simp
  have hH : ((A ⊗ₖ B).submatrix e e).IsHermitian :=
    by
      have : (A ⊗ₖ B).IsHermitian := by
        rw [IsHermitian, conjTranspose_kronecker, hA.eq, hB.eq]
      exact this.submatrix e
  unfold vnEntropy
  rw [x8_trace_cfc _ hH W hW1 hW2 (fun k : α × β => hA.eigenvalues k.1 * hB.eigenvalues k.2) hM]
  rw [← vnEntropy, ← vnEntropy, x8_ent_eig hA, x8_ent_eig hB]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [Fintype.sum_prod_type]
  simp_rw [x8_flog, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    x8_sum_eig hA htA, x8_sum_eig hB htB]
  simp

end X8P33


open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open Matrix

namespace X8P33
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

def x8eS {n : ℕ} (D F : Fin n → Type) (E Z : Type) (s : Finset (Fin n)) :
    SubBasis (fun i => D i × F i) s × (E × Z) ≃ (SubBasis D s × E) × (SubBasis F s × Z) where
  toFun a := ((fun i => (a.1 i).1, a.2.1), (fun i => (a.1 i).2, a.2.2))
  invFun b := (fun i => (b.1.1 i, b.2.1 i), (b.1.2, b.2.2))
  left_inv a := rfl
  right_inv b := rfl

def x8pi {n : ℕ} (D F : Fin n → Type) :
    RegisterBasis (fun i => D i × F i) ≃ RegisterBasis D × RegisterBasis F where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv x := rfl
  right_inv p := rfl

theorem x8_split {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (f : RegisterBasis (fun i => D i × F i) → ℂ) :
    ∑ x, f x = ∑ x1 : RegisterBasis D, ∑ x2 : RegisterBasis F, f (fun i => (x1 i, x2 i)) := by
  rw [← (x8pi D F).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

theorem x8_marg_entry {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    {E Z : Type} (rho : RegisterBasis D × E → RegisterBasis D × E → ℂ)
    (sigma : RegisterBasis F × Z → RegisterBasis F × Z → ℂ) (s : Finset (Fin n))
    (a b : SubBasis (fun i => D i × F i) s × (E × Z)) :
    (∑ x : RegisterBasis (fun i => D i × F i), ∑ y : RegisterBasis (fun i => D i × F i),
      if (∀ i (hi : i ∈ s), x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧ (∀ i, i ∉ s → x i = y i) then
        rho ((fun i => (x i).1), a.2.1) ((fun i => (y i).1), b.2.1) *
          sigma ((fun i => (x i).2), a.2.2) ((fun i => (y i).2), b.2.2) else 0) =
    (∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
      if (∀ i (hi : i ∈ s), x i = (a.1 ⟨i,hi⟩).1 ∧ y i = (b.1 ⟨i,hi⟩).1) ∧
        (∀ i, i ∉ s → x i = y i) then rho (x, a.2.1) (y, b.2.1) else 0) *
    (∑ x : RegisterBasis F, ∑ y : RegisterBasis F,
      if (∀ i (hi : i ∈ s), x i = (a.1 ⟨i,hi⟩).2 ∧ y i = (b.1 ⟨i,hi⟩).2) ∧
        (∀ i, i ∉ s → x i = y i) then sigma (x, a.2.2) (y, b.2.2) else 0) := by
  rw [Finset.sum_mul_sum]
  rw [x8_split]
  simp_rw [x8_split (D := D) (F := F), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  refine Finset.sum_congr rfl fun x2 _ => ?_
  refine Finset.sum_congr rfl fun y1 _ => ?_
  refine Finset.sum_congr rfl fun y2 _ => ?_
  rw [ite_zero_mul_ite_zero]
  congr 1
  simp only [Prod.ext_iff]
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun i hi => ⟨(h1 i hi).1.1, (h1 i hi).2.1⟩, fun i hi => (h2 i hi).1⟩,
      ⟨fun i hi => ⟨(h1 i hi).1.2, (h1 i hi).2.2⟩, fun i hi => (h2 i hi).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun i hi => ⟨⟨(h1 i hi).1, (h3 i hi).1⟩, ⟨(h1 i hi).2, (h3 i hi).2⟩⟩,
      fun i hi => ⟨h2 i hi, h4 i hi⟩⟩

theorem x8_marg {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    {E Z : Type} (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ) (s : Finset (Fin n)) :
    registerMarginal (pairedProduct rho sigma) s =
      ((registerMarginal rho s) ⊗ₖ (registerMarginal sigma s)).submatrix
        (x8eS D F E Z s) (x8eS D F E Z s) := by
  ext a b
  rw [submatrix_apply, kroneckerMap_apply]
  simp only [registerMarginal, pairedProduct, x8eS, Equiv.coe_fn_mk]
  convert x8_marg_entry rho sigma s a b <;> exact if_congr Iff.rfl rfl rfl

theorem x8_sum_ite {α : Type*} [Fintype α] (c : ℂ) (P : α → Prop) [DecidablePred P] (a0 : α)
    (hP : ∀ a, P a ↔ a = a0) : ∑ a, (if P a then c else 0) = c := by
  simp [hP]

theorem x8_marg_herm {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] {E : Type}
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) (hρ : rho.IsHermitian)
    (s : Finset (Fin n)) : (registerMarginal rho s).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, registerMarginal, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [apply_ite star, star_zero]
  refine if_congr ?_ (hρ.apply _ _) rfl
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => ⟨(h1 i hi).2, (h1 i hi).1⟩, fun i hi => (h2 i hi).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => ⟨(h1 i hi).2, (h1 i hi).1⟩, fun i hi => (h2 i hi).symm⟩

theorem x8_marg_trace {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] {E : Type} [Fintype E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin n)) : Matrix.trace (registerMarginal rho s) = Matrix.trace rho := by
  simp only [trace, diag, registerMarginal]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_comm (f := fun x e => rho (x, e) (x, e))]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hy : ∀ (a1 : SubBasis D s) (x : RegisterBasis D),
      (∑ y : RegisterBasis D, if (∀ i (hi : i ∈ s), x i = a1 ⟨i,hi⟩ ∧ y i = a1 ⟨i,hi⟩) ∧
        (∀ i, i ∉ s → x i = y i) then rho (x, e) (y, e) else 0) =
      if (∀ i (hi : i ∈ s), x i = a1 ⟨i,hi⟩) then rho (x, e) (x, e) else 0 := by
    intro a1 x
    rw [Finset.sum_eq_single x]
    · exact if_congr ⟨fun h i hi => (h.1 i hi).1, fun h => ⟨fun i hi => ⟨h i hi, h i hi⟩,
        fun _ _ => rfl⟩⟩ rfl rfl
    · intro y _ hyx
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hyx
      funext i
      by_cases hi : i ∈ s
      · rw [(h1 i hi).1, (h1 i hi).2]
      · exact (h2 i hi).symm
    · intro h; exact absurd (Finset.mem_univ x) h
  simp_rw [hy]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine x8_sum_ite _ _ (fun i => x i.1) fun a1 => ⟨fun h => funext fun i => (h i.1 i.2).symm,
    fun h i hi => by rw [h]⟩

theorem x8_ent_add {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    {E Z : Type} [Fintype E] [Fintype Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (s : Finset (Fin n)) :
    entropyAt (pairedProduct rho sigma) s = entropyAt rho s + entropyAt sigma s := by
  unfold entropyAt
  rw [x8_marg]
  convert x8_ent_kron (x8_marg_herm rho hrho.1.1 s) (x8_marg_herm sigma hsigma.1.1 s)
    ((x8_marg_trace rho s).trans hrho.2) ((x8_marg_trace sigma s).trans hsigma.2) _

theorem x8_main {D F : Fin 3 → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    {E Z : Type} [Fintype E] [Fintype Z] [Nonempty E] [Nonempty Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (pairedProduct rho sigma) (singleParties 3) ∅ =
      conditionalMultipartiteInformation kind rho (singleParties 3) ∅ +
        conditionalMultipartiteInformation kind sigma (singleParties 3) ∅ := by
  intro kind
  cases kind <;>
  · simp only [conditionalMultipartiteInformation, x8_ent_add rho sigma hrho hsigma,
      Finset.sum_add_distrib]
    ring

end X8P33

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33 in
theorem solution {D F : Fin 3 → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    {E Z : Type} [Fintype E] [Fintype Z] [Nonempty E] [Nonempty Z]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (sigma : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (pairedProduct rho sigma) (singleParties 3) ∅ =
      conditionalMultipartiteInformation kind rho (singleParties 3) ∅ +
        conditionalMultipartiteInformation kind sigma (singleParties 3) ∅ :=
  X8P33.x8_main rho sigma hrho hsigma
