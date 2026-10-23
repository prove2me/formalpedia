-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.proposition1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:38:21.747159+00:00
-- url     : https://prove2.me/submissions/31b3a667-2369-42c2-b597-2287da7266d1

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


open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open Matrix

namespace X8P33
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

def x8tot {n m : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin m → Finset (Fin n)) (e : Finset (Fin n)) : ℝ :=
  (∑ i, S (a i ∪ e)) - S (allParties a ∪ e) - (m-1 : ℕ) * S e

def x8dual {n m : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin m → Finset (Fin n)) (e : Finset (Fin n)) : ℝ :=
  (∑ i, S ((Finset.univ.erase i).biUnion a ∪ e)) - (m-1 : ℕ) * S (allParties a ∪ e) - S e

theorem x8_tot_eq {n m : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] {E : Type} [Fintype E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) (a : Fin m → Finset (Fin n))
    (e : Finset (Fin n)) :
    conditionalMultipartiteInformation .total rho a e = x8tot (entropyAt rho) a e := rfl

theorem x8_dual_eq {n m : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] {E : Type} [Fintype E]
    (rho : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ) (a : Fin m → Finset (Fin n))
    (e : Finset (Fin n)) :
    conditionalMultipartiteInformation .dual rho a e = x8dual (entropyAt rho) a e := rfl

theorem x8_all2 {n : ℕ} (u v : Finset (Fin n)) : allParties ![u, v] = u ∪ v := by
  ext t; simp [allParties, Fin.exists_fin_two]

theorem x8_allAttach {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) (x : Finset (Fin n)) :
    allParties (attachFirst a x) = x ∪ allParties a := by
  ext t
  simp only [allParties, attachFirst, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    · rcases Finset.mem_union.mp hi with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨i, h'⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, by simp [h]⟩
    · by_cases h : i = 0
      · subst h; exact ⟨0, by simp [hi]⟩
      · exact ⟨i, by simp [h, hi]⟩

theorem x8_erase0 {k : ℕ} (g : Fin (k+2) → ℝ) :
    ∑ i ∈ Finset.univ.erase 0, g i = ∑ i : Fin (k+1), g i.succ := by
  have h := Finset.add_sum_erase Finset.univ g (Finset.mem_univ 0)
  rw [Fin.sum_univ_succ] at h
  linarith

theorem x8_tot2 {n : ℕ} (S : Finset (Fin n) → ℝ) (u v e : Finset (Fin n)) :
    x8tot S ![u, v] e = S (u ∪ e) + S (v ∪ e) - S (u ∪ v ∪ e) - S e := by
  simp [x8tot, x8_all2, Fin.sum_univ_two]

theorem x8_sum_attach {n k : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (k+2) → Finset (Fin n))
    (x e : Finset (Fin n)) :
    ∑ i, S (attachFirst a x i ∪ e) = S (x ∪ a 0 ∪ e) + ∑ i : Fin (k+1), S (a i.succ ∪ e) := by
  rw [Fin.sum_univ_succ]
  simp [attachFirst, Fin.succ_ne_zero]

theorem x8_c1 {n k : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) :
    x8tot S (attachFirst a x) ∅ = x8tot S a x + ∑ i ∈ Finset.univ.erase 0, x8tot S ![x, a i] ∅ := by
  rw [x8_erase0]
  simp_rw [x8_tot2]
  unfold x8tot
  rw [x8_sum_attach, x8_allAttach, Fin.sum_univ_succ (f := fun i => S (a i ∪ x))]
  simp only [Finset.union_empty, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [Finset.union_comm (a _) x, Finset.union_comm (allParties a) x]
  push_cast
  ring

def x8B {n m : ℕ} (a : Fin m → Finset (Fin n)) (t : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin m => j.val < t).biUnion a

theorem x8_B_eq {n m : ℕ} (a : Fin m → Finset (Fin n)) (i : Fin m) :
    earlierParties a i = x8B a i.val := rfl

theorem x8_B_succ {n m : ℕ} (a : Fin m → Finset (Fin n)) (i : Fin m) :
    a i ∪ x8B a i.val = x8B a (i.val + 1) := by
  ext t
  simp only [x8B, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (h | ⟨j, hj, h⟩)
    · exact ⟨i, by omega, h⟩
    · exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩
    by_cases hji : j = i
    · subst hji; exact Or.inl h
    · right; refine ⟨j, ?_, h⟩
      have : j.val ≠ i.val := fun h' => hji (Fin.ext h')
      omega

theorem x8_B_one {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) : x8B a 1 = a 0 := by
  have := x8_B_succ a 0
  have h0 : x8B a (0 : Fin (k+2)).val = ∅ := by
    ext t; simp [x8B]
  rw [h0, Finset.union_empty] at this
  exact this.symm

theorem x8_B_top {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) : x8B a (k+2) = allParties a := by
  ext t; simp [x8B, allParties]

theorem x8_tele {k : ℕ} (h : ℕ → ℝ) :
    ∑ i : Fin (k+1), (h (i.succ.val + 1) - h i.succ.val) = h (k+2) - h 1 := by
  simp only [Fin.val_succ]
  rw [Fin.sum_univ_eq_sum_range (fun i => h (i + 1 + 1) - h (i + 1)) (k+1)]
  rw [Finset.sum_range_sub (fun i => h (i + 1))]

theorem x8_c7 {n m : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (m+2) → Finset (Fin n))
    (e : Finset (Fin n)) :
    x8tot S a e = ∑ i ∈ Finset.univ.erase 0, x8tot S ![a i, earlierParties a i] e := by
  rw [x8_erase0]
  simp_rw [x8_tot2, x8_B_eq, x8_B_succ]
  have ht := x8_tele (k := m) (fun t => S (x8B a t ∪ e))
  rw [x8_B_top, x8_B_one] at ht
  unfold x8tot
  rw [Fin.sum_univ_succ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht ⊢
  push_cast
  linarith

theorem x8_c2 {n k : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) :
    x8tot S (attachFirst a x) ∅ = x8tot S a ∅ +
      ∑ i ∈ Finset.univ.erase 0, x8tot S ![x, a i] (earlierParties a i) := by
  rw [x8_erase0]
  simp_rw [x8_tot2, x8_B_eq, Finset.union_assoc x, x8_B_succ]
  have ht1 := x8_tele (k := k) (fun t => S (x ∪ x8B a t))
  have ht2 := x8_tele (k := k) (fun t => S (x8B a t))
  rw [x8_B_top, x8_B_one] at ht1 ht2
  unfold x8tot
  rw [x8_sum_attach, x8_allAttach, Fin.sum_univ_succ (f := fun i => S (a i ∪ ∅))]
  simp only [Finset.union_empty, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht1 ht2 ⊢
  push_cast
  linarith

theorem x8_C_attach0 {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) (x : Finset (Fin n)) :
    (Finset.univ.erase 0).biUnion (attachFirst a x) = laterParties a := by
  ext t
  simp only [laterParties, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
    attachFirst]
  constructor
  · rintro ⟨i, hi, h⟩; rw [if_neg hi] at h; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rw [if_neg hi]; exact h⟩

theorem x8_C_attach {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) (x : Finset (Fin n))
    (i : Fin (k+2)) (hi : i ≠ 0) :
    (Finset.univ.erase i).biUnion (attachFirst a x) = x ∪ (Finset.univ.erase i).biUnion a := by
  ext t
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
    attachFirst]
  constructor
  · rintro ⟨j, hj, h⟩
    split_ifs at h with h0
    · rcases Finset.mem_union.mp h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨j, hj, h'⟩
    · exact Or.inr ⟨j, hj, h⟩
  · rintro (h | ⟨j, hj, h⟩)
    · exact ⟨0, Ne.symm hi, by simp [h]⟩
    · by_cases h0 : j = 0
      · subst h0; exact ⟨0, hj, by simp [h]⟩
      · exact ⟨j, hj, by simp [h0, h]⟩

theorem x8_all_succ {n k : ℕ} (a : Fin (k+2) → Finset (Fin n)) :
    allParties (fun i : Fin (k+1) => a i.succ) = laterParties a := by
  ext t
  simp only [allParties, laterParties, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true]
  constructor
  · rintro ⟨i, h⟩; exact ⟨i.succ, Fin.succ_ne_zero i, h⟩
  · rintro ⟨i, hi, h⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    exact ⟨j, h⟩

theorem x8_aC {n m : ℕ} (a : Fin m → Finset (Fin n)) (x : Finset (Fin n)) (i : Fin m) :
    a i ∪ (x ∪ (Finset.univ.erase i).biUnion a) = x ∪ allParties a := by
  ext t
  simp only [allParties, Finset.mem_union, Finset.mem_biUnion, Finset.mem_erase,
    Finset.mem_univ, and_true, true_and]
  constructor
  · rintro (h | h | ⟨j, _, h⟩)
    · exact Or.inr ⟨i, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h⟩
  · rintro (h | ⟨j, h⟩)
    · exact Or.inr (Or.inl h)
    · by_cases hj : j = i
      · subst hj; exact Or.inl h
      · exact Or.inr (Or.inr ⟨j, hj, h⟩)

theorem x8_dsum_attach {n k : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (k+2) → Finset (Fin n))
    (x e : Finset (Fin n)) :
    ∑ i, S ((Finset.univ.erase i).biUnion (attachFirst a x) ∪ e) =
      S (laterParties a ∪ e) +
        ∑ i : Fin (k+1), S (x ∪ (Finset.univ.erase i.succ).biUnion a ∪ e) := by
  rw [Fin.sum_univ_succ, x8_C_attach0]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [x8_C_attach a x _ (Fin.succ_ne_zero i)]

theorem x8_c3 {n k : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) :
    x8dual S (attachFirst a x) ∅ = x8dual S a x + x8tot S ![x, laterParties a] ∅ := by
  rw [x8_tot2]
  unfold x8dual
  rw [x8_dsum_attach, x8_allAttach, Fin.sum_univ_succ
    (f := fun i => S ((Finset.univ.erase i).biUnion a ∪ x))]
  simp only [Finset.union_empty]
  have hL : (Finset.univ.erase (0 : Fin (k+2))).biUnion a = laterParties a := rfl
  rw [hL]
  simp_rw [Finset.union_comm _ x]
  push_cast
  ring

theorem x8_c4 {n k : ℕ} (S : Finset (Fin n) → ℝ) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) :
    x8dual S (attachFirst a x) ∅ = -x8tot S (fun i : Fin (k+1) => a i.succ) ∅ +
      ∑ i ∈ Finset.univ.erase 0, x8tot S ![a i, x ∪ (Finset.univ.erase i).biUnion a] ∅ := by
  rw [x8_erase0]
  simp_rw [x8_tot2, x8_aC]
  unfold x8dual x8tot
  rw [x8_dsum_attach, x8_allAttach, x8_all_succ]
  simp only [Finset.union_empty, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem x8_c6 {n j : ℕ} (S : Finset (Fin n) → ℝ) (c : Fin j → ℝ) (s : Fin j → Finset (Fin n))
    (e f : Finset (Fin n)) :
    ∑ t, c t * (S (s t ∪ (e ∪ f)) - S (e ∪ f)) =
      ∑ t, c t * ((S ((s t ∪ e) ∪ f) - S f) - (S (e ∪ f) - S f)) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.union_assoc]; ring

theorem x8_ent_block {α ι γ : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    [Fintype γ] [DecidableEq γ] (N : ι → Matrix α α ℂ) (hN : ∀ j, (N j).IsHermitian)
    (ht : ∀ j, (N j).trace = 1) (p : ι → ℝ) (e : γ ≃ α × ι) :
    vnEntropy ((blockDiagonal fun j => ((p j : ℂ) • N j)).submatrix e e) =
      -∑ j, p j * Real.logb 2 (p j) + ∑ j, p j * vnEntropy (N j) := by
  set U : ι → Matrix α α ℂ := fun j => ((hN j).eigenvectorUnitary : Matrix α α ℂ) with hU
  set BU : Matrix (α × ι) (α × ι) ℂ := blockDiagonal U with hBU
  set W : Matrix γ (α × ι) ℂ := BU.submatrix e (Equiv.refl _) with hWd
  have hWc : Wᴴ = BUᴴ.submatrix (Equiv.refl _) e := by
    rw [hWd, conjTranspose_submatrix]
  have hB1 : BUᴴ * BU = 1 := by
    rw [hBU, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hU, x8_U1]
    exact blockDiagonal_one
  have hB2 : BU * BUᴴ = 1 := by
    rw [hBU, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hU, x8_U2]
    exact blockDiagonal_one
  have hW1 : Wᴴ * W = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hB1, submatrix_one_equiv]
  have hW2 : W * Wᴴ = 1 := by
    rw [hWc, hWd, submatrix_mul_equiv, hB2, submatrix_one_equiv]
  set D := diagonal (fun k : α × ι => ((p k.2 * (hN k.2).eigenvalues k.1 : ℝ) : ℂ)) with hD
  have hM : (blockDiagonal fun j => ((p j : ℂ) • N j)).submatrix e e = W * D * Wᴴ := by
    have hk : (blockDiagonal fun j => ((p j : ℂ) • N j)) = BU * D * BUᴴ := by
      have hj : ∀ j, ((p j : ℂ) • N j) = U j *
          diagonal (fun k => ((p j * (hN j).eigenvalues k : ℝ) : ℂ)) * (U j)ᴴ := by
        intro j
        conv_lhs => rw [x8_spec (hN j)]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
        congr 3; ext k; push_cast; simp
      simp_rw [hj]
      rw [blockDiagonal_mul, blockDiagonal_mul, hD, blockDiagonal_diagonal, hBU,
        blockDiagonal_conjTranspose]
    rw [hk, hWc, hWd, ← submatrix_mul_equiv _ _ e (Equiv.refl (α × ι)) e,
      ← submatrix_mul_equiv _ _ e (Equiv.refl (α × ι)) (Equiv.refl (α × ι))]
    simp
  have hH : ((blockDiagonal fun j => ((p j : ℂ) • N j)).submatrix e e).IsHermitian := by
    have : (blockDiagonal fun j => ((p j : ℂ) • N j)).IsHermitian := by
      rw [IsHermitian, blockDiagonal_conjTranspose]
      congr 1; funext j
      rw [conjTranspose_smul, (hN j).eq]
      simp
    exact this.submatrix e
  have hE : ∀ j, vnEntropy (N j) =
      -∑ k, (hN j).eigenvalues k * Real.logb 2 ((hN j).eigenvalues k) := fun j => x8_ent_eig (hN j)
  simp_rw [hE]
  unfold vnEntropy
  rw [x8_trace_cfc _ hH W hW1 hW2 (fun k : α × ι => p k.2 * (hN k.2).eigenvalues k.1) hM]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [mul_comm (p _) ((hN _).eigenvalues _), x8_flog, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, x8_sum_eig (hN _) (ht _)]
  simp only [one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, mul_neg]
  ring

def x8eq {n : ℕ} (D : Fin n → Type) (s : Finset (Fin n)) (ell : ℕ) :
    SubBasis D s × Fin ell ≃ (SubBasis D s × Unit) × Fin ell where
  toFun a := ((a.1, ()), a.2)
  invFun b := (b.1.1, b.2)
  left_inv a := rfl
  right_inv b := rfl

theorem x8_cq_entry {n ell : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] (p : Fin ell → ℝ)
    (r : Fin ell → RegisterBasis D → RegisterBasis D → ℂ) (s : Finset (Fin n))
    (a b : SubBasis D s × Fin ell) :
    (∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
      if (∀ i (hi : i ∈ s), x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧ (∀ i, i ∉ s → x i = y i) then
        (if a.2 = b.2 then (p a.2 : ℂ) * r a.2 x y else 0) else 0) =
    if a.2 = b.2 then (p a.2 : ℂ) * ∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
      (if (∀ i (hi : i ∈ s), x i = a.1 ⟨i,hi⟩ ∧ y i = b.1 ⟨i,hi⟩) ∧ (∀ i, i ∉ s → x i = y i) then
        r a.2 x y else 0) else 0 := by
  split_ifs with h
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  · simp

theorem x8_cq_marg {n ell : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] (p : Fin ell → ℝ)
    (r : Fin ell → Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) :
    registerMarginal (E := Fin ell)
      (fun u v => if u.2 = v.2 then (p u.2 : ℂ) * r u.2 u.1 v.1 else 0) s =
    (blockDiagonal fun j => (p j : ℂ) • registerMarginal (trivialExtension (r j)) s).submatrix
      (x8eq D s ell) (x8eq D s ell) := by
  ext a b
  have hE := x8_cq_entry p (fun j => r j) s a b
  rw [submatrix_apply, blockDiagonal_apply]
  by_cases h : a.2 = b.2
  · rw [if_pos (show (x8eq D s ell a).2 = (x8eq D s ell b).2 from h), Matrix.smul_apply,
      smul_eq_mul]
    rw [if_pos h] at hE
    convert hE using 1
    · unfold registerMarginal
      congr 1
    · congr 1
  · rw [if_neg (show ¬ (x8eq D s ell a).2 = (x8eq D s ell b).2 from h)]
    rw [if_neg h] at hE
    refine Eq.trans ?_ hE
    unfold registerMarginal
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    exact if_congr Iff.rfl rfl rfl

theorem x8_triv_herm {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hr : r.IsHermitian) :
    (trivialExtension r).IsHermitian := by
  ext a b
  simp only [trivialExtension, conjTranspose_apply]
  exact hr.apply _ _

theorem x8_triv_trace {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (r : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    Matrix.trace (trivialExtension r) = Matrix.trace r := by
  simp only [Matrix.trace, diag, trivialExtension, Fintype.sum_prod_type, Finset.univ_unique,
    Finset.sum_singleton]

theorem x8_cq_ent {n ell : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] (p : Fin ell → ℝ)
    (r : Fin ell → Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hr : ∀ j, IsDensityMatrix (r j)) (s : Finset (Fin n)) :
    entropyAt (E := Fin ell) (fun u v => if u.2 = v.2 then (p u.2 : ℂ) * r u.2 u.1 v.1 else 0) s =
      -∑ j, p j * Real.logb 2 (p j) + ∑ j, p j * entropyAt (trivialExtension (r j)) s := by
  unfold entropyAt
  rw [x8_cq_marg]
  convert x8_ent_block (fun j => registerMarginal (trivialExtension (r j)) s)
    (fun j => x8_marg_herm _ (x8_triv_herm _ (hr j).1.1) s)
    (fun j => (x8_marg_trace _ s).trans ((x8_triv_trace _).trans (hr j).2)) p (x8eq D s ell)

theorem x8_c5 (m : ℕ) (D F : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    (E Z : Type) [Fintype E] [Fintype Z]
    (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ)
    (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) (kind : InformationKind) :
    conditionalMultipartiteInformation kind (pairedProduct r s) (singleParties m) ∅ =
      conditionalMultipartiteInformation kind r (singleParties m) ∅ +
        conditionalMultipartiteInformation kind s (singleParties m) ∅ := by
  cases kind <;>
  · simp only [conditionalMultipartiteInformation, x8_ent_add r s hr hs, Finset.sum_add_distrib]
    ring

theorem x8_c8 {n k ell : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (a : Fin (k+2) → Finset (Fin n)) (p : Fin ell → ℝ)
    (r : Fin ell → Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (cq : Matrix (RegisterBasis D × Fin ell) (RegisterBasis D × Fin ell) ℂ)
    (hc : ∀ s, entropyAt cq s =
      -∑ j, p j * Real.logb 2 (p j) + ∑ j, p j * entropyAt (trivialExtension (r j)) s)
    (hp1 : ∑ j, p j = 1) (kind : InformationKind) :
    conditionalMultipartiteInformation kind cq a ∅ = ∑ j, p j * info kind (r j) a ∅ := by
  have hk : (k + 2 - 1 : ℕ) = k + 1 := by omega
  cases kind
  · rw [x8_tot_eq]
    simp only [info, x8_tot_eq, x8tot, hc, hk]
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun i j => p j * entropyAt (trivialExtension (r j)) (a i ∪ ∅))]
    simp_rw [mul_left_comm (p _) ((k + 1 : ℕ) : ℝ)]
    rw [← Finset.mul_sum (s := Finset.univ) (f := fun j => p j * entropyAt (trivialExtension (r j)) ∅)]
    push_cast
    ring
  · rw [x8_dual_eq]
    simp only [info, x8_dual_eq, x8dual, hc, hk]
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun i j => p j * entropyAt (trivialExtension (r j))
      ((Finset.univ.erase i).biUnion a ∪ ∅))]
    simp_rw [mul_left_comm (p _) ((k + 1 : ℕ) : ℝ)]
    rw [← Finset.mul_sum (s := Finset.univ)
      (f := fun j => p j * entropyAt (trivialExtension (r j)) (allParties a ∪ ∅))]
    push_cast
    ring

end X8P33

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33 in
theorem solution {n k : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a : Fin (k+2) → Finset (Fin n))
    (x : Finset (Fin n)) (hdis : DisjointRegisters a x) :
    (info .total rho (attachFirst a x) ∅ = info .total rho a x +
      ∑ i ∈ Finset.univ.erase 0, info .total rho ![x,a i] ∅) ∧
    (info .total rho (attachFirst a x) ∅ = info .total rho a ∅ +
      ∑ i ∈ Finset.univ.erase 0, info .total rho ![x,a i] (earlierParties a i)) ∧
    (info .dual rho (attachFirst a x) ∅ = info .dual rho a x +
      info .total rho ![x,laterParties a] ∅) ∧
    (info .dual rho (attachFirst a x) ∅ =
      -info .total rho (fun i : Fin (k+1) => a i.succ) ∅ +
      ∑ i ∈ Finset.univ.erase 0,
        info .total rho ![a i,x ∪ (Finset.univ.erase i).biUnion a] ∅) ∧
    (∀ (m : ℕ) (D F : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
      [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
      (E Z : Type) [Fintype E] [Fintype Z] [Nonempty E] [Nonempty Z]
      (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
      (s : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ),
      2 ≤ m → IsDensityMatrix r → IsDensityMatrix s → ∀ kind : InformationKind,
      conditionalMultipartiteInformation kind (pairedProduct r s) (singleParties m) ∅ =
        conditionalMultipartiteInformation kind r (singleParties m) ∅ + conditionalMultipartiteInformation kind s (singleParties m) ∅) ∧
    (∀ (j : ℕ) (c : Fin j → ℝ) (s : Fin j → Finset (Fin n))
      (e f : Finset (Fin n)),
      entropyExpression (trivialExtension rho) c s (e ∪ f) =
        twiceConditioned (trivialExtension rho) c s e f) ∧
    (∀ (m : ℕ) (a : Fin (m+2) → Finset (Fin n)) (e : Finset (Fin n)),
      DisjointRegisters a e → info .total rho a e =
        ∑ i ∈ Finset.univ.erase 0,
          info .total rho ![a i,earlierParties a i] e) ∧
    (∀ (ell : ℕ) (p : Fin ell → ℝ)
      (r : Fin ell → Matrix (RegisterBasis D) (RegisterBasis D) ℂ),
      (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → (∀ j, IsDensityMatrix (r j)) →
      ∀ kind : InformationKind,
      let cq : Matrix (RegisterBasis D × Fin ell) (RegisterBasis D × Fin ell) ℂ :=
        fun u v => if u.2 = v.2 then (p u.2 : ℂ) * r u.2 u.1 v.1 else 0
      conditionalMultipartiteInformation kind cq a ∅ = ∑ j, p j * info kind (r j) a ∅) := by
  refine ⟨X8P33.x8_c1 _ a x, X8P33.x8_c2 _ a x, X8P33.x8_c3 _ a x, X8P33.x8_c4 _ a x, ?_, ?_, ?_, ?_⟩
  · intro m D F _ _ _ _ E Z _ _ _ _ r s _ hr hs kind
    exact X8P33.x8_c5 m D F E Z r s hr hs kind
  · intro j c s e f
    exact X8P33.x8_c6 _ c s e f
  · intro m a e _
    exact X8P33.x8_c7 _ a e
  · intro ell p r _ hp1 hr kind
    exact X8P33.x8_c8 a p r _ (X8P33.x8_cq_ent p r hr) hp1 kind

