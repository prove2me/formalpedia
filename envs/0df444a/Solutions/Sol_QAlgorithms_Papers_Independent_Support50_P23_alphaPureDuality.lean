-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.alphaPureDuality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:00:24.810993+00:00
-- url     : https://prove2.me/submissions/bd22c907-0a78-432a-bb1e-c0da015abe87

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib

section X5mod_AI_Base
open Matrix

section X5mod_AI_Base

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_finite_cont' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  M.finite_real_spectrum.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

/-- identity tensor X as a star algebra hom -/
noncomputable def x5ai_kronHom (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (C × n) (C × n) ℂ where
  toFun X := Matrix.kronecker (1 : Matrix C C ℂ) X
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    have := Matrix.mul_kronecker_mul (1 : Matrix C C ℂ) (1 : Matrix C C ℂ) X Y
    rw [Matrix.mul_one] at this
    exact this
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem x5ai_kron (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.kronecker (1 : Matrix C C ℂ) M) = Matrix.kronecker (1 : Matrix C C ℂ) (cfc f M) := by
  have hK : (Matrix.kronecker (1 : Matrix C C ℂ) M).IsHermitian := by
    simp [IsHermitian, Matrix.conjTranspose_kronecker, hM.eq]
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_kronHom C (n := n)) f M (x5ai_finite_cont' M f)
    (by
      change Continuous fun X : Matrix n n ℂ => Matrix.kronecker (1 : Matrix C C ℂ) X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _)))
    hM.isSelfAdjoint hK.isSelfAdjoint
  exact h.symm

end X5mod_AI_Base
end X5mod_AI_Base

section X5mod_AD_Kron
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aeval_diag (δ : ι → ℂ) (p : ℝ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => aeval (δ k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
    rfl

lemma cfc_diag (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => ((d k : ℝ) : ℂ))) = diagonal (fun k => ((f (d k) : ℝ) : ℂ)) := by
  set D := diagonal (fun k => ((d k : ℝ) : ℂ))
  have hfin : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := Finset.univ.image d ∪ hfin.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have hD : IsSelfAdjoint D := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  have h1 : cfc f D = cfc (fun x => p.eval x) D :=
    cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial p D hD, aeval_diag]
  congr 1; ext k
  rw [show ((d k : ℝ) : ℂ) = algebraMap ℝ ℂ (d k) from rfl, aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval,
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
  rfl

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((hX.eigenvalues k : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma cfc_spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((f (hX.eigenvalues k) : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma uu {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem cfc_kron {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = f x * f y) :
    cfc f (X ⊗ₖ Y) = cfc f X ⊗ₖ cfc f Y := by
  have hXh := hX.isHermitian
  have hYh := hY.isHermitian
  set U := (hXh.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hYh.eigenvectorUnitary : Matrix κ κ ℂ)
  set d := hXh.eigenvalues
  set e := hYh.eigenvalues
  have hW : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, uu hXh, uu hYh, one_kronecker_one]
  have hDE : diagonal (fun k => ((d k : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((e k : ℝ) : ℂ)) =
      diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p; simp
  have hXY : X ⊗ₖ Y = (U ⊗ₖ V) * diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [spec hXh, spec hYh]
    rw [← hDE, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hDh : (diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  rw [hXY, x5ai_conj (U ⊗ₖ V) hW _ hDh f hf0, cfc_diag (fun p : ι × κ => d p.1 * e p.2) f,
    cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((f (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((f (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p
    simp [hmul _ _ (hd p.1) (he p.2)]
  rw [hDE', conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X5AD
end X5mod_AD_Kron

section X5mod_DU_Base
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5DU
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma interp {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : ∃ p : ℝ[X], cfc f X = aeval X p ∧ cfc f Y = aeval Y p := by
  have hfX : (spectrum ℝ X).Finite := X.finite_real_spectrum
  have hfY : (spectrum ℝ Y).Finite := Y.finite_real_spectrum
  set s : Finset ℝ := hfX.toFinset ∪ hfY.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  refine ⟨p, ?_, ?_⟩
  · rw [← cfc_polynomial p X hX.isSelfAdjoint]
    exact cfc_congr fun x hx => (hp x (Finset.mem_union_left _ (hfX.mem_toFinset.2 hx))).symm
  · rw [← cfc_polynomial p Y hY.isSelfAdjoint]
    exact cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfY.mem_toFinset.2 hx))).symm

lemma aeval_intertwine (P : Matrix m n ℂ) (p : ℝ[X]) :
    aeval (P * Pᴴ) p * P = P * aeval (Pᴴ * P) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul]
    congr 1
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, Matrix.mul_assoc P Pᴴ P, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]

theorem cfc_intertwine (P : Matrix m n ℂ) (f : ℝ → ℝ) :
    cfc f (P * Pᴴ) * P = P * cfc f (Pᴴ * P) := by
  obtain ⟨p, h1, h2⟩ := interp (isHermitian_mul_conjTranspose_self P)
    (isHermitian_conjTranspose_mul_self P) f
  rw [h1, h2, aeval_intertwine]

lemma aeval_transpose (X : Matrix m m ℂ) (p : ℝ[X]) : aeval Xᵀ p = (aeval X p)ᵀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, transpose_add, hp, hq]
  | monomial k c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, transpose_smul,
      Matrix.one_mul, transpose_pow]

theorem cfc_transpose {X : Matrix m m ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f Xᵀ = (cfc f X)ᵀ := by
  obtain ⟨p, h1, h2⟩ := interp hX.transpose hX f
  rw [h1, h2, aeval_transpose]

end X5DU
end X5mod_DU_Base

section X5mod_AD_Prod
open Matrix
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- regrouping (A×C)×(B×D) → (A×B)×(C×D) -/
def eR : (A × C) × (B × D) ≃ (A × B) × (C × D) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def Pm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (e : m ≃ n) : Matrix m n ℂ :=
  fun x y => if e x = y then 1 else 0

lemma Pm_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (e : m ≃ n) (M : Matrix n n ℂ) :
    Pm e * M * (Pm e)ᴴ = M.submatrix e e := by
  ext x y
  simp [Pm, mul_apply, conjTranspose_apply]

lemma Pm_iso {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    (Pm e)ᴴ * Pm e = 1 := by
  ext k l
  simp only [Pm, mul_apply, conjTranspose_apply, one_apply]
  have : ∀ x, (star (if e x = k then (1 : ℂ) else 0)) * (if e x = l then 1 else 0) =
      if x = e.symm k then (if k = l then 1 else 0) else 0 := by
    intro x
    by_cases hx : x = e.symm k
    · subst hx; simp
    · have : e x ≠ k := fun h => hx (by rw [← h]; simp)
      simp [this, hx]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable (A B C D) in
noncomputable def PR : Matrix ((A × C) × (B × D)) ((A × B) × (C × D)) ℂ := Pm eR

lemma PR_conj (M : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) :
    PR A B C D * M * (PR A B C D)ᴴ = M.submatrix eR eR := Pm_conj eR M

lemma PR_iso : (PR A B C D)ᴴ * PR A B C D = 1 := Pm_iso eR

lemma iP_eq (rho : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × D) (C × D) ℂ) :
    independentProduct rho tau = PR A B C D * (rho ⊗ₖ tau) * (PR A B C D)ᴴ := by
  rw [PR_conj]; rfl

lemma iT_eq (sigma : Matrix B B ℂ) (omega : Matrix D D ℂ) :
    identityTensorReference (A := A × C) (sigma ⊗ₖ omega) =
      PR A B C D * (identityTensorReference (A := A) sigma ⊗ₖ identityTensorReference (A := C) omega) *
        (PR A B C D)ᴴ := by
  rw [PR_conj]
  ext ⟨⟨a, c⟩, ⟨b, d⟩⟩ ⟨⟨a', c'⟩, ⟨b', d'⟩⟩
  simp only [identityTensorReference, submatrix_apply, kronecker_apply, one_apply, eR,
    Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hc : c = c' <;> simp [ha, hc]

/-- the trace functional behind finiteAlpha -/
noncomputable def Tr {I : Type*} [Fintype I] [DecidableEq I] (R N : Matrix I I ℂ) (t : ℝ) : ℂ :=
  (cfc (fun x : ℝ => x ^ t) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace

lemma f_mul (t : ℝ) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x * y) ^ t = x ^ t * y ^ t :=
  fun x y hx hy => Real.mul_rpow hx hy

lemma g_mul (t : ℝ) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) (x * y) =
      (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) x * (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) y := by
  intro x y hx hy
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  simp [h0, h1, Real.mul_rpow hx hy]

lemma Tr_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (K1 K2 : Matrix n n ℂ) (h1 : K1.IsHermitian) (h2 : K2.IsHermitian) (t : ℝ) (ht : 0 < t) :
    Tr (Pm e * K1 * (Pm e)ᴴ) (Pm e * K2 * (Pm e)ᴴ) t = Tr K1 K2 t := by
  unfold Tr
  rw [x5ai_conj (Pm e) (Pm_iso e) K1 h1 _ (Real.zero_rpow ht.ne' : (0:ℝ) ^ t = 0),
    x5ai_conj (Pm e) (Pm_iso e) K2 h2 _ (by simp)]
  have : Pm e * cfc (fun x : ℝ => x ^ t) K1 * (Pm e)ᴴ *
      (Pm e * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) K2 * (Pm e)ᴴ) =
      Pm e * (cfc (fun x : ℝ => x ^ t) K1 * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) K2) *
        (Pm e)ᴴ := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (Pm e)ᴴ (Pm e), Pm_iso, Matrix.one_mul]
  rw [this, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Pm_iso, Matrix.mul_one]

lemma Tr_kron {X1 Y1 : Matrix (A × B) (A × B) ℂ} {X2 Y2 : Matrix (C × D) (C × D) ℂ}
    (hX1 : X1.PosSemidef) (hY1 : Y1.PosSemidef) (hX2 : X2.PosSemidef) (hY2 : Y2.PosSemidef)
    (t : ℝ) (ht : 0 < t) :
    Tr (X1 ⊗ₖ X2) (Y1 ⊗ₖ Y2) t = Tr X1 Y1 t * Tr X2 Y2 t := by
  unfold Tr
  rw [cfc_kron hX1 hX2 _ (Real.zero_rpow ht.ne' : (0:ℝ) ^ t = 0) (f_mul t), cfc_kron hY1 hY2 _ (by simp) (g_mul t),
    ← mul_kronecker_mul, trace_kronecker]

lemma iP_psd {rho : Matrix (A × B) (A × B) ℂ} {tau : Matrix (C × D) (C × D) ℂ}
    (h1 : rho.PosSemidef) (h2 : tau.PosSemidef) : (independentProduct rho tau).PosSemidef := by
  rw [iP_eq]; exact (h1.kronecker h2).mul_mul_conjTranspose_same _

lemma iP_density {rho : Matrix (A × B) (A × B) ℂ} {tau : Matrix (C × D) (C × D) ℂ}
    (h1 : IsDensityMatrix rho) (h2 : IsDensityMatrix tau) : IsDensityMatrix (independentProduct rho tau) := by
  refine ⟨iP_psd h1.1 h2.1, ?_⟩
  rw [iP_eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, PR_iso, Matrix.mul_one,
    trace_kronecker, h1.2, h2.2, one_mul]

lemma kron_density {sigma : Matrix B B ℂ} {omega : Matrix D D ℂ}
    (h1 : IsDensityMatrix sigma) (h2 : IsDensityMatrix omega) : IsDensityMatrix (sigma ⊗ₖ omega) :=
  ⟨h1.1.kronecker h2.1, by rw [trace_kronecker, h1.2, h2.2, one_mul]⟩

end X5AD
end X5mod_AD_Prod

section X5mod_DU_Q
open Matrix
open scoped ComplexOrder Kronecker ComplexConjugate

namespace X5DU
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
  [DecidableEq C]

def Ψ (psi : EuclideanSpace ℂ ((A × B) × C)) : Matrix (A × B) C ℂ := Matrix.of fun x c => psi (x, c)
def Φ (psi : EuclideanSpace ℂ ((A × B) × C)) : Matrix (A × C) B ℂ :=
  Matrix.of fun y b => psi ((y.1, b), y.2)

variable (psi : EuclideanSpace ℂ ((A × B) × C))

lemma rAB : traceRight (pureDensity psi) = Ψ psi * (Ψ psi)ᴴ := by
  ext x y; simp [traceRight, pureDensity, Ψ, mul_apply]

lemma rAC : traceMiddleABC (pureDensity psi) = Φ psi * (Φ psi)ᴴ := by
  ext x y; simp [traceMiddleABC, pureDensity, Φ, mul_apply]

lemma rB : traceLeft (Ψ psi * (Ψ psi)ᴴ) = ((Φ psi)ᴴ * Φ psi)ᵀ := by
  ext b b'; simp [traceLeft, Ψ, Φ, mul_apply, Fintype.sum_prod_type, mul_comm]

lemma rC : traceLeft (Φ psi * (Φ psi)ᴴ) = ((Ψ psi)ᴴ * Ψ psi)ᵀ := by
  ext c c'
  simp only [traceLeft, Ψ, Φ, mul_apply, Fintype.sum_prod_type, of_apply, conjTranspose_apply,
    transpose_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

omit [DecidableEq C] in
lemma tr_kron {X : Matrix (A × B) (A × B) ℂ} (M : Matrix B B ℂ) :
    (X * ((1 : Matrix A A ℂ) ⊗ₖ M)).trace = ∑ a, ∑ b, ∑ b', X (a, b) (a, b') * M b' b := by
  simp only [trace, diag, mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma idx (H : Matrix C C ℂ) (G : Matrix B B ℂ) :
    (Ψ psi * H * (Ψ psi)ᴴ * ((1 : Matrix A A ℂ) ⊗ₖ Gᵀ)).trace =
      (Φ psi * G * (Φ psi)ᴴ * ((1 : Matrix A A ℂ) ⊗ₖ Hᵀ)).trace := by
  rw [tr_kron, tr_kron]
  simp only [mul_apply, transpose_apply, Ψ, Φ, of_apply, conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- LHS order b b' c' c ; RHS order c c' b' b
  have e1 : ∀ (F : B → B → C → C → ℂ), ∑ b, ∑ b', ∑ c', ∑ c, F b b' c' c =
      ∑ c, ∑ c', ∑ b', ∑ b, F b b' c' c := by
    intro F
    calc ∑ b, ∑ b', ∑ c', ∑ c, F b b' c' c = ∑ b, ∑ b', ∑ c, ∑ c', F b b' c' c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ b', ∑ c', F b b' c' c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ b', ∑ c', F b b' c' c := Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ c', ∑ b', F b b' c' c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ c', ∑ b, ∑ b', F b b' c' c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ c', ∑ b', ∑ b, F b b' c' c :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [e1]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ =>
    Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C] in
lemma cfc_split {m : Type*} [Fintype m] [DecidableEq m] {X : Matrix m m ℂ} (hX : X.PosSemidef)
    (s : ℝ) (hs : 0 < s) :
    cfc (fun x : ℝ => x ^ s) X = cfc (fun x : ℝ => if x = 0 then 0 else x ^ (s - 1)) X * X := by
  have hsa := hX.isHermitian.isSelfAdjoint
  calc cfc (fun x : ℝ => x ^ s) X
        = cfc (fun x : ℝ => (if x = 0 then 0 else x ^ (s - 1)) * x) X := by
          refine cfc_congr fun x hx => ?_
          rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
          obtain ⟨i, rfl⟩ := hx
          have h0 := hX.eigenvalues_nonneg i
          split_ifs with h
          · rw [h, Real.zero_rpow hs.ne', zero_mul]
          · rw [Real.rpow_sub_one h, div_mul_cancel₀ _ h]
    _ = cfc (fun x : ℝ => if x = 0 then 0 else x ^ (s - 1)) X * cfc (fun x : ℝ => x) X :=
          cfc_mul _ _ X (x5ai_finite_cont' X _) (x5ai_finite_cont' X _)
    _ = _ := by rw [cfc_id' ℝ X hsa]

theorem Q_eq (t : ℝ) (ht0 : 0 < t) (ht2 : t < 2) :
    X5AD.Tr (traceRight (pureDensity psi))
        (identityTensorReference (A := A) (traceLeft (traceRight (pureDensity psi)))) t =
      X5AD.Tr (traceMiddleABC (pureDensity psi))
        (identityTensorReference (A := A) (traceLeft (traceMiddleABC (pureDensity psi)))) (2 - t) := by
  have hB : ((Φ psi)ᴴ * Φ psi).IsHermitian := isHermitian_conjTranspose_mul_self _
  have hC : ((Ψ psi)ᴴ * Ψ psi).IsHermitian := isHermitian_conjTranspose_mul_self _
  simp only [X5AD.Tr, identityTensorReference]
  rw [rAB, rAC, rB, rC, x5ai_kron A _ hB.transpose, x5ai_kron A _ hC.transpose, cfc_transpose hB,
    cfc_transpose hC, cfc_split (posSemidef_self_mul_conjTranspose (Ψ psi)) t ht0,
    cfc_split (posSemidef_self_mul_conjTranspose (Φ psi)) (2 - t) (by linarith)]
  have e1 : (fun x : ℝ => if x = 0 then 0 else x ^ (t - 1)) =
      (fun x : ℝ => if x = 0 then 0 else x ^ (1 - (2 - t))) := by
    funext x; rw [show 1 - (2 - t) = t - 1 by ring]
  have e2 : (fun x : ℝ => if x = 0 then 0 else x ^ (2 - t - 1)) =
      (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) := by
    funext x; rw [show 2 - t - 1 = 1 - t by ring]
  rw [e1, e2, ← Matrix.mul_assoc (cfc _ _) (Ψ psi), cfc_intertwine,
    ← Matrix.mul_assoc (cfc _ _) (Φ psi), cfc_intertwine]
  exact idx psi _ _

end X5DU
end X5mod_DU_Q

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- overlap matrix of the two eigenbases -/
noncomputable def ov {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) : Matrix I I ℂ :=
  star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hN.eigenvectorUnitary : Matrix I I ℂ)

noncomputable def w {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) : ℝ :=
  ‖ov hR hN i j‖ ^ 2

lemma ov_unitary {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) :
    ov hR hN * star (ov hR hN) = 1 := by
  unfold ov
  have hU : star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hR.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hV : (hN.eigenvectorUnitary : Matrix I I ℂ) * star (hN.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (hN.eigenvectorUnitary : Matrix I I ℂ),
    hV, Matrix.one_mul, hU]

lemma w_row {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i : I) :
    ∑ j, w hR hN i j = 1 := by
  have h := congrFun (congrFun (ov_unitary hR hN) i) i
  rw [mul_apply, one_apply_eq] at h
  have : (∑ j, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj']
  exact_mod_cast this

lemma w_nonneg {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    0 ≤ w hR hN i j := by unfold w; positivity

lemma tr_cfc_cfc {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f R * cfc g N).trace =
      ∑ i, ∑ j, ((f (hR.eigenvalues i) * g (hN.eigenvalues j) * w hR hN i j : ℝ) : ℂ) := by
  rw [hR.cfc_eq, hN.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  set Df := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR.eigenvalues)
  set Dg := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hN.eigenvalues)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hR.eigenvectorUnitary).2
  have : (U * Df * star U * (V * Dg * star V)).trace = (Df * (star U * V) * Dg * star (star U * V)).trace := by
    rw [star_mul, star_star]
    rw [show U * Df * star U * (V * Dg * star V) = U * (Df * (star U * V) * Dg * (star V * U)) * star U by
      simp only [Matrix.mul_assoc]; rw [hU']; simp]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [this]
  change (Df * ov hR hN * Dg * star (ov hR hN)).trace = _
  have hE : ∀ i k, (Df * ov hR hN * Dg) i k =
      ((f (hR.eigenvalues i) : ℝ) : ℂ) * ov hR hN i k * ((g (hN.eigenvalues k) : ℝ) : ℂ) := by
    intro i k; simp [Df, Dg, diagonal_mul, mul_diagonal]
  simp only [Matrix.trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, star_apply]
  simp only [w, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.mul_conj', RCLike.star_def]
  ring

lemma ov_apply {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    ov hR hN i j = star (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hN.eigenvectorBasis j).ofLp := by
  simp only [ov, mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, dotProduct, Pi.star_apply]

lemma supp_fwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin) (i j : I)
    (hi : hR.eigenvalues i ≠ 0) (hj : hN.eigenvalues j = 0) : ov hR hN i j = 0 := by
  set b := (hR.eigenvectorBasis i).ofLp
  set v := (hN.eigenvectorBasis j).ofLp
  have hNv : N *ᵥ v = 0 := by rw [hN.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hRv : R *ᵥ v = 0 := by
    have := h (show v ∈ LinearMap.ker N.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have key : ((hR.eigenvalues i : ℝ) : ℂ) * (star b ⬝ᵥ v) = 0 := by
    have hb : R *ᵥ b = hR.eigenvalues i • b := hR.mulVec_eigenvectorBasis i
    have : star (R *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (R *ᵥ v) := by
      rw [star_mulVec, hR.eq, dotProduct_mulVec]
    rw [hRv, dotProduct_zero, hb, star_smul] at this
    rw [← this, smul_dotProduct]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [ov_apply]
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (by exact_mod_cast h1) hi
  · exact h1

lemma spec_mulVec {R : Matrix I I ℂ} (hR : R.IsHermitian) (x : I → ℂ) :
    R *ᵥ x = (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ
      (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x)) := by
  conv_lhs => rw [hR.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]

lemma supp_bwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ i j, hR.eigenvalues i ≠ 0 → hN.eigenvalues j = 0 → ov hR hN i j = 0) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  have hV' : star V * V = 1 := Unitary.star_mul_self_of_mem (hN.eigenvectorUnitary).2
  set c := star V *ᵥ x
  have hc : ∀ j, hN.eigenvalues j ≠ 0 → c j = 0 := by
    intro j hj
    have h1 : star V *ᵥ (N *ᵥ x) = 0 := by rw [hx, mulVec_zero]
    rw [spec_mulVec hN, mulVec_mulVec, hV', one_mulVec] at h1
    have := congrFun h1 j
    rw [mulVec_diagonal] at this
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd (by simpa using h2) hj
    · exact h2
  have hUx : star U *ᵥ x = ov hR hN *ᵥ c := by
    rw [show ov hR hN = star U * V from rfl, mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hD : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star U *ᵥ x) = 0 := by
    ext i
    rw [hUx, mulVec_diagonal, Pi.zero_apply]
    by_cases hi : hR.eigenvalues i = 0
    · simp [hi]
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      by_cases hj : hN.eigenvalues j = 0
      · rw [h i j hi hj, zero_mul]
      · rw [hc j hj, mul_zero]
  rw [spec_mulVec hR, hD, mulVec_zero]

end X5OL
end X5mod_OL_Base

section X5mod_OL_Main
open Matrix Filter
open scoped ComplexOrder Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- the scalar function behind tr(ρ^α N^{1-α}) -/
noncomputable def Φ (ν μ : I → ℝ) (W : I → I → ℝ) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (α * Real.log (ν i) + (1 - α) * Real.log (μ j)) else 0

noncomputable def Φ' (ν μ : I → ℝ) (W : I → I → ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i * (Real.log (ν i) - Real.log (μ j)) else 0

lemma Φ_deriv (ν μ : I → ℝ) (W : I → I → ℝ) : HasDerivAt (Φ ν μ W) (Φ' ν μ W) 1 := by
  unfold Φ Φ'
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  split_ifs with h
  · have h1 : HasDerivAt (fun α : ℝ => α * Real.log (ν i) + (1 - α) * Real.log (μ j))
        (Real.log (ν i) - Real.log (μ j)) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).mul_const (Real.log (ν i))).add
        (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ))).mul_const (Real.log (μ j)))
      exact this.congr_deriv (by ring)
    have h2 := (h1.exp).const_mul (W i j)
    refine h2.congr_deriv ?_
    simp only [one_mul, sub_self, zero_mul, add_zero, Real.exp_log h.1]
    ring
  · exact hasDerivAt_const _ _

lemma Φ_cont (ν μ : I → ℝ) (W : I → I → ℝ) : Continuous (Φ ν μ W) := by
  unfold Φ
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

lemma Φ_one (ν μ : I → ℝ) (W : I → I → ℝ) :
    Φ ν μ W 1 = ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0 := by
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · simp [Real.exp_log h.1]
  · rfl

lemma tr_alpha {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (hR0 : ∀ i, 0 ≤ hR.eigenvalues i) (hN0 : ∀ j, 0 ≤ hN.eigenvalues j) (α : ℝ) (hα : 0 < α) :
    (cfc (fun x : ℝ => x ^ α) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - α)) N).trace.re =
      Φ hR.eigenvalues hN.eigenvalues (w hR hN) α := by
  rw [tr_cfc_cfc hR hN, Complex.re_sum]
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_re]
  rcases (hR0 i).lt_or_eq with hi | hi
  · rcases (hN0 j).lt_or_eq with hj | hj
    · rw [if_neg hj.ne', if_pos ⟨hi, hj⟩, Real.rpow_def_of_pos hi, Real.rpow_def_of_pos hj, ← Real.exp_add]
      ring_nf
    · rw [← hj]; simp
  · rw [← hi]; simp [Real.zero_rpow hα.ne']

section scalar
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j)
  (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
include hν hμ hrow

lemma Φ_one_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) : Φ ν μ W 1 = ∑ i, ν i := by
  rw [Φ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_congr rfl fun j _ => ?_).trans
    (show ∑ j, ν i * W i j = ν i by rw [← Finset.mul_sum, hrow, mul_one])
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm, mul_zero]
  · rw [if_neg (fun h => h.1.ne hi), ← hi, zero_mul]

lemma value_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) :
    (∑ i, ∑ j, ν i * Real.logb 2 (μ j) * W i j) + -∑ i, ν i * Real.logb 2 (ν i) =
      -Φ' ν μ W / Real.log 2 := by
  unfold Φ'
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ν i * Real.logb 2 (ν i) = ∑ j, ν i * Real.logb 2 (ν i) * W i j by
      rw [← Finset.mul_sum, hrow, mul_one]]
  rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; unfold Real.logb; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm]; simp
  · rw [if_neg (fun h => h.1.ne hi), ← hi]; simp

include hW in
lemma Φ_one_lt (hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0) : Φ ν μ W 1 < ∑ i, ν i := by
  obtain ⟨i0, j0, hi0, hj0, hw0⟩ := hex
  rw [Φ_one]
  have hle : ∀ i j, (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) ≤ W i j * ν i := by
    intro i j; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hW i j) (hν i)
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · calc _ ≤ ∑ j, W i j * ν i := Finset.sum_le_sum fun j _ => hle i j
      _ = ν i := by rw [← Finset.sum_mul, hrow, one_mul]
  · calc _ < ∑ j, W i0 j * ν i0 := by
          refine Finset.sum_lt_sum (fun j _ => hle i0 j) ⟨j0, Finset.mem_univ _, ?_⟩
          rw [if_neg (fun h => h.2.ne' hj0)]
          exact mul_pos ((hW i0 j0).lt_of_ne (Ne.symm hw0)) ((hν i0).lt_of_ne (Ne.symm hi0))
      _ = ν i0 := by rw [← Finset.sum_mul, hrow, one_mul]

omit hrow in
include hW in
lemma Φ_zero (h0 : Φ ν μ W 1 = 0) (α : ℝ) : Φ ν μ W α = 0 := by
  rw [Φ_one] at h0
  have hnn : ∀ i j, 0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hW i j) (hν i)
    · exact le_rfl
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)).1 h0
  unfold Φ
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 (h1 i (Finset.mem_univ _)) j
    (Finset.mem_univ _)
  split_ifs at h2 ⊢ with h
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [h3, zero_mul]
    · exact absurd h3 h.1.ne'
  · rfl

end scalar

end X5OL
end X5mod_OL_Main

section X5mod_AM_Conv
open Matrix Filter Set
open scoped Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

section conv
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hW : ∀ i j, 0 ≤ W i j)
include hW

lemma Φ_nonneg_term (t : ℝ) (i j : I) :
    0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
  split_ifs
  · exact mul_nonneg (hW i j) (Real.exp_pos _).le
  · exact le_rfl

lemma Φ_pos (h1 : 0 < Φ ν μ W 1) (t : ℝ) : 0 < Φ ν μ W t := by
  unfold Φ at h1 ⊢
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1.ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hc : 0 < ν i ∧ 0 < μ j := by by_contra h; exact hj (if_neg h)
  have hw : W i j ≠ 0 := by intro h; apply hj; rw [if_pos hc, h, zero_mul]
  have hterm : 0 < (if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
    rw [if_pos hc]; exact mul_pos ((hW i j).lt_of_ne (Ne.symm hw)) (Real.exp_pos _)
  refine lt_of_lt_of_le hterm ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
    Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0)
    (fun j _ => Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ j)

lemma Φ_holder (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : 0 < Φ ν μ W x) (hY : 0 < Φ ν μ W y) :
    Φ ν μ W (a * x + b * y) ≤ Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y)) := by
  set X := Φ ν μ W x
  set Y := Φ ν μ W y
  set E := Real.exp (a * Real.log X + b * Real.log Y)
  have key : ∀ i j, (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp ((a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j)) else 0) ≤
      E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) := by
    intro i j
    split_ifs with hc
    · set ex := x * Real.log (ν i) + (1 - x) * Real.log (μ j)
      set ey := y * Real.log (ν i) + (1 - y) * Real.log (μ j)
      have he : (a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j) =
          (a * Real.log X + b * Real.log Y) + (a * (ex - Real.log X) + b * (ey - Real.log Y)) := by
        simp only [ex, ey]
        have : b = 1 - a := by linarith
        subst this; ring
      have hcv := convexOn_exp.2 (mem_univ (ex - Real.log X)) (mem_univ (ey - Real.log Y)) ha hb hab
      simp only [smul_eq_mul] at hcv
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hX, Real.exp_log hY] at hcv
      rw [he, Real.exp_add]
      calc W i j * (E * Real.exp (a * (ex - Real.log X) + b * (ey - Real.log Y)))
          ≤ W i j * (E * (a * (Real.exp ex / X) + b * (Real.exp ey / Y))) := by
            gcongr
            exact hW i j
        _ = _ := by field_simp
    · simp
  calc Φ ν μ W (a * x + b * y) ≤ ∑ i, ∑ j, E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = E * (a * X / X + b * Y / Y) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
        rfl
    _ = E := by rw [mul_div_assoc, mul_div_assoc, div_self hX.ne', div_self hY.ne', mul_one, mul_one, hab,
          mul_one]

lemma L_convex (h1 : 0 < Φ ν μ W 1) : ConvexOn ℝ univ (fun t => Real.log (Φ ν μ W t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hX := Φ_pos ν μ W hW h1 x
  have hY := Φ_pos ν μ W hW h1 y
  have := Φ_holder ν μ W hW x y a b ha hb hab hX hY
  calc Real.log (Φ ν μ W (a * x + b * y))
      ≤ Real.log (Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y))) :=
        Real.log_le_log (Φ_pos ν μ W hW h1 _) this
    _ = _ := Real.log_exp _

end conv

end X5OL
end X5mod_AM_Conv

section X5mod_OL_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma N_psd (sigma : Matrix B B ℂ) (hs : sigma.PosSemidef) :
    (identityTensorReference (A := A) sigma).PosSemidef := by
  unfold identityTensorReference Matrix.kronecker
  exact Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hs

/-- real limit in the supported case -/
lemma real_limit {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ) (h1 : Φ ν μ W 1 = 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] 1)
      (𝓝 (-Φ' ν μ W / Real.log 2)) := by
  set ψ := fun t => Real.log (Φ ν μ W t) / Real.log 2
  have hψ : HasDerivAt ψ (Φ' ν μ W / Φ ν μ W 1 / Real.log 2) 1 :=
    ((Φ_deriv ν μ W).log (by rw [h1]; norm_num)).div_const _
  rw [h1, div_one] at hψ
  have hs := (hasDerivAt_iff_tendsto_slope.1 hψ).neg
  have hmono : 𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] (1 : ℝ) ≤ 𝓝[{(1 : ℝ)}ᶜ] 1 :=
    nhdsWithin_mono _ fun t ht => ht.2
  rw [neg_div]
  refine (hs.mono_left hmono).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 ht.2
  have hψ1 : ψ 1 = 0 := by simp [ψ, h1]
  rw [slope_def_field, hψ1, sub_zero]
  simp only [ψ, Real.logb]
  field_simp
  have : (1 - t) = -(t - 1) := by ring
  rw [this]; field_simp

lemma real_atBot {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ)
    (h0 : 0 < Φ ν μ W 1) (h1 : Φ ν μ W 1 < 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) atBot := by
  have hC : Real.logb 2 (Φ ν μ W 1) < 0 := Real.logb_neg (by norm_num) h0 h1
  have hg : Tendsto (fun t => Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) (𝓝 (Real.logb 2 (Φ ν μ W 1))) := by
    have : ContinuousAt (fun t => Real.log (Φ ν μ W t) / Real.log 2) 1 :=
      ((Φ_cont ν μ W).continuousAt.log h0.ne').div_const _
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun t : ℝ => 1 - t) (𝓝[Ioo 0 1] 1) (𝓝[Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.2 ht.2
  have hf : Tendsto (fun t : ℝ => 1 / (1 - t)) (𝓝[Ioo 0 1] 1) atTop := by
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hsub
  exact hf.atTop_mul_neg hC hg

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Tendsto (finiteAlpha rho sigma)
      (nhdsWithin 1 {t : ℝ | 0 < t ∧ t ≠ 1}) (nhds (fixedVonNeumann rho sigma)) ∧
      alphaEntropy rho sigma 1 = fixedVonNeumann rho sigma := by
  refine ⟨?_, by simp [alphaEntropy, finiteAlpha]⟩
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  -- traces as sums
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  by_cases hS : supportedBy rho N
  · -- supported case
    have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    rw [hval]
    have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
      (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds (by rw [hΦ1]; norm_num))
    refine (EReal.tendsto_coe.2 (real_limit ν μ W hΦ1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos] with t ht hp
    rw [hFA t ht.1 ht.2, if_neg (fun h => h.2 hS)]
    unfold log2Extended
    rw [if_neg hp.ne', ← EReal.coe_mul]
  · -- unsupported case
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    rw [hval]
    have hset : {t : ℝ | 0 < t ∧ t ≠ 1} = Ioo 0 1 ∪ Ioi 1 := by
      ext t; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨h0, h1⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr h
      · rintro (⟨h0, h1⟩ | h)
        · exact ⟨h0, h1.ne⟩
        · exact ⟨by linarith, h.ne'⟩
    rw [hset, nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · -- left
      have hΦnn : 0 ≤ Φ ν μ W 1 := by
        rw [Φ_one]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          split_ifs
          · exact mul_nonneg (hW i j) (hν i)
          · exact le_rfl
      rcases hΦnn.eq_or_lt with h0 | h0
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le)),
          Φ_zero ν μ W hν hμ hW h0.symm t]
        unfold log2Extended
        rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by have := ht.2; rw [one_div]; exact inv_pos.2 (by linarith))]
      · rw [EReal.tendsto_nhds_bot_iff_real]
        intro x
        have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
          (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds h0)
        filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos,
          (real_atBot ν μ W h0 hlt).eventually (eventually_lt_atBot x)] with t ht hp hlx
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le))]
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul, EReal.coe_lt_coe_iff]
        exact hlx
    · -- right
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hFA t (by have := ht; simp only [mem_Ioi] at this; linarith) (ne_of_gt ht), if_pos ⟨ht, hS⟩]

end X5OL
end X5mod_OL_Thm

section X5mod_AM_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fa_anti [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    AntitoneOn (finiteAlpha rho sigma) (Ioi 0) := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  have hF1 : finiteAlpha rho sigma 1 = fixedVonNeumann rho sigma := by
    unfold finiteAlpha; rw [if_pos rfl]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hS : supportedBy rho N
  · have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    set L := fun t => Real.log (Φ ν μ W t) with hLdef
    have hconv := L_convex ν μ W hW (by rw [hΦ1]; norm_num)
    have hL : HasDerivAt L (Φ' ν μ W) 1 := by
      have := (Φ_deriv ν μ W).log (by rw [hΦ1]; norm_num)
      rwa [hΦ1, div_one] at this
    have hL1 : L 1 = 0 := by simp [hLdef, hΦ1]
    set h : ℝ → ℝ := fun t => if t = 1 then Φ' ν μ W else slope L 1 t with hhdef
    have hg : ∀ t, 0 < t → finiteAlpha rho sigma t = ((-(h t) / Real.log 2 : ℝ) : EReal) := by
      intro t ht
      by_cases ht1 : t = 1
      · subst ht1; rw [hF1, hval]; simp [hhdef]
      · rw [hFA t ht ht1, if_neg (fun h => h.2 hS)]
        have hp := Φ_pos ν μ W hW (by rw [hΦ1]; norm_num) t
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul]
        congr 1
        simp only [hhdef, if_neg ht1, slope_def_field, sub_zero, hLdef, Real.logb, hΦ1, Real.log_one]
        have : t - 1 ≠ 0 := sub_ne_zero.2 ht1
        have : 1 - t ≠ 0 := fun h' => this (by linarith)
        field_simp
        ring
    have hmono : Monotone h := by
      intro s t hst
      rcases hst.lt_or_eq with hst | rfl
      · simp only [hhdef]
        by_cases hs1 : s = 1
        · subst hs1
          rw [if_pos rfl, if_neg hst.ne']
          exact hconv.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
        · by_cases ht1 : t = 1
          · subst ht1
            rw [if_neg hs1, if_pos rfl, slope_comm]
            exact hconv.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
          · rw [if_neg hs1, if_neg ht1]
            exact hconv.slope_mono (mem_univ _) ⟨mem_univ _, hs1⟩ ⟨mem_univ _, ht1⟩ hst.le
      · exact le_rfl
    intro s hs t ht hst
    rw [hg s hs, hg t ht, EReal.coe_le_coe_iff]
    have := hmono hst
    rw [div_le_div_iff_of_pos_right hl2]
    linarith
  · have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hbot : ∀ t, 1 ≤ t → finiteAlpha rho sigma t = ⊥ := by
      intro t ht
      rcases ht.lt_or_eq with ht | rfl
      · rw [hFA t (by linarith) ht.ne', if_pos ⟨ht, hS⟩]
      · rw [hF1, hval]
    have hΦnn : 0 ≤ Φ ν μ W 1 := by
      rw [Φ_one]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact mul_nonneg (hW i j) (hν i)
        · exact le_rfl
    intro s hs t ht hst
    by_cases ht1 : 1 ≤ t
    · rw [hbot t ht1]; exact bot_le
    push Not at ht1
    have hs1 : s < 1 := lt_of_le_of_lt hst ht1
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    rw [hFA t ht0 ht1.ne, hFA s hs0 hs1.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht1.le)),
      if_neg (fun h => absurd h.1 (not_lt.2 hs1.le))]
    rcases hΦnn.eq_or_lt with h0 | h0
    · rw [Φ_zero ν μ W hν hμ hW h0.symm t]
      unfold log2Extended
      rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by rw [one_div]; exact inv_pos.2 (by linarith))]
      exact bot_le
    · have hpt := Φ_pos ν μ W hW h0 t
      have hps := Φ_pos ν μ W hW h0 s
      unfold log2Extended
      rw [if_neg hpt.ne', if_neg hps.ne', ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hconv := L_convex ν μ W hW h0
      have hL1 : Real.log (Φ ν μ W 1) < 0 := Real.log_neg h0 hlt
      set θ := (1 - t) / (1 - s)
      have h1s : 0 < 1 - s := by linarith
      have h1t : 0 < 1 - t := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg h1t.le h1s.le
      have hθ1 : 0 ≤ 1 - θ := by
        simp only [θ]; rw [sub_nonneg, div_le_one h1s]; linarith
      have hc := hconv.2 (mem_univ s) (mem_univ 1) hθ0 hθ1 (by ring)
      simp only [smul_eq_mul, mul_one] at hc
      have ht' : θ * s + (1 - θ) = t := by simp only [θ]; field_simp; ring
      rw [ht'] at hc
      have hc2 : Real.log (Φ ν μ W t) ≤ θ * Real.log (Φ ν μ W s) := by
        have := mul_nonpos_of_nonneg_of_nonpos hθ1 hL1.le
        linarith
      unfold Real.logb
      have hθs : θ * (1 - s) = 1 - t := by simp only [θ]; field_simp
      have k : Real.log (Φ ν μ W t) * (1 - s) ≤ Real.log (Φ ν μ W s) * (1 - t) := by
        rw [← hθs]
        have := mul_le_mul_of_nonneg_right hc2 h1s.le
        linarith
      have e1 : ∀ (x y : ℝ), 1 / x * (y / Real.log 2) = (y / x) / Real.log 2 := fun x y => by ring
      rw [e1, e1]
      refine div_le_div_of_nonneg_right ?_ hl2.le
      rw [div_le_div_iff₀ h1t h1s]
      linarith

end X5OL

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

theorem am_main {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Antitone (alphaEntropy rho sigma) := by
  have hg := fa_anti rho sigma hrho hsigma
  have hsup : ∀ t : ℝ, 0 < t → finiteAlpha rho sigma t ≤ alphaEntropy rho sigma 0 := by
    intro t ht
    unfold alphaEntropy; rw [if_pos rfl]
    exact le_sSup ⟨t, ht, rfl⟩
  have hinf : ∀ t : ℝ, 0 < t → alphaEntropy rho sigma ⊤ ≤ finiteAlpha rho sigma t := by
    intro t ht
    unfold alphaEntropy; rw [if_neg ENNReal.top_ne_zero, if_pos rfl]
    exact sInf_le ⟨t, ht, rfl⟩
  have hfin : ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ →
      alphaEntropy rho sigma a = finiteAlpha rho sigma a.toReal ∧ 0 < a.toReal := by
    intro a h0 hT
    refine ⟨?_, ENNReal.toReal_pos h0 hT⟩
    unfold alphaEntropy; rw [if_neg h0, if_neg hT]
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; exact le_rfl
    by_cases hbT : b = ⊤
    · subst hbT; exact (hinf 1 one_pos).trans (hsup 1 one_pos)
    obtain ⟨e, hp⟩ := hfin b hb0 hbT
    rw [e]; exact hsup _ hp
  by_cases haT : a = ⊤
  · subst haT; rw [top_le_iff.1 hab]
  obtain ⟨ea, hpa⟩ := hfin a ha0 haT
  have hb0 : b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) bot_le)
  by_cases hbT : b = ⊤
  · subst hbT; rw [ea]; exact hinf _ hpa
  obtain ⟨eb, hpb⟩ := hfin b hb0 hbT
  rw [ea, eb]
  exact hg hpa hpb (ENNReal.toReal_mono hbT hab)

end X5OL
end X5mod_AM_Thm

section X5mod_AD_Fin
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

section single
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- spectral facts for one pair -/
theorem pack (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ t, Tr rho (identityTensorReference (A := A) sigma) t =
        (((Tr rho (identityTensorReference (A := A) sigma) t).re : ℝ) : ℂ)) ∧
    (∀ t, 0 < t → 0 ≤ (Tr rho (identityTensorReference (A := A) sigma) t).re) ∧
    (supportedBy rho (identityTensorReference (A := A) sigma) ↔
      (Tr rho (identityTensorReference (A := A) sigma) 1).re = 1) ∧
    (Tr rho (identityTensorReference (A := A) sigma) 1).re ≤ 1 ∧
    (supportedBy rho (identityTensorReference (A := A) sigma) →
      ∀ t, 0 < t → 0 < (Tr rho (identityTensorReference (A := A) sigma) t).re) := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hT : ∀ t, 0 < t → (Tr rho N t).re = Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hΦnn : ∀ t, 0 ≤ Φ ν μ W t := fun t =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Φ_nonneg_term ν μ W hW t i j
  have hsupp : supportedBy rho N ↔ Φ ν μ W 1 = 1 := by
    constructor
    · intro hS
      have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
        intro i j hi hj
        simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
      rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    · intro h1
      by_contra hS
      have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hS
        refine supp_bwd hR hN fun i j hi hj => ?_
        have := hne i j hi hj
        simp only [W, w] at this
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
      have := Φ_one_lt ν μ W hν hμ hW hrow hex
      rw [htr] at this; linarith
  have hle1 : Φ ν μ W 1 ≤ 1 := by
    by_cases hS : supportedBy rho N
    · exact (hsupp.1 hS).le
    · have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hS
        refine supp_bwd hR hN fun i j hi hj => ?_
        have := hne i j hi hj
        simp only [W, w] at this
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
      have := Φ_one_lt ν μ W hν hμ hW hrow hex
      rw [htr] at this; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    unfold Tr
    rw [tr_cfc_cfc hR hN]
    simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  · intro t ht; rw [hT t ht]; exact hΦnn t
  · rw [hT 1 one_pos]; exact hsupp
  · rw [hT 1 one_pos]; exact hle1
  · intro hS t ht
    rw [hT t ht]
    exact Φ_pos ν μ W hW (by rw [hsupp.1 hS]; norm_num) t

end single

lemma L_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    log2Extended (x * y) = log2Extended x + log2Extended y := by
  unfold log2Extended
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  rw [if_neg (mul_ne_zero h0 h1), if_neg h0, if_neg h1, Real.logb_mul h0 h1, EReal.coe_add]

lemma L_ne_top (x : ℝ) : log2Extended x ≠ ⊤ := by
  unfold log2Extended; split_ifs <;> simp

lemma emul_add (c : ℝ) (u v : EReal) (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    (c : EReal) * (u + v) = c * u + c * v := by
  induction u using EReal.rec with
  | top => exact absurd rfl hu
  | bot =>
    induction v using EReal.rec with
    | top => exact absurd rfl hv
    | bot =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h]
    | coe s =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h, ← EReal.coe_mul]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h, ← EReal.coe_mul]
  | coe r =>
    induction v using EReal.rec with
    | top => exact absurd rfl hv
    | bot =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h, ← EReal.coe_mul]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h, ← EReal.coe_mul]
    | coe s => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]

end X5AD
end X5mod_AD_Fin

section X5mod_LS_T1
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tr_cfc {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

lemma cont (A : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn _

lemma spec_nonneg {R : Matrix I I ℂ} (hR : R.PosSemidef) : ∀ x ∈ spectrum ℝ R, 0 ≤ x := by
  intro x hx
  rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hR.eigenvalues_nonneg i

lemma sq_herm (R : Matrix I I ℂ) : (cfc Real.sqrt R).IsHermitian :=
  (cfc_predicate Real.sqrt R : IsSelfAdjoint _)

lemma sq_mul_sq {R : Matrix I I ℂ} (hR : R.PosSemidef) : cfc Real.sqrt R * cfc Real.sqrt R = R := by
  rw [← cfc_mul (hf := cont R _) (hg := cont R _)]
  conv_rhs => rw [← cfc_id' ℝ R hR.isHermitian.isSelfAdjoint]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spec_nonneg hR x hx)

lemma tr_psd {R X : Matrix I I ℂ} (hR : R.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (R * X).trace.re := by
  set S := cfc Real.sqrt R
  have h : (S * X * Sᴴ).PosSemidef := hX.mul_mul_conjTranspose_same S
  have e : (R * X).trace = (S * X * Sᴴ).trace := by
    rw [← sq_mul_sq hR, (sq_herm R).eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [e]
  exact (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma tn_aux (M U : Matrix I I ℂ) (d : I → ℝ) (hUU : star U * U = 1) (hUU' : U * star U = 1)
    (e : M * Mᴴ = U * diagonal (RCLike.ofReal ∘ d) * star U) :
    (trace M).re ≤ ∑ j, Real.sqrt (d j) := by
  set K := star U * M * U with hK
  have hKK : K * Kᴴ = diagonal (RCLike.ofReal ∘ d) := by
    have h1 : Kᴴ = star U * Mᴴ * U := by
      simp [hK, conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [h1]
    calc star U * M * U * (star U * Mᴴ * U) = star U * (M * Mᴴ) * U := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc U, hUU', Matrix.one_mul]
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]; rw [hUU, Matrix.mul_one,
            ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htr : trace M = trace K := by
    rw [hK, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  rw [htr, Matrix.trace, Complex.re_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : ∑ k, ‖K j k‖ ^ 2 = d j := by
    have := congrFun (congrFun hKK j) j
    simp only [mul_apply, conjTranspose_apply, diagonal_apply_eq, Function.comp_apply] at this
    have h2 : ∀ k, K j k * star (K j k) = ((‖K j k‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [h2] at this
    rw [← Complex.ofReal_sum] at this
    exact Complex.ofReal_injective this
  have h3 : ‖K j j‖ ^ 2 ≤ d j := by
    rw [← hj]
    exact Finset.single_le_sum (f := fun k => ‖K j k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
  simp only [diag_apply]
  calc (K j j).re ≤ ‖K j j‖ := Complex.re_le_norm _
    _ = Real.sqrt (‖K j j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h3

lemma tn (M : Matrix I I ℂ) : (trace M).re ≤ (trace (cfc Real.sqrt (M * Mᴴ))).re := by
  have hH : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have e : M * Mᴴ = (hH.eigenvectorUnitary : Matrix I I ℂ) *
      diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star (hH.eigenvectorUnitary : Matrix I I ℂ) := by
    conv_lhs => rw [← cfc_id' ℝ (M * Mᴴ)]
    rw [hH.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  rw [tr_cfc hH, Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact tn_aux M _ _ (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _) e

end X5LS
end X5mod_LS_T1

section X5mod_LS_T2
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

open scoped MatrixOrder in
lemma cfc_psd {X : Matrix I I ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x ∈ spectrum ℝ X, 0 ≤ f x) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg hf

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma sqrt_mono {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    (cfc Real.sqrt B - cfc Real.sqrt A).PosSemidef := by
  have hA0 : (0 : Matrix I I ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hle : A ≤ B := Matrix.le_iff.mpr hAB
  have hB0 : (0 : Matrix I I ℂ) ≤ B := hA0.trans hle
  have h := CFC.sqrt_le_sqrt A B hle
  rw [CFC.sqrt_eq_real_sqrt A hA0, CFC.sqrt_eq_real_sqrt B hB0,
    cfcₙ_eq_cfc (by exact (A.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn _ |>.mono (by rw [quasispectrum_eq_spectrum_union_zero])) (by simp),
    cfcₙ_eq_cfc (by exact (B.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn _ |>.mono (by rw [quasispectrum_eq_spectrum_union_zero])) (by simp)] at h
  exact Matrix.le_iff.mp h

lemma herm_cfc (X : Matrix I I ℂ) (f : ℝ → ℝ) : (cfc f X).IsHermitian :=
  (cfc_predicate f X : IsSelfAdjoint _)

/-- conjugation by a hermitian matrix preserves PSD -/
lemma conj_psd {X C : Matrix I I ℂ} (hX : X.PosSemidef) (hC : C.IsHermitian) :
    (C * X * C).PosSemidef := by
  have := hX.mul_mul_conjTranspose_same C
  rwa [hC.eq] at this

lemma re_tr_herm {G R : Matrix I I ℂ} (hR : R.IsHermitian) :
    (R * Gᴴ).trace.re = (G * R).trace.re := by
  have : R * Gᴴ = (G * R)ᴴ := by rw [conjTranspose_mul, hR.eq]
  rw [this, trace_conjTranspose]
  simp

end X5LS
end X5mod_LS_T2

section X5mod_LS_T3
open Matrix
open scoped ComplexOrder

namespace X5LS
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

lemma posneg (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    X = cfc (fun x : ℝ => max x 0) X - cfc (fun x : ℝ => max (-x) 0) X := by
  rw [← cfc_sub (hf := cont X _) (hg := cont X _)]
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  refine cfc_congr fun x _ => ?_
  rcases le_total x 0 with h | h
  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]

lemma iB_B {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B * B = cfc Real.sqrt B := by
  conv_lhs => arg 2; rw [← cfc_id' ℝ B hB.isHermitian.isSelfAdjoint]
  rw [← cfc_mul (hf := cont B _) (hg := cont B _)]
  refine cfc_congr fun x hx => ?_
  have h0 := spec_nonneg hB x hx
  rcases h0.lt_or_eq with h | h
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    field_simp
    rw [Real.sq_sqrt h.le]
  · subst h; simp

lemma one_sub_P {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    (1 - cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B * B * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B).PosSemidef := by
  rw [iB_B hB, ← cfc_mul (hf := cont B _) (hg := cont B _),
    ← cfc_one ℝ B hB.isHermitian.isSelfAdjoint, ← cfc_sub (hf := cont B _) (hg := cont B _)]
  refine cfc_psd hB.isHermitian _ fun x hx => ?_
  have h0 := spec_nonneg hB x hx
  rcases h0.lt_or_eq with h | h
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    simp [hs.ne']
  · subst h; simp

theorem core (ρ A : Matrix I I ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (hA : A.PosSemidef) :
    ∃ τ : Matrix I I ℂ, τ.PosSemidef ∧ τ.trace.re ≤ 1 ∧ (A - τ).PosSemidef ∧
      1 - (cfc (fun x : ℝ => max x 0) (ρ - A)).trace.re ≤
        (cfc Real.sqrt (cfc Real.sqrt ρ * τ * cfc Real.sqrt ρ)).trace.re := by
  have hX : (ρ - A).IsHermitian := hρ.isHermitian.sub hA.isHermitian
  set D := cfc (fun x : ℝ => max x 0) (ρ - A) with hD
  set N := cfc (fun x : ℝ => max (-x) 0) (ρ - A) with hN
  have hDpsd : D.PosSemidef := cfc_psd hX _ fun x _ => le_max_right _ _
  have hNpsd : N.PosSemidef := cfc_psd hX _ fun x _ => le_max_right _ _
  have hpn := posneg (ρ - A) hX
  set B := A + D with hBdef
  have hB : B.PosSemidef := hA.add hDpsd
  have hBρ : (B - ρ).PosSemidef := by
    have : B - ρ = N := by
      rw [hBdef]; rw [← hD, ← hN] at hpn
      calc A + D - ρ = D - (ρ - A) - 0 + 0 := by abel
        _ = N := by rw [hpn]; abel
    rw [this]; exact hNpsd
  have hBA : (B - A).PosSemidef := by rw [hBdef, add_sub_cancel_left]; exact hDpsd
  set sA := cfc Real.sqrt A
  set sB := cfc Real.sqrt B
  set iB := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B
  set sρ := cfc Real.sqrt ρ
  have hsA : sA.IsHermitian := herm_cfc _ _
  have hiB : iB.IsHermitian := herm_cfc _ _
  have hsρ : sρ.IsHermitian := herm_cfc _ _
  set G := sA * iB with hG
  have hGh : Gᴴ = iB * sA := by rw [hG, conjTranspose_mul, hsA.eq, hiB.eq]
  have h1P := one_sub_P hB
  -- 1 - iB X iB is PSD whenever B - X is PSD
  have key : ∀ X : Matrix I I ℂ, (B - X).PosSemidef → (1 - iB * X * iB).PosSemidef := by
    intro X hX'
    have e : 1 - iB * X * iB = (1 - iB * B * iB) + iB * (B - X) * iB := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]; exact h1P.add (conj_psd hX' hiB)
  refine ⟨G * ρ * Gᴴ, hρ.mul_mul_conjTranspose_same G, ?_, ?_, ?_⟩
  · -- trace bound
    have hGG : (1 - Gᴴ * G).PosSemidef := by
      have : Gᴴ * G = iB * A * iB := by
        rw [hGh, hG]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc sA sA, sq_mul_sq hA]
      rw [this]; exact key A hBA
    have h := tr_psd hρ hGG
    have e : (G * ρ * Gᴴ).trace = (ρ * (Gᴴ * G)).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [e]
    rw [Matrix.mul_sub, Matrix.mul_one, trace_sub, htr, Complex.sub_re, Complex.one_re] at h
    linarith
  · -- A - τ PSD
    have e : A - G * ρ * Gᴴ = sA * (1 - iB * ρ * iB) * sA := by
      rw [hGh, hG, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sq_mul_sq hA]
      simp only [Matrix.mul_assoc]
    rw [e]; exact conj_psd (key ρ hBρ) hsA
  · -- fidelity
    set M := sρ * G * sρ with hM
    have hMh : Mᴴ = sρ * Gᴴ * sρ := by
      rw [hM, conjTranspose_mul, conjTranspose_mul, hsρ.eq, Matrix.mul_assoc]
    have hρ' : ρ = sρ * sρ := (sq_mul_sq hρ).symm
    have hMM : sρ * (G * ρ * Gᴴ) * sρ = M * Mᴴ := by
      calc sρ * (G * ρ * Gᴴ) * sρ = sρ * (G * (sρ * sρ) * Gᴴ) * sρ := by rw [← hρ']
        _ = M * Mᴴ := by rw [hMh, hM]; simp only [Matrix.mul_assoc]
    rw [hMM]
    refine le_trans ?_ (tn M)
    have htrM : M.trace = (G * ρ).trace := by
      rw [hM, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, sq_mul_sq hρ]
    rw [htrM]
    -- 2 - G - Gᴴ is PSD
    have h2 : ((2 : Matrix I I ℂ) - G - Gᴴ).PosSemidef := by
      have hGG : (1 - Gᴴ * G).PosSemidef := by
        have : Gᴴ * G = iB * A * iB := by
          rw [hGh, hG]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc sA sA, sq_mul_sq hA]
        rw [this]; exact key A hBA
      have h1 := posSemidef_conjTranspose_mul_self (1 - G)
      have e : (2 : Matrix I I ℂ) - G - Gᴴ = (1 - G)ᴴ * (1 - G) + (1 - Gᴴ * G) := by
        rw [conjTranspose_sub, conjTranspose_one]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
        rw [show (2 : Matrix I I ℂ) = 1 + 1 by norm_num]; abel
      rw [e]; exact h1.add hGG
    have hT := tr_psd hBρ h2
    have hT2 : 0 ≤ (sA * (sB - sA)).trace.re := tr_psd (cfc_psd hA.isHermitian _ fun x _ => Real.sqrt_nonneg x) (sqrt_mono hA hBA)
    have eGB : (G * B).trace = (sA * sB).trace := by
      rw [hG, Matrix.mul_assoc, iB_B hB]
    have eA : (sA * sA).trace = A.trace := by rw [sq_mul_sq hA]
    have r1 := re_tr_herm (G := G) hB.isHermitian
    have r2 := re_tr_herm (G := G) hρ.isHermitian
    rw [Matrix.mul_sub, trace_sub, eA, Complex.sub_re] at hT2
    have eT : ((B - ρ) * (2 - G - Gᴴ)).trace.re =
        2 * B.trace.re - (B * G).trace.re - (B * Gᴴ).trace.re - 2 * ρ.trace.re
          + (ρ * G).trace.re + (ρ * Gᴴ).trace.re := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, trace_sub, Complex.sub_re]
      rw [show (2 : Matrix I I ℂ) = (2 : ℂ) • (1 : Matrix I I ℂ) by
        rw [two_smul]; norm_num]
      simp [trace_smul]
      ring
    rw [eT, r1, r2, Matrix.trace_mul_comm B G, Matrix.trace_mul_comm ρ G, eGB, htr] at hT
    have eB : B.trace.re = A.trace.re + D.trace.re := by rw [hBdef, trace_add, Complex.add_re]
    simp only [Complex.one_re] at hT
    linarith

end X5LS
end X5mod_LS_T3

section X5mod_EO_PT
open Matrix
open scoped ComplexOrder Kronecker

namespace X5EO
set_option linter.unusedSectionVars false
open QAlgorithms

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- embedding of a B-vector into the a-th block -/
def emb (a : A) (y : B → ℂ) : A × B → ℂ := fun p => if p.1 = a then y p.2 else 0

lemma pt_kron (rho : Matrix (A × B) (A × B) ℂ) (Y : Matrix B B ℂ) :
    (rho * ((1 : Matrix A A ℂ) ⊗ₖ Y)).trace = (traceLeft rho * Y).trace := by
  simp only [Matrix.trace, diag_apply, mul_apply, kronecker_apply, one_apply, traceLeft, of_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma qf_emb (rho : Matrix (A × B) (A × B) ℂ) (y : B → ℂ) :
    star y ⬝ᵥ (traceLeft rho *ᵥ y) = ∑ a, star (emb a y) ⬝ᵥ (rho *ᵥ emb a y) := by
  simp only [dotProduct, mulVec, traceLeft, of_apply, emb, Pi.star_apply, Fintype.sum_prod_type,
    apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ x : B, ∑ i : A, ∑ y1 : B, star (y x) * (rho (i, x) (i, y1) * y y1) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma tl_psd {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) : (traceLeft rho).PosSemidef := by
  have hH : (traceLeft rho).IsHermitian := by
    ext b b'
    simp only [conjTranspose_apply, traceLeft, of_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := congrFun (congrFun h.isHermitian (a, b)) (a, b')
    rw [conjTranspose_apply] at this
    exact this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  rw [qf_emb]
  exact Finset.sum_nonneg fun a _ => h.dotProduct_mulVec_nonneg _

lemma tl_trace (rho : Matrix (A × B) (A × B) ℂ) : (traceLeft rho).trace = rho.trace := by
  simp only [Matrix.trace, diag_apply, traceLeft, of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma tl_density {rho : Matrix (A × B) (A × B) ℂ} (h : IsDensityMatrix rho) : IsDensityMatrix (traceLeft rho) :=
  ⟨tl_psd h.1, by rw [tl_trace, h.2]⟩

/-- (1 ⊗ Y) applied to the block embedding -/
lemma kron_emb (Y : Matrix B B ℂ) (a : A) (y : B → ℂ) :
    ((1 : Matrix A A ℂ) ⊗ₖ Y) *ᵥ emb a y = emb a (Y *ᵥ y) := by
  ext ⟨a', b⟩
  simp only [mulVec, dotProduct, kronecker_apply, one_apply, emb, Fintype.sum_prod_type, ite_mul,
    one_mul, zero_mul, mul_ite, mul_zero]
  by_cases h : a' = a
  · subst h; simp
  · simp [h, Ne.symm h]

lemma emb_sum (x : A × B → ℂ) : x = ∑ a, emb a (fun b => x (a, b)) := by
  ext ⟨a', b⟩
  simp [emb, Finset.sum_apply]

/-- kernel of (1⊗Y) splits blockwise -/
lemma ker_kron {Y : Matrix B B ℂ} {x : A × B → ℂ} (h : ((1 : Matrix A A ℂ) ⊗ₖ Y) *ᵥ x = 0) (a : A) :
    Y *ᵥ (fun b => x (a, b)) = 0 := by
  ext b
  have := congrFun h (a, b)
  simpa [mulVec, dotProduct, kronecker_apply, one_apply, Fintype.sum_prod_type] using this

lemma supp_tl {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    LinearMap.ker ((1 : Matrix A A ℂ) ⊗ₖ traceLeft rho).mulVecLin ≤ LinearMap.ker rho.mulVecLin := by
  intro x hx
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  have hblk : ∀ a, traceLeft rho *ᵥ (fun b => x (a, b)) = 0 := ker_kron hx
  have hzero : ∀ a a', rho *ᵥ emb a' (fun b => x (a, b)) = 0 := by
    intro a a'
    have h0 : star (fun b => x (a, b)) ⬝ᵥ (traceLeft rho *ᵥ (fun b => x (a, b))) = 0 := by
      rw [hblk a, dotProduct_zero]
    rw [qf_emb] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => h.dotProduct_mulVec_nonneg
      (emb a' (fun b => x (a, b))))).1 h0 a' (Finset.mem_univ _)
    exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff h _).1 this
  rw [emb_sum x, mulVec_sum]
  exact Finset.sum_eq_zero fun a _ => hzero a a

lemma supp_tl_of {rho : Matrix (A × B) (A × B) ℂ} {sigma : Matrix B B ℂ}
    (h : LinearMap.ker ((1 : Matrix A A ℂ) ⊗ₖ sigma).mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker (traceLeft rho).mulVecLin := by
  intro y hy
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hy ⊢
  have h1 : ∀ a, rho *ᵥ emb a y = 0 := by
    intro a
    have := h (x := emb a y) (by simp only [LinearMap.mem_ker, mulVecLin_apply]; rw [kron_emb, hy]; ext p; simp [emb])
    simpa using this
  ext b
  have : (traceLeft rho *ᵥ y) b = ∑ a, (rho *ᵥ emb a y) (a, b) := by
    simp only [mulVec, dotProduct, traceLeft, of_apply, emb, Fintype.sum_prod_type, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_mul]
    exact Finset.sum_comm
  rw [this]
  simp [h1]

end X5EO
end X5mod_EO_PT

section X5mod_DU_Thm
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology ComplexConjugate ENNReal

namespace X5DU
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

section cont
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem cont_gt1 (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hS : supportedBy rho (identityTensorReference (A := A) sigma)) (t0 : ℝ) (ht0 : 1 < t0) :
    ContinuousAt (finiteAlpha rho sigma) t0 := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  have hν : ∀ i, 0 ≤ hR.eigenvalues i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ hN.eigenvalues j := hNpsd.eigenvalues_nonneg
  set Φf := X5OL.Φ hR.eigenvalues hN.eigenvalues (w hR hN)
  have hT : ∀ t, 0 < t → (X5AD.Tr rho N t).re = Φf t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hpos : ∀ t, 0 < t → 0 < Φf t := fun t ht => by
    rw [← hT t ht]; exact (X5AD.pack rho sigma hrho hsigma).2.2.2.2 hS t ht
  set g : ℝ → ℝ := fun t => (1 / (1 - t)) * (Real.log (Φf t) / Real.log 2)
  have hev : (fun t => ((g t : ℝ) : EReal)) =ᶠ[𝓝 t0] finiteAlpha rho sigma := by
    filter_upwards [Ioi_mem_nhds ht0] with t (ht : 1 < t)
    have ht1 : t ≠ 1 := ht.ne'
    have htr : (cfc (fun x : ℝ => x ^ t) rho *
        cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re = Φf t := hT t (by linarith)
    simp only [finiteAlpha, ← hNdef, ht1, if_false, hS, not_true, and_false, htr, log2Extended,
      (hpos t (by linarith)).ne', g, Real.logb]
    rw [EReal.coe_mul]
  refine ContinuousAt.congr ?_ hev
  refine continuous_coe_real_ereal.continuousAt.comp ?_
  have h1 : (1 : ℝ) - t0 ≠ 0 := by linarith
  have hΦc : Continuous Φf := X5OL.Φ_cont _ _ _
  exact (continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1).mul
    ((hΦc.continuousAt.log (hpos t0 (by linarith)).ne').div_const _)

end cont

lemma endpoint (F G : ℝ → EReal) (hF : AntitoneOn F (Ioi 0)) (hG : AntitoneOn G (Ioi 0))
    (hFG : ∀ t, 0 < t → t < 2 → F t = -G (2 - t)) (hc : ContinuousAt G 2) :
    sSup {h : EReal | ∃ t : ℝ, 0 < t ∧ h = F t} = -G 2 := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    rcases lt_or_ge t 2 with h2 | h2
    · rw [hFG t ht h2]
      exact EReal.neg_le_neg_iff.2 (hG (show (0 : ℝ) < 2 - t by linarith)
        (show (0 : ℝ) < 2 by norm_num) (by linarith))
    · calc F t ≤ F 1 := hF (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < t by linarith) (by linarith)
        _ = -G 1 := by rw [hFG 1 one_pos (by norm_num)]; norm_num
        _ ≤ -G 2 := EReal.neg_le_neg_iff.2 (hG (show (0 : ℝ) < 1 by norm_num)
          (show (0 : ℝ) < 2 by norm_num) (by norm_num))
  · have hm : Tendsto (fun t : ℝ => 2 - t) (𝓝[>] 0) (𝓝 2) := by
      have := ((tendsto_const_nhds (x := (2 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have ht : Tendsto (fun t => -G (2 - t)) (𝓝[>] 0) (𝓝 (-G 2)) :=
      (continuous_neg.tendsto _).comp (hc.tendsto.comp hm)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with t ⟨h0, h2⟩
    rw [← hFG t h0 h2]
    exact le_sSup ⟨t, h0, rfl⟩

section main
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
  [DecidableEq C]

lemma unit (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : ‖psi‖ = 1) :
    ∑ p, psi p * star (psi p) = 1 := by
  have h1 : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
  exact h1

lemma dAB (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : ‖psi‖ = 1) :
    IsDensityMatrix (traceRight (pureDensity psi)) := by
  rw [rAB]
  refine ⟨posSemidef_self_mul_conjTranspose _, ?_⟩
  rw [← unit psi hpsi]
  simp [trace, mul_apply, Ψ, Fintype.sum_prod_type]

lemma dAC (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : ‖psi‖ = 1) :
    IsDensityMatrix (traceMiddleABC (pureDensity psi)) := by
  rw [rAC]
  refine ⟨posSemidef_self_mul_conjTranspose _, ?_⟩
  rw [← unit psi hpsi]
  simp only [trace, diag, mul_apply, Φ, of_apply, conjTranspose_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

variable (psi : EuclideanSpace ℂ ((A × B) × C))

lemma fin_ne (hpsi : ‖psi‖ = 1) (t : ℝ) (h0 : 0 < t) (h2 : t < 2) (h1 : t ≠ 1) :
    finiteAlpha (traceRight (pureDensity psi)) (traceLeft (traceRight (pureDensity psi))) t =
      -finiteAlpha (traceMiddleABC (pureDensity psi))
        (traceLeft (traceMiddleABC (pureDensity psi))) (2 - t) := by
  have hSB : supportedBy (traceRight (pureDensity psi))
      (identityTensorReference (A := A) (traceLeft (traceRight (pureDensity psi)))) :=
    X5EO.supp_tl (dAB psi hpsi).1
  have hSC : supportedBy (traceMiddleABC (pureDensity psi))
      (identityTensorReference (A := A) (traceLeft (traceMiddleABC (pureDensity psi)))) :=
    X5EO.supp_tl (dAC psi hpsi).1
  have h1' : 2 - t ≠ 1 := fun h => h1 (by linarith)
  have hq := congrArg Complex.re (Q_eq psi t h0 h2)
  unfold X5AD.Tr at hq
  simp only [finiteAlpha, h1, h1', hSB, hSC, not_true, and_false, if_false]
  rw [hq, ← EReal.neg_mul, ← EReal.coe_neg, show (1 : ℝ) - (2 - t) = -(1 - t) by ring, div_neg,
    neg_neg]

lemma fin_eq [Nonempty A] [Nonempty B] [Nonempty C] (hpsi : ‖psi‖ = 1) (t : ℝ) (h0 : 0 < t)
    (h2 : t < 2) :
    finiteAlpha (traceRight (pureDensity psi)) (traceLeft (traceRight (pureDensity psi))) t =
      -finiteAlpha (traceMiddleABC (pureDensity psi))
        (traceLeft (traceMiddleABC (pureDensity psi))) (2 - t) := by
  rcases ne_or_eq t 1 with h1 | rfl
  · exact fin_ne psi hpsi t h0 h2 h1
  set F := finiteAlpha (traceRight (pureDensity psi)) (traceLeft (traceRight (pureDensity psi)))
  set G := finiteAlpha (traceMiddleABC (pureDensity psi))
    (traceLeft (traceMiddleABC (pureDensity psi)))
  have dB := X5EO.tl_density (dAB psi hpsi)
  have dC := X5EO.tl_density (dAC psi hpsi)
  set S : Set ℝ := {t : ℝ | 0 < t ∧ t ≠ 1}
  have hF := (X5OL.main _ _ (dAB psi hpsi) dB).1
  have hG := (X5OL.main _ _ (dAC psi hpsi) dC).1
  have hF1 : F 1 = fixedVonNeumann (traceRight (pureDensity psi))
      (traceLeft (traceRight (pureDensity psi))) := by simp [F, finiteAlpha]
  have hG1 : G 1 = fixedVonNeumann (traceMiddleABC (pureDensity psi))
      (traceLeft (traceMiddleABC (pureDensity psi))) := by simp [G, finiteAlpha]
  rw [← hF1] at hF
  rw [← hG1] at hG
  have hlt : ∀ᶠ t in 𝓝[S] (1 : ℝ), t < 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  have hm : Tendsto (fun t : ℝ => 2 - t) (𝓝[S] 1) (𝓝[S] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((tendsto_const_nhds (x := (2 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))).mono_left
        (nhdsWithin_le_nhds (s := S))
      convert this using 2 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin, hlt] with t ⟨ht0, ht1⟩ ht2
      exact ⟨by linarith, fun h => ht1 (by linarith)⟩
  have hG' : Tendsto (fun t => -G (2 - t)) (𝓝[S] 1) (𝓝 (-G 1)) :=
    (continuous_neg.tendsto _).comp (hG.comp hm)
  have hev : F =ᶠ[𝓝[S] 1] fun t => -G (2 - t) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with t ⟨ht0, ht1⟩ ht2
    exact fin_ne psi hpsi t ht0 ht2 ht1
  haveI : (𝓝[S] (1 : ℝ)).NeBot := by
    refine Filter.NeBot.mono (inferInstance : (𝓝[>] (1 : ℝ)).NeBot) (nhdsWithin_mono _ ?_)
    intro t (ht : 1 < t); exact ⟨by linarith, ht.ne'⟩
  rw [show (2 : ℝ) - 1 = 1 by norm_num]
  exact tendsto_nhds_unique hF (hG'.congr' hev.symm)

theorem du_main [Nonempty A] [Nonempty B] [Nonempty C] (hpsi : ‖psi‖ = 1)
    (alpha : ℝ≥0∞) (halpha : alpha ≤ 2) :
    alphaEntropy (traceRight (pureDensity psi))
      (traceLeft (traceRight (pureDensity psi))) alpha =
    -alphaEntropy (traceMiddleABC (pureDensity psi))
      (traceLeft (traceMiddleABC (pureDensity psi))) (2 - alpha) := by
  set F := finiteAlpha (traceRight (pureDensity psi)) (traceLeft (traceRight (pureDensity psi)))
  set G := finiteAlpha (traceMiddleABC (pureDensity psi))
    (traceLeft (traceMiddleABC (pureDensity psi)))
  have dB := X5EO.tl_density (dAB psi hpsi)
  have dC := X5EO.tl_density (dAC psi hpsi)
  have hFa : AntitoneOn F (Ioi 0) := X5OL.fa_anti _ _ (dAB psi hpsi) dB
  have hGa : AntitoneOn G (Ioi 0) := X5OL.fa_anti _ _ (dAC psi hpsi) dC
  have hFG : ∀ t, 0 < t → t < 2 → F t = -G (2 - t) := fun t h0 h2 => fin_eq psi hpsi t h0 h2
  have hFc : ContinuousAt F 2 := cont_gt1 _ _ (dAB psi hpsi) dB (X5EO.supp_tl (dAB psi hpsi).1) 2
    (by norm_num)
  have hGc : ContinuousAt G 2 := cont_gt1 _ _ (dAC psi hpsi) dC (X5EO.supp_tl (dAC psi hpsi).1) 2
    (by norm_num)
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rcases eq_or_ne alpha 0 with rfl | ha0
  · simp only [alphaEntropy, if_true, tsub_zero, h2ne0, h2top, if_false, ENNReal.toReal_ofNat]
    exact endpoint F G hFa hGa hFG hGc
  rcases eq_or_ne alpha 2 with rfl | ha2
  · simp only [alphaEntropy, tsub_self, if_true, h2ne0, h2top, if_false, ENNReal.toReal_ofNat]
    have := endpoint G F hGa hFa (fun s h0 h2 => by
      rw [hFG (2 - s) (by linarith) (by linarith), neg_neg, sub_sub_cancel]) hFc
    rw [this, neg_neg]
  have hlt : alpha < 2 := lt_of_le_of_ne halpha ha2
  have hatop : alpha ≠ ⊤ := ne_top_of_lt hlt
  have hb0 : 2 - alpha ≠ 0 := (tsub_pos_of_lt hlt).ne'
  have hbtop : 2 - alpha ≠ ⊤ := ENNReal.sub_ne_top h2top
  simp only [alphaEntropy, ha0, hatop, hb0, hbtop, if_false]
  rw [ENNReal.toReal_sub_of_le halpha h2top, ENNReal.toReal_ofNat]
  refine hFG _ (ENNReal.toReal_pos ha0 hatop) ?_
  have := (ENNReal.toReal_lt_toReal hatop h2top).2 hlt
  simpa using this

end main

end X5DU
end X5mod_DU_Thm

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

theorem solution {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : ‖psi‖ = 1)
    (alpha : ℝ≥0∞) (halpha : alpha ≤ 2) :
    alphaEntropy (traceRight (pureDensity psi))
      (traceLeft (traceRight (pureDensity psi))) alpha =
    -alphaEntropy (traceMiddleABC (pureDensity psi))
      (traceLeft (traceMiddleABC (pureDensity psi))) (2 - alpha) :=
  X5DU.du_main psi hpsi alpha halpha

end
