-- Prove2me | solution 1 for WildeQIT.EntManip.theorem_19_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T20:27:55.951079+00:00
-- url     : https://prove2.me/submissions/6ead23c3-67c7-4332-b5ea-72e27691595a

import Mathlib
import Definitions.Def_WildeQIT_EntManip_entEntropy
import Definitions.Def_WildeQIT_EntManip_IsAchievableRate
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_EntManip_tensorPowVec

set_option autoImplicit false

section F0


/-! Draft for 2ba22dc4 WildeQIT.EntManip.theorem_19_4_1 (Wilde Thm 19.4.1).
Stage 0: the IsLUB glue from the two top children (achievability, converse),
plus the child statements as `Prop` definitions so they typecheck against the
mirror imports. See scratch/decomp/2ba22dc4.plan.md. -/


open scoped Kronecker Matrix ComplexOrder

namespace EntManip2ba

open WildeQIT.EntManip Matrix

/-- Parent glue: achievability below the ratio plus the converse give `IsLUB`. -/
theorem glue {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ) (r : ℝ)
    (hach : ∀ E : ℝ, E < r → IsAchievableRate ψ φ E)
    (hconv : ∀ E : ℝ, IsAchievableRate ψ φ E → E ≤ r) :
    IsLUB {E : ℝ | IsAchievableRate ψ φ E} r := by
  refine ⟨fun E hE => hconv E hE, fun u hu => ?_⟩
  by_contra h
  have h : u < r := not_le.mp h
  have hmid : (u + r) / 2 < r := by linarith
  have := hu (hach _ hmid)
  linarith

/-- Child A (achievability, Wilde §19.4 concentration + dilution). -/
def ChildAchieve : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 → ∑ z, ‖φ z‖ ^ 2 = 1 → 0 < entEntropy φ →
    ∀ E : ℝ, E < entEntropy ψ / entEntropy φ → IsAchievableRate ψ φ E

/-- Child C (converse, Wilde §19.4 / Schmidt-rank argument). -/
def ChildConverse : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 → ∑ z, ‖φ z‖ ^ 2 = 1 → 0 < entEntropy φ →
    ∀ E : ℝ, IsAchievableRate ψ φ E → E ≤ entEntropy ψ / entEntropy φ

/-- K1: every LOCC channel has a product Kraus form `∑ j (A j ⊗ B j) ρ (A j ⊗ B j)†`
with completeness (Wilde §19.2: LOCC ⊂ separable operations). -/
def K1_LOCCKraus : Prop :=
  ∀ {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ), IsLOCC Λ →
    ∃ (J : Type) (_ : Fintype J) (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ),
      (∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1) ∧
      ∀ ρ, Λ ρ = ∑ j, (A j ⊗ₖ B j) * ρ * (A j ⊗ₖ B j)ᴴ

/-- K2a: contraction lower bound for the trace norm of a Hermitian matrix. -/
def K2a_traceNorm_ge : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] (M Q : Matrix n n ℂ), M.IsHermitian →
    (1 - Qᴴ * Q).PosSemidef → (Matrix.trace (Q * M)).re ≤ WildeQIT.traceNorm M

/-- K2b: the trace norm of a Hermitian matrix is attained by a Hermitian contraction
(the sign of `M`). -/
def K2b_traceNorm_attained : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ), M.IsHermitian →
    ∃ S : Matrix n n ℂ, S.IsHermitian ∧ (1 - Sᴴ * S).PosSemidef ∧
      WildeQIT.traceNorm M = (Matrix.trace (S * M)).re

/-- K3: Schmidt form of a unit bipartite vector and the entropy of entanglement as the
Shannon entropy of the Schmidt coefficients. -/
def K3_Schmidt : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 →
    ∃ (e : a → a → ℂ) (w : a → b → ℂ) (p : a → ℝ),
      (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) ∧
      (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0) ∧
      (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
      (∀ i k, ψ (i, k) = ∑ x, e x i * w x k) ∧
      entEntropy ψ = -∑ x, p x * Real.logb 2 (p x)

-- K1 PROVED (2026-11-11)
lemma sum_kron {ι l m n p : Type} (s : Finset ι) (A : ι → Matrix l m ℂ) (B : Matrix n p ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

lemma kron_sum {ι l m n p : Type} (s : Finset ι) (A : Matrix l m ℂ) (B : ι → Matrix n p ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

/-- Motive with existential `Fintype` instances (the `comp` constructor of `IsLOCC`
carries none for the intermediate systems). -/
theorem k1_aux : ∀ {a b a' b' : Type}
    {Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ}, IsLOCC Λ →
    ∃ (_ : Fintype a) (_ : Fintype b) (_ : Fintype a') (_ : Fintype b')
      (J : Type) (_ : Fintype J) (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ),
      (∀ (_ : DecidableEq a) (_ : DecidableEq b),
        ∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1) ∧
      ∀ ρ, Λ ρ = ∑ j, (A j ⊗ₖ B j) * ρ * (A j ⊗ₖ B j)ᴴ := by
  intro a b a' b' Λ h
  induction h with
  | @oneWayAB a b a' b' _ _ _ _ _ _ Λ h =>
    obtain ⟨X, iX, κ, iκ, F, G, hF, hΛ⟩ := h
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      (Σ x : X, κ × (G x).ι), inferInstance, fun j => F j.1 j.2.1,
      fun j => (G j.1).K j.2.2, ?_, ?_⟩
    · have hc : ∑ j : (Σ x : X, κ × (G x).ι),
          (F j.1 j.2.1 ⊗ₖ (G j.1).K j.2.2)ᴴ * (F j.1 j.2.1 ⊗ₖ (G j.1).K j.2.2) = 1 := by
        simp only [Fintype.sum_sigma, Fintype.sum_prod_type, conjTranspose_kronecker,
          ← mul_kronecker_mul, ← kron_sum, (G _).complete, ← sum_kron, hF, one_kronecker_one]
      intro _ _
      convert hc
    · intro ρ
      rw [hΛ ρ, Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type]
  | @oneWayBA a b a' b' _ _ _ _ _ _ Λ h =>
    obtain ⟨X, iX, κ, iκ, F, G, hF, hΛ⟩ := h
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      (Σ x : X, κ × (G x).ι), inferInstance, fun j => (G j.1).K j.2.2,
      fun j => F j.1 j.2.1, ?_, ?_⟩
    · have hc : ∑ j : (Σ x : X, κ × (G x).ι),
          ((G j.1).K j.2.2 ⊗ₖ F j.1 j.2.1)ᴴ * ((G j.1).K j.2.2 ⊗ₖ F j.1 j.2.1) = 1 := by
        simp only [Fintype.sum_sigma, Fintype.sum_prod_type, conjTranspose_kronecker,
          ← mul_kronecker_mul, ← sum_kron, (G _).complete, ← kron_sum, hF, one_kronecker_one]
      intro _ _
      convert hc
    · intro ρ
      rw [hΛ ρ, Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type]
  | @comp a b a' b' a'' b'' Λ₁ Λ₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨ia, ib, ia', ib', J1, iJ1, A1, B1, hc1, hΛ1⟩ := ih₁
    obtain ⟨ja', jb', ia'', ib'', J2, iJ2, A2, B2, hc2, hΛ2⟩ := ih₂
    obtain rfl : ja' = ia' := Subsingleton.elim _ _
    obtain rfl : jb' = ib' := Subsingleton.elim _ _
    classical
    refine ⟨ia, ib, ia'', ib'', J1 × J2, inferInstance, fun j => A2 j.2 * A1 j.1,
      fun j => B2 j.2 * B1 j.1, ?_, ?_⟩
    · intro d1 d2
      have e : ∀ j : J1 × J2, (A2 j.2 * A1 j.1) ⊗ₖ (B2 j.2 * B1 j.1)
          = (A2 j.2 ⊗ₖ B2 j.2) * (A1 j.1 ⊗ₖ B1 j.1) := fun j => mul_kronecker_mul _ _ _ _
      simp only [e, conjTranspose_mul]
      rw [Fintype.sum_prod_type]
      have : ∀ j1 : J1, ∑ j2 : J2, (A1 j1 ⊗ₖ B1 j1)ᴴ * (A2 j2 ⊗ₖ B2 j2)ᴴ *
          ((A2 j2 ⊗ₖ B2 j2) * (A1 j1 ⊗ₖ B1 j1)) = (A1 j1 ⊗ₖ B1 j1)ᴴ * (A1 j1 ⊗ₖ B1 j1) := by
        intro j1
        have h2 := hc2 inferInstance inferInstance
        calc _ = (A1 j1 ⊗ₖ B1 j1)ᴴ * (∑ j2 : J2, (A2 j2 ⊗ₖ B2 j2)ᴴ * (A2 j2 ⊗ₖ B2 j2)) *
              (A1 j1 ⊗ₖ B1 j1) := by
                rw [Matrix.mul_sum, Matrix.sum_mul]
                refine Finset.sum_congr rfl fun j2 _ => ?_
                simp only [Matrix.mul_assoc]
          _ = _ := by rw [h2, Matrix.mul_one]
      rw [Finset.sum_congr rfl fun j1 _ => this j1]
      exact hc1 d1 d2
    · intro ρ
      have e : ∀ j : J1 × J2, (A2 j.2 * A1 j.1) ⊗ₖ (B2 j.2 * B1 j.1)
          = (A2 j.2 ⊗ₖ B2 j.2) * (A1 j.1 ⊗ₖ B1 j.1) := fun j => mul_kronecker_mul _ _ _ _
      simp only [Function.comp_apply, hΛ1, hΛ2, e, conjTranspose_mul, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j2 _ => ?_
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j1 _ => ?_
      simp only [Matrix.mul_assoc]

theorem k1 {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ) (h : IsLOCC Λ) :
    ∃ (J : Type) (_ : Fintype J) (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ),
      (∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1) ∧
      ∀ ρ, Λ ρ = ∑ j, (A j ⊗ₖ B j) * ρ * (A j ⊗ₖ B j)ᴴ := by
  obtain ⟨ia, ib, ia', ib', J, iJ, A, B, hc, hΛ⟩ := k1_aux h
  refine ⟨J, iJ, A, B, ?_, fun ρ => ?_⟩
  · convert hc inferInstance inferInstance
  · convert hΛ ρ

end EntManip2ba


end F0

section F1



open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace EntManip2ba

open WildeQIT Matrix

section K2
variable {n : Type} [Fintype n] [DecidableEq n]

lemma conj_apply (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U X
      = (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ := by
  rw [Unitary.conjStarAlgAut_apply]; rfl

lemma trace_conj (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    trace ((U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ) = trace X := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have : (U : Matrix n n ℂ)ᴴ * U = 1 := Unitary.coe_star_mul_self U
  rw [this, Matrix.one_mul]

lemma sqrt_herm (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    CFC.sqrt (Mᴴ * M) = cfc (fun x : ℝ => |x|) M := by
  have hsa : IsSelfAdjoint M := hM.isSelfAdjoint
  rw [CFC.sqrt_eq_iff _ _ ?_ ?_]
  · rw [← cfc_mul (fun x : ℝ => |x|) (fun x => |x|) M]
    have : (fun x : ℝ => |x| * |x|) = fun x => x * x := by
      funext x; exact abs_mul_abs_self x
    rw [this, cfc_mul (fun x : ℝ => x) (fun x => x) M, cfc_id' ℝ M, hM.eq]
  · exact Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self M)
  · exact cfc_nonneg (fun x _ => abs_nonneg x)

/-- Spectral form with explicit unitary. -/
lemma herm_eq (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    M = (hM.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (hM.eigenvalues i : ℂ)) *
      (hM.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [conj_apply]; rfl

lemma traceNorm_herm (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    traceNorm M = ∑ i, |hM.eigenvalues i| := by
  unfold traceNorm
  rw [sqrt_herm M hM, hM.cfc_eq, Matrix.IsHermitian.cfc, conj_apply, trace_conj, trace_diagonal]
  all_goals simp [Complex.re_sum]

lemma sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · subst h; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

lemma sign_sq_le (x : ℝ) : Real.sign x ^ 2 ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h]; norm_num
  · subst h; simp
  · rw [Real.sign_of_pos h]; norm_num

section Core
variable (U : Matrix n n ℂ) (hUU : Uᴴ * U = 1) (hUU' : U * Uᴴ = 1)
include hUU

lemma trace_conj' (X : Matrix n n ℂ) : trace (U * X * Uᴴ) = trace X := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]

include hUU'

lemma k2b_core (lam s : n → ℝ) (hs : ∀ i, s i * lam i = |lam i|) (hs2 : ∀ i, s i ^ 2 ≤ 1) :
    (U * diagonal (fun i => (s i : ℂ)) * Uᴴ).IsHermitian ∧
    (1 - (U * diagonal (fun i => (s i : ℂ)) * Uᴴ)ᴴ *
      (U * diagonal (fun i => (s i : ℂ)) * Uᴴ)).PosSemidef ∧
    (trace (U * diagonal (fun i => (s i : ℂ)) * Uᴴ *
      (U * diagonal (fun i => (lam i : ℂ)) * Uᴴ))).re = ∑ i, |lam i| := by
  have hDh : (diagonal (fun i => (s i : ℂ)))ᴴ = diagonal (fun i => (s i : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp
  refine ⟨?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDh,
      Matrix.mul_assoc]
  · have e : 1 - (U * diagonal (fun i => (s i : ℂ)) * Uᴴ)ᴴ *
        (U * diagonal (fun i => (s i : ℂ)) * Uᴴ)
        = U * diagonal (fun i => ((1 - s i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDh]
      have h1 : U * diagonal (fun i => (s i : ℂ)) * Uᴴ * (U * diagonal (fun i => (s i : ℂ)) * Uᴴ)
          = U * (diagonal (fun i => (s i : ℂ)) * diagonal (fun i => (s i : ℂ))) * Uᴴ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
      have h2 : (1 : Matrix n n ℂ) = U * 1 * Uᴴ := by rw [Matrix.mul_one, hUU']
      rw [← Matrix.mul_assoc U (diagonal fun i => (s i : ℂ)) Uᴴ, h1, diagonal_mul_diagonal]
      conv_lhs => rw [h2]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← diagonal_one, diagonal_sub]
      congr 2; funext i; push_cast; ring
    rw [e]
    refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    have := hs2 i
    exact_mod_cast (sub_nonneg.mpr this)
  · have e : U * diagonal (fun i => (s i : ℂ)) * Uᴴ * (U * diagonal (fun i => (lam i : ℂ)) * Uᴴ)
        = U * diagonal (fun i => ((|lam i| : ℝ) : ℂ)) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
        diagonal_mul_diagonal]
      congr 3; funext i; rw [← hs]; push_cast; ring
    rw [e, trace_conj' U hUU, trace_diagonal]
    simp [Complex.re_sum]

lemma k2a_core (lam : n → ℝ) (Q : Matrix n n ℂ) (hQ : (1 - Qᴴ * Q).PosSemidef) :
    (trace (Q * (U * diagonal (fun i => (lam i : ℂ)) * Uᴴ))).re ≤ ∑ i, |lam i| := by
  have hQ'c : (1 - (Uᴴ * Q * U)ᴴ * (Uᴴ * Q * U)).PosSemidef := by
    have e : 1 - (Uᴴ * Q * U)ᴴ * (Uᴴ * Q * U) = Uᴴ * (1 - Qᴴ * Q) * U := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ, hUU', Matrix.one_mul]
    rw [e]
    exact hQ.conjTranspose_mul_mul_same U
  have hdiag : ∀ i, ‖(Uᴴ * Q * U) i i‖ ≤ 1 := by
    intro i
    have h0 := hQ'c.diag_nonneg (i := i)
    have hre := (Complex.le_def.mp h0).1
    have hsum : (((Uᴴ * Q * U)ᴴ * (Uᴴ * Q * U)) i i).re = ∑ k, ‖(Uᴴ * Q * U) k i‖ ^ 2 := by
      simp only [Matrix.mul_apply (M := (Uᴴ * Q * U)ᴴ), conjTranspose_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    have hle : ‖(Uᴴ * Q * U) i i‖ ^ 2 ≤ ∑ k, ‖(Uᴴ * Q * U) k i‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖(Uᴴ * Q * U) k i‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ i)
    rw [Matrix.sub_apply, Complex.sub_re, hsum, Matrix.one_apply_eq, Complex.one_re,
      Complex.zero_re] at hre
    have h2 : ‖(Uᴴ * Q * U) i i‖ ^ 2 ≤ 1 := by linarith
    nlinarith [norm_nonneg ((Uᴴ * Q * U) i i)]
  have htr : trace (Q * (U * diagonal (fun i => (lam i : ℂ)) * Uᴴ))
      = ∑ i, (Uᴴ * Q * U) i i * (lam i : ℂ) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_diagonal]
  rw [htr, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ((Uᴴ * Q * U) i i * (lam i : ℂ)).re ≤ ‖(Uᴴ * Q * U) i i * (lam i : ℂ)‖ :=
        Complex.re_le_norm _
    _ = ‖(Uᴴ * Q * U) i i‖ * |lam i| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * |lam i| := by gcongr; exact hdiag i
    _ = |lam i| := one_mul _

end Core

/-- K2b: the trace norm of a Hermitian matrix is attained by a Hermitian contraction. -/
theorem k2b (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    ∃ S : Matrix n n ℂ, S.IsHermitian ∧ (1 - Sᴴ * S).PosSemidef ∧
      traceNorm M = (Matrix.trace (S * M)).re := by
  obtain ⟨h1, h2, h3⟩ := k2b_core (hM.eigenvectorUnitary : Matrix n n ℂ)
    (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _) hM.eigenvalues
    (fun i => Real.sign (hM.eigenvalues i)) (fun i => sign_mul_self _) (fun i => sign_sq_le _)
  refine ⟨_, h1, h2, ?_⟩
  rw [traceNorm_herm M hM, ← h3, ← herm_eq M hM]

/-- K2a: contraction lower bound for the trace norm of a Hermitian matrix. -/
theorem k2a (M Q : Matrix n n ℂ) (hM : M.IsHermitian) (hQ : (1 - Qᴴ * Q).PosSemidef) :
    (Matrix.trace (Q * M)).re ≤ traceNorm M := by
  have := k2a_core (hM.eigenvectorUnitary : Matrix n n ℂ)
    (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _) hM.eigenvalues Q hQ
  rw [← herm_eq M hM] at this
  rw [traceNorm_herm M hM]
  exact this

end K2

end EntManip2ba

end F1

section F2



open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace EntManip2ba

open WildeQIT Matrix

section K3
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]

/-- The coefficient matrix of a bipartite vector. -/
def coefMat (ψ : a × b → ℂ) : Matrix a b ℂ := Matrix.of fun i k => ψ (i, k)

lemma rho_eq (ψ : a × b → ℂ) :
    partialTraceRight (ObliviousRSP.pureState ψ) = coefMat ψ * (coefMat ψ)ᴴ := by
  ext i j
  simp [partialTraceRight, ObliviousRSP.pureState, coefMat, Matrix.mul_apply, vecMulVec_apply]

lemma trace_rho (ψ : a × b → ℂ) :
    trace (coefMat ψ * (coefMat ψ)ᴴ) = ((∑ z, ‖ψ z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diag_apply, Matrix.mul_apply, conjTranspose_apply, coefMat, of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; rfl

/-- Generic Schmidt core: from a unitary diagonalisation `ρ_A = V diag λ Vᴴ`. -/
lemma k3_core (ψ : a × b → ℂ) (hψ : ∑ z, ‖ψ z‖ ^ 2 = 1) (V : Matrix a a ℂ)
    (hVV : Vᴴ * V = 1) (hVV' : V * Vᴴ = 1) (lam : a → ℝ)
    (hρ : coefMat ψ * (coefMat ψ)ᴴ = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) :
    (∀ x y, star (fun i => V i x) ⬝ᵥ (fun i => V i y) = if x = y then 1 else 0) ∧
    (∀ x y, star ((Vᴴ * coefMat ψ) x) ⬝ᵥ (Vᴴ * coefMat ψ) y
      = if x = y then (lam x : ℂ) else 0) ∧
    (∀ x, 0 ≤ lam x) ∧ ∑ x, lam x = 1 ∧
    (∀ i k, ψ (i, k) = ∑ x, V i x * (Vᴴ * coefMat ψ) x k) := by
  set W := Vᴴ * coefMat ψ with hW
  have hWW : W * Wᴴ = diagonal (fun i => (lam i : ℂ)) := by
    rw [hW, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (coefMat ψ), hρ]
    simp only [Matrix.mul_assoc]
    rw [hVV, Matrix.mul_one, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have := congrFun (congrFun hVV x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    simp [dotProduct, conjTranspose_apply]
  · intro x y
    have := congrFun (congrFun hWW y) x
    rw [Matrix.mul_apply, diagonal_apply] at this
    simp only [dotProduct, Pi.star_apply]
    rw [show (if x = y then (lam x : ℂ) else 0) = if y = x then (lam y : ℂ) else 0 by
      by_cases h : x = y
      · subst h; simp
      · simp [h, Ne.symm h], ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, mul_comm]
  · intro x
    have h0 : (0 : ℂ) ≤ (W * Wᴴ) x x :=
      (Matrix.posSemidef_self_mul_conjTranspose W).diag_nonneg
    rw [hWW, diagonal_apply_eq] at h0
    exact_mod_cast h0
  · have h1 := trace_rho ψ
    rw [hψ, hρ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul,
      trace_diagonal] at h1
    exact_mod_cast h1
  · intro i k
    have : V * W = coefMat ψ := by rw [hW, ← Matrix.mul_assoc, hVV', Matrix.one_mul]
    have := congrFun (congrFun this i) k
    rw [Matrix.mul_apply] at this
    rw [this]; rfl

/-- Entropy core: `S(ρ) = -∑ λ log₂ λ` from a diagonalisation of `ρ` and of `log ρ`. -/
lemma vn_core (ρ V : Matrix a a ℂ) (hVV : Vᴴ * V = 1) (lam : a → ℝ)
    (hρ : ρ = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ)
    (hlog : cfc (Real.logb 2) ρ = V * diagonal (fun i => (Real.logb 2 (lam i) : ℂ)) * Vᴴ) :
    QMemory.vonNeumann ρ = -∑ x, lam x * Real.logb 2 (lam x) := by
  unfold QMemory.vonNeumann
  rw [hlog]
  conv_lhs => rw [hρ]
  have e : V * diagonal (fun i => (lam i : ℂ)) * Vᴴ *
      (V * diagonal (fun i => (Real.logb 2 (lam i) : ℂ)) * Vᴴ)
      = V * diagonal (fun i => ((lam i * Real.logb 2 (lam i) : ℝ) : ℂ)) * Vᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    congr 3; funext i; push_cast; ring
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul, trace_diagonal]
  simp [Complex.re_sum]

/-- K3: Schmidt form and the entropy of entanglement. -/
theorem k3 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ : a × b → ℂ) (hψ : ∑ z, ‖ψ z‖ ^ 2 = 1) :
    ∃ (e : a → a → ℂ) (w : a → b → ℂ) (p : a → ℝ),
      (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) ∧
      (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0) ∧
      (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
      (∀ i k, ψ (i, k) = ∑ x, e x i * w x k) ∧
      WildeQIT.EntManip.entEntropy ψ = -∑ x, p x * Real.logb 2 (p x) := by
  have hH : (partialTraceRight (ObliviousRSP.pureState ψ)).IsHermitian := by
    rw [rho_eq]; exact (Matrix.posSemidef_self_mul_conjTranspose _).isHermitian
  have hsp := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  have hVV : (hH.eigenvectorUnitary : Matrix a a ℂ)ᴴ * hH.eigenvectorUnitary = 1 :=
    Unitary.coe_star_mul_self _
  have hVV' : (hH.eigenvectorUnitary : Matrix a a ℂ) * (hH.eigenvectorUnitary : Matrix a a ℂ)ᴴ
      = 1 := Unitary.coe_mul_star_self _
  have hρ : partialTraceRight (ObliviousRSP.pureState ψ)
      = (hH.eigenvectorUnitary : Matrix a a ℂ) * diagonal (fun i => (hH.eigenvalues i : ℂ)) *
        (hH.eigenvectorUnitary : Matrix a a ℂ)ᴴ := hsp
  have hlog : cfc (Real.logb 2) (partialTraceRight (ObliviousRSP.pureState ψ))
      = (hH.eigenvectorUnitary : Matrix a a ℂ) *
        diagonal (fun i => (Real.logb 2 (hH.eigenvalues i) : ℂ)) *
        (hH.eigenvectorUnitary : Matrix a a ℂ)ᴴ := by
    rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl
  have hρ' := (rho_eq ψ).symm.trans hρ
  obtain ⟨h1, h2, h3, h4, h5⟩ := k3_core ψ hψ _ hVV hVV' _ hρ'
  refine ⟨fun x i => (hH.eigenvectorUnitary : Matrix a a ℂ) i x, _, _, h1, h2, h3, h4, h5, ?_⟩
  exact vn_core _ _ hVV _ hρ hlog

end K3

end EntManip2ba

end F2

section F3


/-! 2ba22dc4 K4: Schmidt-rank overlap bound for product Kraus families (converse core). -/


open scoped Matrix Kronecker

namespace EntManip2ba

open Matrix Finset

/-- Squared Euclidean norm. -/
noncomputable def N2 {n : Type} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma N2_nonneg {n : Type} [Fintype n] (v : n → ℂ) : 0 ≤ N2 v :=
  Finset.sum_nonneg fun i _ => by positivity

lemma star_mul_self_c (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma nc_eq {n : Type} [Fintype n] (v : n → ℂ) : star v ⬝ᵥ v = (N2 v : ℂ) := by
  rw [N2, Complex.ofReal_sum]
  simp only [dotProduct, Pi.star_apply, star_mul_self_c]

lemma N2_of_dot {n : Type} [Fintype n] (v : n → ℂ) (r : ℝ) (h : star v ⬝ᵥ v = (r : ℂ)) :
    N2 v = r := by
  rw [nc_eq] at h
  exact_mod_cast h

lemma cs {n : Type} [Fintype n] (v z : n → ℂ) : ‖star v ⬝ᵥ z‖ ^ 2 ≤ N2 v * N2 z := by
  have h1 : ‖star v ⬝ᵥ z‖ ≤ ∑ i, ‖v i‖ * ‖z i‖ := by
    simp only [dotProduct, Pi.star_apply]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun i => ‖z i‖)
  calc ‖star v ⬝ᵥ z‖ ^ 2 ≤ (∑ i, ‖v i‖ * ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

lemma kraus_N2 {m n J : Type} [Fintype m] [Fintype n] [Fintype J] [DecidableEq n]
    (K : J → Matrix m n ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (v : n → ℂ) :
    ∑ j, N2 (K j *ᵥ v) = N2 v := by
  have h : ∀ j, star (K j *ᵥ v) ⬝ᵥ (K j *ᵥ v) = star v ⬝ᵥ (((K j)ᴴ * K j) *ᵥ v) := by
    intro j
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
  have hc : ((∑ j, N2 (K j *ᵥ v) : ℝ) : ℂ) = (N2 v : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [← nc_eq, h]
    rw [← dotProduct_sum, ← sum_mulVec, hK, one_mulVec]
  exact_mod_cast hc

lemma kraus_cs {m n J : Type} [Fintype m] [Fintype n] [Fintype J] [DecidableEq n]
    (K : J → Matrix m n ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (u : m → ℂ) (v : n → ℂ) :
    ∑ j, ‖star u ⬝ᵥ (K j *ᵥ v)‖ ^ 2 ≤ N2 u * N2 v := by
  calc _ ≤ ∑ j, N2 u * N2 (K j *ᵥ v) := Finset.sum_le_sum fun j _ => cs _ _
    _ = _ := by rw [← Finset.mul_sum, kraus_N2 K hK v]

/-- Product vector `u x ⊗ v x`. -/
def pv {X a b : Type} (u : X → a → ℂ) (v : X → b → ℂ) (x : X) : a × b → ℂ :=
  fun z => u x z.1 * v x z.2

lemma pv_dot {X Y a b : Type} [Fintype a] [Fintype b] (u : X → a → ℂ) (v : X → b → ℂ)
    (u' : Y → a → ℂ) (v' : Y → b → ℂ) (x : X) (y : Y) :
    star (pv u v x) ⬝ᵥ pv u' v' y = (star (u x) ⬝ᵥ u' y) * (star (v x) ⬝ᵥ v' y) := by
  simp only [pv, dotProduct, Pi.star_apply, Fintype.sum_prod_type, Finset.sum_mul_sum,
    star_mul']
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma N2_pv {X a b : Type} [Fintype a] [Fintype b] (u : X → a → ℂ) (v : X → b → ℂ) (x : X) :
    N2 (pv u v x) = N2 (u x) * N2 (v x) := by
  simp only [N2, pv, Fintype.sum_prod_type, norm_mul, mul_pow, Finset.sum_mul_sum]

lemma kron_pv {X a b a' b' : Type} [Fintype a] [Fintype b] (A : Matrix a' a ℂ)
    (B : Matrix b' b ℂ) (u : X → a → ℂ) (v : X → b → ℂ) (x : X) :
    (A ⊗ₖ B) *ᵥ pv u v x = pv (fun x => A *ᵥ u x) (fun x => B *ᵥ v x) x := by
  ext ⟨i, k⟩
  simp only [pv, mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k' _ => by ring

lemma N2_psum {X a b : Type} [Fintype a] [Fintype b] [DecidableEq X] (u : X → a → ℂ)
    (v : X → b → ℂ) (p : X → ℝ) (hu : ∀ x y, star (u x) ⬝ᵥ u y = if x = y then 1 else 0)
    (hv : ∀ x y, star (v x) ⬝ᵥ v y = if x = y then (p x : ℂ) else 0) (s : Finset X) :
    N2 (∑ x ∈ s, pv u v x) = ∑ x ∈ s, p x := by
  have h : ((N2 (∑ x ∈ s, pv u v x) : ℝ) : ℂ) = ((∑ x ∈ s, p x : ℝ) : ℂ) := by
    rw [← nc_eq, star_sum, sum_dotProduct, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [dotProduct_sum, Finset.sum_eq_single x]
    · rw [pv_dot, hu, hv, if_pos rfl, if_pos rfl, one_mul]
    · intro y _ hy
      rw [pv_dot, hu, if_neg (Ne.symm hy), zero_mul]
    · intro h
      exact absurd hx h
  exact_mod_cast h

/-- Bessel inequality for an orthogonal family with squared norms at most `θ`. -/
lemma bessel {Y n : Type} [Fintype n] (f : Y → n → ℂ) (s : Finset Y) (θ : ℝ) (hθ : 0 ≤ θ)
    (horth : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → star (f y) ⬝ᵥ f y' = 0)
    (hq : ∀ y ∈ s, N2 (f y) ≤ θ) (z : n → ℂ) :
    ∑ y ∈ s, ‖star (f y) ⬝ᵥ z‖ ^ 2 ≤ θ * N2 z := by
  set G := ∑ y ∈ s, ‖star (f y) ⬝ᵥ z‖ ^ 2 with hG
  set v : n → ℂ := ∑ y ∈ s, (star (f y) ⬝ᵥ z) • f y with hv
  have h1 : star v ⬝ᵥ z = (G : ℂ) := by
    rw [hv, star_sum, sum_dotProduct, hG, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_smul, smul_dotProduct, smul_eq_mul, star_mul_self_c]
  have e : (N2 v : ℂ) = ((∑ y ∈ s, ‖star (f y) ⬝ᵥ z‖ ^ 2 * N2 (f y) : ℝ) : ℂ) := by
    rw [← nc_eq, hv, star_sum, sum_dotProduct, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [dotProduct_sum, Finset.sum_eq_single y]
    · rw [star_smul, smul_dotProduct, dotProduct_smul, nc_eq, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, star_mul_self_c]
      push_cast
      ring
    · intro y' hy' hne
      rw [star_smul, smul_dotProduct, dotProduct_smul, horth y hy y' hy' (Ne.symm hne)]
      simp
    · intro h
      exact absurd hy h
  have e' : N2 v = ∑ y ∈ s, ‖star (f y) ⬝ᵥ z‖ ^ 2 * N2 (f y) := by exact_mod_cast e
  have h2 : N2 v ≤ θ * G := by
    rw [e', hG, Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    rw [mul_comm θ]
    exact mul_le_mul_of_nonneg_left (hq y hy) (by positivity)
  have h3 : G ^ 2 ≤ N2 v * N2 z := by
    have := cs v z
    rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    exact this
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun y _ => by positivity
  have hz := N2_nonneg z
  have h4 : G ^ 2 ≤ θ * G * N2 z := h3.trans (mul_le_mul_of_nonneg_right h2 hz)
  rcases hG0.lt_or_eq with hpos | h0
  · nlinarith
  · rw [← h0]
    exact mul_nonneg hθ hz

lemma cpart_x {X Y a' b' : Type} [Fintype a'] [Fintype b'] [DecidableEq Y]
    (e : Y → a' → ℂ) (w : Y → b' → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0)
    (S : Finset Y) (θ : ℝ) (hθ : 0 ≤ θ) (hS : ∀ y ∈ S, q y ≤ θ)
    (f : X → a' → ℂ) (g : X → b' → ℂ) (x : X) :
    ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ pv f g x‖ ^ 2 ≤ θ * (N2 (f x) * N2 (g x)) := by
  have h1 : star (∑ y ∈ S, pv e w y) ⬝ᵥ pv f g x
      = ∑ y ∈ S, (star (e y) ⬝ᵥ f x) * (star (w y) ⬝ᵥ g x) := by
    rw [star_sum, sum_dotProduct]
    exact Finset.sum_congr rfl fun y _ => pv_dot _ _ _ _ _ _
  have hb1 := bessel e S 1 zero_le_one (fun y _ y' _ h => by rw [he, if_neg h])
    (fun y _ => le_of_eq (N2_of_dot _ _ (by rw [he, if_pos rfl]; simp))) (f x)
  have hb2 := bessel w S θ hθ (fun y _ y' _ h => by rw [hw, if_neg h])
    (fun y hy => (N2_of_dot _ _ (by rw [hw, if_pos rfl])).trans_le (hS y hy)) (g x)
  rw [h1]
  calc ‖∑ y ∈ S, (star (e y) ⬝ᵥ f x) * (star (w y) ⬝ᵥ g x)‖ ^ 2
      ≤ (∑ y ∈ S, ‖star (e y) ⬝ᵥ f x‖ * ‖star (w y) ⬝ᵥ g x‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun y _ => norm_mul _ _
    _ ≤ (∑ y ∈ S, ‖star (e y) ⬝ᵥ f x‖ ^ 2) * (∑ y ∈ S, ‖star (w y) ⬝ᵥ g x‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (1 * N2 (f x)) * (θ * N2 (g x)) :=
        mul_le_mul hb1 hb2 (Finset.sum_nonneg fun _ _ => by positivity)
          (by rw [one_mul]; exact N2_nonneg _)
    _ = θ * (N2 (f x) * N2 (g x)) := by ring

lemma cpart {X Y J a b a' b' : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Fintype a'] [Fintype b'] [DecidableEq X] [DecidableEq Y] [Fintype J]
    (u : X → a → ℂ) (v : X → b → ℂ) (p : X → ℝ)
    (hu : ∀ x y, star (u x) ⬝ᵥ u y = if x = y then 1 else 0)
    (hv : ∀ x y, star (v x) ⬝ᵥ v y = if x = y then (p x : ℂ) else 0)
    (e : Y → a' → ℂ) (w : Y → b' → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0)
    (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ)
    (hc : ∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1)
    (T : Finset X) (S : Finset Y) (θ : ℝ) (hθ : 0 ≤ θ) (hS : ∀ y ∈ S, q y ≤ θ) :
    ∑ j, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x)‖ ^ 2
      ≤ T.card * (θ * ∑ x ∈ T, p x) := by
  have hj : ∀ j, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x)‖ ^ 2
      ≤ T.card * (θ * ∑ x ∈ T, N2 ((A j ⊗ₖ B j) *ᵥ pv u v x)) := by
    intro j
    rw [mulVec_sum, dotProduct_sum]
    calc _ ≤ (∑ x ∈ T, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ pv u v x)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ T.card * ∑ x ∈ T, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ pv u v x)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ T.card * ∑ x ∈ T, θ * N2 ((A j ⊗ₖ B j) *ᵥ pv u v x) := by
          gcongr with x hx
          rw [kron_pv, N2_pv]
          exact cpart_x e w q he hw S θ hθ hS _ _ x
      _ = _ := by rw [← Finset.mul_sum]
  have hx : ∀ x, ∑ j, N2 ((A j ⊗ₖ B j) *ᵥ pv u v x) = p x := by
    intro x
    have h := kraus_N2 (fun j => A j ⊗ₖ B j) hc (pv u v x)
    rw [h, N2_pv, N2_of_dot _ 1 (by rw [hu, if_pos rfl]; simp),
      N2_of_dot _ (p x) (by rw [hv, if_pos rfl]), one_mul]
  calc _ ≤ ∑ j, T.card * (θ * ∑ x ∈ T, N2 ((A j ⊗ₖ B j) *ᵥ pv u v x)) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = T.card * (θ * ∑ x ∈ T, ∑ j, N2 ((A j ⊗ₖ B j) *ᵥ pv u v x)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    _ = T.card * (θ * ∑ x ∈ T, p x) := by
        simp only [hx]

lemma sq3 (x y z : ℂ) : ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h0 := norm_nonneg (x + y + z)
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg z, sq_nonneg (‖x‖ - ‖y‖),
    sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖), mul_le_mul h h h0 (by positivity)]

/-- K4: overlap of a product-Kraus image of `ψ = ∑ u x ⊗ v x` with `φ = ∑ e y ⊗ w y`. -/
theorem k4 {a b a' b' X Y J : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    [DecidableEq a] [DecidableEq b] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype J]
    (u : X → a → ℂ) (v : X → b → ℂ) (p : X → ℝ)
    (hu : ∀ x y, star (u x) ⬝ᵥ u y = if x = y then 1 else 0)
    (hv : ∀ x y, star (v x) ⬝ᵥ v y = if x = y then (p x : ℂ) else 0)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (e : Y → a' → ℂ) (w : Y → b' → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0)
    (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ)
    (hc : ∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1) (T : Finset X) (θ : ℝ) (hθ : 0 < θ) :
    ∑ j, ‖star (∑ y, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)‖ ^ 2
      ≤ 3 * ((∑ y ∈ univ.filter (fun y => θ < q y), q y) + θ * T.card + ∑ x ∈ Tᶜ, p x) := by
  set L := univ.filter (fun y : Y => θ < q y) with hL
  set S := univ.filter (fun y : Y => ¬ θ < q y) with hS
  have hφ : (∑ y, pv e w y) = (∑ y ∈ L, pv e w y) + ∑ y ∈ S, pv e w y :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hψ : (∑ x, pv u v x) = (∑ x ∈ T, pv u v x) + ∑ x ∈ Tᶜ, pv u v x :=
    (Finset.sum_add_sum_compl _ _).symm
  have split : ∀ j, star (∑ y, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)
      = star (∑ y ∈ L, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)
        + star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ Tᶜ, pv u v x)
        + star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x) := by
    intro j
    have e1 : star (∑ y, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)
        = star (∑ y ∈ L, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)
          + star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x) := by
      rw [← add_dotProduct, ← star_add, ← hφ]
    have e2 : star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)
        = star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ Tᶜ, pv u v x)
          + star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x) := by
      rw [← dotProduct_add, ← mulVec_add, add_comm (∑ x ∈ Tᶜ, pv u v x), ← hψ]
    rw [e1, e2, add_assoc]
  have hA : ∑ j, ‖star (∑ y ∈ L, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)‖ ^ 2
      ≤ ∑ y ∈ L, q y := by
    have h := kraus_cs (fun j => A j ⊗ₖ B j) hc (∑ y ∈ L, pv e w y) (∑ x, pv u v x)
    rw [N2_psum e w q he hw, N2_psum u v p hu hv, hp1, mul_one] at h
    exact h
  have hB : ∑ j, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ Tᶜ, pv u v x)‖ ^ 2
      ≤ ∑ x ∈ Tᶜ, p x := by
    have h := kraus_cs (fun j => A j ⊗ₖ B j) hc (∑ y ∈ S, pv e w y) (∑ x ∈ Tᶜ, pv u v x)
    rw [N2_psum e w q he hw, N2_psum u v p hu hv] at h
    have hS1 : ∑ y ∈ S, q y ≤ 1 := by
      rw [← hq1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hq0 y)
    have hT0 : 0 ≤ ∑ x ∈ Tᶜ, p x := Finset.sum_nonneg fun x _ => hp0 x
    exact h.trans (by nlinarith)
  have hC := cpart u v p hu hv e w q he hw A B hc T S θ hθ.le
    (fun y hy => not_lt.mp (Finset.mem_filter.mp hy).2)
  have hT1 : ∑ x ∈ T, p x ≤ 1 := by
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hp0 x)
  have hC' : ∑ j, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x)‖ ^ 2
      ≤ θ * T.card := by
    refine hC.trans ?_
    have hc0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hT1 hθ.le]
  calc _ = ∑ j, ‖star (∑ y ∈ L, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)
        + star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ Tᶜ, pv u v x)
        + star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x)‖ ^ 2 := by
        simp only [split]
    _ ≤ ∑ j, 3 * (‖star (∑ y ∈ L, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)‖ ^ 2
        + ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ Tᶜ, pv u v x)‖ ^ 2
        + ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x)‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => sq3 _ _ _
    _ = 3 * ((∑ j, ‖star (∑ y ∈ L, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)‖ ^ 2)
        + (∑ j, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ Tᶜ, pv u v x)‖ ^ 2)
        + ∑ j, ‖star (∑ y ∈ S, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x ∈ T, pv u v x)‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 3 * ((∑ y ∈ L, q y) + (∑ x ∈ Tᶜ, p x) + θ * T.card) := by
        gcongr
    _ = _ := by ring

end EntManip2ba

end F3

section F4


/-! 2ba22dc4 K5 (typicality / Chebyshev LLN for -log p^n) and K6 (tensor-power Schmidt form). -/


open scoped Matrix

namespace EntManip2ba

open Finset

section K5
variable {α : Type} [Fintype α]

lemma sum_succ_fun (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → α, f (Fin.cons a x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma iid_one (p : α → ℝ) (hp1 : ∑ a, p a = 1) (n : ℕ) :
    ∑ x : Fin n → α, ∏ i, p (x i) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum, ih,
      mul_one, hp1]

/-- Shannon entropy in bits. -/
noncomputable def ent (p : α → ℝ) : ℝ := -∑ a, p a * Real.logb 2 (p a)

/-- Centered information density. -/
noncomputable def hfun (p : α → ℝ) (a : α) : ℝ := -Real.logb 2 (p a) - ent p

lemma hfun_mean (p : α → ℝ) (hp1 : ∑ a, p a = 1) : ∑ a, p a * hfun p a = 0 := by
  have : ∑ a, p a * hfun p a
      = ∑ a, -(p a * Real.logb 2 (p a)) - (∑ a, p a) * ent p := by
    unfold hfun
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [this, hp1, Finset.sum_neg_distrib]
  unfold ent
  ring

lemma iid_mean (p : α → ℝ) (hp1 : ∑ a, p a = 1) (h : α → ℝ) (hm : ∑ a, p a * h a = 0)
    (n : ℕ) : ∑ x : Fin n → α, (∏ i, p (x i)) * ∑ i, h (x i) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h1 : ∀ a, ∑ x : Fin n → α, (p a * ∏ i, p (x i)) * (h a + ∑ i, h (x i))
        = p a * h a := by
      intro a
      calc _ = p a * h a * ∑ x : Fin n → α, ∏ i, p (x i)
              + p a * ∑ x : Fin n → α, (∏ i, p (x i)) * ∑ i, h (x i) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [iid_one p hp1, ih]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, hm]

lemma iid_var (p : α → ℝ) (hp1 : ∑ a, p a = 1) (h : α → ℝ) (hm : ∑ a, p a * h a = 0)
    (n : ℕ) : ∑ x : Fin n → α, (∏ i, p (x i)) * (∑ i, h (x i)) ^ 2
      = n * ∑ a, p a * h a ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h1 : ∀ a, ∑ x : Fin n → α, (p a * ∏ i, p (x i)) * (h a + ∑ i, h (x i)) ^ 2
        = p a * h a ^ 2 + p a * (n * ∑ a, p a * h a ^ 2) := by
      intro a
      calc _ = p a * h a ^ 2 * ∑ x : Fin n → α, ∏ i, p (x i)
              + 2 * p a * h a * ∑ x : Fin n → α, (∏ i, p (x i)) * ∑ i, h (x i)
              + p a * ∑ x : Fin n → α, (∏ i, p (x i)) * (∑ i, h (x i)) ^ 2 := by
                rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
                  ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun x _ => by ring
        _ = _ := by rw [iid_one p hp1, iid_mean p hp1 h hm, ih]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, ← Finset.sum_mul, hp1]
    push_cast
    ring

lemma cheb (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (h : α → ℝ)
    (hm : ∑ a, p a * h a = 0) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    ∑ x ∈ univ.filter (fun x : Fin n → α => t ≤ |∑ i, h (x i)|), ∏ i, p (x i)
      ≤ (n * ∑ a, p a * h a ^ 2) / t ^ 2 := by
  rw [le_div_iff₀ (by positivity), ← iid_var p hp1 h hm n, Finset.sum_mul]
  calc _ ≤ ∑ x ∈ univ.filter (fun x : Fin n → α => t ≤ |∑ i, h (x i)|),
        (∏ i, p (x i)) * (∑ i, h (x i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter] at hx
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hp0 (x i))
        have h2 := hx.2
        nlinarith [mul_le_mul h2 h2 ht.le (abs_nonneg _), sq_abs (∑ i, h (x i))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => hp0 (x i)) (sq_nonneg _))

lemma prob_eq (p : α → ℝ) (n : ℕ) (x : Fin n → α) (hx : 0 < ∏ i, p (x i)) :
    ∏ i, p (x i) = (2 : ℝ) ^ (-(∑ i, hfun p (x i)) - n * ent p) := by
  have hne : ∀ i ∈ (univ : Finset (Fin n)), p (x i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (ne_of_gt hx)
  calc ∏ i, p (x i) = (2 : ℝ) ^ Real.logb 2 (∏ i, p (x i)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ = _ := by
        congr 1
        rw [Real.logb_prod _ _ hne]
        unfold hfun
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

/-- K5a: a set of `p^n`-positive sequences with `∑ hfun < nδ` has at most `2^{n(H+δ)}` elements. -/
lemma typ_card (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (n : ℕ) (δ : ℝ)
    (S : Finset (Fin n → α))
    (hS : ∀ x ∈ S, 0 < ∏ i, p (x i) ∧ ∑ i, hfun p (x i) < n * δ) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ (n * (ent p + δ)) := by
  have hle : ∀ x ∈ S, (2 : ℝ) ^ (-(n * (ent p + δ))) ≤ ∏ i, p (x i) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hS x hx
    rw [prob_eq p n x h1]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have e1 : (n : ℝ) * (ent p + δ) = n * ent p + n * δ := by ring
    rw [e1]
    linarith
  have key : (S.card : ℝ) * (2 : ℝ) ^ (-(n * (ent p + δ))) ≤ 1 := by
    have h3 : ∑ x ∈ S, (2 : ℝ) ^ (-(n * (ent p + δ))) ≤ ∑ x ∈ S, ∏ i, p (x i) :=
      Finset.sum_le_sum hle
    have h4 : ∑ x ∈ S, ∏ i, p (x i) ≤ ∑ x : Fin n → α, ∏ i, p (x i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun (x : Fin n → α) _ _ => Finset.prod_nonneg fun i _ => hp0 (x i))
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    rw [iid_one p hp1 n] at h4
    linarith
  have h2 : (2 : ℝ) ^ (-(n * (ent p + δ))) * (2 : ℝ) ^ (n * (ent p + δ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ (n * (ent p + δ)) := by positivity
  calc (S.card : ℝ) = (S.card : ℝ) * (2 : ℝ) ^ (-(n * (ent p + δ)))
        * (2 : ℝ) ^ (n * (ent p + δ)) := by rw [mul_assoc, h2, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (n * (ent p + δ)) := mul_le_mul_of_nonneg_right key h5
    _ = _ := one_mul _

/-- K5b: Chebyshev tail of the information density. -/
lemma tail_le (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ : 0 < δ) :
    ∑ x ∈ univ.filter (fun x : Fin n → α => n * δ ≤ |∑ i, hfun p (x i)|), ∏ i, p (x i)
      ≤ (∑ a, p a * hfun p a ^ 2) / (δ ^ 2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := cheb p hp0 hp1 (hfun p) (hfun_mean p hp1) n (n * δ) (by positivity)
  calc _ ≤ _ := h
    _ = _ := by field_simp

end K5

section K6

lemma tp_dot {ι κ : Type} [Fintype κ] (u v : ι → κ → ℂ) (n : ℕ) (x y : Fin n → ι) :
    star (fun i : Fin n → κ => ∏ t, u (x t) (i t)) ⬝ᵥ (fun i => ∏ t, v (y t) (i t))
      = ∏ t, star (u (x t)) ⬝ᵥ v (y t) := by
  simp only [dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [eq_comm, Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma prod_ite_eq_ite {ι : Type} [DecidableEq ι] {n : ℕ} (x y : Fin n → ι) (c : ι → ℂ) :
    ∏ t, (if x t = y t then c (x t) else 0) = if x = y then ∏ t, c (x t) else 0 := by
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨t, ht⟩ : ∃ t, x t ≠ y t := by
      by_contra hc
      exact h (funext fun t => not_not.mp fun h' => hc ⟨t, h'⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])

lemma tp_decomp {a b : Type} (ψ : a × b → ℂ) {ι : Type} [Fintype ι] (e : ι → a → ℂ)
    (w : ι → b → ℂ) (hd : ∀ i k, ψ (i, k) = ∑ x, e x i * w x k) (n : ℕ)
    (i : Fin n → a) (k : Fin n → b) :
    WildeQIT.EntManip.tensorPowVec ψ n (i, k)
      = ∑ x : Fin n → ι, (∏ t, e (x t) (i t)) * ∏ t, w (x t) (k t) := by
  simp only [WildeQIT.EntManip.tensorPowVec, hd, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- K6: Schmidt data of `ψ` tensorises to Schmidt data of `ψ^{⊗n}`. -/
theorem k6 {a b : Type} [Fintype a] [Fintype b] (ψ : a × b → ℂ) {ι : Type} [Fintype ι]
    [DecidableEq ι]
    (e : ι → a → ℂ) (w : ι → b → ℂ) (p : ι → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0)
    (hd : ∀ i k, ψ (i, k) = ∑ x, e x i * w x k) (n : ℕ) :
    (∀ x y : Fin n → ι, star (fun i : Fin n → a => ∏ t, e (x t) (i t)) ⬝ᵥ
        (fun i => ∏ t, e (y t) (i t)) = if x = y then 1 else 0) ∧
    (∀ x y : Fin n → ι, star (fun k : Fin n → b => ∏ t, w (x t) (k t)) ⬝ᵥ
        (fun k => ∏ t, w (y t) (k t)) = if x = y then ((∏ t, p (x t) : ℝ) : ℂ) else 0) ∧
    (∀ i k, WildeQIT.EntManip.tensorPowVec ψ n (i, k)
      = ∑ x : Fin n → ι, (∏ t, e (x t) (i t)) * ∏ t, w (x t) (k t)) := by
  refine ⟨fun x y => ?_, fun x y => ?_, tp_decomp ψ e w hd n⟩
  · rw [tp_dot]
    simp only [he]
    have := prod_ite_eq_ite x y (fun _ => (1 : ℂ))
    simpa using this
  · rw [tp_dot]
    simp only [hw]
    rw [prod_ite_eq_ite x y (fun z => (p z : ℂ))]
    push_cast
    try rfl

end K6

end EntManip2ba

end F4

section F5


/-! 2ba22dc4 converse assembly (ChildConverse) from the infrastructure children,
which enter as `Prop` hypotheses (K1, K2a, K3, K4, K6, K5 pieces); at merge time
they are discharged by `k1`, `k2a`, `k3`, `k4`, `k6`, `typ_card`, `tail_le`,
`prob_eq`, `iid_one`. -/


open scoped Kronecker Matrix ComplexOrder

namespace EntManip2baC

open WildeQIT.EntManip Matrix Finset Filter

/-- Duplicates of the K4/K5 definitions (identical copies are dropped at merge). -/
def pv {X a b : Type} (u : X → a → ℂ) (v : X → b → ℂ) (x : X) : a × b → ℂ :=
  fun z => u x z.1 * v x z.2

noncomputable def ent {α : Type} [Fintype α] (p : α → ℝ) : ℝ := -∑ a, p a * Real.logb 2 (p a)

noncomputable def hfun {α : Type} [Fintype α] (p : α → ℝ) (a : α) : ℝ :=
  -Real.logb 2 (p a) - ent p

def K1_LOCCKraus : Prop :=
  ∀ {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ), IsLOCC Λ →
    ∃ (J : Type) (_ : Fintype J) (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ),
      (∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1) ∧
      ∀ ρ, Λ ρ = ∑ j, (A j ⊗ₖ B j) * ρ * (A j ⊗ₖ B j)ᴴ

def K2a_traceNorm_ge : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] (M Q : Matrix n n ℂ), M.IsHermitian →
    (1 - Qᴴ * Q).PosSemidef → (Matrix.trace (Q * M)).re ≤ WildeQIT.traceNorm M

def K3_Schmidt : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 →
    ∃ (e : a → a → ℂ) (w : a → b → ℂ) (p : a → ℝ),
      (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) ∧
      (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0) ∧
      (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
      (∀ i k, ψ (i, k) = ∑ x, e x i * w x k) ∧
      entEntropy ψ = -∑ x, p x * Real.logb 2 (p x)

def K4P : Prop :=
  ∀ {a b a' b' X Y J : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    [DecidableEq a] [DecidableEq b] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype J]
    (u : X → a → ℂ) (v : X → b → ℂ) (p : X → ℝ),
    (∀ x y, star (u x) ⬝ᵥ u y = if x = y then 1 else 0) →
    (∀ x y, star (v x) ⬝ᵥ v y = if x = y then (p x : ℂ) else 0) →
    (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
    ∀ (e : Y → a' → ℂ) (w : Y → b' → ℂ) (q : Y → ℝ),
    (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) →
    (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0) →
    (∀ y, 0 ≤ q y) → ∑ y, q y = 1 →
    ∀ (A : J → Matrix a' a ℂ) (B : J → Matrix b' b ℂ),
    ∑ j, (A j ⊗ₖ B j)ᴴ * (A j ⊗ₖ B j) = 1 → ∀ (T : Finset X) (θ : ℝ), 0 < θ →
    ∑ j, ‖star (∑ y, pv e w y) ⬝ᵥ ((A j ⊗ₖ B j) *ᵥ ∑ x, pv u v x)‖ ^ 2
      ≤ 3 * ((∑ y ∈ univ.filter (fun y => θ < q y), q y) + θ * T.card + ∑ x ∈ Tᶜ, p x)

def K6P : Prop :=
  ∀ {a b : Type} [Fintype a] [Fintype b] (ψ : a × b → ℂ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (e : ι → a → ℂ) (w : ι → b → ℂ) (p : ι → ℝ),
    (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) →
    (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0) →
    (∀ i k, ψ (i, k) = ∑ x, e x i * w x k) → ∀ (n : ℕ),
    (∀ x y : Fin n → ι, star (fun i : Fin n → a => ∏ t, e (x t) (i t)) ⬝ᵥ
        (fun i => ∏ t, e (y t) (i t)) = if x = y then 1 else 0) ∧
    (∀ x y : Fin n → ι, star (fun k : Fin n → b => ∏ t, w (x t) (k t)) ⬝ᵥ
        (fun k => ∏ t, w (y t) (k t)) = if x = y then ((∏ t, p (x t) : ℝ) : ℂ) else 0) ∧
    (∀ i k, WildeQIT.EntManip.tensorPowVec ψ n (i, k)
      = ∑ x : Fin n → ι, (∏ t, e (x t) (i t)) * ∏ t, w (x t) (k t))

def TypP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ), (∀ a, 0 ≤ p a) → ∑ a, p a = 1 →
    ∀ (n : ℕ) (δ : ℝ) (S : Finset (Fin n → α)),
    (∀ x ∈ S, 0 < ∏ i, p (x i) ∧ ∑ i, hfun p (x i) < n * δ) →
    (S.card : ℝ) ≤ (2 : ℝ) ^ (n * (ent p + δ))

def TailP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ), (∀ a, 0 ≤ p a) → ∑ a, p a = 1 →
    ∀ (n : ℕ), 0 < n → ∀ (δ : ℝ), 0 < δ →
    ∑ x ∈ univ.filter (fun x : Fin n → α => n * δ ≤ |∑ i, hfun p (x i)|), ∏ i, p (x i)
      ≤ (∑ a, p a * hfun p a ^ 2) / (δ ^ 2 * n)

def ProbP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ) (n : ℕ) (x : Fin n → α), 0 < ∏ i, p (x i) →
    ∏ i, p (x i) = (2 : ℝ) ^ (-(∑ i, hfun p (x i)) - n * ent p)

def IidP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ), ∑ a, p a = 1 → ∀ (n : ℕ),
    ∑ x : Fin n → α, ∏ i, p (x i) = 1

/-! ### Fidelity step -/

lemma dot_self {ι : Type} [Fintype ι] (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma tr_vmv {ι : Type} [Fintype ι] (u v : ι → ℂ) :
    trace (vecMulVec u v) = ∑ i, u i * v i := by
  simp [Matrix.trace, vecMulVec_apply]

lemma tvv {ι : Type} [Fintype ι] (u v : ι → ℂ) :
    trace (vecMulVec u (star u) * vecMulVec v (star v)) = ((‖star u ⬝ᵥ v‖ ^ 2 : ℝ) : ℂ) := by
  have h : trace (vecMulVec u (star u) * vecMulVec v (star v))
      = (star u ⬝ᵥ v) * star (star u ⬝ᵥ v) := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, vecMulVec_apply, dotProduct, Pi.star_apply,
      star_sum, star_mul', star_star, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, Complex.star_def, Complex.mul_conj']
  push_cast; ring

lemma herm_vmv {ι : Type} [Fintype ι] (u : ι → ℂ) :
    (vecMulVec u (star u))ᴴ = vecMulVec u (star u) := by
  ext i k
  simp [vecMulVec_apply, conjTranspose_apply, mul_comm]

theorem fid_half (hK2a : K2a_traceNorm_ge) {ι κ J : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype J]
    (Ψ : ι → ℂ) (Φ : κ → ℂ) (hΨ : ∑ i, ‖Ψ i‖ ^ 2 = 1) (hΦ : ∑ i, ‖Φ i‖ ^ 2 = 1)
    (K : J → Matrix κ ι ℂ) (hc : ∑ j, (K j)ᴴ * K j = 1) (ε : ℝ)
    (h : (1 / 2 : ℝ) * WildeQIT.traceNorm
      (∑ j, K j * vecMulVec Ψ (star Ψ) * (K j)ᴴ - vecMulVec Φ (star Φ)) ≤ ε) :
    1 - ε ≤ ∑ j, ‖star Φ ⬝ᵥ (K j *ᵥ Ψ)‖ ^ 2 := by
  set P := vecMulVec Φ (star Φ) with hP
  set ρ := vecMulVec Ψ (star Ψ) with hρ
  set F := ∑ j, ‖star Φ ⬝ᵥ (K j *ᵥ Ψ)‖ ^ 2 with hFdef
  have hΦ' : ∑ i, Φ i * star (Φ i) = 1 := by
    have := dot_self Φ
    rw [hΦ] at this
    simpa [dotProduct, mul_comm] using this
  have hΨ' : ∑ i, Ψ i * star (Ψ i) = 1 := by
    have := dot_self Ψ
    rw [hΨ] at this
    simpa [dotProduct, mul_comm] using this
  have hω : ∀ j, K j * ρ * (K j)ᴴ = vecMulVec (K j *ᵥ Ψ) (star (K j *ᵥ Ψ)) := by
    intro j
    ext i k
    simp only [hρ, mul_apply, vecMulVec_apply, mulVec, dotProduct, conjTranspose_apply,
      Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hPP : P * P = P := by
    ext i k
    simp only [hP, mul_apply, vecMulVec_apply, Pi.star_apply]
    calc ∑ j, Φ i * star (Φ j) * (Φ j * star (Φ k))
        = Φ i * star (Φ k) * ∑ j, Φ j * star (Φ j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = Φ i * star (Φ k) := by rw [hΦ', mul_one]
  have hPh : Pᴴ = P := herm_vmv Φ
  set ω := ∑ j, K j * ρ * (K j)ᴴ with hωdef
  set M := ω - P with hM
  have hMh : M.IsHermitian := by
    show (ω - P)ᴴ = ω - P
    rw [conjTranspose_sub, hPh, hωdef, conjTranspose_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hω j, herm_vmv]
  set Q : Matrix κ κ ℂ := 1 - P - P with hQ
  have hQh : Qᴴ = Q := by
    rw [hQ, conjTranspose_sub, conjTranspose_sub, conjTranspose_one, hPh]
  have hQQ : 1 - Qᴴ * Q = 0 := by
    rw [hQh, hQ]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPP]
    abel
  have hk := hK2a M Q hMh (by rw [hQQ]; exact Matrix.PosSemidef.zero)
  have htrP : trace P = 1 := by rw [hP, tr_vmv]; exact hΦ'
  have htrω : trace ω = 1 := by
    have e : ∀ j, trace (K j * ρ * (K j)ᴴ) = trace ((K j)ᴴ * K j * ρ) := fun j => by
      rw [trace_mul_comm, ← Matrix.mul_assoc]
    rw [hωdef, trace_sum, Finset.sum_congr rfl (fun j _ => e j), ← trace_sum,
      ← Finset.sum_mul, hc, Matrix.one_mul, hρ, tr_vmv]
    exact hΨ'
  have htrPω : trace (P * ω) = (F : ℂ) := by
    rw [hωdef, Matrix.mul_sum, trace_sum, hFdef]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hω j, hP, tvv] <;> norm_cast
  have key : trace (Q * M) = ((2 - 2 * F : ℝ) : ℂ) := by
    have e1 : trace (Q * M) = trace M - trace (P * M) - trace (P * M) := by
      rw [hQ, sub_mul, sub_mul, Matrix.one_mul, trace_sub, trace_sub]
    have e2 : trace M = 0 := by rw [hM, trace_sub, htrω, htrP, sub_self]
    have e3 : trace (P * M) = (F : ℂ) - 1 := by
      rw [hM, Matrix.mul_sub, trace_sub, htrPω, hPP, htrP]
    rw [e1, e2, e3]
    push_cast; ring
  rw [key, Complex.ofReal_re] at hk
  linarith

/-! ### Asymptotic core (classical) -/

lemma ent_nonneg {α : Type} [Fintype α] (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) : 0 ≤ ent p := by
  unfold ent
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun a _ => mul_nonpos_of_nonneg_of_nonpos (hp0 a)
    (Real.logb_nonpos (by norm_num) (hp0 a) ?_)
  rw [← hp1]
  exact Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)

theorem conv_core (hTyp : TypP) (hTail : TailP) (hProb : ProbP)
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] (p : X → ℝ) (q : Y → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hq : 0 < ent q) (r : ℝ) (hr : ent p < r * ent q) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → r * n ≤ m → ∃ (T : Finset (Fin n → X)) (θ : ℝ), 0 < θ ∧
      3 * ((∑ y ∈ univ.filter (fun y : Fin m → Y => θ < ∏ t, q (y t)), ∏ t, q (y t))
        + θ * T.card + ∑ x ∈ Tᶜ, ∏ t, p (x t)) < 1 / 2 := by
  have hp_ent : 0 ≤ ent p := ent_nonneg p hp0 hp1
  have hr0 : 0 < r := by
    by_contra h
    push_neg at h
    nlinarith
  have hg0 : 0 < r * ent q - ent p := by linarith
  have h1r : 0 < 1 + r := by linarith
  set η := min (ent q / 2) ((r * ent q - ent p) / (2 * (1 + r))) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  have hη1 : η ≤ ent q / 2 := min_le_left _ _
  have hη2 : η * (1 + r) ≤ (r * ent q - ent p) / 2 := by
    have := min_le_right (ent q / 2) ((r * ent q - ent p) / (2 * (1 + r)))
    calc η * (1 + r) ≤ (r * ent q - ent p) / (2 * (1 + r)) * (1 + r) :=
          mul_le_mul_of_nonneg_right this h1r.le
      _ = (r * ent q - ent p) / 2 := by
          rw [div_mul_eq_mul_div, mul_div_mul_right _ _ h1r.ne']
  set Vp := ∑ x, p x * hfun p x ^ 2 with hVp
  set Vq := ∑ y, q y * hfun q y ^ 2 with hVq
  have hVq0 : 0 ≤ Vq := Finset.sum_nonneg fun y _ => mul_nonneg (hq0 y) (sq_nonneg _)
  set c : ℝ := (2 : ℝ) ^ (-((r * ent q - ent p) / 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have e1 : ∀ᶠ n : ℕ in atTop, Vp / η ^ 2 / (n : ℝ) < 1 / 18 :=
    (tendsto_const_div_atTop_nhds_zero_nat _).eventually_lt_const (by norm_num)
  have e2 : ∀ᶠ n : ℕ in atTop, c ^ n < 1 / 18 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).eventually_lt_const (by norm_num)
  have e3 : ∀ᶠ n : ℕ in atTop, Vq / (η ^ 2 * r) / (n : ℝ) < 1 / 18 :=
    (tendsto_const_div_atTop_nhds_zero_nat _).eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (e1.and (e2.and (e3.and (Filter.eventually_ge_atTop 1))))
  refine ⟨N, fun n m hn hm => ?_⟩
  obtain ⟨h1, h2, h3, hn1⟩ := hN n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (mul_pos hr0 hnpos) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  set T := univ.filter (fun x : Fin n → X => 0 < ∏ t, p (x t) ∧ ∑ t, hfun p (x t) < n * η)
    with hT
  set θ : ℝ := (2 : ℝ) ^ (-((m : ℝ) * (ent q - η))) with hθ
  refine ⟨T, θ, by positivity, ?_⟩
  have hL : (∑ y ∈ univ.filter (fun y : Fin m → Y => θ < ∏ t, q (y t)), ∏ t, q (y t))
      ≤ Vq / (η ^ 2 * m) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hTail q hq0 hq1 m hm0 η hη0)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have hpos : 0 < ∏ t, q (y t) := lt_trans (by positivity) hy
      rw [hProb q m y hpos] at hy
      have hlt := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hy
      exact le_trans (by linarith) (neg_le_abs _)
    · intro y _ _
      exact Finset.prod_nonneg fun t _ => hq0 _
  have hL' : Vq / (η ^ 2 * m) ≤ Vq / (η ^ 2 * r) / n := by
    rw [div_div, mul_assoc]
    exact div_le_div_of_nonneg_left hVq0 (mul_pos (pow_pos hη0 2) (mul_pos hr0 hnpos))
      (mul_le_mul_of_nonneg_left hm (by positivity))
  have hTc : ∑ x ∈ Tᶜ, ∏ t, p (x t) ≤ Vp / (η ^ 2 * n) := by
    refine le_trans ?_ (hTail p hp0 hp1 n (by omega) η hη0)
    rw [← Finset.sum_filter_of_ne
      (p := fun x : Fin n → X => (n : ℝ) * η ≤ |∑ i, hfun p (x i)|) ?_]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      · intro x _ _
        exact Finset.prod_nonneg fun t _ => hp0 _
    · intro x hx hne
      simp only [hT, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
        not_lt] at hx
      have hpos : 0 < ∏ t, p (x t) :=
        lt_of_le_of_ne (Finset.prod_nonneg fun t _ => hp0 _) (Ne.symm hne)
      exact le_trans (hx hpos) (le_abs_self _)
  have hcard := hTyp p hp0 hp1 n η T (fun x hx => by simpa [hT] using hx)
  have hθT : θ * T.card ≤ c ^ n := by
    have hexp : -((m : ℝ) * (ent q - η)) + n * (ent p + η)
        ≤ -((r * ent q - ent p) / 2) * n := by
      have h1 : r * n * (ent q - η) ≤ m * (ent q - η) :=
        mul_le_mul_of_nonneg_right hm (by linarith)
      have h2 : (n : ℝ) * (η * (1 + r)) ≤ n * ((r * ent q - ent p) / 2) :=
        mul_le_mul_of_nonneg_left hη2 hnpos.le
      nlinarith
    calc θ * T.card ≤ θ * (2 : ℝ) ^ (n * (ent p + η)) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = (2 : ℝ) ^ (-((m : ℝ) * (ent q - η)) + n * (ent p + η)) := by
          rw [hθ, Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ) ^ (-((r * ent q - ent p) / 2) * n) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = c ^ n := Real.rpow_mul_natCast (by norm_num) _ _
  have hTc' : Vp / (η ^ 2 * n) = Vp / η ^ 2 / n := by rw [div_div]
  linarith

/-! ### Converse assembly -/

def ChildConverse : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 → ∑ z, ‖φ z‖ ^ 2 = 1 → 0 < entEntropy φ →
    ∀ E : ℝ, IsAchievableRate ψ φ E → E ≤ entEntropy ψ / entEntropy φ

lemma tp_unit (hIid : IidP) {a b : Type} [Fintype a] [Fintype b] (ψ : a × b → ℂ)
    (hψ : ∑ z, ‖ψ z‖ ^ 2 = 1) (n : ℕ) : ∑ z, ‖tensorPowVec ψ n z‖ ^ 2 = 1 := by
  have h := hIid (fun z => ‖ψ z‖ ^ 2) hψ n
  rw [← h]
  let e : (Fin n → a) × (Fin n → b) ≃ (Fin n → a × b) :=
    ⟨fun z t => (z.1 t, z.2 t), fun f => (fun t => (f t).1, fun t => (f t).2),
      fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ (fun z => by
    simp only [tensorPowVec, norm_prod, Finset.prod_pow, e, Equiv.coe_fn_mk])

set_option maxHeartbeats 1000000 in
theorem conv (hK1 : K1_LOCCKraus) (hK2a : K2a_traceNorm_ge) (hK3 : K3_Schmidt) (hK4 : K4P)
    (hK6 : K6P) (hTyp : TypP) (hTail : TailP) (hProb : ProbP) (hIid : IidP) :
    ChildConverse := by
  intro a b _ _ _ _ ψ φ hψ hφ hHφ E hE
  by_contra hlt
  push_neg at hlt
  obtain ⟨e, w, p, he, hw, hp0, hp1, hd, hentψ⟩ := hK3 ψ hψ
  obtain ⟨e', w', q, he', hw', hq0, hq1, hd', hentφ⟩ := hK3 φ hφ
  have hHp : entEntropy ψ = ent p := hentψ
  have hHq : entEntropy φ = ent q := hentφ
  set r := (entEntropy ψ / entEntropy φ + E) / 2 with hr
  have hrE : r < E := by linarith
  have hr' : ent p < r * ent q := by
    rw [← hHp, ← hHq]
    have : entEntropy ψ / entEntropy φ < r := by linarith
    rwa [div_lt_iff₀ hHφ] at this
  obtain ⟨N, hN⟩ := conv_core hTyp hTail hProb p q hp0 hp1 hq0 hq1 (by rw [← hHq]; exact hHφ) r hr'
  obtain ⟨N', hN'⟩ := hE (1 / 2) (by norm_num) (by norm_num) (E - r) (by linarith)
  set n := max (max N N') 1 with hn
  obtain ⟨m, hm, Λ, hΛ, hdist⟩ := hN' n (le_trans (le_max_right N N') (le_max_left _ _))
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n from lt_of_lt_of_le one_pos (le_max_right _ _))
  have hrm : r * n ≤ m := by
    have : r ≤ (m : ℝ) / n := by linarith
    rwa [le_div_iff₀ hnpos] at this
  obtain ⟨T, θ, hθ, hsmall⟩ := hN n m (le_trans (le_max_left N N') (le_max_left _ _)) hrm
  obtain ⟨J, iJ, A, B, hc, hΛeq⟩ := hK1 Λ hΛ
  obtain ⟨hE1, hW1, hdec1⟩ := hK6 ψ e w p he hw hd n
  obtain ⟨hE2, hW2, hdec2⟩ := hK6 φ e' w' q he' hw' hd' m
  have hΨ : tensorPowVec ψ n = ∑ x : Fin n → a,
      pv (fun x i => ∏ t, e (x t) (i t)) (fun x k => ∏ t, w (x t) (k t)) x := by
    funext z
    obtain ⟨i, k⟩ := z
    rw [hdec1, Finset.sum_apply]
    rfl
  have hΦ : tensorPowVec φ m = ∑ y : Fin m → a,
      pv (fun y i => ∏ t, e' (y t) (i t)) (fun y k => ∏ t, w' (y t) (k t)) y := by
    funext z
    obtain ⟨i, k⟩ := z
    rw [hdec2, Finset.sum_apply]
    rfl
  have hF := fid_half hK2a (tensorPowVec ψ n) (tensorPowVec φ m) (tp_unit hIid ψ hψ n)
    (tp_unit hIid φ hφ m) (fun j => A j ⊗ₖ B j) hc (1 / 2) (by rw [hΛeq] at hdist; exact hdist)
  rw [hΨ, hΦ] at hF
  have h4 := hK4 (fun (x : Fin n → a) (i : Fin n → a) => ∏ t, e (x t) (i t))
    (fun (x : Fin n → a) (k : Fin n → b) => ∏ t, w (x t) (k t))
    (fun (x : Fin n → a) => ∏ t, p (x t)) hE1 hW1
    (fun (x : Fin n → a) => Finset.prod_nonneg fun t _ => hp0 (x t))
    (hIid p hp1 n) (fun (y : Fin m → a) (i : Fin m → a) => ∏ t, e' (y t) (i t))
    (fun (y : Fin m → a) (k : Fin m → b) => ∏ t, w' (y t) (k t))
    (fun (y : Fin m → a) => ∏ t, q (y t)) hE2 hW2
    (fun (y : Fin m → a) => Finset.prod_nonneg fun t _ => hq0 (y t))
    (hIid q hq1 m) A B hc T θ hθ
  exact absurd (lt_of_le_of_lt (le_trans hF h4) hsmall) (by norm_num)

end EntManip2baC

end F5

namespace EntManip2ba

theorem childConverse : ChildConverse :=
  EntManip2baC.conv k1 k2a k3 k4 k6 typ_card tail_le prob_eq iid_one

end EntManip2ba


set_option autoImplicit false

open scoped Matrix Kronecker ComplexOrder

namespace EntManip2baK7

open Matrix Finset WildeQIT

noncomputable def N2 {n : Type} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma N2_nonneg {n : Type} [Fintype n] (v : n → ℂ) : 0 ≤ N2 v :=
  Finset.sum_nonneg fun i _ => by positivity

lemma star_mul_self_c (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma nc_eq {n : Type} [Fintype n] (v : n → ℂ) : star v ⬝ᵥ v = (N2 v : ℂ) := by
  rw [N2, Complex.ofReal_sum]
  simp only [dotProduct, Pi.star_apply, star_mul_self_c]

lemma cs {n : Type} [Fintype n] (v z : n → ℂ) : ‖star v ⬝ᵥ z‖ ^ 2 ≤ N2 v * N2 z := by
  have h1 : ‖star v ⬝ᵥ z‖ ≤ ∑ i, ‖v i‖ * ‖z i‖ := by
    simp only [dotProduct, Pi.star_apply]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun i => ‖z i‖)
  calc ‖star v ⬝ᵥ z‖ ^ 2 ≤ (∑ i, ‖v i‖ * ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- K2b, verbatim from scratch/probe/2ba22dc4_k2.lean (`EntManip2ba.k2b`). -/
def K2bP : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ), M.IsHermitian →
    ∃ S : Matrix n n ℂ, S.IsHermitian ∧ (1 - Sᴴ * S).PosSemidef ∧
      traceNorm M = (Matrix.trace (S * M)).re

lemma trS {ι : Type} [Fintype ι] (S : Matrix ι ι ℂ) (u v : ι → ℂ) :
    trace (S * vecMulVec u (star v)) = star v ⬝ᵥ (S *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma contr {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ)
    (hS : (1 - Sᴴ * S).PosSemidef) (u v : ι → ℂ) :
    ‖star v ⬝ᵥ (S *ᵥ u)‖ ≤ Real.sqrt (N2 u) * Real.sqrt (N2 v) := by
  have h0 : 0 ≤ star u ⬝ᵥ ((1 - Sᴴ * S) *ᵥ u) := by
    first
    | exact hS.dotProduct_mulVec_nonneg u
    | exact hS.2 u
  have h1 : star u ⬝ᵥ ((1 - Sᴴ * S) *ᵥ u) = ((N2 u - N2 (S *ᵥ u) : ℝ) : ℂ) := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec,
      ← star_mulVec, nc_eq, nc_eq]
    push_cast
    ring
  rw [h1] at h0
  have h2 : N2 (S *ᵥ u) ≤ N2 u := by
    have := Complex.zero_le_real.mp h0
    linarith
  have h3 : ‖star v ⬝ᵥ (S *ᵥ u)‖ ^ 2 ≤ N2 u * N2 v := by
    calc _ ≤ N2 v * N2 (S *ᵥ u) := cs v _
      _ ≤ N2 v * N2 u := mul_le_mul_of_nonneg_left h2 (N2_nonneg v)
      _ = N2 u * N2 v := mul_comm _ _
  rw [← Real.sqrt_mul (N2_nonneg u)]
  exact Real.le_sqrt_of_sq_le h3

lemma herm_ps {ι : Type} [Fintype ι] (u : ι → ℂ) :
    (ObliviousRSP.pureState u)ᴴ = ObliviousRSP.pureState u := by
  ext i k
  simp [ObliviousRSP.pureState, vecMulVec_apply, conjTranspose_apply, mul_comm]

/-- K7a: trace-distance bound for the round's output `c χχ† + ∑ z z†` against `φφ†`. -/
theorem k7a (hK2b : K2bP) {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K]
    (χ φ : ι → ℂ) (z : K → ι → ℂ) (c : ℝ) (hc0 : 0 ≤ c) (hχ : N2 χ = 1) (hφ : N2 φ = 1)
    (hsum : c + ∑ k, N2 (z k) = 1) :
    (1 / 2 : ℝ) * traceNorm ((c : ℂ) • ObliviousRSP.pureState χ
        + ∑ k, ObliviousRSP.pureState (z k) - ObliviousRSP.pureState φ)
      ≤ Real.sqrt (N2 (χ - φ)) + (1 - c) := by
  set M := (c : ℂ) • ObliviousRSP.pureState χ
        + ∑ k, ObliviousRSP.pureState (z k) - ObliviousRSP.pureState φ with hMdef
  have hM : M.IsHermitian := by
    unfold IsHermitian
    rw [hMdef, conjTranspose_sub, conjTranspose_add, conjTranspose_smul, conjTranspose_sum]
    simp only [herm_ps, Complex.star_def, Complex.conj_ofReal]
  obtain ⟨S, -, hS, hT⟩ := hK2b M hM
  set g : (ι → ℂ) → (ι → ℂ) → ℂ := fun u v => star v ⬝ᵥ (S *ᵥ u) with hg
  have htr : trace (S * M) = (c : ℂ) * g χ χ + ∑ k, g (z k) (z k) - g φ φ := by
    rw [hMdef, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sum, trace_sub,
      trace_add, trace_smul, trace_sum]
    simp only [ObliviousRSP.pureState, trS, hg, smul_eq_mul]
  have hb : ∀ u v, ‖g u v‖ ≤ Real.sqrt (N2 u) * Real.sqrt (N2 v) := fun u v => contr S hS u v
  have hgsub1 : ∀ u u' v, g (u - u') v = g u v - g u' v := by
    intro u u' v
    simp only [hg, mulVec_sub, dotProduct_sub]
  have hgsub2 : ∀ u v v', g u (v - v') = g u v - g u v' := by
    intro u v v'
    simp only [hg, star_sub, sub_dotProduct]
  have hAB : g χ χ - g φ φ = g (χ - φ) χ + g φ (χ - φ) := by
    rw [hgsub1, hgsub2]; ring
  set d := Real.sqrt (N2 (χ - φ))
  have hA : ‖g χ χ‖ ≤ 1 := by
    have := hb χ χ; rwa [hχ, Real.sqrt_one, mul_one] at this
  have hd1 : ‖g (χ - φ) χ‖ ≤ d := by
    have := hb (χ - φ) χ; rwa [hχ, Real.sqrt_one, mul_one] at this
  have hd2 : ‖g φ (χ - φ)‖ ≤ d := by
    have := hb φ (χ - φ); rwa [hφ, Real.sqrt_one, one_mul] at this
  have hz : ∀ k, (g (z k) (z k)).re ≤ N2 (z k) := by
    intro k
    have h := hb (z k) (z k)
    rw [Real.mul_self_sqrt (N2_nonneg _)] at h
    exact (Complex.re_le_norm _).trans h
  have hc1 : c ≤ 1 := by
    have := Finset.sum_nonneg fun k (_ : k ∈ (univ : Finset K)) => N2_nonneg (z k)
    linarith
  have hmain : ‖(c : ℂ) * g χ χ - g φ φ‖ ≤ (1 - c) + 2 * d := by
    have he : (c : ℂ) * g χ χ - g φ φ = ((c - 1 : ℝ) : ℂ) * g χ χ + (g χ χ - g φ φ) := by
      push_cast; ring
    rw [he, hAB]
    calc _ ≤ ‖((c - 1 : ℝ) : ℂ) * g χ χ‖ + (‖g (χ - φ) χ‖ + ‖g φ (χ - φ)‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ (1 - c) * 1 + (d + d) := by
          refine add_le_add ?_ (add_le_add hd1 hd2)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (show c - 1 ≤ 0 by linarith)]
          have := mul_le_mul_of_nonneg_left hA (show (0:ℝ) ≤ -(c - 1) by linarith)
          linarith
      _ = _ := by ring
  have hre : (trace (S * M)).re ≤ (1 - c) + 2 * d + (1 - c) := by
    rw [htr]
    have e1 : ((c : ℂ) * g χ χ + ∑ k, g (z k) (z k) - g φ φ)
        = ((c : ℂ) * g χ χ - g φ φ) + ∑ k, g (z k) (z k) := by ring
    rw [e1, Complex.add_re, Complex.re_sum]
    have h1 := (Complex.re_le_norm ((c : ℂ) * g χ χ - g φ φ)).trans hmain
    have h2 : ∑ k, (g (z k) (z k)).re ≤ ∑ k, N2 (z k) := Finset.sum_le_sum fun k _ => hz k
    linarith
  rw [hT]
  linarith

/-- K7c: Bob's partial isometry `U` (with `U†U` a projection) completed to a channel. -/
noncomputable def complete {b b' : Type} [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b']
    (U : Matrix b' b ℂ) (hU : (Uᴴ * U) * (Uᴴ * U) = Uᴴ * U) (o : b') : QChannel b b' where
  ι := Option b
  K := fun l => match l with
    | none => U
    | some k => Matrix.of fun i j => if i = o then ((1 : Matrix b b ℂ) - Uᴴ * U) k j else 0
  complete := by
    set P := Uᴴ * U with hP
    have hPh : Pᴴ = P := by rw [hP, conjTranspose_mul, conjTranspose_conjTranspose]
    have hrest : ∑ k : b, (Matrix.of fun i j => if i = o then (1 - P) k j else (0 : ℂ))ᴴ
        * (Matrix.of fun i j => if i = o then (1 - P) k j else (0 : ℂ)) = (1 - P)ᴴ * (1 - P) := by
      ext j j'
      simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single o (fun i _ hi => by simp [hi]) (by simp)]
      simp
    rw [Fintype.sum_option]
    simp only
    rw [hrest, conjTranspose_sub, conjTranspose_one, hPh, sub_mul, mul_sub, mul_sub, one_mul,
      mul_one, one_mul, hU]
    abel

section K7b
variable {α β Y : Type} [Fintype α] [Fintype β] [Fintype Y]

/-- Schmidt-form vector with coefficients `d`. -/
noncomputable def sv (e : Y → α → ℂ) (w : Y → β → ℂ) (d : Y → ℂ) : α × β → ℂ :=
  fun z => ∑ y, d y * e y z.1 * w y z.2

lemma ip_key [DecidableEq Y] (e : Y → α → ℂ) (w : Y → β → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0) (y y' : Y) :
    ∑ i, ∑ k, star (e y i * w y k) * (e y' i * w y' k) = if y = y' then (q y : ℂ) else 0 := by
  have h1 := he y y'
  have h2 := hw y y'
  simp only [dotProduct, Pi.star_apply] at h1 h2
  calc _ = (∑ i, star (e y i) * e y' i) * ∑ k, star (w y k) * w y' k := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [star_mul']; ring
    _ = _ := by rw [h1, h2]; split_ifs <;> simp

lemma sv_ip [DecidableEq Y] (e : Y → α → ℂ) (w : Y → β → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0) (d d' : Y → ℂ) :
    star (sv e w d) ⬝ᵥ sv e w d' = ∑ y, star (d y) * d' y * (q y : ℂ) := by
  set G : Y → Y → α → β → ℂ := fun y y' i k =>
    star (d y) * d' y' * (star (e y i * w y k) * (e y' i * w y' k)) with hG
  have h0 : star (sv e w d) ⬝ᵥ sv e w d' = ∑ i, ∑ k, ∑ y', ∑ y, G y y' i k := by
    simp only [dotProduct, sv, Pi.star_apply, star_sum, Fintype.sum_prod_type, Finset.sum_mul,
      Finset.mul_sum, hG]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    simp only [star_mul']; ring
  rw [h0, show ∑ i, ∑ k, ∑ y', ∑ y, G y y' i k = ∑ i, ∑ k, ∑ y, ∑ y', G y y' i k from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  calc ∑ i, ∑ k, ∑ y, ∑ y', G y y' i k = ∑ i, ∑ y, ∑ y', ∑ k, G y y' i k :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y, ∑ i, ∑ y', ∑ k, G y y' i k := Finset.sum_comm
    _ = ∑ y, ∑ y', ∑ i, ∑ k, G y y' i k := Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y, ∑ y', star (d y) * d' y' * (if y = y' then (q y : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        rw [← ip_key e w q he hw y y', Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp [mul_ite, Finset.sum_ite_eq]

lemma sv_N2 [DecidableEq Y] (e : Y → α → ℂ) (w : Y → β → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0) (d : Y → ℂ) :
    N2 (sv e w d) = ∑ y, ‖d y‖ ^ 2 * q y := by
  have h := sv_ip e w q he hw d d
  rw [nc_eq] at h
  apply Complex.ofReal_injective
  rw [h, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [star_mul_self_c]
  push_cast; ring

lemma sv_sub (e : Y → α → ℂ) (w : Y → β → ℂ) (d d' : Y → ℂ) :
    sv e w d - sv e w d' = sv e w (d - d') := by
  funext z
  simp only [sv, Pi.sub_apply, ← Finset.sum_sub_distrib, sub_mul]

/-- K7b: the normalized restriction `χ` of a Schmidt-form unit vector to `S` is a unit vector
with `‖χ - φ‖² ≤ 2 (1 - Q(S))`. -/
theorem k7b [DecidableEq Y] (e : Y → α → ℂ) (w : Y → β → ℂ) (q : Y → ℝ)
    (he : ∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0)
    (hw : ∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0)
    (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1) (S : Finset Y) (hc : 0 < ∑ y ∈ S, q y) :
    N2 (sv e w (fun y => if y ∈ S then ((Real.sqrt (∑ y ∈ S, q y) : ℂ))⁻¹ else 0)) = 1 ∧
    N2 (sv e w (fun y => if y ∈ S then ((Real.sqrt (∑ y ∈ S, q y) : ℂ))⁻¹ else 0) - sv e w 1)
      ≤ 2 * (1 - ∑ y ∈ S, q y) := by
  set c := ∑ y ∈ S, q y with hcdef
  set s := Real.sqrt c with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hc
  have hsq : s ^ 2 = c := Real.sq_sqrt hc.le
  have hc1 : c ≤ 1 := by
    rw [← hq1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun y _ _ => hq0 y
  have hs1 : s ≤ 1 := by nlinarith
  have hcs : ((s : ℂ))⁻¹ = ((s⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  constructor
  · rw [sv_N2 e w q he hw]
    have ht : ∀ y, ‖(if y ∈ S then ((s : ℂ))⁻¹ else 0)‖ ^ 2 * q y
        = if y ∈ S then (s⁻¹) ^ 2 * q y else 0 := by
      intro y
      split_ifs
      · rw [hcs, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · simp
    simp only [ht, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
    rw [← hcdef, ← hsq]
    field_simp
  · rw [sv_sub, sv_N2 e w q he hw]
    have ht : ∀ y, ‖((fun y => if y ∈ S then ((s : ℂ))⁻¹ else 0) - 1) y‖ ^ 2 * q y
        = (if y ∈ S then ((s⁻¹ - 1) ^ 2 - 1) * q y else 0) + q y := by
      intro y
      simp only [Pi.sub_apply, Pi.one_apply]
      split_ifs
      · rw [hcs, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          sq_abs]
        ring
      · simp
    simp only [ht, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum,
      hq1]
    rw [← hcdef, ← hsq]
    have e1 : ((s⁻¹ - 1) ^ 2 - 1) * s ^ 2 = (1 - s) ^ 2 - s ^ 2 := by
      field_simp
    rw [e1]
    nlinarith

end K7b

/-- K7d: a Latin square on a finite set `C` (cyclic shift through `C ≃ Fin |C|`). -/
lemma latin {α : Type} [DecidableEq α] (C : Finset α) : ∃ σ : α → α → α,
    (∀ x0 ∈ C, Set.BijOn (fun i => σ i x0) C C) ∧ (∀ i ∈ C, Set.BijOn (fun x0 => σ i x0) C C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun i _ => i, by simp, by simp⟩
  haveI : NeZero C.card := ⟨Finset.card_ne_zero.mpr hne⟩
  let e : C ≃ Fin C.card := C.equivFin
  let s : C → C → C := fun i x0 => e.symm (e i + e x0)
  refine ⟨fun i x0 => if h : i ∈ C ∧ x0 ∈ C then (s ⟨i, h.1⟩ ⟨x0, h.2⟩ : α) else i, ?_, ?_⟩
  · intro x0 hx0
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun m hm => ?_⟩
    · dsimp only; rw [dif_pos (show i ∈ C ∧ x0 ∈ C from ⟨hi, hx0⟩)]; exact (s _ _).2
    · dsimp only at hij; rw [dif_pos (show i ∈ C ∧ x0 ∈ C from ⟨hi, hx0⟩), dif_pos (show j ∈ C ∧ x0 ∈ C from ⟨hj, hx0⟩)] at hij
      have := Subtype.ext hij
      simp only [s, e.symm.injective.eq_iff, add_left_inj, e.injective.eq_iff,
        Subtype.mk.injEq] at this
      exact this
    · refine ⟨(e.symm (e ⟨m, hm⟩ - e ⟨x0, hx0⟩) : α), (e.symm _).2, ?_⟩
      dsimp only; rw [dif_pos (show _ ∈ C ∧ x0 ∈ C from ⟨(e.symm (e ⟨m, hm⟩ - e ⟨x0, hx0⟩)).2, hx0⟩)]
      simp only [s,
        Subtype.coe_eta, Equiv.apply_symm_apply, sub_add_cancel, Equiv.symm_apply_apply]
  · intro i hi
    refine ⟨fun x0 hx0 => ?_, fun x0 hx0 j hj hij => ?_, fun m hm => ?_⟩
    · dsimp only; rw [dif_pos (show i ∈ C ∧ x0 ∈ C from ⟨hi, hx0⟩)]; exact (s _ _).2
    · dsimp only at hij; rw [dif_pos (show i ∈ C ∧ x0 ∈ C from ⟨hi, hx0⟩), dif_pos (show i ∈ C ∧ j ∈ C from ⟨hi, hj⟩)] at hij
      have := Subtype.ext hij
      simp only [s, e.symm.injective.eq_iff, add_right_inj, e.injective.eq_iff,
        Subtype.mk.injEq] at this
      exact this
    · refine ⟨(e.symm (e ⟨m, hm⟩ - e ⟨i, hi⟩) : α), (e.symm _).2, ?_⟩
      dsimp only; rw [dif_pos (show i ∈ C ∧ _ ∈ C from ⟨hi, (e.symm (e ⟨m, hm⟩ - e ⟨i, hi⟩)).2⟩)]
      simp only [s,
        Subtype.coe_eta, Equiv.apply_symm_apply, add_sub_cancel, Equiv.symm_apply_apply]

section Core
variable {α β α' β' T : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype T] [DecidableEq T]

lemma sum_mulVec' {ι m n : Type} [Fintype n] (s : Finset ι) (M : ι → Matrix m n ℂ) (v : n → ℂ) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

lemma smul_mulVec' {m n : Type} [Fintype n] (c : ℂ) (M : Matrix m n ℂ) (v : n → ℂ) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp only [mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma vmv_mulVec {m n : Type} [Fintype n] (u : m → ℂ) (v w : n → ℂ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma vmv_mul {l m n : Type} [Fintype m] (a : l → ℂ) (b c : m → ℂ) (d : n → ℂ) :
    vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma vmv_ct {m n : Type} (a : m → ℂ) (b : n → ℂ) :
    (vecMulVec a (star b))ᴴ = vecMulVec b (star a) := by
  ext i j
  simp [vecMulVec_apply, conjTranspose_apply, mul_comm]

lemma kron_mulVec_sum {X : Type} [Fintype X] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ)
    (u : X → α → ℂ) (v : X → β → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun z : α × β => ∑ x, u x z.1 * v x z.2)
      = fun z => ∑ x, (A *ᵥ u x) z.1 * (B *ᵥ v x) z.2 := by
  funext z
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Finset.mul_sum,
    Finset.sum_mul]
  calc _ = ∑ i, ∑ x, ∑ k, A z.1 i * B z.2 k * (u x i * v x k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ k, A z.1 i * B z.2 k * (u x i * v x k) := Finset.sum_comm
    _ = ∑ x, ∑ k, ∑ i, A z.1 i * B z.2 k * (u x i * v x k) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun i _ => by ring

/-- Alice's Kraus operator of one good outcome: `∑_t √μ_t |f_t⟩⟨E_{τ t}|`. -/
noncomputable def Fop (E : α → α → ℂ) (f : T → α' → ℂ) (μ : T → ℝ) (τ : T → α) :
    Matrix α' α ℂ :=
  ∑ t, ((Real.sqrt (μ t) : ℂ)) • vecMulVec (f t) (star (E (τ t)))

/-- Bob's partial isometry: `∑_t p0^{-1/2} |g_t⟩⟨W_{τ t}|`. -/
noncomputable def Uop (W : α → β → ℂ) (g : T → β' → ℂ) (p0 : ℝ) (τ : T → α) : Matrix β' β ℂ :=
  ∑ t, ((Real.sqrt p0 : ℂ))⁻¹ • vecMulVec (g t) (star (W (τ t)))

lemma Fop_apply (E : α → α → ℂ) (f : T → α' → ℂ) (μ : T → ℝ) (τ : T → α)
    (hE : ∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0) (x : α) :
    Fop E f μ τ *ᵥ E x = ∑ t, (if τ t = x then (Real.sqrt (μ t) : ℂ) else 0) • f t := by
  simp only [Fop, sum_mulVec', smul_mulVec', vmv_mulVec, hE, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

lemma Uop_apply (W : α → β → ℂ) (g : T → β' → ℂ) (p0 : ℝ) (τ : T → α) (P : α → ℝ)
    (hW : ∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0) (x : α) :
    Uop W g p0 τ *ᵥ W x
      = ∑ t, (if τ t = x then ((Real.sqrt p0 : ℂ))⁻¹ * P (τ t) else 0) • g t := by
  simp only [Uop, sum_mulVec', smul_mulVec', vmv_mulVec, hW, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

lemma inj_sum {X : Type} [Fintype X] [DecidableEq X] (τ : T → X) (hτ : Function.Injective τ)
    (a b : T → ℂ) :
    ∑ x, (∑ t, if τ t = x then a t else 0) * (∑ t, if τ t = x then b t else 0)
      = ∑ t, a t * b t := by
  have hG : ∀ t0, (∑ t, if τ t = τ t0 then a t else 0) * (∑ t, if τ t = τ t0 then b t else 0)
      = a t0 * b t0 := by
    intro t0; simp [hτ.eq_iff]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image τ)) ?_,
    Finset.sum_image (fun x _ y _ h => hτ h)]
  · exact Finset.sum_congr rfl fun t _ => hG t
  · intro x _ hx
    have : ∀ t, τ t ≠ x := fun t ht => hx (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
    simp [this]

/-- Core (1): one good outcome maps `ψ = ∑_x E_x ⊗ W_x` to `√p0 · χ`, `χ = ∑_t √μ_t f_t ⊗ g_t`. -/
theorem core1 (E : α → α → ℂ) (W : α → β → ℂ) (P : α → ℝ) (f : T → α' → ℂ)
    (g : T → β' → ℂ) (μ : T → ℝ) (τ : T → α) (p0 : ℝ)
    (hE : ∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0)
    (hW : ∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0)
    (hτ : Function.Injective τ) (hP : ∀ t, P (τ t) = p0) (hp0 : 0 < p0) :
    (Fop E f μ τ ⊗ₖ Uop W g p0 τ) *ᵥ (fun z : α × β => ∑ x, E x z.1 * W x z.2)
      = fun z => (Real.sqrt p0 : ℂ) * ∑ t, (Real.sqrt (μ t) : ℂ) * f t z.1 * g t z.2 := by
  rw [kron_mulVec_sum]
  funext z
  simp only [Fop_apply E f μ τ hE, Uop_apply W g p0 τ P hW, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ite_mul, zero_mul]
  refine (inj_sum τ hτ _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hs : (Real.sqrt p0 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hp0).ne'
  have hsq : ((Real.sqrt p0 : ℂ)) ^ 2 = p0 := by exact_mod_cast Real.sq_sqrt hp0.le
  have h1 : ((Real.sqrt p0 : ℂ))⁻¹ * ((Real.sqrt p0 : ℂ)) ^ 2 = Real.sqrt p0 := by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  rw [hP t, ← hsq, h1]
  ring

lemma star_sqrt_mul (r : ℝ) (hr : 0 ≤ r) :
    star ((Real.sqrt r : ℂ)) * (Real.sqrt r : ℂ) = r := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]

/-- Core (4): `F†F = ∑_t μ_t |E_{τ t}⟩⟨E_{τ t}|`. -/
theorem core4 (E : α → α → ℂ) (f : T → α' → ℂ) (μ : T → ℝ) (τ : T → α)
    (hf : ∀ s t, star (f s) ⬝ᵥ f t = if s = t then 1 else 0) (hμ : ∀ t, 0 ≤ μ t) :
    (Fop E f μ τ)ᴴ * Fop E f μ τ = ∑ t, (μ t : ℂ) • vecMulVec (E (τ t)) (star (E (τ t))) := by
  simp only [Fop, conjTranspose_sum, conjTranspose_smul, vmv_ct, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, vmv_mul, hf, smul_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s (fun t _ hts => by simp [hts, Ne.symm hts]) (by simp)]
  simp only [if_true, mul_one, one_smul]
  rw [smul_smul, mul_comm, star_sqrt_mul (μ s) (hμ s)]

/-- `U†U = p0⁻¹ ∑_t |W_{τ t}⟩⟨W_{τ t}|`. -/
theorem coreUU (W : α → β → ℂ) (g : T → β' → ℂ) (p0 : ℝ) (τ : T → α) (hp0 : 0 < p0)
    (hg : ∀ s t, star (g s) ⬝ᵥ g t = if s = t then 1 else 0) :
    (Uop W g p0 τ)ᴴ * Uop W g p0 τ
      = ∑ t, ((p0 : ℂ))⁻¹ • vecMulVec (W (τ t)) (star (W (τ t))) := by
  simp only [Uop, conjTranspose_sum, conjTranspose_smul, vmv_ct, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, vmv_mul, hg, smul_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s (fun t _ hts => by simp [hts, Ne.symm hts]) (by simp)]
  simp only [if_true, mul_one, one_smul]
  rw [smul_smul, star_inv₀, ← mul_inv, mul_comm, star_sqrt_mul p0 hp0.le]

lemma UU_mulVec (W : α → β → ℂ) (g : T → β' → ℂ) (p0 : ℝ) (τ : T → α) (P : α → ℝ) (hp0 : 0 < p0)
    (hg : ∀ s t, star (g s) ⬝ᵥ g t = if s = t then 1 else 0)
    (hW : ∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0)
    (hτ : Function.Injective τ) (hP : ∀ t, P (τ t) = p0) (t0 : T) :
    ((Uop W g p0 τ)ᴴ * Uop W g p0 τ) *ᵥ W (τ t0) = W (τ t0) := by
  rw [coreUU W g p0 τ hp0 hg, sum_mulVec']
  simp only [smul_mulVec', vmv_mulVec, hW, hτ.eq_iff]
  rw [Finset.sum_eq_single t0 (fun t _ ht => by simp [ht]) (by simp)]
  simp only [if_true, smul_smul, hP]
  rw [inv_mul_cancel₀ (by exact_mod_cast hp0.ne'), one_smul]

lemma mul_vmv {l m n : Type} [Fintype m] (M : Matrix l m ℂ) (a : m → ℂ) (b : n → ℂ) :
    M * vecMulVec a b = vecMulVec (M *ᵥ a) b := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem coreUU_idem (W : α → β → ℂ) (g : T → β' → ℂ) (p0 : ℝ) (τ : T → α) (P : α → ℝ)
    (hp0 : 0 < p0) (hg : ∀ s t, star (g s) ⬝ᵥ g t = if s = t then 1 else 0)
    (hW : ∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0)
    (hτ : Function.Injective τ) (hP : ∀ t, P (τ t) = p0) :
    ((Uop W g p0 τ)ᴴ * Uop W g p0 τ) * ((Uop W g p0 τ)ᴴ * Uop W g p0 τ)
      = (Uop W g p0 τ)ᴴ * Uop W g p0 τ := by
  have hv := UU_mulVec W g p0 τ P hp0 hg hW hτ hP
  have hMe := coreUU W g p0 τ hp0 hg
  conv_lhs => arg 2; rw [hMe]
  rw [Matrix.mul_sum]
  simp only [Matrix.mul_smul, mul_vmv, hv]
  exact hMe.symm

end Core

section Round
open WildeQIT.EntManip
variable {α β α' β' T : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype T] [DecidableEq T]

lemma sum_kron7 {ι l m n p : Type} (s : Finset ι) (A : ι → Matrix l m ℂ) (B : Matrix n p ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

lemma kron_sum7 {ι l m n p : Type} (s : Finset ι) (A : Matrix l m ℂ) (B : ι → Matrix n p ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

lemma kraus_N2' {m n J : Type} [Fintype m] [Fintype n] [Fintype J] [DecidableEq n]
    (K : J → Matrix m n ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (v : n → ℂ) :
    ∑ j, N2 (K j *ᵥ v) = N2 v := by
  have h : ∀ j, star (K j *ᵥ v) ⬝ᵥ (K j *ᵥ v) = star v ⬝ᵥ (((K j)ᴴ * K j) *ᵥ v) := by
    intro j
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
  have hc : ((∑ j, N2 (K j *ᵥ v) : ℝ) : ℂ) = (N2 v : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [← nc_eq, h]
    rw [← dotProduct_sum, ← sum_mulVec, hK, one_mulVec]
  exact_mod_cast hc

lemma onb_complete (E : α → α → ℂ) (hE : ∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0) :
    ∑ x, vecMulVec (E x) (star (E x)) = 1 := by
  set V : Matrix α α ℂ := Matrix.of fun i x => E x i with hV
  have h1 : Vᴴ * V = 1 := by
    ext x y
    have := hE x y
    simp only [dotProduct, Pi.star_apply] at this
    simp only [hV, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    exact this
  have h2 : V * Vᴴ = 1 := mul_eq_one_comm.mp h1
  rw [← h2]
  ext i j
  simp only [hV, Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, conjTranspose_apply,
    Matrix.of_apply, Pi.star_apply]

lemma vmv_mul_ct {m n k : Type} [Fintype n] (u : m → ℂ) (v : n → ℂ) (M : Matrix k n ℂ) :
    vecMulVec u (star v) * Mᴴ = vecMulVec u (star (M *ᵥ v)) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, conjTranspose_apply, mulVec, dotProduct,
    Pi.star_apply, star_sum, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma ps_conj {m n : Type} [Fintype n] (M : Matrix m n ℂ) (v : n → ℂ) :
    M * ObliviousRSP.pureState v * Mᴴ = ObliviousRSP.pureState (M *ᵥ v) := by
  simp only [ObliviousRSP.pureState]
  rw [mul_vmv, vmv_mul_ct]

lemma ps_zero {n : Type} : ObliviousRSP.pureState (0 : n → ℂ) = 0 := by
  ext i j; simp [ObliviousRSP.pureState, vecMulVec_apply]

lemma ps_smul_sqrt {n : Type} (r : ℝ) (hr : 0 ≤ r) (v : n → ℂ) :
    ObliviousRSP.pureState ((Real.sqrt r : ℂ) • v) = (r : ℂ) • ObliviousRSP.pureState v := by
  have hs : star ((Real.sqrt r : ℂ)) = (Real.sqrt r : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hsq : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = r := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  ext i j
  simp only [ObliviousRSP.pureState, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    star_mul', Matrix.smul_apply, hs]
  linear_combination (v i * star (v j)) * hsq

lemma N2_smul_sqrt {n : Type} [Fintype n] (r : ℝ) (hr : 0 ≤ r) (v : n → ℂ) :
    N2 ((Real.sqrt r : ℂ) • v) = r * N2 v := by
  simp only [N2, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg r), mul_pow, Real.sq_sqrt hr, Finset.mul_sum]

lemma N2_zero {n : Type} [Fintype n] : N2 (0 : n → ℂ) = 0 := by simp [N2]

lemma split_sum {X L V M : Type} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L] [Zero V]
    [AddCommMonoid M] (h : V → M) (h0 : h 0 = 0) (Gd : Finset X) (l0 : L) (v : X → L → V) :
    ∑ x, ∑ l, h (v x l) = ∑ x ∈ Gd, h (v x l0)
      + ∑ j : X × L, h (if j.1 ∈ Gd ∧ j.2 = l0 then 0 else v j.1 j.2) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_sum_compl Gd (fun x => ∑ l, h (v x l)),
    ← Finset.sum_add_sum_compl Gd (fun x => ∑ l, h (if x ∈ Gd ∧ l = l0 then 0 else v x l))]
  have e1 : ∀ x ∈ Gd, ∑ l, h (v x l)
      = h (v x l0) + ∑ l, h (if x ∈ Gd ∧ l = l0 then 0 else v x l) := by
    intro x hx
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l0),
      ← Finset.add_sum_erase _ (fun l => h (if x ∈ Gd ∧ l = l0 then 0 else v x l)) (Finset.mem_univ l0)]
    simp only [hx, true_and, if_true, h0, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [if_neg (Finset.ne_of_mem_erase hl)]
  have e2 : ∀ x ∈ Gdᶜ, ∑ l, h (if x ∈ Gd ∧ l = l0 then 0 else v x l) = ∑ l, h (v x l) := by
    intro x hx
    have hx' : x ∉ Gd := Finset.mem_compl.mp hx
    simp only [hx', false_and, if_false]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib]
  abel

/-- Alice's Kraus operator for outcome `x`. -/
noncomputable def Fx (E : α → α → ℂ) (f : T → α' → ℂ) (μ : T → ℝ) (Gd : Finset α)
    (τ : α → T → α) (a0 : α') (x : α) : Matrix α' α ℂ :=
  if x ∈ Gd then Fop E f μ (τ x) else vecMulVec (Pi.single a0 1) (star (E x))

/-- Bob's partial isometry for outcome `x`. -/
noncomputable def Ux (W : α → β → ℂ) (g : T → β' → ℂ) (P : α → ℝ) (Gd : Finset α)
    (τ : α → T → α) (x : α) : Matrix β' β ℂ :=
  if x ∈ Gd then Uop W g (P x) (τ x) else 0

theorem Fx_complete (E : α → α → ℂ) (f : T → α' → ℂ) (μ : T → ℝ) (Gd : Finset α)
    (τ : α → T → α) (a0 : α')
    (hE : ∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0)
    (hf : ∀ s t, star (f s) ⬝ᵥ f t = if s = t then 1 else 0)
    (hμ0 : ∀ t, 0 ≤ μ t) (hμ1 : ∑ t, μ t = 1)
    (hτG : ∀ x ∈ Gd, ∀ t, τ x t ∈ Gd)
    (hcnt : ∀ i ∈ Gd, ∀ t, (Gd.filter fun x => τ x t = i).card = 1) :
    ∑ x, (Fx E f μ Gd τ a0 x)ᴴ * Fx E f μ Gd τ a0 x = 1 := by
  have hgood : ∀ x ∈ Gd, (Fx E f μ Gd τ a0 x)ᴴ * Fx E f μ Gd τ a0 x
      = ∑ t, (μ t : ℂ) • vecMulVec (E (τ x t)) (star (E (τ x t))) := fun x hx => by
    simp only [Fx, if_pos hx]; exact core4 E f μ (τ x) hf hμ0
  have hbad : ∀ x ∈ Gdᶜ, (Fx E f μ Gd τ a0 x)ᴴ * Fx E f μ Gd τ a0 x
      = vecMulVec (E x) (star (E x)) := fun x hx => by
    simp only [Fx, if_neg (Finset.mem_compl.mp hx)]
    rw [vmv_ct, vmv_mul]
    simp [dotProduct, Pi.single_apply]
  have hfib : ∀ t, ∑ x ∈ Gd, vecMulVec (E (τ x t)) (star (E (τ x t)))
      = ∑ i ∈ Gd, vecMulVec (E i) (star (E i)) := by
    intro t
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => τ x t) (fun x hx => hτG x hx t)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
      hcnt i hi t, one_smul]
  rw [← Finset.sum_add_sum_compl Gd, Finset.sum_congr rfl hgood, Finset.sum_congr rfl hbad,
    Finset.sum_comm]
  simp only [← Finset.smul_sum, hfib, ← Finset.sum_smul]
  rw [← Complex.ofReal_sum, hμ1, Complex.ofReal_one, one_smul, Finset.sum_add_sum_compl,
    onb_complete E hE]

/-- K7 round: one one-way A→B LOCC round converting the Schmidt-form `ψ = ∑ E_x ⊗ W_x`
into `χ = ∑_t √μ_t f_t ⊗ g_t` on the good outcomes. -/
theorem k7round (hK2b : K2bP) (E : α → α → ℂ) (W : α → β → ℂ) (P : α → ℝ)
    (hE : ∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0)
    (hW : ∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (f : T → α' → ℂ) (g : T → β' → ℂ) (μ : T → ℝ)
    (hf : ∀ s t, star (f s) ⬝ᵥ f t = if s = t then 1 else 0)
    (hg : ∀ s t, star (g s) ⬝ᵥ g t = if s = t then 1 else 0)
    (hμ0 : ∀ t, 0 ≤ μ t) (hμ1 : ∑ t, μ t = 1)
    (Gd : Finset α) (τ : α → T → α)
    (hGP : ∀ x ∈ Gd, 0 < P x) (hτinj : ∀ x ∈ Gd, Function.Injective (τ x))
    (hτP : ∀ x ∈ Gd, ∀ t, P (τ x t) = P x) (hτG : ∀ x ∈ Gd, ∀ t, τ x t ∈ Gd)
    (hcnt : ∀ i ∈ Gd, ∀ t, (Gd.filter fun x => τ x t = i).card = 1)
    (a0 : α') (o : β') (φ : α' × β' → ℂ) (hφ : N2 φ = 1) :
    ∃ Λ : Matrix (α × β) (α × β) ℂ → Matrix (α' × β') (α' × β') ℂ,
      IsOneWayLOCCAB Λ ∧
      (1 / 2 : ℝ) * traceNorm (Λ (ObliviousRSP.pureState (sv E W 1)) - ObliviousRSP.pureState φ)
        ≤ Real.sqrt (N2 (sv f g (fun t => (Real.sqrt (μ t) : ℂ)) - φ)) + ∑ x ∈ Gdᶜ, P x := by
  set χ := sv f g (fun t => (Real.sqrt (μ t) : ℂ)) with hχdef
  have hU : ∀ x, (Ux W g P Gd τ x)ᴴ * Ux W g P Gd τ x * ((Ux W g P Gd τ x)ᴴ * Ux W g P Gd τ x)
      = (Ux W g P Gd τ x)ᴴ * Ux W g P Gd τ x := by
    intro x
    by_cases hx : x ∈ Gd
    · simp only [Ux, if_pos hx]
      exact coreUU_idem W g (P x) (τ x) P (hGP x hx) hg hW (hτinj x hx) (hτP x hx)
    · simp [Ux, if_neg hx]
  let G : α → QChannel β β' := fun x => complete (Ux W g P Gd τ x) (hU x) o
  let F : α → Unit → Matrix α' α ℂ := fun x _ => Fx E f μ Gd τ a0 x
  have hFc : ∑ x, ∑ k, (F x k)ᴴ * F x k = 1 := by
    simp only [F, Fintype.sum_unique]
    exact Fx_complete E f μ Gd τ a0 hE hf hμ0 hμ1 hτG hcnt
  let Λ : Matrix (α × β) (α × β) ℂ → Matrix (α' × β') (α' × β') ℂ := fun ρ =>
    ∑ x, ∑ k, ∑ l, (F x k ⊗ₖ (G x).K l) * ρ * (F x k ⊗ₖ (G x).K l)ᴴ
  refine ⟨Λ, ⟨α, inferInstance, Unit, inferInstance, F, G, hFc, fun ρ => rfl⟩, ?_⟩
  set v : α → Option β → (α' × β' → ℂ) := fun x l =>
    (Fx E f μ Gd τ a0 x ⊗ₖ (G x).K l) *ᵥ sv E W 1 with hvdef
  have hψ : sv E W 1 = fun z : α × β => ∑ x, E x z.1 * W x z.2 := by
    funext z; simp [sv]
  have hvg : ∀ x ∈ Gd, v x none = (Real.sqrt (P x) : ℂ) • χ := by
    intro x hx
    show (Fx E f μ Gd τ a0 x ⊗ₖ Ux W g P Gd τ x) *ᵥ sv E W 1 = _
    rw [Fx, Ux, if_pos hx, if_pos hx, hψ,
      core1 E W P f g μ (τ x) (P x) hE hW (hτinj x hx) (hτP x hx) (hGP x hx)]
    funext z
    simp [hχdef, sv, Pi.smul_apply]
  have hΛ : Λ (ObliviousRSP.pureState (sv E W 1)) = ∑ x, ∑ l, ObliviousRSP.pureState (v x l) := by
    simp only [Λ, F, ps_conj, Fintype.sum_unique, hvdef]
    rfl
  set z : α × Option β → (α' × β' → ℂ) :=
    fun j => if j.1 ∈ Gd ∧ j.2 = none then 0 else v j.1 j.2 with hzdef
  set c : ℝ := ∑ x ∈ Gd, P x with hcdef
  have hout : Λ (ObliviousRSP.pureState (sv E W 1))
      = (c : ℂ) • ObliviousRSP.pureState χ + ∑ j, ObliviousRSP.pureState (z j) := by
    rw [hΛ, split_sum ObliviousRSP.pureState ps_zero Gd none v]
    congr 1
    rw [Finset.sum_congr rfl fun x hx => by rw [hvg x hx, ps_smul_sqrt _ (hP0 x)], ← Finset.sum_smul,
      hcdef, Complex.ofReal_sum]
  have hN : ∑ x, ∑ l, N2 (v x l) = 1 := by
    have hK : ∑ j : α × Unit × Option β, (F j.1 j.2.1 ⊗ₖ (G j.1).K j.2.2)ᴴ
        * (F j.1 j.2.1 ⊗ₖ (G j.1).K j.2.2) = 1 := by
      have hGc : ∀ x, ∑ l : Option β, ((G x).K l)ᴴ * (G x).K l = 1 := fun x => (G x).complete
      simp only [Fintype.sum_prod_type, conjTranspose_kronecker, ← mul_kronecker_mul, ← kron_sum7,
        hGc, ← sum_kron7, hFc, one_kronecker_one]
    have h1 := kraus_N2' (fun j : α × Unit × Option β => F j.1 j.2.1 ⊗ₖ (G j.1).K j.2.2) hK (sv E W 1)
    rw [sv_N2 E W P hE hW, Fintype.sum_prod_type] at h1
    simp only [Fintype.sum_prod_type, Fintype.sum_unique, Pi.one_apply, norm_one, one_pow, one_mul,
      hP1] at h1
    exact h1
  have hχ : N2 χ = 1 := by
    rw [hχdef, sv_N2 f g (fun _ => 1) hf (fun s t => by rw [hg]; simp)]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hμ0 _), mul_one, hμ1]
  have hsum : c + ∑ j, N2 (z j) = 1 := by
    rw [← hN, split_sum N2 N2_zero Gd none v]
    congr 1
    rw [hcdef]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hvg x hx, N2_smul_sqrt _ (hP0 x), hχ, mul_one]
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun x _ => hP0 x
  have hbad : 1 - c = ∑ x ∈ Gdᶜ, P x := by
    rw [← hP1, ← Finset.sum_add_sum_compl Gd P]; ring
  rw [hout, ← hbad]
  exact k7a hK2b χ φ z c hc0 hχ hφ hsum

end Round

section Tau
variable {α T : Type} [Fintype α] [DecidableEq α] [Fintype T] [DecidableEq T]

/-- The level class of `x` for the Schmidt probabilities `P`. -/
noncomputable def cls (P : α → ℝ) (x : α) : Finset α := Finset.univ.filter fun i => P i = P x

lemma cls_eq (P : α → ℝ) {a b : α} (h : P a = P b) : cls P a = cls P b := by
  unfold cls; rw [h]

lemma mem_cls (P : α → ℝ) {i x : α} : i ∈ cls P x ↔ P i = P x := by simp [cls]

noncomputable def lsq (C : Finset α) : α → α → α := Classical.choose (latin C)

lemma lsq_row (C : Finset α) : ∀ x0 ∈ C, Set.BijOn (fun i => lsq C i x0) C C :=
  (Classical.choose_spec (latin C)).1

lemma lsq_col (C : Finset α) : ∀ i ∈ C, Set.BijOn (fun x0 => lsq C i x0) C C :=
  (Classical.choose_spec (latin C)).2

noncomputable def embE (C : Finset α) (h : Fintype.card T ≤ C.card) : T ↪ C :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (h.trans_eq (Fintype.card_coe C).symm))

noncomputable def emb (C : Finset α) (x0 : α) : T → α :=
  if h : Fintype.card T ≤ C.card then fun t => (embE C h t : α) else fun _ => x0

lemma emb_spec (C : Finset α) (x0 : α) (h : Fintype.card T ≤ C.card) :
    Function.Injective (emb C x0 : T → α) ∧ ∀ t : T, emb C x0 t ∈ C := by
  unfold emb
  rw [dif_pos h]
  exact ⟨fun a b hab => (embE C h).injective (Subtype.ext hab), fun t => (embE C h t).2⟩

lemma emb_indep (C : Finset α) (x0 x1 : α) (h : Fintype.card T ≤ C.card) :
    (emb C x0 : T → α) = emb C x1 := by
  unfold emb; rw [dif_pos h, dif_pos h]

/-- Good outcomes: positive level with a class at least as large as the target support. -/
noncomputable def Gd (P : α → ℝ) (T : Type) [Fintype T] : Finset α :=
  Finset.univ.filter fun x => 0 < P x ∧ Fintype.card T ≤ (cls P x).card

lemma mem_Gd (P : α → ℝ) {x : α} : x ∈ Gd P T ↔ 0 < P x ∧ Fintype.card T ≤ (cls P x).card := by
  simp [Gd]

lemma row_ex (C : Finset α) (x0 : α) (hx0 : x0 ∈ C) (y : α) (hy : y ∈ C) :
    ∃ i, i ∈ C ∧ lsq C i x0 = y := by
  obtain ⟨i, hi, h⟩ := (lsq_row C x0 hx0).surjOn hy
  exact ⟨i, hi, h⟩

noncomputable def tau (P : α → ℝ) (x0 : α) (t : T) : α :=
  if h : x0 ∈ Gd P T then
    Classical.choose (row_ex (cls P x0) x0 ((mem_cls P).2 rfl) (emb (cls P x0) x0 t)
      ((emb_spec (cls P x0) x0 ((mem_Gd P).1 h).2).2 t))
  else x0

lemma tau_spec (P : α → ℝ) (x0 : α) (h : x0 ∈ Gd P T) (t : T) :
    tau P x0 t ∈ cls P x0 ∧ lsq (cls P x0) (tau P x0 t) x0 = emb (cls P x0) x0 t := by
  unfold tau
  rw [dif_pos h]
  exact Classical.choose_spec (row_ex (cls P x0) x0 ((mem_cls P).2 rfl) (emb (cls P x0) x0 t)
    ((emb_spec (cls P x0) x0 ((mem_Gd P).1 h).2).2 t))

theorem tau_ok (P : α → ℝ) :
    (∀ x ∈ Gd P T, 0 < P x) ∧ (∀ x ∈ Gd P T, Function.Injective (tau P x : T → α)) ∧
    (∀ x ∈ Gd P T, ∀ t : T, P (tau P x t) = P x) ∧ (∀ x ∈ Gd P T, ∀ t : T, tau P x t ∈ Gd P T) ∧
    (∀ i ∈ Gd P T, ∀ t : T, ((Gd P T).filter fun x => tau P x t = i).card = 1) := by
  refine ⟨fun x hx => ((mem_Gd P).1 hx).1, ?_, ?_, ?_, ?_⟩
  · intro x hx t t' htt
    have h1 := (tau_spec P x hx t).2
    have h2 := (tau_spec P x hx t').2
    rw [htt, h2] at h1
    exact (emb_spec _ x ((mem_Gd P).1 hx).2).1 h1.symm
  · intro x hx t
    exact (mem_cls P).1 (tau_spec P x hx t).1
  · intro x hx t
    have hP : P (tau P x t) = P x := (mem_cls P).1 (tau_spec P x hx t).1
    rw [mem_Gd, hP, cls_eq P hP]
    exact (mem_Gd P).1 hx
  · intro i hi t
    obtain ⟨hPi, hci⟩ := (mem_Gd P).1 hi
    set C := cls P i with hC
    have hiC : i ∈ C := (mem_cls P).2 rfl
    obtain ⟨x0, hx0C, hx0⟩ := (lsq_col C i hiC).surjOn ((emb_spec C i hci).2 t)
    have hx0P : P x0 = P i := (mem_cls P).1 hx0C
    have hx0cls : cls P x0 = C := cls_eq P hx0P
    have hx0G : x0 ∈ Gd P T := by
      rw [mem_Gd, hx0P, hx0cls]; exact ⟨hPi, hci⟩
    rw [Finset.card_eq_one]
    refine ⟨x0, Finset.ext fun x => ?_⟩
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxG, hxt⟩
      obtain ⟨hmem, hsp⟩ := tau_spec P x hxG t
      rw [hxt] at hmem hsp
      have hPx : P i = P x := (mem_cls P).1 hmem
      have hclx : cls P x = C := cls_eq P hPx.symm
      rw [hclx, emb_indep C x i hci] at hsp
      have hxC : x ∈ C := (mem_cls P).2 hPx.symm
      exact (lsq_col C i hiC).injOn hxC hx0C (hsp.trans hx0.symm)
    · rintro rfl
      refine ⟨hx0G, ?_⟩
      obtain ⟨hmem, hsp⟩ := tau_spec P x hx0G t
      rw [hx0cls] at hmem hsp
      rw [emb_indep C x i hci, ← hx0] at hsp
      exact (lsq_row C x hx0C).injOn hmem hiC hsp

end Tau

section RoundAdapter
open WildeQIT.EntManip

/-- `k7round` + `tau_ok` in the form used by the achievability assembly (2ba22dc4_ach.lean). -/
def RoundP : Prop :=
  ∀ {α β α' β' T : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype T] [DecidableEq T]
    (E : α → α → ℂ) (W : α → β → ℂ) (P : α → ℝ),
    (∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0) →
    (∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0) →
    (∀ x, 0 ≤ P x) → ∑ x, P x = 1 →
    ∀ (f : T → α' → ℂ) (g : T → β' → ℂ) (μ : T → ℝ),
    (∀ s t, star (f s) ⬝ᵥ f t = if s = t then 1 else 0) →
    (∀ s t, star (g s) ⬝ᵥ g t = if s = t then 1 else 0) →
    (∀ t, 0 ≤ μ t) → ∑ t, μ t = 1 →
    ∀ (a0 : α') (o : β') (φ : α' × β' → ℂ), N2 φ = 1 →
    ∃ Λ : Matrix (α × β) (α × β) ℂ → Matrix (α' × β') (α' × β') ℂ,
      IsOneWayLOCCAB Λ ∧
      (1 / 2 : ℝ) * traceNorm (Λ (ObliviousRSP.pureState (sv E W 1)) - ObliviousRSP.pureState φ)
        ≤ Real.sqrt (N2 (sv f g (fun t => (Real.sqrt (μ t) : ℂ)) - φ)) +
          ∑ x ∈ univ.filter (fun x => ¬ (0 < P x ∧
            Fintype.card T ≤ (univ.filter fun i => P i = P x).card)), P x

theorem roundP (hK2b : K2bP) : RoundP := by
  intro α β α' β' T _ _ _ _ _ _ _ _ _ _ E W P hE hW hP0 hP1 f g μ hf hg hμ0 hμ1 a0 o φ hφ
  obtain ⟨h1, h2, h3, h4, h5⟩ := tau_ok (T := T) P
  obtain ⟨Λ, hΛ, hb⟩ := k7round hK2b E W P hE hW hP0 hP1 f g μ hf hg hμ0 hμ1 (Gd P T)
    (tau P) h1 h2 h3 h4 h5 a0 o φ hφ
  refine ⟨Λ, hΛ, hb.trans (le_of_eq ?_)⟩
  have hset : (Gd P T)ᶜ = univ.filter (fun x => ¬ (0 < P x ∧
      Fintype.card T ≤ (univ.filter fun i => P i = P x).card)) := by
    first
    | (rw [Gd, Finset.compl_filter]; rfl)
    | (ext x; simp only [Gd, cls, Finset.mem_compl]
       exact not_congr (Finset.mem_filter.trans (by simp)))
    | (ext x; simp [Gd, cls, Finset.mem_filter]; tauto)
  rw [hset]

end RoundAdapter

end EntManip2baK7

set_option autoImplicit false

open scoped Matrix Kronecker ComplexOrder Topology

namespace EntManip2baA

open Matrix Finset Filter WildeQIT WildeQIT.EntManip

noncomputable def N2 {n : Type} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

section SV
variable {α β Y : Type} [Fintype α] [Fintype β] [Fintype Y]

noncomputable def sv (e : Y → α → ℂ) (w : Y → β → ℂ) (d : Y → ℂ) : α × β → ℂ :=
  fun z => ∑ y, d y * e y z.1 * w y z.2

end SV

noncomputable def ent {α : Type} [Fintype α] (p : α → ℝ) : ℝ := -∑ a, p a * Real.logb 2 (p a)

noncomputable def hfun {α : Type} [Fintype α] (p : α → ℝ) (a : α) : ℝ :=
  -Real.logb 2 (p a) - ent p

def ChildAchieve : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 → ∑ z, ‖φ z‖ ^ 2 = 1 → 0 < entEntropy φ →
    ∀ E : ℝ, E < entEntropy ψ / entEntropy φ → IsAchievableRate ψ φ E

def K3P : Prop :=
  ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ : a × b → ℂ), ∑ z, ‖ψ z‖ ^ 2 = 1 →
    ∃ (e : a → a → ℂ) (w : a → b → ℂ) (p : a → ℝ),
      (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) ∧
      (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0) ∧
      (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
      (∀ i k, ψ (i, k) = ∑ x, e x i * w x k) ∧
      entEntropy ψ = -∑ x, p x * Real.logb 2 (p x)

def K6P : Prop :=
  ∀ {a b : Type} [Fintype a] [Fintype b] (ψ : a × b → ℂ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (e : ι → a → ℂ) (w : ι → b → ℂ) (p : ι → ℝ),
    (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) →
    (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (p x : ℂ) else 0) →
    (∀ i k, ψ (i, k) = ∑ x, e x i * w x k) → ∀ (n : ℕ),
    (∀ x y : Fin n → ι, star (fun i : Fin n → a => ∏ t, e (x t) (i t)) ⬝ᵥ
        (fun i => ∏ t, e (y t) (i t)) = if x = y then 1 else 0) ∧
    (∀ x y : Fin n → ι, star (fun k : Fin n → b => ∏ t, w (x t) (k t)) ⬝ᵥ
        (fun k => ∏ t, w (y t) (k t)) = if x = y then ((∏ t, p (x t) : ℝ) : ℂ) else 0) ∧
    (∀ i k, WildeQIT.EntManip.tensorPowVec ψ n (i, k)
      = ∑ x : Fin n → ι, (∏ t, e (x t) (i t)) * ∏ t, w (x t) (k t))

def TypP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ), (∀ a, 0 ≤ p a) → ∑ a, p a = 1 →
    ∀ (n : ℕ) (δ : ℝ) (S : Finset (Fin n → α)),
    (∀ x ∈ S, 0 < ∏ i, p (x i) ∧ ∑ i, hfun p (x i) < n * δ) →
    (S.card : ℝ) ≤ (2 : ℝ) ^ (n * (ent p + δ))

def TailP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ), (∀ a, 0 ≤ p a) → ∑ a, p a = 1 →
    ∀ (n : ℕ), 0 < n → ∀ (δ : ℝ), 0 < δ →
    ∑ x ∈ univ.filter (fun x : Fin n → α => n * δ ≤ |∑ i, hfun p (x i)|), ∏ i, p (x i)
      ≤ (∑ a, p a * hfun p a ^ 2) / (δ ^ 2 * n)

def ProbP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ) (n : ℕ) (x : Fin n → α), 0 < ∏ i, p (x i) →
    ∏ i, p (x i) = (2 : ℝ) ^ (-(∑ i, hfun p (x i)) - n * ent p)

def IidP : Prop :=
  ∀ {α : Type} [Fintype α] (p : α → ℝ), ∑ a, p a = 1 → ∀ (n : ℕ),
    ∑ x : Fin n → α, ∏ i, p (x i) = 1

def K7bP : Prop :=
  ∀ {α β Y : Type} [Fintype α] [Fintype β] [Fintype Y] [DecidableEq Y]
    (e : Y → α → ℂ) (w : Y → β → ℂ) (q : Y → ℝ),
    (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) →
    (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0) →
    (∀ y, 0 ≤ q y) → ∑ y, q y = 1 → ∀ (S : Finset Y), 0 < ∑ y ∈ S, q y →
    N2 (sv e w (fun y => if y ∈ S then ((Real.sqrt (∑ y ∈ S, q y) : ℂ))⁻¹ else 0)) = 1 ∧
    N2 (sv e w (fun y => if y ∈ S then ((Real.sqrt (∑ y ∈ S, q y) : ℂ))⁻¹ else 0) - sv e w 1)
      ≤ 2 * (1 - ∑ y ∈ S, q y)

def SvN2P : Prop :=
  ∀ {α β Y : Type} [Fintype α] [Fintype β] [Fintype Y] [DecidableEq Y]
    (e : Y → α → ℂ) (w : Y → β → ℂ) (q : Y → ℝ),
    (∀ x y, star (e x) ⬝ᵥ e y = if x = y then 1 else 0) →
    (∀ x y, star (w x) ⬝ᵥ w y = if x = y then (q x : ℂ) else 0) → ∀ (d : Y → ℂ),
    N2 (sv e w d) = ∑ y, ‖d y‖ ^ 2 * q y

def RoundP : Prop :=
  ∀ {α β α' β' T : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype T] [DecidableEq T]
    (E : α → α → ℂ) (W : α → β → ℂ) (P : α → ℝ),
    (∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0) →
    (∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0) →
    (∀ x, 0 ≤ P x) → ∑ x, P x = 1 →
    ∀ (f : T → α' → ℂ) (g : T → β' → ℂ) (μ : T → ℝ),
    (∀ s t, star (f s) ⬝ᵥ f t = if s = t then 1 else 0) →
    (∀ s t, star (g s) ⬝ᵥ g t = if s = t then 1 else 0) →
    (∀ t, 0 ≤ μ t) → ∑ t, μ t = 1 →
    ∀ (a0 : α') (o : β') (φ : α' × β' → ℂ), N2 φ = 1 →
    ∃ Λ : Matrix (α × β) (α × β) ℂ → Matrix (α' × β') (α' × β') ℂ,
      IsOneWayLOCCAB Λ ∧
      (1 / 2 : ℝ) * traceNorm (Λ (ObliviousRSP.pureState (sv E W 1)) - ObliviousRSP.pureState φ)
        ≤ Real.sqrt (N2 (sv f g (fun t => (Real.sqrt (μ t) : ℂ)) - φ)) +
          ∑ x ∈ univ.filter (fun x => ¬ (0 < P x ∧
            Fintype.card T ≤ (univ.filter fun i => P i = P x).card)), P x

/-! ### K8 combinatorics -/

lemma bad_abs {α : Type} [Fintype α] [DecidableEq α] (P : α → ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (s : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (A : Finset α) (hA : ∀ x ∉ A, P x ≤ θ) (V : Finset ℝ)
    (hV : ∀ x, P x ∈ V) (B : Finset α)
    (hB : ∀ x ∈ B, ¬ (0 < P x ∧ s ≤ (univ.filter fun i => P i = P x).card)) :
    ∑ x ∈ B, P x ≤ ∑ x ∈ A, P x + V.card * (s * θ) := by
  rw [← Finset.sum_filter_add_sum_filter_not B (fun x => x ∈ A)]
  have hsθ : 0 ≤ (s : ℝ) * θ := mul_nonneg (Nat.cast_nonneg s) hθ
  gcongr ?_ + ?_
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx; exact (Finset.mem_filter.1 hx).2
    · intro x _ _; exact hP0 x
  · have inner : ∀ v ∈ V,
        ∑ x ∈ (B.filter (fun x => x ∉ A)).filter (fun x => P x = v), P x ≤ s * θ := by
      intro v _
      have hsum : ∑ x ∈ (B.filter (fun x => x ∉ A)).filter (fun x => P x = v), P x
          = ((B.filter (fun x => x ∉ A)).filter (fun x => P x = v)).card * v := by
        rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.1 hx).2), Finset.sum_const,
          nsmul_eq_mul]
      rw [hsum]
      rcases ((B.filter (fun x => x ∉ A)).filter (fun x => P x = v)).eq_empty_or_nonempty
        with h | ⟨x0, hx0⟩
      · rw [h]; simpa using hsθ
      · have hx0' := hx0
        simp only [Finset.mem_filter] at hx0'
        obtain ⟨⟨hxB, hnA⟩, hv⟩ := hx0'
        have hθv : v ≤ θ := by rw [← hv]; exact hA x0 hnA
        rcases (hP0 x0).lt_or_eq with hpos | hzero
        · have hlt : (univ.filter fun i => P i = P x0).card < s := by
            by_contra hc; exact hB x0 hxB ⟨hpos, not_lt.1 hc⟩
          have hsub : (B.filter (fun x => x ∉ A)).filter (fun x => P x = v)
              ⊆ univ.filter fun i => P i = P x0 := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [(Finset.mem_filter.1 hx).2, hv]
          have hcard : (((B.filter (fun x => x ∉ A)).filter (fun x => P x = v)).card : ℝ) ≤ s := by
            exact_mod_cast (Finset.card_le_card hsub).trans hlt.le
          have hv0 : 0 ≤ v := by rw [← hv]; exact hP0 x0
          exact mul_le_mul hcard hθv hv0 (Nat.cast_nonneg _)
        · rw [← hv, ← hzero]; simpa using hsθ
    calc ∑ x ∈ B.filter (fun x => x ∉ A), P x
        = ∑ v ∈ V, ∑ x ∈ (B.filter (fun x => x ∉ A)).filter (fun x => P x = v), P x :=
          (Finset.sum_fiberwise_of_maps_to (by intro x _; exact hV x) _).symm
      _ ≤ ∑ v ∈ V, ((s : ℝ) * θ) := Finset.sum_le_sum inner
      _ = V.card * (s * θ) := by rw [Finset.sum_const, nsmul_eq_mul]

lemma prod_counts {a : Type} [Fintype a] [DecidableEq a] (p : a → ℝ) (n : ℕ) (x : Fin n → a) :
    ∏ t, p (x t) = ∏ c, p c ^ (univ.filter fun t => x t = c).card := by
  rw [← Finset.prod_fiberwise univ x (fun t => p (x t))]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact Finset.prod_eq_pow_card fun t ht => by rw [(Finset.mem_filter.1 ht).2]

lemma values_card {a : Type} [Fintype a] [DecidableEq a] (p : a → ℝ) (n : ℕ) :
    ∃ V : Finset ℝ, (V.card : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card a ∧
      ∀ x : Fin n → a, ∏ t, p (x t) ∈ V := by
  refine ⟨univ.image (fun c : a → Fin (n + 1) => ∏ i, p i ^ (c i : ℕ)), ?_, ?_⟩
  · have h1 := Finset.card_image_le (s := (univ : Finset (a → Fin (n + 1))))
      (f := fun c : a → Fin (n + 1) => ∏ i, p i ^ (c i : ℕ))
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
    have h2 : ((univ.image (fun c : a → Fin (n + 1) => ∏ i, p i ^ (c i : ℕ))).card : ℝ)
        ≤ (((n + 1) ^ Fintype.card a : ℕ) : ℝ) := by exact_mod_cast h1
    simpa using h2
  · intro x
    rw [Finset.mem_image]
    refine ⟨fun c => ⟨(univ.filter fun t => x t = c).card, Nat.lt_succ_of_le ?_⟩,
      Finset.mem_univ _, ?_⟩
    · exact (Finset.card_filter_le _ _).trans (by simp)
    · rw [prod_counts p n x]

/-! ### Asymptotics -/

lemma asym (Vp Vq δ' R Hq c ε : ℝ) (k : ℕ) (hR : 0 < R) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n ∧ Vq / (δ' ^ 2 * (R * n)) < 1 ∧
      Real.sqrt (2 * (Vq / (δ' ^ 2 * (R * n)))) + Vp / (δ' ^ 2 * n)
        + ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ Hq * (2 : ℝ) ^ (-(c * n)) < ε := by
  have h1 : Tendsto (fun n : ℕ => Vq / (δ' ^ 2 * (R * n))) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (Vq / (δ' ^ 2 * R))
    refine this.congr fun n => ?_
    rw [div_div, mul_assoc]
  have h1s : Tendsto (fun n : ℕ => Real.sqrt (2 * (Vq / (δ' ^ 2 * (R * n))))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto _).comp (h1.const_mul 2)
    rw [mul_zero, Real.sqrt_zero] at this
    exact this
  have h2 : Tendsto (fun n : ℕ => Vp / (δ' ^ 2 * n)) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (Vp / δ' ^ 2)
    refine this.congr fun n => ?_
    rw [div_div]
  set r : ℝ := (2 : ℝ) ^ (-c) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ n : ℕ, (2 : ℝ) ^ (-(c * n)) = r ^ n := by
    intro n
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ Hq * (2 : ℝ) ^ (-(c * n)))
      atTop (𝓝 0) := by
    have hb := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := r)
      (by rw [abs_of_pos hr0]; exact hr1)
    have hb' := (tendsto_add_atTop_iff_nat 1).2 hb
    have := hb'.const_mul ((2 : ℝ) ^ Hq / r)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    rw [hpow]
    push_cast
    rw [pow_succ]
    field_simp
  have hsum := (h1s.add h2).add h3
  rw [add_zero, add_zero] at hsum
  have ev1 := hsum.eventually (gt_mem_nhds hε)
  have ev2 := h1.eventually (gt_mem_nhds one_pos)
  have ev3 := eventually_gt_atTop (0 : ℕ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ev1.and (ev2.and ev3))
  exact ⟨N, fun n hn => ⟨(hN n hn).2.2, (hN n hn).2.1, (hN n hn).1⟩⟩

/-! ### Instantiation of one round on a typical target set -/

theorem inst (hR : RoundP) (hK7b : K7bP) (hSv : SvN2P)
    {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']
    (E : α → α → ℂ) (W : α → β → ℂ) (P : α → ℝ)
    (hE : ∀ x y, star (E x) ⬝ᵥ E y = if x = y then 1 else 0)
    (hW : ∀ x y, star (W x) ⬝ᵥ W y = if x = y then (P x : ℂ) else 0)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
    (E' : α' → α' → ℂ) (W' : α' → β' → ℂ) (Q : α' → ℝ)
    (hE' : ∀ x y, star (E' x) ⬝ᵥ E' y = if x = y then 1 else 0)
    (hW' : ∀ x y, star (W' x) ⬝ᵥ W' y = if x = y then (Q x : ℂ) else 0)
    (hQ0 : ∀ x, 0 ≤ Q x) (hQ1 : ∑ x, Q x = 1)
    (S : Finset α') (hSpos : ∀ y ∈ S, 0 < Q y) (hQS : 0 < ∑ y ∈ S, Q y)
    (a0 : α') (o : β') :
    ∃ Λ : Matrix (α × β) (α × β) ℂ → Matrix (α' × β') (α' × β') ℂ,
      IsLOCC Λ ∧
      (1 / 2 : ℝ) * traceNorm (Λ (ObliviousRSP.pureState (sv E W 1))
          - ObliviousRSP.pureState (sv E' W' 1))
        ≤ Real.sqrt (2 * (1 - ∑ y ∈ S, Q y)) +
          ∑ x ∈ univ.filter (fun x => ¬ (0 < P x ∧
            S.card ≤ (univ.filter fun i => P i = P x).card)), P x := by
  classical
  set qs := ∑ y ∈ S, Q y with hqs
  let f : {y // y ∈ S} → α' → ℂ := fun t => E' t.1
  let g : {y // y ∈ S} → β' → ℂ := fun t => (Real.sqrt (Q t.1))⁻¹ • W' t.1
  let μ : {y // y ∈ S} → ℝ := fun t => Q t.1 / qs
  have hf : ∀ s t : {y // y ∈ S}, star (f s) ⬝ᵥ f t = if s = t then 1 else 0 := by
    intro s t
    rcases eq_or_ne s t with h | h
    · subst h; simp [f, hE']
    · have h' : s.1 ≠ t.1 := fun h'' => h (Subtype.ext h'')
      simp [f, hE', h, h']
  have hg : ∀ s t : {y // y ∈ S}, star (g s) ⬝ᵥ g t = if s = t then 1 else 0 := by
    intro s t
    simp only [g, star_smul, star_trivial, smul_dotProduct, dotProduct_smul, hW' s.1 t.1]
    rcases eq_or_ne s t with h | h
    · subst h
      have hq := hSpos s.1 s.2
      rw [if_pos rfl, if_pos rfl]
      have hr : (Real.sqrt (Q s.1))⁻¹ * ((Real.sqrt (Q s.1))⁻¹ * Q s.1) = 1 := by
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hq.le, inv_mul_cancel₀ hq.ne']
      rw [Complex.real_smul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, mul_assoc, hr, Complex.ofReal_one]
    · have h' : s.1 ≠ t.1 := fun h'' => h (Subtype.ext h'')
      rw [if_neg h', if_neg h]; simp
  have hμ0 : ∀ t, 0 ≤ μ t := fun t => div_nonneg (hQ0 _) hQS.le
  have hμ1 : ∑ t, μ t = 1 := by
    show ∑ t : {y // y ∈ S}, Q t.1 / qs = 1
    rw [Finset.sum_coe_sort S (fun y => Q y / qs), ← Finset.sum_div, div_self hQS.ne']
  have hφ : N2 (sv E' W' 1) = 1 := by
    rw [hSv E' W' Q hE' hW' 1]; simp [hQ1]
  have hchi : sv f g (fun t => (Real.sqrt (μ t) : ℂ))
      = sv E' W' (fun y => if y ∈ S then ((Real.sqrt qs : ℂ))⁻¹ else 0) := by
    funext z
    simp only [sv, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hq := hSpos t.1 t.2
    have hsq : Real.sqrt (Q t.1) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
    have key : Real.sqrt (Q t.1 / qs) * (Real.sqrt (Q t.1))⁻¹ = (Real.sqrt qs)⁻¹ := by
      rw [Real.sqrt_div' _ hQS.le, div_mul_eq_mul_div, mul_inv_cancel₀ hsq, one_div]
    have key' : ((Real.sqrt (Q t.1 / qs) : ℝ) : ℂ) * (((Real.sqrt (Q t.1))⁻¹ : ℝ) : ℂ)
        = ((Real.sqrt qs : ℂ))⁻¹ := by
      rw [← Complex.ofReal_mul, key, Complex.ofReal_inv]
    simp only [μ, f, g, Pi.smul_apply, Complex.real_smul]
    rw [← key']; ring
  obtain ⟨Λ, hΛ, hb⟩ := hR E W P hE hW hP0 hP1 f g μ hf hg hμ0 hμ1 a0 o (sv E' W' 1) hφ
  refine ⟨Λ, IsLOCC.oneWayAB hΛ, hb.trans ?_⟩
  have hcard : Fintype.card {y // y ∈ S} = S.card := Fintype.card_coe S
  simp only [hcard]
  gcongr
  rw [hchi]
  exact (hK7b E' W' Q hE' hW' hQ0 hQ1 S hQS).2

/-! ### Assembly -/

set_option maxHeartbeats 1000000 in
theorem childAchieve (hK3 : K3P) (hK6 : K6P) (hTyp : TypP) (hTail : TailP) (hProb : ProbP)
    (hIid : IidP) (hR : RoundP) (hK7b : K7bP) (hSv : SvN2P) : ChildAchieve := by
  intro a b _ _ _ _ ψ φ hψ hφ hHφ E hE ε hε _ δ hδ
  obtain ⟨e, w, p, he, hw, hp0, hp1, hd, hent⟩ := hK3 ψ hψ
  obtain ⟨e', w', q, he', hw', hq0, hq1, hd', hent'⟩ := hK3 φ hφ
  have hHp : entEntropy ψ = ent p := by rw [hent]; rfl
  have hHq : entEntropy φ = ent q := by rw [hent']; rfl
  have hne : Nonempty (a × b) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hψ
    exact zero_ne_one hψ
  obtain ⟨⟨i0, k0⟩⟩ := hne
  have proto : ∀ (n m : ℕ) (S : Finset (Fin m → a)), (∀ y ∈ S, 0 < ∏ t, q (y t)) →
      0 < ∑ y ∈ S, ∏ t, q (y t) →
      IsManipProtocol ψ φ n m (Real.sqrt (2 * (1 - ∑ y ∈ S, ∏ t, q (y t))) +
        ∑ x ∈ univ.filter (fun x : Fin n → a => ¬ (0 < ∏ t, p (x t) ∧
          S.card ≤ (univ.filter fun i : Fin n → a => ∏ t, p (i t) = ∏ t, p (x t)).card)),
          ∏ t, p (x t)) := by
    intro n m S hSpos hQS
    obtain ⟨hE, hW, hψn⟩ := hK6 ψ e w p he hw hd n
    obtain ⟨hE', hW', hφm⟩ := hK6 φ e' w' q he' hw' hd' m
    have hψn' : tensorPowVec ψ n = sv (fun (x i : Fin n → a) => ∏ t, e (x t) (i t))
        (fun (x : Fin n → a) (k : Fin n → b) => ∏ t, w (x t) (k t)) 1 := by
      funext z; simp only [sv, Pi.one_apply, one_mul]; exact hψn z.1 z.2
    have hφm' : tensorPowVec φ m = sv (fun (x i : Fin m → a) => ∏ t, e' (x t) (i t))
        (fun (x : Fin m → a) (k : Fin m → b) => ∏ t, w' (x t) (k t)) 1 := by
      funext z; simp only [sv, Pi.one_apply, one_mul]; exact hφm z.1 z.2
    obtain ⟨Λ, hΛ, hb⟩ := inst hR hK7b hSv (fun (x i : Fin n → a) => ∏ t, e (x t) (i t))
      (fun (x : Fin n → a) (k : Fin n → b) => ∏ t, w (x t) (k t))
      (fun (x : Fin n → a) => ∏ t, p (x t)) hE hW
      (fun (x : Fin n → a) => Finset.prod_nonneg fun t _ => hp0 (x t)) (hIid p hp1 n)
      (fun (x i : Fin m → a) => ∏ t, e' (x t) (i t))
      (fun (x : Fin m → a) (k : Fin m → b) => ∏ t, w' (x t) (k t))
      (fun (x : Fin m → a) => ∏ t, q (x t)) hE' hW'
      (fun (x : Fin m → a) => Finset.prod_nonneg fun t _ => hq0 (x t))
      (hIid q hq1 m) S hSpos hQS (fun _ => i0) (fun _ => k0)
    refine ⟨Λ, hΛ, ?_⟩
    rw [hψn', hφm']
    exact hb
  have mono : ∀ (n m : ℕ) (x y : ℝ), IsManipProtocol ψ φ n m x → x ≤ y →
      IsManipProtocol ψ φ n m y := by
    intro n m x y ⟨Λ, h1, h2⟩ hxy
    exact ⟨Λ, h1, h2.trans hxy⟩
  by_cases hcase : E - δ ≤ 0
  · refine ⟨0, fun n _ => ⟨0, by rw [Nat.cast_zero, zero_div]; exact hcase, ?_⟩⟩
    have hQS1 : ∑ y ∈ (univ : Finset (Fin 0 → a)), ∏ t, q (y t) = 1 := hIid q hq1 0
    have hpr := proto n 0 univ (fun y _ => by simp) (by rw [hQS1]; exact one_pos)
    refine mono _ _ _ _ hpr ?_
    have hb : ∑ x ∈ univ.filter (fun x : Fin n → a => ¬ (0 < ∏ t, p (x t) ∧
          (univ : Finset (Fin 0 → a)).card ≤
            (univ.filter fun i : Fin n → a => ∏ t, p (i t) = ∏ t, p (x t)).card)),
          ∏ t, p (x t) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have h1 : (univ : Finset (Fin 0 → a)).card ≤
          (univ.filter fun i : Fin n → a => ∏ t, p (i t) = ∏ t, p (x t)).card := by
        rw [Finset.card_univ, Fintype.card_unique]
        exact Finset.card_pos.2 ⟨x, by simp⟩
      have h2 : ¬ (0 < ∏ t, p (x t)) := fun h => hx ⟨h, h1⟩
      exact le_antisymm (not_lt.1 h2) (Finset.prod_nonneg fun t _ => hp0 _)
    rw [hb, hQS1, sub_self, mul_zero, Real.sqrt_zero, add_zero]
    exact hε.le
  · rw [not_le] at hcase
    set R := E - δ with hRdef
    set Hp := ent p with hHpdef
    set Hq := ent q with hHqdef
    have hHq0 : 0 < Hq := by rw [← hHq]; exact hHφ
    have hRE : R < Hp / Hq := by rw [← hHp, ← hHq]; linarith
    have hRH : R * Hq < Hp := (lt_div_iff₀ hHq0).1 hRE
    have h12 : (0 : ℝ) < 1 + 2 * R := by linarith only [hcase]
    set δ' := (Hp - R * Hq) / 2 / (1 + 2 * R) with hδ'def
    have hδ' : 0 < δ' := div_pos (by linarith only [hRH]) h12
    have key : δ' * (1 + 2 * R) = (Hp - R * Hq) / 2 := div_mul_cancel₀ _ h12.ne'
    set c := (Hp - R * Hq) / 2 with hcdef
    have hc : 0 < c := by linarith only [hcdef, hRH]
    have hexp : R * (Hq + 2 * δ') - Hp + δ' = -c := by linear_combination key
    set Vp := ∑ x, p x * hfun p x ^ 2 with hVp
    set Vq := ∑ x, q x * hfun q x ^ 2 with hVq
    have hVq0 : 0 ≤ Vq := Finset.sum_nonneg fun x _ => mul_nonneg (hq0 x) (sq_nonneg _)
    obtain ⟨N, hN⟩ := asym Vp Vq δ' R (Hq + 2 * δ') c ε (Fintype.card a) hcase hc hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hn0, hsmall, hlt⟩ := hN n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    set m := ⌈R * n⌉₊ with hmdef
    have hmR : R * n ≤ m := Nat.le_ceil _
    have hm1 : (m : ℝ) < R * n + 1 := Nat.ceil_lt_add_one (by positivity)
    have hmpos' : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmR
    have hmpos : 0 < m := by exact_mod_cast hmpos'
    refine ⟨m, by rw [le_div_iff₀ hnR]; exact hmR, ?_⟩
    set S := univ.filter (fun y : Fin m → a =>
      0 < ∏ t, q (y t) ∧ |∑ i, hfun q (y i)| ≤ m * δ') with hSdef
    have hSpos : ∀ y ∈ S, 0 < ∏ t, q (y t) := fun y hy => (Finset.mem_filter.1 hy).2.1
    -- tail of the target
    have htail : 1 - ∑ y ∈ S, ∏ t, q (y t) ≤ Vq / (δ' ^ 2 * (R * n)) := by
      have hsplit := Finset.sum_filter_add_sum_filter_not univ
        (fun y : Fin m → a => 0 < ∏ t, q (y t) ∧ |∑ i, hfun q (y i)| ≤ m * δ')
        (fun y => ∏ t, q (y t))
      rw [hIid q hq1 m, ← hSdef] at hsplit
      have hle : ∑ y ∈ univ.filter (fun y : Fin m → a =>
            ¬ (0 < ∏ t, q (y t) ∧ |∑ i, hfun q (y i)| ≤ m * δ')), ∏ t, q (y t)
          ≤ ∑ y ∈ univ.filter (fun y : Fin m → a => m * δ' ≤ |∑ i, hfun q (y i)|),
              ∏ t, q (y t) := by
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro y _
        by_cases h1 : (0 < ∏ t, q (y t) ∧ |∑ i, hfun q (y i)| ≤ m * δ')
        · rw [if_neg (not_not.2 h1)]
          split_ifs
          · exact Finset.prod_nonneg fun t _ => hq0 _
          · exact le_rfl
        · rw [if_pos h1]
          split_ifs with h2
          · exact le_rfl
          · exact not_lt.1 fun hq => h1 ⟨hq, (not_le.1 h2).le⟩
      have ht := hTail q hq0 hq1 m hmpos δ' hδ'
      rw [← hVq] at ht
      have hdiv : Vq / (δ' ^ 2 * m) ≤ Vq / (δ' ^ 2 * (R * n)) :=
        div_le_div_of_nonneg_left hVq0 (by positivity)
          (mul_le_mul_of_nonneg_left hmR (by positivity))
      linarith only [hsplit, hle, ht, hdiv]
    have hQS : 0 < ∑ y ∈ S, ∏ t, q (y t) := by linarith only [htail, hsmall]
    -- size of the target typical set
    have hcardS : (S.card : ℝ) ≤ (2 : ℝ) ^ (m * (Hq + 2 * δ')) := by
      refine hTyp q hq0 hq1 m (2 * δ') S fun y hy => ⟨hSpos y hy, ?_⟩
      have hy2 := (Finset.mem_filter.1 hy).2.2
      have hmδ : (0 : ℝ) < (m : ℝ) * δ' := mul_pos hmpos' hδ'
      linarith only [le_abs_self (∑ i, hfun q (y i)), hy2, hmδ,
        show (m : ℝ) * (2 * δ') = 2 * ((m : ℝ) * δ') by ring]
    -- bad mass of the source
    obtain ⟨V, hVc, hV⟩ := values_card p n
    set θ := (2 : ℝ) ^ (-(n * (Hp - δ'))) with hθdef
    have hθ0 : 0 ≤ θ := by positivity
    have hA : ∀ x ∉ univ.filter (fun x : Fin n → a => n * δ' ≤ |∑ i, hfun p (x i)|),
        ∏ t, p (x t) ≤ θ := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx
      rcases (Finset.prod_nonneg fun t _ => hp0 (x t) : 0 ≤ ∏ t, p (x t)).lt_or_eq with hpos | hz
      · rw [hProb p n x hpos]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h4 := neg_le_abs (∑ i, hfun p (x i))
        have e3 : -((n : ℝ) * (Hp - δ')) = -((n : ℝ) * Hp) + n * δ' := by ring
        have e4 : (n : ℝ) * ent p = n * Hp := by rw [hHpdef]
        rw [e3]
        linarith only [h4, hx, e4]
      · rw [← hz]; exact hθ0
    have hbad := bad_abs (fun x : Fin n → a => ∏ t, p (x t))
      (fun x => Finset.prod_nonneg fun t _ => hp0 _) S.card θ hθ0 _ hA V hV
      (univ.filter (fun x : Fin n → a => ¬ (0 < ∏ t, p (x t) ∧
          S.card ≤ (univ.filter fun i : Fin n → a => ∏ t, p (i t) = ∏ t, p (x t)).card)))
      (fun x hx => (Finset.mem_filter.1 hx).2)
    have hAt := hTail p hp0 hp1 n hn0 δ' hδ'
    rw [← hVp] at hAt
    have hexpo : (2 : ℝ) ^ (m * (Hq + 2 * δ')) * θ ≤ (2 : ℝ) ^ (Hq + 2 * δ') * (2 : ℝ) ^ (-(c * n)) := by
      rw [hθdef, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hHq'0 : 0 ≤ Hq + 2 * δ' := by linarith only [hHq0, hδ']
      have e1 : (m : ℝ) * (Hq + 2 * δ') ≤ (R * n + 1) * (Hq + 2 * δ') :=
        mul_le_mul_of_nonneg_right hm1.le hHq'0
      have e2 : (R * n + 1) * (Hq + 2 * δ') + -(n * (Hp - δ')) = (Hq + 2 * δ') + -(c * n) := by
        linear_combination (n : ℝ) * hexp
      linarith only [e1, e2]
    have hVS : (V.card : ℝ) * (S.card * θ) ≤
        ((n : ℝ) + 1) ^ Fintype.card a * (2 : ℝ) ^ (Hq + 2 * δ') * (2 : ℝ) ^ (-(c * n)) := by
      rw [mul_assoc]
      exact mul_le_mul hVc ((mul_le_mul_of_nonneg_right hcardS hθ0).trans hexpo)
        (mul_nonneg (Nat.cast_nonneg _) hθ0) (by positivity)
    have hsq : Real.sqrt (2 * (1 - ∑ y ∈ S, ∏ t, q (y t)))
        ≤ Real.sqrt (2 * (Vq / (δ' ^ 2 * (R * n)))) := Real.sqrt_le_sqrt (by linarith only [htail])
    refine mono _ _ _ _ (proto n m S hSpos hQS) ?_
    linarith only [hsq, hbad, hAt, hVS, hlt]

end EntManip2baA

theorem achieve_main : EntManip2baA.ChildAchieve :=
  EntManip2baA.childAchieve EntManip2ba.k3 EntManip2ba.k6 EntManip2ba.typ_card EntManip2ba.tail_le
    EntManip2ba.prob_eq EntManip2ba.iid_one
    (EntManip2baK7.roundP (by intro n _ _ M hM; exact EntManip2ba.k2b M hM))
    EntManip2baK7.k7b EntManip2baK7.sv_N2

open WildeQIT.EntManip in
theorem solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ) (hψ : ∑ z, ‖ψ z‖ ^ 2 = 1) (hφ : ∑ z, ‖φ z‖ ^ 2 = 1)
    (hφpos : 0 < entEntropy φ) :
    IsLUB {E : ℝ | IsAchievableRate ψ φ E} (entEntropy ψ / entEntropy φ) := by
  exact EntManip2ba.glue ψ φ _ (fun E hE => achieve_main ψ φ hψ hφ hφpos E hE)
    (fun E hE => EntManip2ba.childConverse ψ φ hψ hφ hφpos E hE)
