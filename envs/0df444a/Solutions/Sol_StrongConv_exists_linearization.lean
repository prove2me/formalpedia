-- Prove2me | solution 1 for StrongConv.exists_linearization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T03:59:19.747539+00:00
-- url     : https://prove2.me/submissions/0b6be12c-45ef-4c54-b204-e9ae9b0a39e4

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_unital_completelyPositive_extension

section
/-!
# Blueprint: Pisier's linearization (CGTvH Lemma 9.1)

Route (see `BRIEF.md` beside this file):
* `Part1`  (Lemma 1 + Hahn–Banach): factorization with contractive linear factors follows from
  `core_bound`.
* `core_bound` from `per_degree` (CES with frames, Lemmas 2–6), `shift_average` (Lemma 7),
  `coherent_limit` (Lemma 8), `compress` (Lemma 9), `endgame` (Lemma 10, Arveson + Stinespring).
-/

noncomputable section

namespace StrongConv.S9.Pisier

open scoped InnerProductSpace

/-! ## Operators with matrix coefficients between two Hilbert spaces -/

section Ops

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- `A ⊗ T : H₁ⁿ → H₂ᵐ` for `T : H₁ → H₂`: the `(a, b)` block is `A a b • T`. -/
def tOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    PiLp 2 (fun _ : Fin n => H₁) →L[ℂ] PiLp 2 (fun _ : Fin m => H₂) :=
  ∑ a : Fin m, ∑ b : Fin n, A a b •
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => H₂)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.single ℂ (fun _ : Fin m => H₂) a).comp
        (T.comp (PiLp.proj 2 (fun _ : Fin n => H₁) b))))

/-- The amplification `∑ₗ X(l) ⊗ ρ(l)` of a letter map `ρ` at a matrix of letters `X`. -/
def amp {ι : Type*} [Fintype ι] (ρ : ι → H₁ →L[ℂ] H₂) {m n : ℕ}
    (X : ι → Matrix (Fin m) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n => H₁) →L[ℂ] PiLp 2 (fun _ : Fin m => H₂) :=
  ∑ l, tOp (X l) (ρ l)

end Ops

/-- The operator norm of a scalar `m × n` matrix acting `ℂⁿ → ℂᵐ` (Euclidean norms). -/
def sNorm {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C)‖

section Letters

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- A word in the letters evaluated by a letter map: the product of its letters in order. -/
def evalW {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : ι → H →L[ℂ] H) (w : List ι) : H →L[ℂ] H :=
  (w.map ρ).prod

/-- A formal `n × n` matrix polynomial evaluated by a letter map. -/
def evalP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : ι → H →L[ℂ] H) {n : ℕ} (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  ∑ w ∈ y.support, tOp (y w) (evalW ρ w)

/-- The pairing `⟪y, F⟫ = ∑_w ∑_{i,j} y(w)ᵢⱼ F(w)ᵢⱼ` of a formal polynomial with a coefficient
functional. -/
def pairing {n : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ w ∈ y.support, ∑ i, ∑ j, y w i j * F w i j

/-- `ρ` is completely contractive relative to `e` on the span of the letters, at every square
matrix level. -/
def CC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : ι → L →L[ℂ] L) (ρ : ι → H →L[ℂ] H) : Prop :=
  ∀ (k : ℕ) (X : ι → Matrix (Fin k) (Fin k) ℂ), ‖amp ρ X‖ ≤ ‖amp e X‖

/-- `ρ` satisfies every linear relation among words that `e` satisfies. -/
def RespectsRel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : ι → L →L[ℂ] L) (ρ : ι → H →L[ℂ] H) : Prop :=
  ∀ t : List ι →₀ ℂ, (∑ w ∈ t.support, t w • evalW e w) = 0 →
    (∑ w ∈ t.support, t w • evalW ρ w) = 0

/-- The coefficient functional `F` satisfies every linear relation among words that `e`
satisfies. -/
def FRel (e : ι → L →L[ℂ] L) {n : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ t : List ι →₀ ℂ, (∑ w ∈ t.support, t w • evalW e w) = 0 →
    (∑ w ∈ t.support, t w • F w) = 0

/-- The product `X₀(w₀) X₁(w₁) ⋯` of square letter matrices along a word of fixed length. -/
def prodX {M K : ℕ} (X : Fin M → ι → Matrix (Fin K) (Fin K) ℂ) (w : Fin M → ι) :
    Matrix (Fin K) (Fin K) ℂ :=
  (List.ofFn fun l => X l (w l)).prod

/-- The hypothesis on `F` coming from `‖f‖ ≤ 1` for the factorization gauge: for every chain of
contractive square letter matrices framed by contractive scalar matrices `C` and `R`,
`|∑_w ∑_{i,j} (C X(w) R)ᵢⱼ F(w)ᵢⱼ| ≤ 1`. -/
def ChainBound (e : ι → L →L[ℂ] L) {n : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (M K : ℕ) (X : Fin M → ι → Matrix (Fin K) (Fin K) ℂ) (C : Matrix (Fin n) (Fin K) ℂ)
    (R : Matrix (Fin K) (Fin n) ℂ),
    (∀ l, ‖amp e (X l)‖ ≤ 1) → sNorm C ≤ 1 → sNorm R ≤ 1 →
      ‖∑ w : Fin M → ι, ∑ i, ∑ j, (C * prodX X w * R) i j * F (List.ofFn w) i j‖ ≤ 1

/-- Standing assumptions on the letters: a unit letter `o` with `e o = 1`, and every letter is a
unitary whose adjoint is again a letter. -/
structure UnitaryLetters (e : ι → L →L[ℂ] L) where
  o : ι
  e_o : e o = 1
  inv : ι → ι
  e_inv : ∀ l, e (inv l) = star (e l)
  unitary : ∀ l, e l ∈ unitary (L →L[ℂ] L)

/-! ## The chain of the analytic argument -/

/-! ## Chains of linear factors -/

/-- The product `X_t X_{t+1} ⋯ X_{t+k-1}` of linear factors `X_j = ∑ₗ A_{j,l} ⊗ e(l)`
(generic version of the bundle's `linChain`). -/
def gChain (e : ι → L →L[ℂ] L) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (t : ℕ) :
    ∀ k : ℕ, PiLp 2 (fun _ : Fin (Dim (t + k)) => L) →L[ℂ]
      PiLp 2 (fun _ : Fin (Dim t) => L)
  | 0 => ContinuousLinearMap.id ℂ _
  | k + 1 => (gChain e Dim A t k).comp (amp e (A (t + k)))

/-- `X₁ ⋯ X_q` on `D` copies of `L` when `D₁ = D_{q+1} = D` (generic `linChainOn`). -/
def gChainOn (e : ι → L →L[ℂ] L) {D : ℕ} (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (q : ℕ)
    (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D) :
    PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L) :=
  (reindexCopies (finCongr h₁)).comp ((gChain e Dim A 1 q).comp (reindexCopies (finCongr hq).symm))

end Letters

/-! ## Lemma 9.1 -/

/-- The letters `g₀ = e, gᵢ, gᵢ⁻¹` acting on `ℓ²(F_d)`. -/
def freeLetters (d : ℕ) : Letter d → L2Free d →L[ℂ] L2Free d :=
  fun l => wordEval (sLimit d) [l]

/-- The inverse of a letter: `g₀ ↦ g₀`, `gᵢ ↔ gᵢ⁻¹`. -/
def letterInv {d : ℕ} : Letter d → Letter d
  | none => none
  | some (Sum.inl i) => some (Sum.inr i)
  | some (Sum.inr i) => some (Sum.inl i)

end StrongConv.S9.Pisier
end
end

section
/-!
# PartD, generic peeling (finite-dimensional Christensen–Effros–Sinclair with abstract slot norms)

Sub-blueprint (internal to PartD):

* Words have `m` slots over one alphabet `α`; slot `0` is the *rightmost* factor.
* Each slot carries an abstract "matrix norm" `N l κ X` for `X : α → Matrix κ κ ℂ`
  satisfying `NAx` (homogeneity, left multiplication by scalar contractions, block diagonals).
* `HC N Ψ`: the multilinear functional `Ψ` is Haagerup-contractive (normalized form, with the
  Euclidean norm of the output column absorbing the left frame).
* `step`: one cut (Hahn–Banach on a sublinear functional on `End V`, `V = ⊕_α H`) produces a
  contractive last factor and a Haagerup-contractive remainder.
* `peel`: induction, everything padded into `EuclideanSpace ℂ (Fin R)`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix

namespace StrongConv.S9.Pisier.PartD

/-- Reversed ordered product `f (m-1) * ⋯ * f 0`. -/
def rprod {Mo : Type*} [Monoid Mo] : (m : ℕ) → (Fin m → Mo) → Mo
  | 0, _ => 1
  | m + 1, f => rprod m (fun l => f l.succ) * f 0

@[simp] lemma rprod_zero {Mo : Type*} [Monoid Mo] (f : Fin 0 → Mo) : rprod 0 f = 1 := rfl

lemma rprod_succ {Mo : Type*} [Monoid Mo] (m : ℕ) (f : Fin (m + 1) → Mo) :
    rprod (m + 1) f = rprod m (fun l => f l.succ) * f 0 := rfl

/-- Abstract per-slot matrix norms. -/
abbrev NormFn (α : Type) := ∀ (κ : Type) [Fintype κ], (α → Matrix κ κ ℂ) → ℝ

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Axioms on a slot norm. -/
structure NAx (N : NormFn α) : Prop where
  nonneg : ∀ (κ : Type) [Fintype κ] (Y : α → Matrix κ κ ℂ), 0 ≤ N κ Y
  smul : ∀ (κ : Type) [Fintype κ] (t : ℂ) (Y : α → Matrix κ κ ℂ),
    N κ (fun c => t • Y c) ≤ ‖t‖ * N κ Y
  mul : ∀ (κ : Type) [Fintype κ] (β : Matrix κ κ ℂ) (Y : α → Matrix κ κ ℂ),
    (∀ x : κ → ℂ, ∑ a, ‖(β *ᵥ x) a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2) → N κ (fun c => β * Y c) ≤ N κ Y
  diag : ∀ (κ₁ κ₂ : Type) [Fintype κ₁] [Fintype κ₂] (Y₁ : α → Matrix κ₁ κ₁ ℂ)
    (Y₂ : α → Matrix κ₂ κ₂ ℂ),
    N (κ₁ ⊕ κ₂) (fun c => Matrix.fromBlocks (Y₁ c) 0 0 (Y₂ c)) ≤ max (N κ₁ Y₁) (N κ₂ Y₂)

lemma NAx.zero_le_one {N : NormFn α} (hN : NAx N) (κ : Type) [Fintype κ] :
    N κ (fun _ => 0) ≤ 1 := by
  have h0 := hN.smul κ 0 (fun _ => 0)
  simp only [zero_smul, norm_zero, zero_mul] at h0
  linarith

/-- The output column of a chain applied to a column of vectors. -/
def sV {m : ℕ} {H : Type} [AddCommGroup H] [Module ℂ H] {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : (Fin m → α) → H →ₗ[ℂ] ℂ) (X : Fin m → α → Matrix κ κ ℂ) (h : κ → H) : κ → ℂ :=
  fun a => ∑ w : Fin m → α, ∑ b, rprod m (fun l => X l (w l)) a b * Ψ w (h b)

/-- Haagerup contractivity (normalized). -/
def HC {m : ℕ} (N : Fin m → NormFn α) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ψ : (Fin m → α) → H →ₗ[ℂ] ℂ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Fin m → α → Matrix κ κ ℂ) (h : κ → H),
    (∀ l, N l κ (X l) ≤ 1) → ∑ a, ‖sV Ψ X h a‖ ^ 2 ≤ ∑ b, ‖h b‖ ^ 2

/-- Complete contractivity of a letter map relative to a slot norm (normalized). -/
def CCN (N : NormFn α) {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (φ : α → H₁ →L[ℂ] H₂) : Prop :=
  ∀ (κ : Type) [Fintype κ] (X : α → Matrix κ κ ℂ), N κ X ≤ 1 → ∀ ζ : κ → H₁,
    ∑ a, ‖∑ c, ∑ b, X c a b • φ c (ζ b)‖ ^ 2 ≤ ∑ b, ‖ζ b‖ ^ 2

abbrev E (R : ℕ) := EuclideanSpace ℂ (Fin R)

end StrongConv.S9.Pisier.PartD
end
end

section
/-!
# PartD, the one-cut step

`V = PiLp 2 (α → H)`. A Hahn–Banach argument on the sublinear functional `p` on `End V`
(`exists_ell`) gives a real functional `ℓ` with `‖s(X, v)‖² ≤ ℓ(Gram v)` for contractive chains
and `ℓ(Gram (Y h)) ≤ ‖h‖²` for contractive last letters; `ℓ` is a positive form, factored as
`‖Γ z‖² = ℓ(|z⟩⟨z|)`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix InnerProductSpace
open scoped Pointwise

set_option synthInstance.maxHeartbeats 200000

namespace StrongConv.S9.Pisier.PartD

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## Generic finite-dimensional lemmas -/

/-- Factor `B` through `A` when `ker A ≤ ker B`, vanishing on `(range A)ᗮ`. -/
lemma factor {V K W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] [AddCommGroup W] [Module ℂ W] (A : V →ₗ[ℂ] K) (B : V →ₗ[ℂ] W)
    (hker : ∀ x, A x = 0 → B x = 0) :
    ∃ T : K →ₗ[ℂ] W, (∀ x, T (A x) = B x) ∧ ∀ y, ∃ x, T y = B x ∧ ‖A x‖ ≤ ‖y‖ := by
  classical
  let Rg : Submodule ℂ K := LinearMap.range A
  let T₀ : Rg →ₗ[ℂ] W := ((LinearMap.ker A).liftQ B (fun x hx =>
    LinearMap.mem_ker.mpr (hker x (LinearMap.mem_ker.mp hx)))).comp
      A.quotKerEquivRange.symm.toLinearMap
  have hT₀ : ∀ x, T₀ ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    intro x
    simp only [T₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let P : K →L[ℂ] Rg := Rg.orthogonalProjectionOnto
  refine ⟨T₀ ∘ₗ P.toLinearMap, fun x => ?_, fun y => ?_⟩
  · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    have : P (A x) = ⟨A x, LinearMap.mem_range_self A x⟩ :=
      Rg.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, LinearMap.mem_range_self A x⟩
    rw [this, hT₀]
  · obtain ⟨x, hx⟩ := (P y).2
    refine ⟨x, ?_, ?_⟩
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      have : P y = ⟨A x, LinearMap.mem_range_self A x⟩ := Subtype.ext hx.symm
      rw [this, hT₀]
    · rw [hx]
      exact Rg.norm_orthogonalProjectionOnto_apply_le y

lemma euc_expand {κ : Type} [Fintype κ] [DecidableEq κ] (y : EuclideanSpace ℂ κ) :
    y = ∑ a, y a • EuclideanSpace.single a (1 : ℂ) := by
  ext b
  simp [Pi.single_apply]

lemma euc_norm_sq {κ : Type} [Fintype κ] (y : EuclideanSpace ℂ κ) :
    ‖y‖ ^ 2 = ∑ a, ‖y a‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- Douglas' lemma for finite families. -/
lemma douglas {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} [Fintype κ] [DecidableEq κ] (u v : κ → V)
    (huv : ∀ z, ∑ d, ‖⟪v d, z⟫_ℂ‖ ^ 2 ≤ ∑ a, ‖⟪u a, z⟫_ℂ‖ ^ 2) :
    ∃ β : Matrix κ κ ℂ, (∀ x : κ → ℂ, ∑ a, ‖(β *ᵥ x) a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2) ∧
      ∀ d, v d = ∑ a, β d a • u a := by
  classical
  let A : V →ₗ[ℂ] EuclideanSpace ℂ κ :=
    { toFun := fun z => WithLp.toLp 2 (fun a => ⟪u a, z⟫_ℂ)
      map_add' := fun x y => by ext a; simp [inner_add_right]
      map_smul' := fun c x => by ext a; simp [inner_smul_right] }
  let B : V →ₗ[ℂ] EuclideanSpace ℂ κ :=
    { toFun := fun z => WithLp.toLp 2 (fun a => ⟪v a, z⟫_ℂ)
      map_add' := fun x y => by ext a; simp [inner_add_right]
      map_smul' := fun c x => by ext a; simp [inner_smul_right] }
  have hA : ∀ z a, A z a = ⟪u a, z⟫_ℂ := fun _ _ => rfl
  have hB : ∀ z a, B z a = ⟪v a, z⟫_ℂ := fun _ _ => rfl
  have hnorm : ∀ z, ‖B z‖ ≤ ‖A z‖ := by
    intro z
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), euc_norm_sq, euc_norm_sq]
    simpa only [hA, hB] using huv z
  obtain ⟨T, hTA, hT⟩ := factor A B (fun x hx => by
    have := hnorm x
    rw [hx, norm_zero] at this
    exact norm_le_zero_iff.mp this)
  have hTc : ∀ y, ‖T y‖ ≤ ‖y‖ := fun y => by
    obtain ⟨x, hx, hxn⟩ := hT y
    rw [hx]
    exact (hnorm x).trans hxn
  let β : Matrix κ κ ℂ := fun d a => conj (T (EuclideanSpace.single a 1) d)
  have hTy : ∀ (y : EuclideanSpace ℂ κ) d, T y d = ∑ a, y a * T (EuclideanSpace.single a 1) d := by
    intro y d
    conv_lhs => rw [euc_expand y]
    simp [map_sum, map_smul]
  refine ⟨β, fun x => ?_, fun d => ?_⟩
  · let y : EuclideanSpace ℂ κ := WithLp.toLp 2 (fun a => conj (x a))
    have h1 : ∀ d, (β *ᵥ x) d = conj (T y d) := by
      intro d
      rw [hTy]
      simp [β, mulVec, dotProduct, y, map_sum, mul_comm]
    have h2 := hTc y
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), euc_norm_sq, euc_norm_sq] at h2
    simpa [h1, y] using h2
  · apply ext_inner_right ℂ
    intro z
    have h1 : ⟪v d, z⟫_ℂ = T (A z) d := by rw [hTA, hB]
    rw [h1, hTy, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [β, inner_smul_left, hA, mul_comm]

/-- A real functional on `End V`, positive on rank-one projections and vanishing on `i` times
them, is a sum of squares of linear functionals. -/
lemma exists_Gamma {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ℓ : (V →L[ℂ] V) →ₗ[ℝ] ℝ) (hpos : ∀ z, 0 ≤ ℓ (rankOne ℂ z z))
    (hI : ∀ z, ℓ ((Complex.I : ℂ) • rankOne ℂ z z) = 0) :
    ∃ (r : ℕ) (Γ : V →ₗ[ℂ] E r), ∀ z, ‖Γ z‖ ^ 2 = ℓ (rankOne ℂ z z) := by
  classical
  let ℓc : (V →L[ℂ] V) →ₗ[ℂ] ℂ := Module.Dual.extendRCLike ℓ
  have hℓc : ∀ T, ℓc T = (ℓ T : ℂ) - Complex.I * (ℓ ((Complex.I : ℂ) • T) : ℂ) :=
    fun T => Module.Dual.extendRCLike_apply ℓ T
  have hℓcz : ∀ z, ℓc (rankOne ℂ z z) = (ℓ (rankOne ℂ z z) : ℂ) := by
    intro z; rw [hℓc, hI]; simp
  let f : V → StrongDual ℂ V := fun x =>
    LinearMap.toContinuousLinearMap (ℓc ∘ₗ ((rankOne ℂ).flip x : V →L[ℂ] (V →L[ℂ] V)).toLinearMap)
  have hf : ∀ x w, f x w = ℓc (rankOne ℂ w x) := fun x w => rfl
  let Ωf : V → V := fun x => (toDual ℂ V).symm (f x)
  have hΩ : ∀ x w, ⟪Ωf x, w⟫_ℂ = ℓc (rankOne ℂ w x) := by
    intro x w; simp only [Ωf, toDual_symm_apply, hf]
  let Ω : V →ₗ[ℂ] V :=
    { toFun := Ωf
      map_add' := fun x y => by
        apply ext_inner_right ℂ; intro w
        rw [inner_add_left, hΩ, hΩ, hΩ, map_add, map_add]
      map_smul' := fun c x => by
        apply ext_inner_right ℂ; intro w
        rw [inner_smul_left, hΩ, hΩ, map_smulₛₗ, map_smul]
        simp }
  have hΩz : ∀ z, ⟪Ω z, z⟫_ℂ = (ℓ (rankOne ℂ z z) : ℂ) := fun z => (hΩ z z).trans (hℓcz z)
  have hΩpos : (LinearMap.toContinuousLinearMap Ω).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    simp only [LinearMap.coe_toContinuousLinearMap', hΩz, Complex.ofReal_re]
    exact ⟨rfl, hpos x⟩
  obtain ⟨r, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hΩpos
  let Γ : V →ₗ[ℂ] E r :=
    { toFun := fun z => WithLp.toLp 2 (fun i => ⟪u i, z⟫_ℂ)
      map_add' := fun x y => by ext a; simp [inner_add_right]
      map_smul' := fun c x => by ext a; simp [inner_smul_right] }
  refine ⟨r, Γ, fun z => ?_⟩
  have h1 : ⟪Ω z, z⟫_ℂ = ∑ i, ⟪u i, z⟫_ℂ * conj ⟪u i, z⟫_ℂ := by
    have : Ω z = (LinearMap.toContinuousLinearMap Ω) z := rfl
    rw [this, hu]
    simp only [FunLike.coe_sum, Finset.sum_apply, rankOne_apply, sum_inner,
      inner_smul_left, inner_conj_symm]
    refine Finset.sum_congr rfl fun i _ => by rw [← inner_conj_symm (u i) z]; ring
  have h2 : ‖Γ z‖ ^ 2 = ∑ i, ‖⟪u i, z⟫_ℂ‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rfl
  have h3 := congrArg Complex.re (hΩz z)
  rw [h1] at h3
  simp only [Complex.mul_conj, Complex.re_sum, Complex.ofReal_re] at h3
  rw [h2, ← h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

/-! ## The setting of one cut -/

section Cut

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The space of the cut. -/
abbrev VS (α H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  PiLp 2 (fun _ : α => H)

/-- `Ψ̃(u)(v) = ∑_c Ψ(c :: u)(v c)`. -/
def Ψt (Ψ : (Fin (m + 1) → α) → H →ₗ[ℂ] ℂ) (u : Fin m → α) : VS α H →ₗ[ℂ] ℂ :=
  ∑ c, (Ψ (Fin.cons c u)).comp (PiLp.projₗ 2 (fun _ : α => H) c)

/-- The column `Y ⊙ h` of vectors of `V`. -/
def Yh {κ : Type} [Fintype κ] (Y : α → Matrix κ κ ℂ) (h : κ → H) : κ → VS α H :=
  fun a => WithLp.toLp 2 (fun c => ∑ b, Y c a b • h b)

/-- The Gram quadratic form of a column. -/
def Gq {κ : Type} [Fintype κ] (u : κ → VS α H) (z : VS α H) : ℝ := ∑ a, ‖⟪u a, z⟫_ℂ‖ ^ 2

/-- The Gram operator of a column. -/
def Gop {κ : Type} [Fintype κ] (u : κ → VS α H) : VS α H →L[ℂ] VS α H :=
  ∑ a, rankOne ℂ (u a) (u a)

lemma re_inner_Gop {κ : Type} [Fintype κ] (u : κ → VS α H) (z : VS α H) :
    Complex.re ⟪z, Gop u z⟫_ℂ = Gq u z := by
  simp only [Gop, FunLike.coe_sum, Finset.sum_apply, rankOne_apply, inner_sum,
    inner_smul_right, Complex.re_sum, Gq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← inner_conj_symm (u a) z, Complex.conj_mul']
  norm_cast
  rw [RCLike.norm_conj]

lemma Ψt_apply (Ψ : (Fin (m + 1) → α) → H →ₗ[ℂ] ℂ) (u : Fin m → α) (v : VS α H) :
    Ψt Ψ u v = ∑ c, Ψ (Fin.cons c u) (v c) := by
  simp [Ψt, LinearMap.sum_apply]

/-- The peeling identity. -/
lemma sV_cons {κ : Type} [Fintype κ] [DecidableEq κ] (Ψ : (Fin (m + 1) → α) → H →ₗ[ℂ] ℂ)
    (Y : α → Matrix κ κ ℂ) (X : Fin m → α → Matrix κ κ ℂ) (h : κ → H) :
    sV Ψ (Fin.cons Y X : Fin (m + 1) → α → Matrix κ κ ℂ) h = sV (Ψt Ψ) X (Yh Y h) := by
  funext a
  simp only [sV]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, rprod_succ, Fin.cons_zero, Fin.cons_succ, Ψt_apply, Yh,
    PiLp.toLp_apply, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  rw [show (Fin.consEquiv fun _ => α) (c, u) = Fin.cons c u from rfl]
  ring

/-- Block-diagonal chains. -/
def dchain {κ₁ κ₂ : Type} {k : ℕ} (X₁ : Fin k → α → Matrix κ₁ κ₁ ℂ)
    (X₂ : Fin k → α → Matrix κ₂ κ₂ ℂ) : Fin k → α → Matrix (κ₁ ⊕ κ₂) (κ₁ ⊕ κ₂) ℂ :=
  fun l c => Matrix.fromBlocks (X₁ l c) 0 0 (X₂ l c)

lemma rprod_fromBlocks {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂]
    [DecidableEq κ₂] : ∀ (k : ℕ) (f₁ : Fin k → Matrix κ₁ κ₁ ℂ) (f₂ : Fin k → Matrix κ₂ κ₂ ℂ),
    rprod k (fun l => Matrix.fromBlocks (f₁ l) 0 0 (f₂ l)) =
      Matrix.fromBlocks (rprod k f₁) 0 0 (rprod k f₂)
  | 0, _, _ => by simp
  | k + 1, f₁, f₂ => by
    rw [rprod_succ, rprod_succ, rprod_succ, rprod_fromBlocks k, Matrix.fromBlocks_multiply]
    simp

lemma sV_dchain {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {κ₁ κ₂ : Type} [Fintype κ₁]
    [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (Φ : (Fin k → α) → W →ₗ[ℂ] ℂ)
    (X₁ : Fin k → α → Matrix κ₁ κ₁ ℂ) (X₂ : Fin k → α → Matrix κ₂ κ₂ ℂ) (h₁ : κ₁ → W)
    (h₂ : κ₂ → W) :
    sV Φ (dchain X₁ X₂) (Sum.elim h₁ h₂) = Sum.elim (sV Φ X₁ h₁) (sV Φ X₂ h₂) := by
  funext a
  cases a with
  | inl a => simp [sV, dchain, rprod_fromBlocks, Fintype.sum_sum_type]
  | inr a => simp [sV, dchain, rprod_fromBlocks, Fintype.sum_sum_type]

lemma Yh_diag {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (Y₁ : α → Matrix κ₁ κ₁ ℂ)
    (Y₂ : α → Matrix κ₂ κ₂ ℂ) (h₁ : κ₁ → H) (h₂ : κ₂ → H) :
    Yh (fun c => Matrix.fromBlocks (Y₁ c) 0 0 (Y₂ c)) (Sum.elim h₁ h₂) =
      Sum.elim (Yh Y₁ h₁) (Yh Y₂ h₂) := by
  funext a
  cases a with
  | inl a => ext c; simp [Yh, Fintype.sum_sum_type]
  | inr a => ext c; simp [Yh, Fintype.sum_sum_type]

lemma Gq_zero {κ : Type} [Fintype κ] (z : VS α H) : Gq (fun _ : κ => (0 : VS α H)) z = 0 := by
  simp [Gq]

lemma Gq_smul {κ : Type} [Fintype κ] (c : ℂ) (u : κ → VS α H) (z : VS α H) :
    Gq (fun a => c • u a) z = ‖c‖ ^ 2 * Gq u z := by
  simp only [Gq, inner_smul_left, norm_mul, Complex.norm_conj, mul_pow, Finset.mul_sum]

lemma Gq_elim {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (u₁ : κ₁ → VS α H) (u₂ : κ₂ → VS α H)
    (z : VS α H) : Gq (Sum.elim u₁ u₂) z = Gq u₁ z + Gq u₂ z := by
  simp [Gq, Fintype.sum_sum_type]

lemma Yh_zero_left {κ : Type} [Fintype κ] (h : κ → H) :
    Yh (fun _ : α => (0 : Matrix κ κ ℂ)) h = fun _ => 0 := by
  funext a; ext c; simp [Yh]

lemma Yh_smul {κ : Type} [Fintype κ] (Y : α → Matrix κ κ ℂ) (c : ℂ) (h : κ → H) :
    Yh Y (fun b => c • h b) = fun a => c • Yh Y h a := by
  funext a; ext x; simp [Yh, Finset.smul_sum, smul_smul, mul_comm]

lemma sV_smul {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {κ : Type} [Fintype κ]
    [DecidableEq κ] (Φ : (Fin k → α) → W →ₗ[ℂ] ℂ) (X : Fin k → α → Matrix κ κ ℂ) (c : ℂ)
    (v : κ → W) : sV Φ X (fun b => c • v b) = fun a => c * sV Φ X v a := by
  funext a
  simp only [sV, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma sV_zero {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {κ : Type} [Fintype κ]
    [DecidableEq κ] (Φ : (Fin k → α) → W →ₗ[ℂ] ℂ) (X : Fin k → α → Matrix κ κ ℂ) :
    sV Φ X (fun _ => (0 : W)) = fun _ => 0 := by
  funext a; simp [sV]

lemma inner_single_left' (c : α) (x : H) (z : VS α H) :
    ⟪PiLp.single 2 c x, z⟫_ℂ = ⟪x, z c⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma rprod_unit : ∀ (k : ℕ) (g : Fin k → Matrix Unit Unit ℂ),
    rprod k g () () = ∏ l, g l () ()
  | 0, _ => by simp
  | k + 1, g => by
    rw [rprod_succ, Matrix.mul_apply, Fintype.sum_unique, rprod_unit k, Fin.prod_univ_succ]
    simp only [PUnit.default_eq_unit]
    ring

variable (N : Fin (m + 1) → NormFn α) (Ψ : (Fin (m + 1) → α) → H →ₗ[ℂ] ℂ)

/-- The data defining the sublinear functional. -/
def Adata (S : VS α H →L[ℂ] VS α H) : Set ℝ :=
  {r | ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Y : α → Matrix κ κ ℂ) (h : κ → H)
    (X : Fin m → α → Matrix κ κ ℂ) (v : κ → VS α H), N 0 κ Y ≤ 1 ∧
    (∀ l, N l.succ κ (X l) ≤ 1) ∧ (∀ z, Complex.re ⟪z, S z⟫_ℂ ≤ Gq (Yh Y h) z - Gq v z) ∧
    r = ∑ b, ‖h b‖ ^ 2 - ∑ a, ‖sV (Ψt Ψ) X v a‖ ^ 2}

lemma key (hN : ∀ l, NAx (N l)) (hΨ : HC N Ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (Y : α → Matrix κ κ ℂ) (h : κ → H) (X : Fin m → α → Matrix κ κ ℂ) (v : κ → VS α H)
    (hY : N 0 κ Y ≤ 1) (hX : ∀ l, N l.succ κ (X l) ≤ 1) (hv : ∀ z, Gq v z ≤ Gq (Yh Y h) z) :
    ∑ a, ‖sV (Ψt Ψ) X v a‖ ^ 2 ≤ ∑ b, ‖h b‖ ^ 2 := by
  obtain ⟨β, hβ, hvβ⟩ := douglas (Yh Y h) v (fun z => hv z)
  have hv' : v = Yh (fun c => β * Y c) h := by
    funext d
    rw [hvβ d]
    ext c
    simp only [Yh, PiLp.toLp_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
  rw [hv', ← sV_cons]
  apply hΨ
  intro l
  refine Fin.cases ?_ (fun l => ?_) l
  · exact ((hN 0).mul κ β Y hβ).trans hY
  · simpa using hX l

lemma Adata_nonempty (hN : ∀ l, NAx (N l)) (S : VS α H →L[ℂ] VS α H) :
    (Adata N Ψ S).Nonempty := by
  classical
  let d := Module.finrank ℂ H
  let bH := stdOrthonormalBasis ℂ H
  let D : α → Matrix (α × Fin d) (α × Fin d) ℂ :=
    fun c => Matrix.diagonal (fun q => if q.1 = c then 1 else 0)
  have hD0 := (hN 0).nonneg (α × Fin d) D
  set t : ℝ := 1 / (N 0 (α × Fin d) D + 1) with ht_def
  have ht : 0 < t := by positivity
  set ρ : ℝ := Real.sqrt ‖S‖ with hρ
  let Y : α → Matrix (α × Fin d) (α × Fin d) ℂ := fun c => (t : ℂ) • D c
  let h : α × Fin d → H := fun q => ((ρ / t : ℝ) : ℂ) • bH q.2
  refine ⟨_, α × Fin d, inferInstance, inferInstance, Y, h, fun _ _ => 0, fun _ => 0, ?_,
    fun l => (hN l.succ).zero_le_one _, fun z => ?_, rfl⟩
  · calc N 0 (α × Fin d) Y ≤ ‖(t : ℂ)‖ * N 0 (α × Fin d) D := (hN 0).smul _ t D
      _ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg ht.le, ht_def, div_mul_eq_mul_div, one_mul,
          div_le_one (by linarith)]
        linarith
  · have hY : ∀ q, Yh Y h q = PiLp.single 2 q.1 ((ρ : ℂ) • bH q.2) := by
      intro q
      ext c
      simp only [Yh, PiLp.toLp_apply]
      rw [Finset.sum_eq_single q (fun q' _ hq' => by
        simp [Y, D, Matrix.diagonal_apply, Ne.symm hq']) (by simp)]
      simp only [Y, D, h, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
        PiLp.single_apply, smul_smul]
      by_cases hc : q.1 = c
      · subst hc
        simp only [if_true, mul_one]
        congr 1
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
        push_cast
        field_simp
      · simp [hc, Ne.symm hc]
    have hG : Gq (Yh Y h) z = ρ ^ 2 * ‖z‖ ^ 2 := by
      simp only [Gq, hY, inner_single_left', inner_smul_left, norm_mul, mul_pow,
        Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ ρ from Real.sqrt_nonneg _)]
      rw [Fintype.sum_prod_type, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      dsimp only
      rw [← Finset.mul_sum, OrthonormalBasis.sum_sq_norm_inner_right]
    rw [hG, Gq_zero, sub_zero, hρ, Real.sq_sqrt (norm_nonneg _)]
    calc Complex.re ⟪z, S z⟫_ℂ ≤ ‖⟪z, S z⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖z‖ * ‖S z‖ := norm_inner_le_norm _ _
      _ ≤ ‖z‖ * (‖S‖ * ‖z‖) := by gcongr; exact S.le_opNorm z
      _ = ‖S‖ * ‖z‖ ^ 2 := by ring

lemma Adata_add (hN : ∀ l, NAx (N l)) {S T : VS α H →L[ℂ] VS α H} {a b : ℝ}
    (ha : a ∈ Adata N Ψ S) (hb : b ∈ Adata N Ψ T) : a + b ∈ Adata N Ψ (S + T) := by
  obtain ⟨κ₁, _, _, Y₁, h₁, X₁, v₁, hY₁, hX₁, hS₁, rfl⟩ := ha
  obtain ⟨κ₂, _, _, Y₂, h₂, X₂, v₂, hY₂, hX₂, hS₂, rfl⟩ := hb
  refine ⟨κ₁ ⊕ κ₂, inferInstance, inferInstance, fun c => Matrix.fromBlocks (Y₁ c) 0 0 (Y₂ c),
    Sum.elim h₁ h₂, dchain X₁ X₂, Sum.elim v₁ v₂, ?_, ?_, fun z => ?_, ?_⟩
  · exact ((hN 0).diag κ₁ κ₂ Y₁ Y₂).trans (max_le hY₁ hY₂)
  · intro l
    exact ((hN l.succ).diag κ₁ κ₂ (X₁ l) (X₂ l)).trans (max_le (hX₁ l) (hX₂ l))
  · rw [Yh_diag, Gq_elim, Gq_elim, _root_.add_apply, inner_add_right,
      Complex.add_re]
    linarith [hS₁ z, hS₂ z]
  · rw [sV_dchain]
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    ring

lemma Adata_nonneg (hN : ∀ l, NAx (N l)) (hΨ : HC N Ψ) {a : ℝ} (ha : a ∈ Adata N Ψ 0) :
    0 ≤ a := by
  obtain ⟨κ, _, _, Y, h, X, v, hY, hX, hS, rfl⟩ := ha
  have := key N Ψ hN hΨ Y h X v hY hX (fun z => by
    have := hS z
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, Complex.zero_re] at this
    linarith)
  linarith

lemma Adata_scale {S : VS α H →L[ℂ] VS α H} {a : ℝ} (ha : a ∈ Adata N Ψ S) {s : ℝ}
    (hs : 0 < s) : s ^ 2 * a ∈ Adata N Ψ ((s ^ 2 : ℝ) • S) := by
  obtain ⟨κ, _, _, Y, h, X, v, hY, hX, hS, rfl⟩ := ha
  refine ⟨κ, inferInstance, inferInstance, Y, fun b => (s : ℂ) • h b, X, fun a => (s : ℂ) • v a,
    hY, hX, fun z => ?_, ?_⟩
  · rw [Yh_smul, Gq_smul, Gq_smul]
    have h1 : ((s ^ 2 : ℝ) • S) z = ((s ^ 2 : ℝ) : ℂ) • S z := by
      rw [_root_.smul_apply]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
    rw [h1, inner_smul_right]
    have h2 := hS z
    simp only [Complex.re_ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    nlinarith [sq_nonneg s]
  · rw [sV_smul]
    simp only [norm_smul, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hs.le,
      ← Finset.mul_sum]
    ring

lemma Adata_empty {S : VS α H →L[ℂ] VS α H} (hN : ∀ l, NAx (N l))
    (hS : ∀ z, Complex.re ⟪z, S z⟫_ℂ ≤ 0) : (0 : ℝ) ∈ Adata N Ψ S := by
  refine ⟨PEmpty, inferInstance, inferInstance, fun _ => 0, PEmpty.elim, fun _ _ => 0,
    PEmpty.elim, (hN 0).zero_le_one PEmpty, fun l => (hN l.succ).zero_le_one PEmpty,
    fun z => ?_, ?_⟩
  · simpa [Gq] using hS z
  · simp

lemma Adata_upper (hN : ∀ l, NAx (N l)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (Y : α → Matrix κ κ ℂ) (h : κ → H) (hY : N 0 κ Y ≤ 1) :
    ∑ b, ‖h b‖ ^ 2 ∈ Adata N Ψ (Gop (Yh Y h)) := by
  refine ⟨κ, inferInstance, inferInstance, Y, h, fun _ _ => 0, fun _ => 0, hY,
    fun l => (hN l.succ).zero_le_one κ, fun z => ?_, ?_⟩
  · rw [re_inner_Gop, Gq_zero, sub_zero]
  · rw [sV_zero]; simp

lemma Adata_lower (hN : ∀ l, NAx (N l)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (X : Fin m → α → Matrix κ κ ℂ) (v : κ → VS α H) (hX : ∀ l, N l.succ κ (X l) ≤ 1) :
    -∑ a, ‖sV (Ψt Ψ) X v a‖ ^ 2 ∈ Adata N Ψ (-Gop v) := by
  refine ⟨κ, inferInstance, inferInstance, fun _ => 0, fun _ => 0, X, v,
    (hN 0).zero_le_one κ, hX, fun z => ?_, ?_⟩
  · rw [Yh_zero_left, Gq_zero, _root_.neg_apply, inner_neg_right, Complex.neg_re, re_inner_Gop]
    simp
  · simp

/-- Hahn–Banach. -/
lemma exists_ell (hN : ∀ l, NAx (N l)) (hΨ : HC N Ψ) :
    ∃ ℓ : (VS α H →L[ℂ] VS α H) →ₗ[ℝ] ℝ,
      (∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Y : α → Matrix κ κ ℂ) (h : κ → H),
        N 0 κ Y ≤ 1 → ℓ (Gop (Yh Y h)) ≤ ∑ b, ‖h b‖ ^ 2) ∧
      (∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Fin m → α → Matrix κ κ ℂ)
        (v : κ → VS α H), (∀ l, N l.succ κ (X l) ≤ 1) →
          ∑ a, ‖sV (Ψt Ψ) X v a‖ ^ 2 ≤ ℓ (Gop v)) ∧
      (∀ z, ℓ ((Complex.I : ℂ) • rankOne ℂ z z) = 0) := by
  classical
  let p : (VS α H →L[ℂ] VS α H) → ℝ := fun S => sInf (Adata N Ψ S)
  have hbdd : ∀ S, BddBelow (Adata N Ψ S) := by
    intro S
    obtain ⟨b, hb⟩ := Adata_nonempty N Ψ hN (-S)
    refine ⟨-b, fun a ha => ?_⟩
    have := Adata_nonneg N Ψ hN hΨ (by simpa using Adata_add N Ψ hN ha hb)
    linarith
  have hle : ∀ S a, a ∈ Adata N Ψ S → p S ≤ a := fun S a ha => csInf_le (hbdd S) ha
  have hhom : ∀ c : ℝ, 0 < c → ∀ S, p (c • S) = c * p S := by
    intro c hc S
    have hset : Adata N Ψ (c • S) = c • Adata N Ψ S := by
      ext x
      constructor
      · intro hx
        refine ⟨c⁻¹ * x, ?_, by simp [smul_eq_mul]; field_simp⟩
        have := Adata_scale N Ψ hx (s := Real.sqrt c⁻¹) (by positivity)
        rwa [Real.sq_sqrt (by positivity), smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      · rintro ⟨y, hy, rfl⟩
        have := Adata_scale N Ψ hy (s := Real.sqrt c) (by positivity)
        rwa [Real.sq_sqrt hc.le] at this
    show sInf _ = c * sInf _
    rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  have hadd : ∀ S T, p (S + T) ≤ p S + p T := by
    intro S T
    have h1 : ∀ a ∈ Adata N Ψ S, p (S + T) - a ≤ p T := by
      intro a ha
      refine le_csInf (Adata_nonempty N Ψ hN T) fun b hb => ?_
      have := hle _ _ (Adata_add N Ψ hN ha hb)
      linarith
    have h2 : p (S + T) - p T ≤ p S := by
      refine le_csInf (Adata_nonempty N Ψ hN S) fun a ha => ?_
      have := h1 a ha
      linarith
    linarith
  have hp0 : p 0 = 0 := by
    have h2 := hhom 2 (by norm_num) 0
    have h3 : p ((2 : ℝ) • (0 : VS α H →L[ℂ] VS α H)) = p 0 := by
      congr 1
      ext x
      simp
    linarith
  obtain ⟨ℓ, -, hℓ⟩ := exists_extension_of_le_sublinear
    (⟨⊥, 0⟩ : (VS α H →L[ℂ] VS α H) →ₗ.[ℝ] ℝ) p hhom hadd (by
      rintro ⟨x, hx⟩
      rw [Submodule.mem_bot] at hx
      subst hx
      simp [hp0])
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro κ _ _ Y h hY
    exact (hℓ _).trans (hle _ _ (Adata_upper N Ψ hN Y h hY))
  · intro κ _ _ X v hX
    have h1 := (hℓ _).trans (hle _ _ (Adata_lower N Ψ hN X v hX))
    rw [map_neg] at h1
    linarith
  · intro z
    have hz : ∀ z', Complex.re ⟪z', ((Complex.I : ℂ) • rankOne ℂ z z) z'⟫_ℂ = 0 := by
      intro z'
      simp only [_root_.smul_apply, rankOne_apply, inner_smul_right]
      rw [← inner_conj_symm z z', Complex.conj_mul']
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im]
      norm_cast
      simp
    have h1 := (hℓ _).trans (hle _ _ (Adata_empty N Ψ hN (S := (Complex.I : ℂ) • rankOne ℂ z z)
      (fun z' => (hz z').le)))
    have h2 := (hℓ _).trans (hle _ _ (Adata_empty N Ψ hN
      (S := -((Complex.I : ℂ) • rankOne ℂ z z)) (fun z' => by
        simp only [_root_.neg_apply, inner_neg_right, Complex.neg_re, hz z',
          neg_zero, le_refl])))
    rw [map_neg] at h2
    linarith

/-- The kernel condition for the factorization. -/
lemma kernel (hN : ∀ l, NAx (N l)) (ℓ : (VS α H →L[ℂ] VS α H) →ₗ[ℝ] ℝ)
    (hℓ : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Fin m → α → Matrix κ κ ℂ)
        (v : κ → VS α H), (∀ l, N l.succ κ (X l) ≤ 1) →
          ∑ a, ‖sV (Ψt Ψ) X v a‖ ^ 2 ≤ ℓ (Gop v))
    (x : VS α H) (hx : ℓ (rankOne ℂ x x) = 0) (u : Fin m → α) : Ψt Ψ u x = 0 := by
  classical
  let ind : Fin m → α → Matrix Unit Unit ℂ := fun l c =>
    Matrix.of fun _ _ => if c = u l then (1 : ℂ) else 0
  let t : Fin m → ℝ := fun l => 1 / (N l.succ Unit (ind l) + 1)
  have ht : ∀ l, 0 < t l := fun l => by
    have := (hN l.succ).nonneg Unit (ind l)
    positivity
  let X : Fin m → α → Matrix Unit Unit ℂ := fun l c => (t l : ℂ) • ind l c
  have hX : ∀ l, N l.succ Unit (X l) ≤ 1 := by
    intro l
    have h0 := (hN l.succ).nonneg Unit (ind l)
    calc N l.succ Unit (X l) ≤ ‖(t l : ℂ)‖ * N l.succ Unit (ind l) := (hN l.succ).smul _ _ _
      _ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (ht l).le]
        simp only [t]
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
        linarith
  have h1 := hℓ Unit X (fun _ => x) hX
  have hG : Gop (fun _ : Unit => x) = rankOne ℂ x x := by simp [Gop]
  rw [hG, hx, Fintype.sum_unique] at h1
  have h2 : sV (Ψt Ψ) X (fun _ => x) default = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm h1 (by positivity))
    exact norm_eq_zero.mp this
  have h3 : sV (Ψt Ψ) X (fun _ => x) default = (∏ l, (t l : ℂ)) * Ψt Ψ u x := by
    simp only [sV, Fintype.sum_unique, PUnit.default_eq_unit, rprod_unit]
    have : ∀ w : Fin m → α, (∏ l, X l (w l) () ()) = if w = u then ∏ l, (t l : ℂ) else 0 := by
      intro w
      simp only [X, ind, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero]
      rw [Finset.prod_ite_zero]
      simp [funext_iff]
    simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h3] at h2
  have hne : (∏ l, (t l : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => by exact_mod_cast (ht l).ne'
  exact (mul_eq_zero.mp h2).resolve_left hne

end Cut

/-- One cut. -/
theorem step {m : ℕ} (N : Fin (m + 1) → NormFn α) (hN : ∀ l, NAx (N l))
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (Ψ : (Fin (m + 1) → α) → H →ₗ[ℂ] ℂ) (hΨ : HC N Ψ) :
    ∃ (r : ℕ) (φ₀ : α → H →L[ℂ] E r) (Ψ' : (Fin m → α) → E r →ₗ[ℂ] ℂ),
      CCN (N 0) φ₀ ∧ HC (fun l => N l.succ) Ψ' ∧
      ∀ c u h, Ψ (Fin.cons c u) h = Ψ' u (φ₀ c h) := by
  classical
  obtain ⟨ℓ, hup, hlow, hI⟩ := exists_ell N Ψ hN hΨ
  have hpos : ∀ z, 0 ≤ ℓ (rankOne ℂ z z) := by
    intro z
    have h1 := hlow Unit (fun _ _ => 0) (fun _ => z) (fun l => NAx.zero_le_one (hN l.succ) Unit)
    have h2 : Gop (fun _ : Unit => z) = rankOne ℂ z z := by simp [Gop]
    rw [h2] at h1
    exact le_trans (Finset.sum_nonneg fun _ _ => by positivity) h1
  obtain ⟨r, Γ, hΓ⟩ := exists_Gamma ℓ hpos hI
  have hΓsum : ∀ {κ : Type} [Fintype κ] (u : κ → VS α H),
      ∑ a, ‖Γ (u a)‖ ^ 2 = ℓ (Gop u) := by
    intro κ _ u
    simp only [Gop, map_sum, hΓ]
  -- the last factor
  let sing : α → H →ₗ[ℂ] VS α H := fun c =>
    (WithLp.linearEquiv 2 ℂ (α → H)).symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ => H) c
  let φ₀ : α → H →L[ℂ] E r := fun c => LinearMap.toContinuousLinearMap (Γ ∘ₗ sing c)
  have hsing : ∀ {κ : Type} [Fintype κ] (Y : α → Matrix κ κ ℂ) (ζ : κ → H) (a : κ),
      ∑ c, ∑ b, Y c a b • φ₀ c (ζ b) = Γ (Yh Y ζ a) := by
    intro κ _ Y ζ a
    have hY : Yh Y ζ a = ∑ c, ∑ b, Y c a b • sing c (ζ b) := by
      ext c'
      simp [Yh, sing, Pi.single_apply]
    rw [hY]
    simp [φ₀, map_sum, map_smul]
  -- the remainder
  let B : VS α H →ₗ[ℂ] ((Fin m → α) → ℂ) := LinearMap.pi fun u => Ψt Ψ u
  obtain ⟨T, hTA, hT⟩ := factor Γ B (fun x hx => by
    funext u
    exact kernel N Ψ hN ℓ hlow x (by rw [← hΓ x, hx, norm_zero]; ring) u)
  let Ψ' : (Fin m → α) → E r →ₗ[ℂ] ℂ := fun u => LinearMap.proj u ∘ₗ T
  refine ⟨r, φ₀, Ψ', ?_, ?_, ?_⟩
  · intro κ _ Y hY ζ
    simp_rw [hsing]
    rw [hΓsum]
    exact hup κ Y ζ hY
  · intro κ _ _ X z hX
    choose x hx hxn using fun b => hT (z b)
    have hs : sV Ψ' X z = sV (Ψt Ψ) X x := by
      funext a
      simp only [sV, Ψ', LinearMap.comp_apply, hx]
      rfl
    rw [hs]
    calc ∑ a, ‖sV (Ψt Ψ) X x a‖ ^ 2 ≤ ℓ (Gop x) := hlow κ X x hX
      _ = ∑ b, ‖Γ (x b)‖ ^ 2 := (hΓsum x).symm
      _ ≤ ∑ b, ‖z b‖ ^ 2 := by
        gcongr with b
        exact hxn b
  · intro c u h
    have h1 : Ψt Ψ u (sing c h) = Ψ (Fin.cons c u) h := by
      rw [Ψt_apply, Finset.sum_eq_single c (fun b _ hb => by simp [sing, hb]) (by simp)]
      simp [sing]
    rw [← h1]
    show Ψt Ψ u (sing c h) = T (Γ (sing c h)) u
    rw [hTA]
    rfl

end StrongConv.S9.Pisier.PartD
end
end

section
noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix

namespace StrongConv.S9.Pisier.PartD

set_option linter.deprecated false

variable {α : Type} [Fintype α] [DecidableEq α]

/-- An isometry into a large enough Euclidean space. -/
lemma exists_isometry (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (R : ℕ) (hR : Module.finrank ℂ H ≤ R) :
    Nonempty (H →ₗᵢ[ℂ] E R) := by
  classical
  set d := Module.finrank ℂ H
  let b := stdOrthonormalBasis ℂ H
  let P : E d →ₗ[ℂ] E R :=
    { toFun := fun v => WithLp.toLp 2 (fun i : Fin R => if h : i.val < d then v ⟨i, h⟩ else 0)
      map_add' := fun x y => by ext i; by_cases h : i.val < d <;> simp [h]
      map_smul' := fun c x => by ext i; by_cases h : i.val < d <;> simp [h] }
  have hP : ∀ v, ‖P v‖ = ‖v‖ := by
    intro v
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hR) (Fin.castLE_injective hR) _ _ ?_ ?_
    · intro i hi
      have : ¬ i.val < d := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [P, this]
    · intro j
      simp [P, j.isLt]
  let J0 : E d →ₗᵢ[ℂ] E R := { toLinearMap := P, norm_map' := hP }
  exact ⟨J0.comp b.repr.toLinearIsometry⟩

/-- Conjugating by an isometry and a contraction preserves `CCN`. -/
lemma CCN_conj (N : NormFn α) {H₁ H₂ K₁ K₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [NormedAddCommGroup K₁]
    [InnerProductSpace ℂ K₁] [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂]
    (φ : α → H₁ →L[ℂ] H₂) (hφ : CCN N φ) (A : H₂ →L[ℂ] K₂) (hA : ∀ x, ‖A x‖ = ‖x‖)
    (B : K₁ →L[ℂ] H₁) (hB : ∀ x, ‖B x‖ ≤ ‖x‖) :
    CCN N (fun c => A.comp ((φ c).comp B)) := by
  intro κ _ X hX ζ
  have h1 : ∀ a, ∑ c, ∑ b, X c a b • (A.comp ((φ c).comp B)) (ζ b) =
      A (∑ c, ∑ b, X c a b • φ c (B (ζ b))) := by
    intro a
    simp [map_sum, map_smul]
  simp_rw [h1, hA]
  refine (hφ κ X hX (fun b => B (ζ b))).trans ?_
  gcongr with b
  exact hB _

/-- The base case. -/
lemma base (N : Fin 0 → NormFn α)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (Ψ : (Fin 0 → α) → H →ₗ[ℂ] ℂ) (hΨ : HC N Ψ) :
    ∃ η : H, ‖η‖ ≤ 1 ∧ ∀ w h, Ψ w h = ⟪η, h⟫_ℂ := by
  classical
  let w₀ : Fin 0 → α := Fin.elim0
  have hw : ∀ w : Fin 0 → α, w = w₀ := fun w => funext fun l => l.elim0
  have hb : ∀ x : H, ‖Ψ w₀ x‖ ≤ ‖x‖ := by
    intro x
    have h := hΨ Unit (fun l => l.elim0) (fun _ => x) (fun l => l.elim0)
    have hs : sV Ψ (fun l => l.elim0) (fun _ : Unit => x) () = Ψ w₀ x := by
      simp only [sV, Fintype.sum_unique, rprod_zero]
      rw [hw default]
      simp
    rw [Fintype.sum_unique, Fintype.sum_unique] at h
    rw [← hs]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa using h)
  let f : StrongDual ℂ H := LinearMap.toContinuousLinearMap (Ψ w₀)
  refine ⟨(InnerProductSpace.toDual ℂ H).symm f, ?_, fun w h => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa [f] using hb x
  · rw [InnerProductSpace.toDual_symm_apply, hw w]
    rfl

theorem peel (m : ℕ) : ∀ (N : Fin m → NormFn α), (∀ l, NAx (N l)) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (Ψ : (Fin m → α) → H →ₗ[ℂ] ℂ), HC N Ψ →
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∃ (φ : Fin m → α → E R →L[ℂ] E R) (η : E R) (J : H →ₗᵢ[ℂ] E R),
      (∀ l, CCN (N l) (φ l)) ∧ ‖η‖ ≤ 1 ∧
      ∀ w h, Ψ w h = ⟪η, rprod m (fun l => φ l (w l)) (J h)⟫_ℂ := by
  induction m with
  | zero =>
    intro N _ H _ _ _ Ψ hΨ
    obtain ⟨η, hη, hrep⟩ := base N H Ψ hΨ
    refine ⟨Module.finrank ℂ H, fun R hR => ?_⟩
    obtain ⟨J⟩ := exists_isometry H R hR
    refine ⟨fun l => l.elim0, J η, J, fun l => l.elim0, by simpa using hη, fun w h => ?_⟩
    rw [hrep w h]
    simp
  | succ m ih =>
    intro N hN H _ _ _ Ψ hΨ
    obtain ⟨r, φ₀, Ψ', hφ₀, hΨ', hrep⟩ := step N hN H Ψ hΨ
    obtain ⟨R₀, hR₀⟩ := ih (fun l => N l.succ) (fun l => hN l.succ) (E r) Ψ' hΨ'
    refine ⟨max R₀ (Module.finrank ℂ H), fun R hR => ?_⟩
    obtain ⟨φ', η, J', hφ', hη, hrep'⟩ := hR₀ R (le_of_max_le_left hR)
    obtain ⟨J⟩ := exists_isometry H R (le_of_max_le_right hR)
    have hJJ : ∀ x, (J.toContinuousLinearMap.adjoint) (J x) = x := by
      intro x
      apply ext_inner_right ℂ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp
    let φ : Fin (m + 1) → α → E R →L[ℂ] E R :=
      Fin.cons (fun c => J'.toContinuousLinearMap.comp
        ((φ₀ c).comp J.toContinuousLinearMap.adjoint)) φ'
    refine ⟨φ, η, J, ?_, hη, ?_⟩
    · intro l
      refine Fin.cases ?_ (fun l => ?_) l
      · exact CCN_conj (N 0) φ₀ hφ₀ _ (fun x => J'.norm_map x) _ (fun x => by
          calc ‖J.toContinuousLinearMap.adjoint x‖
              ≤ ‖J.toContinuousLinearMap.adjoint‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖x‖ := by
                gcongr
                rw [ContinuousLinearMap.adjoint.norm_map]
                exact J.norm_toContinuousLinearMap_le
            _ = ‖x‖ := one_mul _)
      · exact hφ' l
    · intro w h
      rw [← Fin.cons_self_tail w, hrep (w 0) (Fin.tail w) h, hrep' (Fin.tail w)]
      simp only [rprod_succ, φ, Fin.cons_zero, Fin.cons_succ, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, hJJ]

end StrongConv.S9.Pisier.PartD
end
end

section
/-!
# PartD, slot norms given by amplifications of letter operators

`ampN e'` is the slot norm `κ, X ↦ ‖∑_c X c ⊗ e' c‖` on `PiLp 2 (κ → L)`; it satisfies `NAx`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix

namespace StrongConv.S9.Pisier.PartD

set_option synthInstance.maxHeartbeats 400000

variable {α : Type} [Fintype α] [DecidableEq α]

section Amp

variable {L₁ L₂ : Type} [NormedAddCommGroup L₁] [InnerProductSpace ℂ L₁] [NormedAddCommGroup L₂]
  [InnerProductSpace ℂ L₂]

/-- The amplification `∑_c X c ⊗ e' c` for a general finite index type. -/
def ampG (e' : α → L₁ →L[ℂ] L₂) {κ : Type} [Fintype κ] (X : α → Matrix κ κ ℂ) :
    PiLp 2 (fun _ : κ => L₁) →L[ℂ] PiLp 2 (fun _ : κ => L₂) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => L₂)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a => ∑ c, ∑ b, X c a b • (e' c).comp (PiLp.proj 2 (fun _ : κ => L₁) b))

lemma ampG_apply (e' : α → L₁ →L[ℂ] L₂) {κ : Type} [Fintype κ] (X : α → Matrix κ κ ℂ)
    (ζ : PiLp 2 (fun _ : κ => L₁)) (a : κ) :
    ampG e' X ζ a = ∑ c, ∑ b, X c a b • e' c (ζ b) := by
  simp [ampG]

lemma ampG_sum_le (e' : α → L₁ →L[ℂ] L₂) {κ : Type} [Fintype κ] (X : α → Matrix κ κ ℂ)
    (ζ : κ → L₁) :
    ∑ a, ‖∑ c, ∑ b, X c a b • e' c (ζ b)‖ ^ 2 ≤ ‖ampG e' X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by
  have h := (ampG e' X).le_opNorm (WithLp.toLp 2 ζ)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at h2
  simpa [ampG_apply] using h2

lemma ampG_le_of (e' : α → L₁ →L[ℂ] L₂) {κ : Type} [Fintype κ] (X : α → Matrix κ κ ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (h : ∀ ζ : κ → L₁, ∑ a, ‖∑ c, ∑ b, X c a b • e' c (ζ b)‖ ^ 2 ≤ C ^ 2 * ∑ b, ‖ζ b‖ ^ 2) :
    ‖ampG e' X‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun ζ => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  simpa [ampG_apply] using h ζ

/-- A scalar contraction amplified to vectors is a contraction. -/
lemma amp1 {κ : Type} [Fintype κ] (β : Matrix κ κ ℂ)
    (hβ : ∀ x : κ → ℂ, ∑ a, ‖(β *ᵥ x) a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2) (ζ : κ → L₂) :
    ∑ a, ‖∑ b, β a b • ζ b‖ ^ 2 ≤ ∑ b, ‖ζ b‖ ^ 2 := by
  classical
  let W : Submodule ℂ L₂ := Submodule.span ℂ (Set.range ζ)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ζ)
  let bW := stdOrthonormalBasis ℂ W
  let ζ' : κ → W := fun b => ⟨ζ b, Submodule.subset_span ⟨b, rfl⟩⟩
  have hn : ∀ w : W, ‖(w : L₂)‖ ^ 2 = ∑ k, ‖⟪bW k, w⟫_ℂ‖ ^ 2 := fun w => by
    rw [show ‖(w : L₂)‖ = ‖w‖ from rfl, OrthonormalBasis.sum_sq_norm_inner_right]
  have h1 : ∀ a, ∑ b, β a b • ζ b = ((∑ b, β a b • ζ' b : W) : L₂) := by
    intro a; simp [ζ']
  calc ∑ a, ‖∑ b, β a b • ζ b‖ ^ 2
      = ∑ a, ∑ k, ‖(β *ᵥ fun b => ⟪bW k, ζ' b⟫_ℂ) a‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [h1, hn]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [mulVec, dotProduct, inner_sum, inner_smul_right]
    _ = ∑ k, ∑ a, ‖(β *ᵥ fun b => ⟪bW k, ζ' b⟫_ℂ) a‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ k, ∑ b, ‖⟪bW k, ζ' b⟫_ℂ‖ ^ 2 := Finset.sum_le_sum fun k _ => hβ _
    _ = ∑ b, ‖ζ b‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hn]

/-- The slot norm of a letter map. -/
def ampN (e' : α → L₁ →L[ℂ] L₂) : NormFn α := fun κ _ X => ‖ampG e' X‖

theorem ampN_NAx (e' : α → L₁ →L[ℂ] L₂) : NAx (ampN e') where
  nonneg κ _ Y := norm_nonneg (ampG e' Y)
  smul κ _ t Y := by
    have : ampG e' (fun c => t • Y c) = t • ampG e' Y := by
      ext ζ a
      simp [ampG_apply, Finset.smul_sum, smul_smul]
    show ‖ampG e' (fun c => t • Y c)‖ ≤ ‖t‖ * ‖ampG e' Y‖
    rw [this]
    exact ContinuousLinearMap.opNorm_smul_le t _
  mul κ _ β Y hβ := by
    show ‖ampG e' (fun c => β * Y c)‖ ≤ ‖ampG e' Y‖
    refine ampG_le_of e' _ _ (norm_nonneg (ampG e' Y)) fun ζ => ?_
    have h1 : ∀ a, ∑ c, ∑ b, (β * Y c) a b • e' c (ζ b) =
        ∑ d, β a d • ∑ c, ∑ b, Y c d b • e' c (ζ b) := by
      intro a
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    simp_rw [h1]
    exact (amp1 β hβ _).trans (ampG_sum_le e' Y ζ)
  diag κ₁ κ₂ _ _ Y₁ Y₂ := by
    show ‖ampG e' (fun c => Matrix.fromBlocks (Y₁ c) 0 0 (Y₂ c))‖ ≤
      max ‖ampG e' Y₁‖ ‖ampG e' Y₂‖
    refine ampG_le_of e' _ _ (le_max_of_le_left (norm_nonneg (ampG e' Y₁))) fun ζ => ?_
    have h1 := ampG_sum_le e' Y₁ (fun b => ζ (Sum.inl b))
    have h2 := ampG_sum_le e' Y₂ (fun b => ζ (Sum.inr b))
    have hm1 : ‖ampG e' Y₁‖ ^ 2 ≤ max ‖ampG e' Y₁‖ ‖ampG e' Y₂‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg (ampG e' Y₁)) (le_max_left _ _) 2
    have hm2 : ‖ampG e' Y₂‖ ^ 2 ≤ max ‖ampG e' Y₁‖ ‖ampG e' Y₂‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg (ampG e' Y₂)) (le_max_right _ _) 2
    simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, zero_add]
    calc _ ≤ ‖ampG e' Y₁‖ ^ 2 * ∑ b, ‖ζ (Sum.inl b)‖ ^ 2 +
          ‖ampG e' Y₂‖ ^ 2 * ∑ b, ‖ζ (Sum.inr b)‖ ^ 2 := add_le_add h1 h2
      _ ≤ _ := by
        rw [mul_add]
        gcongr

end Amp

end StrongConv.S9.Pisier.PartD
end
end

section
/-!
# PartD: `per_degree` (MATH.md Lemmas 2–6)

The coefficient functional of words of length `M`, framed by a column slot and a row slot, is a
Haagerup-contractive multilinear functional on `M + 2` slots over the alphabet `Fin n ⊕ ι`
(`HC_fr`, from `ChainBound`). The generic peeling theorem `peel` represents it on one
`EuclideanSpace ℂ (Fin R)`; the frame slots give `ξ` and `η`.

Internal slot order: slot `0` is the right frame (index `j`), slot `(k.castSucc).succ` carries the
letter at position `rev k`, slot `last` is the left frame (index `i`).
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Matrix InnerProductSpace

namespace StrongConv.S9.Pisier.PartD

open StrongConv.S9.Pisier

set_option synthInstance.maxHeartbeats 400000
set_option linter.deprecated false

/-! ## Reversed products -/

lemma rprod_eq_ofFn {Mo : Type*} [Monoid Mo] : ∀ (m : ℕ) (f : Fin m → Mo),
    rprod m f = (List.ofFn fun l => f (Fin.rev l)).prod
  | 0, f => by simp
  | m + 1, f => by
    rw [rprod_succ, rprod_eq_ofFn m, List.ofFn_succ', List.prod_concat]
    simp [Fin.rev_castSucc, Fin.rev_last]

lemma rprod_succ' {Mo : Type*} [Monoid Mo] (m : ℕ) (f : Fin (m + 1) → Mo) :
    rprod (m + 1) f = f (Fin.last m) * rprod m (fun l => f l.castSucc) := by
  rw [rprod_eq_ofFn, rprod_eq_ofFn, List.ofFn_succ, List.prod_cons]
  simp [Fin.rev_succ, Fin.rev_zero]

/-- Coordinates of the Blueprint amplification. -/
lemma amp_apply {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {κ : Type*} [Fintype κ]
    (ρ : κ → H₁ →L[ℂ] H₂) {k : ℕ} (X : κ → Matrix (Fin k) (Fin k) ℂ)
    (ζ : PiLp 2 (fun _ : Fin k => H₁)) (a : Fin k) :
    amp ρ X ζ a = ∑ c, ∑ b, X c a b • ρ c (ζ b) := by
  simp [amp, tOp, Pi.single_apply]


lemma sNorm_le_of {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℂ)
    (h : ∀ x : Fin n → ℂ, ∑ i, ‖(C *ᵥ x) i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2) : sNorm C ≤ 1 := by
  unfold sNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simpa [Matrix.toEuclideanLin_apply] using h x

section Frames

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- The frame space `ℂ^{1+n}`. -/
abbrev Fr (n : ℕ) := EuclideanSpace ℂ (Option (Fin n))

/-- Right frame letters: `δ_{some j} ↦ δ_none`. -/
def eR (ι : Type) (n : ℕ) : Fin n ⊕ ι → Fr n →L[ℂ] Fr n :=
  Sum.elim (fun j => rankOne ℂ (EuclideanSpace.single none 1) (EuclideanSpace.single (some j) 1))
    (fun _ => 0)

/-- Left frame letters: `δ_none ↦ δ_{some i}`. -/
def eL (ι : Type) (n : ℕ) : Fin n ⊕ ι → Fr n →L[ℂ] Fr n :=
  Sum.elim (fun i => rankOne ℂ (EuclideanSpace.single (some i) 1) (EuclideanSpace.single none 1))
    (fun _ => 0)

/-- The letters on the middle slots. -/
def eM {n : ℕ} (e : ι → L →L[ℂ] L) : Fin n ⊕ ι → L →L[ℂ] L :=
  Sum.elim (fun _ => 0) e

/-- The slot norms. -/
def Nslot (e : ι → L →L[ℂ] L) (n M : ℕ) : Fin (M + 2) → NormFn (Fin n ⊕ ι) :=
  fun k => if k = 0 then ampN (eR ι n) else if k = Fin.last (M + 1) then ampN (eL ι n)
    else ampN (eM (n := n) e)

lemma Nslot_NAx (e : ι → L →L[ℂ] L) (n M : ℕ) (k : Fin (M + 2)) : NAx (Nslot e n M k) := by
  unfold Nslot
  split_ifs
  · exact ampN_NAx _
  · exact ampN_NAx _
  · exact ampN_NAx _

/-- Encoding of a framed word. -/
def enc {n M : ℕ} (i : Fin n) (w' : Fin M → ι) (j : Fin n) : Fin (M + 2) → Fin n ⊕ ι :=
  Fin.cons (Sum.inl j) (Fin.snoc (fun k : Fin M => Sum.inr (w' (Fin.rev k))) (Sum.inl i))

lemma enc_last {n M : ℕ} (i : Fin n) (w : Fin M → ι) (j : Fin n) :
    enc i w j (Fin.last (M + 1)) = Sum.inl i := by
  rw [← Fin.succ_last]
  simp [enc]

lemma enc_mid {n M : ℕ} (i : Fin n) (w : Fin M → ι) (j : Fin n) (k : Fin M) :
    enc i w j k.castSucc.succ = Sum.inr (w (Fin.rev k)) := by
  simp [enc]

lemma enc_zero {n M : ℕ} (i : Fin n) (w : Fin M → ι) (j : Fin n) :
    enc i w j 0 = Sum.inl j := by
  simp [enc]

lemma rprod_enc {Mo : Type*} [Monoid Mo] {n M : ℕ} (g : Fin (M + 2) → Fin n ⊕ ι → Mo)
    (i : Fin n) (w : Fin M → ι) (j : Fin n) :
    rprod (M + 2) (fun l => g l (enc i w j l)) =
      g (Fin.last (M + 1)) (Sum.inl i) *
        (List.ofFn fun l => g (Fin.rev l).castSucc.succ (Sum.inr (w l))).prod *
        g 0 (Sum.inl j) := by
  rw [rprod_succ, rprod_succ', rprod_eq_ofFn]
  simp only [Fin.succ_last, enc_last, enc_mid, Fin.rev_rev, enc_zero]

lemma enc_injective {n M : ℕ} {i i' : Fin n} {w w' : Fin M → ι} {j j' : Fin n}
    (h : enc i w j = enc i' w' j') : i = i' ∧ w = w' ∧ j = j' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun h (Fin.last (M + 1))
    rw [enc_last, enc_last] at this
    exact Sum.inl_injective this
  · funext l
    have := congrFun h (Fin.rev l).castSucc.succ
    rw [enc_mid, enc_mid, Fin.rev_rev] at this
    exact Sum.inr_injective this
  · have := congrFun h 0
    rw [enc_zero, enc_zero] at this
    exact Sum.inl_injective this

/-- The framed functional. -/
def Ψfr {n : ℕ} (M : ℕ) (F : List ι → Matrix (Fin n) (Fin n) ℂ) :
    (Fin (M + 2) → Fin n ⊕ ι) → ℂ →ₗ[ℂ] ℂ :=
  fun w => (∑ i, ∑ w' : Fin M → ι, ∑ j, if w = enc i w' j then F (List.ofFn w') i j else 0) •
    LinearMap.id

lemma Ψfr_enc {n M : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (w' : Fin M → ι)
    (j : Fin n) : Ψfr M F (enc i w' j) 1 = F (List.ofFn w') i j := by
  have hiff : ∀ i₂ w₂ j₂, (enc i w' j = enc i₂ w₂ j₂) ↔ (i = i₂ ∧ w' = w₂ ∧ j = j₂) := by
    intro i₂ w₂ j₂
    constructor
    · exact enc_injective
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  simp only [Ψfr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]
  simp only [hiff, ite_and]
  simp [Finset.sum_ite_eq]

lemma sum_mul_G {n M : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (f : (Fin (M + 2) → Fin n ⊕ ι) → ℂ) :
    ∑ w, f w * (∑ i, ∑ w' : Fin M → ι, ∑ j,
      if w = enc i w' j then F (List.ofFn w') i j else 0) =
      ∑ i, ∑ w' : Fin M → ι, ∑ j, f (enc i w' j) * F (List.ofFn w') i j := by
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq']
  simp

lemma chainBound_unit (e : ι → L →L[ℂ] L) {n M : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (hF : ChainBound e F) {κ : Type} [Fintype κ] [DecidableEq κ]
    (X : Fin M → ι → Matrix κ κ ℂ)
    (hX : ∀ l (ζ : κ → L), ∑ a, ‖∑ c, ∑ b, X l c a b • e c (ζ b)‖ ^ 2 ≤ ∑ b, ‖ζ b‖ ^ 2)
    (C : Matrix (Fin n) κ ℂ) (R : Matrix κ (Fin n) ℂ)
    (hC : ∀ x : κ → ℂ, ∑ i, ‖(C *ᵥ x) i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2)
    (hR : ∀ y : Fin n → ℂ, ∑ k, ‖(R *ᵥ y) k‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2) :
    ‖∑ w : Fin M → ι, ∑ i, ∑ j,
      (C * (List.ofFn fun l => X l (w l)).prod * R) i j * F (List.ofFn w) i j‖ ≤ 1 := by
  classical
  let σ := Fintype.equivFin κ
  let K := Fintype.card κ
  let X' : Fin M → ι → Matrix (Fin K) (Fin K) ℂ := fun l c => Matrix.reindex σ σ (X l c)
  let C' : Matrix (Fin n) (Fin K) ℂ := C.submatrix id σ.symm
  let R' : Matrix (Fin K) (Fin n) ℂ := R.submatrix σ.symm id
  have hprod : ∀ w : Fin M → ι, C' * prodX X' w * R' =
      C * (List.ofFn fun l => X l (w l)).prod * R := by
    intro w
    have h1 : prodX X' w = Matrix.reindex σ σ (List.ofFn fun l => X l (w l)).prod := by
      simp only [prodX, X']
      rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ σ, map_list_prod, List.map_ofFn]
      rfl
    rw [h1, Matrix.reindex_apply]
    simp only [C', R']
    rw [← Matrix.submatrix_mul C _ id σ.symm σ.symm σ.symm.bijective,
      ← Matrix.submatrix_mul _ R id σ.symm id σ.symm.bijective]
    simp
  have hX' : ∀ l, ‖amp e (X' l)‖ ≤ 1 := by
    intro l
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ζ => ?_
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2]
    simp only [amp_apply, X', Matrix.reindex_apply, Matrix.submatrix_apply]
    calc ∑ a, ‖∑ c, ∑ b, X l c (σ.symm a) (σ.symm b) • e c (ζ b)‖ ^ 2
        = ∑ a : κ, ‖∑ c, ∑ b : κ, X l c a b • e c (ζ (σ b))‖ ^ 2 := by
          rw [← σ.sum_comp]
          refine Finset.sum_congr rfl fun a _ => ?_
          congr 2
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← σ.sum_comp]
          simp
      _ ≤ ∑ b : κ, ‖ζ (σ b)‖ ^ 2 := hX l _
      _ = ∑ b, ‖ζ b‖ ^ 2 := σ.sum_comp (fun b => ‖ζ b‖ ^ 2)
  have hC' : sNorm C' ≤ 1 := by
    refine sNorm_le_of _ fun x => ?_
    have h := hC (fun k => x (σ k))
    have h2 : ∀ i, (C' *ᵥ x) i = (C *ᵥ fun k => x (σ k)) i := by
      intro i
      simp only [C', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
      rw [← σ.sum_comp]
      simp
    simp only [h2]
    refine h.trans (le_of_eq ?_)
    exact σ.sum_comp (fun k => ‖x k‖ ^ 2)
  have hR' : sNorm R' ≤ 1 := by
    refine sNorm_le_of _ fun y => ?_
    have h := hR y
    have h2 : ∀ k, (R' *ᵥ y) k = (R *ᵥ y) (σ.symm k) := by
      intro k
      simp [R', Matrix.mulVec, dotProduct]
    simp only [h2]
    refine le_of_eq_of_le ?_ h
    exact σ.symm.sum_comp (fun k => ‖(R *ᵥ y) k‖ ^ 2)
  have := hF M K X' C' R' hX' hC' hR'
  simpa only [hprod] using this

/-- Cauchy–Schwarz for finite sums. -/
lemma cs_dot {κ : Type} [Fintype κ] (s v : κ → ℂ) :
    ‖star s ⬝ᵥ v‖ ^ 2 ≤ (∑ a, ‖s a‖ ^ 2) * ∑ a, ‖v a‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 s : EuclideanSpace ℂ κ) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

theorem HC_fr (e : ι → L →L[ℂ] L) {n : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (hF : ChainBound e F) (M : ℕ) : HC (Nslot e n M) (Ψfr M F) := by
  classical
  intro κ _ _ X h hX
  have hlast0 : Fin.last (M + 1) ≠ 0 := by simp
  have hN0 : ampN (eR ι n) κ (X 0) ≤ 1 := by simpa [Nslot] using hX 0
  have hNl : ampN (eL ι n) κ (X (Fin.last (M + 1))) ≤ 1 := by
    simpa [Nslot, hlast0] using hX (Fin.last (M + 1))
  have hNm : ∀ l : Fin M, ampN (eM (n := n) e) κ (X (Fin.rev l).castSucc.succ) ≤ 1 := by
    intro l
    have h1 : (Fin.rev l).castSucc.succ ≠ 0 := Fin.succ_ne_zero _
    have h2 : (Fin.rev l).castSucc.succ ≠ Fin.last (M + 1) := by
      rw [← Fin.succ_last]
      exact fun h => Fin.castSucc_ne_last _ (Fin.succ_injective _ h)
    simpa [Nslot, h1, h2] using hX (Fin.rev l).castSucc.succ
  let Xl : Fin n → Matrix κ κ ℂ := fun i => X (Fin.last (M + 1)) (Sum.inl i)
  let X0 : Fin n → Matrix κ κ ℂ := fun j => X 0 (Sum.inl j)
  let Xe : Fin M → ι → Matrix κ κ ℂ := fun l c => X (Fin.rev l).castSucc.succ (Sum.inr c)
  let P : (Fin M → ι) → Matrix κ κ ℂ := fun w' => (List.ofFn fun l => Xe l (w' l)).prod
  set s := sV (Ψfr M F) X h with hs_def
  have hs : s = ∑ i, ∑ w', ∑ j, F (List.ofFn w') i j • ((Xl i * P w' * X0 j) *ᵥ h) := by
    funext a
    have h1 : s a = ∑ w, (rprod (M + 2) (fun l => X l (w l)) *ᵥ h) a *
        (∑ i, ∑ w' : Fin M → ι, ∑ j, if w = enc i w' j then F (List.ofFn w') i j else 0) := by
      simp only [hs_def, sV, Ψfr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
        Matrix.mulVec, dotProduct, Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun b _ => by
        simp only [← Finset.sum_mul]; ring
    rw [h1, sum_mul_G]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w' _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [rprod_enc (g := X), mul_comm]
  set S2 := ∑ a, ‖s a‖ ^ 2 with hS2_def
  set H2 := ∑ b, ‖h b‖ ^ 2 with hH2_def
  show S2 ≤ H2
  let C : Matrix (Fin n) κ ℂ := Matrix.of fun i => star s ᵥ* Xl i
  let R : Matrix κ (Fin n) ℂ := Matrix.of fun k j => (X0 j *ᵥ h) k
  have hCPR : ∀ w' i j, (C * P w' * R) i j = star s ⬝ᵥ ((Xl i * P w' * X0 j) *ᵥ h) := by
    intro w' i j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec]
    rfl
  have hS2 : (S2 : ℂ) = ∑ w', ∑ i, ∑ j, (C * P w' * R) i j * F (List.ofFn w') i j := by
    have h1 : (S2 : ℂ) = star s ⬝ᵥ s := by
      simp only [hS2_def, dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
      push_cast
      rfl
    rw [h1]
    conv_lhs => arg 2; rw [hs]
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, hCPR]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hsingle : ∀ c : Fin n → ℂ,
      ‖∑ i, c i • EuclideanSpace.single (some i) (1 : ℂ)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    intro c
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    simp [Pi.single_apply]
  have hC : ∀ x : κ → ℂ, ∑ i, ‖(C *ᵥ x) i‖ ^ 2 ≤ S2 * ∑ k, ‖x k‖ ^ 2 := by
    intro x
    have h1 : ∀ i, (C *ᵥ x) i = star s ⬝ᵥ (Xl i *ᵥ x) := by
      intro i; rw [Matrix.dotProduct_mulVec]; rfl
    have h2 : ∑ i, ∑ a, ‖(Xl i *ᵥ x) a‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 := by
      have h3 := ampG_sum_le (eL ι n) (X (Fin.last (M + 1)))
        (fun b => x b • EuclideanSpace.single none (1 : ℂ))
      have h4 : ∀ a, ∑ c, ∑ b, X (Fin.last (M + 1)) c a b •
          eL ι n c (x b • EuclideanSpace.single none (1 : ℂ)) =
          ∑ i, (Xl i *ᵥ x) a • EuclideanSpace.single (some i) (1 : ℂ) := by
        intro a
        simp only [Fintype.sum_sum_type, eL, Sum.elim_inl, Sum.elim_inr,
          _root_.zero_apply, smul_zero, Finset.sum_const_zero, add_zero,
          rankOne_apply, inner_smul_right, EuclideanSpace.inner_single_left, map_one, one_mul,
          PiLp.single_apply, if_true, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by simp [Xl]
      simp only [h4, hsingle, PiLp.norm_single, norm_smul, norm_one, mul_one] at h3
      rw [Finset.sum_comm]
      refine h3.trans ?_
      calc ‖ampG (eL ι n) (X (Fin.last (M + 1)))‖ ^ 2 * ∑ b, ‖x b‖ ^ 2
          ≤ 1 * ∑ b, ‖x b‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hNl
        _ = _ := one_mul _
    calc ∑ i, ‖(C *ᵥ x) i‖ ^ 2 ≤ ∑ i, S2 * ∑ a, ‖(Xl i *ᵥ x) a‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => by rw [h1]; exact cs_dot s _
      _ = S2 * ∑ i, ∑ a, ‖(Xl i *ᵥ x) a‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ S2 * ∑ k, ‖x k‖ ^ 2 := by gcongr
  have hR : ∀ y : Fin n → ℂ, ∑ k, ‖(R *ᵥ y) k‖ ^ 2 ≤ H2 * ∑ j, ‖y j‖ ^ 2 := by
    intro y
    let u : Fr n := ∑ j, y j • EuclideanSpace.single (some j) (1 : ℂ)
    have hu : ‖u‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 := hsingle y
    have h3 := ampG_sum_le (eR ι n) (X 0) (fun b => h b • u)
    have h4 : ∀ k, ∑ c, ∑ b, X 0 c k b • eR ι n c (h b • u) =
        (R *ᵥ y) k • EuclideanSpace.single none (1 : ℂ) := by
      intro k
      have hu' : ∀ j, (u : Fr n) (some j) = y j := by
        intro j
        simp [u, Pi.single_apply]
      simp only [Fintype.sum_sum_type, eR, Sum.elim_inl, Sum.elim_inr,
        _root_.zero_apply, smul_zero, Finset.sum_const_zero, add_zero,
        rankOne_apply, inner_smul_right, EuclideanSpace.inner_single_left, map_one, one_mul,
        hu', smul_smul, Matrix.mulVec, dotProduct, R, X0, Matrix.of_apply, Finset.sum_smul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by
        congr 1; ring
    simp only [h4, PiLp.norm_single, norm_smul, norm_one, mul_one, mul_pow, hu,
      ← Finset.sum_mul] at h3
    refine h3.trans ?_
    calc ‖ampG (eR ι n) (X 0)‖ ^ 2 * ((∑ b, ‖h b‖ ^ 2) * ∑ j, ‖y j‖ ^ 2)
        ≤ 1 * ((∑ b, ‖h b‖ ^ 2) * ∑ j, ‖y j‖ ^ 2) := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hN0
      _ = _ := one_mul _
  have hXe : ∀ l (ζ : κ → L), ∑ a, ‖∑ c, ∑ b, Xe l c a b • e c (ζ b)‖ ^ 2 ≤
      ∑ b, ‖ζ b‖ ^ 2 := by
    intro l ζ
    have h3 := ampG_sum_le (eM (n := n) e) (X (Fin.rev l).castSucc.succ) ζ
    simp only [Fintype.sum_sum_type, eM, Sum.elim_inl, Sum.elim_inr,
      _root_.zero_apply, smul_zero, Finset.sum_const_zero, zero_add] at h3
    refine h3.trans ?_
    calc ‖ampG (eM (n := n) e) (X (Fin.rev l).castSucc.succ)‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2
        ≤ 1 * ∑ b, ‖ζ b‖ ^ 2 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) (hNm l)
      _ = _ := one_mul _
  have hS0le : 0 ≤ S2 := by positivity
  have hH0le : 0 ≤ H2 := by positivity
  rcases hS0le.lt_or_eq with hSpos | hS0
  swap
  · rw [← hS0]; exact hH0le
  rcases hH0le.lt_or_eq with hHpos | hH0
  swap
  · exfalso
    have hh : h = 0 := by
      funext b
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖h b‖)).mp hH0.symm b
        (Finset.mem_univ _)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hs0 : s = 0 := by rw [hs, hh]; simp
    have : S2 = 0 := by rw [hS2_def, hs0]; simp
    linarith
  set cC := Real.sqrt S2 with hcC_def
  set cR := Real.sqrt H2 with hcR_def
  have hcC : 0 < cC := Real.sqrt_pos.mpr hSpos
  have hcR : 0 < cR := Real.sqrt_pos.mpr hHpos
  have hb := chainBound_unit e F hF Xe hXe ((cC⁻¹ : ℂ) • C) ((cR⁻¹ : ℂ) • R)
    (fun x => by
      simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
        ← Finset.mul_sum, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcC.le]
      calc cC⁻¹ ^ 2 * ∑ i, ‖(C *ᵥ x) i‖ ^ 2 ≤ cC⁻¹ ^ 2 * (S2 * ∑ k, ‖x k‖ ^ 2) := by
            gcongr; exact hC x
        _ = ∑ k, ‖x k‖ ^ 2 := by
            rw [hcC_def, inv_pow, Real.sq_sqrt hS0le, ← mul_assoc, inv_mul_cancel₀ hSpos.ne',
              one_mul])
    (fun y => by
      simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
        ← Finset.mul_sum, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcR.le]
      calc cR⁻¹ ^ 2 * ∑ k, ‖(R *ᵥ y) k‖ ^ 2 ≤ cR⁻¹ ^ 2 * (H2 * ∑ j, ‖y j‖ ^ 2) := by
            gcongr; exact hR y
        _ = ∑ j, ‖y j‖ ^ 2 := by
            rw [hcR_def, inv_pow, Real.sq_sqrt hH0le, ← mul_assoc, inv_mul_cancel₀ hHpos.ne',
              one_mul])
  have hsum : ∑ w : Fin M → ι, ∑ i, ∑ j, ((cC⁻¹ : ℂ) • C * (List.ofFn fun l => Xe l (w l)).prod *
      ((cR⁻¹ : ℂ) • R)) i j * F (List.ofFn w) i j = ((cC⁻¹ * cR⁻¹ : ℝ) : ℂ) * (S2 : ℂ) := by
    rw [hS2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hsum, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg hS0le] at hb
  have h1 : S2 ≤ cC * cR := by
    have : S2 = (cC * cR) * (cC⁻¹ * cR⁻¹ * S2) := by field_simp
    rw [this]
    calc cC * cR * (cC⁻¹ * cR⁻¹ * S2) ≤ cC * cR * 1 := by gcongr
      _ = cC * cR := mul_one _
  have h2 : S2 ^ 2 ≤ S2 * H2 := by
    have := pow_le_pow_left₀ hS0le h1 2
    rwa [mul_pow, hcC_def, hcR_def, Real.sq_sqrt hS0le, Real.sq_sqrt hH0le] at this
  nlinarith

/-- From the normalized contractivity on a middle slot to `CC`. -/
lemma CC_of_CCN (e : ι → L →L[ℂ] L) {n R : ℕ}
    (ψ : Fin n ⊕ ι → E R →L[ℂ] E R) (hψ : CCN (ampN (eM (n := n) e)) ψ) :
    CC e (fun c => ψ (Sum.inr c)) := by
  intro k X
  set c := ‖amp e X‖ with hc
  -- the key estimate at a scale `t`
  have key : ∀ t : ℝ, 0 < t → t * c ≤ 1 → ‖amp (fun c => ψ (Sum.inr c)) X‖ ≤ 1 / t := by
    intro t ht htc
    let X'' : Fin n ⊕ ι → Matrix (Fin k) (Fin k) ℂ :=
      Sum.elim (fun _ => 0) (fun c' => (t : ℂ) • X c')
    have hN : ampN (eM (n := n) e) (Fin k) X'' ≤ 1 := by
      refine ampG_le_of _ _ 1 zero_le_one fun ζ => ?_
      have h1 := (amp e X).le_opNorm (WithLp.toLp 2 ζ)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at h2
      simp only [amp_apply] at h2
      simp only [Fintype.sum_sum_type, X'', eM, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply,
        zero_smul, Finset.sum_const_zero, zero_add, Matrix.smul_apply, smul_eq_mul, ← smul_smul,
        ← Finset.smul_sum, norm_smul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
        Real.norm_of_nonneg ht.le]
      calc t ^ 2 * ∑ a, ‖∑ c', ∑ b, X c' a b • e c' (ζ b)‖ ^ 2
          ≤ t ^ 2 * (‖amp e X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2) := by gcongr
        _ = (t * c) ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by rw [hc]; ring
        _ ≤ 1 ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by gcongr
    have h3 := hψ (Fin k) X'' hN
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ζ => ?_
    have h4 := h3 (fun b => ζ b)
    simp only [Fintype.sum_sum_type, X'', Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply,
      zero_smul, Finset.sum_const_zero, zero_add, Matrix.smul_apply, smul_eq_mul, ← smul_smul,
      ← Finset.smul_sum, norm_smul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
      Real.norm_of_nonneg ht.le] at h4
    rw [← PiLp.norm_sq_eq_of_L2] at h4
    have h5 : t ^ 2 * ‖amp (fun c => ψ (Sum.inr c)) X ζ‖ ^ 2 ≤ ‖ζ‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 _ (amp _ X ζ)]
      simpa only [amp_apply] using h4
    have h6 : t * ‖amp (fun c => ψ (Sum.inr c)) X ζ‖ ≤ ‖ζ‖ := by
      rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow]
      exact h5
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ht, mul_comm]
    exact h6
  rcases (norm_nonneg (amp e X)).lt_or_eq with hpos | hzero
  · have hcpos : 0 < c := by rw [hc]; exact hpos
    have := key (1 / c) (by positivity) (by rw [one_div_mul_cancel hcpos.ne'])
    simpa using this
  · have hc0 : c = 0 := by rw [hc]; exact hzero.symm
    by_contra hcon
    rw [not_le, hc0] at hcon
    set A := ‖amp (fun c => ψ (Sum.inr c)) X‖
    have := key (2 / A) (by positivity) (by rw [hc0]; simp)
    rw [one_div_div] at this
    linarith

lemma xi_bound {n R : ℕ} (ψ : Fin n ⊕ ι → E R →L[ℂ] E R) (hψ : CCN (ampN (eR ι n)) ψ)
    (x : E R) (hx : ‖x‖ ≤ 1) : ∑ j, ‖ψ (Sum.inl j) x‖ ^ 2 ≤ 1 := by
  classical
  let X : Fin n ⊕ ι → Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
    Sum.elim (fun j => Matrix.of fun a b => if a = some j ∧ b = none then 1 else 0) (fun _ => 0)
  have hN : ampN (eR ι n) (Option (Fin n)) X ≤ 1 := by
    refine ampG_le_of _ _ 1 zero_le_one fun ζ => ?_
    simp [X, eR, Fintype.sum_sum_type, Fintype.sum_option]
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul, norm_smul,
      PiLp.norm_single, norm_one, mul_one]
    have h1 : ‖ζ none‖ ^ 2 = ‖ζ none none‖ ^ 2 + ∑ j, ‖ζ none (some j)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    have h2 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖ζ (some i)‖)
    nlinarith [sq_nonneg ‖ζ none none‖]
  have h := hψ _ X hN (fun b => if b = none then x else 0)
  simp [X, Fintype.sum_sum_type, Fintype.sum_option] at h
  exact h.trans (by nlinarith [norm_nonneg x])

lemma eta_bound {n R : ℕ} (ψ : Fin n ⊕ ι → E R →L[ℂ] E R) (hψ : CCN (ampN (eL ι n)) ψ)
    (x : E R) (hx : ‖x‖ ≤ 1) : ∑ i, ‖(ψ (Sum.inl i)).adjoint x‖ ^ 2 ≤ 1 := by
  classical
  let X : Fin n ⊕ ι → Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
    Sum.elim (fun i => Matrix.of fun a b => if a = none ∧ b = some i then 1 else 0) (fun _ => 0)
  have hN : ampN (eL ι n) (Option (Fin n)) X ≤ 1 := by
    refine ampG_le_of _ _ 1 zero_le_one fun ζ => ?_
    simp [X, eL, Fintype.sum_sum_type, Fintype.sum_option]
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
    have h1 : ‖∑ i, (ζ (some i)) none • EuclideanSpace.single (some i) (1 : ℂ)‖ ^ 2 =
        ∑ i, ‖ζ (some i) none‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
      simp [Pi.single_apply]
    rw [h1]
    have h2 : ∀ i, ‖ζ (some i) none‖ ^ 2 ≤ ‖ζ (some i)‖ ^ 2 := fun i => by
      gcongr
      exact PiLp.norm_apply_le (ζ (some i)) none
    have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
    nlinarith [sq_nonneg ‖ζ none‖]
  let y : Fin n → E R := fun i => (ψ (Sum.inl i)).adjoint x
  have h := hψ _ X hN (fun b => Option.elim b 0 y)
  simp [X, Fintype.sum_sum_type, Fintype.sum_option] at h
  set v := ∑ i, ψ (Sum.inl i) (y i)
  set S := ∑ i, ‖y i‖ ^ 2
  have hS0 : 0 ≤ S := by positivity
  have hxv : ⟪x, v⟫_ℂ = (S : ℂ) := by
    simp only [v, S, inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ContinuousLinearMap.adjoint_inner_left]
    simp [y, inner_self_eq_norm_sq_to_K]
  have h1 : S ≤ ‖v‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) x v
    rw [hxv, Complex.norm_real, Real.norm_of_nonneg hS0] at this
    nlinarith [norm_nonneg v]
  show S ≤ 1
  nlinarith [norm_nonneg v]

end Frames

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem per_degree (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {n : ℕ}
    (F : List ι → Matrix (Fin n) (Fin n) ℂ) (hF : ChainBound e F) (M : ℕ) :
    ∃ (R : ℕ) (φ : Fin M → ι → EuclideanSpace ℂ (Fin R) →L[ℂ] EuclideanSpace ℂ (Fin R))
      (ξ η : Fin n → EuclideanSpace ℂ (Fin R)),
      (∀ l, CC e (φ l)) ∧ (∑ j, ‖ξ j‖ ^ 2 ≤ 1) ∧ (∑ i, ‖η i‖ ^ 2 ≤ 1) ∧
      ∀ (w : Fin M → ι) (i j : Fin n),
        F (List.ofFn w) i j = ⟪η i, (List.ofFn fun l => φ l (w l)).prod (ξ j)⟫_ℂ := by
  obtain ⟨R₀, hR₀⟩ := peel (M + 2) (Nslot e n M) (Nslot_NAx e n M) ℂ (Ψfr M F) (HC_fr e F hF M)
  obtain ⟨φ, η, J, hφ, hη, hrep⟩ := hR₀ R₀ le_rfl
  have hJ1 : ‖J 1‖ ≤ 1 := by simp
  refine ⟨R₀, fun l c => φ (Fin.rev l).castSucc.succ (Sum.inr c),
    fun j => φ 0 (Sum.inl j) (J 1), fun i => (φ (Fin.last (M + 1)) (Sum.inl i)).adjoint η,
    ?_, ?_, ?_, ?_⟩
  · intro l
    apply CC_of_CCN e
    have h := hφ (Fin.rev l).castSucc.succ
    have h1 : (Fin.rev l).castSucc.succ ≠ 0 := Fin.succ_ne_zero _
    have h2 : (Fin.rev l).castSucc.succ ≠ Fin.last (M + 1) := by
      rw [← Fin.succ_last]
      exact fun h => Fin.castSucc_ne_last _ (Fin.succ_injective _ h)
    simpa [Nslot, h1, h2] using h
  · exact xi_bound _ (by simpa [Nslot] using hφ 0) _ hJ1
  · refine eta_bound _ ?_ _ hη
    have h := hφ (Fin.last (M + 1))
    have h1 : Fin.last (M + 1) ≠ 0 := by simp
    simpa [Nslot, h1] using h
  · intro w i j
    rw [← Ψfr_enc F i w j, hrep, rprod_enc (g := φ), ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left]

end StrongConv.S9.Pisier.PartD
end
end

section
noncomputable section

namespace StrongConv.S9.Pisier

open scoped InnerProductSpace

alias per_degree := PartD.per_degree

end StrongConv.S9.Pisier
end
end

section
/-!
# PartL, basic helpers: coordinates of `tOp`/`amp`, words, letter norms
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace StrongConv.S9.Pisier.PartL

variable {ι : Type}

section Amp

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

lemma tOp_apply' {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (T : H₁ →L[ℂ] H₂)
    (x : PiLp 2 (fun _ : Fin k => H₁)) (a : Fin m) :
    tOp A T x a = ∑ b, A a b • T (x b) := by
  simp only [tOp, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.comp_apply]
  simp [Pi.single_apply, Finset.sum_apply]

variable [Fintype ι]

lemma amp_apply' (ρ : ι → H₁ →L[ℂ] H₂) {m k : ℕ} (X : ι → Matrix (Fin m) (Fin k) ℂ)
    (x : PiLp 2 (fun _ : Fin k => H₁)) (a : Fin m) :
    amp ρ X x a = ∑ l, ∑ b, X l a b • ρ l (x b) := by
  simp [amp, tOp_apply']

lemma amp_sum_le (ρ : ι → H₁ →L[ℂ] H₂) {m k : ℕ} (X : ι → Matrix (Fin m) (Fin k) ℂ)
    (ζ : Fin k → H₁) :
    ∑ a, ‖∑ l, ∑ b, X l a b • ρ l (ζ b)‖ ^ 2 ≤ ‖amp ρ X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by
  have h := (amp ρ X).le_opNorm (WithLp.toLp 2 ζ)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at h2
  simpa [amp_apply'] using h2

lemma amp_le_of (ρ : ι → H₁ →L[ℂ] H₂) {m k : ℕ} (X : ι → Matrix (Fin m) (Fin k) ℂ) (C : ℝ)
    (hC : 0 ≤ C)
    (h : ∀ ζ : Fin k → H₁, ∑ a, ‖∑ l, ∑ b, X l a b • ρ l (ζ b)‖ ^ 2 ≤ C ^ 2 * ∑ b, ‖ζ b‖ ^ 2) :
    ‖amp ρ X‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun ζ => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  simpa [amp_apply'] using h ζ

end Amp

section Words

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma evalW_nil' (σ : ι → K →L[ℂ] K) : evalW σ [] = 1 := by simp [evalW]

lemma evalW_cons' (σ : ι → K →L[ℂ] K) (l : ι) (w : List ι) :
    evalW σ (l :: w) = σ l * evalW σ w := by simp [evalW]

lemma evalW_append' (σ : ι → K →L[ℂ] K) (v w : List ι) :
    evalW σ (v ++ w) = evalW σ v * evalW σ w := by simp [evalW]

lemma norm_evalW_le (σ : ι → K →L[ℂ] K) (hσ : ∀ l, ‖σ l‖ ≤ 1) (w : List ι) :
    ‖evalW σ w‖ ≤ 1 := by
  induction w with
  | nil => rw [evalW_nil']; exact ContinuousLinearMap.norm_id_le
  | cons l w ih =>
    rw [evalW_cons']
    calc ‖σ l * evalW σ w‖ ≤ ‖σ l‖ * ‖evalW σ w‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hσ l) ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

end Words

section Letters

variable [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Letters of a CC map relative to unitary letters are contractions. -/
lemma norm_letter_le (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (ρ : ι → K →L[ℂ] K) (hρ : CC e ρ) (l : ι) : ‖ρ l‖ ≤ 1 := by
  classical
  let X : ι → Matrix (Fin 1) (Fin 1) ℂ := fun l' => if l' = l then 1 else 0
  have hX : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : ι → H →L[ℂ] H)
      (ζ : Fin 1 → H), ∑ a, ‖∑ l', ∑ b, X l' a b • σ l' (ζ b)‖ ^ 2 = ‖σ l (ζ 0)‖ ^ 2 := by
    intro H _ _ σ ζ
    simp only [Fin.sum_univ_one]
    congr 2
    rw [Finset.sum_eq_single l (fun l' _ hl' => by simp [X, hl']) (by simp)]
    simp [X]
  have he : ‖amp e X‖ ≤ 1 := by
    refine amp_le_of e X 1 zero_le_one fun ζ => ?_
    rw [hX, Fin.sum_univ_one, ContinuousLinearMap.norm_map_of_mem_unitary (hU.unitary l)]
    simp
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have h1 := amp_sum_le ρ X (fun _ => v)
  rw [hX, Fin.sum_univ_one] at h1
  have h2 : ‖amp ρ X‖ ≤ 1 := (hρ 1 X).trans he
  have h3 : ‖amp ρ X‖ ^ 2 ≤ 1 := by
    exact pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg _) h2
  have h4 : ‖ρ l v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    calc ‖ρ l v‖ ^ 2 ≤ ‖amp ρ X‖ ^ 2 * ‖v‖ ^ 2 := h1
      _ ≤ 1 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = ‖v‖ ^ 2 := one_mul _
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h4

end Letters

end StrongConv.S9.Pisier.PartL
end
end

section
/-!
# PartS: shift averaging (MATH.md Lemma 7)

From `per_degree` at length `M` (slot maps `φ_0, …, φ_{M-1}` on `E`), build
`K = (Fin (M+1) → E)` and the block shift `Φ(c)`, `(Φ(c) x)_k = φ_k(c) x_{k+1}` (with
`φ_M := 0` and `x_{M+1} := 0`). A word `w` of length `m` maps level `k + m` to level `k` by the
chain `φ_k(w_0) ⋯ φ_{k+m-1}(w_{m-1})`. The vectors are spread over the levels with products of
the slot maps at the unit letter.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace StrongConv.S9.Pisier.PartS

open StrongConv.S9.Pisier.PartL

section Shift

set_option linter.unusedSectionVars false

variable {ι : Type} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The level space. -/
abbrev Kp (M : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  PiLp 2 (fun _ : Fin (M + 1) => E)

/-- Level `n` of a vector, `0` beyond the top level. -/
def lev (M : ℕ) (x : Kp M E) (n : ℕ) : E := if h : n < M + 1 then x ⟨n, h⟩ else 0

lemma lev_of_lt (M : ℕ) (x : Kp M E) {n : ℕ} (h : n < M + 1) : lev M x n = x ⟨n, h⟩ :=
  dif_pos h

lemma lev_of_ge (M : ℕ) (x : Kp M E) {n : ℕ} (h : ¬ n < M + 1) : lev M x n = 0 :=
  dif_neg h

lemma lev_add (M : ℕ) (x y : Kp M E) (n : ℕ) : lev M (x + y) n = lev M x n + lev M y n := by
  unfold lev; split_ifs <;> simp

lemma lev_smul (M : ℕ) (c : ℂ) (x : Kp M E) (n : ℕ) : lev M (c • x) n = c • lev M x n := by
  unfold lev; split_ifs <;> simp

/-- The shift as a linear map. -/
def shiftL (M : ℕ) (ψ : ℕ → E →L[ℂ] E) : Kp M E →ₗ[ℂ] Kp M E where
  toFun x := WithLp.toLp 2 (fun k : Fin (M + 1) => ψ k (lev M x (k + 1)))
  map_add' x y := by
    ext k; simp [lev_add]
  map_smul' c x := by
    ext k; simp [lev_smul]

/-- The block shift letter map. -/
def shiftOp (M : ℕ) (φ' : ℕ → ι → E →L[ℂ] E) (c : ι) : Kp M E →L[ℂ] Kp M E :=
  LinearMap.toContinuousLinearMap (shiftL M (fun n => φ' n c))

lemma shiftOp_apply (M : ℕ) (φ' : ℕ → ι → E →L[ℂ] E) (c : ι) (x : Kp M E) (k : Fin (M + 1)) :
    shiftOp M φ' c x k = φ' k c (lev M x (k + 1)) := by
  simp [shiftOp, shiftL]

/-- The chain `φ'_n(w_0) φ'_{n+1}(w_1) ⋯`. -/
def Q (φ' : ℕ → ι → E →L[ℂ] E) : ℕ → List ι → E →L[ℂ] E
  | _, [] => 1
  | n, c :: w => φ' n c * Q φ' (n + 1) w

lemma Q_nil (φ' : ℕ → ι → E →L[ℂ] E) (n : ℕ) : Q φ' n [] = 1 := rfl

lemma Q_cons (φ' : ℕ → ι → E →L[ℂ] E) (n : ℕ) (c : ι) (w : List ι) :
    Q φ' n (c :: w) = φ' n c * Q φ' (n + 1) w := rfl

lemma Q_append (φ' : ℕ → ι → E →L[ℂ] E) (u v : List ι) (n : ℕ) :
    Q φ' n (u ++ v) = Q φ' n u * Q φ' (n + u.length) v := by
  induction u generalizing n with
  | nil => simp [Q_nil]
  | cons c u ih =>
    rw [List.cons_append, Q_cons, Q_cons, ih, mul_assoc]
    congr 3
    simp; omega

lemma Q_norm_le (φ' : ℕ → ι → E →L[ℂ] E) (h : ∀ n c, ‖φ' n c‖ ≤ 1) (u : List ι) (n : ℕ) :
    ‖Q φ' n u‖ ≤ 1 := by
  induction u generalizing n with
  | nil => rw [Q_nil]; exact ContinuousLinearMap.norm_id_le
  | cons c u ih =>
    rw [Q_cons]
    calc ‖φ' n c * Q φ' (n + 1) u‖ ≤ ‖φ' n c‖ * ‖Q φ' (n + 1) u‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (h n c) (ih _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

lemma Q_eq_ofFn (φ' : ℕ → ι → E →L[ℂ] E) (u : List ι) (a : ℕ) :
    Q φ' a u = (List.ofFn fun i : Fin u.length => φ' (a + i) u[i]).prod := by
  induction u generalizing a with
  | nil => simp [Q_nil]
  | cons c u ih =>
    rw [Q_cons, ih, List.ofFn_succ, List.prod_cons]
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    simp only [Fin.val_succ]
    congr 1
    omega

lemma lev_evalW (M : ℕ) (φ' : ℕ → ι → E →L[ℂ] E) (w : List ι) (x : Kp M E) (n : ℕ) :
    lev M (evalW (shiftOp M φ') w x) n = Q φ' n w (lev M x (n + w.length)) := by
  induction w generalizing n with
  | nil => simp [evalW_nil', Q_nil]
  | cons c w ih =>
    rw [evalW_cons', ContinuousLinearMap.mul_apply, Q_cons, ContinuousLinearMap.mul_apply]
    by_cases h : n < M + 1
    · have : lev M (shiftOp M φ' c (evalW (shiftOp M φ') w x)) n =
          φ' n c (lev M (evalW (shiftOp M φ') w x) (n + 1)) := by
        rw [lev_of_lt _ _ h, shiftOp_apply]
      rw [this, ih]
      congr 3
      simp; omega
    · have h1 : lev M (shiftOp M φ' c (evalW (shiftOp M φ') w x)) n = 0 := by
        exact lev_of_ge _ _ h
      have h2 : lev M x (n + (c :: w).length) = 0 := by
        rw [lev_of_ge]
        simp; omega
      rw [h1, ← ContinuousLinearMap.mul_apply, ← Q_cons, h2, map_zero]

lemma sum_lev_succ_sq (M : ℕ) (x : Kp M E) :
    ∑ k : Fin (M + 1), ‖lev M x (k + 1)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h0 : ∀ y : Kp M E, ‖y‖ ^ 2 = ∑ k ∈ Finset.range (M + 1), ‖lev M y k‖ ^ 2 := by
    intro y
    rw [PiLp.norm_sq_eq_of_L2, ← Fin.sum_univ_eq_sum_range (fun k => ‖lev M y k‖ ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lev_of_lt _ _ k.isLt]
  rw [h0, Fin.sum_univ_eq_sum_range (fun k => ‖lev M x (k + 1)‖ ^ 2)]
  have h1 := Finset.sum_range_succ' (fun k => ‖lev M x k‖ ^ 2) (M + 1)
  have h2 := Finset.sum_range_succ (fun k => ‖lev M x k‖ ^ 2) (M + 1)
  have h3 : lev M x (M + 1) = 0 := by simp [lev]
  rw [h3] at h2
  have h4 : 0 ≤ ‖lev M x 0‖ ^ 2 := sq_nonneg _
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h2
  linarith

variable [Fintype ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

lemma shiftOp_CC (M : ℕ) (e : ι → L →L[ℂ] L) (φ' : ℕ → ι → E →L[ℂ] E)
    (hφ : ∀ n, CC e (φ' n)) : CC e (shiftOp M φ') := by
  intro k X
  refine amp_le_of _ X _ (norm_nonneg _) fun ζ => ?_
  have hc : ∀ (a : Fin k) (n : Fin (M + 1)),
      (∑ l, ∑ b, X l a b • shiftOp M φ' l (ζ b)) n =
        ∑ l, ∑ b, X l a b • φ' n l (lev M (ζ b) (n + 1)) := by
    intro a n
    simp [shiftOp_apply]
  calc ∑ a, ‖∑ l, ∑ b, X l a b • shiftOp M φ' l (ζ b)‖ ^ 2
      = ∑ n : Fin (M + 1), ∑ a, ‖∑ l, ∑ b, X l a b • φ' n l (lev M (ζ b) (n + 1))‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hc]
    _ ≤ ∑ n : Fin (M + 1), ‖amp e X‖ ^ 2 * ∑ b, ‖lev M (ζ b) (n + 1)‖ ^ 2 := by
        refine Finset.sum_le_sum fun n _ => ?_
        refine (amp_sum_le (φ' n) X (fun b => lev M (ζ b) (n + 1))).trans ?_
        gcongr
        exact hφ n k X
    _ = ‖amp e X‖ ^ 2 * ∑ b, ∑ n : Fin (M + 1), ‖lev M (ζ b) (n + 1)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ‖amp e X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by
        gcongr with b
        exact sum_lev_succ_sq M (ζ b)

end Shift

section Rel

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

lemma sum_single_sub {V : Type*} [AddCommGroup V] [Module ℂ V] (u w : List ι) (G : List ι → V) :
    (∑ x ∈ (Finsupp.single u (1 : ℂ) - Finsupp.single w 1).support,
      ((Finsupp.single u (1 : ℂ) - Finsupp.single w 1 : List ι →₀ ℂ)) x • G x) = G u - G w := by
  have : (∑ x ∈ (Finsupp.single u (1 : ℂ) - Finsupp.single w 1).support,
      ((Finsupp.single u (1 : ℂ) - Finsupp.single w 1 : List ι →₀ ℂ)) x • G x) =
      (Finsupp.single u (1 : ℂ) - Finsupp.single w 1).sum (fun x c => c • G x) := rfl
  rw [this, Finsupp.sum_sub_index (fun a b₁ b₂ => sub_smul b₁ b₂ (G a)),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    one_smul, one_smul]

lemma frel_eq (e : ι → L →L[ℂ] L) {n : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (hrel : FRel e F) (u w : List ι) (h : evalW e u = evalW e w) : F u = F w := by
  have := hrel (Finsupp.single u (1 : ℂ) - Finsupp.single w 1)
    (by rw [sum_single_sub, h, sub_self])
  rw [sum_single_sub] at this
  exact sub_eq_zero.mp this

lemma evalW_replicate (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) (a : ℕ) :
    evalW e (List.replicate a hU.o) = 1 := by
  induction a with
  | zero => simp [evalW_nil']
  | succ a ih => rw [List.replicate_succ, evalW_cons', ih, hU.e_o, one_mul]

lemma F_pad (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {n : ℕ}
    (F : List ι → Matrix (Fin n) (Fin n) ℂ) (hrel : FRel e F) (a b : ℕ) (w : List ι) :
    F (List.replicate a hU.o ++ w ++ List.replicate b hU.o) = F w := by
  refine frel_eq e F hrel _ _ ?_
  rw [evalW_append', evalW_append', evalW_replicate, evalW_replicate, one_mul, mul_one]

end Rel

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem shift_average (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {n : ℕ}
    (F : List ι → Matrix (Fin n) (Fin n) ℂ) (hF : ChainBound e F) (hrel : FRel e F) (M : ℕ) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (φ : ι → K →L[ℂ] K) (ξ η : Fin n → K),
      CC e φ ∧ (∑ j, ‖ξ j‖ ^ 2 ≤ 1) ∧ (∑ i, ‖η i‖ ^ 2 ≤ 1) ∧
      ∀ (w : List ι) (i j : Fin n), w.length ≤ M →
        ⟪η i, evalW φ w (ξ j)⟫_ℂ = ((1 : ℂ) - (w.length : ℂ) / ((M : ℂ) + 1)) * F w i j := by
  classical
  obtain ⟨R, φ, ξ, η, hφ, hξ, hη, hFφ⟩ := StrongConv.S9.Pisier.per_degree e hU F hF M
  let φ' : ℕ → ι → EuclideanSpace ℂ (Fin R) →L[ℂ] EuclideanSpace ℂ (Fin R) :=
    fun k c => if h : k < M then φ ⟨k, h⟩ c else 0
  have hφ'CC : ∀ k, CC e (φ' k) := by
    intro k
    by_cases h : k < M
    · have : φ' k = φ ⟨k, h⟩ := by funext c; simp [φ', h]
      rw [this]; exact hφ ⟨k, h⟩
    · intro r X
      have h0 : φ' k = fun _ => 0 := by funext c; simp [φ', h]
      have : amp (φ' k) X = 0 := by
        ext x a
        simp [amp_apply', h0]
      rw [this, norm_zero]; exact norm_nonneg _
  have hφ'1 : ∀ k c, ‖φ' k c‖ ≤ 1 := fun k c => norm_letter_le e hU (φ' k) (hφ'CC k) c
  have hQ1 : ∀ k u (x : EuclideanSpace ℂ (Fin R)), ‖Q φ' k u x‖ ≤ ‖x‖ := by
    intro k u x
    have := (Q φ' k u).le_of_opNorm_le (Q_norm_le φ' hφ'1 u k) x
    simpa using this
  set s : ℝ := 1 / Real.sqrt ((M : ℝ) + 1) with hs
  have hs2 : s ^ 2 = 1 / ((M : ℝ) + 1) := by
    rw [hs, div_pow, Real.sq_sqrt (by positivity)]; simp
  have hns : ‖(s : ℂ)‖ ^ 2 = 1 / ((M : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hs2]
  set o := hU.o
  let ξh : Fin n → Kp M (EuclideanSpace ℂ (Fin R)) := fun j => WithLp.toLp 2
    (fun k : Fin (M + 1) => (s : ℂ) • Q φ' k (List.replicate (M - k) o) (ξ j))
  let ηh : Fin n → Kp M (EuclideanSpace ℂ (Fin R)) := fun i => WithLp.toLp 2
    (fun k : Fin (M + 1) =>
      (s : ℂ) • ContinuousLinearMap.adjoint (Q φ' 0 (List.replicate k o)) (η i))
  have hsum : ∀ c : ℝ, ∑ _k : Fin (M + 1), 1 / ((M : ℝ) + 1) * c = c := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨Kp M (EuclideanSpace ℂ (Fin R)), inferInstance, inferInstance, inferInstance,
    shiftOp M φ', ξh, ηh, shiftOp_CC M e φ' hφ'CC, ?_, ?_, ?_⟩
  · have hb : ∀ j, ‖ξh j‖ ^ 2 ≤ ‖ξ j‖ ^ 2 := by
      intro j
      rw [PiLp.norm_sq_eq_of_L2]
      calc ∑ k : Fin (M + 1), ‖ξh j k‖ ^ 2
          ≤ ∑ _k : Fin (M + 1), 1 / ((M : ℝ) + 1) * ‖ξ j‖ ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            simp only [ξh, norm_smul]
            rw [mul_pow, hns]
            gcongr
            exact hQ1 _ _ _
        _ = ‖ξ j‖ ^ 2 := hsum _
    exact (Finset.sum_le_sum fun j _ => hb j).trans hξ
  · have hb : ∀ i, ‖ηh i‖ ^ 2 ≤ ‖η i‖ ^ 2 := by
      intro i
      rw [PiLp.norm_sq_eq_of_L2]
      calc ∑ k : Fin (M + 1), ‖ηh i k‖ ^ 2
          ≤ ∑ _k : Fin (M + 1), 1 / ((M : ℝ) + 1) * ‖η i‖ ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            simp only [ηh, norm_smul]
            rw [mul_pow, hns]
            gcongr
            have h2 : ‖ContinuousLinearMap.adjoint (Q φ' 0 (List.replicate k o))‖ ≤ 1 := by
              rw [LinearIsometryEquiv.norm_map]; exact Q_norm_le φ' hφ'1 _ 0
            have h1 := (ContinuousLinearMap.adjoint (Q φ' 0 (List.replicate k o))).le_of_opNorm_le
              h2 (η i)
            simpa using h1
        _ = ‖η i‖ ^ 2 := hsum _
    exact (Finset.sum_le_sum fun i _ => hb i).trans hη
  · intro w i j hw
    have hterm : ∀ k : Fin (M + 1), ⟪ηh i k, evalW (shiftOp M φ') w (ξh j) k⟫_ℂ =
        if (k : ℕ) + w.length ≤ M then ((s ^ 2 : ℝ) : ℂ) * F w i j else 0 := by
      intro k
      have hk : (evalW (shiftOp M φ') w (ξh j)) k = Q φ' k w (lev M (ξh j) (k + w.length)) := by
        rw [← lev_evalW M φ' w (ξh j) k, lev_of_lt _ _ k.isLt]
      rw [hk]
      split_ifs with hkm
      · have hl : lev M (ξh j) (k + w.length) =
            (s : ℂ) • Q φ' (k + w.length) (List.replicate (M - (k + w.length)) o) (ξ j) := by
          rw [lev_of_lt _ _ (by omega)]
        rw [hl, map_smul]
        simp only [ηh]
        rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
        set u := List.replicate k o ++ w ++ List.replicate (M - (k + w.length)) o with hu_def
        have hQ : Q φ' 0 (List.replicate k o) (Q φ' k w
            (Q φ' (k + w.length) (List.replicate (M - (k + w.length)) o) (ξ j))) =
            Q φ' 0 u (ξ j) := by
          rw [hu_def, Q_append, Q_append]
          simp
        rw [hQ]
        have hu : u.length = M := by simp [u]; omega
        let f : Fin M → ι := fun l => u[l.val]'(by omega)
        have hf : List.ofFn f = u :=
          List.ext_getElem (by simp [hu]) (fun r h1 h2 => by simp [f])
        have hprod : (List.ofFn fun l => φ l (f l)).prod = Q φ' 0 u := by
          rw [Q_eq_ofFn]
          congr 1
          refine List.ext_getElem (by simp [hu]) (fun r h1 h2 => ?_)
          have hr : r < M := by simpa using h1
          simp [f, φ', hr]
        have hFu := hFφ f i j
        rw [hf, hprod] at hFu
        rw [← hFu, hu_def, F_pad e hU F hrel]
        rw [Complex.conj_ofReal]
        push_cast
        ring
      · rw [lev_of_ge _ _ (by omega), map_zero, inner_zero_right]
    rw [PiLp.inner_apply, Finset.sum_congr rfl fun k _ => hterm k,
      Fin.sum_univ_eq_sum_range (fun k => if k + w.length ≤ M then ((s ^ 2 : ℝ) : ℂ) * F w i j
        else 0), Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
    have hc : (Finset.filter (fun k => k + w.length ≤ M) (Finset.range (M + 1))) =
        Finset.range (M + 1 - w.length) := by
      ext k; simp; omega
    rw [hc, Finset.card_range, Nat.cast_sub (by omega), hs2]
    push_cast
    field_simp

end StrongConv.S9.Pisier.PartS
end
end

section
/-!
# PartL: Lemma 8 (coherent limit)

For each `M` the hypothesis gives `(K_M, φ_M, ξ_M, η_M)`. On the formal space
`Pre = (List ι × Fin n) →₀ ℂ` (formal combinations of `evalW φ w (ξ j)`) we put the semi-inner
product `⟪c, d⟫ = lim_𝒰 ⟪u_M c, u_M d⟫`, where `u_M` evaluates a formal combination in `K_M` and
`𝒰` is an ultrafilter finer than `atTop`. Letters act on `Pre` by prepending; they are bounded,
and extend to the completion. `η` is obtained by Riesz from `c ↦ lim ⟪η_M i, u_M c⟫`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate Topology NNReal
open Filter

namespace StrongConv.S9.Pisier.PartL

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Ultrafilter limits -/

/-- A fixed ultrafilter on `ℕ` finer than `atTop`. -/
def U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)

lemma U_le : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

lemma exists_tendsto_U {α : Type} [NormedAddCommGroup α] [ProperSpace α] (f : ℕ → α) (C : ℝ)
    (h : ∀ M, ‖f M‖ ≤ C) : ∃ z, Tendsto f U (𝓝 z) := by
  obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : α) C).ultrafilter_le_nhds (Ultrafilter.map f U)
    (by
      rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
      exact Filter.Eventually.of_forall fun M => by simpa using h M)
  exact ⟨z, hz⟩

lemma norm_le_one_of_sum_sq {E : Type} [NormedAddCommGroup E] {n : ℕ} (f : Fin n → E)
    (h : ∑ j, ‖f j‖ ^ 2 ≤ 1) (j : Fin n) : ‖f j‖ ≤ 1 := by
  have h1 : ‖f j‖ ^ 2 ≤ 1 :=
    (Finset.single_le_sum (f := fun j => ‖f j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)).trans h
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

/-! ## The sequence of models -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- The data of the hypothesis of `coherent_limit`, for all `M`. -/
structure Seq (e : ι → L →L[ℂ] L) (n : ℕ) where
  K : ℕ → Type
  [nag : ∀ M, NormedAddCommGroup (K M)]
  [ips : ∀ M, InnerProductSpace ℂ (K M)]
  φ : ∀ M, ι → K M →L[ℂ] K M
  ξ : ∀ M, Fin n → K M
  η : ∀ M, Fin n → K M
  hφ : ∀ M, CC e (φ M)
  hφ1 : ∀ M l, ‖φ M l‖ ≤ 1
  hξ : ∀ M, ∑ j, ‖ξ M j‖ ^ 2 ≤ 1
  hη : ∀ M, ∑ i, ‖η M i‖ ^ 2 ≤ 1

attribute [instance] Seq.nag Seq.ips

section Model

variable {e : ι → L →L[ℂ] L} {n : ℕ} (S : Seq e n)

/-- Formal combinations of the vectors `evalW φ w (ξ j)`. -/
def Pre (_S : Seq e n) : Type := (List ι × Fin n) →₀ ℂ

instance : AddCommGroup (Pre S) := inferInstanceAs (AddCommGroup ((List ι × Fin n) →₀ ℂ))
instance : Module ℂ (Pre S) := inferInstanceAs (Module ℂ ((List ι × Fin n) →₀ ℂ))

/-- The underlying finsupp. -/
def toF {S : Seq e n} (c : Pre S) : (List ι × Fin n) →₀ ℂ := c

/-- A formal combination from a finsupp. -/
def ofF (f : (List ι × Fin n) →₀ ℂ) : Pre S := f

/-- The formal word vector `[w ⊗ e_j]`. -/
def bas (w : List ι) (j : Fin n) : Pre S := ofF S (Finsupp.single (w, j) 1)

/-- The vector `evalW φ_M w (ξ_M j)`. -/
def vec (M : ℕ) (p : List ι × Fin n) : S.K M := evalW (S.φ M) p.1 (S.ξ M p.2)

/-- Evaluation of formal combinations in `K_M`. -/
def u (M : ℕ) : Pre S →ₗ[ℂ] S.K M where
  toFun c := Finsupp.linearCombination ℂ (vec S M) (toF c)
  map_add' c d := map_add (Finsupp.linearCombination ℂ (vec S M)) (toF c) (toF d)
  map_smul' r c := map_smul (Finsupp.linearCombination ℂ (vec S M)) r (toF c)

lemma u_apply' (M : ℕ) (c : Pre S) :
    u S M c = Finsupp.linearCombination ℂ (vec S M) (toF c) := rfl

/-- The `ℓ¹` norm of a formal combination. -/
def l1 (c : Pre S) : ℝ := ∑ p ∈ (toF c).support, ‖(toF c) p‖

lemma norm_vec_le (M : ℕ) (p : List ι × Fin n) : ‖vec S M p‖ ≤ 1 := by
  unfold vec
  calc ‖evalW (S.φ M) p.1 (S.ξ M p.2)‖ ≤ ‖evalW (S.φ M) p.1‖ * ‖S.ξ M p.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_evalW_le _ (S.hφ1 M) _)
        (norm_le_one_of_sum_sq _ (S.hξ M) _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma u_apply (M : ℕ) (c : Pre S) :
    u S M c = ∑ p ∈ (toF c).support,
      (toF c) p • vec S M p := by
  simp only [u, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.linearCombination_apply, Finsupp.sum]

lemma norm_u_le (M : ℕ) (c : Pre S) : ‖u S M c‖ ≤ l1 S c := by
  rw [u_apply, l1]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul]
  calc ‖(toF c) p‖ * ‖vec S M p‖ ≤ ‖(toF c) p‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_vec_le S M p) (norm_nonneg _)
    _ = _ := mul_one _

lemma u_single (M : ℕ) (w : List ι) (j : Fin n) :
    u S M (bas S w j) = evalW (S.φ M) w (S.ξ M j) := by
  simp [u, vec, bas, ofF, toF]

/-! ## The limit semi-inner product -/

/-- The limit form. -/
def ip (c d : Pre S) : ℂ := limUnder (U : Filter ℕ) (fun M => ⟪u S M c, u S M d⟫_ℂ)

lemma tendsto_ip (c d : Pre S) :
    Tendsto (fun M => ⟪u S M c, u S M d⟫_ℂ) U (𝓝 (ip S c d)) := by
  obtain ⟨z, hz⟩ := exists_tendsto_U (fun M => ⟪u S M c, u S M d⟫_ℂ) (l1 S c * l1 S d)
    (fun M => (norm_inner_le_norm _ _).trans
      (mul_le_mul (norm_u_le S M c) (norm_u_le S M d) (norm_nonneg _)
        ((norm_nonneg _).trans (norm_u_le S M c))))
  exact tendsto_nhds_limUnder ⟨z, hz⟩

lemma ip_eq {c d : Pre S} {z : ℂ} (h : Tendsto (fun M => ⟪u S M c, u S M d⟫_ℂ) U (𝓝 z)) :
    ip S c d = z :=
  tendsto_nhds_unique (tendsto_ip S c d) h

instance core : PreInnerProductSpace.Core ℂ (Pre S) where
  inner := ip S
  conj_inner_symm x y := by
    show conj (ip S y x) = ip S x y
    symm
    apply ip_eq
    have := (Complex.continuous_conj.tendsto _).comp (tendsto_ip S y x)
    refine this.congr fun M => ?_
    simp [Function.comp, inner_conj_symm]
  re_inner_nonneg x := by
    show 0 ≤ RCLike.re (ip S x x)
    refine ge_of_tendsto ((RCLike.continuous_re.tendsto _).comp (tendsto_ip S x x))
      (Filter.Eventually.of_forall fun M => ?_)
    simp only [Function.comp]
    exact inner_self_nonneg
  add_left x y z := by
    show ip S (x + y) z = ip S x z + ip S y z
    apply ip_eq
    refine ((tendsto_ip S x z).add (tendsto_ip S y z)).congr fun M => ?_
    simp [inner_add_left]
  smul_left x y r := by
    show ip S (r • x) y = conj r * ip S x y
    apply ip_eq
    refine ((tendsto_ip S x y).const_mul (conj r)).congr fun M => ?_
    simp [inner_smul_left, mul_comm]

instance seminormed : SeminormedAddCommGroup (Pre S) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance ips : InnerProductSpace ℂ (Pre S) := .ofCore _

lemma inner_eq (c d : Pre S) : ⟪c, d⟫_ℂ = ip S c d := rfl

lemma tendsto_norm_sq (c : Pre S) : Tendsto (fun M => ‖u S M c‖ ^ 2) U (𝓝 (‖c‖ ^ 2)) := by
  have h := (RCLike.continuous_re.tendsto _).comp (tendsto_ip S c c)
  have e1 : ‖c‖ ^ 2 = RCLike.re (ip S c c) := by
    rw [← inner_eq]; exact (inner_self_eq_norm_sq (𝕜 := ℂ) c).symm
  rw [e1]
  refine h.congr fun M => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-! ## Letters on formal combinations -/

/-- Prepending a letter. -/
def T (l : ι) : Pre S →ₗ[ℂ] Pre S :=
  Finsupp.lmapDomain ℂ ℂ (fun p : List ι × Fin n => (l :: p.1, p.2))

lemma u_T (M : ℕ) (l : ι) (c : Pre S) : u S M (T S l c) = S.φ M l (u S M c) := by
  have h1 : u S M (T S l c) = Finsupp.linearCombination ℂ (vec S M ∘
      fun p : List ι × Fin n => (l :: p.1, p.2)) (toF c) := by
    show Finsupp.linearCombination ℂ (vec S M)
      (Finsupp.mapDomain (fun p : List ι × Fin n => (l :: p.1, p.2)) (toF c)) = _
    exact Finsupp.linearCombination_mapDomain _ _ _
  rw [h1, Finsupp.linearCombination_apply, u_apply', Finsupp.linearCombination_apply,
    map_finsuppSum]
  refine Finsupp.sum_congr fun p _ => ?_
  simp [vec, evalW_cons']

lemma T_single (l : ι) (w : List ι) (j : Fin n) :
    T S l (bas S w j) = bas S (l :: w) j := by
  show Finsupp.mapDomain _ (Finsupp.single _ _) = _
  exact Finsupp.mapDomain_single

lemma sq_le_of_forall (c d : Pre S) (C : ℝ) (h : ∀ M, ‖u S M c‖ ^ 2 ≤ C * ‖u S M d‖ ^ 2) :
    ‖c‖ ^ 2 ≤ C * ‖d‖ ^ 2 :=
  le_of_tendsto_of_tendsto' (tendsto_norm_sq S c) ((tendsto_norm_sq S d).const_mul C) h

lemma norm_T_le (l : ι) (c : Pre S) : ‖T S l c‖ ≤ 1 * ‖c‖ := by
  rw [one_mul]
  have h := sq_le_of_forall S (T S l c) c 1 fun M => by
    rw [u_T, one_mul]
    have := (S.φ M l).le_of_opNorm_le (S.hφ1 M l) (u S M c)
    rw [one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [one_mul] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-! ## The completion -/

/-- The limit Hilbert space. -/
abbrev Hs := UniformSpace.Completion (Pre S)

/-- Letters as continuous maps on `Pre`. -/
def Tc (l : ι) : Pre S →L[ℂ] Pre S := (T S l).mkContinuous 1 (norm_T_le S l)

/-- The limit letters. -/
def phi' (l : ι) : Hs S →L[ℂ] Hs S :=
  ((UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S).comp (Tc S l)).extend
    (UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S)

lemma denseRange_toComplL : DenseRange (UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S) := by
  rw [UniformSpace.Completion.coe_toComplL]; exact UniformSpace.Completion.denseRange_coe

lemma isUniformInducing_toComplL :
    IsUniformInducing (UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S) := by
  rw [UniformSpace.Completion.coe_toComplL]; exact UniformSpace.Completion.isUniformInducing_coe _

lemma phi'_coe (l : ι) (c : Pre S) : phi' S l (c : Hs S) = ((T S l c : Pre S) : Hs S) := by
  have h := ContinuousLinearMap.extend_eq
    ((UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S).comp (Tc S l))
    (denseRange_toComplL S) (isUniformInducing_toComplL S) c
  rw [UniformSpace.Completion.coe_toComplL] at h
  rw [phi', h]
  simp [Tc]

/-- The limit vectors `ξ`. -/
def xi' (j : Fin n) : Hs S := (bas S [] j : Pre S)

lemma evalW_phi'_xi' (w : List ι) (j : Fin n) :
    evalW (phi' S) w (xi' S j) = ((bas S w j : Pre S) : Hs S) := by
  induction w with
  | nil => simp [evalW_nil', xi']
  | cons l w ih =>
    rw [evalW_cons', ContinuousLinearMap.mul_apply, ih, phi'_coe, T_single]

lemma coe_eq_toComplL (x : Pre S) :
    (x : Hs S) = (UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S) x := rfl

/-! ## The functional giving `η` -/

lemma bound_eta (M : ℕ) (i : Fin n) (c : Pre S) : ‖⟪S.η M i, u S M c⟫_ℂ‖ ≤ l1 S c := by
  refine (norm_inner_le_norm _ _).trans ?_
  calc ‖S.η M i‖ * ‖u S M c‖ ≤ 1 * l1 S c :=
        mul_le_mul (norm_le_one_of_sum_sq _ (S.hη M) i) (norm_u_le S M c) (norm_nonneg _)
          zero_le_one
    _ = l1 S c := one_mul _

/-- The limit functional `c ↦ lim ⟪η_M i, u_M c⟫`. -/
def fe (i : Fin n) (c : Pre S) : ℂ := limUnder (U : Filter ℕ) (fun M => ⟪S.η M i, u S M c⟫_ℂ)

lemma tendsto_fe (i : Fin n) (c : Pre S) :
    Tendsto (fun M => ⟪S.η M i, u S M c⟫_ℂ) U (𝓝 (fe S i c)) := by
  obtain ⟨z, hz⟩ := exists_tendsto_U _ (l1 S c) (fun M => bound_eta S M i c)
  exact tendsto_nhds_limUnder ⟨z, hz⟩

lemma fe_eq {i : Fin n} {c : Pre S} {z : ℂ}
    (h : Tendsto (fun M => ⟪S.η M i, u S M c⟫_ℂ) U (𝓝 z)) : fe S i c = z :=
  tendsto_nhds_unique (tendsto_fe S i c) h

/-- `fe` as a linear map. -/
def feL (i : Fin n) : Pre S →ₗ[ℂ] ℂ where
  toFun := fe S i
  map_add' c d := fe_eq S (((tendsto_fe S i c).add (tendsto_fe S i d)).congr fun M => by
    simp [inner_add_right])
  map_smul' r c := fe_eq S (((tendsto_fe S i c).const_mul r).congr fun M => by
    simp [inner_smul_right])

/-- The limit of `‖η_M i‖²`. -/
def rr (i : Fin n) : ℝ := limUnder (U : Filter ℕ) (fun M => ‖S.η M i‖ ^ 2)

lemma tendsto_rr (i : Fin n) : Tendsto (fun M => ‖S.η M i‖ ^ 2) U (𝓝 (rr S i)) := by
  obtain ⟨z, hz⟩ := exists_tendsto_U (fun M => ‖S.η M i‖ ^ 2) 1 (fun M => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (norm_nonneg _) (norm_le_one_of_sum_sq _ (S.hη M) i))
  exact tendsto_nhds_limUnder ⟨z, hz⟩

lemma rr_nonneg (i : Fin n) : 0 ≤ rr S i :=
  ge_of_tendsto' (tendsto_rr S i) (fun M => sq_nonneg _)

lemma fe_sq_le (i : Fin n) (c : Pre S) : ‖fe S i c‖ ^ 2 ≤ rr S i * ‖c‖ ^ 2 := by
  refine le_of_tendsto_of_tendsto' (((continuous_norm.tendsto _).comp (tendsto_fe S i c)).pow 2)
    ((tendsto_rr S i).mul (tendsto_norm_sq S c)) (fun M => ?_)
  simp only [Function.comp]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

lemma fe_le (i : Fin n) (c : Pre S) : ‖feL S i c‖ ≤ √(rr S i) * ‖c‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (rr_nonneg S i)]
  exact fe_sq_le S i c

/-- `fe` as a continuous linear map. -/
def feC (i : Fin n) : Pre S →L[ℂ] ℂ := (feL S i).mkContinuous _ (fe_le S i)

/-- Its extension to the completion. -/
def G (i : Fin n) : Hs S →L[ℂ] ℂ :=
  (feC S i).extend (UniformSpace.Completion.toComplL : Pre S →L[ℂ] Hs S)

/-- The limit vectors `η` (Riesz). -/
def eta' (i : Fin n) : Hs S := (InnerProductSpace.toDual ℂ (Hs S)).symm (G S i)

lemma inner_eta' (i : Fin n) (x : Hs S) : ⟪eta' S i, x⟫_ℂ = G S i x :=
  InnerProductSpace.toDual_symm_apply

lemma G_coe (i : Fin n) (c : Pre S) : G S i (c : Hs S) = fe S i c := by
  have h := ContinuousLinearMap.extend_eq (feC S i) (denseRange_toComplL S)
    (isUniformInducing_toComplL S) c
  rw [UniformSpace.Completion.coe_toComplL] at h
  rw [G, h]
  rfl

lemma G_le (i : Fin n) (x : Hs S) : ‖G S i x‖ ≤ √(rr S i) * ‖x‖ := by
  refine isClosed_property (p := fun x : Hs S => ‖G S i x‖ ≤ √(rr S i) * ‖x‖)
    UniformSpace.Completion.denseRange_coe
    (isClosed_le (by fun_prop) (by fun_prop)) (fun c => ?_) x
  show ‖G S i (c : Hs S)‖ ≤ √(rr S i) * ‖(c : Hs S)‖
  rw [G_coe, UniformSpace.Completion.norm_coe]
  exact fe_le S i c

lemma norm_eta'_le (i : Fin n) : ‖eta' S i‖ ≤ √(rr S i) := by
  rw [eta', LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (G_le S i)

/-! ## Complete contractivity of the limit letters -/


lemma cc_pre {k : ℕ} (X : ι → Matrix (Fin k) (Fin k) ℂ) (c : Fin k → Pre S) :
    ∑ a, ‖∑ l, ∑ b, X l a b • T S l (c b)‖ ^ 2 ≤ ‖amp e X‖ ^ 2 * ∑ b, ‖c b‖ ^ 2 := by
  refine le_of_tendsto_of_tendsto' (tendsto_finset_sum _ fun a _ => tendsto_norm_sq S _)
    ((tendsto_finset_sum _ fun b _ => tendsto_norm_sq S (c b)).const_mul _) fun M => ?_
  have hu : ∀ a, u S M (∑ l, ∑ b, X l a b • T S l (c b)) =
      ∑ l, ∑ b, X l a b • S.φ M l (u S M (c b)) := by
    intro a
    simp only [map_sum, map_smul, u_T]
  simp only [hu]
  calc _ ≤ ‖amp (S.φ M) X‖ ^ 2 * ∑ b, ‖u S M (c b)‖ ^ 2 := amp_sum_le _ X _
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) (S.hφ M k X) 2)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma phi'_sum_coe {k : ℕ} (X : ι → Matrix (Fin k) (Fin k) ℂ) (c : Fin k → Pre S) (a : Fin k) :
    ∑ l, ∑ b, X l a b • phi' S l ((c b : Pre S) : Hs S) =
      ((∑ l, ∑ b, X l a b • T S l (c b) : Pre S) : Hs S) := by
  rw [coe_eq_toComplL, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, ← coe_eq_toComplL, phi'_coe]

lemma cc_hs {k : ℕ} (X : ι → Matrix (Fin k) (Fin k) ℂ) (ζ : Fin k → Hs S) :
    ∑ a, ‖∑ l, ∑ b, X l a b • phi' S l (ζ b)‖ ^ 2 ≤ ‖amp e X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2 := by
  have hc : ∀ a, Continuous (fun ζ : Fin k → Hs S => ∑ l, ∑ b, X l a b • phi' S l (ζ b)) := by
    intro a
    refine continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun b _ => ?_
    have hb : Continuous fun ζ : Fin k → Hs S => ζ b := continuous_apply b
    exact ((phi' S l).continuous.comp hb).const_smul (X l a b)
  have hc1 : Continuous (fun ζ : Fin k → Hs S => ∑ a, ‖∑ l, ∑ b, X l a b • phi' S l (ζ b)‖ ^ 2) :=
    continuous_finset_sum _ fun a _ => ((hc a).norm.pow 2)
  have hc2 : Continuous (fun ζ : Fin k → Hs S => ‖amp e X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2) :=
    continuous_const.mul (continuous_finset_sum _ fun b _ =>
      ((continuous_apply b : Continuous fun ζ : Fin k → Hs S => ζ b).norm.pow 2))
  have hclosed : IsClosed {ζ : Fin k → Hs S | ∑ a, ‖∑ l, ∑ b, X l a b • phi' S l (ζ b)‖ ^ 2 ≤
      ‖amp e X‖ ^ 2 * ∑ b, ‖ζ b‖ ^ 2} := isClosed_le hc1 hc2
  have hdense : DenseRange (Pi.map fun (_ : Fin k) (c : Pre S) => (c : Hs S)) :=
    DenseRange.piMap fun _ => UniformSpace.Completion.denseRange_coe
  refine isClosed_property hdense hclosed (fun c => ?_) ζ
  show ∑ a, ‖∑ l, ∑ b, X l a b • phi' S l ((c b : Pre S) : Hs S)‖ ^ 2 ≤
      ‖amp e X‖ ^ 2 * ∑ b, ‖((c b : Pre S) : Hs S)‖ ^ 2
  simp only [phi'_sum_coe, UniformSpace.Completion.norm_coe]
  exact cc_pre S X c

lemma phi'_CC : CC e (phi' S) := fun k X =>
  amp_le_of _ X ‖amp e X‖ (ContinuousLinearMap.opNorm_nonneg _) (cc_hs S X)

/-! ## The limit model -/

lemma tendsto_factor (m : ℕ) (z : ℂ) :
    Tendsto (fun M : ℕ => ((1 : ℂ) - (m : ℂ) / ((M : ℂ) + 1)) * z) atTop (𝓝 z) := by
  have h0 : Tendsto (fun M : ℕ => (m : ℂ) / ((M : ℂ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (m : ℝ)
    have h' := (Complex.continuous_ofReal.tendsto _).comp h
    simp only [mul_zero, Complex.ofReal_zero] at h'
    refine h'.congr fun M => ?_
    simp [div_eq_mul_inv]
  simpa using ((tendsto_const_nhds (x := (1 : ℂ))).sub h0).mul_const z

theorem limit_model (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ (M : ℕ) (w : List ι) (i j : Fin n), w.length ≤ M →
      ⟪S.η M i, evalW (S.φ M) w (S.ξ M j)⟫_ℂ =
        ((1 : ℂ) - (w.length : ℂ) / ((M : ℂ) + 1)) * F w i j) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (φ : ι → K →L[ℂ] K) (ξ η : Fin n → K),
      CC e φ ∧ (∑ j, ‖ξ j‖ ^ 2 ≤ 1) ∧ (∑ i, ‖η i‖ ^ 2 ≤ 1) ∧
      ∀ (w : List ι) (i j : Fin n), ⟪η i, evalW φ w (ξ j)⟫_ℂ = F w i j := by
  refine ⟨Hs S, inferInstance, inferInstance, inferInstance, phi' S, xi' S, eta' S, phi'_CC S,
    ?_, ?_, ?_⟩
  · have h : ∀ j, ‖xi' S j‖ ^ 2 = ‖bas S [] j‖ ^ 2 := fun j => by
      rw [xi', UniformSpace.Completion.norm_coe]
    simp only [h]
    refine le_of_tendsto' (tendsto_finset_sum _ fun j _ => tendsto_norm_sq S (bas S [] j))
      fun M => ?_
    simp only [u_single, evalW_nil', ContinuousLinearMap.one_apply]
    exact S.hξ M
  · calc ∑ i, ‖eta' S i‖ ^ 2 ≤ ∑ i, rr S i := Finset.sum_le_sum fun i _ => by
          have := pow_le_pow_left₀ (norm_nonneg _) (norm_eta'_le S i) 2
          rwa [Real.sq_sqrt (rr_nonneg S i)] at this
      _ ≤ 1 := le_of_tendsto' (tendsto_finset_sum _ fun i _ => tendsto_rr S i) fun M => S.hη M
  · intro w i j
    rw [inner_eta', evalW_phi'_xi', G_coe]
    apply fe_eq
    simp only [u_single]
    refine ((tendsto_factor w.length (F w i j)).congr' ?_).mono_left U_le
    filter_upwards [eventually_ge_atTop w.length] with M hM
    exact (hF M w i j hM).symm

end Model

/-- Lemma 8 (coherent limit): an ultrafilter limit of the Gram kernels of `shift_average`, then
GNS, gives one completely contractive letter map reproducing `F` exactly. -/
theorem coherent_limit (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {n : ℕ}
    (F : List ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ M : ℕ, ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (φ : ι → K →L[ℂ] K) (ξ η : Fin n → K),
      CC e φ ∧ (∑ j, ‖ξ j‖ ^ 2 ≤ 1) ∧ (∑ i, ‖η i‖ ^ 2 ≤ 1) ∧
      ∀ (w : List ι) (i j : Fin n), w.length ≤ M →
        ⟪η i, evalW φ w (ξ j)⟫_ℂ = ((1 : ℂ) - (w.length : ℂ) / ((M : ℂ) + 1)) * F w i j) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (φ : ι → K →L[ℂ] K) (ξ η : Fin n → K),
      CC e φ ∧ (∑ j, ‖ξ j‖ ^ 2 ≤ 1) ∧ (∑ i, ‖η i‖ ^ 2 ≤ 1) ∧
      ∀ (w : List ι) (i j : Fin n), ⟪η i, evalW φ w (ξ j)⟫_ℂ = F w i j := by
  choose K i1 i2 i3 φ ξ η hφ hξ hη hF using hM
  let S : Seq e n :=
    { K := K, nag := i1, ips := i2, φ := φ, ξ := ξ, η := η, hφ := hφ,
      hφ1 := fun M l => norm_letter_le e hU (φ M) (hφ M) l, hξ := hξ, hη := hη }
  exact limit_model S F hF

end StrongConv.S9.Pisier.PartL
end
end

section
/-!
# PartC: Lemma 9 (compression)

`K₀` = closed span of the vectors `evalW φ w (ξ j)`; `N` = the vectors of `K₀` invisible to every
`⟪η i, evalW φ w ·⟫`; `S = K₀ ⊓ Nᗮ`; `ρ l = P_S φ(l)|_S`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace StrongConv.S9.Pisier.PartC

set_option linter.unusedSectionVars false

open StrongConv.S9.Pisier.PartL

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

section Spaces

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (φ : ι → K →L[ℂ] K) {n : ℕ} (ξ η : Fin n → K)

/-- The closed cyclic subspace generated by the `ξ j`. -/
def K0 : Submodule ℂ K :=
  (Submodule.span ℂ (Set.range fun p : List ι × Fin n => evalW φ p.1 (ξ p.2))).topologicalClosure

/-- The vectors invisible to `η` along all words. -/
def Nv : Submodule ℂ K where
  carrier := {v | ∀ (w : List ι) (i : Fin n), ⟪η i, evalW φ w v⟫_ℂ = 0}
  add_mem' := by
    intro a b ha hb w i
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [map_add, inner_add_right, ha w i, hb w i, add_zero]
  zero_mem' := by intro w i; simp
  smul_mem' := by
    intro c a ha w i
    simp only [Set.mem_ofPred_eq] at ha
    rw [map_smul, inner_smul_right, ha w i, mul_zero]

/-- `N = K₀ ∩ Nv`. -/
def Nn : Submodule ℂ K := K0 φ ξ ⊓ Nv φ η

/-- `S = K₀ ⊖ N`. -/
def Sp : Submodule ℂ K := K0 φ ξ ⊓ (Nn φ ξ η)ᗮ

lemma isClosed_K0 : IsClosed (K0 φ ξ : Set K) := Submodule.isClosed_topologicalClosure _

lemma isClosed_Nv : IsClosed (Nv φ η : Set K) := by
  have : (Nv φ η : Set K) = ⋂ w : List ι, ⋂ i : Fin n,
      (fun v => ⟪η i, evalW φ w v⟫_ℂ) ⁻¹' {0} := by
    ext v; simp [Nv]
  rw [this]
  exact isClosed_iInter fun w => isClosed_iInter fun i =>
    isClosed_singleton.preimage (continuous_const.inner (evalW φ w).continuous)

lemma isClosed_Nn : IsClosed (Nn φ ξ η : Set K) := by
  rw [Nn, Submodule.coe_inf]; exact (isClosed_K0 φ ξ).inter (isClosed_Nv φ η)

lemma isClosed_Sp : IsClosed (Sp φ ξ η : Set K) := by
  rw [Sp, Submodule.coe_inf]; exact (isClosed_K0 φ ξ).inter (Submodule.isClosed_orthogonal _)

instance : CompleteSpace (Nn φ ξ η) := (isClosed_Nn φ ξ η).isComplete.completeSpace_coe

instance instSp : CompleteSpace (Sp φ ξ η) := (isClosed_Sp φ ξ η).isComplete.completeSpace_coe

lemma gen_mem_K0 (w : List ι) (j : Fin n) : evalW φ w (ξ j) ∈ K0 φ ξ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(w, j), rfl⟩)

lemma K0_inv (l : ι) {v : K} (hv : v ∈ K0 φ ξ) : φ l v ∈ K0 φ ξ := by
  have h : K0 φ ξ ≤ (K0 φ ξ).comap (φ l : K →ₗ[ℂ] K) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨⟨w, j⟩, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
      have := gen_mem_K0 φ ξ (l :: w) j
      rwa [evalW_cons'] at this
    · exact (isClosed_K0 φ ξ).preimage (φ l).continuous
  exact h hv

lemma K0_evalW (w : List ι) {v : K} (hv : v ∈ K0 φ ξ) : evalW φ w v ∈ K0 φ ξ := by
  induction w with
  | nil => simpa [evalW_nil'] using hv
  | cons l w ih => rw [evalW_cons']; exact K0_inv φ ξ l ih

lemma Nv_inv (l : ι) {v : K} (hv : v ∈ Nv φ η) : φ l v ∈ Nv φ η := by
  intro w i
  have := hv (w ++ [l]) i
  rwa [evalW_append', evalW_cons', evalW_nil', mul_one] at this

lemma Nn_inv (l : ι) {v : K} (hv : v ∈ Nn φ ξ η) : φ l v ∈ Nn φ ξ η :=
  ⟨K0_inv φ ξ l hv.1, Nv_inv φ η l hv.2⟩

/-- For `v ∈ K₀`, `v - P_S v ∈ N`. -/
lemma sub_proj_mem (v : K) (hv : v ∈ K0 φ ξ) : v - (Sp φ ξ η).starProjection v ∈ Nn φ ξ η := by
  set N := Nn φ ξ η
  have hPN : N.starProjection v ∈ N := N.starProjection_apply_mem v
  have hPS : (Sp φ ξ η).starProjection v = v - N.starProjection v := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · refine ⟨(K0 φ ξ).sub_mem hv hPN.1, ?_⟩
      exact N.sub_starProjection_mem_orthogonal v
    · rw [sub_sub_cancel]
      have h1 : Sp φ ξ η ≤ Nᗮ := inf_le_right
      exact Submodule.orthogonal_le h1 (N.le_orthogonal_orthogonal hPN)
  rw [hPS, sub_sub_cancel]; exact hPN

lemma proj_N_eq_zero {v : K} (hv : v ∈ Nn φ ξ η) : (Sp φ ξ η).starProjection v = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff]
  have h1 : Sp φ ξ η ≤ (Nn φ ξ η)ᗮ := inf_le_right
  exact Submodule.orthogonal_le h1 ((Nn φ ξ η).le_orthogonal_orthogonal hv)

lemma Nn_evalW (w : List ι) {v : K} (hv : v ∈ Nn φ ξ η) : evalW φ w v ∈ Nn φ ξ η := by
  induction w with
  | nil => simpa [evalW_nil'] using hv
  | cons l w ih => rw [evalW_cons']; exact Nn_inv φ ξ η l ih

/-- The compressed letters. -/
def rho (l : ι) : Sp φ ξ η →L[ℂ] Sp φ ξ η :=
  (Sp φ ξ η).orthogonalProjectionOnto ∘L ((φ l) ∘L (Sp φ ξ η).subtypeL)

lemma rho_apply (l : ι) (s : Sp φ ξ η) :
    (rho φ ξ η l s : K) = (Sp φ ξ η).starProjection (φ l s) := rfl

lemma S_le_K0 : Sp φ ξ η ≤ K0 φ ξ := inf_le_left

lemma proj_proj_eq (l : ι) {x : K} (hx : x ∈ K0 φ ξ) :
    (Sp φ ξ η).starProjection (φ l ((Sp φ ξ η).starProjection x)) =
      (Sp φ ξ η).starProjection (φ l x) := by
  have hd := sub_proj_mem φ ξ η x hx
  have h0 := proj_N_eq_zero φ ξ η (Nn_inv φ ξ η l hd)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0.symm

lemma evalW_rho (w : List ι) (s : Sp φ ξ η) :
    (evalW (rho φ ξ η) w s : K) = (Sp φ ξ η).starProjection (evalW φ w s) := by
  induction w with
  | nil =>
    simp only [evalW_nil', ContinuousLinearMap.one_apply]
    exact ((Sp φ ξ η).starProjection_eq_self_iff.2 s.2).symm
  | cons l w ih =>
    rw [evalW_cons', evalW_cons', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      rho_apply, ih]
    exact proj_proj_eq φ ξ η l (K0_evalW φ ξ w (S_le_K0 φ ξ η s.2))

end Spaces

section Main

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (φ : ι → K →L[ℂ] K) {n : ℕ} (ξ η : Fin n → K)

lemma rho_CC (e : ι → L →L[ℂ] L) (hφ : CC e φ) : CC e (rho φ ξ η) := by
  intro k X
  refine (amp_le_of _ X ‖amp φ X‖ (norm_nonneg _) fun ζ => ?_).trans (hφ k X)
  refine le_trans ?_ (amp_sum_le φ X (fun b => (ζ b : K)))
  calc ∑ a, ‖∑ l, ∑ b, X l a b • rho φ ξ η l (ζ b)‖ ^ 2
      = ∑ a, ‖(Sp φ ξ η).starProjection (∑ l, ∑ b, X l a b • φ l (ζ b : K))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Submodule.norm_coe]
        congr 2
        simp only [Submodule.coe_sum, Submodule.coe_smul, rho_apply, map_sum, map_smul]
    _ ≤ ∑ a, ‖∑ l, ∑ b, X l a b • φ l (ζ b : K)‖ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2

lemma frel_shift (e : ι → L →L[ℂ] L) {F : List ι → Matrix (Fin n) (Fin n) ℂ} (hrel : FRel e F)
    (t : List ι →₀ ℂ) (ht : ∑ w ∈ t.support, t w • evalW e w = 0) (a b : List ι) (i j : Fin n) :
    ∑ w ∈ t.support, t w * F (a ++ w ++ b) i j = 0 := by
  have hz : ∀ (E : Type) [AddCommMonoid E] [Module ℂ E] (G : List ι → E),
      (∑ w ∈ (t.mapDomain fun w => a ++ w ++ b).support,
        (t.mapDomain fun w => a ++ w ++ b) w • G w) = ∑ w ∈ t.support, t w • G (a ++ w ++ b) := by
    intro E _ _ G
    change Finsupp.sum _ (fun w c => c • G w) = Finsupp.sum t (fun w c => c • G (a ++ w ++ b))
    rw [Finsupp.sum_mapDomain_index (h := fun w c => c • G w) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
  have h := hrel (t.mapDomain fun w => a ++ w ++ b) (by
    rw [hz]
    have : ∑ w ∈ t.support, t w • evalW e (a ++ w ++ b) =
        evalW e a * (∑ w ∈ t.support, t w • evalW e w) * evalW e b := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [evalW_append', evalW_append', mul_smul_comm, smul_mul_assoc]
    rw [this, ht, mul_zero, zero_mul])
  rw [hz] at h
  have := congrFun (congrFun h i) j
  simpa [Matrix.sum_apply] using this

lemma evalW_app3 (a w u : List ι) (x : K) :
    evalW φ (a ++ w ++ u) x = evalW φ a (evalW φ w (evalW φ u x)) := by
  rw [evalW_append', evalW_append']; rfl

lemma rel_mem (e : ι → L →L[ℂ] L) {F : List ι → Matrix (Fin n) (Fin n) ℂ} (hrel : FRel e F)
    (hF : ∀ (w : List ι) (i j : Fin n), ⟪η i, evalW φ w (ξ j)⟫_ℂ = F w i j)
    (t : List ι →₀ ℂ) (ht : ∑ w ∈ t.support, t w • evalW e w = 0) {v : K} (hv : v ∈ K0 φ ξ) :
    ∑ w ∈ t.support, t w • evalW φ w v ∈ Nn φ ξ η := by
  refine ⟨Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (K0_evalW φ ξ w hv), ?_⟩
  intro a i
  let g : K →L[ℂ] ℂ := (innerSL ℂ (η i)) ∘L (evalW φ a ∘L ∑ w ∈ t.support, t w • evalW φ w)
  have hg : ∀ v, g v = ⟪η i, evalW φ a (∑ w ∈ t.support, t w • evalW φ w v)⟫_ℂ := by
    intro v; simp [g]
  have hK : K0 φ ξ ≤ g.ker := by
    refine Submodule.topologicalClosure_minimal _ ?_ g.isClosed_ker
    rw [Submodule.span_le]
    rintro _ ⟨⟨u, j⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hg]
    rw [map_sum, inner_sum]
    rw [← frel_shift e hrel t ht a u i j]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, inner_smul_right, ← evalW_app3, hF]
  have := hK hv
  simpa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hg] using this

lemma rho_rel (e : ι → L →L[ℂ] L) {F : List ι → Matrix (Fin n) (Fin n) ℂ} (hrel : FRel e F)
    (hF : ∀ (w : List ι) (i j : Fin n), ⟪η i, evalW φ w (ξ j)⟫_ℂ = F w i j) :
    RespectsRel e (rho φ ξ η) := by
  intro t ht
  refine ContinuousLinearMap.ext fun s => Subtype.ext ?_
  have : ((∑ w ∈ t.support, t w • evalW (rho φ ξ η) w) s : K) =
      (Sp φ ξ η).starProjection (∑ w ∈ t.support, t w • evalW φ w s) := by
    simp [evalW_rho, map_sum, map_smul]
  rw [this, proj_N_eq_zero φ ξ η (rel_mem φ ξ η e hrel hF t ht (S_le_K0 φ ξ η s.2))]
  simp

lemma final_eq (w : List ι) (i j : Fin n) :
    ⟪η i, (Sp φ ξ η).starProjection (evalW φ w ((Sp φ ξ η).starProjection (ξ j)))⟫_ℂ =
      ⟪η i, evalW φ w (ξ j)⟫_ℂ := by
  set P := (Sp φ ξ η).starProjection
  have hx : ξ j ∈ K0 φ ξ := by simpa [evalW_nil'] using gen_mem_K0 φ ξ [] j
  have hd := sub_proj_mem φ ξ η (ξ j) hx
  have hz : evalW φ w (P (ξ j)) ∈ K0 φ ξ :=
    K0_evalW φ ξ w (S_le_K0 φ ξ η ((Sp φ ξ η).starProjection_apply_mem _))
  have hd' := sub_proj_mem φ ξ η _ hz
  have hm := (Nn φ ξ η).add_mem (Nn_evalW φ ξ η w hd) hd'
  have hm0 := hm.2 [] i
  rw [evalW_nil', ContinuousLinearMap.one_apply] at hm0
  have heq : P (evalW φ w (P (ξ j))) = evalW φ w (ξ j) -
      (evalW φ w (ξ j - P (ξ j)) + (evalW φ w (P (ξ j)) - P (evalW φ w (P (ξ j))))) := by
    rw [map_sub]; abel
  rw [heq, inner_sub_right, hm0, sub_zero]

end Main

/-- Lemma 9 (compression): restricting to the cyclic subspace of `ξ` and compressing away the
vectors invisible to `η` gives a letter map that also respects every relation of `e`. -/
theorem compress (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {n : ℕ}
    (F : List ι → Matrix (Fin n) (Fin n) ℂ) (hrel : FRel e F)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : ι → K →L[ℂ] K) (ξ η : Fin n → K) (hφ : CC e φ) (hξ : ∑ j, ‖ξ j‖ ^ 2 ≤ 1)
    (hη : ∑ i, ‖η i‖ ^ 2 ≤ 1) (hF : ∀ (w : List ι) (i j : Fin n),
      ⟪η i, evalW φ w (ξ j)⟫_ℂ = F w i j) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ρ : ι → H →L[ℂ] H) (ξ' η' : Fin n → H),
      CC e ρ ∧ RespectsRel e ρ ∧ (∑ j, ‖ξ' j‖ ^ 2 ≤ 1) ∧ (∑ i, ‖η' i‖ ^ 2 ≤ 1) ∧
      ∀ (w : List ι) (i j : Fin n), ⟪η' i, evalW ρ w (ξ' j)⟫_ℂ = F w i j := by
  refine ⟨Sp φ ξ η, inferInstance, inferInstance, instSp φ ξ η, rho φ ξ η,
    fun j => (Sp φ ξ η).orthogonalProjectionOnto (ξ j),
    fun i => (Sp φ ξ η).orthogonalProjectionOnto (η i),
    rho_CC φ ξ η e hφ, rho_rel φ ξ η e hrel hF, ?_, ?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun j _ => ?_) hξ
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Submodule.norm_orthogonalProjectionOnto_apply_le _ _) 2
  · refine le_trans (Finset.sum_le_sum fun i _ => ?_) hη
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Submodule.norm_orthogonalProjectionOnto_apply_le _ _) 2
  · intro w i j
    rw [Submodule.coe_inner, evalW_rho, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply, Submodule.inner_starProjection_left_eq_right,
      (Sp φ ξ η).starProjection_eq_self_iff.2 ((Sp φ ξ η).starProjection_apply_mem _),
      final_eq, hF]

end StrongConv.S9.Pisier.PartC
end
end

section
/-!
# PartE helpers: operator matrices

`mOp M` is the operator on `PiLp 2 (Fin n → K)` with blocks `M i j`; it is an injective
⋆-homomorphism of C⋆-algebras, hence isometric and order-reflecting. `tOp`, `amp` and `evalP`
are `mOp` of explicit matrices.
-/

noncomputable section

namespace StrongConv.S9.Pisier.PartE

open scoped InnerProductSpace ComplexOrder

section MOp

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The operator with blocks `M i j`. -/
def mOp {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    PiLp 2 (fun _ : Fin n => K) →L[ℂ] PiLp 2 (fun _ : Fin n => K) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      e.toContinuousLinearMap)

variable {n : ℕ}

@[simp]
lemma mOp_apply (M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K))
    (x : PiLp 2 (fun _ : Fin n => K)) (i : Fin n) :
    mOp M x i = ∑ j, M i j (x j) := by
  simp [mOp]

lemma mOp_add (M N : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    mOp (M + N) = mOp M + mOp N := by
  ext x i
  simp [Finset.sum_add_distrib]

lemma mOp_smul (c : ℂ) (M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    mOp (c • M) = c • mOp M := by
  ext x i
  simp [Finset.smul_sum]

lemma mOp_zero : mOp (0 : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) = 0 := by
  ext x i
  simp

lemma mOp_mul (M N : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    mOp (M * N) = mOp M * mOp N := by
  ext x i
  simp only [mOp_apply, CStarMatrix.mul_apply, ContinuousLinearMap.sum_apply,
    map_sum, ContinuousLinearMap.mul_apply]
  exact Finset.sum_comm

lemma mOp_one : mOp (1 : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) = 1 := by
  ext x i
  simp only [mOp_apply, CStarMatrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

variable [CompleteSpace K]

lemma mOp_star (M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    mOp (star M) = star (mOp M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, mOp_apply, sum_inner, inner_sum,
    CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

/-- `mOp` as a ⋆-homomorphism. -/
def mOpHom : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K) →⋆ₙₐ[ℂ]
    ((PiLp 2 (fun _ : Fin n => K)) →L[ℂ] (PiLp 2 (fun _ : Fin n => K))) where
  toFun := mOp
  map_zero' := mOp_zero
  map_add' := mOp_add
  map_smul' := mOp_smul
  map_mul' := mOp_mul
  map_star' := mOp_star

@[simp] lemma mOpHom_apply (M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    mOpHom (K := K) (n := n) M = mOp M := rfl

omit [CompleteSpace K] in
lemma mOp_injective : Function.Injective (mOp (K := K) (n := n)) := by
  intro M N h
  ext i j v
  have := congrArg (fun T => T (WithLp.toLp 2 (Pi.single j v)) i) h
  simpa [mOp_apply, Pi.single_apply, apply_ite, Finset.sum_ite_eq'] using this

lemma mOpHom_injective : Function.Injective (mOpHom (K := K) (n := n)) := mOp_injective

lemma norm_mOp (M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) : ‖mOp M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map mOpHom mOpHom_injective M

lemma mOp_nonneg {M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)} (hM : 0 ≤ M) : 0 ≤ mOp M := by
  have := map_nonneg (mOpHom (K := K) (n := n)) hM
  simpa using this

lemma nonneg_of_mOp_nonneg {M : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)} (hM : 0 ≤ mOp M) :
    0 ≤ M := by
  rw [← OAI.Compat.map_le_map_iff (mOpHom (K := K) (n := n)) mOpHom_injective]
  simpa [mOp_zero] using hM

end MOp

/-! ## `tOp`, `amp`, `evalP` as operator matrices -/

section TOp

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma tOp_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : K →L[ℂ] K)
    (x : PiLp 2 (fun _ : Fin n => K)) (a : Fin n) :
    tOp A T x a = ∑ b, A a b • T (x b) := by
  simp only [tOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp [Pi.single_apply, Finset.sum_apply]

lemma amp_eq_mOp {ι : Type*} [Fintype ι] (σ : ι → K →L[ℂ] K) {n : ℕ}
    (C : ι → Matrix (Fin n) (Fin n) ℂ) :
    amp σ C = mOp (CStarMatrix.ofMatrix fun a b => ∑ l, C l a b • σ l) := by
  ext x a
  simp only [amp, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, tOp_apply,
    mOp_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  change _ = (∑ l, C l a b • σ l) (x b)
  simp [ContinuousLinearMap.sum_apply]

lemma evalP_eq_mOp {ι : Type} (σ : ι → K →L[ℂ] K) {n : ℕ}
    (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) :
    evalP σ y = mOp (CStarMatrix.ofMatrix fun a b =>
      ∑ w ∈ y.support, y w a b • evalW σ w) := by
  ext x a
  simp only [evalP, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, tOp_apply,
    mOp_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  change _ = (∑ w ∈ y.support, y w a b • evalW σ w) (x b)
  simp [ContinuousLinearMap.sum_apply]

end TOp

end StrongConv.S9.Pisier.PartE

/-! ## A unital map contractive under all scalar shifts is positive -/

namespace StrongConv.S9.Pisier.PartE

open scoped InnerProductSpace ComplexOrder

section Pos

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [CompleteSpace V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [CompleteSpace V₂]

lemma shift_bound (P : V₁ →L[ℂ] V₁) (hP : 0 ≤ P) (t : ℝ) :
    ‖P - (((‖P‖ : ℝ) : ℂ) - (t : ℂ) * Complex.I) • (1 : V₁ →L[ℂ] V₁)‖ ≤
      Real.sqrt (‖P‖ ^ 2 + t ^ 2) := by
  set r := ‖P‖ with hr
  have hsa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg hP
  have h1 : P ≤ algebraMap ℝ _ r := hsa.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at h1
  have h2 : ‖(r • (1 : V₁ →L[ℂ] V₁)) - P‖ ≤ r := by
    have ha : 0 ≤ r • (1 : V₁ →L[ℂ] V₁) - P := sub_nonneg.mpr h1
    have hb : r • (1 : V₁ →L[ℂ] V₁) - P ≤ r • 1 := sub_le_self _ hP
    refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hb).trans ?_
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hpos := (ContinuousLinearMap.isPositive_iff_complex P).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive P).mp hP)
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hx1 : ‖(P - (r : ℂ) • (1 : V₁ →L[ℂ] V₁)) x‖ ≤ r * ‖x‖ := by
    have : P - (r : ℂ) • (1 : V₁ →L[ℂ] V₁) = -(r • (1 : V₁ →L[ℂ] V₁) - P) := by
      rw [neg_sub, Complex.coe_smul]
    rw [this, ContinuousLinearMap.neg_apply, norm_neg]
    exact ((r • (1 : V₁ →L[ℂ] V₁) - P).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have hsplit : (P - (((r : ℝ) : ℂ) - (t : ℂ) * Complex.I) • (1 : V₁ →L[ℂ] V₁)) x =
      (P - (r : ℂ) • (1 : V₁ →L[ℂ] V₁)) x + ((t : ℂ) * Complex.I) • x := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul]
    abel
  have hre : RCLike.re (inner ℂ ((P - (r : ℂ) • (1 : V₁ →L[ℂ] V₁)) x)
      (((t : ℂ) * Complex.I) • x)) = 0 := by
    rw [inner_smul_right, ContinuousLinearMap.sub_apply, inner_sub_left,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_left,
      ← (hpos x).1, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  have hsq : ‖(P - (((r : ℝ) : ℂ) - (t : ℂ) * Complex.I) • (1 : V₁ →L[ℂ] V₁)) x‖ ^ 2 ≤
      (Real.sqrt (r ^ 2 + t ^ 2) * ‖x‖) ^ 2 := by
    rw [hsplit, norm_add_sq (𝕜 := ℂ), hre, mul_pow, Real.sq_sqrt (by positivity), norm_smul]
    have hn : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
    rw [hn]
    have := pow_le_pow_left₀ (norm_nonneg _) hx1 2
    nlinarith [sq_abs t, sq_nonneg ‖x‖]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

lemma pos_of_shift_le (P : V₁ →L[ℂ] V₁) (hP : 0 ≤ P) (Q : V₂ →L[ℂ] V₂)
    (h : ∀ s : ℂ, ‖Q - s • (1 : V₂ →L[ℂ] V₂)‖ ≤ ‖P - s • (1 : V₁ →L[ℂ] V₁)‖) : 0 ≤ Q := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro y
  by_cases hy : y = 0
  · subst hy
    simp
  set r := ‖P‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  set m := ‖y‖ ^ 2 with hm
  set z := inner ℂ (Q y) y with hz
  -- the basic inequality for every real `t`
  have key : ∀ t : ℝ, (z.re - r * m) ^ 2 + (z.im - t * m) ^ 2 ≤ (r ^ 2 + t ^ 2) * m ^ 2 := by
    intro t
    set s : ℂ := ((r : ℝ) : ℂ) - (t : ℂ) * Complex.I
    have h1 : ‖inner ℂ ((Q - s • (1 : V₂ →L[ℂ] V₂)) y) y‖ ≤
        Real.sqrt (r ^ 2 + t ^ 2) * m := by
      refine (norm_inner_le_norm _ _).trans ?_
      calc ‖(Q - s • (1 : V₂ →L[ℂ] V₂)) y‖ * ‖y‖
          ≤ ‖Q - s • (1 : V₂ →L[ℂ] V₂)‖ * ‖y‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ Real.sqrt (r ^ 2 + t ^ 2) * ‖y‖ * ‖y‖ := by
            gcongr
            exact (h s).trans (shift_bound P hP t)
        _ = Real.sqrt (r ^ 2 + t ^ 2) * m := by rw [hm]; ring
    have h2 : inner ℂ ((Q - s • (1 : V₂ →L[ℂ] V₂)) y) y =
        z - ((r : ℂ) + (t : ℂ) * Complex.I) * (m : ℂ) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp [s, hm, map_sub, Complex.conj_ofReal]
      exact hz.symm
    rw [h2] at h1
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, Real.sq_sqrt (by positivity), Complex.sq_norm, Complex.normSq_apply] at h3
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at h3
    nlinarith [h3]
  have hm0 : 0 < m := by rw [hm]; positivity
  have him : z.im = 0 := by
    by_contra hb
    have := key (-(r ^ 2 * m ^ 2 + 1) / (2 * z.im * m))
    have hden : 2 * z.im * m ≠ 0 := by positivity
    have e1 : z.im * (-(r ^ 2 * m ^ 2 + 1) / (2 * z.im * m) * m) =
        -(r ^ 2 * m ^ 2 + 1) / 2 := by
      field_simp
    nlinarith [sq_nonneg (z.re - r * m), sq_nonneg z.im,
      sq_nonneg (-(r ^ 2 * m ^ 2 + 1) / (2 * z.im * m) * m)]
  have hre : 0 ≤ z.re := by
    have := key 0
    nlinarith [mul_nonneg hr0 hm0.le]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [him]
  · simpa using hre

end Pos

end StrongConv.S9.Pisier.PartE
end
end

section
/-!
# PartE helpers: unital completely positive maps into `B(H)`

Star preservation, the Kadison–Schwarz inequality (from 2-positivity), and the multiplicative
domain property for unitaries sent to co-isometries.
-/

noncomputable section

namespace StrongConv.S9.Pisier.PartE

open scoped InnerProductSpace ComplexOrder

lemma scalar_zero (c : ℂ) (K : ℝ) (h : ∀ t : ℂ, 0 ≤ 2 * (t * c).re + ‖t‖ ^ 2 * K) :
    c = 0 := by
  set s : ℝ := 1 / (|K| + 1) with hs
  have hs0 : 0 < s := by positivity
  have hsK : s * K < 1 := by
    rw [hs, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith [le_abs_self K]
  have h1 := h (-(s : ℂ) * (starRingEnd ℂ) c)
  have e1 : (-(s : ℂ) * (starRingEnd ℂ) c * c).re = -s * Complex.normSq c := by
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.mul_re]
  have e2 : ‖-(s : ℂ) * (starRingEnd ℂ) c‖ ^ 2 = s ^ 2 * Complex.normSq c := by
    rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_conj, mul_pow,
      Real.norm_of_nonneg hs0.le, Complex.sq_norm]
  rw [e1, e2] at h1
  have hN : Complex.normSq c ≤ 0 := by
    have hN0 := Complex.normSq_nonneg c
    nlinarith [mul_pos hs0 hs0]
  exact Complex.normSq_eq_zero.mp (le_antisymm hN (Complex.normSq_nonneg c))

variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cp_star (Φ : CompletelyPositiveMap (L →L[ℂ] L) (H →L[ℂ] H)) (a : L →L[ℂ] L) :
    Φ (star a) = star (Φ a) := by
  obtain ⟨x, hx, _, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hxstar (i : Fin 4) : star (x i) = x i := (IsSelfAdjoint.of_nonneg (hx i)).star_eq
  have hystar (i : Fin 4) : star (Φ (x i)) = Φ (x i) :=
    (IsSelfAdjoint.of_nonneg (map_nonneg Φ (hx i))).star_eq
  simp only [star_sum, star_smul, map_sum, map_smul, hxstar, hystar]

/-- Kadison–Schwarz, vector form. -/
lemma cp_schwarz (Φ : CompletelyPositiveMap (L →L[ℂ] L) (H →L[ℂ] H)) (hΦ1 : Φ 1 = 1)
    (x : L →L[ℂ] L) (h : H) :
    ‖Φ x h‖ ^ 2 ≤ RCLike.re (inner ℂ (Φ (star x * x) h) h) := by
  let R : CStarMatrix (Fin 2) (Fin 2) (L →L[ℂ] L) := !![1, x; 0, 0]
  have hM := Φ.map_cstarMatrix_nonneg _ (star_mul_self_nonneg R)
  set M := (star R * R).map Φ with hMdef
  have e : ∀ i j, M i j = Φ (∑ k, star (R k i) * R k j) := fun i j => rfl
  have r00 : R 0 0 = 1 := rfl
  have r01 : R 0 1 = x := rfl
  have r10 : R 1 0 = 0 := rfl
  have r11 : R 1 1 = 0 := rfl
  have hT := (ContinuousLinearMap.isPositive_iff_complex _).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (mOp_nonneg hM))
  have hξ := (hT (WithLp.toLp 2 ![-(Φ x h), h])).2
  have hsx := cp_star Φ x
  simp only [PiLp.inner_apply, mOp_apply, Fin.sum_univ_two, e, r00, r01, r10, r11] at hξ
  simp only [star_one, star_zero, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add,
    hΦ1, hsx, map_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.head_cons] at hξ
  have hadj : inner ℂ (star (Φ x) (Φ x h)) h = inner ℂ (Φ x h) (Φ x h) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [map_neg, ContinuousLinearMap.one_apply, neg_add_cancel, inner_zero_left, zero_add,
    inner_add_left, inner_neg_left, hadj] at hξ
  simp only [map_add, map_neg, inner_self_eq_norm_sq (𝕜 := ℂ)] at hξ
  linarith

/-- Multiplicative domain: a unitary-like element whose image is a co-isometry multiplies on
the left. -/
lemma cp_mult (Φ : CompletelyPositiveMap (L →L[ℂ] L) (H →L[ℂ] H)) (hΦ1 : Φ 1 = 1)
    (u : L →L[ℂ] L) (hu : u * star u = 1) (hU : Φ u * star (Φ u) = 1) (y : L →L[ℂ] L) :
    Φ (u * y) = Φ u * Φ y := by
  set A := Φ (u * y) with hA
  set B := Φ (star y * y) with hB
  set U := Φ u with hUdef
  set Y := Φ y with hY
  have key : ∀ h : H, inner ℂ h ((A - U * Y) h) = 0 := by
    intro h
    apply scalar_zero _ (RCLike.re (inner ℂ (B h) h) - ‖Y h‖ ^ 2)
    intro t
    have hs := cp_schwarz Φ hΦ1 (star u + t • y) h
    have hx : star (star u + t • y) * (star u + t • y) =
        1 + t • (u * y) + (starRingEnd ℂ t) • star (u * y) +
          ((starRingEnd ℂ t) * t) • (star y * y) := by
      simp only [star_add, star_star, star_smul, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, hu, star_mul]
      simp only [Complex.star_def, smul_add, smul_smul]
      rw [mul_comm ((starRingEnd ℂ) t) t]
      abel
    have hL : Φ (star u + t • y) h = star U h + t • Y h := by
      simp [map_add, map_smul, cp_star, hUdef, hY]
    have hR : Φ (star (star u + t • y) * (star u + t • y)) =
        1 + t • A + (starRingEnd ℂ t) • star A + ((starRingEnd ℂ t) * t) • B := by
      rw [hx]
      simp only [map_add, map_smul, hΦ1, cp_star, hA, hB]
    rw [hL, hR, norm_add_sq (𝕜 := ℂ), norm_smul] at hs
    have h1 : ‖star U h‖ ^ 2 = ‖h‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_apply, hU,
        ContinuousLinearMap.one_apply]
    have h2 : inner ℂ (star U h) (t • Y h) = t * inner ℂ h (U (Y h)) := by
      rw [inner_smul_right, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have h3 : inner ℂ ((1 + t • A + (starRingEnd ℂ t) • star A +
        ((starRingEnd ℂ t) * t) • B) h) h =
        inner ℂ h h + (starRingEnd ℂ t) * inner ℂ (A h) h + t * inner ℂ h (A h) +
          (starRingEnd ℂ ((starRingEnd ℂ t) * t)) * inner ℂ (B h) h := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_add_left, inner_smul_left]
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      simp
    rw [h1, h2, h3] at hs
    have e1 : RCLike.re ((starRingEnd ℂ t) * inner ℂ (A h) h) =
        RCLike.re (t * inner ℂ h (A h)) := by
      rw [← inner_conj_symm (A h) h, ← map_mul, RCLike.conj_re]
    have e2 : RCLike.re ((starRingEnd ℂ ((starRingEnd ℂ t) * t)) * inner ℂ (B h) h) =
        ‖t‖ ^ 2 * RCLike.re (inner ℂ (B h) h) := by
      have hc : starRingEnd ℂ ((starRingEnd ℂ t) * t) = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
        rw [map_mul, Complex.conj_conj, mul_comm, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
      rw [hc, RCLike.re_to_complex, Complex.re_ofReal_mul, RCLike.re_to_complex]
    have e3 : RCLike.re (inner ℂ h h) = ‖h‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) h
    have e4 : inner ℂ h ((A - U * Y) h) = inner ℂ h (A h) - inner ℂ h (U (Y h)) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.mul_apply]
    rw [e4, mul_sub]
    simp only [map_add, e1, e2, e3, Complex.sub_re] at hs ⊢
    simp only [RCLike.re_to_complex, Complex.sub_re] at hs ⊢
    nlinarith [hs, mul_pow ‖t‖ ‖Y h‖ 2]
  have hT0 := (inner_map_self_eq_zero (A - U * Y).toLinearMap).mp (fun h => by
    change inner ℂ ((A - U * Y) h) h = 0
    rw [← inner_conj_symm, key h, map_zero])
  have hT : A - U * Y = 0 :=
    ContinuousLinearMap.coe_injective (hT0.trans ContinuousLinearMap.coe_zero.symm)
  exact sub_eq_zero.mp hT

end StrongConv.S9.Pisier.PartE
end
end

section
/-!
# Part E: Pisier's endgame (MATH.md Lemma 10)

`S = span {e l}` is an operator system and `φ (e l) = ρ l` is well defined (by `RespectsRel`),
unital, and positive at every matrix level (a unital map that stays contractive under all scalar
shifts is positive; `CC` gives that contractivity). Arveson extends `φ` to a unital completely
positive `Φ` on `B(L)`. Each `e l` is unitary and `Φ (e l) = ρ l` is a co-isometry, so `e l` lies
in the multiplicative domain of `Φ` (Kadison–Schwarz); hence `Φ` is multiplicative on words and
`Φ` applied entrywise sends `evalP e y` to `evalP ρ y`. Positivity of `Φ` at level `n`, applied to
`‖Y‖² - Y⋆Y ≥ 0`, gives the norm bound. No Stinespring dilation is needed.
-/

noncomputable section

namespace StrongConv.S9.Pisier.PartE

open scoped InnerProductSpace ComplexOrder
open OAI.BoundedHochschild.KadisonRingrose

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

section Words

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

omit [Fintype ι] [DecidableEq ι] in
lemma evalW_nil (σ : ι → K →L[ℂ] K) : evalW σ [] = 1 := by simp [evalW]

omit [Fintype ι] [DecidableEq ι] in
lemma evalW_cons (σ : ι → K →L[ℂ] K) (l : ι) (w : List ι) :
    evalW σ (l :: w) = σ l * evalW σ w := by simp [evalW]

omit [Fintype ι] [DecidableEq ι] in
lemma evalW_append (σ : ι → K →L[ℂ] K) (v w : List ι) :
    evalW σ (v ++ w) = evalW σ v * evalW σ w := by simp [evalW]

omit [Fintype ι] [DecidableEq ι] in
lemma evalW_singleton (σ : ι → K →L[ℂ] K) : (evalW σ ∘ fun l : ι => [l]) = σ := by
  funext l; simp [evalW]

omit [Fintype ι] [DecidableEq ι] in
lemma sum_support_eq {E : Type*} [AddCommGroup E] [Module ℂ E] (t : List ι →₀ ℂ)
    (f : List ι → E) : ∑ w ∈ t.support, t w • f w = Finsupp.linearCombination ℂ f t := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]

/-- The letters spanned with coefficients. -/
def fE (σ : ι → K →L[ℂ] K) : (ι →₀ ℂ) →ₗ[ℂ] (K →L[ℂ] K) := Finsupp.linearCombination ℂ σ

omit [DecidableEq ι] in
lemma fE_apply (σ : ι → K →L[ℂ] K) (c : ι →₀ ℂ) : fE σ c = ∑ l, c l • σ l := by
  rw [fE, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  intro l; simp

lemma mOp_sub {n : ℕ} [CompleteSpace K] (M N : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K)) :
    mOp (M - N) = mOp M - mOp N :=
  map_sub (mOpHom (K := K) (n := n)) M N

omit [DecidableEq ι] in
lemma amp_shift [CompleteSpace K] [DecidableEq ι] (σ : ι → K →L[ℂ] K) (o : ι) (hσ : σ o = 1)
    {n : ℕ} (C : ι → Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    amp σ (fun l => C l - if l = o then s • (1 : Matrix (Fin n) (Fin n) ℂ) else 0) =
      amp σ C - s • (1 : PiLp 2 (fun _ : Fin n => K) →L[ℂ] PiLp 2 (fun _ : Fin n => K)) := by
  rw [amp_eq_mOp, amp_eq_mOp, ← mOp_one, ← mOp_smul, ← mOp_sub]
  congr 1
  refine CStarMatrix.ext fun a b => ?_
  change ∑ l, (C l - if l = o then s • (1 : Matrix (Fin n) (Fin n) ℂ) else 0) a b • σ l =
    (∑ l, C l a b • σ l) - s • (if a = b then (1 : K →L[ℂ] K) else 0)
  have hl : ∀ l, (C l - if l = o then s • (1 : Matrix (Fin n) (Fin n) ℂ) else 0) a b • σ l =
      C l a b • σ l - if l = o then s • (if a = b then (1 : K →L[ℂ] K) else 0) else 0 := by
    intro l
    by_cases hlo : l = o
    · subst hlo
      by_cases hab : a = b
      · simp [hab, hσ, sub_smul]
      · simp [hab, sub_smul, Matrix.one_apply_ne hab]
    · simp [hlo]
  simp only [hl, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Words

section System

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {e : ι → L →L[ℂ] L} {ρ : ι → H →L[ℂ] H}

omit [Fintype ι] [DecidableEq ι] [CompleteSpace L] [CompleteSpace H] in
lemma rel_words (hrel : RespectsRel e ρ) (v w : List ι) (h : evalW e v = evalW e w) :
    evalW ρ v = evalW ρ w := by
  classical
  have := hrel (Finsupp.single v 1 - Finsupp.single w 1) (by
    rw [sum_support_eq]; simp [h])
  rw [sum_support_eq] at this
  simpa [sub_eq_zero] using this

omit [Fintype ι] [DecidableEq ι] [CompleteSpace L] [CompleteSpace H] in
lemma rel_letters (hrel : RespectsRel e ρ) (c : ι →₀ ℂ)
    (h : Finsupp.linearCombination ℂ e c = 0) : Finsupp.linearCombination ℂ ρ c = 0 := by
  have := hrel (c.mapDomain fun l => [l]) (by
    rw [sum_support_eq, Finsupp.linearCombination_mapDomain, evalW_singleton]; exact h)
  rwa [sum_support_eq, Finsupp.linearCombination_mapDomain, evalW_singleton] at this

variable (e) in
/-- The operator system spanned by the letters. -/
def sysS : Submodule ℂ (L →L[ℂ] L) := LinearMap.range (fE e)

omit [Fintype ι] [DecidableEq ι] [CompleteSpace L] in
lemma mem_sysS (c : ι →₀ ℂ) : fE e c ∈ sysS e := LinearMap.mem_range_self _ _

omit [Fintype ι] [DecidableEq ι] [CompleteSpace L] [CompleteSpace H] in
lemma ker_le (hrel : RespectsRel e ρ) : LinearMap.ker (fE e) ≤ LinearMap.ker (fE ρ) :=
  fun c hc => rel_letters hrel c hc

variable (e ρ) in
/-- `φ (e l) = ρ l`, extended linearly. -/
def sysPhi (hrel : RespectsRel e ρ) : sysS e →ₗ[ℂ] (H →L[ℂ] H) :=
  ((LinearMap.ker (fE e)).liftQ (fE ρ) (ker_le hrel)).comp
    (fE e).quotKerEquivRange.symm.toLinearMap

omit [Fintype ι] [DecidableEq ι] [CompleteSpace L] [CompleteSpace H] in
lemma sysPhi_apply (hrel : RespectsRel e ρ) (c : ι →₀ ℂ) (hc : fE e c ∈ sysS e) :
    sysPhi e ρ hrel ⟨fE e c, hc⟩ = fE ρ c := by
  have h := LinearMap.quotKerEquivRange_symm_apply_image (fE e) c hc
  change ((LinearMap.ker (fE e)).liftQ (fE ρ) (ker_le hrel))
    ((fE e).quotKerEquivRange.symm ⟨fE e c, hc⟩) = fE ρ c
  rw [h]
  rfl

lemma rho_o (hU : UnitaryLetters e) (hrel : RespectsRel e ρ) : ρ hU.o = 1 := by
  have := rel_words hrel [hU.o] [] (by simp [evalW, hU.e_o])
  simpa [evalW] using this

omit [DecidableEq ι] [CompleteSpace H] in
lemma sysS_one (hU : UnitaryLetters e) : (1 : L →L[ℂ] L) ∈ sysS e :=
  ⟨Finsupp.single hU.o 1, by simp [fE, hU.e_o]⟩

omit [DecidableEq ι] [CompleteSpace H] in
lemma sysS_star (hU : UnitaryLetters e) (a : L →L[ℂ] L) (ha : a ∈ sysS e) :
    star a ∈ sysS e := by
  rw [sysS, fE, Finsupp.range_linearCombination] at ha ⊢
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [← hU.e_inv]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

lemma sysPhi_one (hU : UnitaryLetters e) (hrel : RespectsRel e ρ) :
    sysPhi e ρ hrel ⟨1, sysS_one hU⟩ = 1 := by
  have h1 : fE e (Finsupp.single hU.o 1) = 1 := by simp [fE, hU.e_o]
  have : (⟨1, sysS_one hU⟩ : sysS e) = ⟨fE e (Finsupp.single hU.o 1), mem_sysS _⟩ :=
    Subtype.ext h1.symm
  rw [this, sysPhi_apply]
  simp [fE, rho_o hU hrel]

/-- Positivity of `φ` at every matrix level. -/
lemma sysPhi_pos (hU : UnitaryLetters e) (hρ : CC e ρ) (hrel : RespectsRel e ρ) (n : ℕ)
    (X : operatorSystemMatrices (sysS e) n)
    (hX : 0 ≤ (X : CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L))) :
    0 ≤ operatorSystemAmplification (sysS e) (sysPhi e ρ hrel) n X := by
  have hmem : ∀ a b, ∃ c, fE e c = (X : CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L)) a b :=
    fun a b => LinearMap.mem_range.mp (X.2 a b)
  choose c hc using hmem
  let C : ι → Matrix (Fin n) (Fin n) ℂ := fun l a b => c a b l
  have hXeq : (X : CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L)) =
      CStarMatrix.ofMatrix fun a b => ∑ l, C l a b • e l := by
    refine CStarMatrix.ext fun a b => ?_
    rw [← hc a b, fE_apply]
    rfl
  have hZeq : operatorSystemAmplification (sysS e) (sysPhi e ρ hrel) n X =
      CStarMatrix.ofMatrix fun a b => ∑ l, C l a b • ρ l := by
    refine CStarMatrix.ext fun a b => ?_
    change sysPhi e ρ hrel ⟨X.val a b, X.property a b⟩ = ∑ l, C l a b • ρ l
    have : (⟨X.val a b, X.property a b⟩ : sysS e) = ⟨fE e (c a b), mem_sysS _⟩ :=
      Subtype.ext (hc a b).symm
    rw [this, sysPhi_apply, fE_apply]
  apply nonneg_of_mOp_nonneg
  rw [hZeq, ← amp_eq_mOp]
  have hP : 0 ≤ amp e C := by
    rw [amp_eq_mOp, ← hXeq]
    exact mOp_nonneg hX
  apply pos_of_shift_le _ hP
  intro s
  have := hρ n (fun l => C l - if l = hU.o then s • (1 : Matrix (Fin n) (Fin n) ℂ) else 0)
  rwa [amp_shift ρ hU.o (rho_o hU hrel), amp_shift e hU.o hU.e_o] at this

end System

/-- Lemma 10 (Pisier's endgame, via Arveson's extension theorem and Stinespring): a completely
contractive letter map respecting the relations of unitary letters is completely contractive on
all polynomials. -/
theorem endgame (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ι → H →L[ℂ] H) (hρ : CC e ρ) (hrel : RespectsRel e ρ) {n : ℕ}
    (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) :
    ‖evalP ρ y‖ ≤ ‖evalP e y‖ := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have : evalP ρ y = 0 := by
      ext x i
      exact Subsingleton.elim _ _
    rw [this, norm_zero]
    exact norm_nonneg _
  obtain ⟨Φ, hΦ1, -, hΦext⟩ := exists_unital_completelyPositive_extension (sysS e)
    (sysS_one hU) (sysS_star hU) (sysPhi e ρ hrel) (sysPhi_one hU hrel)
    (sysPhi_pos hU hρ hrel)
  have hΦe : ∀ l, Φ (e l) = ρ l := by
    intro l
    have h := hΦext ⟨fE e (Finsupp.single l 1), mem_sysS _⟩
    rw [sysPhi_apply] at h
    simpa [fE] using h
  have hinv : ∀ l, ρ (hU.inv l) = star (ρ l) := by
    intro l
    rw [← hΦe, ← hΦe, hU.e_inv, cp_star]
  have hρu : ∀ l, ρ l * star (ρ l) = 1 := by
    intro l
    rw [← hinv]
    have := rel_words hrel [l, hU.inv l] [] (by
      simp [evalW, hU.e_inv, Unitary.mul_star_self_of_mem (hU.unitary l)])
    simpa [evalW] using this
  have hmd : ∀ l (b : L →L[ℂ] L), Φ (e l * b) = ρ l * Φ b := by
    intro l b
    rw [cp_mult Φ hΦ1 (e l) (Unitary.mul_star_self_of_mem (hU.unitary l))
      (by rw [hΦe]; exact hρu l), hΦe]
  have hword : ∀ (w : List ι) (b : L →L[ℂ] L), Φ (evalW e w * b) = evalW ρ w * Φ b := by
    intro w
    induction w with
    | nil => intro b; simp [evalW_nil]
    | cons l w ih =>
      intro b
      rw [evalW_cons, evalW_cons, mul_assoc, hmd, ih, mul_assoc]
  have hword1 : ∀ w, Φ (evalW e w) = evalW ρ w := fun w => by
    simpa [hΦ1] using hword w 1
  have hstarW : ∀ w : List ι, star (evalW e w) = evalW e ((w.map hU.inv).reverse) := by
    intro w
    induction w with
    | nil => simp [evalW]
    | cons l w ih =>
      rw [evalW_cons, star_mul, ih, List.map_cons, List.reverse_cons, evalW_append,
        ← hU.e_inv]
      simp [evalW]
  set W := Submodule.span ℂ (Set.range (evalW e)) with hW
  have hWmd : ∀ a ∈ W, ∀ b, Φ (a * b) = Φ a * Φ b := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro b
      rw [hword, hword1]
    | zero => intro b; simp
    | add x z _ _ hx hz => intro b; rw [add_mul, map_add, map_add, hx, hz, add_mul]
    | smul c x _ hx => intro b; rw [smul_mul_assoc, map_smul, map_smul, hx, smul_mul_assoc]
  have hWstar : ∀ a ∈ W, star a ∈ W := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      rw [hstarW]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx
  let M : CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L) :=
    CStarMatrix.ofMatrix fun a b => ∑ w ∈ y.support, y w a b • evalW e w
  have hMW : ∀ a b, M a b ∈ W := fun a b =>
    Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
  let N : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) := M.map Φ
  have hX : evalP e y = mOp M := evalP_eq_mOp e y
  have hY : evalP ρ y = mOp N := by
    rw [evalP_eq_mOp]
    congr 1
    refine CStarMatrix.ext fun a b => ?_
    change ∑ w ∈ y.support, y w a b • evalW ρ w = Φ (∑ w ∈ y.support, y w a b • evalW e w)
    simp [map_sum, map_smul, hword1]
  have hNN : star N * N = (star M * M).map Φ := by
    refine CStarMatrix.ext fun a b => ?_
    change ∑ k, star (Φ (M k a)) * Φ (M k b) = Φ (∑ k, star (M k a) * M k b)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hWmd _ (hWstar _ (hMW k a)), cp_star]
  set r : ℝ := ‖M‖ ^ 2 with hr
  have hP : 0 ≤ algebraMap ℝ (CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L)) r - star M * M :=
    sub_nonneg.mpr CStarAlgebra.star_mul_le_algebraMap_norm_sq
  have hPΦ := Φ.map_cstarMatrix_nonneg _ hP
  have hPeq : (algebraMap ℝ (CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L)) r - star M * M).map Φ =
      (r : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) - star N * N := by
    rw [hNN]
    refine CStarMatrix.ext fun a b => ?_
    change Φ ((algebraMap ℝ (CStarMatrix (Fin n) (Fin n) (L →L[ℂ] L)) r) a b -
        (star M * M) a b) =
      (r : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) a b - Φ ((star M * M) a b)
    rw [map_sub]
    congr 1
    rw [CStarMatrix.algebraMap_apply, CStarMatrix.one_apply]
    split_ifs with hab
    · rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, hΦ1]
    · simp
  have hpos := mOp_nonneg hPΦ
  rw [hPeq, mOp_sub, mOp_smul, mOp_one, mOp_mul, mOp_star] at hpos
  rw [hY, hX, norm_mOp M]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hx := ((ContinuousLinearMap.isPositive_iff_complex _).mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos) x).2
  have hcalc : inner ℂ ((((r : ℂ) • 1 - star (mOp N) * mOp N :
      PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))) x) x =
      ((r * ‖x‖ ^ 2 - ‖mOp N x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply, inner_sub_left,
      inner_smul_left]
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp [Complex.conj_ofReal]
  rw [hcalc, RCLike.re_to_complex, Complex.ofReal_re] at hx
  have h2 : ‖mOp N x‖ ^ 2 ≤ (‖M‖ * ‖x‖) ^ 2 := by
    rw [mul_pow, ← hr]; linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2

end StrongConv.S9.Pisier.PartE
end
end

section
/-!
# Part A: bookkeeping stubs

`freeLetters_none`, `freeLetters_inv`, `freeLetters_mem_unitary` (the free letters are `1`,
`sᵢ`, `sᵢ*`, and `sᵢ = λ(gᵢ)` is unitary), and `pairing_le` (a represented functional is a matrix
coefficient of `evalP`, hence bounded by its norm).
-/

noncomputable section

namespace StrongConv.S9.Pisier.PartA

open scoped InnerProductSpace

/-! ## The free letters -/

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    (leftReg g f) h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg g * leftReg g' = leftReg (g * g') := by
  ext f h
  simp only [ContinuousLinearMap.mul_apply, leftReg_apply, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma leftReg_norm {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) : ‖leftReg g f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.mulLeft g⁻¹).tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal)

lemma leftReg_mem_unitary {d : ℕ} (g : FreeGroup (Fin d)) :
    leftReg g ∈ unitary (L2Free d →L[ℂ] L2Free d) := by
  let u : (L2Free d →L[ℂ] L2Free d)ˣ :=
    { val := leftReg g
      inv := leftReg g⁻¹
      val_inv := by rw [leftReg_mul, mul_inv_cancel, leftReg_one]
      inv_val := by rw [leftReg_mul, inv_mul_cancel, leftReg_one] }
  refine IsUnit.mem_unitary_of_star_mul_self ⟨u, rfl⟩ ?_
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (leftReg_norm g)

theorem freeLetters_none (d : ℕ) : freeLetters d none = 1 := by
  simp [freeLetters, wordEval]

theorem freeLetters_inv (d : ℕ) (l : Letter d) :
    freeLetters d (letterInv l) = star (freeLetters d l) := by
  rcases l with _ | i | i
  · simp [freeLetters, wordEval, letterInv]
  · simp [freeLetters, wordEval, letterInv, letterOp]
  · simp [freeLetters, wordEval, letterInv, letterOp]

theorem freeLetters_mem_unitary (d : ℕ) (l : Letter d) :
    freeLetters d l ∈ unitary (L2Free d →L[ℂ] L2Free d) := by
  rcases l with _ | i | i
  · simp [freeLetters, wordEval]
  · simpa [freeLetters, wordEval, letterOp, sLimit] using leftReg_mem_unitary (FreeGroup.of i)
  · simpa [freeLetters, wordEval, letterOp, sLimit] using
      Unitary.star_mem (leftReg_mem_unitary (FreeGroup.of i))

/-! ## The pairing bound -/

section Pairing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma tOp_apply {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (T : K →L[ℂ] K)
    (x : PiLp 2 (fun _ : Fin n => K)) (a : Fin n) :
    tOp A T x a = ∑ b, A a b • T (x b) := by
  simp only [tOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp [Pi.single_apply, Finset.sum_apply]

/-- The pairing of a represented functional is a matrix coefficient of `evalP`, hence bounded by
its norm (Cauchy–Schwarz). -/
theorem pairing_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ι → H →L[ℂ] H) {n : ℕ} (F : List ι → Matrix (Fin n) (Fin n) ℂ) (ξ η : Fin n → H)
    (hξ : ∑ j, ‖ξ j‖ ^ 2 ≤ 1) (hη : ∑ i, ‖η i‖ ^ 2 ≤ 1)
    (hF : ∀ (w : List ι) (i j : Fin n), ⟪η i, evalW ρ w (ξ j)⟫_ℂ = F w i j)
    (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) :
    ‖pairing F y‖ ≤ ‖evalP ρ y‖ := by
  set X : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 ξ
  set Y : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 η
  have hX : ‖X‖ ≤ 1 := by
    rw [PiLp.norm_eq_of_L2]
    exact Real.sqrt_le_one.mpr hξ
  have hY : ‖Y‖ ≤ 1 := by
    rw [PiLp.norm_eq_of_L2]
    exact Real.sqrt_le_one.mpr hη
  have heq : pairing F y = ⟪Y, evalP ρ y X⟫_ℂ := by
    simp only [pairing, evalP, PiLp.inner_apply, ContinuousLinearMap.sum_apply,
      tOp_apply, inner_sum, inner_smul_right, X, Y]
    simp only [hF]
  rw [heq]
  calc ‖⟪Y, evalP ρ y X⟫_ℂ‖ ≤ ‖Y‖ * ‖evalP ρ y X‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖evalP ρ y‖ * 1) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
    _ = ‖evalP ρ y‖ := by ring

end Pairing

end StrongConv.S9.Pisier.PartA
end
end

section
noncomputable section

namespace StrongConv.S9.Pisier

open scoped InnerProductSpace

alias shift_average := PartS.shift_average
alias coherent_limit := PartL.coherent_limit
alias compress := PartC.compress
alias endgame := PartE.endgame
alias pairing_le := PartA.pairing_le
alias freeLetters_none := PartA.freeLetters_none
alias freeLetters_inv := PartA.freeLetters_inv
alias freeLetters_mem_unitary := PartA.freeLetters_mem_unitary

section Letters
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- The analytic core: a coefficient functional bounded by `1` on contractive chains is bounded
by the operator norm on every polynomial. -/
theorem core_bound (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {n : ℕ}
    (F : List ι → Matrix (Fin n) (Fin n) ℂ) (hF : ChainBound e F) (hrel : FRel e F)
    (y : List ι →₀ Matrix (Fin n) (Fin n) ℂ) :
    ‖pairing F y‖ ≤ ‖evalP e y‖ := by
  obtain ⟨K, _, _, _, φ, ξ, η, hφ, hξ, hη, hK⟩ :=
    coherent_limit e hU F (fun M => shift_average e hU F hF hrel M)
  obtain ⟨H, _, _, _, ρ, ξ', η', hρ, hρrel, hξ', hη', hH⟩ :=
    compress e hU F hrel φ ξ η hφ hξ hη hK
  exact (pairing_le ρ F ξ' η' hξ' hη' hH y).trans (endgame e hU ρ hρ hρrel y)

end Letters

def freeLetters_unitary (d : ℕ) : UnitaryLetters (freeLetters d) where
  o := none
  e_o := freeLetters_none d
  inv := letterInv
  e_inv := freeLetters_inv d
  unitary := freeLetters_mem_unitary d

end StrongConv.S9.Pisier
end
end

section
/-!
# PartF helpers: algebra and norms of `tOp` and `amp`
-/

noncomputable section

open scoped InnerProductSpace
open Matrix

namespace StrongConv.S9.Pisier.PartF

section Ops

variable {H₁ H₂ H₃ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃]

lemma tOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂)
    (x : PiLp 2 (fun _ : Fin n => H₁)) (a : Fin m) :
    tOp A T x a = ∑ b, A a b • T (x b) := by
  simp only [tOp]
  simp [Pi.single_apply, Finset.sum_ite_eq']

lemma tOp_add {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    tOp (A + B) T = tOp A T + tOp B T := by
  ext x a
  simp [tOp_apply, add_smul, Finset.sum_add_distrib]

lemma tOp_smul {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    tOp (c • A) T = c • tOp A T := by
  ext x a
  simp [tOp_apply, Finset.smul_sum, smul_smul]

@[simp] lemma tOp_zero {m n : ℕ} (T : H₁ →L[ℂ] H₂) :
    tOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  ext x a
  simp [tOp_apply]

lemma tOp_sum {m n : ℕ} {β : Type*} (s : Finset β) (A : β → Matrix (Fin m) (Fin n) ℂ)
    (T : H₁ →L[ℂ] H₂) : tOp (∑ k ∈ s, A k) T = ∑ k ∈ s, tOp (A k) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, tOp_add, ih]

lemma tOp_add_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (S T : H₁ →L[ℂ] H₂) :
    tOp A (S + T) = tOp A S + tOp A T := by
  ext x a
  simp [tOp_apply, smul_add, Finset.sum_add_distrib]

lemma tOp_smul_right {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    tOp A (c • T) = c • tOp A T := by
  ext x a
  simp [tOp_apply, Finset.smul_sum, smul_smul, mul_comm]

@[simp] lemma tOp_zero_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    tOp A (0 : H₁ →L[ℂ] H₂) = 0 := by
  ext x a
  simp [tOp_apply]

lemma tOp_sum_right {m n : ℕ} {β : Type*} (s : Finset β) (A : Matrix (Fin m) (Fin n) ℂ)
    (T : β → H₁ →L[ℂ] H₂) : tOp A (∑ k ∈ s, T k) = ∑ k ∈ s, tOp A (T k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, tOp_add_right, ih]

lemma tOp_comp {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (S : H₂ →L[ℂ] H₃) (T : H₁ →L[ℂ] H₂) :
    (tOp A S).comp (tOp B T) = tOp (A * B) (S.comp T) := by
  ext x a
  simp only [ContinuousLinearMap.comp_apply, tOp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

lemma tOp_one_one {n : ℕ} :
    tOp (1 : Matrix (Fin n) (Fin n) ℂ) (ContinuousLinearMap.id ℂ H₁) =
      ContinuousLinearMap.id ℂ _ := by
  ext x a
  simp only [tOp_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma tOp_eq_sum_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H₁ →L[ℂ] H₂) :
    tOp A T = ∑ i, ∑ j, A i j • tOp (Matrix.single i j (1 : ℂ)) T := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [tOp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tOp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tOp_smul, Matrix.smul_single, smul_eq_mul, mul_one]

end Ops

section Norms

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

lemma opNorm_le_of_sq {m n : ℕ}
    (T : PiLp 2 (fun _ : Fin n => H₁) →L[ℂ] PiLp 2 (fun _ : Fin m => H₂)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : PiLp 2 (fun _ : Fin n => H₁), ∑ a, ‖T x a‖ ^ 2 ≤ C ^ 2 * ∑ b, ‖x b‖ ^ 2) :
    ‖T‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  exact h x

/-- A scalar contraction amplified to vectors is a contraction (rectangular version of PartD's
`amp1`). -/
lemma amp1R {m n : ℕ} (β : Matrix (Fin m) (Fin n) ℂ)
    (hβ : ∀ x : Fin n → ℂ, ∑ a, ‖(β *ᵥ x) a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2) (ζ : Fin n → H₂) :
    ∑ a, ‖∑ b, β a b • ζ b‖ ^ 2 ≤ ∑ b, ‖ζ b‖ ^ 2 := by
  classical
  let W : Submodule ℂ H₂ := Submodule.span ℂ (Set.range ζ)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ζ)
  let bW := stdOrthonormalBasis ℂ W
  let ζ' : Fin n → W := fun b => ⟨ζ b, Submodule.subset_span ⟨b, rfl⟩⟩
  have hn : ∀ w : W, ‖(w : H₂)‖ ^ 2 = ∑ k, ‖⟪bW k, w⟫_ℂ‖ ^ 2 := fun w => by
    rw [show ‖(w : H₂)‖ = ‖w‖ from rfl, OrthonormalBasis.sum_sq_norm_inner_right]
  have h1 : ∀ a, ∑ b, β a b • ζ b = ((∑ b, β a b • ζ' b : W) : H₂) := by
    intro a; simp [ζ']
  calc ∑ a, ‖∑ b, β a b • ζ b‖ ^ 2
      = ∑ a, ∑ k, ‖(β *ᵥ fun b => ⟪bW k, ζ' b⟫_ℂ) a‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [h1, hn]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [mulVec, dotProduct, inner_sum, inner_smul_right]
    _ = ∑ k, ∑ a, ‖(β *ᵥ fun b => ⟪bW k, ζ' b⟫_ℂ) a‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ k, ∑ b, ‖⟪bW k, ζ' b⟫_ℂ‖ ^ 2 := Finset.sum_le_sum fun k _ => hβ _
    _ = ∑ b, ‖ζ b‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hn]

lemma tOp_id_norm_le {m n : ℕ} (β : Matrix (Fin m) (Fin n) ℂ)
    (hβ : ∀ x : Fin n → ℂ, ∑ a, ‖(β *ᵥ x) a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2) :
    ‖tOp β (ContinuousLinearMap.id ℂ H₂)‖ ≤ 1 := by
  refine opNorm_le_of_sq _ 1 zero_le_one fun x => ?_
  simp only [tOp_apply, ContinuousLinearMap.id_apply, one_pow, one_mul]
  exact amp1R β hβ _

lemma sq_le_of_sNorm {m n : ℕ} (β : Matrix (Fin m) (Fin n) ℂ) (h : sNorm β ≤ 1) :
    ∀ x : Fin n → ℂ, ∑ a, ‖(β *ᵥ x) a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2 := by
  intro x
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin β)).le_opNorm
    (WithLp.toLp 2 x)
  have h2 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin β)) (WithLp.toLp 2 x)‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ := by
    refine h1.trans ?_
    calc _ ≤ 1 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ := by
          gcongr; exact h
      _ = _ := one_mul _
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at h3
  simpa using h3

lemma tOp_one_norm_le {n : ℕ} (T : H₁ →L[ℂ] H₂) :
    ‖tOp (1 : Matrix (Fin n) (Fin n) ℂ) T‖ ≤ ‖T‖ := by
  refine opNorm_le_of_sq _ _ (norm_nonneg _) fun x => ?_
  have : ∀ a, tOp (1 : Matrix (Fin n) (Fin n) ℂ) T x a = T (x a) := by
    intro a
    rw [tOp_apply, Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [this, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2

end Norms

end StrongConv.S9.Pisier.PartF
end
end

section
/-!
# PartF helpers: two-block decompositions of `Fin (K₁ + K₂)`
-/

noncomputable section

open scoped InnerProductSpace
open Matrix

namespace StrongConv.S9.Pisier.PartF

/-- The coordinate projection onto the first block. -/
def P1 (K₁ K₂ : ℕ) : Matrix (Fin K₁) (Fin (K₁ + K₂)) ℂ :=
  Matrix.of fun k k' => if k' = Fin.castAdd K₂ k then 1 else 0

/-- The coordinate projection onto the second block. -/
def P2 (K₁ K₂ : ℕ) : Matrix (Fin K₂) (Fin (K₁ + K₂)) ℂ :=
  Matrix.of fun k k' => if k' = Fin.natAdd K₁ k then 1 else 0

lemma P1_mul_P1H (K₁ K₂ : ℕ) : P1 K₁ K₂ * (P1 K₁ K₂)ᴴ = 1 := by
  ext i j
  simp only [P1, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.castAdd K₂ i)]
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Fin.castAdd_inj]
  · intro b _ hb; simp [hb]
  · simp

lemma P1_mul_P2H (K₁ K₂ : ℕ) : P1 K₁ K₂ * (P2 K₁ K₂)ᴴ = 0 := by
  ext i j
  simp only [P1, P2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : b = Fin.castAdd K₂ i
  · subst h
    have : Fin.castAdd K₂ i ≠ Fin.natAdd K₁ j := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    simp [this]
  · simp [h]

lemma P2_mul_P1H (K₁ K₂ : ℕ) : P2 K₁ K₂ * (P1 K₁ K₂)ᴴ = 0 := by
  have := congrArg Matrix.conjTranspose (P1_mul_P2H K₁ K₂)
  simpa [Matrix.conjTranspose_mul] using this

lemma P2_mul_P2H (K₁ K₂ : ℕ) : P2 K₁ K₂ * (P2 K₁ K₂)ᴴ = 1 := by
  ext i j
  simp only [P2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.natAdd K₁ i)]
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Fin.natAdd_inj]
  · intro b _ hb; simp [hb]
  · simp

section Ops

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "Id" => ContinuousLinearMap.id ℂ H

lemma pi1_apply {K₁ K₂ : ℕ} (x : PiLp 2 (fun _ : Fin (K₁ + K₂) => H)) (k : Fin K₁) :
    tOp (P1 K₁ K₂) Id x k = x (Fin.castAdd K₂ k) := by
  rw [tOp_apply, Finset.sum_eq_single (Fin.castAdd K₂ k)]
  · simp [P1]
  · intro b _ hb; simp [P1, hb]
  · simp

lemma pi2_apply {K₁ K₂ : ℕ} (x : PiLp 2 (fun _ : Fin (K₁ + K₂) => H)) (k : Fin K₂) :
    tOp (P2 K₁ K₂) Id x k = x (Fin.natAdd K₁ k) := by
  rw [tOp_apply, Finset.sum_eq_single (Fin.natAdd K₁ k)]
  · simp [P2]
  · intro b _ hb; simp [P2, hb]
  · simp

lemma iota1_apply_castAdd {K₁ K₂ : ℕ} (u : PiLp 2 (fun _ : Fin K₁ => H)) (k : Fin K₁) :
    tOp (P1 K₁ K₂)ᴴ Id u (Fin.castAdd K₂ k) = u k := by
  rw [tOp_apply, Finset.sum_eq_single k]
  · simp [P1]
  · intro b _ hb; simp [P1, Fin.castAdd_inj, Ne.symm hb]
  · simp

lemma iota1_apply_natAdd {K₁ K₂ : ℕ} (u : PiLp 2 (fun _ : Fin K₁ => H)) (k : Fin K₂) :
    tOp (P1 K₁ K₂)ᴴ Id u (Fin.natAdd K₁ k) = 0 := by
  rw [tOp_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : Fin.natAdd K₁ k ≠ Fin.castAdd K₂ b := by
    intro h'; have := congrArg Fin.val h'; simp at this; omega
  simp [P1, this]

lemma iota2_apply_castAdd {K₁ K₂ : ℕ} (u : PiLp 2 (fun _ : Fin K₂ => H)) (k : Fin K₁) :
    tOp (P2 K₁ K₂)ᴴ Id u (Fin.castAdd K₂ k) = 0 := by
  rw [tOp_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : Fin.castAdd K₂ k ≠ Fin.natAdd K₁ b := by
    intro h'; have := congrArg Fin.val h'; simp at this; omega
  simp [P2, this]

lemma iota2_apply_natAdd {K₁ K₂ : ℕ} (u : PiLp 2 (fun _ : Fin K₂ => H)) (k : Fin K₂) :
    tOp (P2 K₁ K₂)ᴴ Id u (Fin.natAdd K₁ k) = u k := by
  rw [tOp_apply, Finset.sum_eq_single k]
  · simp [P2]
  · intro b _ hb; simp [P2, Fin.natAdd_inj, Ne.symm hb]
  · simp

lemma pyth_pi {K₁ K₂ : ℕ} (x : PiLp 2 (fun _ : Fin (K₁ + K₂) => H)) :
    ‖tOp (P1 K₁ K₂) Id x‖ ^ 2 + ‖tOp (P2 K₁ K₂) Id x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
  simp only [pi1_apply, pi2_apply]

lemma pyth_iota {K₁ K₂ : ℕ} (u : PiLp 2 (fun _ : Fin K₁ => H))
    (v : PiLp 2 (fun _ : Fin K₂ => H)) :
    ‖tOp (P1 K₁ K₂)ᴴ Id u + tOp (P2 K₁ K₂)ᴴ Id v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
  simp only [PiLp.add_apply, iota1_apply_castAdd, iota2_apply_castAdd, iota1_apply_natAdd,
    iota2_apply_natAdd, add_zero, zero_add]

/-- Block-diagonal operators are contractions when both blocks are. -/
lemma blockDiag_norm_le {K₁ K₂ : ℕ} (S₁ : PiLp 2 (fun _ : Fin K₁ => H) →L[ℂ] PiLp 2 (fun _ : Fin K₁ => H))
    (S₂ : PiLp 2 (fun _ : Fin K₂ => H) →L[ℂ] PiLp 2 (fun _ : Fin K₂ => H))
    (h₁ : ‖S₁‖ ≤ 1) (h₂ : ‖S₂‖ ≤ 1) :
    ‖(tOp (P1 K₁ K₂)ᴴ Id).comp (S₁.comp (tOp (P1 K₁ K₂) Id)) +
      (tOp (P2 K₁ K₂)ᴴ Id).comp (S₂.comp (tOp (P2 K₁ K₂) Id))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [pyth_iota, ← pyth_pi x]
  have a1 := S₁.le_opNorm (tOp (P1 K₁ K₂) Id x)
  have a2 := S₂.le_opNorm (tOp (P2 K₁ K₂) Id x)
  have b1 : ‖S₁ (tOp (P1 K₁ K₂) Id x)‖ ≤ ‖tOp (P1 K₁ K₂) Id x‖ :=
    a1.trans (mul_le_of_le_one_left (norm_nonneg _) h₁)
  have b2 : ‖S₂ (tOp (P2 K₁ K₂) Id x)‖ ≤ ‖tOp (P2 K₁ K₂) Id x‖ :=
    a2.trans (mul_le_of_le_one_left (norm_nonneg _) h₂)
  gcongr

/-- A row `[a A, b B]` of contractions with `‖a‖² + ‖b‖² ≤ 1` is a contraction. -/
lemma row_norm_le {K₁ K₂ D : ℕ}
    (A : PiLp 2 (fun _ : Fin K₁ => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))
    (B : PiLp 2 (fun _ : Fin K₂ => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (a b : ℂ) (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 1) :
    ‖a • A.comp (tOp (P1 K₁ K₂) Id) + b • B.comp (tOp (P2 K₁ K₂) Id)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  have hp := pyth_pi x
  set u := tOp (P1 K₁ K₂) Id x
  set v := tOp (P2 K₁ K₂) Id x
  have a1 : ‖A u‖ ≤ ‖u‖ := (A.le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  have a2 : ‖B v‖ ≤ ‖v‖ := (B.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
  calc ‖a • A u + b • B v‖ ≤ ‖a‖ * ‖u‖ + ‖b‖ * ‖v‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
        gcongr
    _ ≤ ‖x‖ := by
        have h0 : 0 ≤ ‖a‖ * ‖u‖ + ‖b‖ * ‖v‖ := by positivity
        rw [← sq_le_sq₀ h0 (norm_nonneg _), ← hp]
        nlinarith [sq_nonneg (‖a‖ * ‖v‖ - ‖b‖ * ‖u‖), norm_nonneg a, norm_nonneg b,
          sq_nonneg ‖u‖, sq_nonneg ‖v‖]

/-- A column `[a A; b B]` of contractions with `‖a‖² + ‖b‖² ≤ 1` is a contraction. -/
lemma col_norm_le {K₁ K₂ D : ℕ}
    (A : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin K₁ => H))
    (B : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin K₂ => H))
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (a b : ℂ) (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 1) :
    ‖a • (tOp (P1 K₁ K₂)ᴴ Id).comp A + b • (tOp (P2 K₁ K₂)ᴴ Id).comp B‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [← map_smul (tOp (P1 K₁ K₂)ᴴ Id) a (A x), ← map_smul (tOp (P2 K₁ K₂)ᴴ Id) b (B x),
    pyth_iota, norm_smul, norm_smul]
  have a1 : ‖A x‖ ≤ ‖x‖ := (A.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  have a2 : ‖B x‖ ≤ ‖x‖ := (B.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
  have c1 : (‖a‖ * ‖A x‖) ^ 2 ≤ ‖a‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [mul_pow]; gcongr
  have c2 : (‖b‖ * ‖B x‖) ^ 2 ≤ ‖b‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [mul_pow]; gcongr
  nlinarith [sq_nonneg ‖x‖]

end Ops

end StrongConv.S9.Pisier.PartF
end
end

section
/-!
# PartF helpers: the set of framed contractive chains is absolutely convex
-/

noncomputable section

open scoped InnerProductSpace
open Matrix

namespace StrongConv.S9.Pisier.PartF

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

local notation "Id" => ContinuousLinearMap.id ℂ L

/-- The letter matrix with `C` at the letter `l` and `0` elsewhere. -/
def letterAt (l : ι) {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℂ) : ι → Matrix (Fin m) (Fin n) ℂ :=
  fun l' => if l' = l then C else 0

lemma amp_letterAt (e : ι → L →L[ℂ] L) (l : ι) {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℂ) :
    amp e (letterAt l C) = tOp C (e l) := by
  unfold amp letterAt
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma amp_letterAt_one (e : ι → L →L[ℂ] L) (l : ι) (he : e l = 1) {K : ℕ} :
    amp e (letterAt l (1 : Matrix (Fin K) (Fin K) ℂ)) = 1 := by
  rw [amp_letterAt, he, ContinuousLinearMap.one_def, tOp_one_one]
  rfl

lemma norm_le_one_of_unitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) : ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with h | h
  · rw [Subsingleton.elim U 0, norm_zero]; exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hU).le

/-- A framed chain: `C X₁ ⋯ X_M R` with contractive frames and contractive linear factors. -/
def IsChain (e : ι → L →L[ℂ] L) {D : ℕ}
    (S : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)) : Prop :=
  ∃ (K : ℕ) (C : Matrix (Fin D) (Fin K) ℂ) (Xs : List (ι → Matrix (Fin K) (Fin K) ℂ))
    (R : Matrix (Fin K) (Fin D) ℂ),
    ‖tOp C Id‖ ≤ 1 ∧ ‖tOp R Id‖ ≤ 1 ∧ (∀ X ∈ Xs, ‖amp e X‖ ≤ 1) ∧
      S = (tOp C Id).comp (((Xs.map (amp e)).prod).comp (tOp R Id))

lemma isChain_zero (e : ι → L →L[ℂ] L) {D : ℕ} :
    IsChain e (0 : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)) := by
  refine ⟨D, 0, [], 0, by simp, by simp, by simp, ?_⟩
  simp

/-- Padding a chain with identity factors. -/
lemma isChain_pad (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    {S : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)} (hS : IsChain e S) :
    ∃ (K : ℕ) (C : Matrix (Fin D) (Fin K) ℂ) (Xs : List (ι → Matrix (Fin K) (Fin K) ℂ))
      (R : Matrix (Fin K) (Fin D) ℂ),
      ‖tOp C Id‖ ≤ 1 ∧ ‖tOp R Id‖ ≤ 1 ∧ (∀ X ∈ Xs, ‖amp e X‖ ≤ 1) ∧
        S = (tOp C Id).comp (((Xs.map (amp e)).prod).comp (tOp R Id)) ∧
        ∀ N, ∃ Ys : List (ι → Matrix (Fin K) (Fin K) ℂ), Ys.length = Xs.length + N ∧
          (∀ X ∈ Ys, ‖amp e X‖ ≤ 1) ∧
          S = (tOp C Id).comp (((Ys.map (amp e)).prod).comp (tOp R Id)) := by
  obtain ⟨K, C, Xs, R, hC, hR, hX, rfl⟩ := hS
  refine ⟨K, C, Xs, R, hC, hR, hX, rfl, fun N => ?_⟩
  refine ⟨Xs ++ List.replicate N (letterAt o 1), by simp, ?_, ?_⟩
  · intro X hXm
    rcases List.mem_append.1 hXm with h | h
    · exact hX X h
    · rw [List.eq_of_mem_replicate h, amp_letterAt_one e o he]
      exact ContinuousLinearMap.norm_id_le
  · simp [List.map_replicate, amp_letterAt_one e o he]

/-- Block-diagonal letters. -/
def bd {K₁ K₂ : ℕ} (X : ι → Matrix (Fin K₁) (Fin K₁) ℂ) (Y : ι → Matrix (Fin K₂) (Fin K₂) ℂ) :
    ι → Matrix (Fin (K₁ + K₂)) (Fin (K₁ + K₂)) ℂ :=
  fun l => (P1 K₁ K₂)ᴴ * X l * P1 K₁ K₂ + (P2 K₁ K₂)ᴴ * Y l * P2 K₁ K₂

lemma tOp_sandwich {m n K : ℕ} (A : Matrix (Fin m) (Fin K) ℂ) (X : Matrix (Fin K) (Fin K) ℂ)
    (B : Matrix (Fin K) (Fin n) ℂ) (T : L →L[ℂ] L) :
    tOp (A * X * B) T = (tOp A Id).comp ((tOp X T).comp (tOp B Id)) := by
  rw [tOp_comp, tOp_comp, Matrix.mul_assoc]
  rfl

lemma amp_bd (e : ι → L →L[ℂ] L) {K₁ K₂ : ℕ} (X : ι → Matrix (Fin K₁) (Fin K₁) ℂ)
    (Y : ι → Matrix (Fin K₂) (Fin K₂) ℂ) :
    amp e (bd X Y) = (tOp (P1 K₁ K₂)ᴴ Id).comp ((amp e X).comp (tOp (P1 K₁ K₂) Id)) +
      (tOp (P2 K₁ K₂)ᴴ Id).comp ((amp e Y).comp (tOp (P2 K₁ K₂) Id)) := by
  unfold amp bd
  simp only [tOp_add, tOp_sandwich, Finset.sum_add_distrib,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp]

lemma pi1_comp_amp_bd (e : ι → L →L[ℂ] L) {K₁ K₂ : ℕ} (X : ι → Matrix (Fin K₁) (Fin K₁) ℂ)
    (Y : ι → Matrix (Fin K₂) (Fin K₂) ℂ) :
    (tOp (P1 K₁ K₂) Id).comp (amp e (bd X Y)) = (amp e X).comp (tOp (P1 K₁ K₂) Id) := by
  rw [amp_bd, ContinuousLinearMap.comp_add,
    ← ContinuousLinearMap.comp_assoc (tOp (P1 K₁ K₂) Id) (tOp (P1 K₁ K₂)ᴴ Id),
    ← ContinuousLinearMap.comp_assoc (tOp (P1 K₁ K₂) Id) (tOp (P2 K₁ K₂)ᴴ Id),
    tOp_comp, tOp_comp, P1_mul_P1H, P1_mul_P2H, tOp_zero]
  simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.zero_comp, add_zero]
  rw [tOp_one_one, ContinuousLinearMap.id_comp]

lemma pi2_comp_amp_bd (e : ι → L →L[ℂ] L) {K₁ K₂ : ℕ} (X : ι → Matrix (Fin K₁) (Fin K₁) ℂ)
    (Y : ι → Matrix (Fin K₂) (Fin K₂) ℂ) :
    (tOp (P2 K₁ K₂) Id).comp (amp e (bd X Y)) = (amp e Y).comp (tOp (P2 K₁ K₂) Id) := by
  rw [amp_bd, ContinuousLinearMap.comp_add,
    ← ContinuousLinearMap.comp_assoc (tOp (P2 K₁ K₂) Id) (tOp (P1 K₁ K₂)ᴴ Id),
    ← ContinuousLinearMap.comp_assoc (tOp (P2 K₁ K₂) Id) (tOp (P2 K₁ K₂)ᴴ Id),
    tOp_comp, tOp_comp, P2_mul_P1H, P2_mul_P2H, tOp_zero]
  simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.zero_comp, zero_add]
  rw [tOp_one_one, ContinuousLinearMap.id_comp]

lemma pi1_comp_prod (e : ι → L →L[ℂ] L) {K₁ K₂ : ℕ} :
    ∀ (Xs : List (ι → Matrix (Fin K₁) (Fin K₁) ℂ)) (Ys : List (ι → Matrix (Fin K₂) (Fin K₂) ℂ)),
      Xs.length = Ys.length →
      (tOp (P1 K₁ K₂) Id).comp (((List.zipWith bd Xs Ys).map (amp e)).prod) =
        ((Xs.map (amp e)).prod).comp (tOp (P1 K₁ K₂) Id)
  | [], [], _ => by simp [ContinuousLinearMap.one_def]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | X :: Xs, Y :: Ys, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, List.prod_cons,
      ContinuousLinearMap.mul_def]
    rw [← ContinuousLinearMap.comp_assoc, pi1_comp_amp_bd, ContinuousLinearMap.comp_assoc,
      pi1_comp_prod e Xs Ys (by simpa using h), ContinuousLinearMap.comp_assoc]

lemma pi2_comp_prod (e : ι → L →L[ℂ] L) {K₁ K₂ : ℕ} :
    ∀ (Xs : List (ι → Matrix (Fin K₁) (Fin K₁) ℂ)) (Ys : List (ι → Matrix (Fin K₂) (Fin K₂) ℂ)),
      Xs.length = Ys.length →
      (tOp (P2 K₁ K₂) Id).comp (((List.zipWith bd Xs Ys).map (amp e)).prod) =
        ((Ys.map (amp e)).prod).comp (tOp (P2 K₁ K₂) Id)
  | [], [], _ => by simp [ContinuousLinearMap.one_def]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | X :: Xs, Y :: Ys, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, List.prod_cons,
      ContinuousLinearMap.mul_def]
    rw [← ContinuousLinearMap.comp_assoc, pi2_comp_amp_bd, ContinuousLinearMap.comp_assoc,
      pi2_comp_prod e Xs Ys (by simpa using h), ContinuousLinearMap.comp_assoc]

lemma sqrt_split (a : ℂ) : ∃ a₁ a₂ : ℂ, a₁ * a₂ = a ∧ ‖a₁‖ ^ 2 = ‖a‖ ∧ ‖a₂‖ ^ 2 = ‖a‖ := by
  by_cases ha : a = 0
  · exact ⟨0, 0, by simp [ha], by simp [ha], by simp [ha]⟩
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  set α := Real.sqrt ‖a‖ with hα
  have hα0 : 0 < α := Real.sqrt_pos.2 hpos
  have hα2 : α ^ 2 = ‖a‖ := Real.sq_sqrt hpos.le
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα0.ne'
  refine ⟨(α : ℂ), a / (α : ℂ), ?_, ?_, ?_⟩
  · field_simp
  · rw [Complex.norm_real, Real.norm_of_nonneg hα0.le, hα2]
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hα0.le, div_pow, hα2]
    field_simp

lemma mem_zipWith_exists {α β γ : Type*} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β) (c : γ), c ∈ List.zipWith f l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, c = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l₁, b :: l₂, c, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨a, by simp, b, by simp, h⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWith_exists f l₁ l₂ c h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

/-- The set of framed chains is absolutely convex. -/
theorem isChain_absConvex (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    {S₁ S₂ : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)}
    (h₁ : IsChain e S₁) (h₂ : IsChain e S₂) (a b : ℂ) (hab : ‖a‖ + ‖b‖ ≤ 1) :
    IsChain e (a • S₁ + b • S₂) := by
  obtain ⟨K₁, C₁, Xs₀, R₁, hC₁, hR₁, -, -, hp₁⟩ := isChain_pad e o he h₁
  obtain ⟨K₂, C₂, Ys₀, R₂, hC₂, hR₂, -, -, hp₂⟩ := isChain_pad e o he h₂
  obtain ⟨Xs, hXl, hX, rfl⟩ := hp₁ Ys₀.length
  obtain ⟨Ys, hYl, hY, rfl⟩ := hp₂ Xs₀.length
  have hl : Xs.length = Ys.length := by omega
  obtain ⟨a₁, a₂, ha, ha₁, ha₂⟩ := sqrt_split a
  obtain ⟨b₁, b₂, hb, hb₁, hb₂⟩ := sqrt_split b
  set π₁ := tOp (P1 K₁ K₂) Id
  set π₂ := tOp (P2 K₁ K₂) Id
  set ι₁ := tOp (P1 K₁ K₂)ᴴ Id
  set ι₂ := tOp (P2 K₁ K₂)ᴴ Id
  have hCe : tOp (a₁ • (C₁ * P1 K₁ K₂) + b₁ • (C₂ * P2 K₁ K₂)) Id =
      a₁ • (tOp C₁ Id).comp π₁ + b₁ • (tOp C₂ Id).comp π₂ := by
    rw [tOp_add, tOp_smul, tOp_smul, tOp_comp, tOp_comp, ContinuousLinearMap.id_comp]
  have hRe : tOp (a₂ • ((P1 K₁ K₂)ᴴ * R₁) + b₂ • ((P2 K₁ K₂)ᴴ * R₂)) Id =
      a₂ • ι₁.comp (tOp R₁ Id) + b₂ • ι₂.comp (tOp R₂ Id) := by
    rw [tOp_add, tOp_smul, tOp_smul, tOp_comp, tOp_comp, ContinuousLinearMap.id_comp]
  have hR1 : π₁.comp (tOp (a₂ • ((P1 K₁ K₂)ᴴ * R₁) + b₂ • ((P2 K₁ K₂)ᴴ * R₂)) Id) =
      a₂ • tOp R₁ Id := by
    rw [tOp_comp, ContinuousLinearMap.id_comp, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, P1_mul_P1H, P1_mul_P2H, Matrix.one_mul,
      Matrix.zero_mul, smul_zero, add_zero, tOp_smul]
  have hR2 : π₂.comp (tOp (a₂ • ((P1 K₁ K₂)ᴴ * R₁) + b₂ • ((P2 K₁ K₂)ᴴ * R₂)) Id) =
      b₂ • tOp R₂ Id := by
    rw [tOp_comp, ContinuousLinearMap.id_comp, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, P2_mul_P1H, P2_mul_P2H, Matrix.one_mul,
      Matrix.zero_mul, smul_zero, zero_add, tOp_smul]
  refine ⟨K₁ + K₂, a₁ • (C₁ * P1 K₁ K₂) + b₁ • (C₂ * P2 K₁ K₂), List.zipWith bd Xs Ys,
    a₂ • ((P1 K₁ K₂)ᴴ * R₁) + b₂ • ((P2 K₁ K₂)ᴴ * R₂), ?_, ?_, ?_, ?_⟩
  · rw [hCe]
    exact row_norm_le _ _ hC₁ hC₂ a₁ b₁ (by rw [ha₁, hb₁]; exact hab)
  · rw [hRe]
    exact col_norm_le _ _ hR₁ hR₂ a₂ b₂ (by rw [ha₂, hb₂]; exact hab)
  · intro Z hZ
    obtain ⟨X, hXm, Y, hYm, rfl⟩ := mem_zipWith_exists bd Xs Ys Z hZ
    rw [amp_bd]
    exact blockDiag_norm_le _ _ (hX X hXm) (hY Y hYm)
  · rw [hCe, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc π₁,
      ← ContinuousLinearMap.comp_assoc π₂, pi1_comp_prod e Xs Ys hl, pi2_comp_prod e Xs Ys hl,
      ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hR1, hR2,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, smul_smul, smul_smul, ha, hb]

end StrongConv.S9.Pisier.PartF
end
end

section
/-!
# PartF helpers: framed chains are `gChainOn` products
-/

noncomputable section

open scoped InnerProductSpace
open Matrix

namespace StrongConv.S9.Pisier.PartF

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Reindexing copies along an equality of sizes. -/
def rc {a b : ℕ} (h : a = b) :
    PiLp 2 (fun _ : Fin a => L) →L[ℂ] PiLp 2 (fun _ : Fin b => L) :=
  reindexCopies (finCongr h)

omit [CompleteSpace L] in
lemma rc_self {a : ℕ} (h : a = a) : (rc h : PiLp 2 (fun _ : Fin a => L) →L[ℂ] _) =
    ContinuousLinearMap.id ℂ _ := by
  ext x i
  simp [rc, reindexCopies]

omit [CompleteSpace L] in
lemma rc_comp_rc {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) :
    (rc h₂ : PiLp 2 (fun _ : Fin b => L) →L[ℂ] _).comp (rc h₁) = rc (h₁.trans h₂) := by
  subst h₁ h₂
  simp only [rc_self, ContinuousLinearMap.id_comp]

omit [CompleteSpace L] in
lemma rc_comp_rc_comp {a b c : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (h₁ : a = b) (h₂ : b = c) (T : E →L[ℂ] PiLp 2 (fun _ : Fin a => L)) :
    (rc h₂ : PiLp 2 (fun _ : Fin b => L) →L[ℂ] _).comp ((rc h₁).comp T) =
      (rc (h₁.trans h₂)).comp T := by
  rw [← ContinuousLinearMap.comp_assoc, rc_comp_rc]

omit [CompleteSpace L] in
lemma reindexCopies_finCongr {a b : ℕ} (h : a = b) :
    (reindexCopies (finCongr h) : PiLp 2 (fun _ : Fin a => L) →L[ℂ] _) = rc h := rfl

omit [CompleteSpace L] in
lemma reindexCopies_symm_eq {a b : ℕ} (h : a = b) :
    (reindexCopies (finCongr h).symm : PiLp 2 (fun _ : Fin b => L) →L[ℂ] _) = rc h.symm := by
  rw [rc, finCongr_symm]

/-- Casting a matrix along equalities of sizes. -/
def castM {a a' b b' : ℕ} (h₁ : a = a') (h₂ : b = b') (M : Matrix (Fin a) (Fin b) ℂ) :
    Matrix (Fin a') (Fin b') ℂ :=
  M.submatrix (Fin.cast h₁.symm) (Fin.cast h₂.symm)

omit [CompleteSpace L] in
lemma amp_castM (e : ι → L →L[ℂ] L) {a a' b b' : ℕ} (h₁ : a = a') (h₂ : b = b')
    (X : ι → Matrix (Fin a) (Fin b) ℂ) :
    amp e (fun l => castM h₁ h₂ (X l)) = (rc h₁).comp ((amp e X).comp (rc h₂.symm)) := by
  subst h₁ h₂
  simp only [rc_self, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  rfl

omit [CompleteSpace L] in
lemma norm_amp_castM (e : ι → L →L[ℂ] L) {a a' b b' : ℕ} (h₁ : a = a') (h₂ : b = b')
    (X : ι → Matrix (Fin a) (Fin b) ℂ) :
    ‖amp e (fun l => castM h₁ h₂ (X l))‖ = ‖amp e X‖ := by
  subst h₁ h₂
  rfl

/-- Operators `L^m → L^D` that are chains of contractive linear factors (any length). -/
def RealC (e : ι → L →L[ℂ] L) {D m : ℕ}
    (T : PiLp 2 (fun _ : Fin m => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)) : Prop :=
  ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (h₁ : Dim 1 = D) (hq : Dim (1 + q) = m),
    T = (reindexCopies (finCongr h₁)).comp
        ((gChain e Dim A 1 q).comp (reindexCopies (finCongr hq).symm)) ∧
      ∀ j ∈ Finset.Icc 1 q, ‖amp e (A j)‖ ≤ 1

omit [CompleteSpace L] in
lemma realC_id (e : ι → L →L[ℂ] L) {D : ℕ} :
    RealC e (ContinuousLinearMap.id ℂ (PiLp 2 (fun _ : Fin D => L))) := by
  refine ⟨0, fun _ => D, fun _ _ => 0, rfl, rfl, ?_, by simp⟩
  rw [reindexCopies_symm_eq]
  show _ = (rc rfl).comp ((ContinuousLinearMap.id ℂ _).comp (rc rfl))
  simp only [rc_self]
  rfl

/-- The extended dimension function. -/
def appDim (Dim : ℕ → ℕ) (q m' : ℕ) (j : ℕ) : ℕ := if j ≤ 1 + q then Dim j else m'

lemma appDim_le {Dim : ℕ → ℕ} {q m' j : ℕ} (h : j ≤ 1 + q) : appDim Dim q m' j = Dim j := by
  simp [appDim, h]

lemma appDim_last {Dim : ℕ → ℕ} {q m' : ℕ} : appDim Dim q m' (1 + (q + 1)) = m' := by
  simp [appDim]

/-- The extended factor list. -/
def appA (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (q : ℕ) {m m' : ℕ} (hq : Dim (1 + q) = m) (X : ι → Matrix (Fin m) (Fin m') ℂ) :
    ∀ j : ℕ, ι → Matrix (Fin (appDim Dim q m' j)) (Fin (appDim Dim q m' (j + 1))) ℂ :=
  fun j =>
    if h : j + 1 ≤ 1 + q then
      fun l => castM (appDim_le (by omega)).symm (appDim_le h).symm (A j l)
    else if h' : j = 1 + q then
      fun l => castM (by subst h'; rw [appDim_le le_rfl, hq]) (by subst h'; exact appDim_last.symm)
        (X l)
    else 0

lemma appA_lt (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (q : ℕ) {m m' : ℕ} (hq : Dim (1 + q) = m) (X : ι → Matrix (Fin m) (Fin m') ℂ) (j : ℕ)
    (h : j + 1 ≤ 1 + q) :
    appA Dim A q hq X j = fun l => castM (appDim_le (by omega)).symm (appDim_le h).symm (A j l) := by
  simp only [appA, dif_pos h]

lemma appA_last (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (q : ℕ) {m m' : ℕ} (hq : Dim (1 + q) = m) (X : ι → Matrix (Fin m) (Fin m') ℂ) :
    appA Dim A q hq X (1 + q) = fun l => castM (by rw [appDim_le le_rfl, hq]) appDim_last.symm (X l) := by
  have h : ¬ (1 + q + 1 ≤ 1 + q) := by omega
  simp only [appA, dif_neg h, dif_pos]

omit [CompleteSpace L] in
lemma gChain_app (e : ι → L →L[ℂ] L) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (q : ℕ) {m m' : ℕ} (hq : Dim (1 + q) = m) (X : ι → Matrix (Fin m) (Fin m') ℂ) :
    ∀ k (hk : k ≤ q), gChain e (appDim Dim q m') (appA Dim A q hq X) 1 k =
      (rc (appDim_le (by omega)).symm).comp
        ((gChain e Dim A 1 k).comp (rc (appDim_le (by omega))))
  | 0, _ => by
    show ContinuousLinearMap.id ℂ _ = _
    rw [show gChain e Dim A 1 0 = ContinuousLinearMap.id ℂ _ from rfl,
      ContinuousLinearMap.id_comp, rc_comp_rc, rc_self]
  | k + 1, hk => by
    show (gChain e (appDim Dim q m') (appA Dim A q hq X) 1 k).comp
        (amp e (appA Dim A q hq X (1 + k))) = _
    rw [gChain_app e Dim A q hq X k (by omega), appA_lt Dim A q hq X (1 + k) (by omega),
      amp_castM]
    show _ = (rc _).comp (((gChain e Dim A 1 k).comp (amp e (A (1 + k)))).comp (rc _))
    simp only [ContinuousLinearMap.comp_assoc]
    rw [rc_comp_rc_comp, rc_self, ContinuousLinearMap.id_comp]

omit [CompleteSpace L] in
lemma realC_append (e : ι → L →L[ℂ] L) {D m m' : ℕ}
    {T : PiLp 2 (fun _ : Fin m => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)} (hT : RealC e T)
    (X : ι → Matrix (Fin m) (Fin m') ℂ) (hX : ‖amp e X‖ ≤ 1) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = m'),
      1 ≤ q ∧ T.comp (amp e X) = (reindexCopies (finCongr h₁)).comp
        ((gChain e Dim A 1 q).comp (reindexCopies (finCongr hq).symm)) ∧
      ∀ j ∈ Finset.Icc 1 q, ‖amp e (A j)‖ ≤ 1 := by
  obtain ⟨q, Dim, A, h₁, hq, rfl, hA⟩ := hT
  refine ⟨q + 1, appDim Dim q m', appA Dim A q hq X, (appDim_le (by omega)).trans h₁,
    appDim_last, by omega, ?_, ?_⟩
  · show _ = (reindexCopies (finCongr _)).comp
      (((gChain e (appDim Dim q m') (appA Dim A q hq X) 1 q).comp
        (amp e (appA Dim A q hq X (1 + q)))).comp (reindexCopies (finCongr _).symm))
    rw [gChain_app e Dim A q hq X q le_rfl, appA_last, amp_castM]
    simp only [reindexCopies_symm_eq, reindexCopies_finCongr, ContinuousLinearMap.comp_assoc]
    rw [rc_comp_rc_comp, rc_comp_rc_comp, rc_comp_rc, rc_self, ContinuousLinearMap.comp_id]
  · intro j hj
    rcases Finset.mem_Icc.1 hj with ⟨hj1, hj2⟩
    by_cases hjq : j ≤ q
    · rw [appA_lt Dim A q hq X j (by omega), norm_amp_castM]
      exact hA j (Finset.mem_Icc.2 ⟨hj1, hjq⟩)
    · have : j = 1 + q := by omega
      subst this
      rw [appA_last, norm_amp_castM]
      exact hX

omit [CompleteSpace L] in
lemma realC_append' (e : ι → L →L[ℂ] L) {D m m' : ℕ}
    {T : PiLp 2 (fun _ : Fin m => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)} (hT : RealC e T)
    (X : ι → Matrix (Fin m) (Fin m') ℂ) (hX : ‖amp e X‖ ≤ 1) : RealC e (T.comp (amp e X)) := by
  obtain ⟨q, Dim, A, h₁, hq, -, h, hA⟩ := realC_append e hT X hX
  exact ⟨q, Dim, A, h₁, hq, h, hA⟩

omit [CompleteSpace L] in
lemma realC_comp_prod (e : ι → L →L[ℂ] L) {D K : ℕ} :
    ∀ (Xs : List (ι → Matrix (Fin K) (Fin K) ℂ))
      (T : PiLp 2 (fun _ : Fin K => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)),
      RealC e T → (∀ X ∈ Xs, ‖amp e X‖ ≤ 1) → RealC e (T.comp ((Xs.map (amp e)).prod))
  | [], T, hT, _ => by simpa [ContinuousLinearMap.one_def] using hT
  | X :: Xs, T, hT, hX => by
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_def]
    rw [← ContinuousLinearMap.comp_assoc]
    exact realC_comp_prod e Xs _ (realC_append' e hT X (hX X (by simp)))
      (fun Y hY => hX Y (List.mem_cons_of_mem _ hY))

lemma isChain_gChainOn (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    {S : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)} (hS : IsChain e S) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ S = gChainOn e Dim A q h₁ hq ∧ ∀ j ∈ Finset.Icc 1 q, ‖amp e (A j)‖ ≤ 1 := by
  obtain ⟨K, C, Xs, R, hC, hR, hX, rfl⟩ := hS
  have hCa : amp e (letterAt o C) = tOp C (ContinuousLinearMap.id ℂ L) := by
    rw [amp_letterAt, he, ContinuousLinearMap.one_def]
  have hRa : amp e (letterAt o R) = tOp R (ContinuousLinearMap.id ℂ L) := by
    rw [amp_letterAt, he, ContinuousLinearMap.one_def]
  have h1 : RealC e (tOp C (ContinuousLinearMap.id ℂ L)) := by
    have := realC_append' e (realC_id e (D := D)) (letterAt o C) (by rw [hCa]; exact hC)
    rwa [ContinuousLinearMap.id_comp, hCa] at this
  have h2 := realC_comp_prod e Xs _ h1 hX
  obtain ⟨q, Dim, A, h₁, hq, hq1, h, hA⟩ :=
    realC_append e h2 (letterAt o R) (by rw [hRa]; exact hR)
  refine ⟨q, Dim, A, h₁, hq, hq1, ?_, hA⟩
  rw [hRa, ContinuousLinearMap.comp_assoc] at h
  exact h

end StrongConv.S9.Pisier.PartF
end
end

section
/-!
# PartF helpers: the span of the chains, monomials, and the expansion of chains
-/

noncomputable section

open scoped InnerProductSpace Pointwise
open Matrix

namespace StrongConv.S9.Pisier.PartF

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

local notation "Id" => ContinuousLinearMap.id ℂ L

lemma isChain_smul (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    {S : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)} (hS : IsChain e S)
    (a : ℂ) (ha : ‖a‖ ≤ 1) : IsChain e (a • S) := by
  have := isChain_absConvex e o he hS hS a 0 (by simpa using ha)
  have h0 : a • S + (0 : ℂ) • S = a • S :=
    (congrArg (a • S + ·) (zero_smul ℂ S)).trans (add_zero _)
  rwa [h0] at this

lemma real_smul_clm {D : ℕ} (a : ℝ)
    (T : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)) :
    a • T = (a : ℂ) • T := by
  ext z i
  simp [Complex.coe_smul]

/-- The operators that are positive multiples of framed chains. -/
def chainSpan (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) :
    Submodule ℂ (PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)) where
  carrier := {x | ∃ r : ℝ, 0 < r ∧ ∃ S, IsChain e S ∧ x = (r : ℂ) • S}
  zero_mem' := ⟨1, one_pos, 0, isChain_zero e, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr, S, hS, rfl⟩ ⟨r', hr', S', hS', rfl⟩
    have hrr : 0 < r + r' := by positivity
    refine ⟨r + r', hrr, ((r / (r + r') : ℝ) : ℂ) • S + ((r' / (r + r') : ℝ) : ℂ) • S',
      isChain_absConvex e o he hS hS' _ _ ?_, ?_⟩
    · rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity), ← add_div, div_self hrr.ne']
    · rw [smul_add, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        mul_div_cancel₀ _ hrr.ne', mul_div_cancel₀ _ hrr.ne']
  smul_mem' := by
    rintro a x ⟨r, hr, S, hS, rfl⟩
    have hpos : 0 < ‖a‖ * r + 1 := by positivity
    refine ⟨‖a‖ * r + 1, hpos, ((a * r) / ((‖a‖ * r + 1 : ℝ) : ℂ)) • S,
      isChain_smul e o he hS _ ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_le_one hpos]
      linarith
    · have hc : ((‖a‖ * r + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [smul_smul, smul_smul, mul_div_cancel₀ _ hc]

lemma mem_chainSpan_of_isChain (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    {S : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)} (hS : IsChain e S) :
    S ∈ chainSpan e o he D :=
  ⟨1, one_pos, S, hS, by simp⟩

omit [CompleteSpace L] in
lemma prod_map_tOp_one (e : ι → L →L[ℂ] L) {K : ℕ} :
    ∀ w : List ι, (w.map (fun l => tOp (1 : Matrix (Fin K) (Fin K) ℂ) (e l))).prod =
      tOp (1 : Matrix (Fin K) (Fin K) ℂ) (evalW e w)
  | [] => by
    simp only [List.map_nil, List.prod_nil, evalW, ContinuousLinearMap.one_def, tOp_one_one]
  | l :: w => by
    rw [List.map_cons, List.prod_cons, prod_map_tOp_one e w, ContinuousLinearMap.mul_def,
      tOp_comp, Matrix.one_mul]
    simp only [evalW, List.map_cons, List.prod_cons, ContinuousLinearMap.mul_def]

/-- Monomials `Eᵢⱼ ⊗ e(w)` are chains. -/
lemma isChain_mono (e : ι → L →L[ℂ] L) (he : ∀ l, ‖e l‖ ≤ 1) {D : ℕ} (i j : Fin D)
    (w : List ι) : IsChain e (tOp (Matrix.single i j (1 : ℂ)) (evalW e w)) := by
  refine ⟨1, Matrix.single i 0 1, w.map (fun l => letterAt l (1 : Matrix (Fin 1) (Fin 1) ℂ)),
    Matrix.single 0 j 1, ?_, ?_, ?_, ?_⟩
  · refine tOp_id_norm_le _ fun x => ?_
    rw [Matrix.single_mulVec, Fin.sum_univ_one, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · refine tOp_id_norm_le _ fun x => ?_
    rw [Matrix.single_mulVec, Fin.sum_univ_one]
    simp only [Function.update_self, one_mul]
    exact Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ j)
  · intro X hX
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hX
    rw [amp_letterAt]
    exact (tOp_one_norm_le _).trans (he l)
  · rw [List.map_map]
    have : (amp e ∘ fun l => letterAt l (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
        fun l => tOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (e l) := by
      funext l; simp [amp_letterAt]
    rw [this, prod_map_tOp_one, tOp_comp, tOp_comp, Matrix.one_mul,
      Matrix.single_mul_single_same, mul_one]
    rfl

omit [CompleteSpace L] in
/-- Expansion of a product of amplifications into words. -/
lemma prod_ofFn_amp (e : ι → L →L[ℂ] L) {K : ℕ} :
    ∀ (M : ℕ) (X : Fin M → ι → Matrix (Fin K) (Fin K) ℂ),
      ((List.ofFn X).map (amp e)).prod =
        ∑ w : Fin M → ι, tOp (prodX X w) (evalW e (List.ofFn w))
  | 0, X => by
    rw [Fintype.sum_unique]
    simp only [List.ofFn_zero, List.map_nil, List.prod_nil, prodX, evalW,
      ContinuousLinearMap.one_def, tOp_one_one]
  | M + 1, X => by
    rw [List.ofFn_succ, List.map_cons, List.prod_cons, prod_ofFn_amp e M,
      ← (Fin.consEquiv (fun _ : Fin (M + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    unfold amp
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun w _ => ?_
    rw [ContinuousLinearMap.mul_def, tOp_comp]
    simp only [Fin.consEquiv_apply, prodX, evalW, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.prod_cons, List.map_cons, ContinuousLinearMap.mul_def]

/-- A framed chain as in `ChainBound` is a chain. -/
lemma isChain_framed (e : ι → L →L[ℂ] L) {D M K : ℕ} (X : Fin M → ι → Matrix (Fin K) (Fin K) ℂ)
    (C : Matrix (Fin D) (Fin K) ℂ) (R : Matrix (Fin K) (Fin D) ℂ)
    (hX : ∀ l, ‖amp e (X l)‖ ≤ 1) (hC : sNorm C ≤ 1) (hR : sNorm R ≤ 1) :
    IsChain e ((tOp C Id).comp ((((List.ofFn X).map (amp e)).prod).comp (tOp R Id))) := by
  refine ⟨K, C, List.ofFn X, R, tOp_id_norm_le C (sq_le_of_sNorm C hC),
    tOp_id_norm_le R (sq_le_of_sNorm R hR), ?_, rfl⟩
  intro Y hY
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hY
  exact hX l

omit [CompleteSpace L] in
lemma framed_eq_sum (e : ι → L →L[ℂ] L) {D M K : ℕ} (X : Fin M → ι → Matrix (Fin K) (Fin K) ℂ)
    (C : Matrix (Fin D) (Fin K) ℂ) (R : Matrix (Fin K) (Fin D) ℂ) :
    (tOp C Id).comp ((((List.ofFn X).map (amp e)).prod).comp (tOp R Id)) =
      ∑ w : Fin M → ι, tOp (C * prodX X w * R) (evalW e (List.ofFn w)) := by
  rw [prod_ofFn_amp, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [tOp_comp, tOp_comp, Matrix.mul_assoc]
  rfl

/-- Hahn–Banach for the gauge of a balanced convex absorbent set. -/
theorem exists_dual_gauge {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] {s : Set M}
    (hb : Balanced ℂ s) (hc : Convex ℝ s) (ha : Absorbent ℝ s) (x₀ : M) :
    ∃ f : M →ₗ[ℂ] ℂ, (∀ v, ‖f v‖ ≤ gauge s v) ∧ f x₀ = (gauge s x₀ : ℂ) := by
  let p : Seminorm ℂ M := gaugeSeminorm hb hc ha
  letI : SeminormedAddCommGroup M := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  letI : NormedSpace ℂ M := ⟨fun a x => (map_smul_eq_mul p a x).le⟩
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℂ x₀
  refine ⟨g.toLinearMap, fun v => ?_, hgx⟩
  calc ‖g v‖ ≤ ‖g‖ * ‖v‖ := g.le_opNorm v
    _ ≤ 1 * ‖v‖ := by gcongr
    _ = gauge s v := one_mul _

/-- The span of the chains as a bare complex vector space (no norm, and only the real structure
obtained by restricting scalars). -/
def CS (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) : Type := chainSpan e o he D

instance (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) : AddCommGroup (CS e o he D) :=
  inferInstanceAs (AddCommGroup (chainSpan e o he D))

instance (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) : Module ℂ (CS e o he D) :=
  inferInstanceAs (Module ℂ (chainSpan e o he D))

/-- The inclusion of `CS` into the operators. -/
def CS.valL (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) :
    CS e o he D →ₗ[ℂ] (PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L)) :=
  (chainSpan e o he D).subtype

lemma CS.valL_injective (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) :
    Function.Injective (CS.valL e o he D) :=
  Subtype.val_injective

/-- An element of `CS` from a member of the span. -/
def CS.mk (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    (T : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L))
    (h : T ∈ chainSpan e o he D) : CS e o he D := (⟨T, h⟩ : chainSpan e o he D)

@[simp] lemma CS.valL_mk (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ}
    (T : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L))
    (h : T ∈ chainSpan e o he D) : CS.valL e o he D (CS.mk e o he T h) = T := rfl

/-- The chains inside `CS`. -/
def chainSetW (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) : Set (CS e o he D) :=
  {v | IsChain e (CS.valL e o he D v)}

lemma valL_real_smul (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) {D : ℕ} (r : ℝ)
    (v : CS e o he D) : CS.valL e o he D (r • v) = (r : ℂ) • CS.valL e o he D v := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  rfl

lemma chainSetW_balanced (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) :
    Balanced ℂ (chainSetW e o he D) := by
  intro a ha
  rintro _ ⟨v, hv, rfl⟩
  show IsChain e (CS.valL e o he D (a • v))
  rw [map_smul]
  exact isChain_smul e o he hv a ha

lemma chainSetW_convex (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) :
    Convex ℝ (chainSetW e o he D) := by
  intro x hx y hy a b ha hb hab
  have := isChain_absConvex e o he hx hy (a : ℂ) (b : ℂ) (by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hab])
  show IsChain e (CS.valL e o he D (a • x + b • y))
  rw [map_add, valL_real_smul, valL_real_smul]
  exact this

lemma chainSetW_absorbent (e : ι → L →L[ℂ] L) (o : ι) (he : e o = 1) (D : ℕ) :
    Absorbent ℝ (chainSetW e o he D) := by
  intro x
  rw [absorbs_iff_norm]
  obtain ⟨r, hr, S, hS, hx⟩ := (x : chainSpan e o he D).2
  refine ⟨r, fun c hc => ?_⟩
  rw [Set.singleton_subset_iff]
  have hc0 : 0 < ‖c‖ := hr.trans_le hc
  have hcne : c ≠ 0 := norm_pos_iff.1 hc0
  have hx' : CS.valL e o he D x = (r : ℂ) • S := hx
  refine ⟨((c⁻¹ : ℝ) : ℂ) • x, ?_, ?_⟩
  · show IsChain e (CS.valL e o he D (((c⁻¹ : ℝ) : ℂ) • x))
    rw [map_smul, hx', smul_smul]
    refine isChain_smul e o he hS _ ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, norm_inv,
      Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hc0, mul_one]
    exact hc
  · apply CS.valL_injective e o he D
    rw [valL_real_smul, map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hcne,
      Complex.ofReal_one, one_smul]

end StrongConv.S9.Pisier.PartF
end
end

section
/-!
# PartF: the factorization theorem (MATH.md Lemma 1 + the Hahn–Banach half of Lemma 11)

The set of framed contractive chains is absolutely convex (`isChain_absConvex`); on its span
its gauge is a seminorm. Hahn–Banach gives a functional `f` with `|f| ≤ gauge` and
`f(evalP e y) = gauge(evalP e y)`. Its coefficients `F w i j = f(Eᵢⱼ ⊗ e(w))` satisfy
`ChainBound` and `FRel`, so `core_bound` bounds the gauge by the operator norm.
-/

noncomputable section

open scoped InnerProductSpace Pointwise
open Matrix

namespace StrongConv.S9.Pisier.PartF

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem factorization (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {D : ℕ}
    (y : List ι →₀ Matrix (Fin D) (Fin D) ℂ) (c : ℝ) (hc : ‖evalP e y‖ < c) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ evalP e y = c • gChainOn e Dim A q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖amp e (A j)‖ ≤ 1 := by
  classical
  have hc0 : 0 < c := (norm_nonneg _).trans_lt hc
  have he := hU.e_o
  have hnorm : ∀ l, ‖e l‖ ≤ 1 := fun l => norm_le_one_of_unitary _ (hU.unitary l)
  let V := chainSpan e hU.o he D
  have hmono : ∀ (w : List ι) (i j : Fin D),
      tOp (Matrix.single i j (1 : ℂ)) (evalW e w) ∈ V := fun w i j =>
    mem_chainSpan_of_isChain e hU.o he (isChain_mono e hnorm i j w)
  have htOp_mem : ∀ (B : Matrix (Fin D) (Fin D) ℂ) (w : List ι), tOp B (evalW e w) ∈ V := by
    intro B w
    rw [tOp_eq_sum_single]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (hmono w i j)
  have hx₀ : evalP e y ∈ V := Submodule.sum_mem _ fun w _ => htOp_mem _ w
  let mk := fun (T : PiLp 2 (fun _ : Fin D => L) →L[ℂ] PiLp 2 (fun _ : Fin D => L))
    (h : T ∈ V) => CS.mk e hU.o he T h
  let val := CS.valL e hU.o he D
  have hval_mk : ∀ T h, val (mk T h) = T := fun _ _ => rfl
  let x₀ := mk (evalP e y) hx₀
  obtain ⟨f, hf, hfx⟩ := exists_dual_gauge (chainSetW_balanced e hU.o he D)
    (chainSetW_convex e hU.o he D) (chainSetW_absorbent e hU.o he D) x₀
  let F : List ι → Matrix (Fin D) (Fin D) ℂ := fun w =>
    Matrix.of fun i j => f (mk (tOp (Matrix.single i j (1 : ℂ)) (evalW e w)) (hmono w i j))
  have hF_tOp : ∀ (B : Matrix (Fin D) (Fin D) ℂ) (w : List ι),
      f (mk (tOp B (evalW e w)) (htOp_mem B w)) = ∑ i, ∑ j, B i j * F w i j := by
    intro B w
    have : mk (tOp B (evalW e w)) (htOp_mem B w) =
        ∑ i, ∑ j, B i j • mk (tOp (Matrix.single i j (1 : ℂ)) (evalW e w)) (hmono w i j) := by
      apply CS.valL_injective e hU.o he D
      simp only [map_sum, map_smul]
      exact tOp_eq_sum_single B _
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  -- `F` is bounded on chains
  have hFB : ChainBound e F := by
    intro M K X C R hX hC hR
    have hZ := isChain_framed e X C R hX hC hR
    have hZV := mem_chainSpan_of_isChain e hU.o he hZ
    have h1 : ‖f (mk _ hZV)‖ ≤ 1 :=
      (hf _).trans (gauge_le_one_of_mem (s := chainSetW e hU.o he D) hZ)
    have h2 : mk _ hZV = ∑ w : Fin M → ι,
        mk (tOp (C * prodX X w * R) (evalW e (List.ofFn w))) (htOp_mem _ _) := by
      apply CS.valL_injective e hU.o he D
      simp only [map_sum]
      exact framed_eq_sum e X C R
    rw [h2, map_sum] at h1
    simpa only [hF_tOp] using h1
  -- `F` respects the relations of `e`
  have hFR : FRel e F := by
    intro t ht
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    have : (∑ w ∈ t.support, t w •
        mk (tOp (Matrix.single i j (1 : ℂ)) (evalW e w)) (hmono w i j)) = 0 := by
      apply CS.valL_injective e hU.o he D
      simp only [map_sum, map_smul, map_zero]
      change ∑ w ∈ t.support, t w • tOp (Matrix.single i j (1 : ℂ)) (evalW e w) = 0
      simp only [← tOp_smul_right]
      rw [← tOp_sum_right, ht, tOp_zero_right]
    have h2 := congrArg f this
    rw [map_sum, map_zero] at h2
    simp only [map_smul, smul_eq_mul] at h2
    exact h2
  -- the pairing is `f` of the polynomial
  have hpair : pairing F y = f x₀ := by
    have : x₀ = ∑ w ∈ y.support, mk (tOp (y w) (evalW e w)) (htOp_mem _ w) := by
      apply CS.valL_injective e hU.o he D
      simp only [map_sum]
      rfl
    rw [this, map_sum]
    unfold pairing
    exact Finset.sum_congr rfl fun w _ => (hF_tOp (y w) w).symm
  have hcore := core_bound e hU F hFB hFR y
  rw [hpair, hfx, Complex.norm_real, Real.norm_of_nonneg (gauge_nonneg _)] at hcore
  have hlt : gauge (chainSetW e hU.o he D) x₀ < c := hcore.trans_lt hc
  obtain ⟨b, hb0, hbc, hbmem⟩ := exists_lt_of_gauge_lt (chainSetW_absorbent e hU.o he D) hlt
  obtain ⟨v, hv, hvx⟩ := Set.mem_smul_set.1 hbmem
  have hvx' : evalP e y = (b : ℂ) • val v := by
    rw [← valL_real_smul, hvx]
    rfl
  have hS : IsChain e (((b / c : ℝ) : ℂ) • val v) := by
    refine isChain_smul e hU.o he hv _ ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_le_one hc0]
    exact hbc.le
  obtain ⟨q, Dim, A, h₁, hq, hq1, hSeq, hA⟩ := isChain_gChainOn e hU.o he hS
  refine ⟨q, Dim, A, h₁, hq, hq1, ?_, hA⟩
  rw [← hSeq, real_smul_clm, smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hc0.ne', hvx']

end StrongConv.S9.Pisier.PartF
end
end

section
/-!
# Part B: bookkeeping stubs `exists_poly_eq_eval` and `rescale`

* `exists_poly_eq_eval`: a polynomial in `s, s*` is the formal polynomial obtained by reading each
  word `w` as the list of letters `some wᵢ`.
* `rescale`: `linOp = amp (freeLetters d)`, and scaling every factor by `c^{1/q}` scales the chain
  of `q` factors by `c`.
-/

noncomputable section

namespace StrongConv.S9.Pisier.PartB

open scoped InnerProductSpace

/-! ## `exists_poly_eq_eval` -/

lemma tOp_eq_tensorOp {d m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (T : L2Free d →L[ℂ] L2Free d) : tOp A T = tensorOp A T := rfl

lemma freeLetters_some (d : ℕ) (l : Fin d ⊕ Fin d) :
    freeLetters d (some l) = letterOp (sLimit d) l := by
  simp [freeLetters, wordEval]

lemma evalW_map_some {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    evalW (freeLetters d) (w.toList.map some) = wordOp (sLimit d) w := by
  simp only [evalW, wordOp, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun l _ => freeLetters_some d l)

/-- `P(s, s*)` as a formal polynomial in the letters. -/
theorem exists_poly_eq_eval {D d : ℕ} (P : NCPoly D d) :
    ∃ y : List (Letter d) →₀ Matrix (Fin D) (Fin D) ℂ,
      evalP (freeLetters d) y = P.eval (sLimit d) := by
  classical
  let f : FreeMonoid (Fin d ⊕ Fin d) → List (Letter d) := fun w => w.toList.map some
  have hf : Function.Injective f := by
    intro w w' h
    have h' : w.toList = w'.toList :=
      List.map_injective_iff.mpr (Option.some_injective _) h
    exact FreeMonoid.toList.injective h'
  refine ⟨P.mapDomain f, ?_⟩
  unfold evalP NCPoly.eval
  rw [Finsupp.mapDomain_support_of_injective hf, Finset.sum_image (fun a _ b _ h => hf h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply hf, evalW_map_some, tOp_eq_tensorOp]

/-! ## `rescale` -/

lemma linOp_eq_amp {d m n : ℕ} (A : Letter d → Matrix (Fin m) (Fin n) ℂ) :
    linOp A = amp (freeLetters d) A := rfl

lemma amp_smul {ι : Type} [Fintype ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : ι → H →L[ℂ] H) {m n : ℕ} (s : ℂ) (X : ι → Matrix (Fin m) (Fin n) ℂ) :
    amp ρ (fun l => s • X l) = s • amp ρ X := by
  simp only [amp, PartF.tOp_smul, Finset.smul_sum]

lemma linChain_smul {d : ℕ} (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (s : ℂ) (t : ℕ) :
    ∀ k : ℕ, linChain Dim (fun j l => s • A j l) t k = s ^ k • gChain (freeLetters d) Dim A t k
  | 0 => by simp [linChain, gChain]
  | k + 1 => by
    rw [linChain, gChain, linChain_smul Dim A s t k, linOp_eq_amp, amp_smul,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_succ]

/-- `linChainOn` is `gChainOn` for the free letters, and rescaling the factors of
`c • gChainOn` by `c^{1/q}` gives the published form. -/
theorem rescale {D d : ℕ} (c : ℝ) (hc : 0 < c) (q : ℕ) (hq1 : 1 ≤ q) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
    (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D)
    (hA : ∀ j ∈ Finset.Icc 1 q, ‖amp (freeLetters d) (A j)‖ ≤ 1) :
    ∃ A' : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ,
      c • gChainOn (freeLetters d) Dim A q h₁ hq = linChainOn Dim A' q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖linOp (A' j)‖ ≤ c ^ (1 / (q : ℝ)) := by
  set s : ℝ := c ^ (1 / (q : ℝ)) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hc.le _
  have hsq : (s : ℂ) ^ q = (c : ℂ) := by
    rw [← Complex.ofReal_pow, hs, one_div,
      Real.rpow_inv_natCast_pow hc.le (by omega)]
  refine ⟨fun j l => (s : ℂ) • A j l, ?_, ?_⟩
  · unfold gChainOn linChainOn
    rw [linChain_smul, hsq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    exact (Complex.coe_smul (E := PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ]
      PiLp 2 (fun _ : Fin D => L2Free d)) c _).symm
  · intro j hj
    rw [linOp_eq_amp, amp_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs0]
    calc s * ‖amp (freeLetters d) (A j)‖ ≤ s * 1 := mul_le_mul_of_nonneg_left (hA j hj) hs0
      _ = s := mul_one s

end StrongConv.S9.Pisier.PartB
end
end

section
noncomputable section

namespace StrongConv.S9.Pisier

open scoped InnerProductSpace

alias factorization := PartF.factorization
alias exists_poly_eq_eval := PartB.exists_poly_eq_eval
alias rescale := PartB.rescale

theorem exists_linearization_dev {D d : ℕ} (P : NCPoly D d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ P.eval (sLimit d) = linChainOn Dim A q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖linOp (A j)‖ ≤ (‖P.eval (sLimit d)‖ + ε) ^ (1 / (q : ℝ)) := by
  classical
  obtain ⟨y, hy⟩ := exists_poly_eq_eval P
  have hc : ‖evalP (freeLetters d) y‖ < ‖P.eval (sLimit d)‖ + ε := by rw [hy]; linarith
  obtain ⟨q, Dim, A, h₁, hq, hq1, heq, hA⟩ :=
    factorization (freeLetters d) (freeLetters_unitary d) y _ hc
  obtain ⟨A', hA'eq, hA'⟩ := rescale (‖P.eval (sLimit d)‖ + ε) (by positivity) q hq1 Dim A h₁ hq hA
  exact ⟨q, Dim, A', h₁, hq, hq1, hy.symm.trans (heq.trans hA'eq), hA'⟩

end StrongConv.S9.Pisier
end
end

open StrongConv in
theorem solution {D d : ℕ} (P : NCPoly D d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ P.eval (sLimit d) = linChainOn Dim A q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖linOp (A j)‖ ≤ (‖P.eval (sLimit d)‖ + ε) ^ (1 / (q : ℝ)) :=
  StrongConv.S9.Pisier.exists_linearization_dev P ε hε
