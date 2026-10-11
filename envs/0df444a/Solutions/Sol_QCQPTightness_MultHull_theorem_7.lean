-- Prove2me | solution 1 for QCQPTightness.MultHull.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:45:11.949972+00:00
-- url     : https://prove2.me/submissions/edc108b7-38f8-4b9b-8749-e49364194d8e

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult

noncomputable section

namespace RankRedKit

open Matrix

/-! ## §0 Definitions -/

/-- `x ↦ xᵀAx + 2bᵀx + c` (= `QCQPTightness.ConvHull.quad`). -/
def quad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (b ⬝ᵥ x) + c

/-- `Q = [[c, bᵀ], [b, A]]` (= `QCQPTightness.ConvHull.liftQ`). -/
def liftQ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => c) (fun _ j => b j) (fun i _ => b i) A

/-- `Y = [[1, xᵀ], [x, X]]` (= `QCQPTightness.ConvHull.liftY`). -/
def liftY {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ j => x j) (fun i _ => x i) X

/-- Feasible set of the Shor relaxation with constraint data `(A i, b i, c i)`; constraint `i`
is an inequality when `I i`, an equality otherwise (= the roots' `sdpFeasible` with
`I = P.IsIneq`). -/
def shorFeasible {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ)
    (c : Fin m → ℝ) (I : Fin m → Prop) : Set ((Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ) :=
  {p | p.2.IsSymm ∧ (liftY p.1 p.2).PosSemidef ∧
    ∀ i, (I i → (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace ≤ 0) ∧
      (¬ I i → (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace = 0)}

/-- `I_k ⊗ 𝔸` on `Fin k × Fin n` (= `QCQPTightness.MultHull.kronId`). -/
def kronId (k : ℕ) {n : ℕ} (𝔸 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin k) (Fin k) ℝ) 𝔸

/-- `Fin k × Fin n ≃ Fin N` (= `QCQPTightness.MultHull.blockEquiv`). -/
def blockEquiv {k n N : ℕ} (h : k * n = N) : Fin k × Fin n ≃ Fin N :=
  finProdFinEquiv.trans (finCongr h)

/-- `I_k ⊗ 𝔸` transported to `Fin N`, the shape `P.A i = reindex … (kronId k 𝔸)` of the roots. -/
def kronMat {k n N : ℕ} (h : k * n = N) (𝔸 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k 𝔸)

/-- `y ⊗ z ∈ ℝ^N` (= `QCQPTightness.MultTight.kronVec`). -/
def kronVec {k n N : ℕ} (h : k * n = N) (y : Fin k → ℝ) (z : Fin n → ℝ) : Fin N → ℝ :=
  fun i => y ((blockEquiv h).symm i).1 * z ((blockEquiv h).symm i).2

/-- Partial trace over the `ℝ^k` factor: `Σ_j W_{(j,s),(j,s')}`. -/
def partialTrace {k n N : ℕ} (h : k * n = N) (W : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun s s' => ∑ j : Fin k, W (blockEquiv h (j, s)) (blockEquiv h (j, s'))

/-! ### Kit helpers -/

theorem aux_sum_blockEquiv {k n N : ℕ} (h : k * n = N) (f : Fin N → ℝ) :
    ∑ i, f i = ∑ j : Fin k, ∑ s : Fin n, f (blockEquiv h (j, s)) := by
  rw [← Equiv.sum_comp (blockEquiv h), Fintype.sum_prod_type]

theorem aux_kronMat_apply {k n N : ℕ} (h : k * n = N) (𝔸 : Matrix (Fin n) (Fin n) ℝ)
    (j j' : Fin k) (s s' : Fin n) :
    kronMat h 𝔸 (blockEquiv h (j, s)) (blockEquiv h (j', s')) =
      (1 : Matrix (Fin k) (Fin k) ℝ) j j' * 𝔸 s s' := by
  simp [kronMat, kronId, Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]

theorem aux_kronVec_apply {k n N : ℕ} (h : k * n = N) (u : Fin k → ℝ) (z : Fin n → ℝ)
    (j : Fin k) (s : Fin n) : kronVec h u z (blockEquiv h (j, s)) = u j * z s := by
  simp [kronVec]

theorem aux_kronMat_isSymm {k n N : ℕ} (h : k * n = N) {𝔸 : Matrix (Fin n) (Fin n) ℝ}
    (h𝔸 : 𝔸.IsSymm) : (kronMat h 𝔸).IsSymm := by
  show (kronMat h 𝔸)ᵀ = kronMat h 𝔸
  ext i i'
  obtain ⟨⟨j, s⟩, rfl⟩ := (blockEquiv h).surjective i
  obtain ⟨⟨j', s'⟩, rfl⟩ := (blockEquiv h).surjective i'
  rw [transpose_apply, aux_kronMat_apply, aux_kronMat_apply, h𝔸.apply s' s]
  simp [Matrix.one_apply, eq_comm]

theorem aux_vecMulVec_isSymm {N : ℕ} (x : Fin N → ℝ) : (vecMulVec x x).IsSymm := by
  show (vecMulVec x x)ᵀ = vecMulVec x x
  ext i j; simp [vecMulVec_apply, mul_comm]

/-! ## §1 Shor lifting -/

/-- K1. `⟨Q, Y⟩ = q(x) + ⟨A, X − xxᵀ⟩`. No symmetry needed. -/
theorem trace_liftQ_mul_liftY {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ)
    (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftQ A b c * liftY x X).trace = quad A b c x + (A * (X - vecMulVec x x)).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type, liftQ, liftY, quad, dotProduct,
    Matrix.fromBlocks, Finset.sum_add_distrib, mulVec, vecMulVec_apply, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  have key : ∑ i, ∑ j, x i * (A i j * x j) = ∑ i, ∑ j, A i j * (x j * x i) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have key2 : ∑ i, 2 * (b i * x i) = 2 * ∑ i, b i * x i := by rw [Finset.mul_sum]
  linarith

/-- K2. Schur complement: `Y ⪰ 0 ↔ X − xxᵀ ⪰ 0`. -/
theorem liftY_posSemidef_iff {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftY x X).PosSemidef ↔ (X - vecMulVec x x).PosSemidef := by
  let B : Matrix (Fin 1) (Fin N) ℝ := Matrix.of fun _ j => x j
  have hB : liftY x X = fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) B Bᴴ X := by
    unfold liftY; congr 1
    · ext i j; fin_cases i; fin_cases j; rfl
  have hS : Bᴴ * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * B = vecMulVec x x := by
    ext i j; simp [B, Matrix.mul_apply, vecMulVec_apply]
  let _ : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
  rw [hB, ← hS]
  exact PosDef.fromBlocks₁₁ _ _ PosDef.one

/-- K3. Exact expansion of a quadratic along a direction. -/
theorem quad_add {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) (b : Fin N → ℝ) (c : ℝ)
    (x w : Fin N → ℝ) :
    quad A b c (x + w) = quad A b c x + 2 * ((A *ᵥ x + b) ⬝ᵥ w) + w ⬝ᵥ (A *ᵥ w) := by
  have h1 : x ⬝ᵥ (A *ᵥ w) = (A *ᵥ x) ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  simp only [quad, mulVec_add, dotProduct_add, add_dotProduct, h1]
  rw [dotProduct_comm w (A *ᵥ x)]
  ring

/-- K4. The rank-one lift of a QCQP-feasible point is Shor-feasible, with the same values. -/
theorem mem_shorFeasible_vecMulVec {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (I : Fin m → Prop) (x : Fin N → ℝ)
    (hx : ∀ i, (I i → quad (A i) (b i) (c i) x ≤ 0) ∧ (¬ I i → quad (A i) (b i) (c i) x = 0)) :
    (x, vecMulVec x x) ∈ shorFeasible A b c I := by
  refine ⟨aux_vecMulVec_isSymm x, ?_, fun i => ?_⟩
  · rw [liftY_posSemidef_iff, sub_self]; exact PosSemidef.zero
  · simp only [trace_liftQ_mul_liftY, sub_self, Matrix.mul_zero, trace_zero, add_zero]
    exact hx i

theorem aux_liftY_combo {N : ℕ} {a b : ℝ} (hab : a + b = 1) (x y : Fin N → ℝ)
    (X Y : Matrix (Fin N) (Fin N) ℝ) :
    liftY (a • x + b • y) (a • X + b • Y) = a • liftY x X + b • liftY y Y := by
  ext (i | i) (j | j) <;> simp [liftY, Matrix.fromBlocks, hab]

theorem aux_trace_combo {N : ℕ} (Q : Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ) (a b : ℝ)
    (Y₁ Y₂ : Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ) :
    (Q * (a • Y₁ + b • Y₂)).trace = a * (Q * Y₁).trace + b * (Q * Y₂).trace := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, trace_add, trace_smul, trace_smul,
    smul_eq_mul, smul_eq_mul]

theorem aux_combo_nonpos {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : s ≤ 0) (ht : t ≤ 0) :
    a * s + b * t ≤ 0 := by nlinarith

/-- K5. The Shor feasible set is convex. -/
theorem convex_shorFeasible {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (I : Fin m → Prop) :
    Convex ℝ (shorFeasible A b c I) := by
  rintro ⟨x, X⟩ ⟨hS, hP, hC⟩ ⟨y, Y⟩ ⟨hS', hP', hC'⟩ μ ν hμ hν hμν
  simp only [Prod.smul_mk, Prod.mk_add_mk]
  refine ⟨(hS.smul μ).add (hS'.smul ν), ?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · rw [aux_liftY_combo hμν]; exact (hP.smul hμ).add (hP'.smul hν)
  · rw [aux_liftY_combo hμν, aux_trace_combo]
    exact aux_combo_nonpos hμ hν ((hC i).1 hi) ((hC' i).1 hi)
  · rw [aux_liftY_combo hμν, aux_trace_combo, (hC i).2 hi, (hC' i).2 hi]; ring

/-- K5b. The projected Shor epigraph `𝒟_SDP` (the roots' `DSDP`) is convex. -/
theorem convex_shorEpigraph {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ) (b₀ : Fin N → ℝ) (c₀ : ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ)
    (I : Fin m → Prop) :
    Convex ℝ {p : (Fin N → ℝ) × ℝ | ∃ X : Matrix (Fin N) (Fin N) ℝ,
      (p.1, X) ∈ shorFeasible A b c I ∧ (liftQ A₀ b₀ c₀ * liftY p.1 X).trace ≤ 2 * p.2} := by
  rintro ⟨x, t⟩ ⟨X, hX, hXt⟩ ⟨y, s⟩ ⟨Y, hY, hYs⟩ μ ν hμ hν hμν
  refine ⟨μ • X + ν • Y, ?_, ?_⟩
  · have := convex_shorFeasible A b c I hX hY hμ hν hμν
    simpa only [Prod.smul_mk, Prod.mk_add_mk] using this
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [aux_liftY_combo hμν, aux_trace_combo]
    nlinarith

/-! ## §2 Kronecker collapse -/

/-- K6. `(u ⊗ z)ᵀ (I_k ⊗ 𝔸) (u' ⊗ z') = (uᵀu')(zᵀ𝔸z')`. -/
theorem kronVec_dotProduct_kronMat_mulVec {k n N : ℕ} (h : k * n = N)
    (𝔸 : Matrix (Fin n) (Fin n) ℝ) (u u' : Fin k → ℝ) (z z' : Fin n → ℝ) :
    kronVec h u z ⬝ᵥ (kronMat h 𝔸 *ᵥ kronVec h u' z') = (u ⬝ᵥ u') * (z ⬝ᵥ (𝔸 *ᵥ z')) := by
  simp only [dotProduct, mulVec]
  rw [aux_sum_blockEquiv h]
  simp only [aux_kronVec_apply]
  simp_rw [aux_sum_blockEquiv h (fun i => kronMat h 𝔸 _ i * kronVec h u' z' i), aux_kronMat_apply,
    aux_kronVec_apply]
  simp [Matrix.one_apply, ite_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- K7. `⟨I_k ⊗ 𝔸, W⟩ = ⟨𝔸, tr_k W⟩`. -/
theorem trace_kronMat_mul {k n N : ℕ} (h : k * n = N) (𝔸 : Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) :
    (kronMat h 𝔸 * W).trace = (𝔸 * partialTrace h W).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, partialTrace]
  rw [aux_sum_blockEquiv h]
  simp_rw [aux_sum_blockEquiv h (fun i => kronMat h 𝔸 _ i * W i _), aux_kronMat_apply]
  simp [Matrix.one_apply, ite_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/-- K8. The partial trace of a PSD matrix is PSD. -/
theorem partialTrace_posSemidef {k n N : ℕ} (h : k * n = N) {W : Matrix (Fin N) (Fin N) ℝ}
    (hW : W.PosSemidef) : (partialTrace h W).PosSemidef := by
  have : partialTrace h W = ∑ j : Fin k,
      W.submatrix (fun s => blockEquiv h (j, s)) (fun s => blockEquiv h (j, s)) := by
    ext s s'; simp [partialTrace, Matrix.sum_apply]
  rw [this]
  exact posSemidef_sum _ fun j _ => hW.submatrix _

/-- K9. `I_k ⊗ Z` is PSD when `Z` is. -/
theorem kronMat_posSemidef {k n N : ℕ} (h : k * n = N) {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : Z.PosSemidef) : (kronMat h Z).PosSemidef := by
  have h1 : (kronId k Z).PosSemidef := PosSemidef.one.kronecker hZ
  exact h1.submatrix _

/-- K10. `tr_k ((1/k) I_k ⊗ Z) = Z` for `k > 0`. -/
theorem partialTrace_smul_kronMat {k n N : ℕ} (h : k * n = N) (hk : 0 < k)
    (Z : Matrix (Fin n) (Fin n) ℝ) :
    partialTrace h ((k : ℝ)⁻¹ • kronMat h Z) = Z := by
  ext s s'
  simp only [partialTrace, Matrix.smul_apply, aux_kronMat_apply, smul_eq_mul, Matrix.one_apply_eq,
    one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- K11. Collapse, forward: a Shor point `(x, X)` yields `Z ⪰ 0` on `ℝ^n` reproducing every
block-structured lifted value. -/
theorem shor_kron_collapse {k n N : ℕ} (h : k * n = N) (x : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) (hY : (liftY x X).PosSemidef) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      ∀ (𝔸 : Matrix (Fin n) (Fin n) ℝ) (b : Fin N → ℝ) (c : ℝ),
        (liftQ (kronMat h 𝔸) b c * liftY x X).trace = quad (kronMat h 𝔸) b c x + (𝔸 * Z).trace := by
  refine ⟨partialTrace h (X - vecMulVec x x),
    partialTrace_posSemidef h ((liftY_posSemidef_iff x X).mp hY), fun 𝔸 b c => ?_⟩
  rw [trace_liftQ_mul_liftY, trace_kronMat_mul]

/-- K12. Collapse, backward: any `Z ⪰ 0` on `ℝ^n` is realised by a symmetric Shor lift at `x`. -/
theorem shor_kron_expand {k n N : ℕ} (h : k * n = N) (hk : 0 < k) (x : Fin N → ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) :
    ∃ X : Matrix (Fin N) (Fin N) ℝ, X.IsSymm ∧ (liftY x X).PosSemidef ∧
      ∀ (𝔸 : Matrix (Fin n) (Fin n) ℝ) (b : Fin N → ℝ) (c : ℝ),
        (liftQ (kronMat h 𝔸) b c * liftY x X).trace = quad (kronMat h 𝔸) b c x + (𝔸 * Z).trace := by
  have hM : ((k : ℝ)⁻¹ • kronMat h Z).PosSemidef :=
    (kronMat_posSemidef h hZ).smul (inv_nonneg.mpr (Nat.cast_nonneg k))
  refine ⟨vecMulVec x x + (k : ℝ)⁻¹ • kronMat h Z, ?_, ?_, fun 𝔸 b c => ?_⟩
  · have h2 : ((k : ℝ)⁻¹ • kronMat h Z).IsSymm := by
      have := hM.isHermitian
      rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact (aux_vecMulVec_isSymm x).add h2
  · rw [liftY_posSemidef_iff, add_sub_cancel_left]; exact hM
  · rw [trace_liftQ_mul_liftY, add_sub_cancel_left, trace_kronMat_mul, partialTrace_smul_kronMat h hk]

/-- K13. Fewer than `k` linear conditions on `u ⊗ z` leave a unit `u`. -/
theorem exists_unit_kronVec_orthogonal {k n N p : ℕ} (h : k * n = N) (hp : p < k)
    (g : Fin p → Fin N → ℝ) (z : Fin n → ℝ) :
    ∃ u : Fin k → ℝ, u ⬝ᵥ u = 1 ∧ ∀ i, g i ⬝ᵥ kronVec h u z = 0 := by
  let L : (Fin k → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    { toFun := fun u i => g i ⬝ᵥ kronVec h u z
      map_add' := by
        intro u v; ext i; simp [kronVec, dotProduct, add_mul, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r u; ext i; simp [kronVec, dotProduct, Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _; ring }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hp)
  obtain ⟨u₀, hu₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hpos : 0 < u₀ ⬝ᵥ u₀ := by
    rcases (dotProduct_self_star_pos_iff (v := u₀)).mpr hne with h'
    simpa using h'
  refine ⟨(Real.sqrt (u₀ ⬝ᵥ u₀))⁻¹ • u₀, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow,
      Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · intro i
    have : L u₀ i = 0 := by rw [LinearMap.mem_ker.mp hu₀]; rfl
    have h2 : L ((Real.sqrt (u₀ ⬝ᵥ u₀))⁻¹ • u₀) i = 0 := by rw [map_smul]; simp [this]
    exact h2

/-- K14. The splitting step: with `p < k` block-structured quadratics, there is a unit `u` such
that moving `x` by `± u ⊗ z` adds exactly `zᵀ𝔸_i z` to each of them. -/
theorem kron_split {k n N p : ℕ} (h : k * n = N) (hp : p < k)
    (𝔸 : Fin p → Matrix (Fin n) (Fin n) ℝ) (h𝔸 : ∀ i, (𝔸 i).IsSymm)
    (b : Fin p → Fin N → ℝ) (c : Fin p → ℝ) (x : Fin N → ℝ) (z : Fin n → ℝ) :
    ∃ u : Fin k → ℝ, u ⬝ᵥ u = 1 ∧ ∀ i, ∀ σ : ℝ, σ ^ 2 = 1 →
      quad (kronMat h (𝔸 i)) (b i) (c i) (x + σ • kronVec h u z)
        = quad (kronMat h (𝔸 i)) (b i) (c i) x + z ⬝ᵥ (𝔸 i *ᵥ z) := by
  obtain ⟨u, hu, hg⟩ := exists_unit_kronVec_orthogonal h hp
    (fun i => kronMat h (𝔸 i) *ᵥ x + b i) z
  refine ⟨u, hu, fun i σ hσ => ?_⟩
  rw [quad_add (aux_kronMat_isSymm h (h𝔸 i)), dotProduct_smul, hg i, mulVec_smul, dotProduct_smul,
    smul_dotProduct, kronVec_dotProduct_kronMat_mulVec, hu]
  simp only [smul_eq_mul]
  linear_combination (z ⬝ᵥ (𝔸 i *ᵥ z)) * hσ

/-! ## §3 Rank-one peeling -/

/-- K15. A real PSD matrix is a sum of `card n` outer products `z_j z_jᵀ`. -/
theorem posSemidef_eq_sum_vecMulVec {n : Type*} [Fintype n] {Z : Matrix n n ℝ}
    (hZ : Z.PosSemidef) : ∃ z : n → n → ℝ, Z = ∑ j, vecMulVec (z j) (z j) := by
  classical
  open scoped MatrixOrder in
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  refine ⟨fun j => B j, ?_⟩
  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply, star_eq_conjTranspose]

/-- K16. Generic peeling induction: if `Φ p 0` puts `p` in `D`, and a rank-one piece `zzᵀ` can
always be traded for a midpoint split, then `Φ p Z` with `Z ⪰ 0` puts `p` in `conv D`. -/
theorem mem_convexHull_of_peel {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (D : Set E) (Φ : E → Matrix ι ι ℝ → Prop)
    (base : ∀ p, Φ p 0 → p ∈ D)
    (step : ∀ p (Z : Matrix ι ι ℝ) (z : ι → ℝ), Z.PosSemidef → Φ p (Z + vecMulVec z z) →
      ∃ p₁ p₂, p = (1 / 2 : ℝ) • p₁ + (1 / 2 : ℝ) • p₂ ∧ Φ p₁ Z ∧ Φ p₂ Z)
    {p : E} {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (hp : Φ p Z) :
    p ∈ convexHull ℝ D := by
  classical
  obtain ⟨z, rfl⟩ := posSemidef_eq_sum_vecMulVec hZ
  have key : ∀ s : Finset ι, ∀ q, Φ q (∑ j ∈ s, vecMulVec (z j) (z j)) → q ∈ convexHull ℝ D := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro q hq; simp at hq; exact subset_convexHull ℝ D (base q hq)
    | insert a s ha ih =>
      intro q hq
      rw [Finset.sum_insert ha, add_comm] at hq
      have hps : (∑ j ∈ s, vecMulVec (z j) (z j)).PosSemidef :=
        posSemidef_sum s (fun j _ => by simpa using posSemidef_vecMulVec_self_star (z j))
      obtain ⟨p₁, p₂, rfl, h₁, h₂⟩ := step q _ (z a) hps hq
      exact convex_convexHull ℝ D (ih p₁ h₁) (ih p₂ h₂) (by norm_num) (by norm_num) (by norm_num)
  exact key Finset.univ p hp

/-! ## §4 Attainment of the Shor SDP under Assumption 1 -/

theorem aux_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem aux_sq_le_dot {n : Type*} [Fintype n] (v : n → ℝ) (i : n) : v i * v i ≤ v ⬝ᵥ v :=
  Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i)

theorem aux_trace_vecMulVec {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    (M * vecMulVec x x).trace = x ⬝ᵥ M *ᵥ x := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_posDef_coercive {n : Type*} [Fintype n] {G : Matrix n n ℝ} (hG : G.PosDef) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : n → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G *ᵥ v) := by
  have hpos : ∀ v : n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (G *ᵥ v) := fun v hv => by
    simpa using hG.dotProduct_mulVec_pos hv
  have hnorm : ∀ v : n → ℝ, v ≠ 0 → ∃ c : ℝ, (c • v) ⬝ᵥ (c • v) = 1 ∧ c ^ 2 * (v ⬝ᵥ v) = 1 := by
    intro v hv
    have hvv : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (aux_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))
    have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hvv.le
    have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hvv
    have h1 : ((Real.sqrt (v ⬝ᵥ v))⁻¹) ^ 2 * (v ⬝ᵥ v) = 1 := by
      rw [inv_pow, hs2, inv_mul_cancel₀ hvv.ne']
    refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, ?_, h1⟩
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← h1]; ring
  let sph : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}
  have hcomp : IsCompact sph := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun v hv => ?_⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 := aux_sq_le_dot v i
      have h2 : v ⬝ᵥ v = 1 := hv
      rw [Real.norm_eq_abs]
      nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]
  by_cases hne : sph.Nonempty
  · have hcont : Continuous fun v : n → ℝ => v ⬝ᵥ (G *ᵥ v) :=
      continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    obtain ⟨v₀, hv₀, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      rintro rfl; simp [sph] at hv₀
    refine ⟨v₀ ⬝ᵥ (G *ᵥ v₀), hpos v₀ hv₀ne, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨c, hc1, hc2⟩ := hnorm v hv
    have := isMinOn_iff.mp hmin (c • v) hc1
    have hq : (c • v) ⬝ᵥ (G *ᵥ (c • v)) = c ^ 2 * (v ⬝ᵥ (G *ᵥ v)) := by
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
    rw [hq] at this
    have hvv := aux_dot_self_nonneg v
    have hm : v₀ ⬝ᵥ (G *ᵥ v₀) * (v ⬝ᵥ v) ≤ c ^ 2 * (v ⬝ᵥ (G *ᵥ v)) * (v ⬝ᵥ v) :=
      mul_le_mul_of_nonneg_right this hvv
    calc v₀ ⬝ᵥ (G *ᵥ v₀) * (v ⬝ᵥ v) ≤ c ^ 2 * (v ⬝ᵥ (G *ᵥ v)) * (v ⬝ᵥ v) := hm
      _ = (c ^ 2 * (v ⬝ᵥ v)) * (v ⬝ᵥ (G *ᵥ v)) := by ring
      _ = v ⬝ᵥ (G *ᵥ v) := by rw [hc2, one_mul]
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    obtain ⟨c, hc1, -⟩ := hnorm v hv
    exact absurd ⟨c • v, hc1⟩ hne

theorem aux_trace_lower {n : Type*} [Fintype n] {G W : Matrix n n ℝ} {l : ℝ}
    (hl : ∀ v : n → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G *ᵥ v)) (hW : W.PosSemidef) :
    l * W.trace ≤ (G * W).trace := by
  obtain ⟨w, rfl⟩ := posSemidef_eq_sum_vecMulVec hW
  rw [Matrix.mul_sum, trace_sum, trace_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (vecMulVec (w j) (w j)).trace = w j ⬝ᵥ w j := by
    simp [trace, vecMulVec_apply, dotProduct]
  rw [h1, aux_trace_vecMulVec]
  exact hl _

theorem aux_psd_entry {n : Type*} [Fintype n] {W : Matrix n n ℝ} (hW : W.PosSemidef) (i j : n) :
    |W i j| ≤ W.trace := by
  obtain ⟨w, rfl⟩ := posSemidef_eq_sum_vecMulVec hW
  have htr : ∀ l, (vecMulVec (w l) (w l)).trace = w l ⬝ᵥ w l := by
    intro l; simp [trace, vecMulVec_apply, dotProduct]
  rw [trace_sum]
  simp only [Matrix.sum_apply, vecMulVec_apply, htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  have h1 := aux_sq_le_dot (w l) i
  have h2 := aux_sq_le_dot (w l) j
  rw [abs_mul]
  nlinarith [abs_mul_abs_self (w l i), abs_mul_abs_self (w l j), sq_nonneg (|w l i| - |w l j|)]

theorem aux_liftQ_comb {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ) (b₀ : Fin N → ℝ) (c₀ : ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (γ : Fin m → ℝ) :
    liftQ (A₀ + ∑ i, γ i • A i) (b₀ + ∑ i, γ i • b i) (c₀ + ∑ i, γ i * c i) =
      liftQ A₀ b₀ c₀ + ∑ i, γ i • liftQ (A i) (b i) (c i) := by
  ext (i | i) (j | j) <;> simp [liftQ, Matrix.fromBlocks, Matrix.sum_apply, Finset.sum_apply]

theorem aux_coercive_num {l a t d β c M g w : ℝ} (hl : 0 < l) (ha : l * a ≤ g) (ht : l * t ≤ w)
    (h0 : 0 ≤ l ^ 2 * a + 4 * l * d + 4 * β) (hF : g + 2 * d + c + w ≤ M) (ht0 : 0 ≤ t)
    (ha0 : 0 ≤ a) :
    a ≤ (2 * l * M + 4 * β - 2 * l * c) / l ^ 2 ∧ t ≤ (2 * l * M + 4 * β - 2 * l * c) / l ^ 2 := by
  have key : l ^ 2 * a + 2 * l ^ 2 * t ≤ 2 * l * M + 4 * β - 2 * l * c := by nlinarith
  have hl2 : 0 < l ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hl2]; nlinarith
  · rw [le_div_iff₀ hl2]; nlinarith

theorem aux_sq_expand {N : ℕ} (l : ℝ) (x bb : Fin N → ℝ) :
    0 ≤ l ^ 2 * (x ⬝ᵥ x) + 4 * l * (bb ⬝ᵥ x) + 4 * (bb ⬝ᵥ bb) := by
  have h0 := aux_dot_self_nonneg (l • x + (2 : ℝ) • bb)
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm x bb] at h0
  nlinarith

theorem aux_isClosed_imp {α : Type*} [TopologicalSpace α] {P : Prop} {s : Set α}
    (hs : IsClosed s) : IsClosed {p | P → p ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

theorem aux_isClosed_posSemidef {n : Type*} [Fintype n] :
    IsClosed {A : Matrix n n ℝ | A.PosSemidef} := by
  have : {A : Matrix n n ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : n → ℝ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A; simp only [Set.mem_ofPred_eq, posSemidef_iff_dotProduct_mulVec, IsHermitian,
      Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

theorem aux_continuous_liftY {N : ℕ} :
    Continuous fun p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ => liftY p.1 p.2 := by
  unfold liftY
  refine Continuous.matrix_fromBlocks continuous_const ?_ ?_ continuous_snd
  · exact continuous_pi fun _ => continuous_pi fun j => (continuous_apply j).comp continuous_fst
  · exact continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst

theorem aux_isClosed_shorFeasible {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (I : Fin m → Prop) :
    IsClosed (shorFeasible A b c I) := by
  have hY := aux_continuous_liftY (N := N)
  have htr : ∀ i, Continuous fun p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ =>
      (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace := fun i =>
    (continuous_const.matrix_mul hY).matrix_trace
  have e : shorFeasible A b c I = {p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ | p.2ᵀ = p.2} ∩
      ((fun p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ => liftY p.1 p.2) ⁻¹'
        {M | M.PosSemidef}) ∩
      ⋂ i, ({p | I i → p ∈ {p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ |
              (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace ≤ 0}} ∩
            {p | ¬ I i → p ∈ {p : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ |
              (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace = 0}}) := by
    ext p
    simp only [shorFeasible, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [e]
  refine ((isClosed_eq continuous_snd.matrix_transpose continuous_snd).inter
    (aux_isClosed_posSemidef.preimage hY)).inter (isClosed_iInter fun i => ?_)
  exact (aux_isClosed_imp (isClosed_le (htr i) continuous_const)).inter
    (aux_isClosed_imp (isClosed_eq (htr i) continuous_const))

/-- K17. If some multiplier `γ` (nonnegative on inequalities) makes `A₀ + Σ γ_i A_i ≻ 0`, the
Shor objective attains its infimum on a nonempty Shor feasible set. -/
theorem shor_exists_isMinOn {N m : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℝ) (b₀ : Fin N → ℝ) (c₀ : ℝ)
    (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ)
    (I : Fin m → Prop) (γ : Fin m → ℝ) (hγ : ∀ i, I i → 0 ≤ γ i)
    (hPD : (A₀ + ∑ i, γ i • A i).PosDef) (hne : (shorFeasible A b c I).Nonempty) :
    ∃ p ∈ shorFeasible A b c I, ∀ p' ∈ shorFeasible A b c I,
      (liftQ A₀ b₀ c₀ * liftY p.1 p.2).trace ≤ (liftQ A₀ b₀ c₀ * liftY p'.1 p'.2).trace := by
  classical
  let f : (Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ → ℝ :=
    fun p => (liftQ A₀ b₀ c₀ * liftY p.1 p.2).trace
  have hfc : Continuous f := (continuous_const.matrix_mul aux_continuous_liftY).matrix_trace
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨l, hl0, hl⟩ := aux_posDef_coercive hPD
  have hlow : ∀ p ∈ shorFeasible A b c I,
      quad (A₀ + ∑ i, γ i • A i) (b₀ + ∑ i, γ i • b i) (c₀ + ∑ i, γ i * c i) p.1 +
        ((A₀ + ∑ i, γ i • A i) * (p.2 - vecMulVec p.1 p.1)).trace ≤ f p := by
    rintro ⟨x, X⟩ ⟨-, -, hC⟩
    rw [← trace_liftQ_mul_liftY, aux_liftQ_comb, Matrix.add_mul, trace_add, Finset.sum_mul,
      trace_sum]
    have hi : ∀ i, (γ i • liftQ (A i) (b i) (c i) * liftY x X).trace ≤ 0 := by
      intro i
      rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
      by_cases hi : I i
      · exact mul_nonpos_of_nonneg_of_nonpos (hγ i hi) ((hC i).1 hi)
      · rw [(hC i).2 hi, mul_zero]
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hi i
    show _ ≤ (liftQ A₀ b₀ c₀ * liftY x X).trace
    linarith
  have hbound : ∀ p ∈ shorFeasible A b c I, f p ≤ f p₀ →
      (∀ i, |p.1 i| ≤ 1 + 2 * ((2 * l * f p₀ + 4 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ (b₀ + ∑ i, γ i • b i))
        - 2 * l * (c₀ + ∑ i, γ i * c i)) / l ^ 2)) ∧
      (∀ i j, |p.2 i j| ≤ 1 + 2 * ((2 * l * f p₀ + 4 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ
        (b₀ + ∑ i, γ i • b i)) - 2 * l * (c₀ + ∑ i, γ i * c i)) / l ^ 2)) := by
    rintro ⟨x, X⟩ hp hfp
    have hW : (X - vecMulVec x x).PosSemidef := (liftY_posSemidef_iff x X).mp hp.2.1
    have h1 := hlow _ hp
    dsimp only at h1
    unfold quad at h1
    have hF : x ⬝ᵥ ((A₀ + ∑ i, γ i • A i) *ᵥ x) + 2 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ x) +
        (c₀ + ∑ i, γ i * c i) + ((A₀ + ∑ i, γ i • A i) * (X - vecMulVec x x)).trace ≤ f p₀ := by
      linarith
    obtain ⟨hax, htx⟩ := aux_coercive_num hl0 (hl x) (aux_trace_lower hl hW)
      (aux_sq_expand l x (b₀ + ∑ i, γ i • b i)) hF hW.trace_nonneg (aux_dot_self_nonneg x)
    have ha0 := aux_dot_self_nonneg x
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · have := aux_sq_le_dot x i
      show |x i| ≤ _
      nlinarith [abs_mul_abs_self (x i), abs_nonneg (x i), sq_nonneg (|x i| - 1)]
    · have hWij := aux_psd_entry hW i j
      have hX : X i j = (X - vecMulVec x x) i j + x i * x j := by
        simp [vecMulVec_apply]
      have hxi := aux_sq_le_dot x i
      have hxj := aux_sq_le_dot x j
      have hxx : |x i * x j| ≤ x ⬝ᵥ x := by
        rw [abs_mul]
        nlinarith [abs_mul_abs_self (x i), abs_mul_abs_self (x j), sq_nonneg (|x i| - |x j|)]
      show |X i j| ≤ _
      rw [hX]
      have := abs_add_le ((X - vecMulVec x x) i j) (x i * x j)
      linarith
  have hKc : IsCompact (shorFeasible A b c I ∩ {p | f p ≤ f p₀}) := by
    set R := 1 + 2 * ((2 * l * f p₀ + 4 * ((b₀ + ∑ i, γ i • b i) ⬝ᵥ (b₀ + ∑ i, γ i • b i))
        - 2 * l * (c₀ + ∑ i, γ i * c i)) / l ^ 2) with hR
    have hT : IsCompact ((Set.univ.pi fun _ : Fin N => Set.Icc (-R) R) ×ˢ
        (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Set.Icc (-R) R) :
          Set ((Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    refine hT.of_isClosed_subset
      ((aux_isClosed_shorFeasible A b c I).inter (isClosed_le hfc continuous_const)) ?_
    rintro p ⟨hp, hfp⟩
    obtain ⟨h1, h2⟩ := hbound p hp hfp
    exact ⟨fun i _ => abs_le.mp (h1 i), fun i _ j _ => abs_le.mp (h2 i j)⟩
  obtain ⟨p, ⟨hpS, hpM⟩, hmin⟩ := hKc.exists_isMinOn ⟨p₀, hp₀, (le_refl (f p₀) : f p₀ ≤ f p₀)⟩ hfc.continuousOn
  refine ⟨p, hpS, fun p' hp' => ?_⟩
  show f p ≤ f p'
  by_cases h : f p' ≤ f p₀
  · exact isMinOn_iff.mp hmin p' ⟨hp', h⟩
  · exact le_trans hpM (le_of_not_ge h)

end RankRedKit

end

namespace RRAux_QCQPTightness_MultHull_theorem_7

open Matrix

lemma trace_mul_add_vecMulVec {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    (A * (Z + vecMulVec z z)).trace = (A * Z).trace + z ⬝ᵥ (A *ᵥ z) := by
  rw [Matrix.mul_add, Matrix.trace_add]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma half_split {N : ℕ} (x w : Fin N → ℝ) (t : ℝ) :
    (x, t) = (1 / 2 : ℝ) • (x + (1 : ℝ) • w, t) + (1 / 2 : ℝ) • (x + (-1 : ℝ) • w, t) := by
  ext i
  · simp only [Prod.smul_mk, Prod.fst_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [Prod.smul_mk, Prod.snd_add, smul_eq_mul]; ring

end RRAux_QCQPTightness_MultHull_theorem_7

open RRAux_QCQPTightness_MultHull_theorem_7 in
open QCQPTightness.MultHull in
open Matrix in
theorem solution {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m) (h1 : P.Assumption1)
    (k : ℕ) (hk : P.IsQuadEigMult k) (hkm : m + 2 ≤ k) :
    convexHull ℝ P.D = P.DSDP := by
  obtain ⟨n, h, ⟨𝔸₀, h𝔸₀s, hA₀⟩, hA⟩ := hk.1
  choose 𝔸 h𝔸s h𝔸 using hA
  -- translate the root's objects into the kit's
  have hq₀ : ∀ x, P.q₀ x = RankRedKit.quad (RankRedKit.kronMat h 𝔸₀) P.b₀ P.c₀ x := by
    intro x; simp only [QCQP.q₀]; rw [hA₀]; rfl
  have hq : ∀ i x, P.q i x = RankRedKit.quad (RankRedKit.kronMat h (𝔸 i)) (P.b i) (P.c i) x := by
    intro i x; simp only [QCQP.q]; rw [h𝔸 i]; rfl
  have hT₀ : ∀ x X, (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
      QCQPTightness.ConvHull.liftY x X).trace = (RankRedKit.liftQ (RankRedKit.kronMat h 𝔸₀)
        P.b₀ P.c₀ * RankRedKit.liftY x X).trace := by
    intro x X; rw [hA₀]; rfl
  have hT : ∀ i x X, (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) *
      QCQPTightness.ConvHull.liftY x X).trace = (RankRedKit.liftQ (RankRedKit.kronMat h (𝔸 i))
        (P.b i) (P.c i) * RankRedKit.liftY x X).trace := by
    intro i x X; rw [h𝔸 i]; rfl
  apply le_antisymm
  · -- conv 𝒟 ⊆ 𝒟_SDP
    apply convexHull_min
    · rintro ⟨x, t⟩ ⟨hobj, hfeas⟩
      refine ⟨vecMulVec x x, ?_, ?_⟩
      · exact RankRedKit.mem_shorFeasible_vecMulVec P.A P.b P.c P.IsIneq x hfeas
      · have := RankRedKit.trace_liftQ_mul_liftY P.A₀ P.b₀ P.c₀ x (vecMulVec x x)
        rw [sub_self, Matrix.mul_zero, Matrix.trace_zero, add_zero] at this
        show (RankRedKit.liftQ P.A₀ P.b₀ P.c₀ * RankRedKit.liftY x (vecMulVec x x)).trace ≤ 2 * t
        rw [this]; exact hobj
    · exact RankRedKit.convex_shorEpigraph P.A₀ P.b₀ P.c₀ P.A P.b P.c P.IsIneq
  · -- 𝒟_SDP ⊆ conv 𝒟
    rintro ⟨xh, th⟩ ⟨X, ⟨_, hY, hcons⟩, hobj⟩
    obtain ⟨Z, hZ, hZeq⟩ := RankRedKit.shor_kron_collapse h xh X hY
    let Φ : (Fin N → ℝ) × ℝ → Matrix (Fin n) (Fin n) ℝ → Prop := fun p Z =>
      RankRedKit.quad (RankRedKit.kronMat h 𝔸₀) P.b₀ P.c₀ p.1 + (𝔸₀ * Z).trace ≤ 2 * p.2 ∧
      ∀ i, (P.IsIneq i →
          RankRedKit.quad (RankRedKit.kronMat h (𝔸 i)) (P.b i) (P.c i) p.1 + (𝔸 i * Z).trace ≤ 0) ∧
        (¬ P.IsIneq i →
          RankRedKit.quad (RankRedKit.kronMat h (𝔸 i)) (P.b i) (P.c i) p.1 + (𝔸 i * Z).trace = 0)
    refine RankRedKit.mem_convexHull_of_peel P.D Φ ?_ ?_ hZ ?_
    · -- base
      rintro ⟨x, t⟩ ⟨h0, hi⟩
      simp only [Matrix.mul_zero, Matrix.trace_zero, add_zero] at h0 hi
      refine ⟨by rw [hq₀]; exact h0, fun i => ⟨fun hI => ?_, fun hI => ?_⟩⟩
      · rw [hq]; exact (hi i).1 hI
      · rw [hq]; exact (hi i).2 hI
    · -- step
      rintro ⟨x, t⟩ Z' z _ ⟨h0, hi⟩
      let 𝔸' : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ := Fin.cons 𝔸₀ 𝔸
      let b' : Fin (m + 1) → Fin N → ℝ := Fin.cons P.b₀ P.b
      let c' : Fin (m + 1) → ℝ := Fin.cons P.c₀ P.c
      have h𝔸' : ∀ i, (𝔸' i).IsSymm := by
        intro i; refine Fin.cases ?_ (fun j => ?_) i
        · simpa [𝔸'] using h𝔸₀s
        · simpa [𝔸'] using h𝔸s j
      obtain ⟨u, -, hu⟩ := RankRedKit.kron_split h (by omega : m + 1 < k) 𝔸' h𝔸' b' c' x z
      have hu₀ : ∀ σ : ℝ, σ ^ 2 = 1 →
          RankRedKit.quad (RankRedKit.kronMat h 𝔸₀) P.b₀ P.c₀ (x + σ • RankRedKit.kronVec h u z)
            = RankRedKit.quad (RankRedKit.kronMat h 𝔸₀) P.b₀ P.c₀ x + z ⬝ᵥ (𝔸₀ *ᵥ z) :=
        fun σ hσ => by simpa [𝔸', b', c'] using hu 0 σ hσ
      have hui : ∀ i, ∀ σ : ℝ, σ ^ 2 = 1 →
          RankRedKit.quad (RankRedKit.kronMat h (𝔸 i)) (P.b i) (P.c i)
              (x + σ • RankRedKit.kronVec h u z)
            = RankRedKit.quad (RankRedKit.kronMat h (𝔸 i)) (P.b i) (P.c i) x
              + z ⬝ᵥ (𝔸 i *ᵥ z) :=
        fun i σ hσ => by simpa [𝔸', b', c'] using hu i.succ σ hσ
      have key : ∀ σ : ℝ, σ ^ 2 = 1 → Φ (x + σ • RankRedKit.kronVec h u z, t) Z' := by
        intro σ hσ
        refine ⟨?_, fun i => ⟨fun hI => ?_, fun hI => ?_⟩⟩
        · have := h0; rw [trace_mul_add_vecMulVec] at this
          show RankRedKit.quad _ _ _ (x + σ • RankRedKit.kronVec h u z) + _ ≤ _
          rw [hu₀ σ hσ]; linarith
        · have := (hi i).1 hI; rw [trace_mul_add_vecMulVec] at this
          show RankRedKit.quad _ _ _ (x + σ • RankRedKit.kronVec h u z) + _ ≤ _
          rw [hui i σ hσ]; linarith
        · have := (hi i).2 hI; rw [trace_mul_add_vecMulVec] at this
          show RankRedKit.quad _ _ _ (x + σ • RankRedKit.kronVec h u z) + _ = _
          rw [hui i σ hσ]; linarith
      exact ⟨_, _, half_split x (RankRedKit.kronVec h u z) t, key 1 (by norm_num),
        key (-1) (by norm_num)⟩
    · -- the Shor point satisfies Φ with Z
      refine ⟨?_, fun i => ⟨fun hI => ?_, fun hI => ?_⟩⟩
      · rw [← hZeq, ← hT₀]; exact hobj
      · rw [← hZeq, ← hT]; exact (hcons i).1 hI
      · rw [← hZeq, ← hT]; exact (hcons i).2 hI

#print axioms solution
