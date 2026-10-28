-- Prove2me | solution 2 for QCQPTightness.MultHull.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:35:18.467352+00:00
-- url     : https://prove2.me/submissions/f2970bd1-b532-41db-85a7-e991f9f012d2

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult
import Theorems.Thm_Convex_mem_convexHull_of_posSemidef_peel

-- carved verbatim out of submission edc108b7-38f8-4b9b-8749-e49364194d8e, lines 604-690

noncomputable section
open Matrix

namespace RankRedKit

def quad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (b ⬝ᵥ x) + c

end RankRedKit

namespace RankRedKit

def liftQ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => c) (fun _ j => b j) (fun i _ => b i) A

end RankRedKit

namespace RankRedKit

def liftY {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ j => x j) (fun i _ => x i) X

end RankRedKit

namespace RankRedKit

def shorFeasible {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (b : Fin m → Fin N → ℝ)
    (c : Fin m → ℝ) (I : Fin m → Prop) : Set ((Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ) :=
  {p | p.2.IsSymm ∧ (liftY p.1 p.2).PosSemidef ∧
    ∀ i, (I i → (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace ≤ 0) ∧
      (¬ I i → (liftQ (A i) (b i) (c i) * liftY p.1 p.2).trace = 0)}

end RankRedKit

namespace RankRedKit

def kronId (k : ℕ) {n : ℕ} (𝔸 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin k) (Fin k) ℝ) 𝔸

end RankRedKit

namespace RankRedKit

def blockEquiv {k n N : ℕ} (h : k * n = N) : Fin k × Fin n ≃ Fin N :=
  finProdFinEquiv.trans (finCongr h)

end RankRedKit

namespace RankRedKit

def kronMat {k n N : ℕ} (h : k * n = N) (𝔸 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k 𝔸)

end RankRedKit

namespace RankRedKit

def kronVec {k n N : ℕ} (h : k * n = N) (y : Fin k → ℝ) (z : Fin n → ℝ) : Fin N → ℝ :=
  fun i => y ((blockEquiv h).symm i).1 * z ((blockEquiv h).symm i).2

end RankRedKit

namespace RankRedKit

def partialTrace {k n N : ℕ} (h : k * n = N) (W : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun s s' => ∑ j : Fin k, W (blockEquiv h (j, s)) (blockEquiv h (j, s'))

end RankRedKit

namespace RankRedKit

theorem aux_sum_blockEquiv {k n N : ℕ} (h : k * n = N) (f : Fin N → ℝ) :
    ∑ i, f i = ∑ j : Fin k, ∑ s : Fin n, f (blockEquiv h (j, s)) := by
  rw [← Equiv.sum_comp (blockEquiv h), Fintype.sum_prod_type]

end RankRedKit

namespace RankRedKit

theorem aux_kronMat_apply {k n N : ℕ} (h : k * n = N) (𝔸 : Matrix (Fin n) (Fin n) ℝ)
    (j j' : Fin k) (s s' : Fin n) :
    kronMat h 𝔸 (blockEquiv h (j, s)) (blockEquiv h (j', s')) =
      (1 : Matrix (Fin k) (Fin k) ℝ) j j' * 𝔸 s s' := by
  simp [kronMat, kronId, Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]

end RankRedKit

namespace RankRedKit

theorem aux_kronVec_apply {k n N : ℕ} (h : k * n = N) (u : Fin k → ℝ) (z : Fin n → ℝ)
    (j : Fin k) (s : Fin n) : kronVec h u z (blockEquiv h (j, s)) = u j * z s := by
  simp [kronVec]

end RankRedKit

namespace RankRedKit

theorem aux_kronMat_isSymm {k n N : ℕ} (h : k * n = N) {𝔸 : Matrix (Fin n) (Fin n) ℝ}
    (h𝔸 : 𝔸.IsSymm) : (kronMat h 𝔸).IsSymm := by
  show (kronMat h 𝔸)ᵀ = kronMat h 𝔸
  ext i i'
  obtain ⟨⟨j, s⟩, rfl⟩ := (blockEquiv h).surjective i
  obtain ⟨⟨j', s'⟩, rfl⟩ := (blockEquiv h).surjective i'
  rw [transpose_apply, aux_kronMat_apply, aux_kronMat_apply, h𝔸.apply s' s]
  simp [Matrix.one_apply, eq_comm]

end RankRedKit

namespace RankRedKit

theorem aux_vecMulVec_isSymm {N : ℕ} (x : Fin N → ℝ) : (vecMulVec x x).IsSymm := by
  show (vecMulVec x x)ᵀ = vecMulVec x x
  ext i j; simp [vecMulVec_apply, mul_comm]

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

theorem quad_add {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) (b : Fin N → ℝ) (c : ℝ)
    (x w : Fin N → ℝ) :
    quad A b c (x + w) = quad A b c x + 2 * ((A *ᵥ x + b) ⬝ᵥ w) + w ⬝ᵥ (A *ᵥ w) := by
  have h1 : x ⬝ᵥ (A *ᵥ w) = (A *ᵥ x) ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]
  simp only [quad, mulVec_add, dotProduct_add, add_dotProduct, h1]
  rw [dotProduct_comm w (A *ᵥ x)]
  ring

end RankRedKit

namespace RankRedKit

theorem mem_shorFeasible_vecMulVec {N m : ℕ} (A : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (b : Fin m → Fin N → ℝ) (c : Fin m → ℝ) (I : Fin m → Prop) (x : Fin N → ℝ)
    (hx : ∀ i, (I i → quad (A i) (b i) (c i) x ≤ 0) ∧ (¬ I i → quad (A i) (b i) (c i) x = 0)) :
    (x, vecMulVec x x) ∈ shorFeasible A b c I := by
  refine ⟨aux_vecMulVec_isSymm x, ?_, fun i => ?_⟩
  · rw [liftY_posSemidef_iff, sub_self]; exact PosSemidef.zero
  · simp only [trace_liftQ_mul_liftY, sub_self, Matrix.mul_zero, trace_zero, add_zero]
    exact hx i

end RankRedKit

namespace RankRedKit

theorem aux_liftY_combo {N : ℕ} {a b : ℝ} (hab : a + b = 1) (x y : Fin N → ℝ)
    (X Y : Matrix (Fin N) (Fin N) ℝ) :
    liftY (a • x + b • y) (a • X + b • Y) = a • liftY x X + b • liftY y Y := by
  ext (i | i) (j | j) <;> simp [liftY, Matrix.fromBlocks, hab]

end RankRedKit

namespace RankRedKit

theorem aux_trace_combo {N : ℕ} (Q : Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ) (a b : ℝ)
    (Y₁ Y₂ : Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ) :
    (Q * (a • Y₁ + b • Y₂)).trace = a * (Q * Y₁).trace + b * (Q * Y₂).trace := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, trace_add, trace_smul, trace_smul,
    smul_eq_mul, smul_eq_mul]

end RankRedKit

namespace RankRedKit

theorem aux_combo_nonpos {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : s ≤ 0) (ht : t ≤ 0) :
    a * s + b * t ≤ 0 := by nlinarith

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

theorem partialTrace_posSemidef {k n N : ℕ} (h : k * n = N) {W : Matrix (Fin N) (Fin N) ℝ}
    (hW : W.PosSemidef) : (partialTrace h W).PosSemidef := by
  have : partialTrace h W = ∑ j : Fin k,
      W.submatrix (fun s => blockEquiv h (j, s)) (fun s => blockEquiv h (j, s)) := by
    ext s s'; simp [partialTrace, Matrix.sum_apply]
  rw [this]
  exact posSemidef_sum _ fun j _ => hW.submatrix _

end RankRedKit

namespace RankRedKit

theorem shor_kron_collapse {k n N : ℕ} (h : k * n = N) (x : Fin N → ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) (hY : (liftY x X).PosSemidef) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      ∀ (𝔸 : Matrix (Fin n) (Fin n) ℝ) (b : Fin N → ℝ) (c : ℝ),
        (liftQ (kronMat h 𝔸) b c * liftY x X).trace = quad (kronMat h 𝔸) b c x + (𝔸 * Z).trace := by
  refine ⟨partialTrace h (X - vecMulVec x x),
    partialTrace_posSemidef h ((liftY_posSemidef_iff x X).mp hY), fun 𝔸 b c => ?_⟩
  rw [trace_liftQ_mul_liftY, trace_kronMat_mul]

end RankRedKit

namespace RankRedKit

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

end RankRedKit

namespace RankRedKit

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

end RankRedKit

end

section
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

end

section

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
    refine Convex.mem_convexHull_of_posSemidef_peel P.D Φ ?_ ?_ hZ ?_
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

end
