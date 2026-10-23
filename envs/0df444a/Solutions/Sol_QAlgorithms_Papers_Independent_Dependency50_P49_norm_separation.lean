-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P49.norm_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:34:11.881+00:00
-- url     : https://prove2.me/submissions/e949cd51-8746-4f05-9df7-6e19be21e90a

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace X7C13NS

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem X7C_cm_apply {dx dy : ℕ} (C : Fin dy → Fin dy → Fin dx → Fin dx → ℂ)
    (X : Matrix (Fin dx) (Fin dx) ℂ) (y z : Fin dy) :
    coefficientMap C X y z = ∑ a, ∑ b, C y z a b * X a b := rfl

theorem X7C_tm_apply (n : ℕ) (p : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    transposeMixture n p X x y =
      ((1 - p : ℝ) : ℂ) * ((n : ℂ)⁻¹ * (if x = y then X.trace else 0)) + (p : ℂ) * X y x := by
  simp only [transposeMixture, uniformDepolarizing, stateReplacement,
    LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    X7C_cm_apply]
  congr 1
  · congr 1
    split_ifs with h
    · simp [maximallyMixed, Matrix.trace, Matrix.one_apply, Finset.mul_sum]
    · simp

theorem X7C_idT_apply (n r : ℕ) (p : ℝ) (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (a b : Fin r) (x y : Fin n) :
    idTensorSuperop (transposeMixture n p) X (a, x) (b, y) =
      ((1 - p : ℝ) : ℂ) * ((n : ℂ)⁻¹ * (if x = y then ∑ i, X (a, i) (b, i) else 0))
        + (p : ℂ) * X (a, y) (b, x) := by
  simp only [idTensorSuperop, Matrix.of_apply, X7C_tm_apply, Matrix.trace, Matrix.diag]


theorem X7C_sum4 {α β : Type*} [Fintype α] [Fintype β] (f : α → β → α → β → ℂ) :
    ∑ a, ∑ x, ∑ b, ∑ i, f a x b i = ∑ x, ∑ i, ∑ a, ∑ b, f a x b i := by
  calc ∑ a, ∑ x, ∑ b, ∑ i, f a x b i = ∑ x, ∑ a, ∑ b, ∑ i, f a x b i := Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ i, ∑ b, f a x b i := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ a, ∑ b, f a x b i := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem X7C_star_ite (c : Prop) [Decidable c] (z : ℂ) :
    star (if c then z else 0) = if c then star z else 0 := by
  split_ifs <;> simp

theorem X7C_uform {r n : ℕ} (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (w : Fin r × Fin n → ℂ) (x y x' y' : Fin n) :
    star (fun q : Fin r × Fin n => if q.2 = y then w (q.1, x) else 0) ⬝ᵥ
      (X *ᵥ (fun q : Fin r × Fin n => if q.2 = y' then w (q.1, x') else 0)) =
      ∑ a, ∑ b, star (w (a, x)) * X (a, y) (b, y') * w (b, x') := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, X7C_star_ite, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

theorem X7C_E1 {r n : ℕ} (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (w : Fin r × Fin n → ℂ) :
    ∑ a, ∑ x, star (w (a, x)) * ∑ b, ∑ y, (if x = y then ∑ i, X (a, i) (b, i) else 0) * w (b, y)
      = ∑ x, ∑ y, ∑ a, ∑ b, star (w (a, x)) * X (a, y) (b, y) * w (b, x) := by
  rw [← X7C_sum4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem X7C_E2 {r n : ℕ} (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (w : Fin r × Fin n → ℂ) :
    ∑ a, ∑ x, star (w (a, x)) * ∑ b, ∑ y, X (a, y) (b, x) * w (b, y)
      = ∑ x, ∑ y, ∑ a, ∑ b, star (w (a, x)) * X (a, y) (b, x) * w (b, y) := by
  rw [← X7C_sum4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem X7C_qf_two {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    star (Pi.single i (1:ℂ) - Pi.single j 1) ⬝ᵥ (M *ᵥ (Pi.single i (1:ℂ) - Pi.single j 1)) =
      M i i - M i j - M j i + M j j := by
  simp only [star_sub, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

theorem X7C_chan {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsQuantumChannel (transposeMixture n p) ↔ n = 1 ∨ p ≤ 1 / ((n : ℝ) + 1) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · rintro ⟨hCP, -⟩
    by_cases h1 : n = 1
    · exact Or.inl h1
    right
    have h2 : 2 ≤ n := by omega
    obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin n, i0 ≠ i1 :=
      ⟨⟨0, hn⟩, ⟨1, h2⟩, by simp [Fin.ext_iff]⟩
    have hY := hCP n _ (Matrix.posSemidef_vecMulVec_self_star
      (fun q : Fin n × Fin n => if q.1 = q.2 then (1:ℂ) else 0))
    have hq := hY.dotProduct_mulVec_nonneg (Pi.single (i0, i1) (1:ℂ) - Pi.single (i1, i0) 1)
    rw [X7C_qf_two] at hq
    simp only [X7C_idT_apply, Matrix.vecMulVec_apply] at hq
    have h10 : i1 ≠ i0 := fun h => h01 h.symm
    simp [h01, h10, Finset.sum_ite_eq, Finset.sum_ite_eq'] at hq
    have hr : (0:ℝ) ≤ 2 * ((1 - p) / n) - 2 * p := by
      first
      | exact Complex.zero_le_real.mp (by convert hq using 1; push_cast; ring)
      | (convert hq using 1; push_cast; ring)
      | nlinarith [hq]
    rw [le_div_iff₀ (by positivity)]
    have h3 : p ≤ (1 - p) / n := by linarith
    rw [le_div_iff₀ hnr] at h3
    nlinarith
  · intro h
    refine ⟨?_, ?_⟩
    · intro r X hX
      rcases h with h1 | h
      · subst h1
        have : idTensorSuperop (transposeMixture 1 p) X = X := by
          ext ⟨a, x⟩ ⟨b, y⟩
          rw [X7C_idT_apply]
          fin_cases x; fin_cases y
          simp
          ring
        rw [this]; exact hX
      have hc : p ≤ (1 - p) / n := by
        rw [le_div_iff₀ hnr]
        rw [le_div_iff₀ (by positivity)] at h
        nlinarith
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · have hh : ∀ q q', star (X q' q) = X q q' := fun q q' => hX.1.apply q q'
        ext ⟨a, x⟩ ⟨b, y⟩
        rw [Matrix.conjTranspose_apply, X7C_idT_apply, X7C_idT_apply]
        by_cases hxy : x = y
        · subst hxy
          simp [hh, star_sum]
        · have hyx : ¬ y = x := fun e => hxy e.symm
          simp [hh, hxy, hyx]
      · intro w
        let u : Fin n → Fin n → (Fin r × Fin n → ℂ) :=
          fun x y q => if q.2 = y then w (q.1, x) else 0
        have hE : star w ⬝ᵥ (idTensorSuperop (transposeMixture n p) X *ᵥ w) =
            ((1 - p : ℝ) : ℂ) * (n : ℂ)⁻¹ * (∑ x, ∑ y, star (u x y) ⬝ᵥ (X *ᵥ u x y)) +
              (p : ℂ) * (∑ x, ∑ y, star (u x y) ⬝ᵥ (X *ᵥ u y x)) := by
          simp only [u, X7C_uform]
          rw [← X7C_E1, ← X7C_E2]
          calc _ = ∑ a, ∑ x, (((1 - p : ℝ) : ℂ) * (n : ℂ)⁻¹ * (star (w (a, x)) *
                ∑ b, ∑ y, (if x = y then ∑ i, X (a, i) (b, i) else 0) * w (b, y)) +
                (p : ℂ) * (star (w (a, x)) * ∑ b, ∑ y, X (a, y) (b, x) * w (b, y))) := by
                simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, X7C_idT_apply,
                  Pi.star_apply]
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
                simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ => ?_
                ring
            _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
        set S := ∑ x, ∑ y, star (u x y) ⬝ᵥ (X *ᵥ u x y) with hSdef
        set R := ∑ x, ∑ y, star (u x y) ⬝ᵥ (X *ᵥ u y x) with hRdef
        have hT : ∑ x, ∑ y, star (u x y + u y x) ⬝ᵥ (X *ᵥ (u x y + u y x)) = 2 * S + 2 * R := by
          simp only [star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
            Finset.sum_add_distrib]
          have e1 : ∑ x, ∑ y, star (u y x) ⬝ᵥ (X *ᵥ u x y) = R := Finset.sum_comm
          have e2 : ∑ x, ∑ y, star (u y x) ⬝ᵥ (X *ᵥ u y x) = S := Finset.sum_comm
          rw [e1, e2]; ring
        have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
          hX.dotProduct_mulVec_nonneg _
        have hT0 : 0 ≤ ∑ x, ∑ y, star (u x y + u y x) ⬝ᵥ (X *ᵥ (u x y + u y x)) :=
          Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hX.dotProduct_mulVec_nonneg _
        rw [hT] at hT0
        have hc' : (0 : ℂ) ≤ (((1 - p) / n - p : ℝ) : ℂ) := Complex.zero_le_real.mpr (by linarith)
        have hp' : (0 : ℂ) ≤ ((p / 2 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by linarith)
        have : star w ⬝ᵥ (idTensorSuperop (transposeMixture n p) X *ᵥ w) =
            (((1 - p) / n - p : ℝ) : ℂ) * S + ((p / 2 : ℝ) : ℂ) * (2 * S + 2 * R) := by
          rw [hE]; push_cast; ring
        rw [this]
        exact add_nonneg (mul_nonneg hc' hS0) (mul_nonneg hp' hT0)
    · ext x y
      rw [X7C_tm_apply]
      by_cases hxy : x = y
      · subst hxy
        simp [Matrix.one_apply, Matrix.trace, hn']
        try (push_cast; ring)
      · have hyx : ¬ y = x := fun e => hxy e.symm
        simp [Matrix.one_apply, hxy, hyx]

theorem X7C_S_apply (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    uniformDepolarizing n X x y = (n : ℂ)⁻¹ * (if x = y then X.trace else 0) := by
  simp only [uniformDepolarizing, stateReplacement, X7C_cm_apply]
  split_ifs with h
  · simp [maximallyMixed, Matrix.trace, Matrix.one_apply, Finset.mul_sum]
  · simp

theorem X7C_D_apply (n : ℕ) (p : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    (transposeMixture n p - uniformDepolarizing n) X x y =
      (p : ℂ) * X y x - (p : ℂ) * ((n : ℂ)⁻¹ * (if x = y then X.trace else 0)) := by
  rw [LinearMap.sub_apply, Matrix.sub_apply, X7C_tm_apply, X7C_S_apply]
  push_cast; ring

theorem X7C_amp_apply (n m : ℕ) (p : ℝ) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (a b : Fin m) (x y : Fin n) :
    QAlgorithms.Papers.Independent.Information100.P50.amplify
      (transposeMixture n p - uniformDepolarizing n) m X (a, x) (b, y) =
      (p : ℂ) * X (a, y) (b, x) -
        (p : ℂ) * ((n : ℂ)⁻¹ * (if x = y then ∑ i, X (a, i) (b, i) else 0)) := by
  simp only [QAlgorithms.Papers.Independent.Information100.P50.amplify, idTensorSuperop,
    Matrix.of_apply, X7C_D_apply, Matrix.trace, Matrix.diag]

section Norms
open scoped Matrix.Norms.L2Operator

theorem X7C_sch {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    QAlgorithms.Papers.Independent.Information100.P50.schattenNorm ⊤ A = ‖A‖ := by
  unfold QAlgorithms.Papers.Independent.Information100.P50.schattenNorm
  rw [if_pos rfl]
  rfl

theorem X7C_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j 1)
  have h2 : ‖(EuclideanSpace.single j (1:ℂ))‖ = 1 := by simp
  rw [h2, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ i)
  simp [Matrix.mulVec]

theorem X7C_norm_star {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ‖(WithLp.toLp 2 (star v) : EuclideanSpace ℂ ι)‖ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  simp [EuclideanSpace.norm_eq]

theorem X7C_map_star_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖A.map star‖ ≤ ‖A‖ := by
  rw [Matrix.cstar_norm_def (A := A.map star)]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun w => ?_)
  have hw : w = WithLp.toLp 2 w.ofLp := rfl
  rw [hw, Matrix.toEuclideanCLM_toLp]
  have key : (A.map star).mulVec w.ofLp = star (A.mulVec (star w.ofLp)) := by
    funext i; simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (star w.ofLp))
  rw [key]
  calc ‖(WithLp.toLp 2 (star (A.mulVec (star w.ofLp))) : EuclideanSpace ℂ ι)‖
      = ‖(WithLp.toLp 2 (A.mulVec (star w.ofLp)) : EuclideanSpace ℂ ι)‖ := X7C_norm_star _
    _ ≤ ‖A‖ * ‖(WithLp.toLp 2 (star w.ofLp) : EuclideanSpace ℂ ι)‖ := h
    _ = ‖A‖ * ‖(WithLp.toLp 2 w.ofLp : EuclideanSpace ℂ ι)‖ := by rw [X7C_norm_star]

theorem X7C_transpose_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖Aᵀ‖ ≤ ‖A‖ := by
  have : Aᵀ = (A.map star)ᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [this, Matrix.l2_opNorm_conjTranspose]
  exact X7C_map_star_le A

theorem X7C_trace_le (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.trace‖ ≤ n * ‖A‖ := by
  unfold Matrix.trace
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => X7C_entry A i i)) ?_
  simp

theorem X7C_induced (n : ℕ) (hn : 0 < n) :
    QAlgorithms.Papers.Independent.Information100.P50.inducedNorm ⊤
      (transposeMixture n (1 / ((n : ℝ) + 1)) - uniformDepolarizing n) ≤ 2 / ((n : ℝ) + 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold QAlgorithms.Papers.Independent.Information100.P50.inducedNorm
  apply csSup_le
  · exact ⟨_, 0, by rw [X7C_sch]; simp, rfl⟩
  · rintro v ⟨X, hX, rfl⟩
    rw [X7C_sch] at hX ⊢
    set p : ℝ := 1 / ((n : ℝ) + 1) with hp
    have hp0 : 0 ≤ p := by positivity
    have hDX : (transposeMixture n p - uniformDepolarizing n) X =
        (p : ℂ) • (Xᵀ - ((n : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      ext x y
      rw [X7C_D_apply]
      by_cases hxy : x = y
      · subst hxy; simp [Matrix.one_apply]; ring
      · simp [Matrix.one_apply, hxy]
    rw [hDX]
    have hc : ‖(n : ℂ)⁻¹ * X.trace‖ ≤ 1 := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      have := X7C_trace_le n X
      calc (n : ℝ)⁻¹ * ‖X.trace‖ ≤ (n : ℝ)⁻¹ * (n * ‖X‖) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = ‖X‖ := by field_simp
        _ ≤ 1 := hX
    have h1 : ‖((n : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
      refine le_trans (norm_smul_le _ _) ?_
      rw [CStarRing.norm_one, mul_one]; exact hc
    have h2 : ‖Xᵀ - ((n : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      have := X7C_transpose_le X
      linarith
    refine le_trans (norm_smul_le _ _) ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hp0]
    calc p * _ ≤ p * 2 := mul_le_mul_of_nonneg_left h2 hp0
      _ = 2 / ((n : ℝ) + 1) := by rw [hp]; ring

end Norms

end X7C13NS

namespace X7C13NS
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P49
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

section CB
open scoped Matrix.Norms.L2Operator

def X7C_L (m n : ℕ) (i j : Fin n) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun q r => if q.1 = r.1 ∧ q.2 = i ∧ r.2 = j then 1 else 0

theorem X7C_Lmul {m n : ℕ} (i j : Fin n) (Y : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (q r : Fin m × Fin n) :
    (X7C_L m n i j * Y) q r = if q.2 = i then Y (q.1, j) r else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : q.2 = i
  · simp [X7C_L, h, ite_and]
  · simp [X7C_L, h]

theorem X7C_mulL {m n : ℕ} (k l : Fin n) (Y : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (q r : Fin m × Fin n) :
    (Y * X7C_L m n k l) q r = if r.2 = l then Y q (r.1, k) else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : r.2 = l
  · simp [X7C_L, h, ite_and, eq_comm]
  · simp [X7C_L, h]

theorem X7C_L_ct {m n : ℕ} (i j : Fin n) : (X7C_L m n i j)ᴴ = X7C_L m n j i := by
  ext q r
  simp only [Matrix.conjTranspose_apply, X7C_L]
  by_cases h : r.1 = q.1 ∧ r.2 = i ∧ q.2 = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.2, h.2.1⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.2, h'.2.1⟩)]; simp

theorem X7C_LL {m n : ℕ} (i j : Fin n) : X7C_L m n j i * X7C_L m n i j = X7C_L m n j j := by
  ext q r
  rw [X7C_Lmul]
  simp only [X7C_L]
  by_cases h : q.2 = j <;> simp [h]

theorem X7C_L_norm {m n : ℕ} (i j : Fin n) : ‖X7C_L m n i j‖ ≤ 1 := by
  have hP : ‖X7C_L m n j j‖ * ‖X7C_L m n j j‖ = ‖X7C_L m n j j‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, X7C_L_ct, X7C_LL]
  have hP1 : ‖X7C_L m n j j‖ ≤ 1 := by
    have := norm_nonneg (X7C_L m n j j)
    nlinarith
  have h : ‖X7C_L m n i j‖ * ‖X7C_L m n i j‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, X7C_L_ct, X7C_LL]; exact hP1
  have := norm_nonneg (X7C_L m n i j)
  nlinarith

theorem X7C_amp_eq (n m : ℕ) (p : ℝ) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P50.amplify
      (transposeMixture n p - uniformDepolarizing n) m X =
      (p : ℂ) • ((∑ i, ∑ j, X7C_L m n i j * X * X7C_L m n i j) -
        (n : ℂ)⁻¹ • (∑ i, ∑ j, X7C_L m n j i * X * X7C_L m n i j)) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  rw [X7C_amp_apply]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply, X7C_mulL, X7C_Lmul,
    smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy; simp [ite_and]; ring
  · simp [ite_and, hxy, Ne.symm hxy]

theorem X7C_sum_norm {m n : ℕ} (f g : Fin n → Fin n → Fin n) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hX : ‖X‖ ≤ 1) :
    ‖∑ i, ∑ j, X7C_L m n (f i j) (g i j) * X * X7C_L m n i j‖ ≤ (n : ℝ) * n := by
  refine le_trans (norm_sum_le _ _) ?_
  have : ∀ i : Fin n, ‖∑ j, X7C_L m n (f i j) (g i j) * X * X7C_L m n i j‖ ≤ n := by
    intro i
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ j : Fin n, ‖X7C_L m n (f i j) (g i j) * X * X7C_L m n i j‖ ≤ 1 := by
      intro j
      refine le_trans (norm_mul_le _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) ?_
      have h1 := X7C_L_norm (m := m) (f i j) (g i j)
      have h2 := X7C_L_norm (m := m) i j
      have h3 := norm_nonneg (X7C_L m n (f i j) (g i j))
      have h4 := norm_nonneg X
      have h5 := norm_nonneg (X7C_L m n i j)
      calc ‖X7C_L m n (f i j) (g i j)‖ * ‖X‖ * ‖X7C_L m n i j‖ ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    refine le_trans (Finset.sum_le_sum (fun j _ => this j)) ?_
    simp
  refine le_trans (Finset.sum_le_sum (fun i _ => this i)) ?_
  simp

def X7C_F (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun q r => if q.1 = r.2 ∧ q.2 = r.1 then 1 else 0

theorem X7C_FF (n : ℕ) : (X7C_F n)ᴴ * X7C_F n = 1 := by
  ext q r
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, X7C_F, Matrix.one_apply]
  obtain ⟨a, x⟩ := q
  obtain ⟨b, y⟩ := r
  by_cases h : a = b ∧ x = y
  · obtain ⟨rfl, rfl⟩ := h
    simp [ite_and]
  · rw [if_neg (by simpa [Prod.ext_iff] using h)]
    simp only [ite_and]
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro z _
    by_cases h1 : c = x <;> by_cases h2 : z = a <;> by_cases h3 : c = y <;> by_cases h4 : z = b <;>
      simp_all

theorem X7C_F_norm (n : ℕ) : ‖X7C_F n‖ ≤ 1 := by
  have h : ‖X7C_F n‖ * ‖X7C_F n‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, X7C_FF]
    by_cases hn : n = 0
    · subst hn
      have : (1 : Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) ℂ) = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]; norm_num
    · haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
      rw [CStarRing.norm_one]
  have := norm_nonneg (X7C_F n)
  nlinarith

def X7C_v (n : ℕ) : Fin n × Fin n → ℂ := fun q => if q.1 = q.2 then 1 else 0

theorem X7C_eig (n : ℕ) (p : ℝ) :
    (QAlgorithms.Papers.Independent.Information100.P50.amplify
      (transposeMixture n p - uniformDepolarizing n) n (X7C_F n)).mulVec (X7C_v n) =
      ((p * n - p * (n : ℝ)⁻¹ : ℝ) : ℂ) • X7C_v n := by
  funext ⟨a, x⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, X7C_amp_apply, X7C_F, X7C_v,
    Pi.smul_apply, smul_eq_mul]
  by_cases hax : a = x
  · subst hax
    simp [ite_and, sub_mul, Finset.sum_sub_distrib]
    ring
  · simp [ite_and, hax, Ne.symm hax, sub_mul, Finset.sum_sub_distrib]


theorem X7C_bdd (n : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    BddAbove {v : ℝ | ∃ (m : ℕ) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
      QAlgorithms.Papers.Independent.Information100.P50.schattenNorm ⊤ X ≤ 1 ∧
      v = QAlgorithms.Papers.Independent.Information100.P50.schattenNorm ⊤
        (QAlgorithms.Papers.Independent.Information100.P50.amplify
          (transposeMixture n p - uniformDepolarizing n) m X)} := by
  refine ⟨p * ((n : ℝ) * n + (n : ℝ)⁻¹ * ((n : ℝ) * n)), ?_⟩
  rintro v ⟨m, X, hX, rfl⟩
  rw [X7C_sch] at hX ⊢
  rw [X7C_amp_eq]
  refine le_trans (norm_smul_le _ _) ?_
  rw [Complex.norm_real, Real.norm_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left _ hp
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := X7C_sum_norm (fun i j => i) (fun i j => j) X hX
  have h2 := X7C_sum_norm (fun i j => j) (fun i j => i) X hX
  refine add_le_add h1 ?_
  refine le_trans (norm_smul_le _ _) ?_
  rw [norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem X7C_cb (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) - 1) / ((n : ℝ) + 1) ≤
      QAlgorithms.Papers.Independent.Information100.P50.cbNorm ⊤
        (transposeMixture n (1 / ((n : ℝ) + 1)) - uniformDepolarizing n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := 1 / ((n : ℝ) + 1) with hp
  have hp0 : 0 ≤ p := by positivity
  unfold QAlgorithms.Papers.Independent.Information100.P50.cbNorm
  refine le_csSup_of_le (X7C_bdd n p hp0) ⟨n, X7C_F n, by rw [X7C_sch]; exact X7C_F_norm n, rfl⟩ ?_
  rw [X7C_sch]
  set M := QAlgorithms.Papers.Independent.Information100.P50.amplify
    (transposeMixture n p - uniformDepolarizing n) n (X7C_F n)
  set c : ℝ := p * n - p * (n : ℝ)⁻¹ with hc
  have hv : (WithLp.toLp 2 (X7C_v n) : EuclideanSpace ℂ (Fin n × Fin n)) ≠ 0 := by
    intro h
    have := congrArg (fun w : EuclideanSpace ℂ (Fin n × Fin n) => w.ofLp (⟨0, hn⟩, ⟨0, hn⟩)) h
    simp [X7C_v] at this
  have hvpos := norm_pos_iff.mpr hv
  have key := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (X7C_v n))
  have hMv : (EuclideanSpace.equiv (Fin n × Fin n) ℂ).symm (M.mulVec (WithLp.toLp 2 (X7C_v n)).ofLp)
      = (c : ℂ) • (WithLp.toLp 2 (X7C_v n) : EuclideanSpace ℂ (Fin n × Fin n)) := by
    change WithLp.toLp 2 (M.mulVec (X7C_v n)) = _
    rw [X7C_eig]; rfl
  rw [hMv, norm_smul, Complex.norm_real] at key
  have hc1 : ‖c‖ ≤ ‖M‖ := le_of_mul_le_mul_right key hvpos
  have hcval : ((n : ℝ) - 1) / ((n : ℝ) + 1) ≤ c := by
    rw [hc, hp]
    have h1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
    rw [div_le_iff₀ (by positivity)]
    field_simp
    have h2 : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact le_trans hcval (le_trans (Real.le_norm_self c) hc1)

theorem X7C_tendsto :
    Tendsto (fun k : ℕ => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm ⊤
      (transposeMixture (k + 1) (1 / (((k + 1 : ℕ) : ℝ) + 1)) -
        uniformDepolarizing (k + 1))) atTop (𝓝 0) := by
  have hg : Tendsto (fun k : ℕ => 2 / (((k + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun k => ?_)
    (fun k => X7C_induced (k + 1) (Nat.succ_pos k))
  apply Real.sSup_nonneg
  rintro v ⟨X, -, rfl⟩
  rw [X7C_sch]; exact norm_nonneg _

end CB
end X7C13NS

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

open QAlgorithms.Papers.Independent.Dependency50.P49 X7C13NS in
theorem solution :
    (∀ n : ℕ, 0 < n →
      IsQuantumChannel (transposeMixture n (1 / ((n : ℝ) + 1))) ∧
      inducedNorm (transposeMixture n (1 / ((n : ℝ) + 1)) - uniformDepolarizing n) ≤
        2 / ((n : ℝ) + 1) ∧
      ((n : ℝ) - 1) / ((n : ℝ) + 1) ≤
        cbNorm (transposeMixture n (1 / ((n : ℝ) + 1)) - uniformDepolarizing n)) ∧
    Tendsto (fun k : ℕ => inducedNorm
      (transposeMixture (k + 1) (1 / (((k + 1 : ℕ) : ℝ) + 1)) -
        uniformDepolarizing (k + 1))) atTop (𝓝 0) := by
  refine ⟨fun n hn => ⟨?_, X7C_induced n hn, X7C_cb n hn⟩, X7C_tendsto⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  refine (X7C_chan hn _ (by positivity) ?_).2 (Or.inr le_rfl)
  rw [div_le_one (by positivity)]
  linarith

end
