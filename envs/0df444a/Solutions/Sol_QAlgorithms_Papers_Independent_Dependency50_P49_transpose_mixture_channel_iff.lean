-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P49.transpose_mixture_channel_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:36:00.108345+00:00
-- url     : https://prove2.me/submissions/3c11e3dd-8d80-44c7-9541-fa6a57abb753

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem g52b_cm_apply {dx dy : ℕ} (C : Fin dy → Fin dy → Fin dx → Fin dx → ℂ)
    (X : Matrix (Fin dx) (Fin dx) ℂ) (y z : Fin dy) :
    coefficientMap C X y z = ∑ a, ∑ b, C y z a b * X a b := rfl

theorem g52b_tm_apply (n : ℕ) (p : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    transposeMixture n p X x y =
      ((1 - p : ℝ) : ℂ) * ((n : ℂ)⁻¹ * (if x = y then X.trace else 0)) + (p : ℂ) * X y x := by
  simp only [transposeMixture, uniformDepolarizing, stateReplacement,
    LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    g52b_cm_apply]
  congr 1
  · congr 1
    split_ifs with h
    · simp [maximallyMixed, Matrix.trace, Matrix.one_apply, Finset.mul_sum]
    · simp

theorem g52b_idT_apply (n r : ℕ) (p : ℝ) (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (a b : Fin r) (x y : Fin n) :
    idTensorSuperop (transposeMixture n p) X (a, x) (b, y) =
      ((1 - p : ℝ) : ℂ) * ((n : ℂ)⁻¹ * (if x = y then ∑ i, X (a, i) (b, i) else 0))
        + (p : ℂ) * X (a, y) (b, x) := by
  simp only [idTensorSuperop, Matrix.of_apply, g52b_tm_apply, Matrix.trace, Matrix.diag]


theorem g52b_sum4 {α β : Type*} [Fintype α] [Fintype β] (f : α → β → α → β → ℂ) :
    ∑ a, ∑ x, ∑ b, ∑ i, f a x b i = ∑ x, ∑ i, ∑ a, ∑ b, f a x b i := by
  calc ∑ a, ∑ x, ∑ b, ∑ i, f a x b i = ∑ x, ∑ a, ∑ b, ∑ i, f a x b i := Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ i, ∑ b, f a x b i := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ a, ∑ b, f a x b i := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem g52b_star_ite (c : Prop) [Decidable c] (z : ℂ) :
    star (if c then z else 0) = if c then star z else 0 := by
  split_ifs <;> simp

theorem g52b_uform {r n : ℕ} (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (w : Fin r × Fin n → ℂ) (x y x' y' : Fin n) :
    star (fun q : Fin r × Fin n => if q.2 = y then w (q.1, x) else 0) ⬝ᵥ
      (X *ᵥ (fun q : Fin r × Fin n => if q.2 = y' then w (q.1, x') else 0)) =
      ∑ a, ∑ b, star (w (a, x)) * X (a, y) (b, y') * w (b, x') := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, g52b_star_ite, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

theorem g52b_E1 {r n : ℕ} (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (w : Fin r × Fin n → ℂ) :
    ∑ a, ∑ x, star (w (a, x)) * ∑ b, ∑ y, (if x = y then ∑ i, X (a, i) (b, i) else 0) * w (b, y)
      = ∑ x, ∑ y, ∑ a, ∑ b, star (w (a, x)) * X (a, y) (b, y) * w (b, x) := by
  rw [← g52b_sum4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem g52b_E2 {r n : ℕ} (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (w : Fin r × Fin n → ℂ) :
    ∑ a, ∑ x, star (w (a, x)) * ∑ b, ∑ y, X (a, y) (b, x) * w (b, y)
      = ∑ x, ∑ y, ∑ a, ∑ b, star (w (a, x)) * X (a, y) (b, x) * w (b, y) := by
  rw [← g52b_sum4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem g52b_qf_two {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    star (Pi.single i (1:ℂ) - Pi.single j 1) ⬝ᵥ (M *ᵥ (Pi.single i (1:ℂ) - Pi.single j 1)) =
      M i i - M i j - M j i + M j j := by
  simp only [star_sub, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

theorem solution {n : ℕ} (hn : 0 < n)
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
    rw [g52b_qf_two] at hq
    simp only [g52b_idT_apply, Matrix.vecMulVec_apply] at hq
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
          rw [g52b_idT_apply]
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
        rw [Matrix.conjTranspose_apply, g52b_idT_apply, g52b_idT_apply]
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
          simp only [u, g52b_uform]
          rw [← g52b_E1, ← g52b_E2]
          calc _ = ∑ a, ∑ x, (((1 - p : ℝ) : ℂ) * (n : ℂ)⁻¹ * (star (w (a, x)) *
                ∑ b, ∑ y, (if x = y then ∑ i, X (a, i) (b, i) else 0) * w (b, y)) +
                (p : ℂ) * (star (w (a, x)) * ∑ b, ∑ y, X (a, y) (b, x) * w (b, y))) := by
                simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, g52b_idT_apply,
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
      rw [g52b_tm_apply]
      by_cases hxy : x = y
      · subst hxy
        simp [Matrix.one_apply, Matrix.trace, hn']
        try (push_cast; ring)
      · have hyx : ¬ y = x := fun e => hxy e.symm
        simp [Matrix.one_apply, hxy, hyx]

end
