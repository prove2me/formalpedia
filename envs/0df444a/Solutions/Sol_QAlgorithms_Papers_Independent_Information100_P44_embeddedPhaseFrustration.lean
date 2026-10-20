-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.embeddedPhaseFrustration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:52:02.887347+00:00
-- url     : https://prove2.me/submissions/0827ff49-ec4a-4f05-8544-740f4378c1e3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

noncomputable section
open scoped ComplexConjugate ComplexOrder Matrix
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44

attribute [local instance] Classical.propDecidable

lemma g53i_rank_one {n : Type*} [Fintype n] (w : n → ℂ) (hw : w ≠ 0) :
    (Matrix.vecMulVec w (fun i => conj (w i))).rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le _ _)
  rw [Nat.one_le_iff_ne_zero]
  intro h
  unfold Matrix.rank at h
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  have hA : Matrix.vecMulVec w (fun i => conj (w i)) = 0 := by
    apply Matrix.toLin'.injective; rw [map_zero]; exact h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have := congrFun (congrFun hA i) i
  rw [Matrix.vecMulVec_apply, Matrix.zero_apply, Complex.mul_conj] at this
  exact hi (Complex.normSq_eq_zero.mp (by exact_mod_cast this))

lemma g53i_psd_one {n : Type*} [Fintype n] (w : n → ℂ) :
    (Matrix.vecMulVec w (fun i => conj (w i))).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star w

/-- PDF p.22, Corollary 6: zero extension embeds phase frustration in (g,g,1) sectors. -/
theorem solution (g : ℕ) (hg : 1 ≤ g) :
    ∃ u v : Fin g → ℂ,
      (∑ i, Complex.normSq (u i)) = 1 ∧ (∑ i, Complex.normSq (v i)) = 1 ∧
      (∃ V : Matrix (Fin g ⊕ (Fin g ⊕ Fin 1)) (Fin 3) ℂ,
        Vᴴ * V = 1 ∧ frustrationEmbedding u v = V * frustration * Vᴴ) ∧
      (Matrix.fromBlocks
        (Matrix.vecMulVec u (fun i => conj (u i)))
        (-Matrix.vecMulVec u (fun i => conj (v i)))
        (-Matrix.vecMulVec v (fun i => conj (u i)))
        (Matrix.vecMulVec v (fun i => conj (v i)))).PosSemidef ∧
      (Matrix.fromBlocks
        (Matrix.vecMulVec u (fun i => conj (u i)))
        (-Matrix.vecMulVec u (fun i => conj (v i)))
        (-Matrix.vecMulVec v (fun i => conj (u i)))
        (Matrix.vecMulVec v (fun i => conj (v i)))).rank = 1 ∧
      (Matrix.fromBlocks (Matrix.vecMulVec u (fun i => conj (u i)))
        (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) i => conj (u i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).PosSemidef ∧
      (Matrix.fromBlocks (Matrix.vecMulVec u (fun i => conj (u i)))
        (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) i => conj (u i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).rank = 1 ∧
      (Matrix.fromBlocks (Matrix.vecMulVec v (fun i => conj (v i)))
        (fun i (_ : Fin 1) => v i) (fun (_ : Fin 1) i => conj (v i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).PosSemidef ∧
      (Matrix.fromBlocks (Matrix.vecMulVec v (fun i => conj (v i)))
        (fun i (_ : Fin 1) => v i) (fun (_ : Fin 1) i => conj (v i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).rank = 1 ∧
      ¬ (frustrationEmbedding u v).PosSemidef := by
  let i0 : Fin g := ⟨0, hg⟩
  let u : Fin g → ℂ := Pi.single i0 1
  have hu : (∑ i, Complex.normSq (u i)) = 1 := by
    rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [u, hb]) (by simp)]; simp [u]
  have hcu : ∀ i, conj (u i) * u i = (Complex.normSq (u i) : ℂ) := fun i => by
    rw [mul_comm, Complex.mul_conj]
  let V : Matrix (Fin g ⊕ (Fin g ⊕ Fin 1)) (Fin 3) ℂ := Matrix.of fun x k =>
    Sum.elim (fun i => if k = 0 then u i else 0)
      (Sum.elim (fun i => if k = 1 then u i else 0) (fun _ => if k = 2 then 1 else 0)) x
  have hV : Vᴴ * V = 1 := by
    have hs : (∑ i, conj (u i) * u i) = 1 := by
      simp_rw [hcu]; exact_mod_cast hu
    ext k l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type, V,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
    fin_cases k <;> fin_cases l <;> simp [hs, RCLike.star_def]
  have hemb : frustrationEmbedding u u = V * frustration * Vᴴ := by
    ext (x | x | x) (y | y | y) <;>
      simp [frustrationEmbedding, ladderGram, augment, frustration, V, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.conjTranspose_apply, Matrix.fromBlocks, Matrix.vecMulVec_apply,
        Matrix.of_apply, mul_comm] <;> rfl
  have hne : u ≠ 0 := fun h => by
    have := congrFun h i0; simp [u] at this
  let w1 : Fin g ⊕ Fin g → ℂ := Sum.elim u (-u)
  have hM1 : Matrix.fromBlocks
        (Matrix.vecMulVec u (fun i => conj (u i)))
        (-Matrix.vecMulVec u (fun i => conj (u i)))
        (-Matrix.vecMulVec u (fun i => conj (u i)))
        (Matrix.vecMulVec u (fun i => conj (u i))) = Matrix.vecMulVec w1 (fun i => conj (w1 i)) := by
    ext (i | i) (j | j) <;> simp [w1, Matrix.vecMulVec_apply]
  let w2 : Fin g ⊕ Fin 1 → ℂ := Sum.elim u (fun _ => 1)
  have hM2 : Matrix.fromBlocks (Matrix.vecMulVec u (fun i => conj (u i)))
        (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) i => conj (u i))
        (fun (_ _ : Fin 1) => (1 : ℂ)) = Matrix.vecMulVec w2 (fun i => conj (w2 i)) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, w2, Matrix.vecMulVec_apply]
  have hw1 : w1 ≠ 0 := fun h => hne (funext fun i => by simpa [w1] using congrFun h (Sum.inl i))
  have hw2 : w2 ≠ 0 := fun h => by simpa [w2] using congrFun h (Sum.inr 0)
  refine ⟨u, u, hu, hu, ⟨V, hV, hemb⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hM1]; exact g53i_psd_one w1
  · rw [hM1]; exact g53i_rank_one w1 hw1
  · rw [hM2]; exact g53i_psd_one w2
  · rw [hM2]; exact g53i_rank_one w2 hw2
  · rw [hM2]; exact g53i_psd_one w2
  · rw [hM2]; exact g53i_rank_one w2 hw2
  · intro hpsd
    rw [hemb] at hpsd
    have hF := hpsd.conjTranspose_mul_mul_same V
    have : Vᴴ * (V * frustration * Vᴴ) * V = frustration := by
      rw [show Vᴴ * (V * frustration * Vᴴ) * V = (Vᴴ * V) * frustration * (Vᴴ * V) by
        simp only [Matrix.mul_assoc]]
      rw [hV, Matrix.one_mul, Matrix.mul_one]
    rw [this] at hF
    have h3 := hF.dotProduct_mulVec_nonneg ![1, 1, -1]
    simp [frustration, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at h3
    norm_num at h3

end
