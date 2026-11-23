-- Prove2me | solution 1 for PlatonicJEPA.k_pairs_identify_rotation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:15:06.168937+00:00
-- url     : https://prove2.me/submissions/5d66b24d-57f8-4efd-b4fa-923b069d689c

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology
namespace PlatonicJEPA

theorem AuxKP_sqNorm_eq_zero {k : ℕ} (v : Fin k → ℝ) (h : sqNorm v = 0) : v = 0 := by
  unfold sqNorm at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp h i (Finset.mem_univ _)
  simpa using this

theorem AuxKP_sqNorm_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (v j))


theorem k_pairs_identify_rotation {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (h₁ h₂ : Z → Fin k → ℝ) :
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      IsWhitened p h₁ → IsWhitened p (fun z => rot Q (h₁ z))) ∧
    (∀ (Q : Matrix.orthogonalGroup (Fin k) ℝ), (∀ z, h₁ z = rot Q (h₂ z)) →
      ∀ (n : ℕ) (zs : Fin n → Z), k ≤ n →
        Submodule.span ℝ (Set.range fun i => h₂ (zs i)) = ⊤ →
        ∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          ((∀ R' : Matrix.orthogonalGroup (Fin k) ℝ,
              ∑ i, sqNorm (h₁ (zs i) - rot R (h₂ (zs i))) ≤
                ∑ i, sqNorm (h₁ (zs i) - rot R' (h₂ (zs i)))) ↔ R = Q)) := by
  constructor
  · intro Q hw
    have hQ : (Q : Matrix (Fin k) (Fin k) ℝ) * star (Q : Matrix (Fin k) (Fin k) ℝ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff _ _).mp Q.2
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · simp only [rot, Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc _ = ∑ j, (Q : Matrix (Fin k) (Fin k) ℝ) i j * ∑ z, p z * h₁ z j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
        _ = 0 := by simp [hw.1]
    · simp only [rot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      have e1 : ∀ a b, ∑ z, p z * h₁ z a * h₁ z b = if a = b then 1 else 0 := hw.2
      calc _ = ∑ a, ∑ b, (Q : Matrix (Fin k) (Fin k) ℝ) i b * (Q : Matrix (Fin k) (Fin k) ℝ) j a *
              ∑ z, p z * h₁ z b * h₁ z a := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
        _ = ∑ a, (Q : Matrix (Fin k) (Fin k) ℝ) i a * (Q : Matrix (Fin k) (Fin k) ℝ) j a := by
            simp only [e1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        _ = ((Q : Matrix (Fin k) (Fin k) ℝ) * star (Q : Matrix (Fin k) (Fin k) ℝ)) i j := by
            simp [Matrix.mul_apply, Matrix.star_apply]
        _ = _ := by rw [hQ, Matrix.one_apply]
  · intro Q hQ n zs _ hspan R
    constructor
    · intro hmin
      have h1 := hmin Q
      have h0 : ∑ i, sqNorm (h₁ (zs i) - rot Q (h₂ (zs i))) = 0 := by
        simp [hQ, sqNorm]
      rw [h0] at h1
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => AuxKP_sqNorm_nonneg _)).mp
        (le_antisymm h1 (Finset.sum_nonneg fun i _ => AuxKP_sqNorm_nonneg _))
      have hagree : ∀ i, Matrix.mulVecLin (R : Matrix (Fin k) (Fin k) ℝ) (h₂ (zs i)) =
          Matrix.mulVecLin (Q : Matrix (Fin k) (Fin k) ℝ) (h₂ (zs i)) := by
        intro i
        have := AuxKP_sqNorm_eq_zero _ (hz i (Finset.mem_univ _))
        rw [hQ, sub_eq_zero] at this
        simp only [Matrix.mulVecLin_apply]
        exact this.symm
      have hlin := LinearMap.ext_on_range hspan hagree
      apply Subtype.ext
      exact Matrix.toLin'.injective (by simpa [Matrix.toLin'_apply'] using hlin)
    · rintro rfl R'
      have h0 : ∑ i, sqNorm (h₁ (zs i) - rot R (h₂ (zs i))) = 0 := by
        simp [hQ, sqNorm]
      rw [h0]
      exact Finset.sum_nonneg fun i _ => AuxKP_sqNorm_nonneg _


end PlatonicJEPA


open PlatonicJEPA in
theorem solution {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (h₁ h₂ : Z → Fin k → ℝ) :
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      IsWhitened p h₁ → IsWhitened p (fun z => rot Q (h₁ z))) ∧
    (∀ (Q : Matrix.orthogonalGroup (Fin k) ℝ), (∀ z, h₁ z = rot Q (h₂ z)) →
      ∀ (n : ℕ) (zs : Fin n → Z), k ≤ n →
        Submodule.span ℝ (Set.range fun i => h₂ (zs i)) = ⊤ →
        ∀ R : Matrix.orthogonalGroup (Fin k) ℝ,
          ((∀ R' : Matrix.orthogonalGroup (Fin k) ℝ,
              ∑ i, sqNorm (h₁ (zs i) - rot R (h₂ (zs i))) ≤
                ∑ i, sqNorm (h₁ (zs i) - rot R' (h₂ (zs i)))) ↔ R = Q)) :=
  PlatonicJEPA.k_pairs_identify_rotation p h₁ h₂
