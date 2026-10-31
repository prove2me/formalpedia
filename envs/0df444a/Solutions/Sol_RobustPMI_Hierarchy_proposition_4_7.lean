-- Prove2me | solution 1 for RobustPMI.Hierarchy.proposition_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:17:06.320649+00:00
-- url     : https://prove2.me/submissions/3e8bab72-6619-44df-9653-2f1c9580b111

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_lasserre_theorem_2_6

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.P47aux
open MvPolynomial Matrix RobustPMI.Hierarchy

section G
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma mem_monos (D : ℕ) (α : σ →₀ ℕ) : α ∈ monos (σ := σ) D ↔ α.degree ≤ D := by
  unfold monos
  rw [Finset.mem_filter, Finset.mem_Iic]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro i
  simpa using le_trans (Finsupp.le_degree i α) h

/-- moments of the Dirac measure at `y`. -/
noncomputable def dirac (y : σ → ℝ) : (σ →₀ ℕ) → ℝ := fun α => eval y (monomial α (1 : ℝ))

lemma momentMat_mono_psd {ι : Type*} (S : MatSeq σ ι) {D D' : ℕ} (hD : D' ≤ D)
    (h : (momentMat D S).PosSemidef) : (momentMat D' S).PosSemidef := by
  have e : ∀ p : monos (σ := σ) D', p.1 ∈ monos (σ := σ) D := fun p => by
    have := (mem_monos D' p.1).1 p.2
    exact (mem_monos D p.1).2 (le_trans this hD)
  have := h.submatrix (fun p : (monos (σ := σ) D') × ι => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2))
  have heq : momentMat D' S = (momentMat D S).submatrix
      (fun p : (monos (σ := σ) D') × ι => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2))
      (fun p : (monos (σ := σ) D') × ι => ((⟨p.1.1, e p.1⟩ : monos (σ := σ) D), p.2)) := by
    ext p p'; rfl
  rw [heq]; exact this

end G

variable {ℓ m : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma Hs_eq_of_subset (v : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : h.support ⊆ B) : Hs v h = ∑ α ∈ B, coeff α h * v α := by
  unfold Hs
  refine Finset.sum_subset hB ?_
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Hs_add (v : (σ →₀ ℕ) → ℝ) (p q : MvPolynomial σ ℝ) : Hs v (p + q) = Hs v p + Hs v q := by
  classical
  set B := p.support ∪ q.support ∪ (p + q).support
  rw [Hs_eq_of_subset v (p + q) B Finset.subset_union_right,
    Hs_eq_of_subset v p B (fun x hx => by simp [B, hx]),
    Hs_eq_of_subset v q B (fun x hx => by simp [B, hx]), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add]; ring

lemma Hs_zero (v : (σ →₀ ℕ) → ℝ) : Hs v 0 = 0 := by simp [Hs]

lemma Hs_sum {κ : Type*} (v : (σ →₀ ℕ) → ℝ) (s : Finset κ) (p : κ → MvPolynomial σ ℝ) :
    Hs v (∑ i ∈ s, p i) = ∑ i ∈ s, Hs v (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Hs_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Hs_add, ih]

lemma totalDegree_quadForm (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ)) (v : Fin m → ℝ)
    (D : ℕ) (hQ : ∀ a b, (Q a b).totalDegree ≤ D) : (quadForm Q v).totalDegree ≤ D := by
  unfold quadForm
  refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun b _ => ?_
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, add_zero]
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact hQ a b


lemma Hs_C_mul (v : (Fin ℓ →₀ ℕ) → ℝ) (c : ℝ) (p : MvPolynomial (Fin ℓ) ℝ) :
    Hs v (C c * p) = c * Hs v p := by
  rw [Hs_eq_of_subset v (C c * p) p.support (fun α hα => by
    rw [mem_support_iff, coeff_C_mul] at hα; exact mem_support_iff.2 (right_ne_zero_of_mul hα))]
  unfold Hs
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [coeff_C_mul]; ring

lemma Hs_quadForm (v : (Fin ℓ →₀ ℕ) → ℝ) (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ))
    (w : Fin m → ℝ) : Hs v (quadForm Q w) = ∑ a, ∑ b, w a * Hs v (Q a b) * w b := by
  unfold quadForm
  rw [Hs_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Hs_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm (C (w a) * Q a b) (C (w b)), Hs_C_mul, Hs_C_mul]; ring

end RobustPMI.Hierarchy.P47aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.P47aux MvPolynomial Matrix in
theorem solution {ℓ m : ℕ} (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ))
    (hQ : Q.IsSymm) (hconv : IsPSDSOSConvex Q) (v : (Fin ℓ →₀ ℕ) → ℝ) (hv0 : v 0 = 1)
    (hM : (momentMat ((degMat Q + 1) / 2) (scalarSeq v)).PosSemidef) :
    (Q.map (Hs v) - Q.map (eval (sE v))).PosSemidef := by
  have hsym : ∀ a b, Q b a = Q a b := fun a b => congrFun (congrFun hQ.eq a) b
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun w => ?_⟩
  · ext a b
    simp [conjTranspose_apply, hsym]
  · have hdeg : (quadForm Q w).totalDegree ≤ degMat Q :=
      totalDegree_quadForm Q w _ fun a b =>
        Finset.le_sup (f := fun p : Fin m × Fin m => (Q p.1 p.2).totalDegree) (Finset.mem_univ (a, b))
    have hM' : (momentMat (((quadForm Q w).totalDegree + 1) / 2) (scalarSeq v)).PosSemidef :=
      momentMat_mono_psd _ (by omega) hM
    have J := lasserre_theorem_2_6 (quadForm Q w) (hconv w) v hv0 hM'
    rw [Hs_quadForm] at J
    have hev : eval (sE v) (quadForm Q w) = ∑ a, ∑ b, w a * eval (sE v) (Q a b) * w b := by
      simp [quadForm, map_sum]
    rw [hev] at J
    simp only [dotProduct, mulVec, star_trivial, Matrix.sub_apply, map_apply, Finset.mul_sum]
    have : ∑ a, ∑ b, w a * ((Hs v (Q a b) - eval (sE v) (Q a b)) * w b) =
        ∑ a, ∑ b, w a * Hs v (Q a b) * w b - ∑ a, ∑ b, w a * eval (sE v) (Q a b) * w b := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this]; linarith
