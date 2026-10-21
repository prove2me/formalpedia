-- Prove2me | solution 1 for RestartPD.LPSharp.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T11:43:49.610122+00:00
-- url     : https://prove2.me/submissions/7a84a2fc-d9bb-43f0-902a-93c0effe8202

import Mathlib
import Definitions.Def_RestartPD_LPSharp_LP
set_option autoImplicit false
open scoped InnerProductSpace Matrix
open RestartPD.LPSharp
namespace LPSharpProof
variable {n m : ℕ}
lemma le_rho (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z w : PDSpace n m)
    (r : ℝ) (hr : 0 < r) (hw : w ∈ Wball lpX Set.univ r z) :
    ((gapAt (lpL A b c) z w / r : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by
  rw [rho, if_neg hr.ne']
  exact le_iSup_of_le w (le_iSup_of_le hw le_rfl)
lemma rho_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (hz : z.1 ∈ lpX)
    (r : ℝ) (hr : 0 < r) : 0 ≤ rho (lpL A b c) lpX Set.univ r z := by
  have hw : z ∈ Wball lpX Set.univ r z := ⟨⟨hz,Set.mem_univ _⟩,by simpa using hr.le⟩
  simpa [gapAt] using le_rho A b c z z r hr hw
lemma gap_shrink (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z ((1-t) • z) = t * (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ) := by
  simp only [gapAt,lpL,Prod.smul_fst,Prod.smul_snd,map_smul,real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm z.2 b]
  ring
end LPSharpProof
namespace LPSharpProof
variable {n m : ℕ}
lemma eucl_sq (z : PDSpace n m) :
    eucl n m z ^ 2 = ‖z.1‖^2 + ‖z.2‖^2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 z)
lemma transpose_inner (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    ⟪Matrix.toEuclideanLin Aᵀ y,x⟫_ℝ = ⟪y,Matrix.toEuclideanLin A x⟫_ℝ := by
  simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    LinearMap.adjoint_inner_left (Matrix.toEuclideanLin A) x y
lemma inner_pos (u : EuclideanSpace ℝ (Fin n)) :
    ⟪u,WithLp.toLp 2 (fun i => max (u i) 0)⟫_ℝ =
      ‖(WithLp.toLp 2 (fun i => max (u i) 0) : EuclideanSpace ℝ (Fin n))‖^2 := by
  rw [PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.inner_apply]
  change u i * max (u i) 0 = max (u i) 0 ^ 2
  by_cases hi : 0 ≤ u i
  · rw [max_eq_left hi]; ring
  · rw [max_eq_right (le_of_not_ge hi)]; ring
lemma gap_forward (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z v : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z (z + t • v) =
      t * (⟪Matrix.toEuclideanLin Aᵀ z.2-c,v.1⟫_ℝ +
        ⟪b-Matrix.toEuclideanLin A z.1,v.2⟫_ℝ) := by
  simp only [gapAt,lpL,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,inner_sub_left,transpose_inner]
  rw [real_inner_comm b v.2,real_inner_comm (Matrix.toEuclideanLin A z.1) v.2]
  ring
lemma gap_v (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z (z+t • vvec A b c z) = t * eucl n m (vvec A b c z)^2 := by
  rw [gap_forward,eucl_sq]
  have h := inner_pos (Matrix.toEuclideanLin Aᵀ z.2-c)
  simpa only [vvec,PiLp.sub_apply,real_inner_self_eq_norm_sq] using
    congrArg (fun q => t * (q + ‖b-Matrix.toEuclideanLin A z.1‖^2)) h
end LPSharpProof
theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m)
    (hz : z ∈ (lpX : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Set.univ)
    (r : ℝ) (hr : 0 < r) :
    ((eucl n m (vvec A b c z) : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by
  let v := vvec A b c z
  let q := eucl n m v
  have hq : 0 ≤ q := apply_nonneg _ _
  by_cases hq0 : q = 0
  · change (q : EReal) ≤ _
    rw [hq0,EReal.coe_zero]
    exact LPSharpProof.rho_nonneg A b c z hz.1 r hr
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have ht : 0 ≤ r/q := (div_pos hr hqp).le
  have hw : z+(r/q) • v ∈ Wball lpX Set.univ r z := by
    refine ⟨⟨?_,Set.mem_univ _⟩,?_⟩
    · intro i
      change 0 ≤ z.1 i + (r/q)*max ((Matrix.toEuclideanLin Aᵀ z.2) i-c i) 0
      exact add_nonneg (hz.1 i) (mul_nonneg ht (le_max_right _ _))
    · have he : z-(z+(r/q) • v) = -((r/q) • v) := by abel
      rw [he,map_neg_eq_map,map_smul_eq_mul,Real.norm_of_nonneg ht]
      change r/q*q ≤ r
      rw [div_mul_cancel₀ r hq0]
  have h := LPSharpProof.le_rho A b c z (z+(r/q) • v) r hr hw
  rw [LPSharpProof.gap_v] at h
  have he : r/q * q^2/r = q := by field_simp
  change ((r/q*q^2/r : ℝ) : EReal) ≤ _ at h
  rw [he] at h
  exact h
