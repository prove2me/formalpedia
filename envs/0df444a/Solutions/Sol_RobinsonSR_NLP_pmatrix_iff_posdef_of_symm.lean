-- Prove2me | solution 1 for RobinsonSR.NLP.pmatrix_iff_posdef_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:02:40.411266+00:00
-- url     : https://prove2.me/submissions/7c2fef9e-5591-4253-bfa6-44ed2b918714

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix
open Matrix Polynomial

private theorem det_perturb_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : RobinsonSR.NLP.IsPMatrix M)
    (t : ℝ) (ht : 0 ≤ t) : 0 < (1 + t • M).det := by
  let p : ℝ[X] := (1 + (X : ℝ[X]) • M.map C).det
  have hc (n : ℕ) : 0 ≤ p.coeff n := by
    rw [show p = (1 + (X : ℝ[X]) • M.map C).det from rfl,
      Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    apply Finset.sum_nonneg
    intro J hJ
    rcases J.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact (hM J hne).le
  have h0 : p.coeff 0 = 1 := by
    dsimp [p]
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_det_add_X_smul]
    simp
  have hp : 0 < p.eval t := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    apply Finset.sum_pos'
    · intro n hn
      exact mul_nonneg (hc n) (pow_nonneg ht n)
    · refine ⟨0, ?_, ?_⟩
      · exact Polynomial.mem_support_iff.mpr (by rw [h0]; norm_num)
      · simp [h0]
  have heval : p.eval t = (1 + t • M).det := by
    rw [show p = (1 + (X : ℝ[X]) • M.map C).det from rfl,
      Polynomial.eval, ← Polynomial.coe_eval₂RingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp <;> ring
  rwa [heval] at hp

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    RobinsonSR.NLP.IsPMatrix M ↔ RobinsonSR.Schur.PosDefNS M := by
  have hH : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  have hiff : M.PosDef ↔ RobinsonSR.Schur.PosDefNS M := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    simp only [RobinsonSR.Schur.PosDefNS, star_trivial, hH, true_and]
  constructor
  · intro hp
    apply hiff.mp
    apply hH.posDef_iff_eigenvalues_pos.mpr
    intro i
    let v : ι → ℝ := ⇑(hH.eigenvectorBasis i)
    have hv : v ≠ 0 := by
      intro hz
      have hz' : hH.eigenvectorBasis i = 0 := by
        ext j
        exact congrFun hz j
      exact hH.eigenvectorBasis.toBasis.ne_zero i hz'
    have hm : M *ᵥ v = hH.eigenvalues i • v := hH.mulVec_eigenvectorBasis i
    have hnonsing : M.det ≠ 0 := by
      have hne : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
      have hd := hp Finset.univ hne
      have he : (M.submatrix (fun j : (Finset.univ : Finset ι) => (j : ι))
          (fun j : (Finset.univ : Finset ι) => (j : ι))).det = M.det := by
        let e : (Finset.univ : Finset ι) ≃ ι :=
          ⟨Subtype.val, fun j => ⟨j, Finset.mem_univ j⟩, fun _ => rfl, fun _ => rfl⟩
        exact Matrix.det_submatrix_equiv_self e M
      rw [he] at hd
      exact ne_of_gt hd
    have heigen_ne : hH.eigenvalues i ≠ 0 := by
      intro hz
      have hm0 : M *ᵥ v = M *ᵥ (0 : ι → ℝ) := by simpa [hz] using hm
      exact hv (Matrix.mulVec_injective_of_det_ne_zero hnonsing hm0)
    by_contra hpos
    have hneg : hH.eigenvalues i < 0 := lt_of_le_of_ne (le_of_not_gt hpos) heigen_ne
    let t : ℝ := -1 / hH.eigenvalues i
    have ht : 0 ≤ t := by
      dsimp [t]
      exact (div_pos_of_neg_of_neg (by norm_num) hneg).le
    have htv : t * hH.eigenvalues i = -1 := by
      dsimp [t]
      field_simp
    have hprod : (1 + t • M) *ᵥ v = 0 := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hm, smul_smul, htv]
      simp
    have hd := det_perturb_pos M hp t ht
    have hz : v = 0 := Matrix.mulVec_injective_of_det_ne_zero (ne_of_gt hd)
      (by simpa using hprod)
    exact hv hz
  · intro hp J hJ
    exact ((hiff.mpr hp).submatrix Subtype.val_injective).det_pos

#print axioms solution
