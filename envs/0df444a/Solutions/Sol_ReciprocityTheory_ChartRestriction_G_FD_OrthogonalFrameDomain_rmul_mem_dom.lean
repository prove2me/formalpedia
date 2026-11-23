-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:52.840873+00:00
-- url     : https://prove2.me/submissions/bd6e49cb-94a0-4d4b-af95-80c58b9252c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_castLE_lemma {r k : ℕ} (hk : k ≤ r) (f : Fin r → ℂ)
    (hf : ∀ j : Fin r, k ≤ (j : ℕ) → f j = 0) : ∑ j, f j = ∑ j : Fin k, f (Fin.castLE hk j) := by
  have hr : r = k + (r - k) := (Nat.add_sub_cancel' hk).symm
  rw [← Equiv.sum_comp (finCongr hr.symm), Fin.sum_univ_add]
  have h2 : ∑ a : Fin (r - k), f (finCongr hr.symm (Fin.natAdd k a)) = 0 :=
    Finset.sum_eq_zero fun a _ => hf _ (by simp)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun j _ => congrArg f (Fin.ext (by simp))
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
theorem _root_.solution {z b : Frame X.Ψ r} (hz : z ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul z b ∈ X.dom := by
  intro τ
  obtain ⟨hz1, hz2⟩ := hz τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hmat : mat (rmul z b) τ = mat z τ * mat b τ := rfl
  have hgram : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a c
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hprod : gram τ.1 X.Gm (mat z τ * mat b τ) =
      (mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ) := by
    rw [hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have htri : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ a c : Fin n, c < a → M a c = 0) →
      M.det = ∏ a, M a a :=
    fun n M h => Matrix.det_of_upperTriangular (fun a c hca => h a c hca)
  have hdiag : ∀ a, mat b τ a a ≠ 0 := by
    have h0 := hb1
    rw [htri r (mat b τ) hb2] at h0
    exact fun a => Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  refine ⟨by rw [hmat, Matrix.det_mul]; exact mul_ne_zero hz1 hb1, fun i => ?_⟩
  have hk : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hsub : ((mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ)).submatrix
        (Fin.castLE hk) (Fin.castLE hk) =
      ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ *
        (gram τ.1 X.Gm (mat z τ)).submatrix (Fin.castLE hk) (Fin.castLE hk) *
        ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine (sum_castLE_lemma hk _ ?_).trans (Finset.sum_congr rfl fun l _ => ?_)
    · intro l hl
      have hc := c.isLt
      have h0 : mat b τ l (Fin.castLE hk c) = 0 :=
        hb2 l (Fin.castLE hk c) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_right _ ((map_eq_zero _).mpr h0)
    · refine congrArg (fun s => s * _) (sum_castLE_lemma hk _ ?_)
      intro j hj
      have ha := a.isLt
      have h0 : mat b τ j (Fin.castLE hk a) = 0 :=
        hb2 j (Fin.castLE hk a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_left h0 _
  set d := ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det with hd
  have hdne : d ≠ 0 := by
    rw [hd, htri (i : ℕ) ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))
      (fun a c h => hb2 _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]; exact h))]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag (Fin.castLE hk a)
  have hdetmap : (((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ d := by
    rw [hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hclaim : dmin X.Gm (rmul z b) τ i = ((Complex.normSq d : ℝ) : ℂ) * dmin X.Gm z τ i := by
    unfold dmin lminor
    rw [hmat, hprod, hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetmap, ← hd,
      mul_right_comm, Complex.mul_conj]
  rw [hclaim, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hdne
  calc (0 : ℝ) < Complex.normSq d * (psgn X.p0 i * (dmin X.Gm z τ i).re) := mul_pos hpos (hz2 i)
    _ = _ := by ring
end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
