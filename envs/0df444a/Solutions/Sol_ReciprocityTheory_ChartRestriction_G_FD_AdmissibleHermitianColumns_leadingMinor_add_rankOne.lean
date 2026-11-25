-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.leadingMinor_add_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:03.80294+00:00
-- url     : https://prove2.me/submissions/b9fb6dd8-8361-4895-91a8-48333eb46b43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
theorem _root_.solution (A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) (i : Fin (r + 1))
    (hA : lminor A i ≠ 0) : ∃ κ : ℂ, ∀ t : ℂ, lminor (A + t • vecMulVec u v) i = lminor A i * (1 + t * κ) := by
  unfold lminor at hA ⊢
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  set B := A.submatrix e e with hB
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨(v ∘ e) ⬝ᵥ (B⁻¹ *ᵥ (u ∘ e)), fun t => ?_⟩
  have hz : B *ᵥ (B⁻¹ *ᵥ (u ∘ e)) = u ∘ e := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hB', one_mulVec]
  have key : B * (1 + vecMulVec (B⁻¹ *ᵥ (u ∘ e)) (t • (v ∘ e))) =
      (A + t • vecMulVec u v).submatrix e e := by
    rw [mul_add, mul_one]
    ext a b
    have hza : ∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k = u (e a) := congrFun hz a
    simp only [Matrix.add_apply, Matrix.mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rw [show ∑ k, B a k * ((B⁻¹ *ᵥ (u ∘ e)) k * (t * v (e b))) =
        (∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k) * (t * v (e b)) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring, hza]
    simp only [hB, Matrix.submatrix_apply]
    ring
  rw [← key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
