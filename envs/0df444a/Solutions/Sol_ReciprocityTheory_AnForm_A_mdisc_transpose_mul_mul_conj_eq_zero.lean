-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_transpose_mul_mul_conj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:45.310545+00:00
-- url     : https://prove2.me/submissions/684ff28f-5b4b-4e73-b188-f21ec3eedb9d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {E : ℕ} (J : Matrix (Fin E) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin E) (Fin E) ℂ) (w : Fin D → ℂ) (hw : w ≠ 0) (hJw : J *ᵥ w = 0) :
    mdisc (fun k => Jᵀ * A k * J.map (starRingEnd ℂ)) = 0 := by
  classical
  have hc : J.map (starRingEnd ℂ) *ᵥ star w = star (J *ᵥ w) := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum]
  have hv : ∀ k, (Jᵀ * A k * J.map (starRingEnd ℂ)) *ᵥ star w = 0 := by
    intro k
    rw [← Matrix.mulVec_mulVec, hc, hJw, star_zero, Matrix.mulVec_zero]
  have hw' : star w ≠ 0 := by simpa using hw
  have h0 : ∀ S : Finset (Fin D), (∑ k ∈ S, Jᵀ * A k * J.map (starRingEnd ℂ)).det = 0 := by
    intro S
    exact Matrix.exists_mulVec_eq_zero_iff.1
      ⟨star w, hw', by rw [Matrix.sum_mulVec]; exact Finset.sum_eq_zero fun k _ => hv k⟩
  simp [mdisc, h0]
end ReciprocityTheory.AnForm.A
