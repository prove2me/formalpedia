-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:36.174527+00:00
-- url     : https://prove2.me/submissions/4b5e5d4e-bae5-4c4f-9a58-73f2e9beb7ad

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_re_star_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ ∀ u, hq H u = normSq (Q *ᵥ u) := by
  have hnn : 0 ≤ H := Matrix.nonneg_iff_posSemidef.mpr hH.posSemidef
  obtain ⟨Q, hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnn
  rw [Matrix.star_eq_conjTranspose] at hQ
  refine ⟨Q, ?_, fun u => ?_⟩
  · intro h0
    have := hH.det_pos
    rw [hQ, det_mul, h0, mul_zero] at this
    exact lt_irrefl _ this
  · have e : star u ᵥ* Qᴴ = star (Q *ᵥ u) := (star_mulVec Q u).symm
    unfold hq
    rw [hQ, ← mulVec_mulVec, dotProduct_mulVec, e, sb_re_star_dot]
end ReciprocityTheory.MultiplicativeHeights
