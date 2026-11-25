-- Prove2me | solution 1 for PositivityTheory.CW.SecondMomentAlgebra.scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:49.1418+00:00
-- url     : https://prove2.me/submissions/a8aaca48-c201-425b-9cfa-dd369a2927de

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.SecondMomentAlgebra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.SecondMomentAlgebra
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) (hv : v ≠ 0) :
    ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2 =
      ‖v‖ ^ 2 * ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 (((‖v‖ : ℂ)⁻¹) • v)‖ ^ 2 := by
  have h0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm, mul_pow, ← Finset.mul_sum]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]
end PositivityTheory.CW.SecondMomentAlgebra
