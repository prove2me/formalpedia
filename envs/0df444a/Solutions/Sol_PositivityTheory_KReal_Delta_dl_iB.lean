-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.dl_iB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:36.775293+00:00
-- url     : https://prove2.me/submissions/5b18e7ee-c5fd-49e8-b82f-cfb3b8c04d38

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Theorems.Thm_PositivityTheory_KReal_Delta_dl_XR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.Delta
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.Delta
theorem _root_.solution (v : Pol p q 0 s) : dl p q r s (rename (iB p q r s) v) = (1 : Pol p q r 0) ⊗ₜ[ℂ] v := by
  have h : (dl p q r s).comp (rename (iB p q r s)) =
      (Algebra.TensorProduct.includeRight (R := ℂ) (A := Pol p q r 0) (B := Pol p q 0 s)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k | k⟩
    · exact k.elim0
    · simp [iB, dl_XR]
  simpa using DFunLike.congr_fun h v
end PositivityTheory.KReal.Delta
