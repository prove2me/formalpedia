-- Prove2me | solution 2 for PIW.FdPA.det_of_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:33:45.900732+00:00
-- url     : https://prove2.me/submissions/b095624f-947a-4d06-a8d2-0ea8ea5e3ea6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Theorems.Thm_PIW_FdPA_det_ne_of_gram
import Theorems.Thm_PIW_FdPA_lminor_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (τ : X.Ψ) (h : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re) :
    (mat x τ).det ≠ 0 := by
  have h1 := h (Fin.last r)
  have h2 : dmin X.Gm x τ (Fin.last r) ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  unfold dmin at h2
  rw [lminor_last] at h2
  exact det_ne_of_gram _ _ _ h2
end PIW.FdPA
