-- Prove2me | solution 1 for PIW.FdPA.mem_dom_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:43.163513+00:00
-- url     : https://prove2.me/submissions/1c399a6e-24ae-4833-b46d-25db905e5302

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames

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
    (x : Frame X.Ψ r) : x ∈ X.dom ↔ ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := Iff.rfl
end PIW.FdPA
