-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.isIsoV_uvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:09.282129+00:00
-- url     : https://prove2.me/submissions/fc087624-c17d-45a7-88a1-557480b1a803

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_uvec_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_hermC_uvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
theorem _root_.solution {u : Fin 2 → Fin r → E} (hu : IsIsoPair X.Gm u) {a : X.Ψ → Fin 2 → ℂ}
    (ha : ∀ τ, a τ ≠ 0) : X.IsIsoV (X.uvec u a) := fun τ => ⟨hermC_uvec X hu.1 a a τ, uvec_ne X hu.2 (ha τ)⟩
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
