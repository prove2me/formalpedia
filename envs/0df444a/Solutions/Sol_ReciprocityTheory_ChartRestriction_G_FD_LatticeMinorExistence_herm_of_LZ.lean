-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.herm_of_LZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:20.234723+00:00
-- url     : https://prove2.me/submissions/5d74d785-4889-486b-9944-f0a035bc65a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence

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
theorem _root_.solution {g : ℕ} {b : X.Ψ → Fin 2 → Fin 2 → ℂ} (hb : b ∈ X.LZ g) : IsHermFam b := by
  obtain ⟨β, hβ, -, rfl⟩ := hb
  intro τ i k
  simp only [Data.embH]
  rw [← hβ i k, emb_cc]
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
