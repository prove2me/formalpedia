-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:58.570183+00:00
-- url     : https://prove2.me/submissions/92a98b65-20a0-4d32-a6e0-548c40d1cdb0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf___e42b9125a01b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_mem_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution (hw : G.Good w) :
    Set.InjOn (G.zOf w) {ρ | ρ ∈ (G.P.map (deh w 0)).roots} := by
  intro ρ₁ h₁ ρ₂ h₂ h
  calc ρ₁ = deh (G.zOf w ρ₁) (e 0) G.Θ := (G.deh_zOf_Θ hw (G.mem_roots.1 h₁)).symm
    _ = deh (G.zOf w ρ₂) (e 0) G.Θ := by rw [h]
    _ = ρ₂ := G.deh_zOf_Θ hw (G.mem_roots.1 h₂)
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
