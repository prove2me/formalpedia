-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.embF_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:18.210041+00:00
-- url     : https://prove2.me/submissions/8b7b5e7e-e96f-431c-99e1-015e0abacd87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_ent_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
theorem _root_.solution (e' : Ent X) (τ : X.Ψ) (x c : Fin r) :
    embF X (Pi.single e' 1) τ x c = if τ = e'.1 ∧ x = e'.2.1.1 ∧ c = e'.2.1.2 then 1 else 0 := by
  unfold embF
  by_cases h1 : c < x
  · rw [dif_pos h1, Pi.single_apply]
    by_cases h2 : τ = e'.1 ∧ x = e'.2.1.1 ∧ c = e'.2.1.2
    · rw [if_pos h2, if_pos ((ent_eq_iff X _ _).2 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 ((ent_eq_iff X _ _).1 h))]
  · rw [dif_neg h1, if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact h1 e'.2.2
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
