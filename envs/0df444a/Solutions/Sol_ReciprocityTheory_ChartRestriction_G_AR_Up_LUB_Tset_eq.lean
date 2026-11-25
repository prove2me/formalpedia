-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.Tset_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:00.129485+00:00
-- url     : https://prove2.me/submissions/95ac7ffb-7c51-4d00-92a0-833502086172

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_oneF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_invF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_rmul_mem_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_rmul_invF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) :
    Tset X (rmul x1' b1) ρ = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := by
  have hTmem : ∀ {y c : Frame X.Ψ r}, c ∈ Bor X.Ψ r →
      (rmul y c ∈ Tset X (rmul x1' b1) ρ ↔ y ∈ Tset X (rmul x1' b1) ρ) := fun hc =>
    KU.rmul_mem_S X (x0 := rmul x1' b1) (FF := Metric.ball 0 ρ) hc
  ext y
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X (rmul x1' b1) z) b ∈ _
    rw [KU.rmul_mem_S X hb, hs.2.2]
    exact ⟨(Φ X b1 D z, β X b1 D z), ⟨⟨z, hz, rfl⟩, hs.2.1⟩, rfl⟩
  · rintro ⟨⟨w, b⟩, ⟨⟨z, hz, rfl⟩, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X x1' (Φ X b1 D z)) b ∈ Tset X (rmul x1' b1) ρ
    rw [hTmem hb, ← MI.rmul_invF X (y := cpt X x1' (Φ X b1 D z)) hs.2.1, ← hs.2.2,
      hTmem (MI.invF_mem' X hs.2.1)]
    exact ⟨(z, ExtFPf.oneF X), ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
