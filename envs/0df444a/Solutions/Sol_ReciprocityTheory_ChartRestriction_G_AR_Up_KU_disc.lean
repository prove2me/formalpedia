-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:05.054595+00:00
-- url     : https://prove2.me/submissions/6dc6ba03-d280-48e3-8ee9-a6ec63b549e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_orth_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Phi_rho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_Phi_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_oneF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (hPD : PropDisc X) :
    DiscreteTopology ((rho X ho).comp X.Γ.subtype).range := by
  apply discreteTopology_of_isOpen_singleton_one
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 (orth_dom X ho) x0 (orth_dom X ho)
  have h1 : Phi X x0 ⁻¹' U' ∈ 𝓝 (1 : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) := by
    refine (Phi_cont X x0).continuousAt.preimage_mem_nhds ?_
    rw [← map_one (rho X ho), Phi_rho, lact_one]; exact hU'
  have hF : IsClosed ((rho X ho '' {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r,
      lact γ u = rmul u' b}) \ {1}) := ((hfin.image _).sdiff).isClosed
  rw [isOpen_induced_iff]
  refine ⟨interior (Phi X x0 ⁻¹' U') \ _, isOpen_interior.sdiff hF, ?_⟩
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hg1, hg2⟩
    obtain ⟨γ, hγ⟩ := g.2
    apply Subtype.ext
    by_contra hne
    apply hg2
    have hU'γ : lact γ.1 x0 ∈ U' := by
      have := interior_subset hg1
      rw [Set.mem_preimage, ← hγ] at this
      rwa [MonoidHom.comp_apply, Subgroup.subtype_apply, Phi_rho] at this
    exact ⟨⟨γ.1, ⟨γ.2, x0, mem_of_mem_nhds hU, lact γ.1 x0, hU'γ, ExtFPf.oneF X, ExtFPf.oneF_mem X,
      (ExtFPf.rmul_oneF X _).symm⟩, hγ⟩, hne⟩
  · rintro rfl
    exact ⟨mem_interior_iff_mem_nhds.2 h1, fun h => h.2 rfl⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
