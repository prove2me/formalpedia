-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer.LB_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:21.181896+00:00
-- url     : https://prove2.me/submissions/4a25541d-96c0-4ad9-bfaa-8a02174c69fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_span_L__89e1a95f699d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_LB_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_Tmap_inj
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_exists_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integer_smul_eq_coe_smul
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
theorem _root_.solution (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E)) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (LBsub X β ξ) := by
  refine ⟨?_, ?_⟩
  · rw [LB_eq]
    apply Submodule.FG.map
    apply Submodule.fg_of_fg_map_injective (Tmap β ξ) (Tmap_inj β ξ hli)
    rw [Submodule.map_comap_eq]
    have : IsNoetherian (𝓞 E) X.L' := isNoetherian_of_fg_of_noetherian _ X.L'_fg
    have h1 := IsNoetherian.noetherian ((LinearMap.range (Tmap β ξ) ⊓ X.L').comap X.L'.subtype)
    have h2 := h1.map X.L'.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr inf_le_right] at h2
  · rw [eq_top_iff]
    intro c _
    obtain ⟨d, hd, hdv⟩ := HermitianTraceFormVanishing.exists_smul_mem (F := E) X.L' (x := ∑ k, c k • β k)
      (by rw [span_L' X]; trivial)
    have hd' : (d : E) ≠ 0 := by simpa using hd
    have hdc : (d : E) • c ∈ LBsub X β ξ := by
      refine ⟨0, ?_⟩
      rw [zero_smul, add_zero]
      have e1 : ∑ k, ((d : E) • c) k • β k = d • ∑ k, c k • β k := by
        rw [integer_smul_eq_coe_smul d, Finset.smul_sum]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      rw [e1]
      exact hdv
    have h2 := Submodule.smul_mem (Submodule.span E (LBsub X β ξ : Set (Fin n → E))) ((d : E)⁻¹)
      (Submodule.subset_span hdc)
    rwa [smul_smul, inv_mul_cancel₀ hd', one_smul] at h2
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
