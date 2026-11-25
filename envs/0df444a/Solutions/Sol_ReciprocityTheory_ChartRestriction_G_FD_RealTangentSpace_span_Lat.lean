-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.span_Lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:51.204809+00:00
-- url     : https://prove2.me/submissions/f79b28ba-2f13-47c6-b10f-79815fb185c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_VT_val_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_mem_Lat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_Uz_le_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
variable [hz : Fact (z ∈ X.dom)]
namespace ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) (hξ : X.IsIso ξ) :
    Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  let S : VT (X := X) z ξ →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun a => a.val
      map_add' := fun a b => VT.val_add a b
      map_smul' := fun c a => VT.val_smul c a }
  have hS : Function.Injective S := fun a b h => VT.ext h
  have h1 := LatticeSpanMembership.Uz_le_span hD3 hξ v.val_mem
  have h2 : Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) ≤
      Submodule.map S (Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ))) := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span ((mem_Lat z ξ hξ).mpr ⟨μ, rfl⟩))
  obtain ⟨w, hw, hwv⟩ := h2 h1
  rwa [hS hwv] at hw
end ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
