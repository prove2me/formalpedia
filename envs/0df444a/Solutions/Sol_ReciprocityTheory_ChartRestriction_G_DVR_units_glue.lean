-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.units_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:45.660618+00:00
-- url     : https://prove2.me/submissions/9e7a0f0e-e974-4e40-9625-1348d4ed647b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (u : ∀ i, Γ(Y, V i)ˣ)
    (hu : ∀ i j, res (inf_le_left : V i ⊓ V j ≤ V i) (u i) = res (inf_le_right : V i ⊓ V j ≤ V j) (u j)) :
    ∃ w : Γ(Y, W)ˣ, ∀ i, res (hle i) w = u i := by
  have hv : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom ((u i : Γ(Y, V i))) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom ((u j : Γ(Y, V j))) :=
    fun i j => congrArg Units.val (hu i j)
  have hv' : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom (((u i)⁻¹ : Γ(Y, V i)ˣ) : Γ(Y, V i)) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom (((u j)⁻¹ : Γ(Y, V j)ˣ) : Γ(Y, V j)) := by
    intro i j
    have := congrArg (fun x => ((x⁻¹ : Γ(Y, V i ⊓ V j)ˣ) : Γ(Y, V i ⊓ V j))) (hu i j)
    simpa [res] using this
  obtain ⟨g, hg, -⟩ := sec_glue W V hle hcov (fun i => (u i : Γ(Y, V i))) hv
  obtain ⟨g', hg', -⟩ := sec_glue W V hle hcov (fun i => ((u i)⁻¹ : Γ(Y, V i)ˣ)) hv'
  have h1 : g * g' = 1 := by
    obtain ⟨o, -, ho⟩ := sec_glue W V hle hcov (fun _ => 1) (fun i j => by simp)
    have e1 := ho (g * g') (fun i => by rw [map_mul, hg i, hg' i]; simp)
    have e2 := ho 1 (fun i => by simp)
    rw [e1, e2]
  refine ⟨⟨g, g', h1, by rw [mul_comm]; exact h1⟩, fun i => ?_⟩
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  exact hg i
end ReciprocityTheory.ChartRestriction.G.DVR
