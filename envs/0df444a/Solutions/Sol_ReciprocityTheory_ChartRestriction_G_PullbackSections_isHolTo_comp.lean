-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:00.936592+00:00
-- url     : https://prove2.me/submissions/7a763b48-f802-4843-a5bf-634950d448cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {Y Y' : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)} (hy : IsHolTo B y) (φ : Y ⟶ Y') :
    IsHolTo B (fun b => y b ≫ φ) := by
  intro U f
  have hpre : ∀ b, (y b ≫ φ) ⁻¹ᵁ U = y b ⁻¹ᵁ (φ ⁻¹ᵁ U) := fun b => by
    first
      | rfl
      | simp
  obtain ⟨h1, h2⟩ := hy (φ ⁻¹ᵁ U) (φ.app U f)
  simp only [hpre]
  refine ⟨h1, ?_⟩
  refine h2.congr (fun b hb => ?_)
  have hb2 : ⊤ ≤ (y b ≫ φ) ⁻¹ᵁ U := by
    rw [hpre]
    exact hb.2
  unfold valAt'
  rw [dif_pos hb2, dif_pos hb.2]
  first
    | rfl
    | simp [Scheme.comp_app]
    | (simp only [Scheme.comp_app]; done)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
