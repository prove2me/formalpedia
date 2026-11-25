-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabMap_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:10.644493+00:00
-- url     : https://prove2.me/submissions/0d9371fc-0a7c-4e8a-b27e-bd3b84192a21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabMap_cubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_rigIso_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) {L₁ : RigLB t₁.G} {L₂ : RigLB t₂.G} (h₁ : L₁ = t₁.PP) (h₂ : L₂ = t₂.PP) :
    ∃ ψ : t₁.G ≅ t₂.G, IsMonHom ψ.hom ∧ ψ.hom.left ≫ m₂.φ = m₁.φ ∧
      (∀ x, t₁.act.act x ≫ ψ.hom = ψ.hom ≫ t₂.act.act x) ∧
      ∃ (he : eSec t₁.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec t₂.G) (wL : LB.Iso L₁.L (L₂.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec t₁.G) (fun _ => 1)) L₁.rig
          (rigPullOf ψ.hom.left (𝟙 _) he L₂.L L₂.rig) := by
  subst h₁ h₂
  obtain ⟨ψ, hψ, hφ⟩ := grpPullback_iso m₁.cart m₂.cart
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  refine ⟨ψ, hψ, hφ, fun x => ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, m₂.act, reassoc_of% hφ', hφ', m₁.act]
    · rw [Over.w, Over.w]
  · have := hψ
    obtain ⟨w, h₀, hg, hm⟩ := rigIso_congr rfl (CubeMap.ofHom ψ.hom) (sabMap_cubical m₁ m₂ ψ hφ) rfl rfl
    exact ⟨h₀, w, hg, hm⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
