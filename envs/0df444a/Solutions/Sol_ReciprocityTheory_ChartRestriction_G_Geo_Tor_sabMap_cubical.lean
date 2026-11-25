-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabMap_cubical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:21.966437+00:00
-- url     : https://prove2.me/submissions/c7f84538-bb00-4cb0-8432-dbe1e45901e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubCancel


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
    (m₂ : SABMap t₂ t f) (ψ : t₁.G ≅ t₂.G) [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ m₂.φ = m₁.φ) :
    (CubeMap.ofHom ψ.hom).IsPullCubical t₁.cub t₂.cub := by
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  have h3 : m₁.cm.F3 = (CubeMap.ofHom ψ.hom).F3 ≫ m₂.cm.F3 := hom_ext_triple _ fun i => by
    rw [cubeMap_comp_proj_three, Category.assoc, cubeMap_comp_proj_three]
    show _ = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ≫ _
    rw [← Category.assoc, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, Category.assoc, hφ']
  exact pullCubCancel _ _ _ _ _ _ m₂.cm (CubeMap.ofHom ψ.hom) m₁.cm _ _ _ t.cub t₂.cub t₁.cub hφ'.symm h3
    (by show m₁.cm.e = 𝟙 _ ≫ m₂.cm.e; rw [Category.id_comp, m₁.base, m₂.base]) m₂.lin m₁.lin
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
