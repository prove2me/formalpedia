-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__fromSpec_9b2f586a8f0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:55.701169+00:00
-- url     : https://prove2.me/submissions/3c615f5a-465a-4df7-908d-851d934d5afa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPair
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
private theorem valAt'_eqToHom_lemma {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U U' : Y.Opens} (h : U = U')
    (f : Γ(Y, U')) : valAt' x U (Y.presheaf.map (eqToHom h).op f) = valAt' x U' f := by
  subst h
  simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {Y : Scheme.{0}} {Vo : Y.Opens} (hV : IsAffineOpen Vo) (l : Sp ℂ ⟶ Spec Γ(Y, Vo))
    (a : Γ(Y, Vo)) : valAt' (l ≫ hV.fromSpec) Vo a = valAt' l ⊤ ((Scheme.ΓSpecIso Γ(Y, Vo)).inv a) := by
  rw [← valAt'_comp, IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
  exact valAt'_eqToHom_lemma l hV.fromSpec_preimage_self _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
