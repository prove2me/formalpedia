-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.dim_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:15.401556+00:00
-- url     : https://prove2.me/submissions/0435ed1b-e4cc-4be9-a6a0-d3aea94ba3f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) {n m : ℕ} (hn : SmoothOfRelativeDimension n f)
    (hm : SmoothOfRelativeDimension m f) (x : X) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have h₂ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).right
    (Localization.Away t) t _ h
  let _ := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have r₁ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n h₁
  have r₂ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m h₂
  exact_mod_cast r₁.symm.trans r₂
end ReciprocityTheory.ChartRestriction.G.H1
