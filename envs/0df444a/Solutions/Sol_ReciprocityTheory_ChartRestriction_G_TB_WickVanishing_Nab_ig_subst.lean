-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.ig_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:52.403078+00:00
-- url     : https://prove2.me/submissions/614cefa0-62d7-4f1d-bfc4-a2ab7a03b577

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
variable {R k}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, a s ∈ Ig R k τ)
    (hc : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) : subst a f ∈ Ig R k τ := by
  choose a' ha' using fun s => RingHom.mem_range.1 (ha s)
  obtain ⟨f', rfl⟩ := RingHom.mem_range.1 hf
  set b : σ → MvPowerSeries τ R := fun s => a' s - C (constantCoeff (a' s)) with hb
  have hbc : ∀ s, constantCoeff (b s) = 0 := fun s => by simp [hb]
  have hmap : ∀ s, MvPowerSeries.map (algebraMap R k) (b s) = a s := fun s => by
    have e1 : algebraMap R k (constantCoeff (a' s)) = 0 := by
      rw [← hc s, ← ha' s, constantCoeff_map]
    simp [hb, ha' s, e1]
  refine RingHom.mem_range.2 ⟨subst b f', ?_⟩
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero hbc)]
  simp only [hmap]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
