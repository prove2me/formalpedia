-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.relIndex_orthProj_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:33.858997+00:00
-- url     : https://prove2.me/submissions/b05e9ae3-e3d3-4411-8351-eb0fbcf5bb63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthProj_mem_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_projectedVector_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r) :
    (Submodule.span ℤ (Set.range (hwv b c))).toAddSubgroup.relIndex
        ((hStd K r).toAddSubgroup.map (hpvHom b)) =
      (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        (hStd K r).toAddSubgroup := by
  classical
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b ⊔
      Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup]
  congr 1
  ext q
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  constructor
  · rintro ⟨hW, hq⟩
    refine ⟨?_, hq⟩
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hW
    set t : Fin r → K := ∑ p, n p • (integralBasis K p.2 • c p.1) with htdef
    have ht : t ∈ Submodule.span (𝓞 K) (Set.range c) := by
      refine Submodule.sum_mem _ fun p _ => Submodule.smul_of_tower_mem _ _ ?_
      rw [integralBasis_apply, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)
    have hft : hpv b t = hpvHom b q := by
      rw [← hn]
      change hpvHom b t = _
      simp only [t, map_sum, map_zsmul]
      rfl
    have hz : hpv b (q - t) = 0 := by
      change hpvHom b (q - t) = 0
      rw [map_sub]
      change hpvHom b q - hpv b t = 0
      rw [hft, sub_self]
    rw [projectedVector_eq_zero_iff hb] at hz
    have htL : t ∈ hStd K r :=
      (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hc j)) ht
    have hsat : q - t ∈ ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b :=
      ⟨Submodule.sub_mem _ hq htL, hz⟩
    have := Submodule.add_mem_sup hsat ht
    rwa [sub_add_cancel] at this
  · rintro ⟨hS, hq⟩
    refine ⟨?_, hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hS
    change hpvHom b (y + z) ∈ _
    rw [map_add]
    have hy0 : hpvHom b y = 0 := (projectedVector_eq_zero_iff hb y).mpr hy.2
    rw [hy0, zero_add]
    exact orthProj_mem_span b c hz
end ReciprocityTheory.ChartRestriction.G.T0
