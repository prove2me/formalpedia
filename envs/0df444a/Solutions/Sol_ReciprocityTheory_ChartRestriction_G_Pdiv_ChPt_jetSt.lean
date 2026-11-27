-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.jetSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:27:15.322535+00:00
-- url     : https://prove2.me/submissions/c133dadd-cea0-49de-bd77-de88e7b6cd1f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


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
open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
theorem _root_.solution : JetSt := by
  intro T B _ _ _ κ _ b hb
  have hmem : ∀ j, b j ∈ Ideal.span (Set.range b) := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hnil : IsNilpotent (Ideal.span (Set.range b)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range b))]
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact mem_nilradical.mpr (hb j)
  obtain ⟨K, hK⟩ := hnil
  refine ⟨K, fun k hk => ?_⟩
  have hJk : Ideal.span (Set.range b) ^ (k + 1) = ⊥ := by
    apply le_bot_iff.mp
    calc Ideal.span (Set.range b) ^ (k + 1) ≤ Ideal.span (Set.range b) ^ K :=
          Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by rw [hK, Ideal.zero_eq_bot]
  refine ⟨jetLift T _ hJk b hmem, fun j => jetLift_zR _ hJk b hmem j, ?_⟩
  intro ψ hψ
  apply jet_ext
  intro j
  rw [hψ j, jetLift_zR]
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
