-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eig_actD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:34.450729+00:00
-- url     : https://prove2.me/submissions/cfd7a68a-f85b-401c-b4d1-71eaca7f2ea2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {O k : Type} [CommRing O] [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (h : IsEqv χ b c) (a : O) : M a * actD M b c = χ a • actD M b c := by
  obtain ⟨m, hm1, hm2⟩ := h a
  unfold actD
  rw [Finset.mul_sum, Finset.smul_sum]
  calc ∑ i, M a * (c i • M (b i)) = ∑ i, c i • M (a * b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, Matrix.mul_smul]
    _ = ∑ i, c i • ∑ j, ((m i j : ℤ) : k) • M (b j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm1 i, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
    _ = ∑ j, (∑ i, ((m i j : ℤ) : k) * c i) • M (b j) := by
        simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]
    _ = ∑ j, χ a • (c j • M (b j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hm2 j, smul_smul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
