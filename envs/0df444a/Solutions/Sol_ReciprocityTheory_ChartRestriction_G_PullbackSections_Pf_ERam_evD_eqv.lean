-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.evD_eqv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:57.859958+00:00
-- url     : https://prove2.me/submissions/eaa10376-ffaa-4848-8a33-1a47a2c07899

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
theorem _root_.solution (χ χ' : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (h : IsEqv χ b c) (a : O) :
    χ' a * evD χ' b c = χ a * evD χ' b c := by
  obtain ⟨m, hm1, hm2⟩ := h a
  unfold evD
  rw [Finset.mul_sum, Finset.mul_sum]
  calc ∑ i, χ' a * (c i * χ' (b i)) = ∑ i, c i * χ' (a * b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
    _ = ∑ i, c i * ∑ j, ((m i j : ℤ) : k) * χ' (b j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hm1 i, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, zsmul_eq_mul]
    _ = ∑ j, (∑ i, ((m i j : ℤ) : k) * c i) * χ' (b j) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ j, χ a * (c j * χ' (b j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hm2 j]
        ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
