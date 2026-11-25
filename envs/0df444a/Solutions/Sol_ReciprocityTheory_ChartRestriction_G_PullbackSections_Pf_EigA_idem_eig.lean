-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.idem_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:21.338562+00:00
-- url     : https://prove2.me/submissions/1348f16b-a24e-494d-ab72-e513066f0905

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution {d : ℕ} {O k : Type} [CommRing O] [CommRing k] (M : O →+* Matrix (Fin d) (Fin d) k) (χ : O →+* k)
    {n : ℕ} (b : Fin n → O) (c : Fin n → k) (a : O) (m : Fin n → Fin n → ℤ)
    (hb : ∀ i, a * b i = ∑ j, m i j • b j) (hc : ∀ j, ∑ i, (m i j : k) * c i = χ a * c j) :
    M a * ∑ i, c i • M (b i) = χ a • ∑ i, c i • M (b i) := by
  have h1 : ∀ i, M a * (c i • M (b i)) = ∑ j, (c i * (m i j : k)) • M (b j) := by
    intro i
    rw [Matrix.mul_smul, ← map_mul, hb i, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul k, smul_smul]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, smul_smul, ← hc j]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
