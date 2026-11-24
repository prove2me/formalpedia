-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_combD_apply_6bfad6589386
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:47.425749+00:00
-- url     : https://prove2.me/submissions/b835466e-5e2f-4648-aa49-9dbf7ef18328

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
theorem _root_.solution (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i)) then
        (KH.faceSign I.1.1 k i : ℤ) • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  simp only [combD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : FaceOK J n (Function.update I.1.1 k ((I.1.1 k).erase i))
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl
end GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic
