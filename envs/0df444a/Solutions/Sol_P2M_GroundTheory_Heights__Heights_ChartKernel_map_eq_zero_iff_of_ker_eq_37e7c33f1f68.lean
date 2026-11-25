-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_map_eq_zero_iff_of_ker_eq_37e7c33f1f68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:52:06.131956+00:00
-- url     : https://prove2.me/submissions/083b495d-c69d-4016-99c1-338947c67736

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {A B B' σ : Type*} [CommRing A] [CommRing B] [CommRing B']
    {f : A →+* B} {f' : A →+* B'} (h : RingHom.ker f = RingHom.ker f') (x : MvPolynomial σ A) :
    map f x = 0 ↔ map f' x = 0 := by
  simp only [MvPolynomial.ext_iff, coeff_map, coeff_zero]
  exact forall_congr' fun s => by rw [← RingHom.mem_ker, ← RingHom.mem_ker, h]
end GroundTheory.Heights₂.Heights.ChartKernel
