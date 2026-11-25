-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_no_chain_two_1b7260404b30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:49.344668+00:00
-- url     : https://prove2.me/submissions/e2c28289-611a-4363-b88a-b5018ec79e97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveProperClosedFinite

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace CurveProperClosedFinite
theorem _root_.solution {R : Type*} [CommRing R] {W P Q : Ideal R}
    (hW : W.IsPrime) (hP : P.IsPrime) (hQ : Q.IsPrime) (hdim : ringKrullDim (R ⧸ W) = 1)
    (hWP : W < P) (hPQ : P < Q) : False := by
  let a : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨W, hW⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl⟩
  let b : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨P, hP⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 hWP.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨Q, hQ⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (hWP.trans hPQ).le⟩
  have hab : a < b := hWP
  have hbc : b < c := hPQ
  let p0 : LTSeries (PrimeSpectrum.zeroLocus (R := R) (W : Set R)) := RelSeries.singleton _ a
  have h2 := Order.LTSeries.length_le_krullDim ((p0.snoc b hab).snoc c hbc)
  rw [← ringKrullDim_quotient, hdim] at h2
  have hl : ((p0.snoc b hab).snoc c hbc).length = 2 := by
    rfl
  rw [hl] at h2
  norm_num at h2
end CurveProperClosedFinite
end GroundTheory.Heights₂.Heights
