-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_covolume_eq_sqrt_det_gram_f70fe7996734
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:32.378783+00:00
-- url     : https://prove2.me/submissions/e7a187b8-fcf4-41e9-91f3-eb214693e270

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Matrix Module
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (gram ℝ fun i ↦ (b i : V)).det := by
  have hcard : Fintype.card ι = finrank ℝ V := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hcard).symm
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one,
    mul_one, gram_eq_conjTranspose_mul o, det_mul, det_conjTranspose, star_trivial,
    ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]
  congr 2
end GroundTheory.Heights₂.Heights
