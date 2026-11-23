-- Prove2me | solution 1 for P2M_Formalism_F_covol_eq_covolume__7dd9eea74b94
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:32.320055+00:00
-- url     : https://prove2.me/submissions/16cad95d-d006-481c-8637-e3d8da898090

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume
import Theorems.Thm_Formalism_F_gram_sum_smul_eq_transpose_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule MeasureTheory
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : CovolEqCovolume := by
  intro E _ _ _ _ _ L _ _
  classical
  rw [covol, dif_pos (inferInstance : DiscreteTopology L)]
  set b := Module.finBasis ℤ L with hb
  set bR : Basis (Fin (Module.finrank ℤ L)) ℝ E := b.ofZLatticeBasis ℝ L with hbR
  have hrank : Module.finrank ℝ E = Module.finrank ℤ L := (ZLattice.rank ℝ L).symm
  set o : OrthonormalBasis (Fin (Module.finrank ℤ L)) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hrank)
  set A := o.toBasis.toMatrix bR with hA

  have hgo : Matrix.gram ℝ (fun i => o.toBasis i) = 1 := by
    ext i j
    simp [Matrix.gram, Matrix.one_apply, orthonormal_iff_ite.mp o.orthonormal]
  have hv : (fun i => ((b i : L) : E)) = fun j => ∑ i, A i j • o.toBasis i := by
    funext j
    rw [hA, o.toBasis.sum_toMatrix_smul_self]
    exact (Basis.ofZLatticeBasis_apply ℝ L b j).symm
  have hg : Matrix.gram ℝ (fun i => ((b i : L) : E)) = A.transpose * A := by
    rw [hv, gram_sum_smul_eq_transpose_mul, hgo, Matrix.mul_one]
  have hdet : (Matrix.gram ℝ (fun i => ((b i : L) : E))).det = (o.toBasis.det bR) ^ 2 := by
    rw [hg, Matrix.det_mul, Matrix.det_transpose, Basis.det_apply, sq]

  have h1 : ZLattice.covolume L = (MeasureTheory.volume (ZSpan.fundamentalDomain bR)).toReal := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L MeasureTheory.volume
      (ZLattice.isAddFundamentalDomain b MeasureTheory.volume)]
    rfl
  have h2 := ZSpan.measure_fundamentalDomain bR MeasureTheory.volume o.toBasis
  have h3 : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measure_congr
      (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume),
      OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]
  rw [hdet, Real.sqrt_sq_eq_abs, h1, h2, h3, mul_one, ENNReal.toReal_ofReal (abs_nonneg _)]
end Formalism.F
