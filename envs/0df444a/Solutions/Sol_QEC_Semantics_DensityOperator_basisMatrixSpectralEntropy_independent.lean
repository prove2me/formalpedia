-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.basisMatrixSpectralEntropy_independent
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:53:29.337783+00:00
-- url     : https://prove2.me/submissions/d49057b0-4196-4ef5-8469-f727b3737eaf

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem solution (rho : DensityOperator H)
    (b c : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum =
      (((rho.toOperator.toMatrix c.toBasis c.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by
  solve | rfl | simp [DensityOperator, map, entropyTerm] | simp_all [DensityOperator, map, entropyTerm] | omega | norm_num
