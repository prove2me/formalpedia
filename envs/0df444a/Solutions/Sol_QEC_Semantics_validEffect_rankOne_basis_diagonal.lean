-- Prove2me | solution 1 for QEC.Semantics.validEffect_rankOne_basis_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:28:55.41712+00:00
-- url     : https://prove2.me/submissions/652e7519-1eeb-4f9e-889f-871cac373b26

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_validEffect_rankOne_of_norm_one

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace QEC.Semantics
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H) (i : κ) :
    ValidEffect (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap :=
  validEffect_rankOne_of_norm_one (b.orthonormal.norm_eq_one i)
end QEC.Semantics
