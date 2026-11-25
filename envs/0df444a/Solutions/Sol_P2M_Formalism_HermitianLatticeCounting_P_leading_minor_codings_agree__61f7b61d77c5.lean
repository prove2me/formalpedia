-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_leading_minor_codings_agree__61f7b61d77c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:44.615738+00:00
-- url     : https://prove2.me/submissions/ddc356ff-5a39-4fa8-8c2e-deffb8a633f0

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LeadingMinorCodingsAgree := by
  intro R _ d Z l h
  unfold leadingPrincipalMinor LeadingPrincipalMinor
  rw [← Matrix.det_submatrix_equiv_self (Fin.castLEOrderIso h).toEquiv]
  rfl
end Formalism.HermitianLatticeCounting.P
