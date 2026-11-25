-- Prove2me | solution 1 for P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_conj__aca6ea8d7fad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:17.159182+00:00
-- url     : https://prove2.me/submissions/afdcf9d4-4a15-4a2d-b64f-1ffb0a84e039

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (hi : Irreducible f) {x y : L} (hx : aeval x f = 0)
    (hy : aeval y f = 0) : ∃ n : ℕ, y = x ^ Fintype.card K ^ n := by
  have hf0 : f ≠ 0 := hi.ne_zero
  have hu : IsUnit (C f.leadingCoeff⁻¹ : K[X]) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hf0)))
  have hm : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf0
  have hi' : Irreducible (f * C f.leadingCoeff⁻¹) := (irreducible_mul_isUnit hu).mpr hi
  have hx' : aeval x (f * C f.leadingCoeff⁻¹) = 0 := by rw [map_mul, hx, zero_mul]
  have hy' : aeval y (f * C f.leadingCoeff⁻¹) = 0 := by rw [map_mul, hy, zero_mul]
  exact root_conj hm hi' hx' hy'
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
