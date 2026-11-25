-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cosetCoordinates_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:48:36.143729+00:00
-- url     : https://prove2.me/submissions/d8ba3f20-927f-44e9-bde2-5f1f704c846e

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_L2_coset_functional_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_algebraMap_eq_inv_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {f : N → C} (hf : f ∈ AA.carrier) (l : K) :
    (fun x => h3co K β f x l) ∈ AA.carrier := by
  exact coset_functional_mem AA K ((LinearMap.proj l).comp (Matrix.mulVecLin β⁻¹))
    (fun h hh => exists_algebraMap_eq_inv_mulVec AA K β hβ hAK hh l) hf
end ReciprocityTheory.PGsh.L2
