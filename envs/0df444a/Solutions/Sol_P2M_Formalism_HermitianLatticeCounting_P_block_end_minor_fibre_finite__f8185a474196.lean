-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_block_end_minor_fibre_finite__f8185a474196
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:38.843249+00:00
-- url     : https://prove2.me/submissions/4be9bf03-2d3a-44a8-ac00-99c636150e26

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_eq_of_signed_minors_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockEndMinorFibreFinite := by
  classical
  intro F _ p s d T hs hT
  rcases T.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩
  · simp
  have hsub : T ⊆ Fintype.piFinset (fun a => (Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset) := by
    intro t ht
    rw [Fintype.mem_piFinset]
    intro a
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (hs a)]
    exact pow_eq_of_signed_minors_eq s t t0 (hT t0 ht0).1 (fun a => ((hT t ht).2 a).trans ((hT t0 ht0).2 a).symm) a
  calc T.card ≤ (Fintype.piFinset (fun a => (Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset)).card :=
        Finset.card_le_card hsub
    _ = ∏ a, ((Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset).card := Fintype.card_piFinset _
    _ ≤ ∏ a, s a := Finset.prod_le_prod' fun a _ =>
        (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
end Formalism.HermitianLatticeCounting.P
