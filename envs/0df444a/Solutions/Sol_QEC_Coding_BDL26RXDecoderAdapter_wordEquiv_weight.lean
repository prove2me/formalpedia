-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.wordEquiv_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:07:40.073879+00:00
-- url     : https://prove2.me/submissions/4264cc10-d477-4e79-86ca-3bdfbce54bae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (w : Word BDL26Field A) : HammingWeight (wordEquiv e w) = HammingWeight w := by
  unfold HammingWeight
  apply Finset.card_equiv e.symm
  intro b
  constructor
  · intro hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  · intro hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
end QEC.Coding.BDL26RXDecoderAdapter
