-- Prove2me | solution 1 for SyncPrefix.Huffman.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:20:21.407765+00:00
-- url     : https://prove2.me/submissions/d25833ce-0656-41ca-a47d-12f50990b225

import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_SyncPrefix_Huffman_huffmanOfStronglyAcyclic_spec
import Theorems.Thm_SyncPrefix_Huffman_huffmanOfStronglyAcyclic_encode_polyTime

open SyncPrefix.Huffman

theorem solution :
    ∃ f : List (Option Bool) → List (Option Bool), CookPvsNP.PolyTimeComputable f ∧
      ∀ A : Automaton, StronglyAcyclic A.δ → IsSynchronizing A.δ →
        ∃ AH : Automaton, f A.encode = AH.encode ∧ IsHuffmanDecoder AH.δ ∧ AH.k = A.k + 2 ∧
          IsSynchronizing AH.δ ∧ syncLength AH.δ = syncLength A.δ ∧
            A.n ≤ AH.n ∧ AH.n ≤ 2 * A.n := by
  obtain ⟨f, hf, hf_spec⟩ := huffmanOfStronglyAcyclic_encode_polyTime
  refine ⟨f, hf, fun A hSA hSync => ?_⟩
  obtain ⟨hHuff, hSyncH, hLenH⟩ := huffmanOfStronglyAcyclic_spec A hSA hSync
  refine ⟨huffmanOfStronglyAcyclic A, hf_spec A hSA hSync, hHuff, ?_, hSyncH, hLenH, ?_, ?_⟩
  · exact huffmanOfStronglyAcyclic_k A
  · exact le_huffmanOfStronglyAcyclic_n A
  · exact huffmanOfStronglyAcyclic_n_le A
