-- Prove2me | solution 1 for SemigroupBetti.GenData.card_pairsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:19:02.160732+00:00
-- url     : https://prove2.me/submissions/d66465b4-9fae-4ec2-b233-2cd1a0dbb773

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_pairsOf_injOn

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : (G.pairsOf F K i k).card = F.card :=
  card_image_of_injOn (G.pairsOf_injOn hik hKe hF)
end SemigroupBetti.GenData
