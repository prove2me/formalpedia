-- Prove2me | solution 1 for SemigroupBetti.IsPairAntichain.snd_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:54.889999+00:00
-- url     : https://prove2.me/submissions/4c4960fc-81a3-44e0-9c4e-0dbb8faf7bcf

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_SharesVar_symm


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}
namespace SemigroupBetti
namespace IsPairAntichain
theorem _root_.solution (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.2 = y.2) : x = y := by
  rcases le_total x.1 y.1 with h1 | h1
  · exact hT x hx y hy h1 h.le
  · exact (hT y hy x hx h1 h.ge).symm
end IsPairAntichain
end SemigroupBetti
