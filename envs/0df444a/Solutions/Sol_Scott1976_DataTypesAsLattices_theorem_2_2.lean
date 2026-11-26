-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:07.846269+00:00
-- url     : https://prove2.me/submissions/d2d61bf3-f9b1-40ae-af30-ad1a125f17d8

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_2_beta

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  theorem_2_2_beta i body ρ y
end Scott1976.DataTypesAsLattices
