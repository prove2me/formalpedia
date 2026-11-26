-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_2_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:40.382161+00:00
-- url     : https://prove2.me/submissions/723edad4-439d-4499-bceb-143a72ec6eca

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_1
import Theorems.Thm_Scott1976_DataTypesAsLattices_beta


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  beta (theorem_2_1 body ρ i) y
end Scott1976.DataTypesAsLattices
