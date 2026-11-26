-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:02.60565+00:00
-- url     : https://prove2.me/submissions/ac47d572-abfe-4ded-a1ad-b8e60a2ab8de

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_interp_var_isScottContinuous

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) :=
  interp_var_isScottContinuous t ρ i
end Scott1976.DataTypesAsLattices
