-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_forall_cyclotomic_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:32.265827+00:00
-- url     : https://prove2.me/submissions/e0f4eec8-e9db-4531-861a-7a3d731ded35

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Theorems.Thm_ReciprocityTheory_Cheb_exists_forall_isUnramifiedAt
import Theorems.Thm_ReciprocityTheory_Cheb_cyclotomic_irreducible_of_forall_isUnramifiedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Polynomial NumberField
namespace ReciprocityTheory.Cheb
theorem _root_.solution (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ l : ℕ, l.Prime → N < l → Irreducible (cyclotomic l K) := by
  obtain ⟨N, hN⟩ := exists_forall_isUnramifiedAt K
  exact ⟨N, fun l hl hlN => cyclotomic_irreducible_of_forall_isUnramifiedAt hl
    (fun P _ hP => hN l hl hlN P hP)⟩
end ReciprocityTheory.Cheb
