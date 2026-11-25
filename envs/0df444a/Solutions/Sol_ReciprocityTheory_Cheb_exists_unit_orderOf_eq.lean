-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_unit_orderOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:49.474273+00:00
-- url     : https://prove2.me/submissions/745c14f4-32dd-4531-a70f-b9628e2fe1e4

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossGal
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossLift
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFrobE
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossRes
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Definitions.Def_ReciprocityTheory_Chebotarev_ExistsUnitOrderOfEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (l : ℕ) [Fact l.Prime] : ∃ τ : (ZMod l)ˣ, orderOf τ = l - 1 := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  refine ⟨τ, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]
end ReciprocityTheory.Cheb
