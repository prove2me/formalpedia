-- Prove2me | solution 1 for ReciprocityTheory.Cheb.unit_smul_embZ
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:15:27.779799+00:00
-- url     : https://prove2.me/submissions/ad149968-970b-45a7-b19c-1fb126f7cb7c

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem solution (u : (𝓞 E)ˣ) (α : 𝓞 E) : u • embZ α = embZ ((u : 𝓞 E) * α) := by
  simpa [embZ] using (unit_smul_eq_iff_mul_eq (K := E) (x := α) (y := (u : 𝓞 E) * α) (u := u)).mpr rfl
