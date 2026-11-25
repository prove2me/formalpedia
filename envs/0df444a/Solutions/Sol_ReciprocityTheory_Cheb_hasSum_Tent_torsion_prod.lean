-- Prove2me | solution 1 for ReciprocityTheory.Cheb.hasSum_Tent_torsion_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:35.610225+00:00
-- url     : https://prove2.me/submissions/8991043d-ac1d-4340-844d-574339e3b283

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Theorems.Thm_ReciprocityTheory_Cheb_hasSum_snd_of_fintype
import Theorems.Thm_ReciprocityTheory_Cheb_Tent_nonneg__b8ca4a
import Theorems.Thm_ReciprocityTheory_Cheb_hasSum_Tent_add_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (y : Fin (rank E) → ℝ) :
    HasSum (fun p : torsion E × (Fin (rank E) → ℤ) => Tent (fun i => y i + p.2 i))
      (torsionOrder E : ℝ) := by
  have : Fintype (torsion E) := Fintype.ofFinite _
  have h2 : HasSum (fun n : Fin (rank E) → ℤ => Tent (fun i => y i + n i)) 1 := hasSum_Tent_add_int y
  have h := hasSum_snd_of_fintype (α := torsion E)
    (g := fun n : Fin (rank E) → ℤ => Tent (fun i => y i + n i)) (fun n => Tent_nonneg _) h2
  rwa [mul_one, ← Nat.card_eq_fintype_card] at h
end ReciprocityTheory.Cheb
