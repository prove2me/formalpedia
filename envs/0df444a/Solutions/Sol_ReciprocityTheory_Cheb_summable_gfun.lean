-- Prove2me | solution 1 for ReciprocityTheory.Cheb.summable_gfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:38:47.701717+00:00
-- url     : https://prove2.me/submissions/7943b96f-78ea-4521-9d5d-f14d1324923c

import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Theorems.Thm_ReciprocityTheory_Cheb_affine_proper_base_change


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.Units Filter Topology Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) : Summable (gfun χ c s) := by
  have h1 := affine_proper_base_change.1 E (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l))
    (fun a => DirichletCharacter.norm_le_one χ _) s hs
  have h2 := affine_proper_base_change.1 E (fun a => if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0)
    (fun a => by split_ifs <;> simp [DirichletCharacter.norm_le_one]) s hs
  refine (h1.sub (h2.mul_left (Ideal.absNorm c.1 : ℂ))).congr fun a => ?_
  simp only [gfun]
  split_ifs <;> ring
end ReciprocityTheory.Cheb
