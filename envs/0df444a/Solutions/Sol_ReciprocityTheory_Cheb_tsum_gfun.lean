-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tsum_gfun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:53.514788+00:00
-- url     : https://prove2.me/submissions/77923d5d-67d4-42c8-9ca5-df5b21194665

import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Definitions.Def_ReciprocityTheory_Chebotarev_CTrick
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Theorems.Thm_ReciprocityTheory_Cheb_affine_proper_base_change
import Theorems.Thm_ReciprocityTheory_Cheb_tsum_dvd_eq


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
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a, gfun χ c s a = Lser E χ s * (1 - (Ideal.absNorm c.1 : ℂ) *
      (χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)))) := by
  have h1 := affine_proper_base_change.1 E (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l))
    (fun a => DirichletCharacter.norm_le_one χ _) s hs
  have h2 := affine_proper_base_change.1 E (fun a => if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0)
    (fun a => by split_ifs <;> simp [DirichletCharacter.norm_le_one]) s hs
  have hd := tsum_dvd_eq χ c hs
  have e : (fun a => gfun χ c s a) = fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
      ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) - (Ideal.absNorm c.1 : ℂ) *
      ((if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0) *
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) := by
    funext a; simp only [gfun]; split_ifs <;> ring
  have e2 : (fun a : NZIdeal E => (if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0) *
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) = fun a => if c.1 ∣ a.1 then
        χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) else 0 := by
    funext a; split_ifs <;> simp
  rw [e, h1.tsum_sub (h2.mul_left _), tsum_mul_left, e2, hd]
  simp only [Lser]
  ring
end ReciprocityTheory.Cheb
