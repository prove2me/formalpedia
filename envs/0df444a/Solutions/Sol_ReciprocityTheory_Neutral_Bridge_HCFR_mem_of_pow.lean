-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.mem_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:47.851546+00:00
-- url     : https://prove2.me/submissions/d5a7cd46-c036-4867-9477-c8c61982d5bd

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_self
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_ne
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_inf_comp_ne_zero
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m) (hpow : ∀ x : Ideles K, x ^ m ∈ N)
    (hneg : ∀ w : InfinitePlace K, w.IsReal → infIdele K w (-1) ∈ N)
    (a : Ideles K) (ha : (a : AdeleRing (𝓞 K) K).2 = 1) : a ∈ N := by
  classical
  let x : ∀ w : InfinitePlace K, (w.Completion)ˣ :=
    fun w => Units.mk0 ((a : AdeleRing (𝓞 K) K).1 w) (inf_comp_ne_zero K a w)
  have hext : ∀ b c : Ideles K, fstU K b = fstU K c → sndU K b = sndU K c → b = c :=
    fun b c h1 h2 => Units.ext (Prod.ext h1 h2)
  have ha' : a = ∏ w, infIdele K w (x w) := by
    apply hext
    · rw [map_prod]
      funext w'
      have hpa : (∏ i, (fstU K (infIdele K i (x i)) : (v : InfinitePlace K) → v.Completion)) w' =
          ∏ i, (fstU K (infIdele K i (x i)) : (v : InfinitePlace K) → v.Completion) w' :=
        Finset.prod_apply _ _ _
      refine Eq.trans ?_ hpa.symm
      rw [Finset.prod_eq_single w']
      · exact (infIdele_fst_self K w' (x w')).symm
      · intro w _ hw
        exact infIdele_fst_ne K w w' (Ne.symm hw) (x w)
      · intro hw'
        exact absurd (Finset.mem_univ _) hw'
    · rw [map_prod]
      show (a : AdeleRing (𝓞 K) K).2 = ∏ w, sndU K (infIdele K w (x w))
      rw [ha]
      exact (Finset.prod_eq_one fun w _ => rfl).symm
  rw [ha']
  exact Subgroup.prod_mem _ fun w _ => infIdele_mem K N m hm hpow hneg w (x w)
end ReciprocityTheory.Neutral.Bridge.HCFR
