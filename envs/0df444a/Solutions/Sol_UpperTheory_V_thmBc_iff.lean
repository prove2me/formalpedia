-- Prove2me | solution 1 for UpperTheory.V.thmBc_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:06.881838+00:00
-- url     : https://prove2.me/submissions/a441e7a9-dd3b-4da0-843c-ef2c442648b4

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
theorem _root_.solution {Ct : ℝ} (hC : 1 ≤ Ct) : ThmBc Ct ↔ ThmBcFree := by
  classical
  constructor
  · rintro ⟨C, H⟩
    refine ⟨C, fun M e t q d he ht hp E _ _ _ hE => ?_⟩
    set x : ℝ := max ((2 : ℝ) ^ e) t with hx
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hx2 : (2 : ℝ) ≤ x := ht2.trans (le_max_right _ _)
    have hA : admitted 2 Ct (fun y => if y = x then e else 2) (fun y => if y = x then t else 2) := by
      intro y hy
      have h1 : y ≤ y ^ Ct := Real.self_le_rpow_of_one_le (by linarith) hC
      have h2 : y ≤ y ^ (2 : ℝ) := Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
      by_cases hyx : y = x
      · simp only [if_pos hyx]
        exact ⟨he, le_trans (hyx ▸ le_max_left _ _) h2, ht, le_trans (hyx ▸ le_max_right _ _) h1⟩
      · simp only [if_neg hyx]
        refine ⟨le_rfl, ?_, le_rfl, by push_cast; linarith⟩
        rw [Real.rpow_two]
        gcongr
    have := H M 2 _ _ hA x hx2 q d hp E (by simpa only [if_true] using hE)
    simpa only [if_true] using this
  · rintro ⟨C, H⟩
    exact ⟨C, fun M A1 e t ha x hx q d hp E _ _ _ hE => H M _ _ q d (ha x hx).1 (ha x hx).2.2.1 hp E hE⟩
end UpperTheory.V
