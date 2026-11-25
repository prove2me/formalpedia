-- Prove2me | solution 1 for UpperTheory.V.AbF.hasMu_cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:57.914639+00:00
-- url     : https://prove2.me/submissions/71affa74-3559-4654-84ab-7d64fd3642a9

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
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
open NumberField Polynomial
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
namespace AbF
theorem _root_.solution {l q : ℕ} (hl : 0 < l) (hq : 0 < q) : (AbF.cyc (l * q)).HasMu l := by
  have hm : max (l * q) 1 = l * q :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hl hq).ne')
  show (l ∣ max (l * q) 1) ∧ ∀ a : ℕ,
    (∃ u ∈ (⊥ : Subgroup (ZMod (max (l * q) 1))ˣ),
      ((u : (ZMod (max (l * q) 1))ˣ) : ZMod (max (l * q) 1)) = (a : ZMod (max (l * q) 1))) →
      a ≡ 1 [MOD l]
  refine ⟨?_, ?_⟩
  · rw [hm]
    exact dvd_mul_right l q
  · rintro a ⟨u, hu, hua⟩
    rw [Subgroup.mem_bot] at hu
    subst hu
    have h1 : ((a : ℕ) : ZMod (max (l * q) 1)) = ((1 : ℕ) : ZMod (max (l * q) 1)) := by
      simpa using hua.symm
    rw [ZMod.natCast_eq_natCast_iff, hm] at h1
    exact Nat.ModEq.of_mul_right q h1
end AbF
end UpperTheory.V
