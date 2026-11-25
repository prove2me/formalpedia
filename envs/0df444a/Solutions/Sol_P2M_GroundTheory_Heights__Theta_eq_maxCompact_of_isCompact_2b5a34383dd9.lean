-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_eq_maxCompact_of_isCompact_2b5a34383dd9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:11.061061+00:00
-- url     : https://prove2.me/submissions/e9f99897-964f-406b-880b-9d5b4724a01e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_eq_one_of_posDef_of_bounded_b6f9a55710a2
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {p q : ℕ}
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "J" => indefJ p q
local notation "G" => indefiniteUnitaryGroup p q
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : maxCompact G ≤ L) : L = maxCompact G := by
  refine le_antisymm (fun g hg => ?_) hK
  set ks := cartanHomeomorph.symm g
  have hg' : g = cartanMul ks := (cartanHomeomorph.apply_symm_apply g).symm
  set s : G := upqOfMatrix ks.2.1 ks.2.2.2
  have hgs : g = (ks.1 : G) * s := hg'
  have hsmat : ((s : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = ks.2.1 := rfl
  have hsL : s ∈ L := by
    have : s = (ks.1 : G)⁻¹ * g := by rw [hgs, inv_mul_cancel_left]
    rw [this]
    exact L.mul_mem (L.inv_mem (hK ks.1.2)) hg

  obtain ⟨C, hC⟩ := (hL.image continuous_coe_indefiniteUnitary).isBounded.exists_norm_le
  have hbd : ∀ x ∈ L, ‖((x : GL (Fin p ⊕ Fin q) ℂ) : 𝔐)‖ ≤ C := fun x hx => hC _ ⟨x, hx, rfl⟩
  have hs1 : ks.2.1 = 1 := by
    refine eq_one_of_posDef_of_bounded ks.2.2.1 (C := C) (fun k => ?_) (fun k => ?_)
    · have := hbd (s ^ k) (L.pow_mem hsL k)
      rwa [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hsmat] at this
    · have := hbd (s⁻¹ ^ k) (L.pow_mem (L.inv_mem hsL) k)
      have hinv : (((s⁻¹ : G) : GL (Fin p ⊕ Fin q) ℂ) : 𝔐) = ks.2.1⁻¹ := by
        rw [Subgroup.coe_inv, Matrix.coe_units_inv, hsmat]
      rwa [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hinv] at this
  have : s = 1 := Subtype.ext (Units.ext hs1)
  rw [hgs, this, mul_one]
  exact ks.1.2
end GroundTheory.Heights₂.Theta
