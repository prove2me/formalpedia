-- Prove2me | solution 1 for PI.CompDegEF.mem_span_l_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:06.478263+00:00
-- url     : https://prove2.me/submissions/2ca63590-b707-4115-86b0-3f5a227d455e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemSpanLIff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
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
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) (y : ↥(ball K)) :
    y ∈ Ideal.span {((l : ℕ) : ↥(ball K))} ↔
      ‖((y : ↥K.1) : Om l)‖ ≤ ‖((l : ℕ) : Om l)‖ := by
  have hl0' : ((l : ℕ) : Om l) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  have hl0 : ((l : ℕ) : ↥K.1) ≠ 0 := by
    intro h
    apply hl0'
    have h' : (((l : ℕ) : ↥K.1) : Om l) = 0 := by rw [h]; rfl
    simpa using h'
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖((z : ↥K.1) : Om l)‖ ≤ 1 := z.2
    have hc : (((z * ((l : ℕ) : ↥(ball K)) : ↥(ball K)) : ↥K.1) : Om l) =
        ((z : ↥K.1) : Om l) * ((l : ℕ) : Om l) := by simp
    rw [hc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hz
  · intro h
    have hmem : ‖(((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
      have hc : (((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l) =
          ((y : ↥K.1) : Om l) / ((l : ℕ) : Om l) := by simp
      rw [hc, norm_div, div_le_one (norm_pos_iff.mpr hl0')]
      exact h
    refine ⟨⟨(y : ↥K.1) / ((l : ℕ) : ↥K.1), hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    push_cast
    exact div_mul_cancel₀ _ hl0
end PI.CompDegEF
