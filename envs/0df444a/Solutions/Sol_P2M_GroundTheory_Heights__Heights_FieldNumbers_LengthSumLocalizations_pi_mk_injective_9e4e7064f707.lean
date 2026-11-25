-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_pi_mk_injective_9e4e7064f707
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:34.977059+00:00
-- url     : https://prove2.me/submissions/12d076d7-3e8a-433b-bf7d-4003ff383f50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Module TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
variable {B : Type*} [CommRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal B) [h𝔪 : ∀ i, (𝔪 i).IsMaximal]
  (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsLocalization.AtPrime (C i) (𝔪 i)]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
theorem _root_.solution (hall : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (N : Type*)
    [AddCommGroup N] [Module B N] :
    Function.Injective (LinearMap.pi fun i => TensorProduct.mk B (C i) N 1) := by
  rw [injective_iff_map_eq_zero]
  intro n hn
  by_contra hne
  have hlt : LinearMap.ker (LinearMap.toSpanSingleton B N n) ≠ ⊤ := by
    intro htop
    apply hne
    have h1 : (1 : B) ∈ LinearMap.ker (LinearMap.toSpanSingleton B N n) := htop ▸ Submodule.mem_top
    simpa using h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hlt
  obtain ⟨i, rfl⟩ := hall M hM
  have : IsLocalizedModule (𝔪 i).primeCompl (TensorProduct.mk B (C i) N 1) :=
    (isLocalizedModule_iff_isBaseChange (𝔪 i).primeCompl (C i) _).mpr
      (TensorProduct.isBaseChange B N (C i))
  have h0 : TensorProduct.mk B (C i) N 1 n = 0 := by
    simpa using congrFun hn i
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (𝔪 i).primeCompl _).mp h0
  exact s.2 (hle (by rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hs))
end GroundTheory.Heights₂.Heights.FieldNumbers.LengthSumLocalizations
