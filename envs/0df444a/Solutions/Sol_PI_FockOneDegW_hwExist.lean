-- Prove2me | solution 1 for PI.FockOneDegW.hwExist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:24.770075+00:00
-- url     : https://prove2.me/submissions/e175661c-973d-4bd3-8ae8-bf4474ee589d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists
import Theorems.Thm_PI_FockOneDegW_HwC_exists_wtvec
import Theorems.Thm_PI_FockOneDegW_HwC_exists_cover
import Theorems.Thm_PI_FockOneDegW_HwC_fw_shift
import Theorems.Thm_PI_FockOneDegW_HwC_posC_facts
import Theorems.Thm_PI_FockOneDegW_HwC_Ecc_of_wt
import Theorems.Thm_PI_FockOneDegW_HwC_wt_Eab_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW
open HwC
open Classical
namespace PI.FockOneDegW
theorem _root_.solution : HwExist := by
  intro p q r s U hfd hU0 hstab
  haveI := hfd
  obtain ⟨S, hS⟩ := exists_cover U
  have hdiag : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U :=
    fun c => hstab c c (by cases c <;> trivial)

  have hwtS : ∀ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U → v ≠ 0 → IsWt ν v → ν ∈ S.image wtv := by
    intro ν v hv hv0 hw
    obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hv0 (MvPolynomial.support_eq_empty.1 h))
    exact Finset.mem_image.2 ⟨β, hS v hv hβ, funext fun c => hw β hβ c⟩
  have hT : ((S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v)).Nonempty := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨ν, v, hv, hv0, hvw, -⟩ := exists_wtvec U hdiag _ u hu hu0 le_rfl
    exact ⟨ν, Finset.mem_filter.2 ⟨hwtS ν v hv hv0 hvw, v, hv, hv0, hvw⟩⟩

  obtain ⟨ν₀, hν₀, hmax⟩ := Finset.exists_max_image _ fw hT
  obtain ⟨-, v, hv, hv0, hvw⟩ := Finset.mem_filter.1 hν₀
  refine ⟨ν₀, v, hv, ?_⟩
  unfold IsHW hwSub
  refine ⟨hv0, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    intro a
    rw [Ecc_of_wt hvw a, sub_self]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    obtain ⟨hsame, hne, htw⟩ := posC_facts hab
    by_contra hw0
    have hwU := hstab a b hsame v hv
    have hw' := wt_Eab_of hvw a b hsame hne
    have hmemT : (fun c => ν₀ c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) ∈
        (S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v) :=
      Finset.mem_filter.2 ⟨hwtS _ _ hwU hw0 hw', _, hwU, hw0, hw'⟩
    have h1 := hmax _ hmemT
    rw [fw_shift] at h1
    linarith
end PI.FockOneDegW
