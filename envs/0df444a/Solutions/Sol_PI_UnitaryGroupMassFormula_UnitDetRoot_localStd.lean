-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.localStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:52.433664+00:00
-- url     : https://prove2.me/submissions/d9855d48-2a2c-4296-8ff4-95eebe61b49b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_stdLat_le_dual
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_nsmul_relIdx_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_altE_natsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_mem_imgLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : LocalStd := by
  intro a b c d ha hd lam hlam m _ _ Λa hH l _ δ hA hl
  obtain ⟨hok, hsd, hth, hi1, hi2⟩ := hH
  obtain ⟨hiso, hc1, hc2⟩ := hA
  set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt
  set H := UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hHdef
  set M := UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hM
  set k := UnitDetRootDefs.relIdx Lt M with hk
  have partA : ∀ x ∈ M, (k : ℂ) • x ∈ Lt := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_relIdx_mem Lt M hx
  have hdualM : ∀ z, z ∈ UnitDetRootDefs.dualLat H M → z ∈ M := by
    intro z hz
    rw [hM, mem_imgLat]
    rw [UnitDetRootDefs.IsSelfDual] at hsd
    rw [← hsd]
    intro y hy
    have hδy : δ y ∈ M := by rw [hM, mem_imgLat]; simpa using hy
    obtain ⟨n, hn⟩ := hz (δ y) hδy
    refine ⟨n, ?_⟩
    rw [← hn, UnitDetRootDefs.altE, UnitDetRootDefs.altE, ← hiso (δ.symm z) y]
    simp
  refine ⟨k, hl, fun x hx => hdualM _ ?_, partA⟩
  intro y hy
  rw [altE_natsmul]
  exact stdLat_le_dual hx _ (partA y hy)
end PI.UnitaryGroupMassFormula.UnitDetRoot
