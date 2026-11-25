-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.trivS_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:14.085826+00:00
-- url     : https://prove2.me/submissions/0952ff58-9ea2-455e-b62e-f4d60b25d3db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_le_one_of_pow_le
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_pow_mem
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_modPow
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_modEqOne
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isCompact_inter_unit_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (hSG : SsetGroup) (hUW : UWCompact) (hN : NGroup) (hNC : NContract) : TrivS := by
  unfold TrivS
  intro k r z hz hT D hD
  have hG := hSG k r z hz hT
  obtain ⟨hN1, hNmul, hNinv⟩ := hN k r
  have h1S : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r z := hG.2.1
  obtain ⟨h0, hh0, m0, hm0, he0⟩ := h1S
  have hNS : ∀ n ∈ Nset k r, n ∈ Sset k r z := by
    intro n hn
    refine ⟨h0, hh0, m0 * n, hNmul _ hm0 _ hn, ?_⟩
    rw [← mul_assoc, ← he0, one_mul]
  have hUS : ∀ h ∈ UWset k r z, h ∈ Sset k r z := by
    intro h hh
    exact ⟨h, hh, 1, hN1, (mul_one h).symm⟩
  have hpowN : ∀ n ∈ Nset k r, ∀ j : ℕ, n ^ j ∈ Nset k r := by
    intro n hn j
    induction j with
    | zero =>
      rw [pow_zero]
      exact hN1
    | succ j ih =>
      rw [pow_succ]
      exact hNmul _ ih _ hn
  obtain ⟨M, hM⟩ := hD.2.2.2 _ Set.inter_subset_left (isCompact_inter_unit_box hG.1)
  have hNle : ∀ n ∈ Nset k r, D n ≤ 1 := by
    intro n hn
    apply le_one_of_pow_le (M := M)
    intro j
    have hnj := hpowN n hn j
    obtain ⟨c, hcu, hcS, hcb⟩ := hNC k r z hz (n ^ j) hnj 1 one_pos
    have hnjS := hNS _ hnj
    rw [← modPow hG hD (hNS n hn) j, ← hD.2.2.1 c hcu hcS _ hnjS]
    apply hM
    exact ⟨(hcS _).mpr hnjS, fun i' j' => hcb i' j'⟩
  obtain ⟨M', hM'⟩ := hD.2.2.2 _ (fun h hh => hUS h hh) (hUW k r z hz hT)
  have hSle : ∀ g ∈ Sset k r z, D g ≤ M' := by
    intro g hg
    obtain ⟨h, hh, m, hm, rfl⟩ := hg
    rw [hD.2.1 h (hUS h hh) m (hNS m hm)]
    have h1 := hNle m hm
    have h2 := hD.1 h (hUS h hh)
    have h3 := hM' h hh
    calc D h * D m ≤ D h * 1 := mul_le_mul_of_nonneg_left h1 h2.le
      _ ≤ M' := by
        rw [mul_one]
        exact h3
  have hle1 : ∀ g ∈ Sset k r z, D g ≤ 1 := by
    intro g hg
    apply le_one_of_pow_le (M := M')
    intro j
    rw [← modPow hG hD hg j]
    exact hSle _ (pow_mem hG hg j)
  intro g hg
  exact modEqOne hG hD hg (hle1 g hg) (hle1 _ (hG.2.2.2 g hg).1)
end PI.QuotSetU.UnitaryGroupMassFormula.SW
