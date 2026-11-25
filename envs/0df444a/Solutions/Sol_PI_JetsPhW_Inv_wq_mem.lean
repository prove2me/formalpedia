-- Prove2me | solution 1 for PI.JetsPhW.Inv.wq_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:42.974301+00:00
-- url     : https://prove2.me/submissions/d8225ca4-5648-4de6-8f20-7d2ce09123ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Theorems.Thm_PI_JetsPhW_Inv_coeff_pow_memS
import Theorems.Thm_PI_JetsPhW_Inv_coeff_termS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.JetsPhW PI.JetsPhW.Inv
variable {p : ℕ} [Fact p.Prime]
namespace PI.JetsPhW.Inv
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  simp only [IsWq] at h
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X ^ 1 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := by
    rw [pow_one]; exact h
  have key : ∀ n, (∀ i < n, PowerSeries.coeff i wq ∈ S) → PowerSeries.coeff n wq ∈ S := by
    intro n ih
    rw [h']
    simp only [map_add, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn => exact key n ihn
end PI.JetsPhW.Inv
