-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SDiffGram.block_simeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:07.659906+00:00
-- url     : https://prove2.me/submissions/c7d25a30-33fc-471b-bb6c-1736a959eeb5

import Definitions.Def_Formalism_PeriodIntegrals_SDiffGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_SDiffGramMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_PhOn_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_PhVF_equiv
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_ren_GramRhs
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_ren_PhVF


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SDiffGram
open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_X simeq_ren ren_be)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub)
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.SDiffGram
theorem _root_.solution (hl0 : PowerSeries.constantCoeff l = 0) (hex0 : PowerSeries.constantCoeff ex = 0)
    {S : Set (ℂ_[p] × ℂ_[p])}
    (hG : ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A))
    {κ T τ : Type} [Fintype κ] [Fintype T] {n : ℕ} (e : T ≃ Fin n) (r : T → τ)
    (a : T → κ → ℂ_[p] × ℂ_[p]) (ha : ∀ x k, a x k ∈ S) :
    Simeq (PhVF l ex ph a (fun x => X (r x))) (GR l ex ph e a (fun x => X (r x))) := by
  have h := simeq_ren (p := p) (fun j => r (e.symm j)) (hG κ n (fun j => a (e.symm j)) (fun j i => ha _ i))
  rw [PhOn_eq, ren_PhVF hex0 hl0 _ _ _ (fun j => constantCoeff_X j), ren_GramRhs hex0 hl0 e] at h
  simp only [ren_X, Equiv.symm_apply_apply] at h
  have eA : PhVF l ex ph (fun j => a (e.symm j)) (fun j => X (r (e.symm j)) : Fin n → MvPowerSeries τ ℂ_[p]) =
      PhVF l ex ph a (fun x => X (r x)) := PhVF_equiv e a (fun x => X (r x))
  rwa [eA] at h
end PI.UnitaryGroupMassFormula.SDiffGram
