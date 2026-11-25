-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SDiffGram.cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:11.141002+00:00
-- url     : https://prove2.me/submissions/10dd03a7-bdbb-477c-b3f3-f1e216dc433a

import Definitions.Def_Formalism_PeriodIntegrals_SDiffGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_RenGramRhs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramDifferenceRenaming_SDiffGramMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_good_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_simeq_iff_good
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_be
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_simeq_ren
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_cc_mulBy
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_good_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_hP_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_SDiffGram_ren_mulBy


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
    {S : Set (ℂ_[p] × ℂ_[p])} (h0 : (0 : ℂ_[p] × ℂ_[p]) ∈ S) (hsw : ∀ α ∈ S, α.swap ∈ S)
    (hadd : ∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) (hmul : ∀ α ∈ S, ∀ β ∈ S, α * β ∈ S)
    (hconj : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1))))
    {κ ι ι' : Type} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p])
    (ha : ∀ e k, a e k ∈ S) (ha' : ∀ e k, a' e k ∈ S) :
    Good (sdRF l ex ph a a' - sdRF' l ex ph a a') := by
  unfold sdRF sdRF'
  rw [← Finset.sum_sub_distrib]
  refine good_sum _ _ fun f _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine good_sum _ _ fun g _ => ?_
  have hα := hP_mem h0 hsw hadd hmul (a f) (a' g) (ha f) (ha' g)
  have h := simeq_ren (p := p) (![Sum.inl f, Sum.inr g] : Fin 2 → ι ⊕ ι') (hconj _ hα)
  simp only [Xv] at h
  rw [ren_be hex0 hl0 _ (cc_mulBy hex0 hl0 _ (constantCoeff_X _)) (constantCoeff_X _),
    ren_be hex0 hl0 _ (constantCoeff_X _) (cc_mulBy hex0 hl0 _ (constantCoeff_X _)),
    ren_mulBy hl0 _ _ (constantCoeff_X _), ren_mulBy hl0 _ _ (constantCoeff_X _)] at h
  simp only [ren_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact (simeq_iff_good _ _).mp h
end PI.UnitaryGroupMassFormula.SDiffGram
