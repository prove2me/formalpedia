-- Prove2me | solution 1 for PI.RhsWLim.W.uwb_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:24:11.148064+00:00
-- url     : https://prove2.me/submissions/c737b42f-2c5f-490f-ae8b-df482898ffa5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_BallConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarDec
import Theorems.Thm_PI_RhsWLim_W_hpk_mulVec_gen
import Theorems.Thm_PI_RhsWLim_W_herm_bvec
import Theorems.Thm_PI_RhsWLim_W_herm_pres
import Theorems.Thm_PI_RhsWLim_W_MB_bvec_apply
import Theorems.Thm_PI_RhsWLim_W_MB_mulVec_bvec
import Theorems.Thm_PI_RhsWLim_W_embWb_wI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {p : Mat k r} (hp : p ∈ UWb k r) :
    p = embWb k r (fun i j => p (wI k r i) (wI k r j)) := by
  ext i j
  by_cases hj : j.val < r ∨ r + k < j.val
  ·
    have hcol : p *ᵥ bvec j = bvec j := by
      rcases hj with hj | hj
      · have := (hp.2 ⟨j.val, hj⟩).1
        have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
        rwa [e] at this
      · have := (hp.2 ⟨2 * r + k - j.val, by omega⟩).2
        have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rwa [e] at this
    have h1 := congrFun hcol i
    rw [MB.mulVec_bvec, MB.bvec_apply] at h1
    rw [h1]
    unfold embWb
    rw [dif_neg (by omega)]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos ⟨rfl, by omega⟩]
    · rw [if_neg hij, if_neg (fun h => hij h.1)]
  · push Not at hj
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (k + 1), wI k r j' = j :=
      ⟨⟨j.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    by_cases hi : i.val < r ∨ r + k < i.val
    ·
      have hw : (p *ᵥ bvec (wI k r j')) i = 0 := by
        rcases hi with hi | hi
        ·
          set a : Fin r := ⟨i.val, hi⟩
          have hfix := (hp.2 a).2
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (esI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (esI k r a) = i := by
            unfold HU.tau esI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (esI k r a) = 1 := by
            unfold HU.sgn esI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
        · set a : Fin r := ⟨2 * r + k - i.val, by omega⟩
          have hfix := (hp.2 a).1
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (eI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (eI k r a) = i := by
            unfold HU.tau eI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (eI k r a) = 1 := by
            unfold HU.sgn eI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
      rw [MB.mulVec_bvec] at hw
      rw [hw]
      unfold embWb
      rw [dif_neg (by omega), if_neg (fun h => by have := congrArg Fin.val h.1; simp only [wI] at this; omega)]
    · push Not at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (k + 1), wI k r i' = i :=
        ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
      have := embWb_wI (k := k) (r := r) (fun i j => p (wI k r i) (wI k r j)) i' j'
      exact this.symm
end PI.RhsWLim.W
