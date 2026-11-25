-- Prove2me | solution 1 for PI.LowUniSplit.lowSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:28.975997+00:00
-- url     : https://prove2.me/submissions/b28c8138-a2f5-4b67-8d1b-bbed63debdf7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Theorems.Thm_PI_LowUniSplit_mem_LPg_iff
import Theorems.Thm_PI_LowUniSplit_mem_Lstg_iff
import Theorems.Thm_PI_LowUniSplit_first_factor_mem_lower_triangular
import Theorems.Thm_PI_LowUniSplit_second_factor_mem_lower_triangular
import Theorems.Thm_PI_LowUniSplit_fac_mul
import Theorems.Thm_PI_LowUniSplit_uniq_entries

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
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)
namespace PI.LowUniSplit
theorem _root_.solution : LowSplit := by
  intro m P hP l hl
  obtain ⟨w, d, hd, rfl⟩ := hP
  classical
  let S : Fin m → Fin m → Prop := fun i j => w.symm j < w.symm i
  have hne : ∀ i j : Fin m, i ≠ j → w.symm i ≠ w.symm j := fun i j h e => h (w.symm.injective e)
  refine ⟨(fac1 S l, fac2 S l), ⟨?_, ?_, (fac_mul S l hl).symm⟩, ?_⟩
  · rw [mem_LPg_iff w d hd _ (first_factor_mem_lower_triangular S l)]
    intro i j hij
    have hij' : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : ¬ S i j := not_lt.mpr hij.le
    simp [fac1, hij', this]
  · rw [mem_Lstg_iff w d hd _ (second_factor_mem_lower_triangular S l)]
    intro i j hij
    have hij' : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : S i j := hij
    simp [fac2, hij', this]
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    dsimp only at ha hb hab
    have ha' := (mem_LPg_iff w d hd a ha.1).1 ha
    have hb' := (mem_Lstg_iff w d hd b hb.1).1 hb
    have key := uniq_entries S l ha.1 hb.1
      (fun i j hji hs => ha' i j (lt_of_le_of_ne (not_lt.mp hs) (hne i j (ne_of_gt hji))))
      (fun i j hji hs => hb' i j hs) hab
    have e1 : a = fac1 S l := by
      ext i j
      rcases lt_trichotomy i j with h | h | h
      · rw [ha.1.1 i j h, (first_factor_mem_lower_triangular S l).1 i j h]
      · subst h; rw [ha.1.2, (first_factor_mem_lower_triangular S l).2]
      · rw [(key _ i j rfl h).1]
        by_cases hs : S i j <;> simp [fac1, ne_of_gt h, h, hs]
    have e2 : b = fac2 S l := by
      ext i j
      rcases lt_trichotomy i j with h | h | h
      · rw [hb.1.1 i j h, (second_factor_mem_lower_triangular S l).1 i j h]
      · subst h; rw [hb.1.2, (second_factor_mem_lower_triangular S l).2]
      · rw [(key _ i j rfl h).2]
        by_cases hs : S i j <;> simp [fac2, ne_of_gt h, h, hs]
    rw [e1, e2]
end PI.LowUniSplit
