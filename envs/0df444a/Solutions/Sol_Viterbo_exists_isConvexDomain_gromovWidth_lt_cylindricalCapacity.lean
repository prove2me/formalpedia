-- Prove2me | solution 1 for Viterbo.exists_isConvexDomain_gromovWidth_lt_cylindricalCapacity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:08:04.817028+00:00
-- url     : https://prove2.me/submissions/596b7bd0-5a5f-4a6d-a09d-18f192df2f42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isConvexDomain_one_lt_systolicRatio
import Theorems.Thm_Viterbo_exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ
import Theorems.Thm_Viterbo_gromovWidth_pow_le_factorial_mul_volume

namespace Viterbo.StrongViterbo

open MeasureTheory
open scoped ENNReal Pointwise

theorem vol_pos_fin {n : ℕ} {A : Set (OAI.SymmetricPolar.Phase n)} (hA : Viterbo.IsConvexDomain A) :
    0 < volume A ∧ volume A < ⊤ := by
  obtain ⟨hb, -, hi⟩ := hA
  refine ⟨?_, hb.measure_lt_top⟩
  have : 0 < volume (interior A) := isOpen_interior.measure_pos _ hi
  exact lt_of_lt_of_le this (measure_mono interior_subset)

theorem cylinder_smul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Viterbo.capacityCylinder n c = Real.sqrt (c / Real.pi) • Viterbo.capacityCylinder n Real.pi := by
  have hα : 0 < Real.sqrt (c / Real.pi) := Real.sqrt_pos.mpr (div_pos hc Real.pi_pos)
  have hα2 : Real.sqrt (c / Real.pi) ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα.ne']
  simp only [Viterbo.capacityCylinder, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd,
    PiLp.smul_apply, smul_eq_mul]
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  have hpc : Real.pi * (c / Real.pi) = c := by field_simp
  have key : (Real.pi * (((Real.sqrt (c / Real.pi))⁻¹ * z.1 i) ^ 2 + ((Real.sqrt (c / Real.pi))⁻¹ * z.2 i) ^ 2))
      = (Real.pi * (z.1 i ^ 2 + z.2 i ^ 2)) / (Real.sqrt (c / Real.pi)) ^ 2 := by
    field_simp
  rw [key, div_lt_iff₀ (by positivity), hα2, hpc]

theorem cEHZ_le_cyl {n : ℕ} (hn : 1 ≤ n) {A : Set (OAI.SymmetricPolar.Phase n)}
    (hA : Viterbo.IsConvexDomain A) : Viterbo.cEHZ A ≤ Viterbo.cylindricalCapacity A := by
  obtain ⟨⟨c, hc, hcA⟩, -⟩ :=
    Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ n hn
  rw [← hcA A hA]
  unfold Viterbo.cylindricalCapacity
  refine le_sInf ?_
  rintro _ ⟨r, ⟨hr, hemb⟩, rfl⟩
  refine (hc.1 _ _ hemb).trans ?_
  rw [cylinder_smul n hr, hc.2.1 _ (Real.sqrt_pos.mpr (div_pos hr Real.pi_pos)), hc.2.2.2,
    ← ENNReal.ofReal_mul (sq_nonneg _), Real.sq_sqrt (div_pos hr Real.pi_pos).le]
  rw [div_mul_cancel₀ _ Real.pi_pos.ne']

end Viterbo.StrongViterbo

open MeasureTheory
open scoped ENNReal
open Viterbo.StrongViterbo in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : Set (OAI.SymmetricPolar.Phase n), Viterbo.IsConvexDomain K ∧
      OAI.SymmetricPolar.gromovWidth K < Viterbo.cylindricalCapacity K := by
  obtain ⟨A, hA, hfin, hsys⟩ := Viterbo.exists_isConvexDomain_one_lt_systolicRatio n hn
  refine ⟨A, hA, ?_⟩
  obtain ⟨hp, hf⟩ := vol_pos_fin hA
  have hd0 : (n.factorial : ℝ≥0∞) * volume A ≠ 0 := by
    refine mul_ne_zero ?_ hp.ne'
    exact_mod_cast n.factorial_ne_zero
  have hdt : (n.factorial : ℝ≥0∞) * volume A ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hf.ne
  unfold Viterbo.systolicRatio at hsys
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hd0) (Or.inl hdt), one_mul] at hsys
  have h1 := Viterbo.gromovWidth_pow_le_factorial_mul_volume n A hA
  have h2 := cEHZ_le_cyl (by omega) hA
  by_contra hcon
  push Not at hcon
  have : Viterbo.cylindricalCapacity A ^ n ≤ OAI.SymmetricPolar.gromovWidth A ^ n :=
    pow_le_pow_left' hcon n
  have h3 : Viterbo.cEHZ A ^ n ≤ Viterbo.cylindricalCapacity A ^ n := pow_le_pow_left' h2 n
  exact absurd (lt_of_lt_of_le hsys (h3.trans (this.trans h1))) (lt_irrefl _)

