-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum__cdfc9455009b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:53.599565+00:00
-- url     : https://prove2.me/submissions/22dde0fb-cd59-4613-a966-5026036c0713

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_polCoef
import Theorems.Thm_ReciprocityTheory_AnForm_A_polCoef_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k *
      mdisc (Fin.cons (Matrix.single j k 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  classical
  have key : ∀ r : Fin (n + 1) → Fin (n + 1),
      polCoef r * (Matrix.of fun i =>
        (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i).det =
      ∑ j, ∑ k, A j k * (polCoef r * (Matrix.of fun i =>
        (Fin.cons (Matrix.single j k 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (r i) i).det) := by
    intro r
    by_cases hs : Function.Surjective r
    · have hinj := Finite.injective_iff_surjective.mpr hs
      obtain ⟨i0, hi0⟩ := hs 0
      let M : Fin (n + 1) → Fin (n + 1) → ℂ := fun i =>
        (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i
      have hg : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          (Matrix.of fun i =>
            (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i) =
          Function.update M i0 (X i0) := by
        intro X
        funext i
        by_cases hi : i = i0
        · subst hi
          show (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i = _
          simp [hi0]
        · have hr : r i ≠ 0 := fun h => hi (hinj (h.trans hi0.symm))
          obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr hr
          show (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i = _
          simp [M, hi, ← hm]
      let Lm := (Matrix.detRowAlternating :
        (Fin (n + 1) → ℂ) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ).toMultilinearMap.toLinearMap M i0
      have hL : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          (Matrix.of fun i =>
            (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i).det =
          Lm (X i0) := by
        intro X
        rw [hg]
        rfl
      have hA : A i0 = ∑ j, ∑ k, A j k • (Matrix.single j k (1 : ℂ)) i0 := by
        ext c
        simp only [Finset.sum_apply, Pi.smul_apply, Matrix.single_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i0 (by intro b _ hb; simp [hb]) (by simp),
          Finset.sum_eq_single c (by intro b _ hb; simp [hb]) (by simp)]
        simp
      simp_rw [hL]
      rw [hA, map_sum]
      simp_rw [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · simp [polCoef_eq_zero r hs]
  rw [mdisc_eq_sum_polCoef]
  simp_rw [mdisc_eq_sum_polCoef, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => by ring
end ReciprocityTheory.AnForm.A
