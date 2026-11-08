-- Prove2me | solution 1 for RainsSep.Distill.kraus_choi_partial_trace
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:13:40.125296+00:00
-- url     : https://prove2.me/submissions/9bccb4ac-75a9-4098-86c4-9f6afe868f0a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RainsSep_Distill_krausChoi

open QAlgorithms

open scoped Matrix

open RainsSep.Distill in
theorem solution {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq V] (E : ι → Matrix W V ℂ) (hE : IsKrausFamily E) :
    (Matrix.of fun v v' : V => ∑ w : W, ∑ i : ι, krausChoi (E i) (v, w) (v', w)) = 1 := by
  ext v v'
  have h : (∑ j, (E j)ᴴ * E j) v' v = (1 : Matrix V V ℂ) v' v := by
    unfold IsKrausFamily at hE
    rw [hE]
  rw [Matrix.sum_apply] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  have h1 : (1 : Matrix V V ℂ) v' v = (1 : Matrix V V ℂ) v v' := by
    by_cases hv : v = v'
    · subst hv; rfl
    · rw [Matrix.one_apply_ne hv, Matrix.one_apply_ne (Ne.symm hv)]
  rw [← h1, ← h, Matrix.of_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun w _ => ?_))
  simp only [krausChoi, QAlgorithms.pureDensity, opVec, Matrix.of_apply, PiLp.toLp_apply]
  exact mul_comm _ _
