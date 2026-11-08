-- Prove2me | solution 1 for TucciCIT.eq_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:37:30.332342+00:00
-- url     : https://prove2.me/submissions/4753069c-ff2b-44f1-bbd7-b62a8ec22415

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_TucciCIT_entanglementOfFormation

open QAlgorithms
open scoped Matrix

open TucciCIT QAlgorithms.Papers.Independent.Gap48.P20 in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (ψ : Matrix X Y ℂ) :
    entanglementOfFormation ψ = vnEntropy (ψ * ψᴴ) := by
  classical
  have hM : redistributionMarginal (Matrix.of fun i j : X × Y => ψ i.1 i.2 * star (ψ j.1 j.2))
      Prod.fst Prod.snd = ψ * ψᴴ := by
    ext a b
    unfold redistributionMarginal
    rw [Matrix.mul_apply]
    trans ∑ x : X × Y, if x.1 = a then ψ a x.2 * star (ψ b x.2) else 0
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (b, x.2)]
      · by_cases h : x.1 = a
        · rw [if_pos ⟨h, rfl, rfl⟩, if_pos h, Matrix.of_apply, h]
        · rw [if_neg (fun hh => h hh.1), if_neg h]
      · intro y _ hy
        rw [if_neg]
        rintro ⟨_, h2, h3⟩
        exact hy (Prod.ext h2 h3.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [if_pos rfl, Matrix.conjTranspose_apply]
    · intro x1 _ hx1
      exact Finset.sum_eq_zero fun x2 _ => if_neg hx1
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold entanglementOfFormation subsystemEntropy
  rw [hM]
  congr
