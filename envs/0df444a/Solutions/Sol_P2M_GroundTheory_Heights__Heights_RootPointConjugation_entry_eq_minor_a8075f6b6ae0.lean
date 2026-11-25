-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointConjugation_entry_eq_minor_a8075f6b6ae0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:33.102944+00:00
-- url     : https://prove2.me/submissions/587c41e3-5917-4681-a4c3-fd12ac848f1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointConjugation
namespace GroundTheory.Heights₂.Heights.RootPointConjugation
theorem _root_.solution {j m : ℕ} (a : Fin j) (b : Fin m) :
    ∃ s : ℤ, ∀ (R : Type) [CommRing R] (Z : Matrix (Fin j) (Fin m) R),
      Z a b = s * (colsOf (onePipe Z) (idxAB a b)).det := by
  classical
  set I := idxAB a b
  have hmem : ∀ c, colAB a b c ∈ I.1 := fun c => by simp [I, idxAB]
  let e' : Fin j → Fin j := fun c => (I.1.orderIsoOfFin I.2).symm ⟨colAB a b c, hmem c⟩
  have he' : ∀ c, I.1.orderEmbOfFin I.2 (e' c) = colAB a b c := fun c => by
    rw [← Finset.coe_orderIsoOfFin_apply]; simp [e']
  have hinj : Function.Injective e' := fun c d h => colAB_injective a b (by rw [← he', ← he', h])
  let e := Equiv.ofBijective e' (Finite.injective_iff_bijective.mp hinj)
  refine ⟨(Equiv.Perm.sign e : ℤ), fun R _ Z => ?_⟩
  have hsub : (colsOf (onePipe Z) I).submatrix id e = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r c
    simp only [submatrix_apply, colsOf, id, e, Equiv.ofBijective_apply, he', updateCol_apply, onePipe,
      of_apply, colAB]
    split_ifs <;> simp [Fin.append_left, Fin.append_right]
  have := Matrix.det_permute' e (colsOf (onePipe Z) I)
  rw [hsub, ← cramer_apply, cramer_one] at this
  exact this
end GroundTheory.Heights₂.Heights.RootPointConjugation
