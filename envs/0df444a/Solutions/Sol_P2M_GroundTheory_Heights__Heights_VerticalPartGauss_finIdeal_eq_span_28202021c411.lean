-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_eq_span_28202021c411
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:00.522956+00:00
-- url     : https://prove2.me/submissions/0d4dc4c2-323d-4be7-8d08-eaad37a9f1da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.VerticalPartGauss
theorem _root_.solution {P : Ideal (MRing (PBlk n))} {S : Set (MRing (PBlk n))}
    (hS : P = Ideal.span S) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = Ideal.span (rename (blkEquiv n).symm '' S) := by
  have hre : ∀ x : MvPolynomial (Fin n) ℤ, rename (blkEquiv n).symm (rename (fun i : Fin n =>
      (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x) = x := fun x => by
    rw [rename_rename]
    exact rename_id_apply x
  have hre' : ∀ s : MRing (PBlk n), rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))
      (rename (blkEquiv n).symm s) = s := fun s => by
    rw [rename_rename]
    convert rename_id_apply s
    funext p
    rcases p with ⟨⟨⟩, i⟩
    rfl
  apply le_antisymm
  · intro x hx
    have hx' : rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x ∈ Ideal.span S := by
      rw [← hS]; exact hx
    have := Ideal.mem_map_of_mem (rename (blkEquiv n).symm : MRing (PBlk n) →ₐ[ℤ] _).toRingHom hx'
    rw [Ideal.map_span] at this
    simpa [hre] using this
  · rw [Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    change rename _ (rename (blkEquiv n).symm s) ∈ P
    rw [hre', hS]
    exact Ideal.subset_span hs
end GroundTheory.Heights₂.Heights.VerticalPartGauss
