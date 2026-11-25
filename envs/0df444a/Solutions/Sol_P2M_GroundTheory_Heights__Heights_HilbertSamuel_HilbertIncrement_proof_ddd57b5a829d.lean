-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_proof_ddd57b5a829d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:37:37.938178+00:00
-- url     : https://prove2.me/submissions/da57db69-ea01-44af-8ce0-b2f657a5e8b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultiHomogIdeal_sup_X_69669440edab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_quotPiece_natCast_c8e9aee8bbc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultigrading_quotPiece_4a2432f4cf83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_closed_52aa7c2563e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_HilbertIncrement_closed_4d09085c2c1d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
theorem _root_.solution (hrec : IntersectionRecursion.Statement.{u}) : HilbertIncrement.Statement.{u} := by
  intro d hmod F _ K _ _ ι _ q hq hdim b
  obtain ⟨i, hi⟩ := hq.relevant b
  have hJ : IsMultiHomogIdeal (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) :=
    isMultiHomogIdeal_sup_X hq.multiHomog ⟨b, i⟩
  obtain ⟨hstep, hsupp⟩ :=
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.HilbertIncrement.closed.{u} F K ι (d + 1) q b i hq
      hdim (by omega) hi
  obtain ⟨a₀, C, hbd⟩ := hmod F K ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}))
    (quotPiece _) (isMultigrading_quotPiece hJ) (fun W hW hann => by
      rw [Ideal.annihilator_quotient] at hann
      simpa using hsupp W hW hann)
  refine ⟨a₀, C, fun a ha => ?_⟩
  have h1 : hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) =
      (Module.finrank F (quotPiece (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})
        fun k => (a k : ℤ)) : ℤ) := by
    rw [show unitDeg b = Pi.single b 1 from rfl, hstep, hilbFn,
      if_pos (fun k => Nat.cast_nonneg _), quotPiece_natCast]
    have ha' : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => by omega
    rw [ha']
  have h2 : intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) =
      topCycleNum F ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) d
        (fun _ => fun k => (a k : ℤ)) := by
    rw [hrec F K ι q d hq hdim b i hi]
    unfold topCycleNum
    refine finsum_congr fun W => ?_
    have hann : Module.annihilator (MRing ι F)
        (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) =
        q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} := Ideal.annihilator_quotient
    by_cases hc : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dif_pos hc, dif_pos (by rw [hann]; exact hc)]
      rfl
    · rw [dif_neg hc, dif_neg (by rw [hann]; exact hc)]
  rw [h1, h2]
  simpa using hbd a ha
end GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
