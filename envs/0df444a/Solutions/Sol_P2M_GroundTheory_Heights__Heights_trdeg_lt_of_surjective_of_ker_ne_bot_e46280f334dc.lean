-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_trdeg_lt_of_surjective_of_ker_ne_bot_e46280f334dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:36.319351+00:00
-- url     : https://prove2.me/submissions/e2c343c5-8df0-4f7c-80f1-dd79461508cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R B C : Type} [CommRing R] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≠ ⊥)
    (hinj : Function.Injective (algebraMap R C)) (hfin : trdeg R B < ℵ₀) :
    trdeg R C < trdeg R B := by
  have : Nontrivial R := (algebraMap R C).domain_nontrivial
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hinj
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R C
  have hCle : trdeg R C ≤ trdeg R B := trdeg_le_of_surjective f hf
  have hs_card : #s = trdeg R C := hs.cardinalMk_eq_trdeg
  have : Finite s := Cardinal.lt_aleph0_iff_finite.mp (hs_card ▸ hCle.trans_lt hfin)
  let y : s → B := fun i => Function.surjInv hf (i : C)
  have hfy : ∀ i, f (y i) = i := fun i => Function.surjInv_eq hf _
  have hfy' : (fun i => f (y i)) = ((↑) : s → C) := funext hfy
  have hy : AlgebraicIndependent R y := AlgebraicIndependent.of_comp f (by
    change AlgebraicIndependent R (fun i => f (y i))
    rw [hfy']
    exact hs.1)
  by_contra hlt
  push Not at hlt
  have hyb : IsTranscendenceBasis R y :=
    hy.isTranscendenceBasis_of_trdeg_le_of_finite (hlt.trans hs_card.ge)
  have halg := hyb.isAlgebraic
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hne := Ideal.comap_ne_bot_of_algebraic_mem hq0 hq (halg.isAlgebraic q)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have ha' : f (a : B) = 0 := by
    simpa [Ideal.mem_comap, RingHom.mem_ker] using ha
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial s R, aeval y P = a := by
    have h : (a : B) ∈ (aeval y : MvPolynomial s R →ₐ[R] B).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact a.2
    exact h
  have hPx : aeval ((↑) : s → C) P = 0 := by
    rw [← hfy', ← comp_aeval_apply, hP, ha']
  have hP0 : P = 0 := hs.1 (hPx.trans (map_zero _).symm)
  apply ha0
  apply Subtype.ext
  rw [← hP, hP0, map_zero]
  rfl
end GroundTheory.Heights₂.Heights
