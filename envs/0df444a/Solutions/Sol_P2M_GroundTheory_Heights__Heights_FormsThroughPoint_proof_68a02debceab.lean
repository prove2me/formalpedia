-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FormsThroughPoint_proof_68a02debceab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:52.521792+00:00
-- url     : https://prove2.me/submissions/2c4437cd-4da6-4504-999b-678136323a4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFormsThroughPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_mul_homogeneousComponent_881901500cda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053


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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace FormsThroughPoint
theorem _root_.solution (hZ : IncidenceZeroLocus.Statement) (hI : ThroughPointIncIdeal.Statement)
    (hC : ChartZeroTrdeg.Statement) (hT : ThroughTwoPointsTrdeg.Statement)
    (hB : TrdegBaseAlgebraic.Statement) : FormsThroughPoint.Statement := by
  intro F _ n k Q hQ hdim x hx hxQ
  obtain ⟨q, hqQ, hqx⟩ := hxQ

  have h1 := ComponentOfIncIdeal.one_le_ringKrullDim_quot hQ
  obtain ⟨d, hd, hdk⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
      d + 1 ≤ k := by
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at h1 hdim ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := hdim
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m =>
        have h1' : 1 ≤ m := by exact_mod_cast h1
        have hm : m ≤ k := by exact_mod_cast hdim
        refine ⟨m - 1, ?_, by omega⟩
        rw [show m - 1 + 1 = m by omega]
        rfl

  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  let c : Fin n → AlgebraicClosure F := Pi.single j₀ (x j₀)⁻¹
  have hj₀' : x j₀ ≠ 0 := hj₀
  have hc : ∑ j, c j * x j = 1 := by
    rw [Finset.sum_eq_single j₀ (fun b _ hb => by simp [c, hb]) (by simp)]
    simp [c, hj₀']
  by_contra hno
  push Not at hno

  have hg := hI F n k Q x c hc hno
  let K := AlgebraicClosure F
  let R := MvPolynomial (Fin k × Fin n) K
  let Ω := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let v : Fin k × Fin n → Ω := fun ij => algebraMap R Ω (genSubst x c ij)
  have hv : ∀ g ∈ incIdeal Q k, aeval v g = 0 := by
    intro g hgI
    have hval : aeval v g = algebraMap R Ω (aeval (genSubst x c) g) := aeval_algebraMap_apply Ω (genSubst x c) g
    rw [hval, hg g hgI, map_zero]
  obtain ⟨y, hy0, hyQ, hyv⟩ := hZ F n k Q hQ.isHomog Ω v hv

  have hnp : ∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m) := by
    intro t ht
    obtain ⟨e, he⟩ : ∃ e, aeval x (homogeneousComponent e q) ≠ 0 := by
      by_contra h
      push Not at h
      apply hqx
      rw [← sum_homogeneousComponent q, map_sum]
      exact Finset.sum_eq_zero fun e _ => h e
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hy0
      rw [ht]
      funext m
      simp
    have hzero := hyQ _ (hQ.isHomog q hqQ e)
    have hscale := aeval_mul_homogeneousComponent q e t (algebraMap K Ω ∘ x)
    simp only [Function.comp_apply] at hscale
    rw [ht, hscale, aeval_algebraMap_apply] at hzero
    exact mul_ne_zero (pow_ne_zero _ ht0) ((map_ne_zero _).mpr he) hzero

  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have hk := hT K Ω n k hinj x c hc y j hj hnp hyv
  have hb := hB F K Ω inferInstance (Fin n) (fun m => y m * (y j)⁻¹)
  have hd' := hC F n d Q hQ hd Ω y j hyQ hj
  have hkd : (k : Cardinal) ≤ d := hk.trans (hb.trans hd')
  norm_cast at hkd
  omega
end FormsThroughPoint
end GroundTheory.Heights₂.Heights
