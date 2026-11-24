-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:26.003151+00:00
-- url     : https://prove2.me/submissions/8f495560-e75f-4852-82dc-208ffc8f0187

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_log_dualNorm_slice_70443648dabb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3


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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace SliceSectionMass
theorem _root_.solution (hSt : StokesOnVariety.Statement) (hPL : PoincareLelong.Statement)
    (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement) (hE : SliceExhaustion.Statement) :
    SliceSectionMass.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) J F ℓ hJ hF hℓ
  obtain ⟨hinj, himg, hmult⟩ := hC n J u ℓ hJ hℓW
  obtain ⟨f, hfs, hfc, -, -, hlimJ, hlimW, herr⟩ := hE n e h J F u ℓ hJ hF hu hℓ hℓW
  have hsm := smoothNear_log_dualNorm_slice h J ℓ
  have hk : ∀ k, ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) +
      (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
          (vecCons (f k) fun _ x => Real.log (h.dualNorm x)) -
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
          (vecCons (f k) fun _ x => Real.log (h.dualNorm x))) =
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (f k)
        (fun _ x => Real.log (h.dualNorm x)) := by
    intro k
    have hS := hSt n e _ (f k) (fun x => Real.log (h.dualNorm x))
      (fun _ x => Real.log (h.dualNorm x)) hprime hdim (smoothNear_of_contDiff (hfs k)) hsm (fun _ => hsm)
      (Or.inl (hfc k))
    have hP := hPL n e _ u (f k) (fun _ x => Real.log (h.dualNorm x)) hprime hdim (huJ u hu) (hfs k)
      (hfc k) (fun _ => hsm)
    have hcons : (vecCons (fun x => Real.log (h.dualNorm x)) fun (_ : Fin e) x =>
        Real.log (h.dualNorm x)) = fun _ x => Real.log (h.dualNorm x) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    rw [hcons] at hS
    rw [hS, hP, ← himg, finsum_mem_image hinj, finsum_mem_coe_finset]
    have hsum : ∑ W ∈ (divCycle J u).support,
        (localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
          (W ⊔ Ideal.span {linForm ℓ - 1}) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) =
        ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) :=
      Finset.sum_congr rfl fun W hW => by rw [hmult W hW]
    rw [hsum]
    ring
  have hlim := (tendsto_finsetSum _ fun W hW => (hlimW W hW).const_mul
    ((divCycle J u W : ℕ) : ℝ)).add herr
  rw [add_zero] at hlim
  exact tendsto_nhds_unique hlimJ (hlim.congr hk)
end SliceSectionMass
end GroundTheory.Heights₂.Heights
