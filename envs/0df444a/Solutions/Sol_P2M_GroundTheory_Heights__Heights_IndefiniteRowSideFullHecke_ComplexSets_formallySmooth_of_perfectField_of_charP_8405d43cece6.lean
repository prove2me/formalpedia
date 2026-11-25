-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_formallySmooth_of_perfectField_of_charP_8405d43cece6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:20.803682+00:00
-- url     : https://prove2.me/submissions/48175aba-9df1-4e5f-960d-7ef39e4d879a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothExtensionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_extend_ff791a453812
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_frobenius_aee31f96aae4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_upperBound_6efa64ebcdbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sqZeroFrobeniusLift_mk_9f7e8c1b72b5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K : Type} [Field F] [Field K] [Algebra F K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] :
    Algebra.FormallySmooth F K := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ N hN u => ?_
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap F B), CharP.cast_eq_zero, map_zero]
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  have hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p := fun z c hc => by
    show P (u z) = c ^ p
    rw [← hc, sqZeroFrobeniusLift_mk]
  obtain ⟨σ₀, hσ₀⟩ := exists_isGoodPartialLift_frobenius (K := K) p hpB hN u
  have : Nonempty {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} :=
    ⟨⟨σ₀, hσ₀⟩⟩
  obtain ⟨⟨⟨L, φ⟩, hgood⟩, hm⟩ := exists_maximal_of_nonempty_chains_bounded
    (r := fun a b : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} =>
      PartialLiftLE a.1 b.1)
    (exists_isGoodPartialLift_upperBound (p := p) (N := N) (u := u) (ψ := ψ)) (fun hab hbd => hab.trans hbd)
  have htop : (⊤ : IntermediateField F K) ≤ L := by
    intro x _
    by_contra hx
    obtain ⟨σ, hσ, hle, hxσ⟩ := exists_isGoodPartialLift_extend p hψ hgood hx
    exact hx ((hm ⟨σ, hσ⟩ hle).1 hxσ)
  refine ⟨φ.comp ((IntermediateField.inclusion htop).comp IntermediateField.topEquiv.symm.toAlgHom), ?_⟩
  ext x
  exact hgood.2 _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
