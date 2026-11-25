-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_frobenius_aee31f96aae4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:32:01.472988+00:00
-- url     : https://prove2.me/submissions/aa8df738-f521-4df0-805a-ea023379d0cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PartialLiftLE_trans_b74671c00bb0
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
variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]
    {N : Ideal B} (hpB : (p : B) = 0) (hN : N ^ 2 = ⊥) (u : K →ₐ[F] B ⧸ N) :
    ∃ σ, IsGoodPartialLift p N u ((sqZeroFrobeniusLift N hp.out hpB hN).comp u.toRingHom) σ := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  let L₀ : IntermediateField F K :=
    { (frobenius K p).fieldRange with
      algebraMap_mem' := fun a => ⟨algebraMap F K ((frobeniusEquiv F p).symm a), by
        rw [frobenius_def, ← map_pow]; congr 1; exact (frobeniusEquiv F p).apply_symm_apply a⟩ }
  let e := (frobenius K p).rangeRestrictFieldEquiv
  have he : ∀ (y : (frobenius K p).fieldRange) (z : K), (y : K) = z ^ p → e.symm y = z :=
    fun y z h => e.symm_apply_eq.mpr (Subtype.ext (h.trans (frobenius_def p z).symm))
  let φ₀ : L₀ →ₐ[F] B :=
    { ψ.comp (e.symm.toRingHom : (frobenius K p).fieldRange →+* K) with
      commutes' := fun a => by
        obtain ⟨b, rfl⟩ := (frobeniusEquiv F p).surjective a
        have hb : algebraMap F L₀ (frobeniusEquiv F p b) =
            ⟨algebraMap F K b ^ p, ⟨algebraMap F K b, by rw [frobenius_def]⟩⟩ := by
          apply Subtype.ext
          show algebraMap F K (frobeniusEquiv F p b) = _
          rw [frobeniusEquiv_def, map_pow]
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [hb]
        show ψ (e.symm _) = _
        rw [he _ (algebraMap F K b) rfl]
        simp [ψ, P, ← Ideal.Quotient.mk_algebraMap, sqZeroFrobeniusLift_mk, frobenius_def] }
  refine ⟨⟨L₀, φ₀⟩, fun z => ⟨⟨z, by rw [frobenius_def]⟩, congrArg ψ (he _ z rfl)⟩, fun y => ?_⟩
  obtain ⟨z, hz⟩ := y.2
  have hy : y = ⟨z ^ p, ⟨z, by rw [frobenius_def]⟩⟩ := Subtype.ext (hz.symm.trans (frobenius_def p z))
  subst hy
  show Ideal.Quotient.mk N (ψ (e.symm _)) = _
  rw [he _ z rfl]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u z)
  simp [ψ, P, ← hc, sqZeroFrobeniusLift_mk]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
