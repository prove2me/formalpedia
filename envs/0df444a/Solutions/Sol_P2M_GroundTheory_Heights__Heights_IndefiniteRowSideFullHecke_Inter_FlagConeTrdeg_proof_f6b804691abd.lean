-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagConeTrdeg_proof_f6b804691abd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:00:09.194614+00:00
-- url     : https://prove2.me/submissions/d6e71cca-9c05-46c7-8658-4ade828d703f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagConeTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_flagMap_X_2c846709d619
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_range_aeval_flagMap_X_ffa3ac4f6640

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagConeTrdeg
theorem _root_.solution (h₁ : TrdegAdjoinFrac.Statement) (h₂ : FlagMinorsBaseChange.Statement)
    (h₃ : FlagMinorsTrdeg.Statement) : FlagConeTrdeg.Statement := by
  intro K _ ι _ N1 n P B hP hH hB
  have hinj : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : C a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [Ideal.Quotient.algebraMap_eq, algebraMap_eq] using ha
    have h2 : a ∈ P.comap (C : ℤ →+* MRing ι) := this
    rwa [hH, Ideal.mem_bot] at h2
  have e := Ideal.quotientKerEquivRange
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))
  have hk : RingHom.ker
      (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) =
        flagIdeal P B := by
    ext f
    have h : ((aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
          MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) f = flagMap P B f := by
      rw [aeval_flagMap_X]
    rw [RingHom.mem_ker, flagIdeal, RingHom.mem_ker, ← h, RingHom.coe_coe]
  have ht : Algebra.trdeg ℤ (MRing (FlagBundleBlocks ι N1 n) ⧸ RingHom.ker
      (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))) =
      Algebra.trdeg ℤ (aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range := by
    have e' : (MRing (FlagBundleBlocks ι N1 n) ⧸ RingHom.ker (aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))) ≃ₐ[ℤ]
        (aeval fun q => flagMap P B (X q) :
          MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range := e
    exact e'.trdeg_eq
  have e2 := h₂ (FnField P) n N1 B hB
  rw [← hk, ht, range_aeval_flagMap_X]
  exact (h₁ (MRing ι ⧸ P) (MvPolynomial (Fin n × Fin n) (FnField P)) _ hinj).trans (by rw [e2, h₃])
end FlagConeTrdeg
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
