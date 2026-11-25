-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartDim_minimalPrimes_transfer_3c8e8c5d49f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:17:32.074483+00:00
-- url     : https://prove2.me/submissions/cb68e6ed-c236-4bfa-822d-8d1e1b327cfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.SegreChartDim
namespace GroundTheory.Heights₂.Heights.SegreChartDim
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (I : Ideal A) (I' : Ideal B) (hf : I ≤ I'.comap f) (hg : I' ≤ I.comap g)
    (hgf : ∀ a, g (f a) - a ∈ I) (hfg : ∀ b, f (g b) - b ∈ I') (J : Ideal A) (hJ : J ∈ I.minimalPrimes) :
    J.comap g ∈ I'.minimalPrimes ∧ ringKrullDim (A ⧸ J) = ringKrullDim (B ⧸ J.comap g) := by
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hfJ : ∀ a ∈ J, f a ∈ J.comap g := fun a ha => by
    rw [Ideal.mem_comap]
    have := hIJ (hgf a)
    simpa using J.add_mem this ha
  refine ⟨⟨⟨Ideal.comap_isPrime g J, fun b hb => hIJ (hg hb)⟩, fun Z ⟨hZp, hIZ⟩ hZJ => ?_⟩, ?_⟩
  · have hle : Z.comap f ≤ J := fun a ha => by
      have h1 : g (f a) ∈ J := hZJ ha
      have := J.sub_mem h1 (hIJ (hgf a))
      simpa using this
    have hJZ := hJ.2 ⟨Ideal.comap_isPrime f Z, fun a ha => hIZ (hf ha)⟩ hle
    intro b hb
    have h1 : f (g b) ∈ Z := hJZ hb
    have := Z.sub_mem h1 (hIZ (hfg b))
    simpa using this
  · let φ : A ⧸ J →+* B ⧸ J.comap g :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp f) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (hfJ a ha)
    let ψ : B ⧸ J.comap g →+* A ⧸ J :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk J).comp g) fun b hb =>
        Ideal.Quotient.eq_zero_iff_mem.mpr hb
    refine ringKrullDim_eq_of_ringEquiv (RingEquiv.ofRingHom φ ψ ?_ ?_)
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
      show Ideal.Quotient.mk (J.comap g) (f (g b)) = Ideal.Quotient.mk (J.comap g) b
      exact Ideal.Quotient.eq.mpr (hIJ (hg (hfg b)))
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      show Ideal.Quotient.mk J (g (f a)) = Ideal.Quotient.mk J a
      exact Ideal.Quotient.eq.mpr (hIJ (hgf a))
end GroundTheory.Heights₂.Heights.SegreChartDim
