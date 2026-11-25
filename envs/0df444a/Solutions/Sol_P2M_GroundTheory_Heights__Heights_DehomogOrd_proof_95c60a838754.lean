-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DehomogOrd_proof_95c60a838754
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:54.734392+00:00
-- url     : https://prove2.me/submissions/0f0e0221-0155-44fd-9314-dd0b30b04b19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_ringEquiv_611c8cf7273b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_isPrime_map_C_2b9d3db6148a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_disjoint_powers_ad65955fa1d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_X_pow_mul_C_f5945d70f93b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059


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
noncomputable section
open DehomogOrd
namespace GroundTheory.Heights₂.Heights
namespace DehomogOrd
theorem _root_.solution (h₁ : OrdPolynomialLocalization.Statement) : DehomogOrd.Statement := by
  intro F _ n I W t hI hW hIW htW hP hPQ g d hg
  set P := W.map (Ideal.Quotient.mk I) with hPdef
  set PQ : Ideal (ChartRing I t) := W.map (Ideal.Quotient.mk (chartIdealOf I t)) with hPQdef
  have hPB : (Ideal.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) PQ).IsPrime :=
    isPrime_map_C Unit PQ
  have hmemP : ∀ a, Ideal.Quotient.mk I a ∈ P ↔ a ∈ W := fun a => Ideal.mem_quotient_iff_mem hIW
  have hℓP : linClass I t ∉ P := fun h => htW ((hmemP _).mp h)
  have hsPB : (X () : MvPolynomial Unit (ChartRing I t)) ∉ PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) := by
    intro h
    rw [MvPolynomial.mem_map_C_iff] at h
    have h1 : (1 : ChartRing I t) ∈ PQ := by simpa using h (Finsupp.single () 1)
    exact hPQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hdR := disjoint_powers P hℓP
  have hdB := disjoint_powers (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))) hsPB
  have hP' : (P.map (algebraMap _ (Localization.Away (linClass I t)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (linClass I t)) _ P hP hdR
  have hPS : ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
      (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hPB hdB

  have hφP : ∀ r ∈ P, toPolyR I t hI r ∈ PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) := by
    intro r hr
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have ha : a ∈ W := (hmemP a).mp hr
    rw [toPolyR_mk, ← sum_homogeneousComponent a, map_sum]
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [toPoly_hom I t (homogeneousComponent_isHomogeneous k a)]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hW a ha k)))
  have hψPQ : ∀ q ∈ PQ, fromPoly I t hI (C q) ∈ P.map (algebraMap _ (Localization.Away (linClass I t))) := by
    have hle : PQ ≤ Ideal.comap ((fromPoly I t hI).comp C)
        (P.map (algebraMap _ (Localization.Away (linClass I t)))) := by
      rw [hPQdef, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro w hw
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, fromPoly_C_mk, ← sum_homogeneousComponent w,
        map_sum]
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [fromChart_hom I t (homogeneousComponent_isHomogeneous k w)]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ((hmemP _).mpr (hW w hw k)))
    exact fun q hq => hle hq
  have hΨin : ∀ y ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
      (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))),
      fromLoc I t hI y ∈ P.map (algebraMap _ (Localization.Away (linClass I t))) := by
    have hle : (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) ≤
        Ideal.comap (fromLoc I t hI) (P.map (algebraMap _ (Localization.Away (linClass I t)))) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, fromLoc_algebraMap]
      exact hψPQ q hq
    exact fun y hy => hle hy
  have hΦin : ∀ x ∈ P.map (algebraMap _ (Localization.Away (linClass I t))),
      toLoc I t hI x ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) := by
    have hle : P.map (algebraMap _ (Localization.Away (linClass I t))) ≤
        Ideal.comap (toLoc I t hI) ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
          (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.comp_apply, toLoc_algebraMap]
      exact Ideal.mem_map_of_mem _ (hφP r hr)
    exact fun x hx => hle hx
  have hcorr : ∀ y, y ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) ↔
      (locEquiv I t hI).symm y ∈ P.map (algebraMap _ (Localization.Away (linClass I t))) := by
    intro y
    change _ ↔ fromLoc I t hI y ∈ _
    refine ⟨hΨin y, fun h => ?_⟩
    have := hΦin _ h
    rwa [toLoc_fromLoc] at this

  calc Ring.ord (Localization.AtPrime P) (algebraMap _ _ (Ideal.Quotient.mk I g))
      = Ring.ord (Localization.AtPrime (P.map (algebraMap _ (Localization.Away (linClass I t)))))
          (algebraMap _ _ (algebraMap _ (Localization.Away (linClass I t)) (Ideal.Quotient.mk I g))) :=
        (ord_atPrime_map_localization (Submonoid.powers (linClass I t)) P hdR _).symm
    _ = Ring.ord (Localization.AtPrime ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
          (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))))
          (algebraMap _ _ (locEquiv I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)))) :=
        (ord_atPrime_ringEquiv (locEquiv I t hI) _ _ hcorr _).symm
    _ = Ring.ord (Localization.AtPrime ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
          (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))))
          (algebraMap _ _ (algebraMap (MvPolynomial Unit (ChartRing I t))
            (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))
            (toPolyR I t hI (Ideal.Quotient.mk I g)))) := by
        rw [show locEquiv I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)) =
          toLoc I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)) from rfl, toLoc_algebraMap]
    _ = Ring.ord (Localization.AtPrime (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))))
          (algebraMap _ _ (toPolyR I t hI (Ideal.Quotient.mk I g))) :=
        ord_atPrime_map_localization (Submonoid.powers _) (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))) hdB _
    _ = Ring.ord (Localization.AtPrime PQ) (algebraMap _ _ (Ideal.Quotient.mk (chartIdealOf I t) g)) := by
        rw [toPolyR_mk, toPoly_hom I t hg]
        exact ord_X_pow_mul_C h₁ PQ _ d
end DehomogOrd
end GroundTheory.Heights₂.Heights
