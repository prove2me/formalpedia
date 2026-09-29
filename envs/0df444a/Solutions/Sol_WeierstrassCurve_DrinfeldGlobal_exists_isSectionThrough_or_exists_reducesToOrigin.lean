-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d85d302a-0737-57fd-aa85-d4da7a0cb19f

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization WeierstrassCurve.DrinfeldGlobal MvPolynomial

namespace LocalSectionDichotomyAux

variable {T : Type u} [CommRing T]

theorem exists_eq_specMap_comp_awayι [IsLocalRing T] (W : WeierstrassCurve.Projective T)
    {f : ProjModelRingCR W} {m : ℕ} (f_deg : f ∈ projModelGradingCR W m) (hm : 0 < m)
    (s : Spec (CommRingCat.of T) ⟶ projModelCR W)
    (hs : s (closedPoint T) ∈ Proj.basicOpen (projModelGradingCR W) f) :
    ∃ χ : Away (projModelGradingCR W) f →+* T,
      s = Spec.map (CommRingCat.ofHom χ) ≫ Proj.awayι (projModelGradingCR W) f f_deg hm := by
  classical
  have hclosed : s (closedPoint T) ∈ (Proj.awayι (projModelGradingCR W) f f_deg hm).opensRange := by
    rw [Proj.opensRange_awayι]; exact hs
  have htop : s ⁻¹ᵁ (Proj.awayι (projModelGradingCR W) f f_deg hm).opensRange = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem s hclosed
  have hrange : Set.range s ⊆ Set.range (Proj.awayι (projModelGradingCR W) f f_deg hm) := by
    rintro _ ⟨x, rfl⟩
    have hx' : x ∈ s ⁻¹ᵁ (Proj.awayι (projModelGradingCR W) f f_deg hm).opensRange := by
      rw [htop]; trivial
    exact hx'
  set l := IsOpenImmersion.lift (Proj.awayι (projModelGradingCR W) f f_deg hm) s hrange with hl_def
  have hl : l ≫ Proj.awayι (projModelGradingCR W) f f_deg hm = s := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(Spec.preimage l).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, hl]

theorem exists_coord_zero_pow_three_eq (W : WeierstrassCurve.Projective T) :
    ∃ q : ProjModelRingCR W, coord W 0 ^ 3 = coord W 2 * q := by
  refine ⟨Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal
    (X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 * X 2
      - C W.a₂ * X 0 ^ 2 - C W.a₄ * X 0 * X 2 - C W.a₆ * X 2 ^ 2), ?_⟩
  have hP : Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal W.polynomial = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, projModelHomogeneousIdealCR_toIdeal]
    exact Ideal.mem_span_singleton_self _
  have hid : (X 0 : MvPolynomial (Fin 3) T) ^ 3 =
      X 2 * (X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 * X 2
        - C W.a₂ * X 0 ^ 2 - C W.a₄ * X 0 * X 2 - C W.a₆ * X 2 ^ 2) - W.polynomial := by
    rw [WeierstrassCurve.Projective.polynomial]; ring
  show Ideal.Quotient.mk _ (X 0) ^ 3 = Ideal.Quotient.mk _ (X 2) * Ideal.Quotient.mk _ _
  rw [← map_pow, hid, map_sub, hP, sub_zero, map_mul]

theorem isLocalizationElem_eq (W : WeierstrassCurve.Projective T) (g : ProjModelRingCR W)
    (hg : g ∈ projModelGradingCR W 1) :
    Away.isLocalizationElem (coord_mem W 1) hg =
      HomogeneousLocalization.Away.mk (projModelGradingCR W) (coord_mem W 1) 1 g (by simpa using hg) := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.isLocalizationElem, Away.val_mk, pow_one]

end LocalSectionDichotomyAux

open LocalSectionDichotomyAux

theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (S : Section W) :
    (∃ x y : T, IsSectionThrough S x y) ∨ (∃ χ : OriginChartRing W →+* T, ReducesToOrigin S χ (maximalIdeal T)) := by
  classical
  by_cases hZ : S.1 (closedPoint T) ∈ Proj.basicOpen (projModelGradingCR W) (coord W 2)
  · left
    obtain ⟨χ, hχ⟩ := exists_eq_specMap_comp_awayι W (coord_mem W 2) one_pos S.1 hZ
    exact ⟨affX χ, affY χ, χ, hχ, rfl, rfl⟩
  · right
    have hZmem : coord W 2 ∈ (S.1 (closedPoint T)).asHomogeneousIdeal := by
      rwa [Proj.mem_basicOpen, not_not] at hZ
    have hXmem : coord W 0 ∈ (S.1 (closedPoint T)).asHomogeneousIdeal := by
      obtain ⟨q, hq⟩ := exists_coord_zero_pow_three_eq W
      have h3 : coord W 0 ^ 3 ∈ (S.1 (closedPoint T)).asHomogeneousIdeal := by
        rw [hq]; exact Ideal.mul_mem_right _ _ hZmem
      exact (S.1 (closedPoint T)).isPrime.mem_of_pow_mem 3 h3
    have hY : S.1 (closedPoint T) ∈ Proj.basicOpen (projModelGradingCR W) (coord W 1) := by
      rw [Proj.mem_basicOpen]
      intro hY
      apply (S.1 (closedPoint T)).not_irrelevant_le
      refine (WeierstrassProjModel.kw_pbac_irrelevant_le_span_mk_X_CR T W).trans ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hXmem
      · exact hY
      · exact hZmem
    obtain ⟨χ, hχ⟩ := exists_eq_specMap_comp_awayι W (coord_mem W 1) one_pos S.1 hY

    have key : ∀ (g : ProjModelRingCR W) (hg : g ∈ projModelGradingCR W 1),
        g ∈ (S.1 (closedPoint T)).asHomogeneousIdeal →
        χ (HomogeneousLocalization.Away.mk (projModelGradingCR W) (coord_mem W 1) 1 g (by simpa using hg)) ∈
          maximalIdeal T := by
      intro g hg hgx
      by_contra hu
      have hxg : S.1 (closedPoint T) ∈ Proj.basicOpen (projModelGradingCR W) g := by
        rw [hχ, Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
          Proj.awayι_preimage_basicOpen (projModelGradingCR W) (f_deg := coord_mem W 1) (hm := one_pos)
            (g_deg := hg) (hm' := one_pos),
          ]
        change PrimeSpectrum.comap χ (closedPoint T) ∈
          PrimeSpectrum.basicOpen (Away.isLocalizationElem (coord_mem W 1) hg)
        rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, isLocalizationElem_eq W g hg]
        exact hu
      exact (Proj.mem_basicOpen (projModelGradingCR W) g (S.1 (closedPoint T))).mp hxg hgx
    refine ⟨χ, hχ, ?_, ?_⟩
    · exact (maximalIdeal T).neg_mem (key (coord W 0) (coord_mem W 0) hXmem)
    · exact (maximalIdeal T).neg_mem (key (coord W 2) (coord_mem W 2) hZmem)

end S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin (solution)
