-- Prove2me | solution 1 for WeierstrassProjModel.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/cc20d4e3-91b9-50e5-9523-bb8f536ec1ad

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel HomogeneousLocalization WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 320000

namespace ChartVCAux

variable {T : Type u} [CommRing T]

noncomputable def zden (V : WeierstrassCurve.Projective T) : Submonoid.powers (coord V 2) :=
  ⟨coord V 2 ^ 1, (Submonoid.mem_powers_iff _ _).mpr ⟨1, rfl⟩⟩

theorem val_sc (V : WeierstrassCurve.Projective T) (b : T) :
    (fromZeroRingHom (projModelGradingCR V) (Submonoid.powers (coord V 2)) (algebraMap T ((projModelGradingCR V) 0) b)).val =
      algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2))) (cls V (MvPolynomial.C b)) := rfl

theorem val_awaymk (V : WeierstrassCurve.Projective T) (x : ProjModelRingCR V) (hx : x ∈ projModelGradingCR V (1 • 1)) :
    (Away.mk (projModelGradingCR V) (coord_mem V 2) 1 x hx).val =
      IsLocalization.mk' (Localization (Submonoid.powers (coord V 2))) x (zden V) := by
  rw [Away.val_mk, Localization.mk_eq_mk']; rfl

theorem val_xOverZ (V : WeierstrassCurve.Projective T) :
    (xOverZ V).val = IsLocalization.mk' (Localization (Submonoid.powers (coord V 2))) (coord V 0) (zden V) :=
  val_awaymk V _ _

theorem val_yOverZ (V : WeierstrassCurve.Projective T) :
    (yOverZ V).val = IsLocalization.mk' (Localization (Submonoid.powers (coord V 2))) (coord V 1) (zden V) :=
  val_awaymk V _ _

theorem val_lin (V : WeierstrassCurve.Projective T) (c d : T) :
    (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) c) * xOverZ V +
      fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) d)).val =
      IsLocalization.mk' (Localization (Submonoid.powers (coord V 2)))
        (cls V (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 2)) (zden V) := by
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul, val_sc, val_sc, val_xOverZ]
  symm
  rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, add_mul, mul_assoc, IsLocalization.mk'_spec]
  rw [← map_mul (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2)))),
    ← map_mul (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2)))),
    ← map_add (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2))))]
  congr 1
  show _ = Ideal.Quotient.mk _ _
  simp only [cls, coord, zden, map_add, map_mul, pow_one]

theorem val_lin3 (V : WeierstrassCurve.Projective T) (c d e : T) :
    (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) c) * yOverZ V +
      fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) d) * xOverZ V +
      fromZeroRingHom (projModelGradingCR V) _ (algebraMap T ((projModelGradingCR V) 0) e)).val =
      IsLocalization.mk' (Localization (Submonoid.powers (coord V 2)))
        (cls V (MvPolynomial.C c * MvPolynomial.X 1 + MvPolynomial.C d * MvPolynomial.X 0 + MvPolynomial.C e * MvPolynomial.X 2))
        (zden V) := by
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mul, val_sc, val_sc, val_sc, val_xOverZ, val_yOverZ]
  symm
  rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, add_mul, add_mul, mul_assoc, mul_assoc, IsLocalization.mk'_spec,
    IsLocalization.mk'_spec]
  rw [← map_mul (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2)))),
    ← map_mul (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2)))),
    ← map_mul (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2)))),
    ← map_add (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2)))),
    ← map_add (algebraMap (ProjModelRingCR V) (Localization (Submonoid.powers (coord V 2))))]
  congr 1
  show _ = Ideal.Quotient.mk _ _
  simp only [cls, coord, zden, map_add, map_mul, pow_one]

end ChartVCAux

open ChartVCAux in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ) :
    ∃ a : ZChartRing W →+* ZChartRing (C • W),
      zChartι (C • W) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W ∧
      (∀ b : T, a (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) b)) =
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) b)) ∧
      a (xOverZ W) =
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) ((C.u : T) ^ 2)) *
          xOverZ (C • W) +
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) C.r) ∧
      a (yOverZ W) =
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) ((C.u : T) ^ 3)) *
          yOverZ (C • W) +
        fromZeroRingHom (projModelGradingCR (C • W)) _
            (algebraMap T ((projModelGradingCR (C • W)) 0) ((C.u : T) ^ 2 * C.s)) * xOverZ (C • W) +
        fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) C.t) := by
  obtain ⟨hC, hX, hY, hZ⟩ := hvc
  have key : ∀ (s : ProjModelRingCR (C • W)) (hs : s ∈ projModelGradingCR (C • W) 1)
      (e : φ (coord W 2) = s),
      ∃ a : ZChartRing W →+* Away (projModelGradingCR (C • W)) s,
        Proj.awayι (projModelGradingCR (C • W)) s hs one_pos ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom a) ≫ zChartι W ∧
        (∀ b : T, a (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) b)) =
          fromZeroRingHom (projModelGradingCR (C • W)) _ (algebraMap T ((projModelGradingCR (C • W)) 0) b)) ∧
        a (xOverZ W) = Away.mk (projModelGradingCR (C • W)) hs 1 (φ (coord W 0))
          (by simpa using φ.map_mem (coord_mem W 0)) ∧
        a (yOverZ W) = Away.mk (projModelGradingCR (C • W)) hs 1 (φ (coord W 1))
          (by simpa using φ.map_mem (coord_mem W 1)) := by
    intro s hs e
    subst e
    refine ⟨Away.map φ (coord W 2), ?_, ?_, ?_, ?_⟩
    · exact Proj.awayι_comp_map φ hφ one_pos (coord W 2) (coord_mem W 2)
    · intro b
      apply HomogeneousLocalization.val_injective
      show (HomogeneousLocalization.map φ _ (HomogeneousLocalization.mk _)).val = (HomogeneousLocalization.mk _).val
      rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
        Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq']
      congr 1
      show φ (cls W (MvPolynomial.C b)) * ((1 : (projModelGradingCR (C • W)) 0) : ProjModelRingCR (C • W)) =
        cls (C • W) (MvPolynomial.C b) * φ ((1 : (projModelGradingCR W) 0) : ProjModelRingCR W)
      rw [hC b]
      simp
    · show Away.map φ (coord W 2) (Away.mk _ (coord_mem W 2) 1 (coord W 0) _) = _
      rw [Away.map_mk]
    · show Away.map φ (coord W 2) (Away.mk _ (coord_mem W 2) 1 (coord W 1) _) = _
      rw [Away.map_mk]
  obtain ⟨a, ha, hsc, hax, hay⟩ := key (coord (C • W) 2) (coord_mem (C • W) 2) hZ
  refine ⟨a, ha, hsc, ?_, ?_⟩
  · rw [hax]
    apply HomogeneousLocalization.val_injective
    rw [val_awaymk, val_lin, ← hX]
  · rw [hay]
    apply HomogeneousLocalization.val_injective
    rw [val_awaymk, val_lin3, ← hY]

end S_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom
end P2MW
export P2MW.S_WeierstrassProjModel_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota_of_isVariableChangeHom (solution)
