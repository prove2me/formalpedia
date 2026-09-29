-- Prove2me | solution 1 for RingHom.laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3500326a-a884-57bf-b47d-5be4532ddffd

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul

universe u v

theorem solution {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (Λ : A →+* LaurentSeries R) (hΛC : ∀ r : R, Λ (algebraMap R A r) = HahnSeries.C r)
    {t₀ : A} (ht₀ : Λ t₀ = HahnSeries.single 1 1) :
    (∀ g c : A, KaehlerDifferential.D R A g = c • KaehlerDifferential.D R A t₀ →
        LaurentSeries.derivative R (Λ g) = Λ c) ∧
      (Nontrivial R → KaehlerDifferential.D R A t₀ ≠ 0) := by

  letI : Module A (LaurentSeries R) := Module.compHom (LaurentSeries R) Λ
  have hsmul : ∀ (r : R) (a : A), Λ (r • a) = r • Λ a := fun r a => by
    rw [Algebra.smul_def, map_mul, hΛC, HahnSeries.C_mul_eq_smul]
  haveI : IsScalarTower R A (LaurentSeries R) := ⟨fun r a x => by
    change Λ (r • a) * x = r • (Λ a * x)
    rw [hsmul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]⟩
  let ΛL : A →ₗ[R] LaurentSeries R :=
    { toFun := Λ, map_add' := map_add Λ, map_smul' := hsmul }

  let δ : Derivation R A (LaurentSeries R) :=
    Derivation.mk' (LaurentSeries.derivative R ∘ₗ ΛL) fun f g => by
      change LaurentSeries.derivative R (Λ (f * g)) =
        Λ f * LaurentSeries.derivative R (Λ g) + Λ g * LaurentSeries.derivative R (Λ f)
      rw [map_mul, LaurentSeries.derivative_mul_def, mul_comm (LaurentSeries.derivative R (Λ f))]
  have hδ : ∀ g : A, δ.liftKaehlerDifferential (KaehlerDifferential.D R A g) = LaurentSeries.derivative R (Λ g) :=
    fun g => δ.liftKaehlerDifferential_comp_D g

  have hdt : LaurentSeries.derivative R (HahnSeries.single (1 : ℤ) (1 : R)) = 1 := by
    ext n
    rw [LaurentSeries.derivative_coeff, HahnSeries.coeff_single, ← HahnSeries.single_zero_one, HahnSeries.coeff_single]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg (by omega), if_neg hn, smul_zero]
  have hδt : δ.liftKaehlerDifferential (KaehlerDifferential.D R A t₀) = 1 := by rw [hδ, ht₀, hdt]
  refine ⟨fun g c hgc => ?_, fun hR hD => ?_⟩
  · have h1 := congrArg δ.liftKaehlerDifferential hgc
    rw [hδ, LinearMap.map_smul, hδt] at h1
    rw [h1]
    change Λ c * 1 = Λ c
    rw [mul_one]
  · have h1 := hδt
    rw [hD, map_zero] at h1
    exact zero_ne_one h1

end S_RingHom_laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul
end P2MW
export P2MW.S_RingHom_laurentSeries_derivative_eq_of_kaehlerDifferential_D_eq_smul (solution)
