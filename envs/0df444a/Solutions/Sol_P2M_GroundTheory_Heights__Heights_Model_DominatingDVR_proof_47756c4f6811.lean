-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_proof_47756c4f6811
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:41:43.567751+00:00
-- url     : https://prove2.me/submissions/5bab71a8-48cf-47f9-8b1e-f3b4d38f81a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVR
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isFractionRing_of_subalgebra_5f26c5178364

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.Model
namespace DominatingDVR
theorem _root_.solution (hKA : KrullAkizuki.Statement) (hBU : BlowUpChart.Statement) :
    DominatingDVR.Statement := by
  intro A _ _ _ _ hAf K _ _ _

  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))
  have hx' : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := hx
  have hx0 : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hAf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hx']
    exact Submodule.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  obtain ⟨i, hxi, hunit, -⟩ := hBU A K n x hx' hx0

  set B := blowUpChart K x i
  have : IsNoetherianRing B :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  have : IsFractionRing B K := isFractionRing_of_subalgebra B

  set xi : B := algebraMap A B (x i)
  have hspan : Ideal.span {xi} ≠ ⊤ := fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan
  have : q.IsPrime := hq.1.1
  have hxiq : xi ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hxi0 : xi ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by
    simpa [xi] using congrArg Subtype.val h))
  have hq1 : q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hxi0)).trans (Ideal.height_mono hq.1.2))
  have hmq : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ q := by
    rw [← hx', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have e : algebraMap A B (x j) =
        ⟨algebraMap A K (x j) / algebraMap A K (x i), Algebra.subset_adjoin ⟨j, rfl⟩⟩ * xi := by
      apply Subtype.ext
      have : algebraMap A K (x i) ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by simpa using h))
      simp [xi, div_mul_cancel₀ _ this]
    exact e ▸ q.mul_mem_left _ hxiq

  set R := Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime R q := (inferInstance : IsLocalization q.primeCompl R)
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have hdimR : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R, hq1]
    rfl

  set C := integralClosure R K
  have : IsDedekindDomain C := hKA.2 R hdimR K
  have : IsFractionRing C K := isFractionRing_of_subalgebra C
  have hinj : Function.Injective (algebraMap R C) := fun a b h =>
    by
    have h' : ((algebraMap R C a : C) : K) = ((algebraMap R C b : C) : K) := congrArg _ h
    exact IsFractionRing.injective R K h'
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal R) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    have hF : IsField R := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hPc, Ideal.comap_bot_of_injective _ hinj]
    have h0 := ringKrullDim_eq_zero_of_isField hF
    rw [hdimR] at h0
    exact one_ne_zero h0

  set V := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  letI : CommRing V := Subalgebra.toCommRing (R := C) (A := K) V
  have : IsDomain V := Subalgebra.isDomain (R := C) (A := K) V
  have : IsLocalization.AtPrime V P := (inferInstance : IsLocalization P.primeCompl V)
  have hV : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot V
  let φ : A →+* V :=
    (algebraMap C V).comp ((algebraMap R C).comp ((algebraMap B R).comp (algebraMap A B)))
  have hφ : ∀ a, (φ a : K) = algebraMap A K a := fun a => rfl
  refine ⟨Subalgebra.toSubring (R := C) V, hV, fun a => ?_, fun a => ?_⟩
  · show algebraMap A K a ∈ V
    exact hφ a ▸ (φ a).2
  show ¬ IsUnit (φ a) ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h ha => h (ha.map φ), fun ha hu => ?_⟩
  have hb : algebraMap A B a ∈ q := hmq (Ideal.mem_map_of_mem _ (by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))
  have hr : algebraMap B R (algebraMap A B a) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R q _).mpr hb
  rw [← hPc, Ideal.mem_comap] at hr
  exact (IsLocalization.AtPrime.isUnit_to_map_iff V P _).mp hu hr
end DominatingDVR
end GroundTheory.Heights₂.Heights.Model
