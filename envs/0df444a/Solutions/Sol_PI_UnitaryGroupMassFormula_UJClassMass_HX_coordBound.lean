-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.HX.coordBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:52.4793+00:00
-- url     : https://prove2.me/submissions/2d08bf2f-a42b-4f4c-8bb3-8bc57748d17d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
namespace HX
section T
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem exists_int_mul_isIntegral' {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * e) := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hI : Ideal.span {d} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hc : (Ideal.span {d}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ := fun h =>
    hI (Ideal.eq_bot_of_comap_eq_bot h)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hm
  obtain ⟨k, hk⟩ := hm
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hmE : (m : E) = algebraMap (𝓞 E) E k * algebraMap (𝓞 E) E d := by
    rw [← map_mul, hk]
    simp
  have hw : algebraMap (𝓞 E) E (k * n) = (m : E) * e := by
    rw [← hnd, hmE, map_mul]
    field_simp
    try ring
  refine ⟨m, hm0, ?_⟩
  rw [← hw]
  exact NumberField.RingOfIntegers.isIntegral_coe (k * n)
end T
end HX
end PI.UnitaryGroupMassFormula.UJClassMass
end
end

set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open PI.UnitaryGroupMassFormula.UJClassMass.HX
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassMass.HX
theorem _root_.solution {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x) := by
  classical
  let bw := NumberField.RingOfIntegers.basis E
  choose m hm hmi using fun (p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × ι) =>
    exists_int_mul_isIntegral' (B.coord p.2 (algebraMap (𝓞 E) E (bw p.1)))
  refine ⟨∏ p, m p, Finset.prod_ne_zero_iff.2 fun p _ => hm p, fun x hx k => ?_⟩
  obtain ⟨w, rfl⟩ := hx
  have hx' : algebraMap (𝓞 E) E w = ∑ i, ((bw.repr w i : ℤ) : E) * algebraMap (𝓞 E) E (bw i) := by
    conv_lhs => rw [← bw.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  rw [hx', map_sum, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  rw [show B.coord k (((bw.repr w i : ℤ) : E) * algebraMap (𝓞 E) E (bw i)) =
      ((bw.repr w i : ℤ) : F) * B.coord k (algebraMap (𝓞 E) E (bw i)) by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]]
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, k))
  have hq' : IsIntegral ℤ (((q * (bw.repr w i) : ℤ)) : F) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F (q * bw.repr w i)))
  convert hq'.mul (hmi (i, k)) using 1
  rw [hq]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.UJClassMass.HX
