-- Prove2me | solution 1 for WeierstrassCurve.exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/23965ac3-33d2-5999-85d7-14f02ba3078a

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

namespace E0bSol

open CuspForm

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_eigenform_maximal_comap_eq (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝔪 : Ideal (heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (χ : heckeAlgebra N 2 S →+* integralClosure ℤ ℂ) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      𝔪'.IsMaximal ∧ 𝔪'.comap χ = 𝔪 ∧
      (∀ t : heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = ((χ t : integralClosure ℤ ℂ) : ℂ) • f) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ((χ (heckeAlgebra.T hℓ hℓN hℓS) : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff f ℓ := by
  obtain ⟨f, hf, hann⟩ :=
    CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime S 𝔪 h𝔪.isPrime
  obtain ⟨χ, hχf, hχT, -⟩ := hf.exists_ringHom_heckeAlgebra S
  haveI : Module.Finite ℤ (heckeAlgebra N 2 S) := CuspForm.moduleFinite_heckeAlgebra_two N S
  have hint : ∀ t : heckeAlgebra N 2 S, χ t ∈ integralClosure ℤ ℂ := fun t =>
    show IsIntegral ℤ (χ t) from map_isIntegral_int χ (IsIntegral.of_finite ℤ t)
  let χ' : heckeAlgebra N 2 S →+* integralClosure ℤ ℂ := χ.codRestrict (integralClosure ℤ ℂ) hint
  have hχ' : ∀ t, ((χ' t : integralClosure ℤ ℂ) : ℂ) = χ t := fun _ => rfl
  letI : Algebra (heckeAlgebra N 2 S) (integralClosure ℤ ℂ) := χ'.toAlgebra
  haveI : IsScalarTower ℤ (heckeAlgebra N 2 S) (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq fun n =>
      RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (integralClosure ℤ ℂ))
        ((algebraMap (heckeAlgebra N 2 S) (integralClosure ℤ ℂ)).comp
          (algebraMap ℤ (heckeAlgebra N 2 S)))) n
  haveI : Algebra.IsIntegral (heckeAlgebra N 2 S) (integralClosure ℤ ℂ) :=
    ⟨fun z => (Algebra.IsIntegral.isIntegral (R := ℤ) z).tower_top⟩
  have hker : RingHom.ker (algebraMap (heckeAlgebra N 2 S) (integralClosure ℤ ℂ)) ≤ 𝔪 := by
    intro t ht
    apply hann
    have h1 : χ' t = 0 := RingHom.mem_ker.mp ht
    have h0 : χ t = 0 := congrArg Subtype.val h1
    rw [hχf t, h0, zero_smul]
  haveI : 𝔪.IsMaximal := h𝔪
  obtain ⟨𝔪', h𝔪', hcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (R := heckeAlgebra N 2 S)
      (S := integralClosure ℤ ℂ) 𝔪 hker
  refine ⟨f, hf, χ', 𝔪', h𝔪', hcomap, fun t => by rw [hχ', hχf t], fun ℓ hℓ hℓN hℓS => ?_⟩
  rw [hχ', hχT ℓ hℓ hℓN hℓS]

end E0bSol

open CuspForm in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (W : WeierstrassCurve ℤ) (p : ℕ) (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝔪 : Ideal (heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : heckeAlgebra N 2 S) ∈ 𝔪)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      heckeAlgebra.T hℓ hℓN hℓS - (W.apOfModel ℓ : heckeAlgebra N 2 S) ∈ 𝔪) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      f.IsNormalizedEigenform ∧ 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by
  obtain ⟨f, hf, χ, 𝔪', h𝔪', hcomap, -, hχT⟩ := E0bSol.exists_eigenform_maximal_comap_eq N S 𝔪 h𝔪
  refine ⟨f, 𝔪', hf, h𝔪', ?_, fun ℓ hℓ hℓN hℓS => ⟨χ (heckeAlgebra.T hℓ hℓN hℓS), hχT ℓ hℓ hℓN hℓS, ?_⟩⟩
  · have := hp𝔪
    rw [← hcomap, Ideal.mem_comap, map_natCast] at this
    exact this
  · have := hT ℓ hℓ hℓN hℓS
    rw [← hcomap, Ideal.mem_comap, map_sub, map_intCast] at this
    exact this

end S_WeierstrassCurve_exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra
end P2MW
export P2MW.S_WeierstrassCurve_exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra (solution)
