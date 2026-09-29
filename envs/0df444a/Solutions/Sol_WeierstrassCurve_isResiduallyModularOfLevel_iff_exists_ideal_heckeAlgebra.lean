-- Prove2me | solution 1 for WeierstrassCurve.isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b38cad71-d421-55d8-b537-df13bd2a8479

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure
import Theorems.Thm_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra

noncomputable section

open ModularForm ModularFormClass

namespace FrobChareqC2

variable {N : ℕ} {k : ℤ}

theorem qCoeff_zero' (n : ℕ) : qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) n = 0 := by
  simp only [qCoeff, CuspForm.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

end FrobChareqC2

p2m_open "P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra.FrobChareqC2 CuspForm ModularForm.CuspForm"

theorem solution (W : WeierstrassCurve ℤ) {p M : ℕ} [NeZero M] (hM : CuspForm.HasIntegralStructure M 2) : W.IsResiduallyModularOfLevel p M ↔ ∃ 𝔪 : Ideal (CuspForm.heckeAlgebra M 2 {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}), 𝔪.IsMaximal ∧ (p : CuspForm.heckeAlgebra M 2 {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}) ∈ 𝔪 ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}), CuspForm.heckeAlgebra.T hℓ hℓM hℓS - (W.apOfModel ℓ : CuspForm.heckeAlgebra M 2 {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M}) ∈ 𝔪 := by
  set S : Set ℕ := {ℓ | ¬ W.IsGoodPrimeFor ℓ ∨ ℓ = p ∨ ℓ ∣ M} with hSdef
  haveI : Module.Finite ℤ (heckeAlgebra M 2 S) := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hM one_le_two S
  haveI : Module.Finite ℤ (heckeAlgebra M 2 ∅) := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hM one_le_two ∅
  constructor
  · rintro ⟨f, 𝔐, hf, h𝔐, hp𝔐, hcong⟩
    obtain ⟨χ, hχ⟩ := CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure hM hf S
    have hf0 : f ≠ 0 := by
      intro h
      have h1 := hf.qCoeff_one
      rw [h] at h1
      exact one_ne_zero (h1.symm.trans (qCoeff_zero' (N := M) (k := 2) 1))
    have hgen := (CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf

    have hval : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S),
        ((χ (heckeAlgebra.T hℓ hℓM hℓS) : integralClosure ℤ ℂ) : ℂ) = qCoeff ⇑f ℓ := by
      intro ℓ hℓ hℓM hℓS
      have h := hχ (heckeAlgebra.T hℓ hℓM hℓS)
      rw [heckeAlgebra.coe_T, (hgen.2 ℓ hℓ).1 hℓM] at h
      exact (smul_left_injective ℂ hf0 h).symm
    haveI : 𝔐.IsMaximal := h𝔐
    letI : Algebra (heckeAlgebra M 2 S) (integralClosure ℤ ℂ) := χ.toAlgebra
    haveI : Algebra.IsIntegral (heckeAlgebra M 2 S) (integralClosure ℤ ℂ) :=
      ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
    refine ⟨𝔐.comap χ, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔐, ?_, ?_⟩
    · rw [Ideal.mem_comap, map_natCast]
      exact hp𝔐
    · intro ℓ hℓ hℓM hℓS
      have hgood : W.IsGoodPrimeFor ℓ := by
        by_contra h
        exact hℓS (Or.inl h)
      have hℓp : ℓ ≠ p := fun h => hℓS (Or.inr (Or.inl h))
      obtain ⟨a, ha, ha𝔐⟩ := hcong ℓ hℓ hgood hℓM hℓp
      have haχ : a = χ (heckeAlgebra.T hℓ hℓM hℓS) :=
        Subtype.ext (ha.trans (hval ℓ hℓ hℓM hℓS).symm)
      rw [Ideal.mem_comap, RingHom.map_sub, map_intCast, ← haχ]
      exact ha𝔐
  · rintro ⟨𝔪, h𝔪, hp𝔪, hT𝔪⟩

    let ι : heckeAlgebra M 2 S →ₐ[ℤ] heckeAlgebra M 2 ∅ :=
      Subalgebra.inclusion (heckeAlgebra_mono (Set.empty_subset S))
    letI : Algebra (heckeAlgebra M 2 S) (heckeAlgebra M 2 ∅) := ι.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (heckeAlgebra M 2 S) (heckeAlgebra M 2 ∅) :=
      ⟨fun x => by
        have h := (Algebra.IsIntegral.isIntegral (R := ℤ) x).map_of_comp_eq
          (algebraMap ℤ (heckeAlgebra M 2 S)) (RingHom.id (heckeAlgebra M 2 ∅)) (RingHom.ext_int _ _)
        rwa [RingHom.id_apply] at h⟩
    haveI : 𝔪.IsMaximal := h𝔪
    have hker : RingHom.ker (algebraMap (heckeAlgebra M 2 S) (heckeAlgebra M 2 ∅)) ≤ 𝔪 := by
      have hinj : Function.Injective ι := Subalgebra.inclusion_injective _
      have : RingHom.ker (algebraMap (heckeAlgebra M 2 S) (heckeAlgebra M 2 ∅)) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).mp hinj
      rw [this]
      exact bot_le
    obtain ⟨𝔪', h𝔪', h𝔪'𝔪⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔪 hker
    have hover : ∀ t : heckeAlgebra M 2 S, t ∈ 𝔪 → ι t ∈ 𝔪' := by
      intro t ht
      rw [← h𝔪'𝔪, Ideal.mem_comap] at ht
      exact ht

    obtain ⟨g, 𝔐, h𝔐, h𝔐g⟩ := Ideal.exists_ringHom_integralClosure_comap_eq_of_isMaximal 𝔪' h𝔪'

    obtain ⟨f, hf, hfT, -⟩ := CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq hM ((integralClosure ℤ ℂ).val.toRingHom.comp g)
    refine ⟨f, 𝔐, hf, h𝔐, ?_, ?_⟩
    · have h1 : ι (p : heckeAlgebra M 2 S) ∈ 𝔪' := hover _ hp𝔪
      rw [map_natCast, ← h𝔐g, Ideal.mem_comap, map_natCast] at h1
      exact h1
    · intro ℓ hℓ hgood hℓM hℓp
      have hℓS : ℓ ∉ S := by
        rintro (h | h | h)
        exacts [h hgood, hℓp h, hℓM h]
      refine ⟨g (heckeAlgebra.T hℓ hℓM (Set.notMem_empty ℓ)), (hfT ℓ hℓ hℓM (Set.notMem_empty ℓ)).symm, ?_⟩
      have h1 : ι (heckeAlgebra.T hℓ hℓM hℓS - (W.apOfModel ℓ : heckeAlgebra M 2 S)) ∈ 𝔪' :=
        hover _ (hT𝔪 ℓ hℓ hℓM hℓS)
      have h2 : ι (heckeAlgebra.T hℓ hℓM hℓS) = heckeAlgebra.T hℓ hℓM (Set.notMem_empty ℓ) := rfl
      rw [map_sub, map_intCast, h2, ← h𝔐g, Ideal.mem_comap, RingHom.map_sub, map_intCast] at h1
      exact h1

end

end S_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra
end P2MW
export P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra (solution)
