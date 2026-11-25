-- Prove2me | solution 1 for PIW.AdelClassFin.existsBoundedMultiplier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:38.128113+00:00
-- url     : https://prove2.me/submissions/f1c5fcde-fa5b-401e-ac07-fedbf10b813a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_ExistsBoundedMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors
private lemma exists_mem_ne_zero_mul_dvd_of_mul_isPrincipal {R : Type*} [CommRing R] (I J : Ideal R)
    (hIJ : I * J ≠ ⊥) (hP : Submodule.IsPrincipal (I * J)) :
    ∃ c ∈ I, c ≠ 0 ∧ ∀ e ∈ J, ∀ g ∈ I, ∃ q : R, e * g = c * q := by
  obtain ⟨⟨c, hc⟩⟩ := hP
  have hcmem : c ∈ I * J := by
    rw [hc]; exact Submodule.mem_span_singleton_self c
  refine ⟨c, Ideal.mul_le.2 (fun a ha b _ => I.mul_mem_right b ha) hcmem, ?_, ?_⟩
  · rintro rfl
    apply hIJ
    rw [hc]; exact Submodule.span_singleton_eq_bot.2 rfl
  · intro e he g hg
    have hmem : e * g ∈ I * J := by
      rw [mul_comm I J]; exact Ideal.mul_mem_mul he hg
    rw [hc] at hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hmem
    exact ⟨q, hq⟩
private lemma ideal_mem_nonZeroDivisors_of_ne_bot {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    I ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
  mem_nonZeroDivisors_iff_ne_zero.2 (by rwa [Ideal.zero_eq_bot])
private lemma coe_nonZeroDivisors_ideal_ne_bot {E : Type} [Field E] [NumberField E] (K : ↥(nonZeroDivisors (Ideal (𝓞 E)))) :
    (K : Ideal (𝓞 E)) ≠ ⊥ := by
  have h := nonZeroDivisors.coe_ne_zero K
  rwa [Ideal.zero_eq_bot] at h
private lemma mul_isPrincipal_of_classGroup_mk0_eq_inv {E : Type} [Field E] [NumberField E] (I K : ↥(nonZeroDivisors (Ideal (𝓞 E))))
    (hK : ClassGroup.mk0 K = (ClassGroup.mk0 I)⁻¹) :
    Submodule.IsPrincipal ((I : Ideal (𝓞 E)) * (K : Ideal (𝓞 E))) := by
  have hK1 : ClassGroup.mk0 (I * K) = 1 := by
    rw [map_mul, hK, mul_inv_cancel]
  exact (ClassGroup.mk0_eq_one_iff (I * K).2).1 hK1
private lemma exists_bounded_norm_ideal_mul_isPrincipal {E : Type} [Field E] [NumberField E] :
    ∃ B : ℕ, ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J ≤ B ∧
      I * J ≠ ⊥ ∧ Submodule.IsPrincipal (I * J) := by
  letI hF : Fintype (ClassGroup (𝓞 E)) := NumberField.RingOfIntegers.instFintypeClassGroup E
  choose rep hrep using (ClassGroup.mk0_surjective (R := 𝓞 E))
  refine ⟨Finset.univ.sup (fun x => Ideal.absNorm ((rep x : Ideal (𝓞 E)))), ?_⟩
  intro I hI
  refine ⟨rep (ClassGroup.mk0 ⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩)⁻¹, coe_nonZeroDivisors_ideal_ne_bot _,
    Finset.le_sup (f := fun x => Ideal.absNorm ((rep x : Ideal (𝓞 E)))) (Finset.mem_univ _),
    coe_nonZeroDivisors_ideal_ne_bot (⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩ * rep (ClassGroup.mk0 ⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩)⁻¹),
    mul_isPrincipal_of_classGroup_mk0_eq_inv ⟨I, ideal_mem_nonZeroDivisors_of_ne_bot I hI⟩ _ (hrep _)⟩
end PIW.AdelClassFin
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors
namespace PIW.AdelClassFin
theorem _root_.solution : IdealBoundAll := by
  intro E _ _
  obtain ⟨B, hB⟩ := exists_bounded_norm_ideal_mul_isPrincipal (E := E)
  refine ⟨B, fun I hI => ?_⟩
  obtain ⟨J, hJ0, hJB, hIJ0, hP⟩ := hB I hI
  obtain ⟨c, hcI, hc0, hc⟩ := exists_mem_ne_zero_mul_dvd_of_mul_isPrincipal I J hIJ0 hP
  exact ⟨c, hcI, hc0, Ideal.absNorm J,
    Nat.one_le_iff_ne_zero.2 (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)), hJB, hc _ (Ideal.absNorm_mem J)⟩
end PIW.AdelClassFin
