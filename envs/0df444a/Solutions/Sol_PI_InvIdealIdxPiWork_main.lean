-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:58.524318+00:00
-- url     : https://prove2.me/submissions/43259bdf-97af-4292-8edf-7f18ab453216

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup
import Theorems.Thm_PI_InvIdealIdxPiWork_map_compLeft_pi
import Theorems.Thm_PI_InvIdealIdxPiWork_pi_mono
import Theorems.Thm_PI_InvIdealIdxPiWork_submodule_pi_toAddSubgroup
import Theorems.Thm_PI_InvIdealIdxPiWork_idS_mono
import Theorems.Thm_PI_InvIdealIdxPiWork_map_mul_inv
import Theorems.Thm_PI_InvIdealIdxPiWork_relIndex_pi_idS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace PI.InvIdealIdxPiWork
theorem _root_.solution : PI.InvIdealIdxPi := by
  unfold PI.InvIdealIdxPi
  intro E _ _ ι _ J hJ
  have hex : ∀ i, ∃ b ∈ J i, b ≠ 0 := fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
  choose b hbJ hb0 using hex
  obtain ⟨a, ha_def⟩ : ∃ a : 𝓞 E, a = ∏ i, b i := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by
    rw [ha_def]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i
  have haJ : ∀ i, a ∈ J i := by
    intro i
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem b (Finset.mem_univ i)
    rw [ha_def, hd]
    exact (J i).mul_mem_right d (hbJ i)
  have hdiv : ∀ i, ∃ K : Ideal (𝓞 E), Ideal.span {a} = J i * K := by
    intro i
    obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (haJ i)))
    exact ⟨K, hK⟩
  choose K hK using hdiv
  have hc : algebraMap (𝓞 E) E a ≠ 0 := by
    intro h
    exact ha0 (IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm))
  have hφ : Function.Injective ((AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a)).compLeft ι) := by
    intro x y h
    funext i
    exact mul_left_cancel₀ hc (congrFun h i)
  have h1 : (1 : Submodule (𝓞 E) E) =
      ((((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    rw [FractionalIdeal.coeIdeal_top, inv_one, FractionalIdeal.coe_one]
  have e1 : (fun i => ((((J i : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
      Submodule (𝓞 E) E).toAddSubgroup).map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a))) =
      fun i => idS (K i) :=
    funext fun i => map_mul_inv (J i) (K i) (hJ i) a (hK i)
  have e0 : (fun _ : ι => ((((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
      Submodule (𝓞 E) E).toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (𝓞 E) E a))) =
      fun _ => idS (Ideal.span {a}) :=
    funext fun _ => map_mul_inv ⊤ (Ideal.span {a}) top_ne_bot a (by rw [Ideal.top_mul])
  rw [submodule_pi_toAddSubgroup, submodule_pi_toAddSubgroup, h1,
    ← AddSubgroup.relIndex_map_map_of_injective _ _ hφ, map_compLeft_pi, map_compLeft_pi, e0, e1]
  have hAB : AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) (Ideal.span {a})) ≤
      AddSubgroup.pi Set.univ (fun i => idS (K i)) :=
    pi_mono fun i => idS_mono ((hK i).le.trans (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left))
  have hBC : AddSubgroup.pi Set.univ (fun i => idS (E := E) (K i)) ≤
      AddSubgroup.pi Set.univ (fun _ : ι => idS (E := E) ⊤) :=
    pi_mono fun _ => idS_mono le_top
  have hm := AddSubgroup.relIndex_mul_relIndex _ _ _ hAB hBC
  rw [relIndex_pi_idS K, relIndex_pi_idS (fun _ => Ideal.span {a})] at hm
  have hR : ∏ _i : ι, Ideal.absNorm (Ideal.span {a}) =
      (∏ i, Ideal.absNorm (J i)) * ∏ i, Ideal.absNorm (K i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hK i, map_mul]
  have hP : ∏ i, Ideal.absNorm (K i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    intro h
    have := hK i
    rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at this
    exact ha0 this
  exact mul_right_cancel₀ hP (hm.trans hR)
end PI.InvIdealIdxPiWork
