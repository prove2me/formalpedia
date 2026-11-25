-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_sub_mem_of_mem_twist_fibre_1e33c631d6b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:44.274999+00:00
-- url     : https://prove2.me/submissions/4ca9919f-2c1f-4b34-ad06-06d35efb7fbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {F : Type u} [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] (Q : SubSystem S x Ω) {qq : Ideal (Poly S N)}
    (hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) (𝔪 : Ideal S) {b : F}
    (hb : ∀ a ∈ 𝔪, ∃ d : S, b * algebraMap S F a = algebraMap S F d) (I : Chart x) {t : Ω}
    (ht : t ∈ (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).sub I) :
    ∃ u ∈ (Q.twist (idealSys x qq)).sub I, algebraMap F Ω b * (t - u) ∈ Q.sub I := by
  let D : Submodule (chartRing S x I) Ω :=
    { carrier := {t | ∃ u ∈ (Q.twist (idealSys x qq)).sub I, algebraMap F Ω b * (t - u) ∈ Q.sub I}
      add_mem' := by
        rintro t₁ t₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
        refine ⟨u₁ + u₂, Submodule.add_mem _ hu₁ hu₂, ?_⟩
        rw [show algebraMap F Ω b * (t₁ + t₂ - (u₁ + u₂)) =
          algebraMap F Ω b * (t₁ - u₁) + algebraMap F Ω b * (t₂ - u₂) by ring]
        exact Submodule.add_mem _ h₁ h₂
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
      smul_mem' := by
        rintro c t ⟨u, hu, h⟩
        refine ⟨c • u, Submodule.smul_mem _ c hu, ?_⟩
        have := Submodule.smul_mem _ c h
        rw [chartRing_smul_def] at this
        rw [chartRing_smul_def, chartRing_smul_def,
          show algebraMap F Ω b * ((c : Ω) * t - (c : Ω) * u) = (c : Ω) * (algebraMap F Ω b * (t - u)) by ring]
        exact this }
  suffices hle : (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).sub I ≤ D from hle ht
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine Submodule.mul_le.mpr fun r hr y hy => ?_
  refine Submodule.span_induction (p := fun r _ => r * y ∈ D) ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := Submodule.mem_sup.mp hf
    have hsplit : f₁ + f₂ = homogeneousComponent e f₁ + homogeneousComponent e f₂ := by
      rw [← map_add, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hfe), if_pos rfl]
    have hg₂ : ∀ m, coeff m (homogeneousComponent e f₂) ∈ 𝔪 := by
      intro m
      rw [coeff_homogeneousComponent]
      split_ifs
      · exact (mem_map_C_iff.mp hf₂) m
      · exact 𝔪.zero_mem
    have hg₂h := homogeneousComponent_isHomogeneous e f₂
    refine ⟨aeval x (homogeneousComponent e f₁) / aeval x s * y, ?_, ?_⟩
    · rw [SubSystem.twist_sub_eq_mul_of_line]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨_, s, e, hhom f₁ hf₁ e, hs,
        homogeneousComponent_isHomogeneous e f₁, hse, rfl⟩) hy
    · have hA : algebraMap F Ω b * (aeval x (homogeneousComponent e f₂) / aeval x s) ∈ chartRing S x I := by
        choose d hd using hb
        have : algebraMap F Ω b * (aeval x (homogeneousComponent e f₂) / aeval x s) =
            ∑ m ∈ (homogeneousComponent e f₂).support,
              algebraMap S Ω (d _ (hg₂ m)) * (aeval x (monomial m (1 : S)) / aeval x s) := by
          conv_lhs => rw [(homogeneousComponent e f₂).as_sum]
          rw [map_sum, Finset.sum_div, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [aeval_monomial, aeval_monomial, map_one, one_mul,
            IsScalarTower.algebraMap_apply S F Ω (d _ (hg₂ m)), ← hd, map_mul,
            ← IsScalarTower.algebraMap_apply S F Ω]
          ring
        rw [this]
        refine Subalgebra.sum_mem _ fun m hm => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
        exact ⟨monomial m 1, s, e, hs, isHomogeneous_monomial _ (by
          rw [Finsupp.degree_eq_weight_one]; exact hg₂h (mem_support_iff.mp hm)), hse, rfl⟩
      have : algebraMap F Ω b * (aeval x (f₁ + f₂) / aeval x s * y -
          aeval x (homogeneousComponent e f₁) / aeval x s * y) =
          (⟨_, hA⟩ : chartRing S x I) • y := by
        rw [chartRing_smul_def, hsplit, map_add]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ hy
  · exact ⟨0, Submodule.zero_mem _, by simp⟩
  · intro a a' _ _ ha ha'
    rw [add_mul]
    exact D.add_mem ha ha'
  · intro c a _ ha
    have := D.smul_mem c ha
    rw [chartRing_smul_def] at this ⊢
    rw [mul_assoc]
    exact this
end GroundTheory.Heights₂.Heights.Kleiman
