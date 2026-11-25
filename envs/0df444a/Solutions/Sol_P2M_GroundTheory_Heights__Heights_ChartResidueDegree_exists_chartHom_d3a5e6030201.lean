-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartResidueDegree_exists_chartHom_d3a5e6030201
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:01.866368+00:00
-- url     : https://prove2.me/submissions/a7205463-7494-4ae9-bd58-00909f81ecb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_aeval_mul_of_isHomogeneous_ae2da675df58

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartResidueDegree
namespace GroundTheory.Heights₂.Heights.ChartResidueDegree
theorem _root_.solution {F : Type} [Field F] {n e : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)} [W.IsPrime]
    (hWh : IsHomogIdeal W) (hIW : I ≤ W) {t : Fin n → F}
    (ξ : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ W))
    (hξ : ∀ h, aeval ξ h = algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ W)) (Ideal.Quotient.mk W h))
    (ℓ : FractionRing (MvPolynomial (Fin n) F ⧸ W)) (hℓdef : ℓ = aeval ξ (linForm t)) (hℓ : ℓ ≠ 0)
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ W)) (hc : ∑ j, c j * ξ j = 1) :
    ∃ ΦI : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)),
      (∀ s, ΦI (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) s) = aeval (genSubst ξ c) s) ∧
      (∀ h, ΦI (chartX I t e h) = C (aeval (fun m => ξ m / ℓ) h)) ∧
      ∀ h ∈ W, aeval (fun m => ξ m / ℓ) h = 0 := by
  let Φ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →ₐ[F] MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)) :=
    aeval (Sum.elim (fun m => C (ξ m / ℓ)) (genSubst ξ c))
  have hΦinl : ∀ h, Φ (rename Sum.inl h) = C (aeval (fun m => ξ m / ℓ) h) := by
    intro h
    rw [aeval_rename, Sum.elim_comp_inl, ← algebraMap_eq]
    exact aeval_algebraMap_apply _ _ _
  have hΦinr : ∀ h, Φ (rename Sum.inr h) = aeval (genSubst ξ c) h := by
    intro h
    rw [aeval_rename, Sum.elim_comp_inr]
  have hdeh : ∀ h ∈ W, aeval (fun m => ξ m / ℓ) h = 0 := by
    intro h hh
    rw [← sum_homogeneousComponent h, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    have : (fun m => ξ m / ℓ) = fun m => ℓ⁻¹ * ξ m := funext fun m => by rw [div_eq_inv_mul]
    rw [this, aeval_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous d h), hξ,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hWh h hh d), map_zero, mul_zero]
  have hlt1 : aeval (fun m => ξ m / ℓ) (linForm t - 1) = 0 := by
    have : (fun m => ξ m / ℓ) = fun m => ℓ⁻¹ * ξ m := funext fun m => by rw [div_eq_inv_mul]
    have hlin : (linForm t).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
    rw [map_sub, map_one, this, aeval_mul_of_isHomogeneous hlin, pow_one, ← hℓdef,
      inv_mul_cancel₀ hℓ, sub_self]
  have hJ : chartIncIdeal I t e ≤ RingHom.ker Φ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun h hh => ?_) ?_
      · rw [Ideal.mem_comap, RingHom.mem_ker, hΦinl, hdeh h (hIW hh), C_0]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker,
          hΦinl, hlt1, C_0]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sum]
      simp only [map_mul, Φ, aeval_X, Sum.elim_inl, Sum.elim_inr, genSubst]
      set S := ∑ l, X (i, l) * C (ξ l)
      have h1 : ∑ m, X (i, m) * C (ξ m / ℓ) = S * C ℓ⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [div_eq_mul_inv, C_mul, mul_assoc]
      have h2 : ∑ m, S * C (c m) * C (ξ m / ℓ) = S * C ℓ⁻¹ := by
        simp_rw [mul_assoc, ← C_mul, ← Finset.mul_sum, ← map_sum]
        congr 2
        simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
        rw [hc, one_mul]
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      rw [h1, h2, sub_self]

  let ΦI : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)) :=
    Ideal.Quotient.lift (chartIncIdeal I t e) Φ.toRingHom fun a ha => hJ ha
  have hΦIS : ∀ s : MvPolynomial (Fin e × Fin n) F, ΦI (algebraMap _ (ChartInc I t e) s) = aeval (genSubst ξ c) s := by
    intro s
    show ΦI (Ideal.Quotient.mk _ (rename Sum.inr s)) = _
    exact hΦinr s
  have hΦIX : ∀ h, ΦI (chartX I t e h) = C (aeval (fun m => ξ m / ℓ) h) := by
    intro h
    show ΦI (Ideal.Quotient.mk _ (rename Sum.inl h)) = _
    exact hΦinl h
  exact ⟨ΦI, hΦIS, hΦIX, hdeh⟩
end GroundTheory.Heights₂.Heights.ChartResidueDegree
