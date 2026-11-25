-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLocalOrder_proof_c02df12483c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:11.616994+00:00
-- url     : https://prove2.me/submissions/325c1bfb-b59c-4d3c-a960-e0b826978e0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartIncIdeal_eq_sup_897b6b348edb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_iff_656fe0f0fba5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_of_sup_ker_ac2f8cb6366c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
private theorem linForm_isHomogeneous_one {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j
end GroundTheory.Heights₂.Heights
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace ChartLocalOrder
theorem _root_.solution (h₂ : ChartIncDomain.Statement) (h₃ : ChartKernel.Statement)
    (h₄ : ConeDimOfChowForm.Statement) (h₅ : ConeDimComponent.Statement)
    (h₆ : ChowFormExists.Statement) (h₇ : IncIdealPrime.Statement) (h₈ : ChartIncOrd.Statement)
    (h₉ : DehomogOrd.Statement) (h₁₀ : LocalMultOrd.Statement) : ChartLocalOrder.Statement := by
  intro F _ n e I W f t u q p _ hI hf hu hq hp _ hW hqW htW

  obtain ⟨hWp, hWd⟩ := h₅ F n e I W u hI (h₄ F n (e + 1) I f hI hf) hu hW
  have := hWp.isPrime
  have hIW : I ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨g, hg⟩ := h₆ F n e W hWp hWd
  rw [isChowForm_iff] at hg
  have hinc : incIdeal W e = p := by
    have hpr := h₇ F n e W hWp.isPrime hWp.isRelevant
    have hqg : q ∈ Ideal.span {g} := hg.2 ▸ hqW
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hqg
    have hgu : ¬ IsUnit g := fun h => hpr.ne_top (by rw [hg.2, Ideal.span_singleton_eq_top.mpr h])
    have hcu : IsUnit c := (hq.irreducible.isUnit_or_isUnit (by rw [← hc, mul_comm])).resolve_left hgu
    rw [hp, hg.2, Ideal.span_singleton_eq_span_singleton]
    exact ⟨hcu.unit, by rw [IsUnit.unit_spec, mul_comm, hc]⟩

  obtain ⟨hdomW, hkerXW⟩ := h₂ F n e W t hWp htW
  have hkerW := h₃ F n e W t hWp htW
  have hcW := chartIncIdeal_eq_sup t e hIW
  have hcWp : (chartIncIdeal W t e).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdomW
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk _
  have hkπ : RingHom.ker π = chartIncIdeal I t e := Ideal.mk_ker
  have hQ : W.map (chartX I t e) = (W.map (rename Sum.inl)).map π := by
    change _ = Ideal.map π (Ideal.map (rename Sum.inl).toRingHom _)
    rw [Ideal.map_map]; rfl
  have hmem : ∀ a, π a ∈ W.map (chartX I t e) ↔ a ∈ chartIncIdeal W t e := fun a => by
    have hkb : Ideal.comap π (⊥ : Ideal (ChartInc I t e)) = chartIncIdeal I t e := hkπ
    have hcm : Ideal.comap π ((W.map (rename Sum.inl)).map π) =
        W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by
      rw [← hkb]; exact Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective _
    rw [← hcW, ← hQ] at hcm
    exact SetLike.ext_iff.mp hcm a
  have h𝔔 : (W.map (chartX I t e)).IsPrime := by
    rw [hQ]
    exact isPrime_map_of_sup_ker π Ideal.Quotient.mk_surjective _ (by rw [hkπ, ← hcW]; exact hcWp)
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl : Submonoid _) :
      Set (ChartInc I t e)) (W.map (chartX I t e)) := by
    rw [Set.disjoint_left]
    intro y hy hyQ
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    have h1 : π (rename Sum.inr s) ∈ W.map (chartX I t e) := hyQ
    have h0 : algebraMap _ (ChartInc W t e) s = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem _).mp h1)
    have : s ∈ p := by rw [← hinc, ← hkerW]; exact h0
    exact hs this

  have hP : (chartIdeal I t e p W).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ (ChartLoc I t e p) _ h𝔔 hdisj
  refine ⟨hP, ?_⟩
  have hWI : (W.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIW)
  have hWQ : (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime := by
    have := hdomW
    have hpr : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := hkerXW ▸ RingHom.ker_isPrime _
    exact isPrime_map_of_sup_ker _ Ideal.Quotient.mk_surjective _
      (by rw [Ideal.mk_ker, ← sup_assoc, sup_eq_left.mpr hIW]; exact hpr)
  calc _ = Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
          (algebraMap (ChartInc I t e) _ (chartX I t e (linForm u))) :=
        ord_atPrime_map_localization (hP' := hP) _ _ hdisj _
    _ = Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
          (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) (linForm u))) :=
        h₈ F n e I W t (linForm u)
    _ = Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I (linForm u))) :=
        (h₉ F n I W t hI.isHomog hWp.isHomog hIW htW (linForm u) 1 (linForm_isHomogeneous_one u)).symm
    _ = _ := (h₁₀ (MvPolynomial (Fin n) F) I W (linForm u) hW.1).symm
end ChartLocalOrder
end GroundTheory.Heights₂.Heights
