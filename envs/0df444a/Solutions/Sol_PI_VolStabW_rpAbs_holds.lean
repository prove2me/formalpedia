-- Prove2me | solution 1 for PI.VolStabW.rpAbs_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:07.050254+00:00
-- url     : https://prove2.me/submissions/1640feb2-85af-425c-8e0b-3675a8f419f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_KapIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RpAbsHolds
import Theorems.Thm_PI_VolStabW_RPA_hasProd_ind
import Theorems.Thm_PI_VolStabW_RPA_kap_ae
import Theorems.Thm_PI_VolStabW_RPA_kap_eval_null
import Theorems.Thm_PI_VolStabW_RPA_kap_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Filter Finset PI.VolStabW.RPA
open scoped NNReal ENNReal
namespace PI.VolStabW
theorem _root_.solution : RPAbs := by
  intro ι _ W _ m _ L hLm hfin hT
  classical
  have hT' : TailH m L := hT
  refine ⟨Measure.sum (kap m L), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    have := kap_ae (m := m) (L := L) hLm S
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx => ?_) this
    intro hgood
    apply hx
    rw [Filter.eventually_cofinite]
    refine (S.finite_toSet).subset (fun i hi => ?_)
    by_contra hiS
    exact hi ((hgood i).2 hiS)
  · intro i C hC hC0
    rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    refine kap_eval_null (m := m) (L := L) (S := S) (A := Cᶜ) hC.compl ?_
    unfold mu
    split_ifs <;> exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hC0.le)
  · intro f hf hcof
    have hfin0 := Filter.eventually_cofinite.1 hcof
    set S0 := hfin0.toFinset with hS0def
    have hS0 : ∀ i, i ∉ S0 → f i = (L i).indicator 1 := fun i hi => by
      by_contra h; exact hi (hfin0.mem_toFinset.2 h)
    set G : (∀ i, W i) → ℂ := fun x => ∏ i ∈ S0, f i (x i) with hG
    have hae : ∀ S : Finset ι, (fun x => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => if S ⊆ S0 then G x else 0 := by
      intro S
      filter_upwards [kap_ae (m := m) (L := L) hLm S] with x hx
      have hsupp : Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ S0) := by
        intro i hi
        by_contra hn
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
        apply hi
        simp only [hS0 i hn.2, Set.indicator_of_mem ((hx i).2 hn.1), Pi.one_apply]
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
      by_cases hsub : S ⊆ S0
      · rw [if_pos hsub, Finset.union_eq_right.2 hsub]
      · rw [if_neg hsub]
        obtain ⟨j, hjS, hj0⟩ := Finset.not_subset.1 hsub
        refine Finset.prod_eq_zero (Finset.mem_union_left _ hjS) ?_
        simp [hS0 j hj0, (hx j).1 hjS]
    have hK : ∀ S ⊆ S0, Integrable G (kap m L S) ∧
        ∫ x, G x ∂kap m L S = (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) :=
      fun S hS => kap_integral hfin hT' hS f hf
    have hIntS : ∀ S, Integrable (fun x => ∏ᶠ i, f i (x i)) (kap m L S) := by
      intro S
      refine Integrable.congr ?_ (hae S).symm
      by_cases hs : S ⊆ S0
      · simp only [hs, if_true]; exact (hK S hs).1
      · simp only [hs, if_false]; exact integrable_zero _ _ _
    have hzero : ∀ S, S ∉ S0.powerset → ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S = 0 ∧
        ∫ x, ‖∏ᶠ i, f i (x i)‖ ∂kap m L S = 0 := by
      intro S hS
      have hs : ¬ S ⊆ S0 := fun h => hS (Finset.mem_powerset.2 h)
      refine ⟨?_, ?_⟩
      · rw [integral_congr_ae (hae S)]; simp [hs]
      · refine (integral_congr_ae ((hae S).fun_comp norm)).trans ?_
        simp [hs, Function.comp_def]
    have hint : Integrable (fun x => ∏ᶠ i, f i (x i)) (Measure.sum (kap m L)) :=
      integrable_sum_measure hIntS (summable_of_ne_finset_zero (s := S0.powerset)
        (fun S hS => (hzero S hS).2))
    refine ⟨hint, ?_⟩
    rw [integral_sum_measure hint, tsum_eq_sum (s := S0.powerset) (fun S hS => (hzero S hS).1)]
    have hsumS : ∑ S ∈ S0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        ∑ S ∈ S0.powerset, (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [integral_congr_ae (hae S)]
      simp only [hs, if_true]
      exact (hK S hs).2
    rw [hsumS, ← Finset.sum_mul]
    have hsplit : ∀ i, ∫ w, f i w ∂(m i) =
        (∫ w, f i w ∂(m i).restrict (L i)ᶜ) + ∫ w, f i w ∂(m i).restrict (L i) := fun i => by
      rw [add_comm]; exact (integral_add_compl (hLm i) (hf i)).symm
    have hprodadd : ∑ S ∈ S0.powerset, ∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i) =
        ∏ i ∈ S0, ∫ w, f i w ∂(m i) := by
      rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_add]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [← Finset.prod_sdiff hs, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_pos hi]
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [hprodadd]
    have h1 : HasProd (fun i => (((({i | i ∉ S0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        (((tl m L S0 : ℝ≥0) : ℝ) : ℂ) := by
      have := (hasProd_ind hT' S0).map
        (((Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom).comp (NNReal.toRealHom.toMonoidHom))
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
      exact this
    have h2 : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
        (∏ i ∈ S0, ∫ w, f i w ∂(m i)) := by
      have : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
          (∏ i ∈ S0, (if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)) :=
        hasProd_prod_of_ne_finset_one (fun b hb => if_neg hb)
      convert this using 1
      exact (Finset.prod_congr rfl (fun i hi => if_pos hi)).symm
    have h3 := h2.mul h1
    convert h3 using 1
    funext i
    by_cases hi : i ∈ S0
    · simp [hi]
    · have hmem : i ∈ ({i | i ∉ S0} : Set ι) := hi
      rw [if_neg hi, one_mul, Set.mulIndicator_of_mem hmem, hS0 i hi,
        integral_indicator (hLm i)]
      simp [am, Measure.real]
      exact (ENNReal.coe_toNNReal_eq_toReal _).symm
end PI.VolStabW
