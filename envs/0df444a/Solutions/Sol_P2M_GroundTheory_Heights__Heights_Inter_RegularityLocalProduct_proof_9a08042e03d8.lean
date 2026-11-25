-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalProduct_proof_9a08042e03d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:41.802051+00:00
-- url     : https://prove2.me/submissions/e03f5b39-f47d-4921-b0d7-482d75ffe8e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_mul_59a410201a68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_37194c2134d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_mul_750ad0c2d9bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_frac_mem_locRing_a3c1c87b7867
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_frac_unit_locRing_ee3966325a70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityLocalProduct
theorem _root_.solution (hN : RegularityFunctionFieldNumber.Statement) (hR : RegularityFormula.Statement)
    (hD : RegularityDenominator.Statement) (hC : RegularityDivisorSupportClosed.Statement) (hF : RegularityLocalFinite.Statement) :
    RegularityLocalProduct.Statement := by
  classical
  intro K _ ι _ P f g a x t yf yg hP hf hg hfP hgP hx ht
  have : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hcW⟩ := hD K ι P x hP
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hx0 : x ≠ 0 := fun h => hφ f hfP (by rw [← hx, h]; simp)
  have hb0 : x * c ≠ 0 := mul_ne_zero hx0 hc0
  have hxc : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) = x * c := rfl
  have hmem : ∀ {s : MRing ι} {W}, IsMultiHomog s a → s ∉ P → IsClosedPt W → P ≤ W → (W ∈ divSupp P s ↔ s ∈ W) :=
    fun hs hsP hWc hPW => (hC K ι P _ a _ hP hs hsP).trans ⟨fun h => h.2.2, fun h => ⟨hWc, hPW, h⟩⟩
  have key : ∀ W, IsClosedPt W → P ≤ W →
      (if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P)))) -
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P)))) := by
    intro W hWc hPW
    obtain ⟨hcS, hbS⟩ := hcW W hWc hPW
    by_cases hU : W ∈ divSupp P f ∪ divSupp P g
    · obtain ⟨htW, htn, hyf, hyg⟩ := ht W hU
      have hyfS := frac_mem_locRing hPW hf htW htn hyf
      have hygS := frac_mem_locRing hPW hg htW htn hyg
      have hyf0 : yf W ≠ 0 := fun h => hφ f hfP (by rw [← hyf, h, zero_mul])
      have hyg0 : yg W ≠ 0 := fun h => hφ g hgP (by rw [← hyg, h, zero_mul])
      have hrel : yf W = x * yg W :=
        mul_right_cancel₀ (hφ _ fun h => htn (hPW h)) (by rw [hyf, mul_assoc, hyg, hx])
      obtain ⟨s, hs, hsP, hWs⟩ : ∃ s, IsMultiHomog s a ∧ s ∉ P ∧ W ∈ divSupp P s := by
        rcases hU with h | h
        exacts [⟨f, hf, hfP, h⟩, ⟨g, hg, hgP, h⟩]
      have fin : ∀ y, y ∈ locRing P W → y ≠ 0 → Finite (locRing P W ⧸ locIdeal P W y) :=
        fun y hy hy0 => hF K ι P s a W y hP hs hsP hWs hy hy0
      have hc0' : (c : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hc0 (Subtype.ext h)
      have hb0' : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hb0 (Subtype.ext h)
      have e : yf W * c = ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) * yg W := by
        rw [hrel, hxc]; ring
      have hm := log_card_locIdeal_mul hyfS hcS hyf0 (fin _ hyfS hyf0) (fin _ hcS hc0')
      have hm' := log_card_locIdeal_mul hbS hygS hb0' (fin _ hbS hb0') (fin _ hygS hyg0)
      rw [e] at hm
      by_cases h1 : W ∈ divSupp P f <;> by_cases h2 : W ∈ divSupp P g
      · rw [if_pos h1, if_pos h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hg htW (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) htn hyg
        have := log_card_locIdeal_unit hygS hz hz1
        rw [if_pos h1, if_neg h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hf htW (fun h => h1 ((hmem hf hfP hWc hPW).mpr h)) htn hyf
        have := log_card_locIdeal_unit hyfS hz hz1
        rw [if_neg h1, if_pos h2]; linarith
      · exact absurd hU (by simp [h1, h2])
    · have h1 : W ∉ divSupp P f := fun h => hU (Or.inl h)
      have h2 : W ∉ divSupp P g := fun h => hU (Or.inr h)
      obtain ⟨hxS, z, hz, hz1⟩ := frac_unit_locRing hPW hf hg (fun h => h1 ((hmem hf hfP hWc hPW).mpr h))
        (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) hx
      rw [if_neg h1, if_neg h2, hxc, log_card_locIdeal_unit_mul hxS hz hz1 hcS]
      ring
  obtain ⟨hbfin, hbsum⟩ := hR K ι P (x * c) hP hb0 (fun W h1 h2 => (hcW W h1 h2).2)
  obtain ⟨hcfin, hcsum⟩ := hR K ι P c hP hc0 (fun W h1 h2 => (hcW W h1 h2).1)
  have eq1 : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) =
        ∑ᶠ W, (if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0) := by
    intro s y
    rw [finsum_mem_def]
    rfl
  have fsA : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      (Function.support fun W =>
        if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0).Finite :=
    fun s y => (divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h)
  have fsB : ∀ z : FractionRing (MRing ι ⧸ P),
      {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W z) ≠ 1}.Finite →
      (Function.support ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
        fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W z)))).Finite :=
    fun z hz => hz.subset fun W hW => by
      rw [Function.mem_support] at hW
      by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
      · rw [Set.indicator_of_mem hWC] at hW
        exact ⟨hWC.1, hWC.2, fun h1 => hW (by rw [h1]; simp)⟩
      · rw [Set.indicator_of_notMem hWC] at hW
        exact absurd rfl hW
  obtain ⟨hFld, hNF⟩ := hN K ι P hP
  let _ := hFld.toField
  have hσ : ∀ y : funField P, y ≠ 0 → ∀ σ : funField P →+* ℂ, σ y ≠ 0 := fun y hy σ h => by
    obtain ⟨z, hz⟩ := hFld.mul_inv_cancel hy
    have := congrArg σ hz
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc _ = ∑ᶠ W, ((if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0)) := by
        rw [eq1 f yf, eq1 g yg, finsum_sub_distrib (fsA f yf) (fsA g yg)]
    _ = ∑ᶠ W, ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸
              locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P))))) W -
          {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P))))) W) := by
        refine finsum_congr fun W => ?_
        by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
        · rw [Set.indicator_of_mem hWC, Set.indicator_of_mem hWC]
          exact key W hWC.1 hWC.2
        · rw [Set.indicator_of_notMem hWC, Set.indicator_of_notMem hWC,
            if_neg fun h => hWC ⟨((hC K ι P f a W hP hf hfP).mp h).1, ((hC K ι P f a W hP hf hfP).mp h).2.1⟩,
            if_neg fun h => hWC ⟨((hC K ι P g a W hP hg hgP).mp h).1, ((hC K ι P g a W hP hg hgP).mp h).2.1⟩]
    _ = ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ (x * c)‖ - ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ c‖ := by
        rw [finsum_sub_distrib (fsB _ hbfin) (fsB _ hcfin), ← finsum_mem_def, ← finsum_mem_def, hbsum, hcsum]
    _ = _ := by
        rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
        refine finsum_congr fun σ => ?_
        rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hσ x hx0 σ)) (norm_ne_zero_iff.mpr (hσ c hc0 σ))]
        ring
end RegularityLocalProduct
end GroundTheory.Heights₂.Heights.Inter
