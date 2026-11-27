-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSection_proof_30cab09885d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:05:47.199304+00:00
-- url     : https://prove2.me/submissions/28676445-773f-46af-8d20-09074bda77e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartMon_not_mem_3696957b3bbe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_add_25cf9563f061
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chartZ_natCast_d9230e02c1d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_chart_data_45e7364ee652
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_24bb01e3d3b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_exists_chartForm_family_ced0ca1166a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_X_none_21441bf27d48
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_isMultiHomog_chartMon_ffa9ade91345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_mem_projIdeal_iff_1da4cc5def22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_X_none_3cab59bf1f36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_X_some_d4cd627c91e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_projMap_chartMon_ef7312781bb0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_ne_zero_of_live_7f57050cfd7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_segreVec_pow_88ac63332cbb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_sum_truncCoord_one_d40575ce1942
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_tMon_add_4ee6ed9d9839
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineSectionProof_tMon_ne_zero_d64fe00ea655
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
open FlagLineSectionProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FlagLineSection
theorem _root_.solution : FlagLineSection.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy _ N E _ _ B w b hB M a φ hφ Φ _ _ t ht h0
  have hXn : ∀ l : Fin M, projMap F y w φ (truncCoord t 1) (X ⟨none, l⟩) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l (w ⟨0, h0⟩))) * X none := by
    intro l
    rw [projMap_X_none, sum_truncCoord_one t h0]
  have ht0 : t ⟨0, h0⟩ ≠ 0 := fun h => ht.transcendental ⟨0, h0⟩ (h ▸ isAlgebraic_zero)

  have hyne : ∀ k (i : ι k), (X ⟨k, i⟩ : MRing ι F) ∉ pointIdeal F y → y ⟨k, i⟩ ≠ 0 := by
    intro k i hX h
    apply hX
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h]
  choose c0 hc0 using hy.relevant
  have live0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => hyne k _ (hc0 k)
  have hs0 := segreVec_ne_zero_of_live live0
  obtain ⟨hξ0, v0, -, hsum0⟩ := chart_data y B w b hB a φ hφ c0 hs0 h0
  obtain ⟨l0, hl0⟩ : ∃ l0, φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hsum0
  have hu0 : φ l0 (w ⟨0, h0⟩) ≠ 0 := left_ne_zero_of_mul hl0
  obtain ⟨n0, A0, hA0⟩ := exists_chartForm (M := M) y w φ (truncCoord t 1) c0 hs0 (hξ0 l0)
  obtain ⟨p, q, hpq⟩ : ∃ p q : K → ℕ, ∀ k, (p k : ℤ) - q k = -(b ⟨0, h0⟩ k - a k) - n0 :=
    ⟨fun k => (-(b ⟨0, h0⟩ k - a k) - n0).toNat, fun k => (-(-(b ⟨0, h0⟩ k - a k) - n0)).toNat,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hfval : projMap F y w φ (truncCoord t 1) (X ⟨none, l0⟩ * chartMon F M c0 q) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩))) * X none *
        (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ q k)) * tMon q) := by
    rw [map_mul, hXn, projMap_chartMon]
  have hgval : projMap F y w φ (truncCoord t 1) (A0 * chartMon F M c0 p) =
      C (algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0)) *
        tMon (fun _ => n0) * (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ p k)) * tMon p) := by
    rw [map_mul, hA0.2, projMap_chartMon]
  have hprod0 : ∀ r : K → ℕ, ∏ k, y ⟨k, c0 k⟩ ^ r k ≠ 0 :=
    fun r => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (live0 k)
  refine ⟨Pi.single none 1 + liftN q, liftN (fun _ => n0) + liftN p,
    X ⟨none, l0⟩ * chartMon F M c0 q, A0 * chartMon F M c0 p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isMultiHomog_X_none l0).mul (isMultiHomog_chartMon c0 q)
  · exact hA0.1.mul (isMultiHomog_chartMon c0 p)
  · rw [mem_projIdeal_iff, hfval]
    refine mul_ne_zero (mul_ne_zero ?_ (X_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero q))
    · rw [Ne, C_eq_zero]
      exact mul_ne_zero ht0 ((map_ne_zero _).mpr hu0)
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 q)
  · rw [mem_projIdeal_iff, hgval]
    refine mul_ne_zero (mul_ne_zero ?_ (tMon_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero p))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (mul_ne_zero hl0 (pow_ne_zero _ hs0))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 p)
  · funext o
    cases o with
    | none => simp [liftN, zetaDeg, liftDeg]
    | some k =>
      have := hpq k
      simp [liftN, zetaDeg, liftDeg]
      linarith
  · funext W
    show divCycle _ _ W - divCycle _ _ W = 0
    by_cases hW : W.IsPrime ∧ projIdeal F y w φ (truncCoord t 1) ≤ W ∧ IsRelevant W
    · obtain ⟨hWp, hPW, hWrel⟩ := hW
      choose cc hcc using fun k => hWrel (some k)
      let c : ∀ k, ι k := cc
      have hcW : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W := hcc
      obtain ⟨l1, hl1⟩ : ∃ l1 : Fin M, (X ⟨none, l1⟩ : MRing (bundleIdx ι M) F) ∉ W := hWrel none
      have live : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
        intro k h
        apply hcW k
        apply hPW
        rw [mem_projIdeal_iff, projMap_X_some, h, map_zero, C_0, zero_mul]
      have hs := segreVec_ne_zero_of_live live
      obtain ⟨hξ, vc, hvc, hsumc⟩ := chart_data y B w b hB a φ hφ c hs h0
      obtain ⟨nξ, hnξ⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hξ
      obtain ⟨nv, hnv⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hvc
      set m := nξ + nv with hm
      choose Ξ hΞ using hnξ m (by omega)
      choose V hV using hnv m (by omega)
      have htm : (tMon (fun _ : K => m + m) : MvPolynomial (Option K) Φ) =
          tMon (fun _ => m) * tMon (fun _ => m) := tMon_add (fun _ => m) (fun _ => m)
      have hR0 : ∑ l, V l * Ξ l - chartMon F M c (fun _ => m + m) ∈ projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_sum, projMap_chartMon, htm, sub_eq_zero]
        have e1 : ∀ l, projMap F y w φ (truncCoord t 1) (V l * Ξ l) =
            C (algebraMap Ω Φ (vc l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)))) *
              (C (algebraMap Ω Φ (segreVec y c ^ (m + m))) * (tMon (fun _ => m) * tMon (fun _ => m))) := by
          intro l
          rw [map_mul, (hV l).2, (hΞ l).2]
          simp only [map_mul, map_pow, pow_add]
          ring
        rw [Finset.sum_congr rfl (fun l _ => e1 l), ← Finset.sum_mul, ← map_sum, ← map_sum, hsumc,
          map_one, map_one, one_mul]
        simp [segreVec, Finset.prod_pow]
      have hS : chartMon F M c (fun _ => m + m) ∉ W := chartMon_not_mem hcW _
      obtain ⟨l2, hl2⟩ : ∃ l2, Ξ l2 ∉ W := by
        by_contra hcon
        push Not at hcon
        have hsumW : ∑ l, V l * Ξ l ∈ W := Ideal.sum_mem _ fun l _ => W.mul_mem_left _ (hcon l)
        apply hS
        have := W.sub_mem hsumW (hPW hR0)
        rwa [sub_sub_cancel] at this
      have hR1 : X ⟨none, l1⟩ * Ξ l2 - X ⟨none, l2⟩ * Ξ l1 ∈ projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul, map_mul, hXn, hXn, (hΞ l2).2, (hΞ l1).2, sub_eq_zero]
        simp only [map_mul]
        ring
      have h12 : X ⟨none, l1⟩ * Ξ l2 ∉ W := fun h => (hWp.mem_or_mem h).elim hl1 hl2
      have h21 : X ⟨none, l2⟩ * Ξ l1 ∉ W := fun h => h12 (by
        have := W.add_mem (hPW hR1) h
        rwa [sub_add_cancel] at this)
      have hx2 : (X ⟨none, l2⟩ : MRing (bundleIdx ι M) F) ∉ W := fun h => h21 (W.mul_mem_right _ h)
      obtain ⟨α, β, hαβ⟩ : ∃ α β : K → ℕ, ∀ k, (β k : ℤ) - α k = m + (b ⟨0, h0⟩ k - a k) :=
        ⟨fun k => (-(m + (b ⟨0, h0⟩ k - a k))).toNat, fun k => (m + (b ⟨0, h0⟩ k - a k)).toNat,
          fun k => Int.toNat_sub_toNat_neg _⟩
      have hne1 : Ξ l2 * chartMon F M c α ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hl2 (chartMon_not_mem hcW α)
      have hne2 : X ⟨none, l2⟩ * chartMon F M c β ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hx2 (chartMon_not_mem hcW β)
      have hT : (tMon (fun _ => m) * tMon α * tMon q : MvPolynomial (Option K) Φ) =
          tMon β * tMon (fun _ => n0) * tMon p := by
        rw [← tMon_add, ← tMon_add, ← tMon_add, ← tMon_add]
        congr 1
        funext k
        have h1 := hαβ k
        have h2 := hpq k
        simp only [Pi.add_apply]
        omega
      have hc1 : chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m * ∏ k, y ⟨k, c k⟩ ^ α k =
          ∏ k, y ⟨k, c k⟩ ^ β k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live, ← chartZ_add live]
        congr 1
        funext k
        have h1 := hαβ k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hc0 : chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0 * ∏ k, y ⟨k, c0 k⟩ ^ p k =
          ∏ k, y ⟨k, c0 k⟩ ^ q k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live0, ← chartZ_add live0]
        congr 1
        funext k
        have h2 := hpq k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hΩ : φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m *
            (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c0 k⟩ ^ q k) =
          φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
            (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
            (∏ k, y ⟨k, c0 k⟩ ^ p k) := by
        rw [← hc1, ← hc0]
        ring
      have hcross : (Ξ l2 * chartMon F M c α) * (X ⟨none, l0⟩ * chartMon F M c0 q) -
          (X ⟨none, l2⟩ * chartMon F M c β) * (A0 * chartMon F M c0 p) ∈
            projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2 * _),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩ * _), hfval, hgval,
          map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩), (hΞ l2).2, hXn, projMap_chartMon, projMap_chartMon, sub_eq_zero]
        calc _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) *
                segreVec y c ^ m * (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) *
                (∏ k, y ⟨k, c0 k⟩ ^ q k))) * X none * (tMon (fun _ => m) * tMon α * tMon q) := by
              simp only [map_mul]
              ring
          _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
                (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
                (∏ k, y ⟨k, c0 k⟩ ^ p k))) * X none * (tMon β * tMon (fun _ => n0) * tMon p) := by
              rw [hΩ, hT]
          _ = _ := by
              simp only [map_mul]
              ring
      rw [divCycle_eq_of_mul_sub_mem hne1 hne2 hcross, sub_self]
    · have hz : ∀ h, divCycle (projIdeal F y w φ (truncCoord t 1)) h W = 0 := by
        intro h
        by_contra hne
        exact hW (le_and_isRelevant_of_divCycle_ne_zero hne)
      rw [hz, hz, sub_self]
end FlagLineSection
end GroundTheory.Heights₂.Heights.NumbersDVR
