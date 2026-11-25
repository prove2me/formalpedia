-- Prove2me | solution 1 for QPK.siegel_measure_definition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:43.967331+00:00
-- url     : https://prove2.me/submissions/e682ddc8-997e-4fce-a577-f9c726440af7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_SiegelMeasureDefinition
import Theorems.Thm_QPK_map_inv_eq_self
import Theorems.Thm_QPK_map_mul_right_eq_self
import Theorems.Thm_QPK_map_mulSwap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise
open QPK
namespace QPK
theorem _root_.solution : SMeas := by
  intro G _ _ _ _ _ _ _ _ N H hNc hHc hN hH hnorm hU μN μH hμN hfN hpN hμH hfH hpH hconj
  have : SigmaFinite μN := hμN.1
  have : SigmaFinite μH := hμH.1
  have : IsFiniteMeasureOnCompacts μN := hfN
  have : IsFiniteMeasureOnCompacts μH := hfH
  have hHcl : IsClosed H := hHc.isClosed
  have hRH : ∀ s ∈ H, μH.map (fun x => x * s) = μH := fun s hs =>
    map_mul_right_eq_self H hHcl hH μH hμH hHc.measure_lt_top.ne s hs
  have hRN : ∀ s ∈ N, μN.map (fun x => x * s) = μN :=
    hU μN hμN.1 hμN.2.1 hμN.2.2.1 hμN.2.2.2
  have hIH := map_inv_eq_self H hHcl hH μH hμH hRH
  have hIN := map_inv_eq_self N hNc hN μN hμN hRN
  have hm' : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hM : mulMap μN μH = (μH.prod μN).map (fun p : G × G => p.2 * p.1) := by
    have hm1 : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd
    unfold mulMap
    rw [← Measure.prod_swap (μ := μH) (ν := μN), Measure.map_map hm1 measurable_swap]
    rfl
  have hHae : ∀ᵐ k ∂μH, k ∈ H := by
    rw [ae_iff]
    exact hμH.2.2.1
  have hNae : ∀ᵐ n ∂μN, n ∈ N := by
    rw [ae_iff]
    exact hμN.2.2.1
  have hae : ∀ᵐ p ∂(μH.prod μN), p ∈ H ×ˢ N :=
    ((Measure.quasiMeasurePreserving_fst.ae hHae).and
      (Measure.quasiMeasurePreserving_snd.ae hNae)).mono fun p hp => Set.mem_prod.2 hp
  have hnull : (μH.prod μN) (H ×ˢ N)ᶜ = 0 := by
    rw [ae_iff] at hae
    exact hae
  have hSeq : prodSet N H = N * H := by
    ext x
    simp only [prodSet, Set.mem_mul, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm, h, hh, rfl⟩
      exact ⟨m, hm, h, hh, rfl⟩
    · rintro ⟨m, hm, h, hh, rfl⟩
      exact ⟨m, hm, h, hh, rfl⟩
  have hScl : IsClosed (prodSet N H) := by
    rw [hSeq]
    exact hNc.mul_right_of_isCompact hHc

  have hfin : IsFiniteMeasureOnCompacts (mulMap μN μH) := by
    refine ⟨fun L hL => ?_⟩
    rw [hM, Measure.map_apply hm' hL.isClosed.measurableSet]
    have hC : IsCompact (L * H⁻¹) := hL.mul hHc.inv
    have hsub : (fun p : G × G => p.2 * p.1) ⁻¹' L ⊆ (H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ := by
      intro p hp
      by_cases hp2 : p ∈ H ×ˢ N
      · left
        refine ⟨hp2.1, ?_⟩
        exact Set.mem_mul.2 ⟨p.2 * p.1, hp, p.1⁻¹, Set.inv_mem_inv.2 hp2.1, by group⟩
      · right
        exact hp2
    calc (μH.prod μN) ((fun p : G × G => p.2 * p.1) ⁻¹' L)
        ≤ (μH.prod μN) ((H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ) := measure_mono hsub
      _ ≤ (μH.prod μN) (H ×ˢ (L * H⁻¹)) + (μH.prod μN) (H ×ˢ N)ᶜ := measure_union_le _ _
      _ = μH H * μN (L * H⁻¹) := by rw [hnull, add_zero, Measure.prod_prod]
      _ < ⊤ := ENNReal.mul_lt_top hHc.measure_lt_top hC.measure_lt_top

  have hpos : PosOn (mulMap μN μH) (prodSet N H) := by
    rintro U hUo ⟨x, hxU, a, ha, b, hb, hx⟩
    rw [hM, Measure.map_apply hm' hUo.measurableSet]
    have hopen : IsOpen ((fun p : G × G => p.2 * p.1) ⁻¹' U) :=
      hUo.preimage (continuous_snd.mul continuous_fst)
    have hmem : (b, a) ∈ (fun p : G × G => p.2 * p.1) ⁻¹' U := by
      show a * b ∈ U
      rw [← hx]
      exact hxU
    obtain ⟨V₁, V₂, hV₁, hV₂, hb1, ha2, hsub⟩ := isOpen_prod_iff.1 hopen b a hmem
    intro h0
    have h1 : (μH.prod μN) (V₁ ×ˢ V₂) = 0 := measure_mono_null hsub h0
    rw [Measure.prod_prod] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact hpH V₁ hV₁ ⟨b, hb1, hb⟩ h
    · exact hpN V₂ hV₂ ⟨a, ha2, ha⟩ h
  have hne : mulMap μN μH ≠ 0 := by
    have h1 := hpos univ isOpen_univ ⟨1, trivial, 1, hN.1, 1, hH.1, (mul_one 1).symm⟩
    intro h
    rw [h] at h1
    exact h1 rfl
  have hconc : mulMap μN μH (prodSet N H)ᶜ = 0 := by
    rw [hM, Measure.map_apply hm' hScl.measurableSet.compl]
    refine measure_mono_null ?_ hnull
    intro p hp
    simp only [mem_preimage, mem_compl_iff] at hp
    rw [mem_compl_iff]
    rintro ⟨h1, h2⟩
    exact hp ⟨p.2, h2, p.1, h1, rfl⟩

  have hleft : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => s * x) = mulMap μN μH := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have hg : MeasurePreserving (fun p : G × G => (b * p.1, a * (b * p.2 * b⁻¹)))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => b * x)
        (g := fun _ n => a * (b * n * b⁻¹)) ⟨measurable_const_mul b, hμH.2.2.2 b hb⟩
        (((measurable_snd.const_mul b).mul_const b⁻¹).const_mul a) (ae_of_all _ fun _ => ?_)
      have hcj : Measurable (fun x : G => b * x * b⁻¹) := (measurable_const_mul b).mul_const b⁻¹
      have e : μN.map (fun n => a * (b * n * b⁻¹)) =
          (μN.map (fun x => b * x * b⁻¹)).map (fun x => a * x) := by
        rw [Measure.map_map (measurable_const_mul a) hcj]
        rfl
      show μN.map (fun n => a * (b * n * b⁻¹)) = μN
      rw [e, hconj b hb, hμN.2.2.2 a ha]
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ (measurable_const_mul _) (fun p => by simp only; group)

  have hright : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => x * s) = mulMap μN μH := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have hg : MeasurePreserving (fun p : G × G => (p.1 * b, p.2 * (p.1 * a * p.1⁻¹)))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => x * b)
        (g := fun k n => n * (k * a * k⁻¹)) ⟨measurable_mul_const b, hRH b hb⟩
        (measurable_snd.mul ((measurable_fst.mul_const a).mul measurable_fst.inv))
        (hHae.mono fun k hk => ?_)
      exact hRN _ (hnorm k hk a ha)
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ (measurable_mul_const _) (fun p => by simp only; group)

  have hinv : (mulMap μN μH).map (fun x => x⁻¹) = mulMap μN μH := by
    have hg : MeasurePreserving (fun p : G × G => (p.1⁻¹, p.1⁻¹ * p.2⁻¹ * p.1))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => x⁻¹)
        (g := fun k n => k⁻¹ * n⁻¹ * k) ⟨measurable_inv, hIH⟩
        ((measurable_fst.inv.mul measurable_snd.inv).mul measurable_fst)
        (hHae.mono fun k hk => ?_)
      have hcj : Measurable (fun x : G => k⁻¹ * x * k⁻¹⁻¹) :=
        (measurable_const_mul _).mul_const _
      have e : μN.map (fun n => k⁻¹ * n⁻¹ * k) =
          (μN.map (fun x => x⁻¹)).map (fun x => k⁻¹ * x * k⁻¹⁻¹) := by
        rw [Measure.map_map hcj measurable_inv]
        congr 1
        funext x
        simp
      show μN.map (fun n => k⁻¹ * n⁻¹ * k) = μN
      rw [e, hIN, hconj _ (hH.2.2 k hk)]
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ measurable_inv (fun p => by simp only; group)
  have := hfin
  exact ⟨⟨inferInstance, hne, hconc, hleft⟩, hfin, hpos, hright, hinv⟩
end QPK
