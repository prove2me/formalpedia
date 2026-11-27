-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_proof_94d6978acb6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:24.972909+00:00
-- url     : https://prove2.me/submissions/30e2de71-3859-429f-84b9-225cabae76f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_ker_toSub_0f000c74cea3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_chartX_map_2fbd012a6e92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_comap_algebraMap_map_5533eb7a3b9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_disjoint_iff_260247d60a12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_le_of_sup_le_ee37547a7a26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_ne_zero_of_mem_minimalPrimes_0d5be1cc02d3


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
open ChartMaxIdeals
namespace GroundTheory.Heights₂.Heights
namespace ChartMaxIdeals
theorem _root_.solution (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₆ : SpecFirstMemIncIdeal.Statement) (h₇ : ChartFinite.Statement) (h₈ : ChartIncDomain.Statement)
    (h₉ : ChartKernel.Statement) (hH : ChartHomogenise.Statement) (hD : ChartDehomog.Statement)
    (hC : ComponentOfIncIdeal.Statement) : ChartMaxIdeals.Statement := by
  intro F _ n e I f t u q p _ hI hf hu hq hp hqt
  classical
  have hdim := h₁ F n (e + 1) I f hI hf
  have hpt : specFirst f t ∉ p := by rw [hp, Ideal.mem_span_singleton]; exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf hpt
  have : Algebra.IsIntegral (Localization.AtPrime p) (ChartLoc I t e p) := Algebra.IsIntegral.of_finite _ _
  have hsupp : ∀ W, W ∈ (divCycle I u).support ↔
      W ∈ relComps (I ⊔ Ideal.span {linForm u}) ∧ localMult (I ⊔ Ideal.span {linForm u}) W ≠ 0 := by
    intro W
    rw [Finsupp.mem_support_iff, divCycle, fundCycle, Finsupp.onFinset_apply]
    split_ifs with h <;> simp [h]
  have htower : (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) =
      (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

  have key : ∀ W : Ideal (MvPolynomial (Fin n) F), IsProjPrime W → linForm t ∉ W → I ≤ W → incIdeal W e = p →
      (chartIdeal I t e p W).IsMaximal ∧
        (chartIdeal I t e p W).comap (algebraMap (ChartInc I t e) (ChartLoc I t e p)) = W.map (chartX I t e) ∧
        (W.map (chartX I t e)).comap (chartX I t e) = W ⊔ Ideal.span {linForm t - 1} := by
    intro W hW ht hIW hWp
    obtain ⟨hdom, hker⟩ := h₈ F n e W t hW ht
    have hk := h₉ F n e W t hW ht
    have hprime : (W.map (chartX I t e)).IsPrime := by
      rw [← ker_toSub hIW t]; exact RingHom.ker_isPrime _
    have hcS : (W.map (chartX I t e)).comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = p := by
      rw [comap_algebraMap_map hIW t, hk, hWp]
    have hdisj := (disjoint_iff (p := p) (W.map (chartX I t e))).mpr hcS.le
    have h𝔓 : (chartIdeal I t e p W).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hprime hdisj
    have hc𝔓 : (chartIdeal I t e p W).comap (algebraMap (ChartInc I t e) (ChartLoc I t e p)) =
        W.map (chartX I t e) :=
      IsLocalization.under_map_of_isPrime_disjoint _ _ hprime hdisj
    have hO : ((chartIdeal I t e p W).comap (algebraMap (Localization.AtPrime p) (ChartLoc I t e p))).comap
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) = p := by
      rw [Ideal.comap_comap, htower, ← Ideal.comap_comap, hc𝔓, hcS]
    have hmaxO : (chartIdeal I t e p W).comap (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rw [← IsLocalization.map_under p.primeCompl (Localization.AtPrime p)
        ((chartIdeal I t e p W).comap (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)))]
      change Ideal.map _ (Ideal.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) _) = _
      rw [hO, Localization.AtPrime.map_eq_maximalIdeal]
    refine ⟨Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Localization.AtPrime p) _ ?_, hc𝔓, ?_⟩
    · rw [hmaxO]; exact IsLocalRing.maximalIdeal.isMaximal _
    · rw [comap_chartX_map hIW t, hker]

  have hmem : ∀ W ∈ {W | W ∈ (divCycle I u).support ∧ Ideal.span {q} = incIdeal W e},
      IsProjPrime W ∧ linForm t ∉ W ∧ I ≤ W ∧ linForm u ∈ W ∧ incIdeal W e = p := by
    rintro W ⟨hWs, hWq⟩
    obtain ⟨hrel, -⟩ := (hsupp W).mp hWs
    obtain ⟨hWproj, -⟩ := h₂ F n e I W u hI hdim hu hrel
    have hJW : I ⊔ Ideal.span {linForm u} ≤ W := hrel.1.1.2
    have hIW : I ≤ W := le_sup_left.trans hJW
    have ht : linForm t ∉ W := by
      intro htW
      have := h₆ F n e I W f t hf hIW htW
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    exact ⟨hWproj, ht, hIW, hJW (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)), hWq.symm.trans hp.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨hWp, ht, hIW, huW, hinc⟩ := hmem W hW
    refine ⟨(key W hWp ht hIW hinc).1, ?_⟩
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ huW)
  · intro W₁ hW₁ W₂ hW₂ heq
    obtain ⟨hp₁, ht₁, hI₁, -, hinc₁⟩ := hmem W₁ hW₁
    obtain ⟨hp₂, ht₂, hI₂, -, hinc₂⟩ := hmem W₂ hW₂
    obtain ⟨-, hc₁, hx₁⟩ := key W₁ hp₁ ht₁ hI₁ hinc₁
    obtain ⟨-, hc₂, hx₂⟩ := key W₂ hp₂ ht₂ hI₂ hinc₂
    have h12 : W₁ ⊔ Ideal.span {linForm t - 1} = W₂ ⊔ Ideal.span {linForm t - 1} := by
      rw [← hx₁, ← hx₂, ← hc₁, ← hc₂]
      rw [heq]
    exact le_antisymm (le_of_sup_le hD hp₁.isHomog hp₂.isPrime hp₂.isHomog ht₂ h12.le)
      (le_of_sup_le hD hp₂.isHomog hp₁.isPrime hp₁.isHomog ht₁ h12.ge)
  · rintro 𝔓 ⟨hmax, hθ⟩
    have := hmax.isPrime
    set P := 𝔓.comap (algebraMap (ChartInc I t e) (ChartLoc I t e p)) with hPdef
    set Q := P.comap (chartX I t e) with hQdef
    have hzero : ∀ g ∈ I ⊔ Ideal.span {linForm t - 1}, chartX I t e g = 0 := fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
    have hLQ : linForm t - 1 ∈ Q := by
      show chartX I t e (linForm t - 1) ∈ P
      rw [hzero _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))]
      exact P.zero_mem
    have hIQ : I ≤ Q := fun g hg => by
      show chartX I t e g ∈ P
      rw [hzero g (Ideal.mem_sup_left hg)]
      exact P.zero_mem
    have huQ : linForm u ∈ Q := hθ
    obtain ⟨W, hWp, ht, hWQ, hWmax⟩ := hH F n Q t inferInstance hLQ
    have hJW : I ⊔ Ideal.span {linForm u} ≤ W :=
      hWmax _ (isHomogIdeal_sup_span_linForm hI.isHomog u)
        (sup_le hIQ (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact huQ))
    have hIW : I ≤ W := le_sup_left.trans hJW
    have hPW : W.map (chartX I t e) ≤ P := Ideal.map_le_iff_le_comap.mpr (le_sup_left.trans hWQ.le)
    have hPp : P.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) ≤ p := by
      intro s hs
      by_contra hsp
      have hunit : IsUnit (algebraMap (ChartInc I t e) (ChartLoc I t e p)
          (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) s)) :=
        IsLocalization.map_units (ChartLoc I t e p) (⟨_, s, hsp, rfl⟩ :
          Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl)
      exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hunit)
    have hincle : incIdeal W e ≤ Ideal.span {q} := by
      rw [← hp, ← h₉ F n e W t hWp ht, ← comap_algebraMap_map hIW t]
      exact (Ideal.comap_mono hPW).trans hPp
    obtain ⟨hrel, hinc⟩ := hC F n e I W u q hI hdim hu hWp hJW hq hincle
    refine ⟨W, ⟨(hsupp W).mpr ⟨hrel, localMult_ne_zero_of_mem_minimalPrimes hrel.1⟩, hinc.symm⟩, ?_⟩
    have hmaxW := (key W hWp ht hIW (hinc.trans hp.symm)).1
    have hle : chartIdeal I t e p W ≤ 𝔓 := by
      rw [chartIdeal, Ideal.map_le_iff_le_comap]
      exact hPW
    exact hmaxW.eq_of_le hmax.ne_top hle
end ChartMaxIdeals
end GroundTheory.Heights₂.Heights
