-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_EffectiveHS_EffectiveHilbertSamuelJetSecond_proof_3834072d8eb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:31.873979+00:00
-- url     : https://prove2.me/submissions/1bb4e33d-b77d-4c22-ab9b-99a8b2ded519

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_AnalyticAtOfHoloOn
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_sPow_eq_monoSec_dddd22f75433


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open ReciprocityTheory.AnForm.M
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
variable {D : ℕ} {U : Type} [TopologicalSpace U]
namespace GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
namespace _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond
theorem _root_.solution
    (hJ : JetOfMonomialSum.Statement) : IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.Statement := by
  classical
  intro D hD X Y _ _ _ _ _ _ A d s hGood hRes hUnit a ha g
  obtain ⟨c₀, hc₀⟩ := hUnit
  set j := d.T - a with hj
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / d.W.sec c₀ (chartIdx A y) y ^ j)
  let s' : Fin D → Fin A.n → X → ℂ := fun i => d.W.sec (s i)
  let hh : (Fin D → ℕ) → Fin A.n → X → ℂ := fun α =>
    IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.wProd fun _ : Fin j => c₀) (m α)
  have hF : (∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a,
      IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α)) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [TranslateEq.sPow_eq_monoSec]
    rfl
  refine ⟨∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α),
    Submodule.sum_mem _ fun α hα => Submodule.mem_sup_left (Submodule.subset_span
      ⟨j, α, fun _ => c₀, m α, hmV α, ?_, ?_, rfl⟩), ?_⟩
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; omega
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; exact ha
  have hsec : ∀ c' : Fin d.W.n → ℂ,
      d.W.sec c' ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace d.L 1 := fun c' =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (d.W.mem k)
  have pt : ∀ x ∈ d.zeroU s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) = 0) ∧
      iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) =
        ∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, (g α x * d.sJac s (chartIdx A x) x) •
          iteratedFDeriv ℂ a (fun z => ∏ i, d.sLoc s (chartIdx A x) z i ^ α i)
            (A.chart (chartIdx A x) x) := by
    intro x hx
    set c := chartIdx A x with hc
    have hxc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
    have au : ∀ i, AnalyticAt ℂ (s' i c ∘ (A.chart c).symm) (A.chart c x) := fun i =>
      analyticAt_of_holoOn A ((hsec (s i)).1 c) hxc
    have aw : AnalyticAt ℂ (d.W.sec c₀ c ∘ (A.chart c).symm) (A.chart c x) :=
      analyticAt_of_holoOn A ((hsec c₀).1 c) hxc
    have hhc : ∀ α, hh α c ∘ (A.chart c).symm = fun z =>
        (d.W.sec c₀ c ∘ (A.chart c).symm) z ^ j * (m α c ∘ (A.chart c).symm) z := by
      intro α
      funext z
      simp [hh, IndefiniteRowSideFullHecke.EffectiveHS.secMul, IndefiniteRowSideFullHecke.EffectiveHS.FSData.wProd]
    have ah : ∀ α, AnalyticAt ℂ (hh α c ∘ (A.chart c).symm) (A.chart c x) := by
      intro α
      rw [hhc α]
      exact (aw.pow j).mul
        (analyticAt_of_holoOn A ((TranslateEq.space_le_topForms d 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (s' i c ∘ (A.chart c).symm) (A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, h2, -⟩ := hJ D D (fun i => s' i c ∘ (A.chart c).symm)
      (fun α => hh α c ∘ (A.chart c).symm) _ a au hz ah
    rw [chart_sum_eq A s' a hh c]
    refine ⟨h1, ?_⟩
    rw [h2]
    have hJ0 : d.sJac s c x ≠ 0 := hGood.etale x hx
    refine Finset.sum_congr rfl fun α _ => ?_
    have hr := hm α x hx
    have hw0 : d.W.sec c₀ c x ≠ 0 := hc₀ x hx
    simp only [IndefiniteRowSideFullHecke.EffectiveHS.FSData.res] at hr
    rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
    have hcoef : (hh α c ∘ (A.chart c).symm) (A.chart c x) = g α x * d.sJac s c x := by
      rw [hhc α]
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]
      linear_combination hr
    rw [hcoef]
    rfl
  rw [hF]
  exact ⟨fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩
end _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond
end GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
