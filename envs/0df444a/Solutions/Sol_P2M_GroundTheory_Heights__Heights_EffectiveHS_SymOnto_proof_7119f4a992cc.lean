-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_SymOnto_proof_7119f4a992cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:54.146794+00:00
-- url     : https://prove2.me/submissions/a447e876-9373-4945-8618-6eb7e533a610

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_AnalyticAtOfHoloOn
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_chart_sum_eq_8fb30277a532
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_analyticAt_of_holoOn_c7b3bffc3f2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_exists_unit_dd50c86e45ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c


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
namespace _root_.GroundTheory.Heights₂.Heights.EffectiveHS.SymOnto
theorem _root_.solution
    (hJ : JetOfMonomialSum.Statement) : SymOnto.Statement := by
  classical
  intro D T X Z Y hD hT hRes a ha g
  obtain ⟨c₀, hc₀⟩ := exists_unit X.A X.e X.gen Z.finite
  set w : Fin X.A.n → X.U → ℂ := lin X.e c₀ with hw
  set j := T - a with hj
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ i, α i = a := fun α hα =>
    Finset.Nat.mem_antidiagonalTuple.1 hα
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / w (chartIdx X.A y) y ^ j)
  have hwj : w ^ j = ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • ∏ l, X.e (ι l) := by
    rw [← Fin.prod_const j w, hw, lin, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    funext k x
    simp [Finset.prod_apply, Finset.prod_mul_distrib]
  have pt : ∀ x ∈ zeroSet X.A Z.s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
        (X.A.chart (chartIdx X.A x) x) = 0) ∧
      ∀ v : Fin D → ℂ, iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
          (X.A.chart (chartIdx X.A x) x) (fun _ => v) / (a.factorial : ℂ) =
        sJac X.A Z.s (chartIdx X.A x) x * ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
          (∏ i, (sJacMap X.A Z.s (chartIdx X.A x) x v i) ^ α i) * g α x := by
    intro x hx
    set c := chartIdx X.A x with hc
    have hxc : x ∈ (X.A.chart c).source := Classical.choose_spec (X.A.cover x)
    have hlin : ∀ c' : Fin X.N → ℂ, lin X.e c' ∈ X.L.sections 1 := fun c' =>
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)
    have au : ∀ i, AnalyticAt ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) := fun i =>
      analyticAt_of_holoOn X.A ((hlin (Z.c i)).1 c) hxc
    have aw : AnalyticAt ℂ (w c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      analyticAt_of_holoOn X.A ((hlin c₀).1 c) hxc
    have ah : ∀ α, AnalyticAt ℂ ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      fun α => (aw.pow j).mul (analyticAt_of_holoOn X.A ((Y.V_le 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, -, h3⟩ := hJ D D (fun i => Z.s i c ∘ (X.A.chart c).symm)
      (fun α => (w ^ j * m α) c ∘ (X.A.chart c).symm) _ a au hz ah
    have hF := chart_sum_eq X.A Z.s a (fun α => w ^ j * m α) c
    rw [hF]
    refine ⟨h1, fun v => ?_⟩
    rw [h3 v]
    have hJ0 : sJac X.A Z.s c x ≠ 0 := Z.nondeg x hx
    have hcoef : ∀ α, ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) =
        g α x * sJac X.A Z.s c x := by
      intro α
      have hr := hm α x hx
      have hw0 : w c x ≠ 0 := hc₀ x hx
      simp only [res] at hr
      rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc, Pi.mul_apply, Pi.pow_apply]
      linear_combination hr
    have hder : ∀ i, sJacMap X.A Z.s c x v i =
        fderiv ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) v := by
      intro i
      show (fderiv ℂ (fun z i => (Z.s i c ∘ (X.A.chart c).symm) z) (X.A.chart c x)) v i = _
      rw [fderiv_pi (fun i => (au i).differentiableAt)]
      rfl
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hcoef α]
    simp only [hder]
    ring
  refine ⟨∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow Z.s α * (w ^ j * m α), ?_,
    fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩
  refine Submodule.sum_mem _ fun α hα => ?_
  have hexp : sPow Z.s α * (w ^ j * m α) =
      ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • (sPow Z.s α * (∏ l, X.e (ι l)) * m α) := by
    rw [hwj, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [hexp]
  exact Submodule.sum_mem _ fun ι _ => Submodule.smul_mem _ _ (Submodule.mem_sup_left
    (Submodule.subset_span ⟨α, j, ι, m α, hmV α, by rw [hsum α hα]; omega,
      by rw [hsum α hα]; exact ha, rfl⟩))
end _root_.GroundTheory.Heights₂.Heights.EffectiveHS.SymOnto
end GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
