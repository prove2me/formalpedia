-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreGermIntegral_proof_6c70cd55f5c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:02.500867+00:00
-- url     : https://prove2.me/submissions/94e4cbad-7935-4439-b72d-e95134e1b642

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassFiniteness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreGermIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteFibreGermIntegral
theorem _root_.solution (hWF : WeierstrassFiniteness.Statement)
    (hR : RueckertNullstellensatz.Statement) : FiniteFibreGermIntegral.Statement := by
  intro σ _ X x d A hX hiso g hg
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hfx : ∀ i, AnalyticAt ℂ (f i) x := fun i => hf i x hxN
  have hAj : ∀ j : Fin d, AnalyticAt ℂ (fun z => A z j - A x j) x := fun j =>
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt x).sub
      analyticAt_const

  let F : Fin (k + d) → (σ → ℂ) → ℂ := Fin.append f (fun j z => A z j - A x j)
  have hFx : ∀ i, AnalyticAt ℂ (F i) x := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left] using hfx i
    · simpa only [F, Fin.append_right] using hAj j
  have hcoord : ∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j) := by
    intro l
    have hl : AnalyticAt ℂ (fun z : σ → ℂ => z l - x l) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) l).analyticAt x).sub analyticAt_const
    have hvan : ∀ᶠ z in 𝓝 x, (∀ i, F i z = 0) → z l - x l = 0 := by
      filter_upwards [hNo.mem_nhds hxN, hW] with z hzN hzW h0
      have hf0 : ∀ i, f i z = 0 := fun i => by simpa only [F, Fin.append_left] using h0 (Fin.castAdd d i)
      have hA0 : A z = A x := funext fun j =>
        sub_eq_zero.1 (by simpa only [F, Fin.append_right] using h0 (Fin.natAdd k j))
      have hzX : z ∈ X := by
        have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hzN, hf0⟩
        exact this.1
      rw [hWiso z ⟨hzX, hzW⟩ hA0, sub_self]
    obtain ⟨m, h, -, hh, hsum⟩ := hR σ x (k + d) F (fun z => z l - x l) hFx hl hvan
    refine ⟨m, fun i => h (Fin.castAdd d i), fun j => h (Fin.natAdd k j), fun i => hh _, fun j => hh _, ?_⟩
    filter_upwards [hsum] with z hz
    rw [hz, Fin.sum_univ_add]
    simp only [F, Fin.append_left, Fin.append_right]
  obtain ⟨n, a, h, ha, -, hrel⟩ := hWF σ x k f d A hfx hcoord g hg
  refine ⟨n, a, ha, ?_⟩
  filter_upwards [hrel, hNo.mem_nhds hxN] with z hz hzN hzX
  have hz0 : z ∈ X ∩ N := ⟨hzX, hzN⟩
  rw [hXN] at hz0
  rw [hz]
  simp [hz0.2]
end FiniteFibreGermIntegral
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
