-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.step_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:50.990474+00:00
-- url     : https://prove2.me/submissions/b7b4b40a-2bec-465b-ae64-d03871247547

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_kr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_kr_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
set_option maxHeartbeats 1000000
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (C : ℂ) :
    ∫ β, ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ)) =
      ∫ x, Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) ∂μ := by
  have hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1)) :=
    (continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)
  have hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ) :=
    hΨ.aestronglyMeasurable.comp_snd
  have hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ) :=
    (hψc.measurable.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖))
      (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨β, x⟩ := p
    show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)
    rw [norm_mul, norm_mul, norm_mul]
    have hk := norm_kr_le ε t hε (qq x - β)
    calc ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ‖kr ε t (qq x - β)‖)) ≤
          ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ∫ y, ‖gam (n := n) ε y‖)) := by gcongr
      _ = ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖) := by ring
  have e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) =
      fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ := by
    funext β
    rw [← integral_const_mul, ← integral_const_mul]
  have e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) =
      fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext β
    ring
  rw [e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]
end PositivityTheory.Rg.Sw.WR.D.Moll
