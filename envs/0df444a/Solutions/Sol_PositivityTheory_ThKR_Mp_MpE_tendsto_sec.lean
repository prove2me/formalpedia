-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpE.tendsto_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:50.521918+00:00
-- url     : https://prove2.me/submissions/ac66141e-a169-453d-a63c-e03856dfb633

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_sec_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpE
namespace PositivityTheory.ThKR.Mp.MpE
theorem _root_.solution (hD : SecDer l) (f : Sch l) :
    Tendsto (fun s : Sp l => schwartzToL2 l (sec s.1 f)) (𝓝 1) (𝓝 (schwartzToL2 l f)) := by
  let m' : (l ⊕ l) → (l ⊕ l) → (((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] ℝ) := fun a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => ℝ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => (l ⊕ l) → ℝ) a)
  have h := hD ((l ⊕ l) → (l ⊕ l) → ℝ) (fun x => Matrix.of x) m' (fun a b => (1 : Mat l) a b) rfl
    (fun a b => (m' a b).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)) f
  have h2 : schwartzToL2 l (sec (Matrix.of fun a b => (1 : Mat l) a b) f) = schwartzToL2 l f := by
    rw [show (Matrix.of fun a b => (1 : Mat l) a b) = 1 from rfl, sec_one, ContinuousLinearMap.one_apply]
  have h3 : Tendsto (fun x : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of x) f))
      (𝓝 (fun a b => (1 : Mat l) a b)) (𝓝 (schwartzToL2 l f)) := by
    convert h.continuousAt.tendsto using 2
    exact h2.symm
  have hc : Continuous fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ) :=
    continuous_pi fun a => continuous_pi fun b => continuous_subtype_val.matrix_elem a b
  have h4 : Tendsto (fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ)) (𝓝 1)
      (𝓝 (fun a b => (1 : Mat l) a b)) := hc.tendsto 1
  exact h3.comp h4
end PositivityTheory.ThKR.Mp.MpE
