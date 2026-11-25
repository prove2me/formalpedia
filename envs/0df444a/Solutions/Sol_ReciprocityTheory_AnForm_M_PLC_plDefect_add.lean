-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.plDefect_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:29.356501+00:00
-- url     : https://prove2.me/submissions/847b362e-6a10-43fe-9f10-f15e798534d2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurve
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_continuous_of_smooth
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_mInt_congr_phi
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_logNormIntegrable
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntLinear
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m (fun k => {p k}))
    {f f' : X → ℝ} (hf : A.Smooth f) (hf' : A.Smooth f') :
    plDefect A L s m p (fun z => f z + f' z) = plDefect A L s m p f + plDefect A L s m p f' := by
  have hPf := isPotential_ofFun A f hf
  have hPf' := isPotential_ofFun A f' hf'
  have hI : ∀ {h : X → ℝ}, IsPotential A (LocPot.ofFun h) →
      MIntegrable A (Fin.cons (LocPot.ofFun h) ![]) (logNormSec L s) := fun hP =>
    logNormIntegrable A L s m _ hL hs hsnc _ (Fin.forall_fin_one.2 hP)
  have h1 : mInt A ![LocPot.ofFun (fun z => f z + f' z)] (logNormSec L s) =
      mInt A ![LocPot.ofFun f] (logNormSec L s) + mInt A ![LocPot.ofFun f'] (logNormSec L s) := by
    exact (mInt_congr_phi A _ (Fin.cons (LocPot.ofFun f + LocPot.ofFun f') ![])
      (fun i a b => by fin_cases i; rfl) _).trans
      (mIntAdd (e := 0) A _ _ ![] hPf hPf' (fun i => i.elim0) _ (hI hPf) (hI hPf'))
  have hLp : ∀ i, IsPotential A (![L] i) := Fin.forall_fin_one.2 hL
  have h2 : mInt A ![L] (fun z => f z + f' z) = mInt A ![L] f + mInt A ![L] f' := by
    have := mIntLinear A ![L] hLp 1 f f' (mIntegrableCont A _ hLp f (continuous_of_smooth A hf))
      (mIntegrableCont A _ hLp f' (continuous_of_smooth A hf'))
    simpa using this
  unfold plDefect
  rw [h1, h2]
  simp only [mul_add, Finset.sum_add_distrib]
  ring
end ReciprocityTheory.AnForm.M.PLC
