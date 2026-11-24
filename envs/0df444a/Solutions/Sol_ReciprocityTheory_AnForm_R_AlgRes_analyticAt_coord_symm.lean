-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.analyticAt_coord_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:38.334497+00:00
-- url     : https://prove2.me/submissions/54453a51-08c6-4969-a433-65e0e3385bb4

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
import Theorems.Thm_ReciprocityTheory_AnForm_R_analyticAt_eval_of_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace ReciprocityTheory.AnForm.R
namespace AlgRes
theorem _root_.solution (R : AlgRes ι P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} {i : Fin R.n} (hs : ψ.source ⊆ R.src i)
    {g : (Fin e → ℂ) → Fin (R.amb i) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target)
    (hgc : ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w)
    (j : Fin R.n) (h : MvPolynomial (Fin (R.amb j)) ℂ) {w : Fin e → ℂ} (hw : w ∈ ψ.target)
    (hwj : ψ.symm w ∈ R.src j) :
    AnalyticAt ℂ (fun w => eval (R.coord j (ψ.symm w)) h) w := by
  have hwS : ψ.symm w ∈ ψ.source := ψ.map_target hw
  have hxi : ψ.symm w ∈ R.src i := hs hwS
  obtain ⟨q, F, hq0, hqF⟩ := R.trans i j (ψ.symm w) ⟨hxi, hwj⟩
  have hgw : AnalyticAt ℂ g w := hg w hw
  have hga : ∀ l, AnalyticAt ℂ (g · l) w := fun l =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (R.amb i) => ℂ) l).analyticAt (g w)).comp hgw
  have hFa : ∀ l, AnalyticAt ℂ (fun w' => eval (g w') (F l)) w := fun l =>
    analyticAt_eval_of_pi hga (F l)
  have hqa : AnalyticAt ℂ (fun w' => eval (g w') q) w := analyticAt_eval_of_pi hga q
  have hq0' : eval (g w) q ≠ 0 := by
    rw [← hgc w hw]
    exact hq0
  have hA : AnalyticAt ℂ (fun w' => eval (fun l => eval (g w') (F l) / eval (g w') q) h) w :=
    analyticAt_eval_of_pi (f := fun w' l => eval (g w') (F l) / eval (g w') q)
      (fun l => (hFa l).div hqa hq0') h
  refine hA.congr ?_
  have ht : ψ.target ∈ 𝓝 w := ψ.open_target.mem_nhds hw
  have hj : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ R.src j :=
    (ψ.continuousAt_symm hw).preimage_mem_nhds ((R.isOpen_alt_bis j).mem_nhds hwj)
  have hqne : ∀ᶠ w' in 𝓝 w, eval (g w') q ≠ 0 := hqa.continuousAt.eventually_ne hq0'
  filter_upwards [ht, hj, hqne] with w' h1 h2 h3
  have hsrc : ψ.symm w' ∈ R.src i := hs (ψ.map_target h1)
  have hcw : R.coord i (ψ.symm w') = g w' := hgc w' h1
  have hfun : (fun l => eval (g w') (F l) / eval (g w') q) = R.coord j (ψ.symm w') := by
    funext l
    have hl := hqF (ψ.symm w') ⟨hsrc, h2⟩ (by rw [hcw]; exact h3) l
    rw [hcw] at hl
    rw [div_eq_iff h3]
    exact hl.symm
  exact congrArg (fun v => eval v h) hfun
end AlgRes
end ReciprocityTheory.AnForm.R
