-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.analyticOnNhd_comp_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:01.542699+00:00
-- url     : https://prove2.me/submissions/67d76ba8-75e3-42e9-94b8-dd77e9ef2e45

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_analyticAt_coord_symm

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
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} (hψ : R.GoodChart ψ) {m : ℕ}
    (f : R.M → Fin m → ℂ) (S : Set R.M) (hS : IsOpen S) (j : Fin R.n) (hSj : S ⊆ R.src j)
    (r : Fin m → MvPolynomial (Fin (R.amb j)) ℂ) (hf : ∀ y ∈ S, f y = evalFam r (R.coord j y)) :
    AnalyticOnNhd ℂ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' S) := by
  obtain ⟨i, hsi, -, g, hg, hgc⟩ := hψ
  rintro w ⟨hw, hwS⟩
  have hwS' : ψ.symm w ∈ S := hwS
  have hev : (fun w' => evalFam r (R.coord j (ψ.symm w'))) =ᶠ[𝓝 w] (f ∘ ψ.symm) := by
    have hS' : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ S :=
      (ψ.continuousAt_symm hw).preimage_mem_nhds (hS.mem_nhds hwS')
    filter_upwards [hS'] with w' h1
    exact (hf _ h1).symm
  refine AnalyticAt.congr ?_ hev
  rw [analyticAt_pi_iff]
  intro l
  exact R.analyticAt_coord_symm hsi hg hgc j (r l) hw (hSj hwS')
end AlgRes
end ReciprocityTheory.AnForm.R
