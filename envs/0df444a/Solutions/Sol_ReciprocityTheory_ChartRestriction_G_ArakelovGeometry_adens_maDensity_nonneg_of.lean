-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:14.783341+00:00
-- url     : https://prove2.me/submissions/99668528-f070-4158-a08c-a79d8e5bb408

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_isConeTangent
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__id_ce5e717798ac
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_contDiffAt_log__a466d063bccb
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_posSemidef_of_levi
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_nonneg_of_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_eq_maDens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {V : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hV : IsOpen V) (hγ : AnalyticOnNhd ℂ γ V)
    (hpts : ∀ y ∈ V, γ y ∈ pts P) {y : Fin D → ℂ} (hy : y ∈ V) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  have hne : γ y ≠ 0 := (hpts y hy).1
  have h2 := adens_contDiffAt_logρ hsp.1 (hγ y hy) hne
  rw [adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (m.ρ z)) ξ (hγ y hy)
    (adens_contDiffAt_logρ_id hsp.1 hne)
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (m.ρ z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ (hpts y hy) hne _ (adens_isConeTangent hV hγ hpts hy ξ)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
