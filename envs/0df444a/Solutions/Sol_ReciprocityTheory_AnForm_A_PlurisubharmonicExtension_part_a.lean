-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.part_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:44.122134+00:00
-- url     : https://prove2.me/submissions/5272bd66-f0c7-42d9-8947-0ab1710f6bcf

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_local_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹)) :
    ∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → BddAbove (u '' (K \ coordDiv S)) := by
  intro K hK hKU
  choose! ρ hρ M hM using fun p (hp : p ∈ U) => local_bound hU hU1 hc hpsh hg hp
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : K => ball (p : Fin D → ℂ) (ρ p))
    (fun _ => isOpen_ball)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hρ z (hKU hz))⟩)
  refine ⟨∑ p ∈ t, |M p|, ?_⟩
  rintro _ ⟨z, ⟨hzK, hzS⟩, rfl⟩
  obtain ⟨p, hpt, hzp⟩ : ∃ p ∈ t, z ∈ ball (p : Fin D → ℂ) (ρ p) := by
    simpa only [Set.mem_iUnion, exists_prop] using ht hzK
  have h1 := hM p (hKU p.2) z ⟨hzp, hzS⟩
  have h2 : |M p| ≤ ∑ q ∈ t, |M q| := Finset.single_le_sum (f := fun q : K => |M (q : Fin D → ℂ)|) (fun q _ => abs_nonneg _) hpt
  exact h1.trans ((le_abs_self _).trans h2)
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
