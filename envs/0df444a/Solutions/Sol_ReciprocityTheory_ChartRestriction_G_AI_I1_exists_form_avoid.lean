-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.exists_form_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:48.798543+00:00
-- url     : https://prove2.me/submissions/5adaa079-6b0e-4b21-af36-604ece2ed963

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_coordProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_coordProd_not_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (S : Set (Ideal (MRingOver F ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver F ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by
  classical
  set T : Finset (Ideal (MRingOver F ι)) :=
    hS.toFinset.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => hS.mem_toFinset.mp (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := hS.exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hW'.prop,
      fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hgen : ∀ W ∈ T, ∀ W' ∈ T, W' ≠ W →
      ∃ g : MRingOver F ι, ∃ a : K → ℕ, IsMultiHomog g a ∧ g ∈ W' ∧ g ∉ W := by
    intro W hW W' hW' hne
    obtain ⟨S', hS'h, hS'eq⟩ := (hS' W' (hTS W' hW')).2.1
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    apply hne
    refine (hTmax W' hW' W (hTS W hW) ?_).symm
    rw [hS'eq, Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS'h g hg
    exact hc g a ha (hS'eq ▸ Ideal.subset_span hg)
  choose! gen degG hgenH hgenMem hgenNot using hgen
  set a : Ideal (MRingOver F ι) → MRingOver F ι := fun W => ∏ W' ∈ T.erase W, gen W W' with ha
  set δ : Ideal (MRingOver F ι) → K → ℕ := fun W => ∑ W' ∈ T.erase W, degG W W' with hδ
  have haH : ∀ W ∈ T, IsMultiHomog (a W) (δ W) := fun W hW =>
    isMultiHomog_prod _ _ _ fun W' hW' =>
      hgenH W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW')
  have haNot : ∀ W ∈ T, a W ∉ W := by
    intro W hW h
    obtain ⟨W', hW', hg⟩ := ((hS' W (hTS W hW)).1.prod_mem_iff).mp h
    exact hgenNot W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW') hg
  have haMem : ∀ W ∈ T, ∀ W'' ∈ T, W'' ≠ W → a W ∈ W'' := by
    intro W hW W'' hW'' hne
    have hmem : W'' ∈ T.erase W := Finset.mem_erase.mpr ⟨hne, hW''⟩
    show (∏ W' ∈ T.erase W, gen W W') ∈ W''
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hgenMem W hW W'' hW'' hne)
  refine ⟨∑ W ∈ T, δ W, fun d hd => ?_⟩
  have hδd : ∀ W ∈ T, δ W ≤ d := fun W hW =>
    le_trans (Finset.single_le_sum (f := δ) (fun _ _ _ => Nat.zero_le _) hW) hd
  have hrel : ∀ W ∈ T, IsRelevant W := fun W hW => (hS' W (hTS W hW)).2.2
  set m : Ideal (MRingOver F ι) → MRingOver F ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver F ι) ^ (d k - δ W k) else 0
    with hm
  have hmH : ∀ W ∈ T, IsMultiHomog (m W) (d - δ W) := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact isMultiHomog_coordProd _ _
  have hmNot : ∀ W ∈ T, m W ∉ W := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact coordProd_not_mem (hS' W (hTS W hW)).1 _ (fun k => ((hrel W hW) k).choose_spec) _
  refine ⟨∑ W ∈ T, a W * m W, ?_, ?_⟩
  · apply isMultiHomog_sum
    intro W hW
    have := isMultiHomog_mul (haH W hW) (hmH W hW)
    rwa [add_tsub_cancel_of_le (hδd W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ h
      rw [← Finset.add_sum_erase _ _ hW₀] at h
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _
          (haMem W (Finset.mem_of_mem_erase hW) W₀ hW₀ (Finset.ne_of_mem_erase hW).symm)
      have h1 := (Ideal.add_mem_iff_left _ hrest).mp h
      rcases (hS' W₀ (hTS W₀ hW₀)).1.mem_or_mem h1 with h2 | h2
      · exact haNot W₀ hW₀ h2
      · exact hmNot W₀ hW₀ h2
    intro W hW h
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' h)
end ReciprocityTheory.ChartRestriction.G.AI.I1
