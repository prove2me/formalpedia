-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_WellDefined_proof_f636440f4c52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:18:03.008941+00:00
-- url     : https://prove2.me/submissions/91274a64-78e3-44b8-9eda-a6e115fbf677

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PWellDefined
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divSupp_disjoint_of_not_mem_8696054d16d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiProjPrime_of_mem_divSupp_7a36169f94bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_sqMetric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace WellDefined
theorem _root_.solution (h₁ : Swap.Statement) (h₂ : RPositionAdd.Statement) :
    WellDefined.Statement := by
  intro K _ ι _ I P n L B s t hR hA hP hL hB hs ht
  classical
  obtain ⟨bs, hbs, hsH, hsP⟩ := hs
  obtain ⟨bt, hbt, htH, htP⟩ := ht
  have hPm : IsMultiProjPrime P := hP.2.1
  set S : Set (Ideal (MRing ι)) := divSupp P s ∪ divSupp P t ∪ {P} with hSdef
  have hSf : S.Finite :=
    ((divSupp_finite P s).union (divSupp_finite P t)).union (Set.finite_singleton P)
  have hS' : ∀ W ∈ S, IsMultiProjPrime W := by
    rintro W ((hW | hW) | hW)
    · exact isMultiProjPrime_of_mem_divSupp hPm hsH hW
    · exact isMultiProjPrime_of_mem_divSupp hPm htH hW
    · rw [Set.mem_singleton_iff.mp hW]
      exact hPm
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSf hS'
  set M := L (Fin.last n) with hM
  set k : ℕ := ∑ l, (d₀ l + (M.a l).natAbs) with hkdef
  have hk1 : ∀ l, d₀ l + (M.a l).natAbs ≤ k := fun l =>
    Finset.single_le_sum (f := fun l => d₀ l + (M.a l).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l)
  set b : K → ℕ := fun l => (M.a l + k).toNat with hbdef
  have hb : ∀ l, (b l : ℤ) = M.a l + k := fun l =>
    Int.toNat_of_nonneg (by have := hk1 l; omega)
  have hbd : d₀ ≤ b := fun l => by
    have h1 := hk1 l
    have h2 := hb l
    show d₀ l ≤ b l
    omega
  have hkd : d₀ ≤ fun _ => k := fun l => by
    have := hk1 l
    show d₀ l ≤ k
    omega
  obtain ⟨a1, ha1H, ha1S⟩ := hd₀ b hbd
  obtain ⟨a2, ha2H, ha2S⟩ := hd₀ _ hkd
  set H : HermLine ι := HermLine.sqMetric (fun _ => k) with hH
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric _
  have hMs : IsSmoothHerm M := hL _
  have hA1s : IsSmoothHerm (M.tensor H) := isSmoothHerm_tensor hMs hHs
  have hL' : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
  have hPS : P ∈ S := Or.inr rfl
  have hsec1 : IsSectionOn P (M.tensor H) a1 :=
    ⟨b, fun l => by rw [hb l]; rfl, ha1H, ha1S P hPS⟩
  have hsec2 : IsSectionOn P H a2 := ⟨fun _ => k, fun l => rfl, ha2H, ha2S P hPS⟩
  have hsecs : IsSectionOn P B s := ⟨bs, hbs, hsH, hsP⟩
  have hsect : IsSectionOn P B t := ⟨bt, hbt, htH, htP⟩
  have d1s := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inl hW))
  have d1t := divSupp_disjoint_of_not_mem fun W hW => ha1S W (Or.inl (Or.inr hW))
  have d2s := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inl hW))
  have d2t := divSupp_disjoint_of_not_mem fun W hW => ha2S W (Or.inl (Or.inr hW))
  have e1s := h₁ K ι I P n (Fin.init L) B (M.tensor H) s a1 hR hP hL' hB hA1s hsecs hsec1 d1s
  have e1t := h₁ K ι I P n (Fin.init L) B (M.tensor H) t a1 hR hP hL' hB hA1s hsect hsec1 d1t
  have e2s := h₁ K ι I P n (Fin.init L) B H s a2 hR hP hL' hB hHs hsecs hsec2 d2s
  have e2t := h₁ K ι I P n (Fin.init L) B H t a2 hR hP hL' hB hHs hsect hsec2 d2t
  have fs := h₂ K ι I P n (Fin.init L) M H B s hA hP hL' hMs hHs hB hsecs
  have ft := h₂ K ι I P n (Fin.init L) M H B t hA hP hL' hMs hHs hB hsect
  have hLeq : L = Fin.snoc (Fin.init L) M := (Fin.snoc_init_self L).symm
  rw [hLeq]
  linarith
end WellDefined
end GroundTheory.Heights₂.Heights.Inter
