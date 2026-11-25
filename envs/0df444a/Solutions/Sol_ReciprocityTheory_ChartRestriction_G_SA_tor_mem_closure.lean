-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:36.160134+00:00
-- url     : https://prove2.me/submissions/c67db5d9-be8b-4f35-905f-7f6f2baf46cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hm_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_unitaryTransvection_zero_first
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_unitaryTransvection_zero_second
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_hm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_w_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_unitaryTransvection_zero_first_mem_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_unitaryTransvection_zero_second_mem_closure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
section
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
end
private theorem matrix_fin_two_eq_of_entries_eq {α : Type*} {p q r s p' q' r' s' : α} (h1 : p = p') (h2 : q = q')
    (h3 : r = r') (h4 : s = s') : !![p, q; r, s] = !![p', q'; r', s'] := by
  subst h1 h2 h3 h4; rfl
section
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
end
end ReciprocityTheory.ChartRestriction.G.SA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {δ di l li : K} (hσδ : σ δ = -δ) (hδ : δ * di = 1) (hl : σ l = l)
    (hli : l * li = 1) : tor σ J e f l li ∈ Submonoid.closure (eichSet σ J e f) := by
  have hmul : ∀ A B : Matrix (Fin 2) (Fin 2) K,
      hm σ J e f A ∈ Submonoid.closure (eichSet σ J e f) →
      hm σ J e f B ∈ Submonoid.closure (eichSet σ J e f) →
      hm σ J e f (A * B) ∈ Submonoid.closure (eichSet σ J e f) := by
    intro A B hA hB
    rw [← hm_mul hσ hJ he hff hef]
    exact Submonoid.mul_mem _ hA hB
  have hup : ∀ c : K, σ c = -c →
      hm σ J e f !![1, c; 0, 1] ∈ Submonoid.closure (eichSet σ J e f) := by
    intro c hc
    rw [← unitaryTransvection_zero_first σ J e f c]
    exact unitaryTransvection_zero_first_mem_closure hσ hJ he hff hef hc
  have hlow : ∀ c : K, σ c = -c →
      hm σ J e f !![1, 0; c, 1] ∈ Submonoid.closure (eichSet σ J e f) := by
    intro c hc
    rw [← unitaryTransvection_zero_second σ J e f c]
    exact unitaryTransvection_zero_second_mem_closure hσ hJ he hff hef hc
  have hw : ∀ a ai : K, σ a = -a → a * ai = 1 →
      hm σ J e f !![0, a; -ai, 0] ∈ Submonoid.closure (eichSet σ J e f) := by
    intro a ai ha h
    have h1 : σ a * σ ai = 1 := by rw [← map_mul, h, map_one]
    rw [ha] at h1
    have hs : σ ai = -ai := by linear_combination (-ai) * h1 - σ ai * h
    have hs' : σ (-ai) = -(-ai) := by rw [map_neg, hs]
    rw [← w_eq h]
    exact hmul _ _ (hmul _ _ (hup a ha) (hlow _ hs')) (hup a ha)
  have key : (!![l, 0; 0, li] : Matrix (Fin 2) (Fin 2) K) =
      !![0, l * δ; -(li * di), 0] * !![0, -δ; -(-di), 0] := by
    rw [Matrix.mul_fin_two]
    exact matrix_fin_two_eq_of_entries_eq (by linear_combination -l * hδ) (by ring) (by ring)
      (by linear_combination -li * hδ)
  rw [tor_hm, key]
  refine hmul _ _ (hw _ _ ?_ ?_) (hw _ _ ?_ ?_)
  · rw [map_mul, hl, hσδ]; ring
  · linear_combination (δ * di) * hli + hδ
  · rw [map_neg, hσδ]
  · linear_combination hδ
end ReciprocityTheory.ChartRestriction.G.SA
