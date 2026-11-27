-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePacking_proof_d694c453e837
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:52.718556+00:00
-- url     : https://prove2.me/submissions/1dba8e08-cbad-40bc-a551-71d4a04e8294

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_CardLeOfSeparated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePacking_card_le_of_separated_2446897261d7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module Function
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LatticePacking
theorem _root_.solution : LatticePacking.Statement := by
  intro V _ _ L hL B hB hmin
  classical
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
  have : IsAddTorsionFree V := .of_module_rat _
  have : Module.IsTorsionFree ℤ L :=
    Injective.moduleIsTorsionFree (R := ℤ) (fun y : L => (y : V)) Subtype.val_injective
      (fun _ _ => rfl)
  set δ : ℝ := Real.exp (-B) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by rw [hδdef, Real.exp_le_one_iff]; linarith
  let b := Module.Free.chooseBasis ℤ L
  let f : Module.Free.ChooseBasisIndex ℤ L → V := fun i => ((b i : L) : V)
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range f)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  have hdim : finrank ℝ W ≤ finrank ℤ L := by
    exact (finrank_range_le_card (R := ℝ) f).trans
      (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).ge
  have hW : ∀ x ∈ L, x ∈ W := by
    intro x hx
    have h1 : x = ∑ i, b.repr ⟨x, hx⟩ i • f i := by
      calc x = ((⟨x, hx⟩ : L) : V) := rfl
        _ = L.subtype (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, b.repr ⟨x, hx⟩ i • f i := by rw [map_sum]; rfl
    rw [h1]
    exact Submodule.sum_mem _ fun i _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  set S : Set V := {x : V | x ∈ L ∧ ‖x‖ ≤ 1} with hS
  set C : ℝ := ((2 * 1 + δ) / δ) ^ finrank ℝ W with hC
  have key : ∀ t : Finset V, (t : Set V) ⊆ S → (t.card : ℝ) ≤ C := by
    intro t ht
    have hcard : (t.subtype (· ∈ W)).card = t.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem]
      intro x hx
      exact hW x (ht hx).1
    rw [← hcard]
    refine LatticePacking.card_le_of_separated (t.subtype (· ∈ W)) hδ zero_le_one ?_ ?_
    · intro c hc
      rw [Finset.mem_subtype] at hc
      simpa using (ht hc).2
    · intro c hc d hd hcd
      rw [Finset.mem_subtype] at hc hd
      have hne : (c : V) - d ≠ 0 := sub_ne_zero.mpr fun h' => hcd (Subtype.ext h')
      have := hmin ((c : V) - d) (L.sub_mem (ht hc).1 (ht hd).1) hne
      simpa using this
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊C⌋₊ + 1)
    have h1 := key t ht
    rw [htc] at h1
    push_cast at h1
    have hC0 : 0 ≤ C := pow_nonneg (div_nonneg (by linarith) hδ.le) _
    linarith [Nat.lt_floor_add_one C]
  refine ⟨hfin, ?_⟩
  have h1 : (S.ncard : ℝ) ≤ C := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  refine h1.trans ?_
  have hq : (2 * 1 + δ) / δ ≤ 5 / δ := div_le_div_of_nonneg_right (by linarith) hδ.le
  have h5 : 1 ≤ 5 / δ := by rw [le_div_iff₀ hδ]; linarith
  have he : 5 / δ = Real.exp (B + Real.log 5) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), hδdef, Real.exp_neg, div_inv_eq_mul, mul_comm]
  calc C ≤ (5 / δ) ^ finrank ℝ W := pow_le_pow_left₀ (div_nonneg (by linarith) hδ.le) hq _
    _ ≤ (5 / δ) ^ finrank ℤ L := pow_le_pow_right₀ h5 hdim
    _ = Real.exp (finrank ℤ L * (B + Real.log 5)) := by rw [he, Real.exp_nat_mul]
end LatticePacking
end GroundTheory.Heights₂.Heights
