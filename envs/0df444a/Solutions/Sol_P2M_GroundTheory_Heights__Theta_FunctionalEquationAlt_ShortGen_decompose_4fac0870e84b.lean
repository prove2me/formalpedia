-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:29.199432+00:00
-- url     : https://prove2.me/submissions/6aacfb75-4560-4cde-84c3-8c5f9d8e0a27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_finite_of_sep_4b1948ea545f
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_basis_of_discrete_8406af3766d6
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_eq_of_span_eq_a780c4a08928
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_apply_bc8e45da2f5a
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_inner_proj_6ef07283d6e8
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_half_le_norm_proj_ab6caeac0109
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_orth_73427f220327
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_add_ebe2c8ece1c1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {m : ℕ} (b : Fin (m + 1) → W) (hb : LinearIndependent ℝ b) {lam : ℝ}
    (hlam : 0 < lam) (hsep : Sep (span ℤ (Set.range b)) lam) :
    ∃ (v : W) (c : Fin m → W), v ∈ span ℤ (Set.range b) ∧ v ≠ 0 ∧ lam ≤ ‖v‖ ∧
      (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖) ∧ LinearIndependent ℝ c ∧
      (∀ u, u ∈ span ℤ (Set.range c) ↔ ∃ x ∈ span ℤ (Set.range b), proj v x = u) ∧
      Sep (span ℤ (Set.range c)) (lam / 2) ∧
      (gram ℝ b).det = ‖v‖ ^ 2 * (gram ℝ c).det := by
  set L := span ℤ (Set.range b) with hL
  have hb0 : b 0 ≠ 0 := hb.ne_zero 0
  have hb0L : b 0 ∈ L := subset_span ⟨0, rfl⟩
  set T := {x : W | x ∈ L ∧ ‖x‖ ≤ ‖b 0‖} ∩ {x | x ≠ 0} with hT
  have hTfin : T.Finite := (finite_of_sep hlam hsep _).subset Set.inter_subset_left
  have hTne : T.Nonempty := ⟨b 0, ⟨hb0L, le_rfl⟩, hb0⟩
  obtain ⟨v, ⟨⟨hvL, -⟩, hv⟩, hvmin⟩ := Set.exists_min_image T (fun x => ‖x‖) hTfin hTne
  have hmin : ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
    intro x hx hx0
    by_cases h : ‖x‖ ≤ ‖b 0‖
    · exact hvmin x ⟨⟨hx, h⟩, hx0⟩
    · exact (hvmin (b 0) ⟨⟨hb0L, le_rfl⟩, hb0⟩).trans (le_of_not_ge h)
  let L' : Submodule ℤ W := L.map ((proj v).restrictScalars ℤ)
  have hmemL' : ∀ u, u ∈ L' ↔ ∃ x ∈ L, proj v x = u := fun u => by
    simp only [L', Submodule.mem_map, LinearMap.restrictScalars_apply]
  have hsepL' : Sep L' (lam / 2) := by
    intro u hu hu0
    obtain ⟨x, hx, rfl⟩ := (hmemL' u).1 hu
    have := half_le_norm_proj hvL hv hmin hx hu0
    linarith [hsep v hvL hv]
  have hdL' := discreteTopology_of_sep (half_pos hlam) hsepL'
  obtain ⟨n, c, hc, hcspan⟩ := exists_basis_of_discrete L'
  have hlift : ∀ i, ∃ w ∈ L, proj v w = c i := fun i =>
    (hmemL' (c i)).1 (hcspan ▸ subset_span ⟨i, rfl⟩)
  choose w hwL hw using hlift
  have hpv := proj_self v hv
  have hwind : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp (proj v)
    convert hc using 1
    funext i
    exact hw i
  have hvw : v ∉ span ℝ (Set.range w) := by
    intro h
    obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun ℝ).1 h
    have h2 : ∑ i, a i • c i = 0 := by
      have := congrArg (proj v) ha
      rw [map_sum, hpv] at this
      simpa [map_smul, hw] using this
    have ha0 := Fintype.linearIndependent_iff.1 hc a h2
    apply hv
    rw [← ha]
    simp [ha0]
  have hb'ind : LinearIndependent ℝ (Fin.cons v w : Fin (n + 1) → W) :=
    linearIndependent_finCons.2 ⟨hwind, hvw⟩
  have hspan' : span ℤ (Set.range (Fin.cons v w : Fin (n + 1) → W)) = L := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hvL
      · simpa using hwL i
    · intro x hx
      have hpx : proj v x ∈ span ℤ (Set.range c) := by
        rw [hcspan]
        exact (hmemL' _).2 ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun ℤ).1 hpx
      have hyL : x - ∑ i, k i • w i ∈ L :=
        L.sub_mem hx (L.sum_mem fun i _ => L.smul_mem _ (hwL i))
      have hy0 : proj v (x - ∑ i, k i • w i) = 0 := by
        rw [map_sub, map_sum]
        simp only [map_zsmul, hw, hk, sub_self]
      obtain ⟨k0, hk0⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin hyL hy0
      have hx' : x = k0 • v + ∑ i, k i • w i := by
        rw [← hk0]
        abel
      rw [hx']
      refine add_mem (Submodule.smul_mem _ _ (subset_span ⟨0, by simp⟩))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i.succ, by simp⟩))
  have hnm : n = m := by
    have h1 := finrank_span_eq_card hb
    have h2 := finrank_span_eq_card hb'ind
    have hsp : span ℝ (Set.range b) = span ℝ (Set.range (Fin.cons v w : Fin (n + 1) → W)) := by
      rw [← span_span_of_tower ℤ ℝ (Set.range b),
        ← span_span_of_tower ℤ ℝ (Set.range (Fin.cons v w : Fin (n + 1) → W)), hspan']
    rw [hsp, h2] at h1
    simpa using h1
  subst hnm
  refine ⟨v, c, hvL, hv, hsep v hvL hv, hmin, hc, fun u => by rw [hcspan]; exact hmemL' u,
    hcspan ▸ hsepL', ?_⟩
  have hZ : LinearIndependent ℤ b := hb.restrict_scalars' (R := ℤ)
  rw [det_gram_eq_of_span_eq hZ hspan'.symm]
  have hwc : w = fun i => c i + (inner ℝ v (w i) / ‖v‖ ^ 2) • v := by
    funext i
    rw [← hw i, proj_apply]
    abel
  rw [hwc, det_gram_cons_add, det_gram_cons_orth v c (fun i => by rw [← hw i]; exact inner_proj v _ hv)]
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
