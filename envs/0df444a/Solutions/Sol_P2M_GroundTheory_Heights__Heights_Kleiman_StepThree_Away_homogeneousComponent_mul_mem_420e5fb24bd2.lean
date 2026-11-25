-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_mul_mem_420e5fb24bd2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:54.577355+00:00
-- url     : https://prove2.me/submissions/6341bcf5-6355-45c3-8bfe-949e1676dabe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_homog_mul_e19dd5398082
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_div_pow_mem_chartRing_8ee4288dcdfe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
theorem _root_.solution (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) {f : Poly S N} (hf : f ∈ zeroIdeal D σ) (e : ℕ) :
    ∀ δ ∈ D.sub I, aeval x (homogeneousComponent e f) * δ ∈
      Submodule.span (chartRing S x I) {σ * x i ^ e} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [zeroIdeal, Ideal.span] at hf
  induction hf using Submodule.span_induction generalizing e with
  | mem g hg =>
    obtain ⟨c, hgc, hg⟩ := hg
    intro δ hδ
    rw [homogeneousComponent_of_mem hgc]
    split_ifs with hce
    · subst hce
      obtain ⟨o, ho, heq⟩ := hg I δ hδ
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
      obtain ⟨t, rfl⟩ := ho
      rw [heq, Submodule.mem_span_singleton]
      exact ⟨t, by rw [chartRing_smul_def, chartRing_smul_def, zpow_natCast]; ring⟩
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | zero => intro δ _; rw [map_zero, map_zero, zero_mul]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    intro δ hδ
    rw [map_add, map_add, add_mul]
    exact Submodule.add_mem _ (hf e δ hδ) (hg e δ hδ)
  | smul r f _ hf =>
    intro δ hδ
    have hsum : r * f = ∑ d ∈ Finset.range (r.totalDegree + 1), homogeneousComponent d r * f := by
      rw [← Finset.sum_mul, sum_homogeneousComponent]
    rw [smul_eq_mul, hsum, map_sum, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [homogeneousComponent_homog_mul (homogeneousComponent_isHomogeneous d r) f e]
    split_ifs with hde
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hf (e - d) δ hδ)
      rw [map_mul, mul_assoc, ← ht, Submodule.mem_span_singleton]
      refine ⟨⟨_, div_pow_mem_chartRing I hi (homogeneousComponent_isHomogeneous d r)⟩ * t, ?_⟩
      have hpow : x i ^ e = x i ^ d * x i ^ (e - d) := by rw [← pow_add, Nat.add_sub_cancel' hde]
      have hxd : x i ^ d ≠ 0 := pow_ne_zero _ hxi
      rw [chartRing_smul_def, chartRing_smul_def, Subalgebra.coe_mul, hpow]
      field_simp
      try ring
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
