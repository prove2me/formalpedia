-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.inflD_of_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:03.016939+00:00
-- url     : https://prove2.me/submissions/4b5cf795-c827-42c7-b04d-e9807e7af58e

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.InflationTransgression.cj_coe

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution (M : TRep R G) (N : Subgroup G) [N.Normal] (f : N → M.V) (y : G → M.V)
    (h2 : ∀ g (n : N), y (g * n) = y g + M.rho g (f n))
    (h3 : ∀ (n : N) g, y (n * g) = f n + M.rho n (y g)) : InflD M N (D1 M y) := by
  have hc : ∀ (c : G) (n : N), M.rho n (y c) = y c + M.rho c (f (cj N c n)) - f n := by
    intro c n
    have e : (n : G) * c = c * (cj N c n : G) := by rw [cj_coe]; group
    have h := h3 n c
    rw [e, h2] at h
    exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))
  refine ⟨?_, ?_, ?_⟩
  · intro a b n
    simp only [D1]
    rw [h2 b n, ← mul_assoc, h2 (a * b) n]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro a b n
    simp only [D1]
    have e : a * (n : G) * b = a * b * (cj N b n : G) := by rw [cj_coe]; group
    rw [e, h2 (a * b), h2 a n]
    simp only [map_mul, Module.End.mul_apply]
    rw [hc b n]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro a b n
    simp only [D1, map_add, map_sub]
    rw [hc (a * b) n, hc a n]
    have e : (n : G) * a = a * (cj N a n : G) := by rw [cj_coe]; group
    have e2 : M.rho n (M.rho a (y b)) = M.rho a (M.rho (cj N a n) (y b)) := by
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    have e3 : cj N b (cj N a n) = cj N (a * b) n := by
      apply Subtype.ext
      simp only [cj_coe]
      group
    rw [e2, hc b (cj N a n), e3]
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply]
    abel
end ReciprocityTheory.Coh.InflationTransgression
