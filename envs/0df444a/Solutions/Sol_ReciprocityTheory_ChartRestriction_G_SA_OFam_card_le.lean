-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.OFam.card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:37.885796+00:00
-- url     : https://prove2.me/submissions/78e50538-4888-4f84-b3fb-253056414e52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_sum_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable {e f : ι → K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
  (hef : hf σ J e f = 1) (hdet : IsUnit J.det) (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
  (h2 : IsUnit (2 : K)) {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
namespace OFam
theorem _root_.solution [Nontrivial K] {r : ℕ} (F : OFam σ J e f r) : r + 2 ≤ Fintype.card ι := by
  classical
  have hadd1 : ∀ x y z, hf σ J (x + y) z = hf σ J x z + hf σ J y z := by
    intro x y z
    simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hadd2 : ∀ x y z, hf σ J x (y + z) = hf σ J x y + hf σ J x z := by
    intro x y z
    simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hsub2 : ∀ x y z, hf σ J x (y - z) = hf σ J x y - hf σ J x z := by
    intro x y z
    simp only [hf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsm1 : ∀ (c : K) x y, hf σ J (c • x) y = c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsm2 : ∀ (c : K) x y, hf σ J x (c • y) = σ c * hf σ J x y := by
    intro c x y
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsym : ∀ x y, hf σ J y x = σ (hf σ J x y) := by
    intro x y
    simp only [hf, map_sum, map_mul, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJij : J j i = σ (J i j) := congrFun (congrFun hJ i) j
    rw [hJij]
    ring
  have hfe : hf σ J f e = 1 := by rw [hsym, hef, map_one]
  let v : Fin (r + 2) → ι → K := Fin.cons e (Fin.cons f F.a)
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hpair : ∀ z, ∑ i, g i * hf σ J (v i) z = 0 := by
      intro z
      have h1 := congrArg (fun w => hf σ J w z) hg
      have h0 : hf σ J 0 z = 0 := by simp [hf]
      simp only [hf_sum_left, hsm1] at h1
      rw [h1, h0]
    simp only [Fin.sum_univ_succ, v, Fin.cons_zero, Fin.cons_succ] at hpair
    have hg0 : g 0 = 0 := by
      have h := hpair f
      simp only [hef, hff, F.ha_f, mul_zero, Finset.sum_const_zero, add_zero, mul_one] at h
      exact h
    have hg1 : g (Fin.succ 0) = 0 := by
      have h := hpair e
      simp only [he, hfe, F.ha_e, mul_zero, Finset.sum_const_zero, add_zero, mul_one, zero_add] at h
      exact h
    have hgk : ∀ k : Fin r, g k.succ.succ = 0 := by
      intro k
      have h := hpair (F.a k)
      have hek : hf σ J e (F.a k) = 0 := by rw [hsym, F.ha_e, map_zero]
      have hfk : hf σ J f (F.a k) = 0 := by rw [hsym, F.ha_f, map_zero]
      rw [hek, hfk, Finset.sum_eq_single k] at h
      · have h2 : g k.succ.succ * hf σ J (F.a k) (F.a k) = 0 := by simpa using h
        calc g k.succ.succ = g k.succ.succ * (F.inv k * hf σ J (F.a k) (F.a k)) := by
              rw [F.hinv, mul_one]
          _ = 0 := by rw [mul_comm (F.inv k), ← mul_assoc, h2, zero_mul]
      · intro j _ hjk
        rw [F.ho j k hjk, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    intro i
    refine Fin.cases hg0 (fun i' => ?_) i
    exact Fin.cases hg1 (fun k => hgk k) i'
  have hcard := hli.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using hcard
end OFam
end ReciprocityTheory.ChartRestriction.G.SA
