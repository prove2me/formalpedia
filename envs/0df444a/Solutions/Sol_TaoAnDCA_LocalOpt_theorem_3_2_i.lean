-- Prove2me | solution 1 for TaoAnDCA.LocalOpt.theorem_3_2_i
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:24:06.195404+00:00
-- url     : https://prove2.me/submissions/21f17302-c32c-4c93-9e12-8fb455d435e9

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology InnerProductSpace TaoAnDCA.GlobalOpt TaoAnDCA.LocalOpt

theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs : EuclideanSpace ℝ (Fin n)) (hloc : IsDCLocalMin g h xs) :
    xs ∈ Pl g h := by
  classical
  obtain ⟨hfin, _, U, hU, hmin⟩ := hloc
  have hgx : g xs ≠ ⊤ := by
    intro ht
    exact hfin (by simp [dcSub, ht])
  have hhx : h xs ≠ ⊤ := hgh.dom_g_sub hgx
  lift g xs to ℝ using ⟨hgx, hgh.g_mem.1 xs⟩ with a ha
  lift h xs to ℝ using ⟨hhx, hgh.h_mem.1 xs⟩ with b hb
  intro y hy
  obtain ⟨_, hsub⟩ := hy
  refine ⟨by rw [← ha]; exact hgx, ?_⟩
  intro z
  by_cases hgz : g z = ⊤
  · rw [hgz]; exact le_top
  lift g z to ℝ using ⟨hgz, hgh.g_mem.1 z⟩ with c hc
  let w : ℝ → EuclideanSpace ℝ (Fin n) := fun t => (1-t) • xs + t • z
  have hw : Tendsto w (𝓝[>] 0) (𝓝 xs) := by
    have ht : Continuous w := by dsimp [w]; fun_prop
    simpa [w] using (ht.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, w t ∈ U ∧ t < 1 ∧ 0 < t := by
    filter_upwards [hw.eventually_mem hU,
      (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht ht1 ht0
    exact ⟨ht, ht1, ht0⟩
  obtain ⟨t, htU, ht1, ht0⟩ := hevent.exists
  have hepi : g (w t) ≤ (((1-t)*a+t*c : ℝ) : EReal) := by
    have ht := hgh.g_mem.2.2.2 (show (xs,a) ∈ {p | g p.1 ≤ (p.2 : EReal)} by simp [← ha])
      (show (z,c) ∈ {p | g p.1 ≤ (p.2 : EReal)} by simp [← hc])
      (show 0 ≤ 1-t by linarith) (le_of_lt ht0) (show (1-t)+t=1 by ring)
    simpa [w, smul_eq_mul] using ht
  have hgw : g (w t) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hepi
  have hhw : h (w t) ≠ ⊤ := hgh.dom_g_sub hgw
  lift g (w t) to ℝ using ⟨hgw, hgh.g_mem.1 (w t)⟩ with d hd
  lift h (w t) to ℝ using ⟨hhw, hgh.h_mem.1 (w t)⟩ with e he
  have hm := hmin (w t) htU
  have hs := hsub (w t)
  simp only [dcSub, ← ha, ← hb, ← hd, ← he, EReal.coe_ne_top, if_false,
    ← EReal.coe_sub, EReal.coe_le_coe_iff] at hm
  rw [← hb, ← he, ← EReal.coe_add, EReal.coe_le_coe_iff] at hs
  rw [EReal.coe_le_coe_iff] at hepi
  have hinner : inner ℝ y (w t - xs) = t * inner ℝ y (z-xs) := by
    have heq : w t - xs = t • (z-xs) := by dsimp [w]; module
    rw [heq, inner_smul_right]
  rw [hinner] at hs
  rw [← ha, ← EReal.coe_add, EReal.coe_le_coe_iff]
  nlinarith

#print axioms solution
