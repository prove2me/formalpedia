-- Prove2me | solution 1 for TaoAnDCA.GlobalOpt.epsSubdiff_subset_iff_eq8
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:12:48.59246+00:00
-- url     : https://prove2.me/submissions/45cbfb74-6225-476f-a5af-db8bfeb80219

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt

private lemma conj_ne_bot {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (y : EuclideanSpace ℝ (Fin n)) : CondatPD.FinDim.conj f y ≠ ⊥ := by
  obtain ⟨z, hz⟩ := hf.2.1
  lift f z to ℝ using ⟨hz, hf.1 z⟩ with a ha
  have hb := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - f z) z
  rw [← ha, ← EReal.coe_sub] at hb
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb

private lemma rearrange (a b : ℝ) (v : EReal) :
    (a : EReal) + v ≤ (b : EReal) ↔ v ≤ ((b - a : ℝ) : EReal) := by
  cases v with
  | bot => simp only [EReal.add_bot, bot_le, true_iff]
  | top => simp only [EReal.coe_add_top, top_le_iff, EReal.coe_ne_top, false_iff,
      ← EReal.coe_sub, EReal.coe_ne_top, not_false_eq_true]
  | coe r =>
    simp only [← EReal.coe_add, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

private lemma eps_iff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (x y : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    y ∈ epsSubdiff f ε x ↔
      f x + CondatPD.FinDim.conj f y ≤ ((inner ℝ x y + ε : ℝ) : EReal) := by
  by_cases hx : f x = ⊤
  · simp only [epsSubdiff, Set.mem_setOf_eq, hx, ne_eq, not_true_eq_false, false_and,
      EReal.top_add_of_ne_bot (conj_ne_bot f hf y), top_le_iff, EReal.coe_ne_top]
  lift f x to ℝ using ⟨hx, hf.1 x⟩ with a ha
  simp only [epsSubdiff, Set.mem_setOf_eq, ← ha, ne_eq, EReal.coe_ne_top, not_false_eq_true,
    true_and]
  rw [rearrange a (inner ℝ x y + ε), CondatPD.FinDim.conj, iSup_le_iff]
  apply forall_congr'
  intro z
  cases hz : f z with
  | bot => exact (hf.1 z hz).elim
  | top => simp [EReal.sub_top]
  | coe b =>
    simp only [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [inner_sub_left, real_inner_comm y z]
    constructor <;> intro h <;> linarith

theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    (∀ ε : ℝ, 0 < ε → epsSubdiff h ε x ⊆ epsSubdiff g ε x) ↔
      ∀ ε : ℝ, 0 < ε → ∀ y : EuclideanSpace ℝ (Fin n),
        ((inner ℝ x y + ε : ℝ) : EReal) ≥ h x + CondatPD.FinDim.conj h y →
          ((inner ℝ x y + ε : ℝ) : EReal) ≥ g x + CondatPD.FinDim.conj g y := by
  simp only [Set.subset_def, eps_iff g hgh.g_mem, eps_iff h hgh.h_mem]

#print axioms solution
