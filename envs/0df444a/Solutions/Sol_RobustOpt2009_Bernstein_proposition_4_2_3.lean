-- Prove2me | solution 1 for RobustOpt2009.Bernstein.proposition_4_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:47:10.033834+00:00
-- url     : https://prove2.me/submissions/f6a423b0-1846-489f-ba63-ff8fe81e8501

import Mathlib
import Definitions.Def_RobustOpt2009_Bernstein_Setup

open Set
open RobustOpt2009.Bernstein

lemma g79r_pair_single {L : ℕ} (i : Fin L) (s : ℝ) (x : Space L) :
    pairing (Pi.single i s) x = s * x i := by
  simp [pairing, Pi.single_apply]

theorem solution {L M : ℕ} (d : Setup L M)
    (hbot : ∀ u, d.phi u ≠ ⊥)
    (hconv : Convex ℝ {p : Space M × ℝ | d.phi p.1 ≤ (p.2 : EReal)})
    (hrep : representation d.Phi d.phi d.A d.a)
    (hlsc : ∀ c, IsClosed (sublevel d.phi c))
    (hinj : Function.Injective d.A) :
    ∀ c : ℝ, Bornology.IsBounded (sublevel d.phi c) := by
  intro c
  -- key inequality: pairing w (A u + a) ≤ c + Phi w on the sublevel set
  have key : ∀ u ∈ sublevel d.phi c, ∀ w, pairing w (d.A u + d.a) ≤ c + d.Phi w := by
    intro u hu w
    have h1 : ((pairing w (d.A u + d.a) : ℝ) : EReal) - d.phi u ≤ d.Phi w := by
      rw [hrep w]; exact le_iSup (fun u => ((pairing w (d.A u + d.a) : ℝ) : EReal) - d.phi u) u
    have h2 : ((pairing w (d.A u + d.a) : ℝ) : EReal) - (c : EReal) ≤
        ((pairing w (d.A u + d.a) : ℝ) : EReal) - d.phi u :=
      EReal.sub_le_sub le_rfl hu
    have h3 := h2.trans h1
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h3
    linarith
  -- coordinate bound
  set B : ℝ := ∑ i, (|c + d.Phi (Pi.single i 1)| + |c + d.Phi (Pi.single i (-1))| + |d.a i|)
    with hB
  have hcoord : ∀ u ∈ sublevel d.phi c, ∀ i, |d.A u i| ≤ B := by
    intro u hu i
    have hp := key u hu (Pi.single i 1)
    have hm := key u hu (Pi.single i (-1))
    rw [g79r_pair_single] at hp hm
    simp only [Pi.add_apply] at hp hm
    have hle : |c + d.Phi (Pi.single i 1)| + |c + d.Phi (Pi.single i (-1))| + |d.a i| ≤ B := by
      rw [hB]
      exact Finset.single_le_sum (f := fun i => |c + d.Phi (Pi.single i 1)| +
        |c + d.Phi (Pi.single i (-1))| + |d.a i|) (fun j _ => by positivity) (Finset.mem_univ i)
    have e1 := le_abs_self (c + d.Phi (Pi.single i 1))
    have e2 := le_abs_self (c + d.Phi (Pi.single i (-1)))
    have e3 := neg_abs_le (d.a i)
    have e4 := le_abs_self (d.a i)
    have e5 := abs_nonneg (c + d.Phi (Pi.single i 1))
    have e6 := abs_nonneg (c + d.Phi (Pi.single i (-1)))
    rw [abs_le]; constructor <;> linarith
  -- left inverse
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective d.A
    (LinearMap.ker_eq_bot.mpr hinj)
  have hbox : Bornology.IsBounded (d.A '' sublevel d.phi c) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨B, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    refine (pi_norm_le_iff_of_nonneg hB0).mpr fun i => ?_
    rw [Real.norm_eq_abs]; exact hcoord u hu i
  let gc := LinearMap.toContinuousLinearMap g
  have himg := gc.lipschitz.isBounded_image hbox
  refine himg.subset ?_
  intro u hu
  refine ⟨d.A u, ⟨u, hu, rfl⟩, ?_⟩
  show g (d.A u) = u
  rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
