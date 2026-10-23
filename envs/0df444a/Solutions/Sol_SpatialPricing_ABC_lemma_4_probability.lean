-- Prove2me | solution 1 for SpatialPricing.ABC.lemma_4_probability
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:15:55.056987+00:00
-- url     : https://prove2.me/submissions/0d1d34fb-cbe4-4f4e-bdc7-6abc332c8d54

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting
import Definitions.Def_SpatialPricing_ABC_Control

open SpatialPricing.ABC

/-- Counterexample instance: one region, horizon 1, travel time 8, capacity 1,
revenue `x(1-x)`. -/
noncomputable def cexP : Instance where
  N := 1
  T := 1
  τ := fun _ _ => 8
  C := fun _ => 1
  r := fun _ _ _ x => x * (1 - x)

lemma cex_standing : cexP.Standing 2 := by
  refine ⟨le_rfl, le_rfl, fun _ _ => by simp [cexP], fun _ => le_rfl, by norm_num, ?_⟩
  intro t _ i j
  refine ⟨⟨2, by norm_num, ?_⟩, ?_, ?_, by simp [cexP]⟩
  · refine ⟨convex_Icc 0 1, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [cexP, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    have hb : b = 1 - a := by linarith
    subst hb
    nlinarith [sq_nonneg (x - y)]
  · show ContDiff ℝ 2 (fun x : ℝ => x * (1 - x))
    fun_prop
  · intro x hx
    have hd : deriv (fun x : ℝ => x * (1 - x)) = fun x => 1 - 2 * x := by
      funext z
      have : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 * (1 - z) + z * (0 - 1)) z :=
        (hasDerivAt_id z).mul ((hasDerivAt_const z 1).sub (hasDerivAt_id z))
      rw [this.deriv]; ring
    have hd2 : deriv (fun x : ℝ => 1 - 2 * x) = fun _ => -2 := by
      funext z
      have : HasDerivAt (fun x : ℝ => 1 - 2 * x) (0 - 2 * 1) z :=
        (hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul 2)
      rw [this.deriv]; ring
    show |deriv (fun x : ℝ => x * (1 - x)) x| ≤ 2 ∧
      |deriv (deriv (fun x : ℝ => x * (1 - x))) x| ≤ 2 ∧ 0 ≤ x * (1 - x)
    rw [hd, hd2]
    obtain ⟨h0, h1⟩ := hx
    refine ⟨?_, by norm_num, by nlinarith⟩
    rw [abs_le]; constructor <;> linarith

lemma cex_tauMin : cexP.tauMin = 8 := by
  unfold Instance.tauMin
  simp [cexP]

lemma cex_TN : cexP.TN 1 = 1 := by simp [Instance.TN, cexP]

lemma cex_tauN : cexP.tauN 1 = 8 := by simp [Instance.tauN, cex_tauMin]

lemma cex_eps : cexP.epsN 1 = 1 / 8 := by
  simp [Instance.epsN, cex_TN, cex_tauN]

lemma cex_eta : cexP.etaN 1 = 0 := by
  simp [Instance.etaN, cex_eps, cex_tauN]

lemma cex_b_gt : (2 : ℝ) < cexP.bN 1 := by
  rw [Instance.bN, cex_tauN]
  have h3 : ((8 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = 64 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hle
  replace hle := not_lt.mp hle
  have hnn : 0 ≤ (8 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have : ((8 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) ≤ 2 ^ 3 := pow_le_pow_left₀ hnn hle 3
  rw [h3] at this; norm_num at this

theorem solution : ¬ (∀ (P : Instance) (Ψ3 : ℝ) (hP : P.Standing Ψ3)
    (n : ℕ) (hn : 1 ≤ n)
    (hfeas : ∃ x, (P.scale n).DCPFeasible (P.zetaN n) x)
    (hC2 : 2 * P.etaN n / P.bN n < 1),
    1 - 2 * (P.N : ℝ) ^ 2 / (P.bN n * P.TN n) ≤
      (P.scale n).prob
        ((P.scale n).abcRate (P.epsN n) (P.zetaN n) (P.bN n))
        ((P.scale n).inA (P.epsN n) (P.zetaN n) (P.bN n) (P.etaN n))) := by
  intro H
  have hz : cexP.zetaN 1 = 1 / 4 := by
    simp [Instance.zetaN, cex_eps]; norm_num
  have hfeas : ∃ x, (cexP.scale 1).DCPFeasible (cexP.zetaN 1) x := by
    refine ⟨fun _ _ _ => 1 / 2, ?_, ?_⟩
    · intro t ht i
      have ht1 : t = 1 := by simp [Instance.scale, cexP] at ht; omega
      subst ht1
      have hC : ((cexP.scale 1).C i : ℝ) = 1 := by simp [Instance.scale, cexP]
      have hτ : ∀ x, (cexP.scale 1).τ x i = 8 := by simp [Instance.scale, cexP]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.card_Icc, hC, hτ]
      norm_num [Instance.scale, cexP]
    · intro t _ i j
      rw [hz]
      norm_num
  have hC2 : 2 * cexP.etaN 1 / cexP.bN 1 < 1 := by
    rw [cex_eta]; norm_num
  have h := H cexP 2 cex_standing 1 le_rfl hfeas hC2
  -- the event A is empty
  have hA : ∀ ω, ¬ (cexP.scale 1).inA (cexP.epsN 1) (cexP.zetaN 1) (cexP.bN 1)
      (cexP.etaN 1) ω := by
    intro ω hA
    have hbe : ∀ ζ b (i j : Fin (cexP.scale 1).N),
        (cexP.scale 1).batchEnd ζ b i j 1 = 1 := by
      intro ζ b i j
      rw [Instance.batchEnd]
      dsimp only
      split
      · split
        · simp [Instance.scale, cexP]
        · rename_i h _
          have := Nat.find_spec h
          have hb0 : (cexP.scale 1).batchEnd ζ b i j 0 = 0 := rfl
          have hT : (cexP.scale 1).T = 1 := rfl
          have h1 : (cexP.scale 1).batchEnd ζ b i j 0 < Nat.find h := this.1
          have h2 : Nat.find h ≤ (cexP.scale 1).T := this.2.1
          omega
      · simp [Instance.scale, cexP]
    have i0 : Fin (cexP.scale 1).N := ⟨0, by simp [Instance.scale, cexP]⟩
    have h1 := hA i0 i0 1 (by simp [Instance.scale, cexP]) 1 (by
      simp only [Instance.batch, Nat.sub_self, hbe, Finset.mem_Icc]
      simp [Instance.batchEnd])
    rw [cex_eta] at h1
    exact absurd h1 (not_lt.mpr (abs_nonneg _))
  have hprob : (cexP.scale 1).prob
      ((cexP.scale 1).abcRate (cexP.epsN 1) (cexP.zetaN 1) (cexP.bN 1))
      ((cexP.scale 1).inA (cexP.epsN 1) (cexP.zetaN 1) (cexP.bN 1) (cexP.etaN 1)) = 0 := by
    unfold Instance.prob
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg (hA ω)]
  rw [hprob, cex_TN] at h
  have hb := cex_b_gt
  have hN : (cexP.N : ℝ) = 1 := by simp [cexP]
  rw [hN] at h
  have : 2 * (1 : ℝ) ^ 2 / (cexP.bN 1 * 1) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith
