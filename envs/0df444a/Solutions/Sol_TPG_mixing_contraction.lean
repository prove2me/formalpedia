-- Prove2me | solution 1 for TPG.mixing_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:31:45.220979+00:00
-- url     : https://prove2.me/submissions/05d2dba7-13bb-4e75-b29f-5355104fc0de

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPGMixC

variable {S : Type} [Fintype S]

/-- One step of a pure kernel contracts the `ℓ¹` norm of a zero-sum row vector by `γ`
(Jordan decomposition of the vector into two probability vectors). -/
theorem pure_step (E : Env S) (T : ℕ) (γ : ℝ) (hmix : E.Mixing T γ) (t : ℕ) (ht : t < T)
    (z : Bool) (μ : S → ℝ) (hμ : ∑ x, μ x = 0) :
    ∑ x, |Matrix.vecMul μ (E.P t z) x| ≤ γ * ∑ x, |μ x| := by
  have hpos : ∀ x, 0 ≤ max (μ x) 0 := fun x => le_max_right _ _
  have hneg : ∀ x, 0 ≤ max (-μ x) 0 := fun x => le_max_right _ _
  have hdecomp : ∀ x, max (μ x) 0 - max (-μ x) 0 = μ x := by
    intro x
    rcases le_total 0 (μ x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have habs : ∀ x, |μ x| = max (μ x) 0 + max (-μ x) 0 := by
    intro x
    rcases le_total 0 (μ x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ x, max (μ x) 0 := ⟨_, rfl⟩
  have hc' : ∑ x, max (-μ x) 0 = c := by
    have h1 : ∑ x, μ x = ∑ x, max (μ x) 0 - ∑ x, max (-μ x) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => (hdecomp x).symm
    linarith
  have hl1 : ∑ x, |μ x| = 2 * c := by
    rw [Finset.sum_congr rfl fun x _ => habs x, Finset.sum_add_distrib, hc', ← hc]; ring
  have hc0 : 0 ≤ c := by rw [hc]; exact Finset.sum_nonneg fun x _ => hpos x
  rcases hc0.eq_or_lt with h0 | hcpos
  · have h1 : ∑ x, |μ x| = 0 := by rw [hl1, ← h0]; ring
    have hμ0 : μ = 0 := by
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => abs_nonneg (μ x)).1 h1 x
        (Finset.mem_univ x)
      simpa using this
    rw [hμ0]
    simp
  · have hf' : IsProbVec (fun x => max (μ x) 0 / c) :=
      ⟨fun x => div_nonneg (hpos x) hc0, by rw [← Finset.sum_div, ← hc]; exact div_self hcpos.ne'⟩
    have hf : IsProbVec (fun x => max (-μ x) 0 / c) :=
      ⟨fun x => div_nonneg (hneg x) hc0, by rw [← Finset.sum_div, hc']; exact div_self hcpos.ne'⟩
    have key := hmix t ht z _ _ hf hf'
    have hfeq : (fun x => max (μ x) 0 / c) - (fun x => max (-μ x) 0 / c) = c⁻¹ • μ := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← sub_div, hdecomp x, div_eq_inv_mul]
    have h1 : tvDist (Matrix.vecMul (fun x => max (μ x) 0 / c) (E.P t z))
        (Matrix.vecMul (fun x => max (-μ x) 0 / c) (E.P t z))
        = (1 / 2) * (c⁻¹ * ∑ x, |Matrix.vecMul μ (E.P t z) x|) := by
      unfold tvDist
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h2 := congrFun (Matrix.sub_vecMul (E.P t z) (fun x => max (μ x) 0 / c)
        (fun x => max (-μ x) 0 / c)) x
      rw [hfeq, Matrix.smul_vecMul] at h2
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, abs_mul, abs_of_pos (inv_pos.2 hcpos)]
    have h3 : tvDist (fun x => max (μ x) 0 / c) (fun x => max (-μ x) 0 / c)
        = (1 / 2) * (c⁻¹ * ∑ x, |μ x|) := by
      unfold tvDist
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h2 := congrFun hfeq x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
      rw [h2, abs_mul, abs_of_pos (inv_pos.2 hcpos)]
    rw [h1, h3] at key
    have hcinv : 0 < c⁻¹ := inv_pos.2 hcpos
    have key2 : c⁻¹ * ∑ x, |Matrix.vecMul μ (E.P t z) x| ≤ c⁻¹ * (γ * ∑ x, |μ x|) := by
      nlinarith [key]
    exact le_of_mul_le_mul_left key2 hcinv

/-- One step of the mixture kernel `P_θ^t` contracts zero-sum row vectors by `γ`. -/
theorem mix_step (E : Env S) (T : ℕ) (γ : ℝ) (hmix : E.Mixing T γ) (t : ℕ) (ht : t < T)
    (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1) (μ : S → ℝ) (hμ : ∑ x, μ x = 0) :
    ∑ x, |Matrix.vecMul μ (E.PMix θ t) x| ≤ γ * ∑ x, |μ x| := by
  have h1 := pure_step E T γ hmix t ht true μ hμ
  have h0 := pure_step E T γ hmix t ht false μ hμ
  have hpt : ∀ x, |Matrix.vecMul μ (E.PMix θ t) x|
      ≤ θ * |Matrix.vecMul μ (E.P t true) x| + (1 - θ) * |Matrix.vecMul μ (E.P t false) x| := by
    intro x
    have : Matrix.vecMul μ (E.PMix θ t) x
        = θ * Matrix.vecMul μ (E.P t true) x + (1 - θ) * Matrix.vecMul μ (E.P t false) x := by
      unfold Env.PMix
      rw [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    calc |θ * Matrix.vecMul μ (E.P t true) x + (1 - θ) * Matrix.vecMul μ (E.P t false) x|
        ≤ |θ * Matrix.vecMul μ (E.P t true) x| + |(1 - θ) * Matrix.vecMul μ (E.P t false) x| :=
          abs_add_le _ _
      _ = θ * |Matrix.vecMul μ (E.P t true) x| + (1 - θ) * |Matrix.vecMul μ (E.P t false) x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hθ.1, abs_of_nonneg (by linarith [hθ.2] : (0:ℝ) ≤ 1 - θ)]
  calc ∑ x, |Matrix.vecMul μ (E.PMix θ t) x|
      ≤ ∑ x, (θ * |Matrix.vecMul μ (E.P t true) x|
          + (1 - θ) * |Matrix.vecMul μ (E.P t false) x|) := Finset.sum_le_sum fun x _ => hpt x
    _ = θ * ∑ x, |Matrix.vecMul μ (E.P t true) x|
          + (1 - θ) * ∑ x, |Matrix.vecMul μ (E.P t false) x| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ θ * (γ * ∑ x, |μ x|) + (1 - θ) * (γ * ∑ x, |μ x|) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hθ.1)
          (mul_le_mul_of_nonneg_left h0 (by linarith [hθ.2]))
    _ = γ * ∑ x, |μ x| := by ring

/-- Multiplying a row vector by the mixture kernel preserves the sum of its entries. -/
theorem sum_vecMul_PMix (E : Env S) (θ : ℝ) (t : ℕ) (μ : S → ℝ) :
    ∑ x, Matrix.vecMul μ (E.PMix θ t) x = ∑ x, μ x := by
  have hrow : ∀ y, ∑ x, E.PMix θ t y x = 1 := by
    intro y
    unfold Env.PMix
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, E.P_row_sum, E.P_row_sum]
    ring
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, hrow y, mul_one]

end TPGMixC

theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ T)
    (μ : S → ℝ) (hμ : ∑ x, μ x = 0) :
    ∑ x, |Matrix.vecMul μ (((List.Ico a b).map (fun s => E.PMix (q s) s)).prod) x|
      ≤ γ ^ (b - a) * ∑ x, |μ x| := by
  have main : ∀ b, a ≤ b → b ≤ T →
      (∑ x, Matrix.vecMul μ (((List.Ico a b).map (fun s => E.PMix (q s) s)).prod) x = 0) ∧
      ∑ x, |Matrix.vecMul μ (((List.Ico a b).map (fun s => E.PMix (q s) s)).prod) x|
        ≤ γ ^ (b - a) * ∑ x, |μ x| := by
    intro b hab
    induction b, hab using Nat.le_induction with
    | base =>
      intro _
      simp [List.Ico.self_empty, hμ]
    | succ n hn ih =>
      intro hnT
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      have hprod : ((List.Ico a (n + 1)).map (fun s => E.PMix (q s) s)).prod
          = ((List.Ico a n).map (fun s => E.PMix (q s) s)).prod * E.PMix (q n) n := by
        rw [List.Ico.succ_top hn, List.map_append, List.prod_append]
        simp
      rw [hprod, ← Matrix.vecMul_vecMul]
      refine ⟨?_, ?_⟩
      · rw [TPGMixC.sum_vecMul_PMix]; exact ih0
      · have hstep := TPGMixC.mix_step E T γ hmix n (by omega) (q n) (hq n) _ ih0
        have hexp : n + 1 - a = (n - a) + 1 := by omega
        rw [hexp, pow_succ]
        calc _ ≤ γ * ∑ x, |Matrix.vecMul μ (((List.Ico a n).map (fun s => E.PMix (q s) s)).prod) x| :=
              hstep
          _ ≤ γ * (γ ^ (n - a) * ∑ x, |μ x|) := mul_le_mul_of_nonneg_left ih1 hγ
          _ = γ ^ (n - a) * γ * ∑ x, |μ x| := by ring
  exact (main b hab hb).2
