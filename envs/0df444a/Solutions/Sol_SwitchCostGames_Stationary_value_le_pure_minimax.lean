-- Prove2me | solution 1 for SwitchCostGames.Stationary.value_le_pure_minimax
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:20:17.432774+00:00
-- url     : https://prove2.me/submissions/acf4114d-cb6b-4f4e-8696-552b3dcf1b2d

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

open SwitchCostGames.Stationary

namespace SCGAux

theorem take_snoc {m n T : ℕ} (h : History m n T) (x : Fin m × Fin n) (s : ℕ) (hs : s ≤ T) :
    History.take (Fin.snoc h x : History m n (T + 1)) s (hs.trans T.le_succ) =
      History.take h s hs := by
  funext r
  have hr : (r : ℕ) < T := lt_of_lt_of_le r.isLt hs
  simp [History.take, Fin.snoc, hr, Fin.castLT]
  rfl

theorem take_self {m n T : ℕ} (h : History m n T) : History.take h T le_rfl = h := by
  funext r
  simp [History.take]

theorem histProb_snoc {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) (h : History m n T)
    (x : Fin m × Fin n) :
    histProb σ τ (Fin.snoc h x : History m n (T + 1)) =
      histProb σ τ h * (σ.act T h x.1 * τ.act T h x.2) := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    have e1 : (Fin.snoc h x : History m n (T + 1)) (Fin.castSucc s) = h s := Fin.snoc_castSucc ..
    have e2 := take_snoc h x s s.isLt.le
    simp only [Fin.val_castSucc]
    rw [e1, e2]
  · have e1 : (Fin.snoc h x : History m n (T + 1)) (Fin.last T) = x := Fin.snoc_last ..
    have e2 := take_snoc h x T le_rfl
    simp only [Fin.val_last]
    rw [e1, e2, take_self]

theorem histProb_nonneg {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n)
    (h : History m n T) : 0 ≤ histProb σ τ h := by
  unfold histProb
  exact Finset.prod_nonneg (fun s _ =>
    mul_nonneg ((σ.act_mem _ _).1 _) ((τ.act_mem _ _).1 _))

theorem sum_histProb {m n : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) :
    ∀ T : ℕ, ∑ h : History m n T, histProb σ τ h = 1
  | 0 => by simp [histProb]
  | T + 1 => by
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => Fin m × Fin n)).sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have key : ∀ h : History m n T,
        ∑ x : Fin m × Fin n, histProb σ τ (Fin.snoc h x : History m n (T + 1)) =
          histProb σ τ h := by
      intro h
      simp only [histProb_snoc]
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      have : ∑ i : Fin m, ∑ j : Fin n, σ.act T h i * τ.act T h j = 1 := by
        rw [← Finset.sum_mul_sum, (σ.act_mem _ _).2, (τ.act_mem _ _).2, one_mul]
      simp only at this ⊢
      rw [this, mul_one]
    calc ∑ h : History m n T, ∑ x : Fin m × Fin n,
          histProb σ τ (Fin.snoc h x : History m n (T + 1))
        = ∑ h : History m n T, histProb σ τ h := Finset.sum_congr rfl (fun h _ => key h)
      _ = 1 := sum_histProb σ τ T

theorem prevAction_of_const {m n : ℕ} [NeZero n] (j : Fin n) :
    ∀ {t : ℕ} (h : History m n t), (∀ r, (h r).2 = j) → t ≠ 0 → prevAction h = j
  | 0, _, _, ht => absurd rfl ht
  | t + 1, h, hj, _ => hj (Fin.last t)

end SCGAux

open SCGAux

theorem solution {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c v : ℝ)
    (hc : 0 ≤ c) (hv : IsValue G c v) :
    v ≤ Finset.univ.inf' Finset.univ_nonempty
      (fun j : Fin n => Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m => G.A i j)) := by
  classical
  obtain ⟨σ, -, -, -, hσ, -⟩ := hv
  apply Finset.le_inf'
  intro j _
  set M := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m => G.A i j) with hM
  set mA := Finset.univ.inf' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2)
  set K := c * G.S 0 j with hK
  -- the constant pure strategy `j` of player 2
  let τ : Strategy2 m n :=
    { act := fun _ _ => BlottoLP.Flow.pureMixed j
      act_mem := fun _ _ => by
        refine ⟨fun a => ?_, ?_⟩
        · unfold BlottoLP.Flow.pureMixed; split_ifs <;> norm_num
        · simp [BlottoLP.Flow.pureMixed] }
  refine (hσ τ).trans ?_
  -- positive-probability histories only use column `j`
  have hsupp : ∀ (T : ℕ) (h : History m n T), histProb σ τ h ≠ 0 → ∀ s, (h s).2 = j := by
    intro T h hne s
    unfold histProb at hne
    have := (Finset.prod_ne_zero_iff.1 hne) s (Finset.mem_univ _)
    have h2 : τ.act s (h.take s s.isLt.le) (h s).2 ≠ 0 := right_ne_zero_of_mul this
    simp only [τ, BlottoLP.Flow.pureMixed] at h2
    by_contra hcon
    exact h2 (if_neg hcon)
  -- upper bound on the stage-sum of a history using only column `j`
  have hrew_up : ∀ (T : ℕ) (h : History m n T), (∀ s, (h s).2 = j) →
      (∑ s : Fin T, (G.A (h s).1 (h s).2 +
        c * G.S (prevAction (h.take s s.isLt.le)) (h s).2)) ≤ T * M + K := by
    intro T h hj
    rw [Finset.sum_add_distrib]
    have h1 : ∑ s : Fin T, G.A (h s).1 (h s).2 ≤ T * M := by
      calc ∑ s : Fin T, G.A (h s).1 (h s).2 ≤ ∑ _s : Fin T, M := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            rw [hj s]
            exact Finset.le_sup' (fun i : Fin m => G.A i j) (Finset.mem_univ _)
        _ = T * M := by simp
    have h2 : ∑ s : Fin T, c * G.S (prevAction (h.take s s.isLt.le)) (h s).2 ≤ K := by
      cases T with
      | zero => simp [hK]; exact mul_nonneg hc (G.S_nonneg _ _)
      | succ T' =>
        rw [Fin.sum_univ_succ]
        have h0 : c * G.S (prevAction (h.take ((0 : Fin (T' + 1)) : ℕ)
            (0 : Fin (T' + 1)).isLt.le)) (h 0).2 = K := by
          rw [hj 0]; rfl
        have hrest : ∀ s : Fin T', c * G.S (prevAction (h.take ((Fin.succ s : Fin (T' + 1)) : ℕ)
            (Fin.succ s).isLt.le)) (h (Fin.succ s)).2 = 0 := by
          intro s
          have hp : prevAction (h.take ((Fin.succ s : Fin (T' + 1)) : ℕ) (Fin.succ s).isLt.le)
              = j := prevAction_of_const j _ (fun r => hj _) (by simp)
          rw [hp, hj, G.S_diag, mul_zero]
        rw [h0, Finset.sum_congr rfl (fun s _ => hrest s)]
        simp
    linarith
  -- lower bound on the stage-sum of any history
  have hrew_lo : ∀ (T : ℕ) (h : History m n T),
      (T : ℝ) * mA ≤ ∑ s : Fin T, (G.A (h s).1 (h s).2 +
        c * G.S (prevAction (h.take s s.isLt.le)) (h s).2) := by
    intro T h
    calc (T : ℝ) * mA = ∑ _s : Fin T, mA := by simp
      _ ≤ _ := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        have : mA ≤ G.A (h s).1 (h s).2 :=
          Finset.inf'_le (fun p : Fin m × Fin n => G.A p.1 p.2) (Finset.mem_univ (h s))
        have : 0 ≤ c * G.S (prevAction (h.take s s.isLt.le)) (h s).2 :=
          mul_nonneg hc (G.S_nonneg _ _)
        linarith
  have hET_up : ∀ T : ℕ, expectedTotal G c σ τ T ≤ T * M + K := by
    intro T
    unfold expectedTotal
    calc _ ≤ ∑ h : History m n T, histProb σ τ h * (T * M + K) := by
          refine Finset.sum_le_sum (fun h _ => ?_)
          by_cases hp : histProb σ τ h = 0
          · rw [hp]; simp
          · exact mul_le_mul_of_nonneg_left (hrew_up T h (hsupp T h hp))
              (histProb_nonneg σ τ h)
      _ = T * M + K := by rw [← Finset.sum_mul, sum_histProb, one_mul]
  have hET_lo : ∀ T : ℕ, (T : ℝ) * mA ≤ expectedTotal G c σ τ T := by
    intro T
    unfold expectedTotal
    calc (T : ℝ) * mA = ∑ h : History m n T, histProb σ τ h * (T * mA) := by
          rw [← Finset.sum_mul, sum_histProb, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun h _ =>
          mul_le_mul_of_nonneg_left (hrew_lo T h) (histProb_nonneg σ τ h))
  -- pass to the liminf
  unfold payoff
  have hg : Filter.Tendsto (fun T : ℕ => M + K / (T : ℝ)) Filter.atTop (nhds M) := by
    have := tendsto_const_div_atTop_nhds_zero_nat K
    simpa using (tendsto_const_nhds (x := M)).add this
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      expectedTotal G c σ τ T / T ≤ M + K / (T : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_le_iff₀ hTpos, add_mul, div_mul_cancel₀ _ hTpos.ne']
    have := hET_up T
    linarith
  have hlo : ∀ᶠ T : ℕ in Filter.atTop, mA ≤ expectedTotal G c σ τ T / T := by
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [le_div_iff₀ hTpos, mul_comm]
    exact hET_lo T
  calc Filter.liminf (fun T : ℕ => expectedTotal G c σ τ T / T) Filter.atTop
      ≤ Filter.liminf (fun T : ℕ => M + K / (T : ℝ)) Filter.atTop :=
        Filter.liminf_le_liminf hle (Filter.isBoundedUnder_of_eventually_ge hlo)
          hg.isCoboundedUnder_ge
    _ = M := hg.liminf_eq
