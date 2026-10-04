-- Prove2me | solution 1 for ProcessingNetworks.Subcriticality.ehl_load_eq_ps_load
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:04:52.390759+00:00
-- url     : https://prove2.me/submissions/d3a5da11-8e88-4e98-89e7-3f862c0b262d

import Mathlib

open Matrix

theorem ehl_load_eq_ps_load_core_pow (n : ℕ) :
    (Matrix.of fun _ _ => (1 / 2 : ℝ) : Matrix (Fin 1) (Fin 1) ℝ) ^ n =
      Matrix.of fun _ _ => (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => ext i j; fin_cases i; fin_cases j; simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    simp [pow_succ, Matrix.mul_apply]

theorem solution : ¬ (∀ {I K : ℕ} (S : Fin I → ℕ)
    (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) (A : Matrix (Fin K) (Fin I) ℝ)
    (m : Fin I → ℝ) (alpha : Fin I → ℝ)
    (pinit : (i : Fin I) → Fin (S i) → ℝ)
    (Pph : (i : Fin I) → Matrix (Fin (S i)) (Fin (S i)) ℝ)
    (mph : (i : Fin I) → Fin (S i) → ℝ)
    (_hP_nonneg : ∀ i j, 0 ≤ P i j) (_hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (_hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (_hPph_nonneg : ∀ i s s', 0 ≤ Pph i s s') (_hPph_rowsum : ∀ i s, ∑ s', Pph i s s' ≤ 1)
    (_hPph_transient : ∀ i s s', Filter.Tendsto (fun n => ((Pph i) ^ n) s s') Filter.atTop (nhds 0))
    (nu : (i : Fin I) → Fin (S i) → ℝ)
    (_hnu : ∀ i, ((1 : Matrix (Fin (S i)) (Fin (S i)) ℝ) - (Pph i).transpose).mulVec (nu i)
      = pinit i)
    (_hm : ∀ i, m i = ∑ s, nu i s * mph i s)
    (ltil : ((i : Fin I) × Fin (S i)) → ℝ)
    (Ptil : Matrix ((i : Fin I) × Fin (S i)) ((i : Fin I) × Fin (S i)) ℝ)
    (atil : ((i : Fin I) × Fin (S i)) → ℝ)
    (_hltil : ∀ (i : Fin I) (s : Fin (S i)), ltil ⟨i, s⟩ = lam i * pinit i s)
    (_hPtil_same : ∀ (i : Fin I) (s s' : Fin (S i)), Ptil ⟨i, s⟩ ⟨i, s'⟩ = Pph i s s')
    (_hPtil_diff : ∀ (i j : Fin I), i ≠ j → ∀ (s : Fin (S i)) (s' : Fin (S j)),
      Ptil ⟨i, s⟩ ⟨j, s'⟩ = (1 - ∑ s'' : Fin (S i), Pph i s s'') * P i j * pinit j s')
    (_hatil : ((1 : Matrix ((i : Fin I) × Fin (S i)) ((i : Fin I) × Fin (S i)) ℝ)
      - Ptil.transpose).mulVec atil = ltil)
    (_halpha : ((1 : Matrix (Fin I) (Fin I) ℝ) - P.transpose).mulVec alpha = lam),
    (fun k => ∑ c : (i : Fin I) × Fin (S i), A k c.1 * mph c.1 c.2 * atil c)
      = fun k => ∑ i, A k i * m i * alpha i) := by
  intro h
  have := h (I := 1) (K := 1) (fun _ => 1) (fun _ => 1) (Matrix.of fun _ _ => 1 / 2) (fun _ _ => 1)
    (fun _ => 1) (fun _ => 2) (fun _ _ => 1) (fun _ => 0) (fun _ _ => 1)
    (fun _ _ => by simp) (fun _ => by simp; norm_num)
    (fun i j => by
      simp only [ehl_load_eq_ps_load_core_pow, Matrix.of_apply]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (fun _ _ _ => le_refl _) (fun _ _ => by simp)
    (fun _ _ _ => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [zero_pow (by omega)]; rfl)
    (fun _ _ => 1)
    (fun i => by ext s; simp)
    (fun i => by simp)
    (fun _ => 1) 0 (fun _ => 1)
    (fun i s => by simp)
    (fun i s s' => rfl)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (by ext c; simp)
    (by ext i; fin_cases i; simp [Matrix.mulVec, dotProduct]; norm_num)
  have h0 := congrFun this 0
  simp at h0


