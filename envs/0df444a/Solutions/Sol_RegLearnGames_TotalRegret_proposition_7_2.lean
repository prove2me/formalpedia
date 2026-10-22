-- Prove2me | solution 2 for RegLearnGames.TotalRegret.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:39:25.550314+00:00
-- url     : https://prove2.me/submissions/789ceb6a-409e-4b5f-b97c-b18378476687

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
set_option autoImplicit false

open RegLearnGames.TotalRegret

lemma rl_l1_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) : l1 (c • v) = |c| * l1 v := by
  unfold l1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [abs_mul]

lemma rl_l1_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ l1 v :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma rl_l1_neg {d : ℕ} (v : Fin d → ℝ) : l1 (-v) = l1 v := by
  have := rl_l1_smul (-1) v
  simpa using this

lemma rl_dot_le {d : ℕ} (x y : Fin d → ℝ) : x ⬝ᵥ y ≤ l1 x * ‖y‖ := by
  unfold l1 dotProduct
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc x i * y i ≤ |x i * y i| := le_abs_self _
    _ = |x i| * |y i| := abs_mul _ _
    _ ≤ |x i| * ‖y‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := norm_le_pi_norm y i
        simpa using this

lemma rl_dyadic {d : ℕ} (R : (Fin d → ℝ) → ℝ)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (a b : Fin d → ℝ) (ha : a ∈ stdSimplex ℝ (Fin d)) (hb : b ∈ stdSimplex ℝ (Fin d)) :
    ∀ k : ℕ, ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b ∈ stdSimplex ℝ (Fin d)) ∧
      R ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b) ≤
        ((1 / 2 : ℝ) ^ k) * R b + (1 - (1 / 2 : ℝ) ^ k) * R a -
          (1 / 2) * ((1 / 2 : ℝ) ^ k) * (1 - (1 / 2 : ℝ) ^ k) * (l1 (a - b)) ^ 2 := by
  intro k
  induction k with
  | zero =>
    simp only [pow_zero, sub_self, zero_smul, one_smul, zero_add]
    refine ⟨hb, ?_⟩
    simp
  | succ k ih =>
    obtain ⟨hmem, hle⟩ := ih
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    have hp1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hid : (1 / 2 : ℝ) • (a + ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b))
        = (1 - (1 / 2 : ℝ) ^ (k + 1)) • a + ((1 / 2 : ℝ) ^ (k + 1)) • b := by
      rw [pow_succ]
      module
    have hmem2 : (1 - (1 / 2 : ℝ) ^ (k + 1)) • a + ((1 / 2 : ℝ) ^ (k + 1)) • b ∈ stdSimplex ℝ (Fin d) := by
      have hp1' : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact (convex_stdSimplex ℝ (Fin d)) ha hb (by linarith) (by positivity) (by ring)
    refine ⟨hmem2, ?_⟩
    have h1 := hR a ha _ hmem
    rw [hid] at h1
    have h2 : a - ((1 - (1 / 2 : ℝ) ^ k) • a + ((1 / 2 : ℝ) ^ k) • b) = ((1 / 2 : ℝ) ^ k) • (a - b) := by
      module
    rw [h2, rl_l1_smul, abs_of_nonneg hp0] at h1
    have h3 : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by rw [pow_succ]; ring
    rw [h3] at h1 ⊢
    set p := (1 / 2 : ℝ) ^ k
    nlinarith [h1, hle]

lemma rl_strong {d : ℕ} (R : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (c w g : Fin d → ℝ) (hw : w ∈ stdSimplex ℝ (Fin d)) (hg : g ∈ stdSimplex ℝ (Fin d))
    (hopt : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c - R v / η ≤ w ⬝ᵥ c - R w / η) :
    (l1 (w - g)) ^ 2 / (2 * η) ≤ (R g - R w) / η - (g - w) ⬝ᵥ c := by
  have hk : ∀ k : ℕ, (l1 (w - g)) ^ 2 / (2 * η) * (1 - (1 / 2 : ℝ) ^ k) ≤ (R g - R w) / η - (g - w) ⬝ᵥ c := by
    intro k
    obtain ⟨hmem, hle⟩ := rl_dyadic R hR w g hw hg k
    have h1 := hopt _ hmem
    set p := (1 / 2 : ℝ) ^ k with hp
    have hp0 : 0 < p := by positivity
    have hdot : ((1 - p) • w + p • g) ⬝ᵥ c = w ⬝ᵥ c + p * ((g - w) ⬝ᵥ c) := by
      simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]
      ring
    rw [hdot] at h1
    have h2 : R ((1 - p) • w + p • g) / η ≤
        (p * R g + (1 - p) * R w - (1 / 2) * p * (1 - p) * (l1 (w - g)) ^ 2) / η :=
      div_le_div_of_nonneg_right hle hη.le
    have h3 : 0 ≤ p * ((R g - R w) / η - (g - w) ⬝ᵥ c) - (1 / (2 * η)) * p * (1 - p) * (l1 (w - g)) ^ 2 := by
      have e : (p * R g + (1 - p) * R w - (1 / 2) * p * (1 - p) * (l1 (w - g)) ^ 2) / η
          = p * R g / η + (1 - p) * R w / η - (1 / (2 * η)) * p * (1 - p) * (l1 (w - g)) ^ 2 := by
        field_simp
      have e2 : p * ((R g - R w) / η) = p * R g / η - p * R w / η := by ring
      have e3 : (1 - p) * R w / η = R w / η - p * R w / η := by ring
      nlinarith [h1, h2, e, e2, e3]
    have h4 : 0 ≤ ((R g - R w) / η - (g - w) ⬝ᵥ c) - (1 / (2 * η)) * (1 - p) * (l1 (w - g)) ^ 2 := by
      have : 0 ≤ p * (((R g - R w) / η - (g - w) ⬝ᵥ c) - (1 / (2 * η)) * (1 - p) * (l1 (w - g)) ^ 2) := by
        nlinarith [h3]
      exact (mul_nonneg_iff_of_pos_left hp0).1 this
    have e4 : (l1 (w - g)) ^ 2 / (2 * η) * (1 - p) = (1 / (2 * η)) * (1 - p) * (l1 (w - g)) ^ 2 := by ring
    linarith
  by_contra hcon
  push_neg at hcon
  set X := (l1 (w - g)) ^ 2 / (2 * η) with hX
  set Y := (R g - R w) / η - (g - w) ⬝ᵥ c
  have hX0 : 0 ≤ X := by positivity
  have hpos : 0 < X - Y := by linarith
  obtain ⟨k, hk'⟩ := exists_pow_lt_of_lt_one (show 0 < (X - Y) / (X + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have := hk k
  have h5 : X * (1 / 2 : ℝ) ^ k < X - Y := by
    calc X * (1 / 2 : ℝ) ^ k ≤ (X + 1) * (1 / 2 : ℝ) ^ k := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < (X + 1) * ((X - Y) / (X + 1)) := by
          apply mul_lt_mul_of_pos_left hk' (by positivity)
      _ = X - Y := by field_simp
  nlinarith

lemma rl_key {d : ℕ} (R : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (c c' w w' : Fin d → ℝ) (hw : w ∈ stdSimplex ℝ (Fin d)) (hw' : w' ∈ stdSimplex ℝ (Fin d))
    (hopt : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c - R v / η ≤ w ⬝ᵥ c - R w / η)
    (hopt' : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c' - R v / η ≤ w' ⬝ᵥ c' - R w' / η) :
    l1 (w - w') ≤ η * ‖c - c'‖ := by
  have h1 := rl_strong R η hη hR c w w' hw hw' hopt
  have h2 := rl_strong R η hη hR c' w' w hw' hw hopt'
  have hl : l1 (w' - w) = l1 (w - w') := by
    rw [← rl_l1_neg (w - w')]; congr 1; abel
  rw [hl] at h2
  set D := l1 (w - w') with hD
  have hD0 : 0 ≤ D := rl_l1_nonneg _
  have hdot : (w - w') ⬝ᵥ (c - c') ≤ D * ‖c - c'‖ := rl_dot_le _ _
  have e1 : (w' - w) ⬝ᵥ c = -((w - w') ⬝ᵥ c) := by
    rw [← neg_sub, neg_dotProduct]
  have e2 : (w - w') ⬝ᵥ (c - c') = (w - w') ⬝ᵥ c - (w - w') ⬝ᵥ c' := by
    rw [dotProduct_sub]
  have h3 : D ^ 2 / η ≤ D * ‖c - c'‖ := by
    have : D ^ 2 / (2 * η) + D ^ 2 / (2 * η) = D ^ 2 / η := by field_simp; ring
    rw [← this]
    have e3 : (R w' - R w) / η + (R w - R w') / η = 0 := by ring
    linarith
  rcases hD0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : D ^ 2 ≤ η * (D * ‖c - c'‖) := by
      rw [div_le_iff₀ hη] at h3; linarith
    nlinarith

lemma rl_Icc_eq {d : ℕ} (u : ℕ → Fin d → ℝ) (t : ℕ) :
    ∑ s ∈ Finset.Icc 1 t, u s = ∑ s ∈ Finset.Ico 1 (t + 1), u s := by
  rw [Finset.Ico_add_one_right_eq_Icc]

lemma rl_Ico_succ {d : ℕ} (u : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∑ s ∈ Finset.Ico 1 (t + 1), u s = ∑ s ∈ Finset.Ico 1 t, u s + u t :=
  Finset.sum_Ico_succ_top ht _

lemma rl_lem20 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g) :
    ∀ t : ℕ, l1 (w t - g t) ≤ η * ‖M t - u t‖ ∧ l1 (g t - w (t + 1)) ≤ η * ‖M (t + 1)‖ := by
  have hR := h𝓡.2
  intro t
  constructor
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · have h := rl_key 𝓡 η hη hR 0 0 (w 0) (g 0) hw.1.1 (hg 0).1
        (by
          intro v hv
          simp only [dotProduct_zero, zero_sub, neg_le_neg_iff]
          exact div_le_div_of_nonneg_right (hw.1.2 v hv) hη.le)
        (by
          intro v hv
          have := (hg 0).2 v hv
          simpa using this)
      simp only [sub_self, norm_zero, mul_zero] at h
      exact h.trans (by positivity)
    · have h := rl_key 𝓡 η hη hR ((∑ s ∈ Finset.Ico 1 t, u s) + M t) (∑ s ∈ Finset.Icc 1 t, u s) (w t) (g t)
        (hw.2 t ht).1 (hg t).1 (hw.2 t ht).2 (hg t).2
      have e : ((∑ s ∈ Finset.Ico 1 t, u s) + M t) - (∑ s ∈ Finset.Icc 1 t, u s) = M t - u t := by
        rw [rl_Icc_eq, rl_Ico_succ u t ht]; abel
      rw [e] at h
      exact h
  · have h := rl_key 𝓡 η hη hR (∑ s ∈ Finset.Icc 1 t, u s) ((∑ s ∈ Finset.Ico 1 (t + 1), u s) + M (t + 1))
        (g t) (w (t + 1)) (hg t).1 (hw.2 (t + 1) (by omega)).1 (hg t).2 (hw.2 (t + 1) (by omega)).2
    have e : (∑ s ∈ Finset.Icc 1 t, u s) - ((∑ s ∈ Finset.Ico 1 (t + 1), u s) + M (t + 1)) = -M (t + 1) := by
      rw [rl_Icc_eq]; abel
    rw [e, norm_neg] at h
    exact h

lemma rl_zero {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g) :
    l1 (w 0 - g 0) = 0 := by
  have h := rl_key 𝓡 η hη h𝓡.2 0 0 (w 0) (g 0) hw.1.1 (hg 0).1
    (by
      intro v hv
      simp only [dotProduct_zero, zero_sub, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right (hw.1.2 v hv) hη.le)
    (by
      intro v hv
      have := (hg 0).2 v hv
      simpa using this)
  simp only [sub_self, norm_zero, mul_zero] at h
  exact le_antisymm h (rl_l1_nonneg _)

lemma rl_l1_add {d : ℕ} (x y : Fin d → ℝ) : l1 (x + y) ≤ l1 x + l1 y := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa using abs_add_le (x i) (y i)

lemma rl_quad {d : ℕ} (R : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (hR : ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      R ((1 / 2 : ℝ) • (a + b)) ≤ (R a + R b) / 2 - (l1 (a - b)) ^ 2 / 8)
    (c w g : Fin d → ℝ) (hw : w ∈ stdSimplex ℝ (Fin d)) (hg : g ∈ stdSimplex ℝ (Fin d))
    (hopt : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ c - R v / η ≤ w ⬝ᵥ c - R w / η) :
    g ⬝ᵥ c - R g / η + (l1 (w - g)) ^ 2 / (2 * η) ≤ w ⬝ᵥ c - R w / η := by
  have h := rl_strong R η hη hR c w g hw hg hopt
  have e : (g - w) ⬝ᵥ c = g ⬝ᵥ c - w ⬝ᵥ c := sub_dotProduct _ _ _
  have e2 : (R g - R w) / η = R g / η - R w / η := sub_div _ _ _
  linarith

lemma rl_dot_sum {d : ℕ} (v : Fin d → ℝ) (u : ℕ → Fin d → ℝ) (S : Finset ℕ) :
    v ⬝ᵥ (∑ s ∈ S, u s) = ∑ s ∈ S, v ⬝ᵥ u s := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dotProduct_add, ih]

lemma rl_step {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g) (n : ℕ) :
    g (n + 1) ⬝ᵥ (∑ s ∈ Finset.Icc 1 (n + 1), u s) - 𝓡 (g (n + 1)) / η
      - (g n ⬝ᵥ (∑ s ∈ Finset.Icc 1 n, u s) - 𝓡 (g n) / η)
    ≤ w (n + 1) ⬝ᵥ u (n + 1) + ‖u (n + 1) - M (n + 1)‖ * l1 (w (n + 1) - g (n + 1))
      - (l1 (w (n + 1) - g (n + 1)) ^ 2 + l1 (w (n + 1) - g n) ^ 2) / (2 * η) := by
  have hR := h𝓡.2
  have hwn := hw.2 (n + 1) (by omega)
  have hIco : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := Finset.Ico_add_one_right_eq_Icc 1 n
  rw [hIco] at hwn
  set U := ∑ s ∈ Finset.Icc 1 n, u s with hU
  have hU1 : (∑ s ∈ Finset.Icc 1 (n + 1), u s) = U + u (n + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega), Finset.Ico_add_one_right_eq_Icc]
  have q1 := rl_quad 𝓡 η hη hR (U + M (n + 1)) (w (n + 1)) (g (n + 1)) hwn.1 (hg (n + 1)).1 hwn.2
  have q2 := rl_quad 𝓡 η hη hR U (g n) (w (n + 1)) (hg n).1 hwn.1 (hg n).2
  have hl : l1 (g n - w (n + 1)) = l1 (w (n + 1) - g n) := by
    rw [← rl_l1_neg (w (n + 1) - g n)]; congr 1; abel
  rw [hl] at q2
  have hd := rl_dot_le (g (n + 1) - w (n + 1)) (u (n + 1) - M (n + 1))
  have hl2 : l1 (g (n + 1) - w (n + 1)) = l1 (w (n + 1) - g (n + 1)) := by
    rw [← rl_l1_neg (w (n + 1) - g (n + 1))]; congr 1; abel
  rw [hl2] at hd
  rw [hU1]
  simp only [dotProduct_add, add_dotProduct, sub_dotProduct, dotProduct_sub] at q1 q2 hd ⊢
  have e : ∀ a b : ℝ, (a + b) / (2 * η) = a / (2 * η) + b / (2 * η) := fun a b => add_div a b _
  rw [e]
  nlinarith [q1, q2, hd]

lemma rl_tele {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g) (T : ℕ) :
    g T ⬝ᵥ (∑ s ∈ Finset.Icc 1 T, u s) - 𝓡 (g T) / η - (g 0 ⬝ᵥ (∑ s ∈ Finset.Icc 1 0, u s) - 𝓡 (g 0) / η)
    ≤ ∑ t ∈ Finset.Icc 1 T, (w t ⬝ᵥ u t + ‖u t - M t‖ * l1 (w t - g t)
      - (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) / (2 * η)) := by
  induction T with
  | zero => simp
  | succ n ih =>
    have hs := Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)
      (fun t => w t ⬝ᵥ u t + ‖u t - M t‖ * l1 (w t - g t)
        - (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) / (2 * η))
    simp only [Nat.add_sub_cancel] at hs
    rw [hs]
    have := rl_step 𝓡 η hη h𝓡 M u w g hw hg n
    linarith

theorem rl_T19 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + ∑ t ∈ Finset.Icc 1 T, ‖u t - M t‖ * l1 (w t - g t)
        - 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) := by
  have h1 := rl_tele 𝓡 η hη h𝓡 M u w g hw hg T
  have h2 := (hg T).2 wstar hwstar
  have h3 := hR wstar hwstar (g 0) (hg 0).1
  have h4 : ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t
      = wstar ⬝ᵥ (∑ s ∈ Finset.Icc 1 T, u s) - ∑ t ∈ Finset.Icc 1 T, w t ⬝ᵥ u t := by
    rw [rl_dot_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [sub_dotProduct]
  have h5 : ∑ t ∈ Finset.Icc 1 T, (w t ⬝ᵥ u t + ‖u t - M t‖ * l1 (w t - g t)
      - (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) / (2 * η))
      = ∑ t ∈ Finset.Icc 1 T, w t ⬝ᵥ u t + ∑ t ∈ Finset.Icc 1 T, ‖u t - M t‖ * l1 (w t - g t)
        - 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [h5] at h1
  have e0 : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by decide
  simp only [e0, Finset.sum_empty, dotProduct_zero, zero_sub] at h1
  have h6 : (𝓡 wstar - 𝓡 (g 0)) / η ≤ R / η := div_le_div_of_nonneg_right h3 hη.le
  have h7 : (𝓡 wstar - 𝓡 (g 0)) / η = 𝓡 wstar / η - 𝓡 (g 0) / η := sub_div _ _ _
  rw [h4]
  linarith


lemma rl_exists_leader {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (hc : ContinuousOn 𝓡 (stdSimplex ℝ (Fin d))) (hne : (stdSimplex ℝ (Fin d)).Nonempty)
    (u : ℕ → Fin d → ℝ) : ∃ g : ℕ → Fin d → ℝ, IsLeader 𝓡 η u g := by
  have : ∀ T : ℕ, ∃ g : Fin d → ℝ, g ∈ stdSimplex ℝ (Fin d) ∧ ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ (∑ t ∈ Finset.Icc 1 T, u t) - 𝓡 v / η ≤ g ⬝ᵥ (∑ t ∈ Finset.Icc 1 T, u t) - 𝓡 g / η := by
    intro T
    have hcont : ContinuousOn (fun v : Fin d → ℝ => v ⬝ᵥ (∑ t ∈ Finset.Icc 1 T, u t) - 𝓡 v / η)
        (stdSimplex ℝ (Fin d)) := by
      have h1 : Continuous (fun v : Fin d → ℝ => v ⬝ᵥ (∑ t ∈ Finset.Icc 1 T, u t)) := by
        unfold dotProduct
        fun_prop
      exact h1.continuousOn.sub (hc.div_const η)
    obtain ⟨g, hg, hmax⟩ := (isCompact_stdSimplex ℝ (Fin d)).exists_isMaxOn hne hcont
    exact ⟨g, hg, fun v hv => hmax hv⟩
  choose g hg1 hg2 using this
  exact ⟨g, fun T => ⟨hg1 T, hg2 T⟩⟩

lemma rl_sq_shift (a : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, a (t - 1) ^ 2 + a T ^ 2 = ∑ t ∈ Finset.Icc 1 T, a t ^ 2 + a 0 ^ 2 := by
  induction T with
  | zero => simp
  | succ n ih =>
    have hs := Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega) (fun t => a (t - 1) ^ 2)
    have hs2 := Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega) (fun t => a t ^ 2)
    simp only [Nat.add_sub_cancel] at hs hs2
    rw [hs, hs2]
    linarith

lemma rl_prop7 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (u w : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η (fun T => u (T - 1)) u w)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2
        - 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2 := by
  obtain ⟨g, hg⟩ := rl_exists_leader 𝓡 η hη h𝓡.1 ⟨w 0, hw.1.1⟩ u
  have h19 := rl_T19 𝓡 η R hη h𝓡 hR (fun T => u (T - 1)) u w g hw hg T wstar hwstar
  have h20 := rl_lem20 𝓡 η hη h𝓡 (fun T => u (T - 1)) u w g hw hg
  have h0 := rl_zero 𝓡 η hη h𝓡 (fun T => u (T - 1)) u w g hw hg
  -- bound 1
  have b1 : ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ * l1 (w t - g t)
      ≤ η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    have this : l1 (w t - g t) ≤ η * ‖u (t - 1) - u t‖ := (h20 t).1
    rw [norm_sub_rev] at this
    nlinarith [norm_nonneg (u t - u (t - 1))]
  -- bound 2
  set a : ℕ → ℝ := fun t => l1 (w t - g t) with ha
  have b2 : ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2
      ≤ 2 * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) := by
    have hsh := rl_sq_shift a T
    have h00 : a 0 = 0 := h0
    have hT0 : 0 ≤ a T ^ 2 := sq_nonneg _
    have hle : ∀ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2
        ≤ 2 * l1 (w t - g (t - 1)) ^ 2 + 2 * a (t - 1) ^ 2 := by
      intro t _
      have htri : l1 (w t - w (t - 1)) ≤ l1 (w t - g (t - 1)) + a (t - 1) := by
        have : w t - w (t - 1) = (w t - g (t - 1)) + (g (t - 1) - w (t - 1)) := by abel
        rw [this]
        refine (rl_l1_add _ _).trans ?_
        have e : l1 (g (t - 1) - w (t - 1)) = a (t - 1) := by
          simp only [ha]
          rw [← rl_l1_neg (w (t - 1) - g (t - 1))]; congr 1; abel
        rw [e]
      have h1 := rl_l1_nonneg (w t - w (t - 1))
      nlinarith [sq_nonneg (l1 (w t - g (t - 1)) - a (t - 1))]
    calc ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2
        ≤ ∑ t ∈ Finset.Icc 1 T, (2 * l1 (w t - g (t - 1)) ^ 2 + 2 * a (t - 1) ^ 2) :=
          Finset.sum_le_sum hle
      _ = 2 * ∑ t ∈ Finset.Icc 1 T, l1 (w t - g (t - 1)) ^ 2 + 2 * ∑ t ∈ Finset.Icc 1 T, a (t - 1) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) := by
          rw [Finset.sum_add_distrib]
          have : ∑ t ∈ Finset.Icc 1 T, a (t - 1) ^ 2 ≤ ∑ t ∈ Finset.Icc 1 T, l1 (w t - g t) ^ 2 := by
            have : ∑ t ∈ Finset.Icc 1 T, a t ^ 2 = ∑ t ∈ Finset.Icc 1 T, l1 (w t - g t) ^ 2 := rfl
            rw [h00] at hsh
            linarith
          linarith
  have hpos : 0 < 1 / (4 * η) := by positivity
  have e1 : 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2)
      ≥ 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2 := by
    have : 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2
        ≤ 1 / (4 * η) * (2 * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_left b2 hpos.le
    have e : 1 / (4 * η) * (2 * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2))
        = 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) := by
      field_simp; ring
    linarith
  have b1' : ∑ t ∈ Finset.Icc 1 T, ‖u t - (fun T => u (T - 1)) t‖ * l1 (w t - g t)
      ≤ η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2 := b1
  linarith

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (u w : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η (fun T => u (T - 1)) u w)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2
        - 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2 :=
  rl_prop7 𝓡 η R hη h𝓡 hR u w hw T wstar hwstar
