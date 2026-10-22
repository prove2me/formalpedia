-- Prove2me | solution 1 for SocialManip.Beliefs.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:02:40.007123+00:00
-- url     : https://prove2.me/submissions/c405cd9f-b12d-472d-98f6-ec68d972146e

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

open Filter Topology Matrix

namespace SMAux
open SocialManip.Beliefs

/-- iterates `v_t = W^t 1` -/
noncomputable def itv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => ∑ j, M i j * itv M t j

theorem weights {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i) :
    (∀ i j, 0 ≤ W B α i j) ∧ ∃ w : Fin n → ℝ, ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ (∀ i, 1 ≤ w i) ∧
      ∀ i, ∑ j, W B α i j * w j ≤ γ * w i := by
  set M := W B α with hM
  have hWnn : ∀ i j, 0 ≤ M i j := by
    intro i j
    simp only [hM, W, Matrix.of_apply]
    split_ifs with h
    · exact le_rfl
    · exact hα i h j
  have hWrow : ∀ i, ∑ j, M i j ≤ 1 := by
    intro i
    by_cases h : i ∈ B
    · simp [hM, W, h]
    · simp only [hM, W, Matrix.of_apply, h, if_false]
      linarith [hrow i h, hθ i h]
  obtain ⟨k, hk⟩ : ∃ k, ∑ j, M k j < 1 := by
    obtain ⟨i, hi⟩ := hA1iv
    refine ⟨i, ?_⟩
    by_cases h : i ∈ B
    · simp [hM, W, h]
    · simp only [hM, W, Matrix.of_apply, h, if_false]
      linarith [hrow i h, (hA1iii i h).2 hi]
  set v := itv M with hv
  have hv0 : ∀ i, v 0 i = 1 := fun i => rfl
  have hvs : ∀ t i, v (t + 1) i = ∑ j, M i j * v t j := fun t i => rfl
  have hbd : ∀ t i, 0 ≤ v t i ∧ v t i ≤ 1 := by
    intro t
    induction t with
    | zero => intro i; simp [hv0]
    | succ t ih =>
      intro i
      rw [hvs]
      constructor
      · exact Finset.sum_nonneg fun j _ => mul_nonneg (hWnn i j) (ih j).1
      · calc ∑ j, M i j * v t j ≤ ∑ j, M i j :=
              Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hWnn i j) (ih j).2
          _ ≤ 1 := hWrow i
  have hmono : ∀ t i, v (t + 1) i ≤ v t i := by
    intro t
    induction t with
    | zero => intro i; rw [hv0]; exact (hbd 1 i).2
    | succ t ih =>
      intro i
      rw [hvs, hvs t]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hWnn i j)
  have hanti : ∀ i, Antitone fun t => v t i := fun i => antitone_nat_of_succ_le fun t => hmono t i
  have hstep : ∀ a b, adj a b → (∃ t, v t b < 1) → ∃ t, v t a < 1 := by
    intro a b hab ⟨t, ht⟩
    by_cases ha : a ∈ B
    · refine ⟨1, ?_⟩
      rw [hvs]
      simp [hM, W, ha]
    · refine ⟨t + 1, ?_⟩
      rw [hvs]
      have hpos : 0 < M a b := by
        simp only [hM, W, Matrix.of_apply, ha, if_false]
        exact (hadj a ha b).1 hab
      calc ∑ j, M a j * v t j < ∑ j, M a j := by
            apply Finset.sum_lt_sum
            · intro j _; exact mul_le_of_le_one_right (hWnn a j) (hbd t j).2
            · exact ⟨b, Finset.mem_univ _, by nlinarith⟩
        _ ≤ 1 := hWrow a
  have hk1 : v 1 k < 1 := by
    rw [hvs]; simpa [hv0] using hk
  have hreach : ∀ i, ∃ t, v t i < 1 := by
    intro i
    by_cases hik : i = k
    · exact ⟨1, hik ▸ hk1⟩
    · have hT := hA1ii i k hik
      clear hik
      induction hT using Relation.TransGen.head_induction_on with
      | single h => exact hstep _ _ h ⟨1, hk1⟩
      | head h' _ ih => exact hstep _ _ h' ih
  have hev : ∀ᶠ t in atTop, ∀ i, v t i < 1 := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨t, ht⟩ := hreach i
    filter_upwards [eventually_ge_atTop t] with s hs
    exact lt_of_le_of_lt (hanti i hs) ht
  obtain ⟨N, hN⟩ := hev.exists
  set w : Fin n → ℝ := fun i => ∑ t ∈ Finset.range (N + 1), v t i with hw
  have hw1 : ∀ i, 1 ≤ w i := by
    intro i
    simp only [hw]
    rw [Finset.sum_range_succ']
    have : 0 ≤ ∑ t ∈ Finset.range N, v (t + 1) i :=
      Finset.sum_nonneg fun t _ => (hbd _ i).1
    rw [hv0]; linarith
  have hWw : ∀ i, ∑ j, M i j * w j < w i := by
    intro i
    have e1 : ∑ j, M i j * w j = ∑ t ∈ Finset.range (N + 1), v (t + 1) i := by
      simp only [hw, Finset.mul_sum, hvs]
      rw [Finset.sum_comm]
    rw [e1]
    have e2 : ∑ t ∈ Finset.range (N + 1), v (t + 1) i + v 0 i =
        w i + v (N + 1) i := by
      simp only [hw]
      rw [← Finset.sum_range_succ' (fun t => v t i), Finset.sum_range_succ]
    have : v (N + 1) i < 1 := lt_of_le_of_lt (hmono N i) (hN i)
    rw [hv0] at e2
    linarith
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ
    (fun i => (∑ j, M i j * w j) / w i) ⟨k, Finset.mem_univ _⟩
  refine ⟨hWnn, w, (∑ j, M i0 j * w j) / w i0, ?_, ?_, hw1, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hWnn i0 j) (hwpos j).le)
      (hwpos i0).le
  · rw [div_lt_one (hwpos i0)]; exact hWw i0
  · intro i
    have := hi0 i (Finset.mem_univ _)
    rwa [div_le_iff₀ (hwpos i)] at this

/-- contraction in the weighted sup norm -/
theorem contr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (w : Fin n → ℝ) (γ : ℝ) (hW : ∀ i, ∑ j, M i j * w j ≤ γ * w i)
    (x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a) (hx : ∀ j, |x j| ≤ a * w j) (i : Fin n) :
    |(M *ᵥ x) i| ≤ γ * a * w i := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, M i j * x j| ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, M i j * (a * w j) := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, abs_of_nonneg (hM i j)]
        exact mul_le_mul_of_nonneg_left (hx j) (hM i j)
    _ = a * ∑ j, M i j * w j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ a * (γ * w i) := mul_le_mul_of_nonneg_left (hW i) ha
    _ = γ * a * w i := by ring

/-- a fixed point of a weighted contraction is zero -/
theorem fix_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (w : Fin n → ℝ) (γ : ℝ) (hγ : γ < 1) (hw1 : ∀ i, 1 ≤ w i)
    (hW : ∀ i, ∑ j, M i j * w j ≤ γ * w i)
    (x : Fin n → ℝ) (hx : M *ᵥ x = x) : x = 0 := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · funext i; exact (IsEmpty.false i).elim
  obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ
    (fun i => |x i| / w i) Finset.univ_nonempty
  set a := |x i0| / w i0
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) (hwpos i0).le
  have hxa : ∀ j, |x j| ≤ a * w j := by
    intro j
    have := hi0 j (Finset.mem_univ _)
    rwa [div_le_iff₀ (hwpos j)] at this
  have h1 := contr M hM w γ hW x a ha hxa i0
  rw [hx] at h1
  have h2 : |x i0| = a * w i0 := by
    simp only [a]; field_simp [(hwpos i0).ne']
  have ha0 : a = 0 := by
    rw [h2] at h1
    have : (1 - γ) * (a * w i0) ≤ 0 := by nlinarith
    have hpos : 0 < 1 - γ := by linarith
    have : a * w i0 ≤ 0 := by
      by_contra hc; nlinarith
    have := mul_nonneg ha (hwpos i0).le
    have : a * w i0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (hwpos i0).ne'
  funext j
  have := hxa j
  rw [ha0, zero_mul] at this
  simpa using abs_nonpos_iff.mp this

theorem isUnit_of_weights {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (w : Fin n → ℝ) (γ : ℝ) (hγ : γ < 1) (hw1 : ∀ i, 1 ≤ w i)
    (hW : ∀ i, ∑ j, M i j * w j ≤ γ * w i) : IsUnit (1 - M) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  apply hx0
  apply fix_zero M hM w γ hγ hw1 hW
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hx
  exact hx.symm

/-- perturbed contraction iteration converges to zero -/
theorem iter_tendsto {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (w : Fin n → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hw1 : ∀ i, 1 ≤ w i)
    (hW : ∀ i, ∑ j, M i j * w j ≤ γ * w i)
    (e δ : ℕ → Fin n → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (he : ∀ t, e (t + 1) = δ t + M *ᵥ e t) : Tendsto e atTop (𝓝 0) := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  set C := ∑ i, w i with hC
  have hwC : ∀ i, w i ≤ C := fun i =>
    Finset.single_le_sum (fun j _ => (hwpos j).le) (Finset.mem_univ i)
  have key : ∀ ε > 0, ∀ᶠ t in atTop, ∀ i, |e t i| ≤ ε := by
    intro ε hε
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact Eventually.of_forall fun t i => (IsEmpty.false i).elim
    obtain ⟨i1⟩ := hn
    have hCpos : 0 < C := lt_of_lt_of_le (hwpos i1) (hwC i1)
    set ε' := ε / (2 * C) with hε'
    have hε'pos : 0 < ε' := by positivity
    have hδev : ∀ᶠ t in atTop, ∀ i, |δ t i| ≤ ε' * (1 - γ) := by
      rw [Filter.eventually_all]
      intro i
      have hi : Tendsto (fun t => δ t i) atTop (𝓝 0) := tendsto_pi_nhds.mp hδ i
      have hpos : 0 < ε' * (1 - γ) := mul_pos hε'pos (by linarith)
      filter_upwards [(Metric.tendsto_nhds.mp hi) _ hpos] with t ht
      rw [Real.dist_eq, sub_zero] at ht
      exact ht.le
    obtain ⟨T0, hT0⟩ := eventually_atTop.mp hδev
    set A := ∑ i, |e T0 i| with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hind : ∀ s, ∀ i, |e (T0 + s) i| ≤ (ε' + γ ^ s * A) * w i := by
      intro s
      induction s with
      | zero =>
        intro i
        simp only [add_zero, pow_zero, one_mul]
        have h1 : |e T0 i| ≤ A :=
          Finset.single_le_sum (f := fun i => |e T0 i|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        nlinarith [hw1 i]
      | succ s ih =>
        intro i
        rw [← add_assoc, he, Pi.add_apply]
        have hc := contr M hM w γ hW (e (T0 + s)) (ε' + γ ^ s * A)
          (by positivity) ih i
        have hd := hT0 (T0 + s) (by omega) i
        calc |δ (T0 + s) i + (M *ᵥ e (T0 + s)) i|
            ≤ |δ (T0 + s) i| + |(M *ᵥ e (T0 + s)) i| := abs_add_le _ _
          _ ≤ ε' * (1 - γ) * w i + γ * (ε' + γ ^ s * A) * w i := by
              have : ε' * (1 - γ) ≤ ε' * (1 - γ) * w i := by
                have : 0 ≤ ε' * (1 - γ) := mul_nonneg hε'pos.le (by linarith)
                nlinarith [hw1 i]
              linarith
          _ = (ε' + γ ^ (s + 1) * A) * w i := by ring
    have hpow : ∀ᶠ s in atTop, γ ^ s * A ≤ ε' := by
      have h1 : Tendsto (fun s : ℕ => γ ^ s * A) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ).mul_const A
      filter_upwards [(Metric.tendsto_nhds.mp h1) ε' hε'pos] with s hs
      rw [Real.dist_eq, sub_zero] at hs
      exact (le_abs_self _).trans hs.le
    obtain ⟨S, hS⟩ := eventually_atTop.mp hpow
    rw [eventually_atTop]
    refine ⟨T0 + S, fun t ht i => ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = T0 + s := ⟨t - T0, by omega⟩
    have h1 := hind s i
    have h2 := hS s (by omega)
    calc |e (T0 + s) i| ≤ (ε' + γ ^ s * A) * w i := h1
      _ ≤ (2 * ε') * C := by
          apply mul_le_mul (by linarith) (hwC i) (hwpos i).le (by positivity)
      _ = ε := by rw [hε']; field_simp
  rw [tendsto_pi_nhds]
  intro i
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (key (ε / 2) (by positivity))
  refine ⟨T, fun t ht => ?_⟩
  rw [Real.dist_eq, Pi.zero_apply, sub_zero]
  exact lt_of_le_of_lt (hT t ht i) (by linarith)

end SMAux

open SocialManip.Beliefs

theorem solution {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ) (α : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, 1 / 2 ≤ p i ∧ p i < 1)
    (hθ : ∀ i ∉ B, 0 ≤ θ i) (hα : ∀ i ∉ B, ∀ j, 0 ≤ α i j)
    (hrow : ∀ i ∉ B, θ i + ∑ j, α i j = 1)
    (adj : Fin n → Fin n → Prop) (hadj : ∀ i ∉ B, ∀ j, adj i j ↔ 0 < α i j)
    (hA1ii : ∀ i j, i ≠ j → Relation.TransGen adj i j)
    (hA1iii : ∀ i ∉ B, (0 < θ i ↔ 1 / 2 < p i))
    (hA1iv : ∃ i, 1 / 2 < p i) :
    spectralRadius ℂ ((W B α).map (algebraMap ℝ ℂ)) < 1 := by
  obtain ⟨hWnn, w, γ, hγ0, hγ1, hw1, hW⟩ :=
    SMAux.weights B θ α p hθ hα hrow adj hadj hA1ii hA1iii hA1iv
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  set Mc := (W B α).map (algebraMap ℝ ℂ) with hMc
  have hbound : ∀ k ∈ spectrum ℂ Mc, ‖k‖ ≤ γ := by
    intro k hk
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hk
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hk
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hv
    have hn : Nonempty (Fin n) := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hv0 (funext fun i => (IsEmpty.false i).elim)
    obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ
      (fun i => ‖v i‖ / w i) Finset.univ_nonempty
    set a := ‖v i0‖ / w i0 with ha
    have hva : ∀ j, ‖v j‖ ≤ a * w j := by
      intro j
      have := hi0 j (Finset.mem_univ _)
      rwa [div_le_iff₀ (hwpos j)] at this
    have hapos : 0 < a := by
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra h; push_neg at h; exact hv0 (funext h)
      have h1 : 0 < ‖v j‖ / w j := div_pos (norm_pos_iff.mpr hj) (hwpos j)
      exact lt_of_lt_of_le h1 (hi0 j (Finset.mem_univ _))
    have hcoord := congr_fun hv i0
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hMc,
      Matrix.map_apply] at hcoord
    have h1 : ‖k‖ * ‖v i0‖ ≤ a * (γ * w i0) := by
      rw [← norm_mul, hcoord]
      calc ‖∑ j, (algebraMap ℝ ℂ) (W B α i0 j) * v j‖
          ≤ ∑ j, ‖(algebraMap ℝ ℂ) (W B α i0 j) * v j‖ := norm_sum_le _ _
        _ ≤ ∑ j, W B α i0 j * (a * w j) := by
            apply Finset.sum_le_sum; intro j _
            rw [norm_mul, Complex.coe_algebraMap, Complex.norm_of_nonneg (hWnn i0 j)]
            exact mul_le_mul_of_nonneg_left (hva j) (hWnn i0 j)
        _ = a * ∑ j, W B α i0 j * w j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ a * (γ * w i0) := mul_le_mul_of_nonneg_left (hW i0) hapos.le
    have h2 : ‖v i0‖ = a * w i0 := by
      rw [ha]; field_simp [(hwpos i0).ne']
    rw [h2] at h1
    have hp : 0 < a * w i0 := mul_pos hapos (hwpos i0)
    nlinarith
  calc spectralRadius ℂ Mc ≤ ENNReal.ofReal γ := by
        apply iSup₂_le
        intro k hk
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (hbound k hk)
    _ < 1 := ENNReal.ofReal_lt_one.mpr hγ1
