-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:26:52.72193+00:00
-- url     : https://prove2.me/submissions/86658354-377c-4631-8480-f331a8f3ea65

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model
import Theorems.Thm_TimeDepFolk_Asymptotic_lemma_4_2

namespace TDFTail

open TimeDepFolk.Asymptotic Finset

theorem summable_shift (θ : Evaluation) (n : ℕ) : Summable (fun r => θ.θ (n + r)) := by
  have := (summable_nat_add_iff n).2 θ.hasSum.summable
  simpa [add_comm] using this

theorem tail_nonneg (θ : Evaluation) (n : ℕ) : 0 ≤ ∑' r, θ.θ (n + r) :=
  tsum_nonneg fun r => θ.nonneg _

theorem cont_nonneg (θ : Evaluation) (n t : ℕ) : 0 ≤ cont θ.θ n t :=
  div_nonneg (θ.nonneg _) (tail_nonneg θ n)

theorem cont_le_zero (θ : Evaluation) (n t : ℕ) : cont θ.θ n t ≤ cont θ.θ n 0 :=
  div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem cont_antitone (θ : Evaluation) (n : ℕ) : Antitone (cont θ.θ n) :=
  fun _ _ h => div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem hasSum_cont (θ : Evaluation) (n : ℕ) (h : 0 < ∑' r, θ.θ (n + r)) :
    HasSum (cont θ.θ n) 1 := by
  have := ((summable_shift θ n).hasSum).div_const (∑' r, θ.θ (n + r))
  rwa [div_self h.ne'] at this

theorem sum_range_cont (θ : Evaluation) (n m : ℕ) :
    ∑ t ∈ range m, cont θ.θ n t = (∑ t ∈ range m, θ.θ (n + t)) / ∑' r, θ.θ (n + r) := by
  simp only [cont, Finset.sum_div]

theorem tail_split (θ : Evaluation) (n m : ℕ) :
    ∑' r, θ.θ (n + r) = ∑ r ∈ range m, θ.θ (n + r) + ∑' r, θ.θ (n + m + r) := by
  have := (summable_shift θ n).sum_add_tsum_nat_add m
  rw [← this]
  congr 1
  refine tsum_congr fun r => ?_
  congr 1; omega

end TDFTail

namespace TDF43

open Finset

/-- A point of the convex hull of a finite family is a convex combination of the whole family. -/
theorem exists_weights {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E] (v : α → E)
    (x : E) (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ p : α → ℝ, (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧ ∑ a, p a • v a = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw0, hw1, hwx⟩ := hx
  refine ⟨fun a => if a ∈ s then w a else 0, fun a => ?_, ?_, ?_⟩
  · dsimp only; split_ifs with h
    · exact hw0 a h
    · exact le_rfl
  · rw [Finset.sum_ite_mem, Finset.univ_inter, hw1]
  · rw [← hwx, s.affineCombination_eq_linear_combination v w hw1]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

end TDF43

open TimeDepFolk.Asymptotic Finset

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    ∀ η > 0, ∃ K : ℕ, ∀ x ∈ F g, ∀ k ≥ K, ∃ h : ℕ → (∀ i, A i),
      purePayoff g (θ k).θ h = x ∧
        ∀ T ≥ 1, ‖purePayoff g (cont (θ k).θ T) (fun s => h (T + s)) - x‖ ≤ η := by
  classical
  intro η hη
  set G : (∀ i, A i) → I → ℝ := fun a i => g i a with hG
  set N : ℕ := Fintype.card (∀ i, A i) with hN
  have hN0 : (0 : ℝ) < N := by
    have : 0 < Fintype.card (∀ i, A i) := Fintype.card_pos
    exact_mod_cast this
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ i a, |g i a| ≤ M := by
    obtain ⟨M, hM⟩ := (Set.finite_range (fun p : I × (∀ i, A i) => |g p.1 p.2|)).bddAbove
    exact ⟨max M 1, by positivity, fun i a => (hM ⟨(i, a), rfl⟩).trans (le_max_left _ _)⟩
  -- the tolerance on barycentric coordinates
  set ε : ℝ := min (η / (2 * M)) (1 / 2) with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεM : 2 * ε * M ≤ η := by
    have : ε ≤ η / (2 * M) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  -- patience: small first continuation weights, and positive weights
  have h42 := (lemma_4_2 θ hθ).1
  rw [Metric.tendstoUniformly_iff] at h42
  obtain ⟨K1, hK1⟩ := Filter.eventually_atTop.1 (h42 (ε / N) (by positivity))
  have hθ' := hθ
  rw [IsPatient, Metric.tendstoUniformly_iff] at hθ'
  obtain ⟨K2, hK2⟩ := Filter.eventually_atTop.1 (hθ' (1 / 2) (by norm_num))
  refine ⟨max K1 K2, fun x hx k hk => ?_⟩
  have hxG : x ∈ convexHull ℝ (Set.range G) := hx.1
  obtain ⟨p, hp0, hp1, hpx⟩ := TDF43.exists_weights G x hxG
  set w := (θ k).θ with hw
  set τ : ℕ → ℝ := fun m => ∑' r, w (m + r) with hτ
  have hτsucc : ∀ m, τ (m + 1) = τ m - w m := by
    intro m
    have := TDFTail.tail_split (θ k) m 1
    simp only [Finset.range_one, Finset.sum_singleton, add_zero] at this
    simp only [τ, w]; linarith
  have hτ0 : τ 0 = 1 := by simp [τ, w, (θ k).hasSum.tsum_eq]
  have hw0 : ∀ m, 0 ≤ w m := (θ k).nonneg
  have hwpos : ∀ m, 0 < w (m + 1) := by
    intro m
    have h := hK2 k (le_of_max_le_right hk) m
    rcases (hw0 (m + 1)).eq_or_lt with h0 | h0
    · have h0' : (θ k).θ (m + 1) = 0 := h0.symm
      rw [h0', div_zero, dist_zero_right, norm_one] at h; norm_num at h
    · exact h0
  have hτpos : ∀ m, 0 < τ m := by
    intro m
    have h1 := TDFTail.tail_split (θ k) m 2
    have h2 := TDFTail.tail_nonneg (θ k) (m + 2)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, add_zero] at h1
    have h3 := hwpos m
    have h4 := hw0 m
    show 0 < ∑' r, (θ k).θ (m + r)
    simp only [w] at h3 h4
    linarith
  have hwτ : ∀ m, w m ≤ ε / N * τ m := by
    intro m
    have hc := hK1 k (le_of_max_le_left hk) m
    rw [dist_zero_left, Real.norm_eq_abs] at hc
    have : cont (θ k).θ m 0 = w m / τ m := by simp [cont, τ, w]
    rw [this, abs_of_nonneg (div_nonneg (hw0 m) (hτpos m).le), div_lt_iff₀ (hτpos m)] at hc
    linarith
  -- greedy construction on unnormalised coordinates with margin `(1-ε) τ p`
  let amax : ((∀ i, A i) → ℝ) → (∀ i, A i) := fun f => (Finite.exists_max f).choose
  have hamax : ∀ (f : (∀ i, A i) → ℝ) (j : (∀ i, A i)), f j ≤ f (amax f) :=
    fun f => (Finite.exists_max f).choose_spec
  let pick : ℕ → ((∀ i, A i) → ℝ) → (∀ i, A i) := fun m c => amax (fun l => c l - (1 - ε) * τ m * p l)
  let C : ℕ → (∀ i, A i) → ℝ := fun m =>
    Nat.rec p (fun m c j => c j - (if j = pick m c then w m else 0)) m
  have hC0 : C 0 = p := rfl
  have hCs : ∀ m j, C (m + 1) j = C m j - (if j = pick m (C m) then w m else 0) :=
    fun m j => rfl
  set h : ℕ → (∀ i, A i) := fun m => pick m (C m) with hhdef
  have hsumC : ∀ m, ∑ j, C m j = τ m := by
    intro m
    induction m with
    | zero => rw [hC0, hp1, hτ0]
    | succ m ih =>
      simp only [hCs, Finset.sum_sub_distrib, ih, hτsucc]
      simp
  have hmarg : ∀ m j, (1 - ε) * τ m * p j ≤ C m j := by
    intro m
    induction m with
    | zero => intro j; rw [hC0, hτ0]; nlinarith [hp0 j]
    | succ m ih =>
      intro j
      rw [hCs, hτsucc]
      by_cases hj : j = pick m (C m)
      · rw [if_pos hj]
        have hslack : ε / N * τ m ≤ C m j - (1 - ε) * τ m * p j := by
          have hle : ∀ l, C m l - (1 - ε) * τ m * p l ≤ C m j - (1 - ε) * τ m * p j := by
            intro l; rw [hj]; exact hamax (fun l => C m l - (1 - ε) * τ m * p l) l
          have hs : ∑ l, (C m l - (1 - ε) * τ m * p l) = ε * τ m := by
            rw [Finset.sum_sub_distrib, hsumC, ← Finset.mul_sum, hp1]; ring
          have := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hle l
          rw [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
          rw [show ε / (N : ℝ) * τ m = (ε * τ m) / N by ring, div_le_iff₀ hN0]
          linarith
        have := hwτ m
        have hpj : (1 - ε) * w m * p j ≥ 0 := by
          have := hp0 j; have := hw0 m; have : 0 ≤ 1 - ε := by linarith
          positivity
        nlinarith
      · rw [if_neg hj, sub_zero]
        have := ih j
        have : 0 ≤ (1 - ε) * w m * p j := by
          have := hp0 j; have := hw0 m; have : 0 ≤ 1 - ε := by linarith
          positivity
        nlinarith
  have hrem : ∀ m, x - ∑ i ∈ range m, w i • G (h i) = ∑ j, C m j • G j := by
    intro m
    induction m with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_zero, hC0, hpx]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ih]
      simp only [hCs, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul]
      simp [h]
  -- the normalised deviations are small: `∑ |C/τ - p| ≤ 2ε`
  have hdev : ∀ m, ∑ j, |C m j / τ m - p j| ≤ 2 * ε := by
    intro m
    have hτm := hτpos m
    set d : (∀ i, A i) → ℝ := fun j => C m j / τ m - p j with hd
    have hd0 : ∑ j, d j = 0 := by
      simp only [d, Finset.sum_sub_distrib, ← Finset.sum_div, hsumC, div_self hτm.ne', hp1,
        sub_self]
    have hdlow : ∀ j, -(ε * p j) ≤ d j := by
      intro j
      have := hmarg m j
      simp only [d]
      rw [le_sub_iff_add_le, le_div_iff₀ hτm]
      nlinarith [hp0 j]
    -- `|d| = d + 2 d⁻` and `d⁻ ≤ ε p`
    have habs : ∀ j, |d j| ≤ d j + 2 * (ε * p j) := by
      intro j
      rcases le_or_gt 0 (d j) with h0 | h0
      · rw [abs_of_nonneg h0]; nlinarith [hp0 j, hε0]
      · rw [abs_of_neg h0]; linarith [hdlow j]
    calc ∑ j, |d j| ≤ ∑ j, (d j + 2 * (ε * p j)) := Finset.sum_le_sum fun j _ => habs j
      _ = 2 * ε := by rw [Finset.sum_add_distrib, hd0, ← Finset.mul_sum, ← Finset.mul_sum, hp1]; ring
  -- the tail tends to zero
  have hτlim : Filter.Tendsto τ Filter.atTop (nhds 0) := by
    have e : ∀ m, τ m = 1 - ∑ i ∈ range m, w i := by
      intro m
      have := TDFTail.tail_split (θ k) 0 m
      simp only [zero_add] at this
      rw [(θ k).hasSum.tsum_eq] at this
      simp only [τ, w]; linarith
    rw [show τ = fun m => 1 - ∑ i ∈ range m, w i from funext e]
    have := (θ k).hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  -- componentwise convergence of the payoff series
  have hser : ∀ i, HasSum (fun s => w s * g i (h s)) (x i) := by
    intro i
    have hsumm : Summable (fun s => w s * g i (h s)) := by
      refine Summable.of_norm_bounded ((θ k).hasSum.summable.mul_right M) fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 s)]
      exact mul_le_mul_of_nonneg_left (hM _ _) (hw0 s)
    rw [hsumm.hasSum_iff_tendsto_nat, tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ m, ‖∑ s ∈ range m, w s * g i (h s) - x i‖ ≤ τ m * ((1 + 2 * ε) * M) := by
      intro m
      have := congrFun (hrem m) i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, G] at this
      rw [norm_sub_rev, Real.norm_eq_abs, this]
      have hτm := hτpos m
      calc |∑ j, C m j * g i j| ≤ ∑ j, |C m j| * M := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _ _) (abs_nonneg _)
        _ = τ m * (∑ j, |C m j / τ m|) * M := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_div, abs_of_pos hτm]; field_simp
        _ ≤ τ m * (1 + 2 * ε) * M := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hτm.le) hM0.le
            calc ∑ j, |C m j / τ m| ≤ ∑ j, (|C m j / τ m - p j| + p j) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  have := abs_sub_abs_le_abs_sub (C m j / τ m) (p j)
                  rw [abs_of_nonneg (hp0 j)] at this; linarith
              _ ≤ 2 * ε + 1 := by rw [Finset.sum_add_distrib, hp1]; linarith [hdev m]
              _ = 1 + 2 * ε := by ring
        _ = τ m * ((1 + 2 * ε) * M) := by ring
    refine squeeze_zero (fun m => norm_nonneg _) hb ?_
    simpa using hτlim.mul_const ((1 + 2 * ε) * M)
  refine ⟨h, ?_, ?_⟩
  · funext i
    exact (hser i).tsum_eq
  · intro T hT
    have hτT := hτpos T
    -- the continuation payoff is the normalised remainder
    have hcont : purePayoff g (cont (θ k).θ T) (fun s => h (T + s)) =
        ∑ j, (C T j / τ T) • G j := by
      funext i
      have hsplit := (hser i).summable.sum_add_tsum_nat_add T
      rw [(hser i).tsum_eq] at hsplit
      have hr := congrFun (hrem T) i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, G] at hr
      simp only [purePayoff, cont, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, G]
      have e1 : ∑' s, w (T + s) / τ T * g i (h (T + s)) =
          (∑' s, w (s + T) * g i (h (s + T))) / τ T := by
        rw [← tsum_div_const]
        refine tsum_congr fun s => ?_
        rw [add_comm s T]; ring
      simp only [τ, w] at e1 ⊢
      rw [e1]
      have : ∑' s, (θ k).θ (s + T) * g i (h (s + T)) = ∑ j, C T j * g i j := by
        simp only [w] at hsplit hr; linarith
      rw [this, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hcont, ← hpx]
    have e : ∑ j, (C T j / τ T) • G j - ∑ a, p a • G a = ∑ j, (C T j / τ T - p j) • G j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (sub_smul _ _ _).symm
    rw [e]
    refine (pi_norm_le_iff_of_nonneg hη.le).2 fun i => ?_
    rw [Finset.sum_apply, Real.norm_eq_abs]
    calc |∑ j, ((C T j / τ T - p j) • G j) i| ≤ ∑ j, |C T j / τ T - p j| * M := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          simp only [Pi.smul_apply, smul_eq_mul, G, abs_mul]
          exact mul_le_mul_of_nonneg_left (hM _ _) (abs_nonneg _)
      _ = (∑ j, |C T j / τ T - p j|) * M := by rw [Finset.sum_mul]
      _ ≤ 2 * ε * M := mul_le_mul_of_nonneg_right (hdev T) hM0.le
      _ ≤ η := hεM
