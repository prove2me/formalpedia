-- Prove2me | solution 1 for OptRobustCD.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:29:21.48023+00:00
-- url     : https://prove2.me/submissions/fe18c311-3070-4076-82ea-58e3a579126b

import Mathlib
import Definitions.Def_OptRobustCD_BP

namespace OptRobustCD.L410Aux

open Finset OptRobustCD
open scoped Classical

/-! ### `tanh` is 1-Lipschitz -/

theorem tanh_lip (a b : ℝ) : |Real.tanh a - Real.tanh b| ≤ |a - b| := by
  have hd : ∀ x, HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    intro x
    have h1 := Real.hasDerivAt_sinh x
    have h2 := Real.hasDerivAt_cosh x
    have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have h3 := h1.div h2 hc
    have heq : (Real.sinh / Real.cosh) = Real.tanh := by
      funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
    rw [heq] at h3
    have hval : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
        1 / Real.cosh x ^ 2 := by
      rw [← Real.cosh_sq_sub_sinh_sq x]; ring
    rw [hval] at h3
    exact h3
  have hlip : LipschitzWith 1 Real.tanh := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    have hc := Real.one_le_cosh x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one,
      abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith
  have := hlip.dist_le_mul a b
  simpa [Real.dist_eq] using this

/-! ### Locality of BP on a fixed graph -/

theorem bpMap_congr {n : ℕ} (lam : ℝ) (S : Finset (Fin n)) (m m' : Fin n → ℝ)
    (h : ∀ w ∈ S, m w = m' w) : bpMap lam S m = bpMap lam S m' := by
  unfold bpMap
  have e1 : ∏ w ∈ S, (1 + lam * m w) = ∏ w ∈ S, (1 + lam * m' w) :=
    prod_congr rfl (fun w hw => by rw [h w hw])
  have e2 : ∏ w ∈ S, (1 - lam * m w) = ∏ w ∈ S, (1 - lam * m' w) :=
    prod_congr rfl (fun w hw => by rw [h w hw])
  rw [e1, e2]

theorem msg_loc {n : ℕ} (G : SimpleGraph (Fin n)) (lam γ : ℝ) (τ τ' : Fin n × Fin n → Bool) :
    ∀ (s : ℕ) (u v : Fin n), G.Adj v u →
      (∀ y z, G.Adj y z → ((y = v ∧ z = u) ∨ G.edist u y + 1 ≤ (s : ℕ∞)) →
        τ (y, z) = τ' (y, z)) →
      bpMsg G lam γ τ s u v = bpMsg G lam γ τ' s u v := by
  intro s
  induction s with
  | zero =>
    intro u v hvu h
    show γ * spinR (τ (v, u)) = γ * spinR (τ' (v, u))
    rw [h v u hvu (Or.inl ⟨rfl, rfl⟩)]
  | succ s ih =>
    intro u v _ h
    show bpMap lam ((nbrs G u).erase v) (fun w => bpMsg G lam γ τ s w u) =
      bpMap lam ((nbrs G u).erase v) (fun w => bpMsg G lam γ τ' s w u)
    apply bpMap_congr
    intro w hw
    have hadj : G.Adj u w := by
      have := mem_of_mem_erase hw
      simpa [nbrs] using this
    apply ih w u hadj
    intro y z hyz hc
    apply h y z hyz
    right
    rcases hc with ⟨hy, _⟩ | hd
    · rw [hy, SimpleGraph.edist_self, zero_add]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
    · have h1 : G.edist u y ≤ G.edist u w + G.edist w y := SimpleGraph.edist_triangle
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at h1
      calc G.edist u y + 1 ≤ (1 + G.edist w y) + 1 := by gcongr
        _ = (G.edist w y + 1) + 1 := by ring
        _ ≤ (s : ℕ∞) + 1 := by gcongr
        _ = ((s + 1 : ℕ) : ℕ∞) := by push_cast; rfl

theorem out_loc {n : ℕ} (G : SimpleGraph (Fin n)) (lam γ : ℝ) (t : ℕ)
    (τ τ' : Fin n × Fin n → Bool) (v : Fin n)
    (h : ∀ y z, G.Adj y z → G.edist v y ≤ (t : ℕ∞) → τ (y, z) = τ' (y, z)) :
    bpOut G lam t γ τ v = bpOut G lam t γ τ' v := by
  have hmap : bpMap lam (nbrs G v) (fun w => bpMsg G lam γ τ t w v) =
      bpMap lam (nbrs G v) (fun w => bpMsg G lam γ τ' t w v) := by
    apply bpMap_congr
    intro w hw
    have hadj : G.Adj v w := by simpa [nbrs] using hw
    apply msg_loc G lam γ τ τ' t w v hadj
    intro y z hyz hc
    apply h y z hyz
    rcases hc with ⟨hy, _⟩ | hd
    · rw [hy, SimpleGraph.edist_self]; exact zero_le
    · have h1 : G.edist v y ≤ G.edist v w + G.edist w y := SimpleGraph.edist_triangle
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at h1
      calc G.edist v y ≤ 1 + G.edist w y := h1
        _ = G.edist w y + 1 := add_comm _ _
        _ ≤ t := hd
  simp only [bpOut]
  rw [hmap]

/-! ### The coordinatewise maximal coupling -/

noncomputable def fA {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) (b : Bool) : ℝ :=
  (1 + spinR b * Real.tanh (Y p)) / 2

noncomputable def kA {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b b' : Bool) : ℝ :=
  if b = b' then min (fA Y p b) (fA Y' p b) else max 0 (fA Y p b - fA Y' p b)

theorem fA_true {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) :
    fA Y p true = (1 + Real.tanh (Y p)) / 2 := by simp [fA, spinR]

theorem fA_false {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) :
    fA Y p false = (1 - Real.tanh (Y p)) / 2 := by simp [fA, spinR]; ring

theorem fA_nonneg {n : ℕ} (Y : EVec n) (p : Fin n × Fin n) (b : Bool) : 0 ≤ fA Y p b := by
  have h1 := Real.tanh_lt_one (Y p)
  have h2 := Real.neg_one_lt_tanh (Y p)
  cases b
  · rw [fA_false]; linarith
  · rw [fA_true]; linarith

theorem kA_nonneg {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b b' : Bool) :
    0 ≤ kA Y Y' p b b' := by
  unfold kA
  split_ifs
  · exact le_min (fA_nonneg Y p b) (fA_nonneg Y' p b)
  · exact le_max_left _ _

theorem kA_row {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b : Bool) :
    ∑ b', kA Y Y' p b b' = fA Y p b := by
  rw [Fintype.sum_bool]
  unfold kA
  cases b <;> simp only [fA_true, fA_false, Bool.true_eq_false, Bool.false_eq_true,
    if_true, if_false] <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem kA_col {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) (b' : Bool) :
    ∑ b, kA Y Y' p b b' = fA Y' p b' := by
  rw [Fintype.sum_bool]
  unfold kA
  cases b' <;> simp only [fA_true, fA_false, Bool.true_eq_false, Bool.false_eq_true,
    if_true, if_false] <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem kA_total {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) :
    ∑ b, ∑ b', kA Y Y' p b b' = 1 := by
  rw [Finset.sum_congr rfl (fun b _ => kA_row Y Y' p b), Fintype.sum_bool, fA_true, fA_false]
  ring

theorem kA_disagree {n : ℕ} (Y Y' : EVec n) (p : Fin n × Fin n) :
    ∑ b, ∑ b', kA Y Y' p b b' * (if b ≠ b' then 1 else 0) ≤ |Y p - Y' p| / 2 := by
  have hl := tanh_lip (Y p) (Y' p)
  simp only [Fintype.sum_bool, kA, fA_true, fA_false]
  simp only [ne_eq, not_true_eq_false, Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
    if_true, if_false, mul_zero, mul_one, zero_add, add_zero]
  rcases le_total (Real.tanh (Y p)) (Real.tanh (Y' p)) with h | h
  · rw [abs_of_nonpos (by linarith)] at hl
    rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    linarith [le_abs_self (Y p - Y' p), neg_abs_le (Y p - Y' p)]
  · rw [abs_of_nonneg (by linarith)] at hl
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    linarith [le_abs_self (Y p - Y' p), neg_abs_le (Y p - Y' p)]

/-! ### Product measures -/

theorem dsum_prod {P : Type} [Fintype P] [DecidableEq P] (F : P → Bool → Bool → ℝ) :
    ∑ τ : P → Bool, ∑ τ' : P → Bool, ∏ q, F q (τ q) (τ' q) = ∏ q, ∑ x, ∑ x', F q x x' := by
  have h1 : ∀ τ : P → Bool, ∑ τ' : P → Bool, ∏ q, F q (τ q) (τ' q) =
      ∏ q, ∑ x', F q (τ q) x' := fun τ => by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl (fun τ _ => h1 τ), Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem marg {P : Type} [Fintype P] [DecidableEq P] (k : P → Bool → Bool → ℝ)
    (hk : ∀ q, ∑ x, ∑ x', k q x x' = 1) (p : P) (g : Bool → Bool → ℝ) :
    ∑ τ : P → Bool, ∑ τ' : P → Bool, (∏ q, k q (τ q) (τ' q)) * g (τ p) (τ' p) =
      ∑ x, ∑ x', k p x x' * g x x' := by
  let F : P → Bool → Bool → ℝ := fun q x x' => k q x x' * (if q = p then g x x' else 1)
  have e : ∀ τ τ' : P → Bool,
      (∏ q, k q (τ q) (τ' q)) * g (τ p) (τ' p) = ∏ q, F q (τ q) (τ' q) := by
    intro τ τ'
    simp only [F]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq']
    simp
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun τ' _ => e τ τ')), dsum_prod F,
    Finset.prod_eq_single_of_mem p (mem_univ p) (fun q _ hq => by simp only [F, if_neg hq, mul_one]; exact hk q)]
  simp [F]

end OptRobustCD.L410Aux

open OptRobustCD OptRobustCD.L410Aux Finset in
open scoped Classical in
theorem solution (lam : ℝ) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1) {n : ℕ} (G : SimpleGraph (Fin n))
    (t : ℕ) (ht : 1 ≤ t) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (Y Y' : EVec n)
    (hY : SupportedOn G Y) (hY' : SupportedOn G Y') :
    ∃ μ : (Fin n → Bool) → (Fin n → Bool) → ℝ, (∀ a b, 0 ≤ μ a b) ∧
      (∀ a, ∑ b, μ a b = bpProb G lam t γ Y a) ∧ (∀ b, ∑ a, μ a b = bpProb G lam t γ Y' b) ∧
      ∑ a, ∑ b, μ a b * ((Finset.univ.filter fun v => a v ≠ b v).card : ℝ) ≤
        (1 / 2) * Real.sqrt (∑ v, (ballCard G v (t + 1) : ℝ) ^ 3) * l2 (Y - Y') := by
  let K : (Fin n × Fin n → Bool) → (Fin n × Fin n → Bool) → ℝ :=
    fun τ τ' => ∏ p, kA Y Y' p (τ p) (τ' p)
  have hK0 : ∀ τ τ', 0 ≤ K τ τ' := fun τ τ' =>
    Finset.prod_nonneg (fun p _ => kA_nonneg Y Y' p (τ p) (τ' p))
  have hKrow : ∀ τ, ∑ τ', K τ τ' = roundWeight Y τ := by
    intro τ
    have h : ∑ τ' : Fin n × Fin n → Bool, ∏ p, kA Y Y' p (τ p) (τ' p) =
        ∏ p, ∑ b, kA Y Y' p (τ p) b := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [K]
    rw [h]
    unfold roundWeight
    exact prod_congr rfl (fun p _ => kA_row Y Y' p (τ p))
  have hKcol : ∀ τ', ∑ τ, K τ τ' = roundWeight Y' τ' := by
    intro τ'
    have h : ∑ τ : Fin n × Fin n → Bool, ∏ p, kA Y Y' p (τ p) (τ' p) =
        ∏ p, ∑ b, kA Y Y' p b (τ' p) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [K]
    rw [h]
    unfold roundWeight
    exact prod_congr rfl (fun p _ => kA_col Y Y' p (τ' p))
  let out := bpOut G lam t γ
  -- the joint law, written over pairs `x = (τ, τ')`
  let μ : (Fin n → Bool) → (Fin n → Bool) → ℝ := fun a b =>
    ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
      K x.1 x.2 * (if out x.1 = a ∧ out x.2 = b then 1 else 0)
  -- expectation of any function of the two outputs
  have hexp : ∀ Φ : (Fin n → Bool) → (Fin n → Bool) → ℝ,
      ∑ a, ∑ b, μ a b * Φ a b =
        ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool), K x.1 x.2 * Φ (out x.1) (out x.2) := by
    intro Φ
    simp only [μ, Finset.sum_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_eq_single (out x.1) (fun a ha => Finset.sum_eq_zero (fun b _ => by
      rw [if_neg (fun h => ha h.1.symm)]; ring))]
    rw [Fintype.sum_eq_single (out x.2) (fun b hb => by
      rw [if_neg (fun h => hb h.2.symm)]; ring)]
    rw [if_pos ⟨rfl, rfl⟩]
    ring
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · intro a b
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (hK0 _ _)
    split_ifs <;> norm_num
  · intro a
    simp only [μ]
    rw [Finset.sum_comm]
    have h1 : ∀ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
        ∑ b, K x.1 x.2 * (if out x.1 = a ∧ out x.2 = b then (1 : ℝ) else 0) =
          K x.1 x.2 * (if out x.1 = a then 1 else 0) := by
      intro x
      rw [← Finset.mul_sum]
      congr 1
      by_cases ha : out x.1 = a
      · simp [ha]
      · simp [ha]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Fintype.sum_prod_type]
    unfold bpProb
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    dsimp only
    calc _ = (∑ y, K τ y) * (if out τ = a then (1 : ℝ) else 0) := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hKrow τ]
  · intro b
    simp only [μ]
    rw [Finset.sum_comm]
    have h1 : ∀ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
        ∑ a, K x.1 x.2 * (if out x.1 = a ∧ out x.2 = b then (1 : ℝ) else 0) =
          K x.1 x.2 * (if out x.2 = b then 1 else 0) := by
      intro x
      rw [← Finset.mul_sum]
      congr 1
      by_cases hb : out x.2 = b
      · simp [hb]
      · simp [hb]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Fintype.sum_prod_type, Finset.sum_comm]
    unfold bpProb
    refine Finset.sum_congr rfl (fun τ' _ => ?_)
    dsimp only
    calc _ = (∑ x, K x τ') * (if out τ' = b then (1 : ℝ) else 0) := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hKcol τ']
  · -- the expected number of disagreements
    rw [hexp]
    -- indicator of the dependency region of `v`
    let I : Fin n → Fin n × Fin n → ℝ := fun v p =>
      if G.Adj p.1 p.2 ∧ G.edist v p.1 ≤ (t : ℕ∞) then 1 else 0
    let D : (Fin n × Fin n → Bool) → (Fin n × Fin n → Bool) → Fin n × Fin n → ℝ :=
      fun τ τ' p => if τ p ≠ τ' p then 1 else 0
    have hcount : ∀ τ τ' : Fin n × Fin n → Bool,
        ((Finset.univ.filter fun v => out τ v ≠ out τ' v).card : ℝ) ≤
          ∑ v, ∑ p, I v p * D τ τ' p := by
      intro τ τ'
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_le_sum
      intro v _
      split_ifs with hv
      · by_contra hlt
        push_neg at hlt
        apply hv
        apply out_loc G lam γ t τ τ' v
        intro y z hyz hd
        by_contra hne
        have hle : I v (y, z) * D τ τ' (y, z) ≤ ∑ p, I v p * D τ τ' p :=
          Finset.single_le_sum (f := fun p => I v p * D τ τ' p)
            (fun p _ => mul_nonneg (by simp only [I]; split_ifs <;> norm_num)
              (by simp only [D]; split_ifs <;> norm_num)) (mem_univ (y, z))
        have h1 : I v (y, z) * D τ τ' (y, z) = 1 := by
          simp only [I, D]; rw [if_pos ⟨hyz, hd⟩, if_pos hne]; norm_num
        linarith
      · exact Finset.sum_nonneg (fun p _ => mul_nonneg (by simp only [I]; split_ifs <;> norm_num)
          (by simp only [D]; split_ifs <;> norm_num))
    -- coverage numbers
    let c : Fin n × Fin n → ℝ := fun p => ∑ v, I v p
    have hstep1 : ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
        K x.1 x.2 * ((Finset.univ.filter fun v => out x.1 v ≠ out x.2 v).card : ℝ) ≤
          ∑ p, c p * (|Y p - Y' p| / 2) := by
      calc _ ≤ ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
            K x.1 x.2 * ∑ v, ∑ p, I v p * D x.1 x.2 p :=
            Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hcount x.1 x.2) (hK0 _ _))
        _ = ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool), ∑ v, ∑ p,
              K x.1 x.2 * (I v p * D x.1 x.2 p) := by simp only [Finset.mul_sum]
        _ = ∑ v, ∑ p, ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
              K x.1 x.2 * (I v p * D x.1 x.2 p) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun v _ => Finset.sum_comm)
        _ = ∑ p, ∑ v, ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
              K x.1 x.2 * (I v p * D x.1 x.2 p) := Finset.sum_comm
        _ = ∑ p, c p * ∑ x : (Fin n × Fin n → Bool) × (Fin n × Fin n → Bool),
              K x.1 x.2 * D x.1 x.2 p := by
            simp only [c, Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun v _ => ?_))
            ring
        _ ≤ ∑ p, c p * (|Y p - Y' p| / 2) := by
            apply Finset.sum_le_sum
            intro p _
            have hc0 : 0 ≤ c p := Finset.sum_nonneg (fun v _ => by
              simp only [I]; split_ifs <;> norm_num)
            apply mul_le_mul_of_nonneg_left _ hc0
            rw [Fintype.sum_prod_type]
            have hm := marg (fun q => kA Y Y' q) (fun q => kA_total Y Y' q) p
              (fun b b' => if b ≠ b' then 1 else 0)
            simp only [K, D]
            rw [hm]
            exact kA_disagree Y Y' p
    -- Cauchy–Schwarz and the ball bound
    have hc_le : ∀ p, c p ≤ (if G.Adj p.1 p.2 then (ballCard G p.1 (t + 1) : ℝ) else 0) := by
      intro p
      simp only [c, I]
      split_ifs with hadj
      · rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        unfold ballCard
        have hsub : (Finset.univ.filter fun v => G.Adj p.1 p.2 ∧ G.edist v p.1 ≤ (t : ℕ∞)) ⊆
            Finset.univ.filter fun u => G.edist p.1 u ≤ ((t + 1 : ℕ) : ℕ∞) := by
          intro v hv
          simp only [mem_filter, mem_univ, true_and] at hv ⊢
          rw [SimpleGraph.edist_comm]
          exact hv.2.trans (by exact_mod_cast Nat.le_succ t)
        exact_mod_cast Finset.card_le_card hsub
      · simp [hadj]
    have hc0 : ∀ p, 0 ≤ c p := fun p => Finset.sum_nonneg (fun v _ => by
      simp only [I]; split_ifs <;> norm_num)
    have hdeg : ∀ y, ((Finset.univ.filter fun z => G.Adj y z).card : ℝ) ≤
        (ballCard G y (t + 1) : ℝ) := by
      intro y
      unfold ballCard
      have hsub : (Finset.univ.filter fun z => G.Adj y z) ⊆
          Finset.univ.filter fun u => G.edist y u ≤ ((t + 1 : ℕ) : ℕ∞) := by
        intro z hz
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        rw [SimpleGraph.edist_eq_one_iff_adj.mpr hz]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le t)
      exact_mod_cast Finset.card_le_card hsub
    have hcsq : ∑ p, c p ^ 2 ≤ ∑ v, (ballCard G v (t + 1) : ℝ) ^ 3 := by
      calc ∑ p, c p ^ 2 ≤ ∑ p : Fin n × Fin n,
            (if G.Adj p.1 p.2 then (ballCard G p.1 (t + 1) : ℝ) else 0) ^ 2 :=
            Finset.sum_le_sum (fun p _ => pow_le_pow_left₀ (hc0 p) (hc_le p) 2)
        _ = ∑ y, ((Finset.univ.filter fun z => G.Adj y z).card : ℝ) *
              (ballCard G y (t + 1) : ℝ) ^ 2 := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [Finset.card_filter]
            push_cast
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            split_ifs <;> simp
        _ ≤ ∑ y, (ballCard G y (t + 1) : ℝ) * (ballCard G y (t + 1) : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hdeg y) (sq_nonneg _))
        _ = ∑ v, (ballCard G v (t + 1) : ℝ) ^ 3 := by
            refine Finset.sum_congr rfl (fun y _ => ?_); ring
    have hcs : ∑ p, c p * |Y p - Y' p| ≤
        Real.sqrt (∑ p, c p ^ 2) * Real.sqrt (∑ p, |Y p - Y' p| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    have hl2 : Real.sqrt (∑ p, |Y p - Y' p| ^ 2) = l2 (Y - Y') := by
      unfold l2
      congr 1
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [sq_abs, Pi.sub_apply]
    have hsq : Real.sqrt (∑ p, c p ^ 2) ≤ Real.sqrt (∑ v, (ballCard G v (t + 1) : ℝ) ^ 3) :=
      Real.sqrt_le_sqrt hcsq
    have hl0 : 0 ≤ l2 (Y - Y') := Real.sqrt_nonneg _
    have hfinal : ∑ p, c p * (|Y p - Y' p| / 2) = (1 / 2) * ∑ p, c p * |Y p - Y' p| := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [hl2] at hcs
    calc _ ≤ ∑ p, c p * (|Y p - Y' p| / 2) := hstep1
      _ = (1 / 2) * ∑ p, c p * |Y p - Y' p| := hfinal
      _ ≤ (1 / 2) * (Real.sqrt (∑ p, c p ^ 2) * l2 (Y - Y')) := by linarith
      _ ≤ (1 / 2) * (Real.sqrt (∑ v, (ballCard G v (t + 1) : ℝ) ^ 3) * l2 (Y - Y')) := by
          have := mul_le_mul_of_nonneg_right hsq hl0
          linarith
      _ = _ := by ring
