-- Prove2me | solution 1 for PutermanMDP.SemiMarkov.finite_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T18:00:18.651558+00:00
-- url     : https://prove2.me/submissions/67261cbd-1fa2-4829-ad05-8dff2c20334f

import Mathlib
import Definitions.Def_PutermanMDP_SemiMarkov_Deviation

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Matrix

namespace PutermanMDP.SemiMarkov.FEv

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma pmf_sum_toReal (p : PMF S) : ∑ j, (p j).toReal = 1 := by
  have h := PMF.tsum_coe p
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top p j), h]
  simp

lemma epochLaw_toReal (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    (epochLaw M d n s j).toReal = ((transitionMatrix M d) ^ n) s j := by
  induction n generalizing j with
  | zero =>
    simp only [epochLaw, PMF.pure_apply, pow_zero, Matrix.one_apply]
    by_cases h : s = j
    · subst h; simp
    · simp [h, Ne.symm h]
  | succ n ih =>
    simp only [epochLaw, PMF.bind_apply, tsum_fintype, pow_succ, Matrix.mul_apply]
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.toReal_mul, ih]
    rfl

lemma P_nonneg (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    0 ≤ ((transitionMatrix M d) ^ n) s j := by
  rw [← epochLaw_toReal]; exact ENNReal.toReal_nonneg

lemma P_rowsum (M : Model S) (d : Rule M) (n : ℕ) (s : S) :
    ∑ j, ((transitionMatrix M d) ^ n) s j = 1 := by
  simp_rw [← epochLaw_toReal]; exact pmf_sum_toReal _

lemma P_le_one (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    ((transitionMatrix M d) ^ n) s j ≤ 1 := by
  rw [← P_rowsum M d n s]
  exact Finset.single_le_sum (fun i _ => P_nonneg M d n s i) (Finset.mem_univ j)

/-- partial sums of powers -/
noncomputable def T (M : Model S) (d : Rule M) (n : ℕ) : Matrix S S ℝ :=
  ∑ k ∈ Finset.range n, (transitionMatrix M d) ^ k

noncomputable def Ces (M : Model S) (d : Rule M) (n : ℕ) : Matrix S S ℝ :=
  ((n : ℝ)⁻¹) • T M d n

lemma Ces_apply (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    Ces M d n s j = (∑ k ∈ Finset.range n, ((transitionMatrix M d) ^ k) s j) / n := by
  simp only [Ces, T, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [div_eq_inv_mul]

lemma cesaro_eq (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    cesaro M d n s j = Ces M d n s j := by
  rw [Ces_apply]; simp only [cesaro, epochLaw_toReal]

lemma Ces_nonneg (M : Model S) (d : Rule M) (n : ℕ) (s j : S) : 0 ≤ Ces M d n s j := by
  rw [Ces_apply]
  exact div_nonneg (Finset.sum_nonneg (fun k _ => P_nonneg M d k s j)) (Nat.cast_nonneg n)

lemma Ces_le_one (M : Model S) (d : Rule M) (n : ℕ) (s j : S) : Ces M d n s j ≤ 1 := by
  rw [Ces_apply]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [div_le_one (by exact_mod_cast hn)]
    calc ∑ k ∈ Finset.range n, ((transitionMatrix M d) ^ k) s j
        ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => P_le_one M d k s j)
      _ = n := by simp

lemma Ces_rowsum (M : Model S) (d : Rule M) (n : ℕ) (hn : 1 ≤ n) (s : S) :
    ∑ j, Ces M d n s j = 1 := by
  simp_rw [Ces_apply]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [P_rowsum]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [this]

lemma T_mul_P (M : Model S) (d : Rule M) (n : ℕ) :
    T M d n * transitionMatrix M d - T M d n = (transitionMatrix M d) ^ n - 1 := by
  simp only [T, Finset.sum_mul, ← pow_succ]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => (transitionMatrix M d) ^ k)]
  simp

lemma P_mul_T (M : Model S) (d : Rule M) (n : ℕ) :
    transitionMatrix M d * T M d n - T M d n = (transitionMatrix M d) ^ n - 1 := by
  simp only [T, Finset.mul_sum, ← pow_succ']
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => (transitionMatrix M d) ^ k)]
  simp

lemma pow_sub_one_abs (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    |((transitionMatrix M d) ^ n - 1) s j| ≤ 1 := by
  rw [Matrix.sub_apply, abs_le]
  have h1 := P_nonneg M d n s j
  have h2 := P_le_one M d n s j
  have h3 : (0 : ℝ) ≤ (1 : Matrix S S ℝ) s j := by
    rw [Matrix.one_apply]; split_ifs <;> norm_num
  have h4 : (1 : Matrix S S ℝ) s j ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> norm_num
  constructor <;> linarith

lemma inv_mul_tendsto_zero (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) * c n) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n => ?_) (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
  calc ((n : ℝ))⁻¹ * |c n| ≤ ((n : ℝ))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (hc n) (inv_nonneg.2 (Nat.cast_nonneg n))
    _ = _ := mul_one _

lemma Ces_mul_P_sub (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    (Ces M d n * transitionMatrix M d) s j - Ces M d n s j =
      ((n : ℝ)⁻¹) * (((transitionMatrix M d) ^ n - 1) s j) := by
  have := congrArg (fun A : Matrix S S ℝ => (((n : ℝ)⁻¹) • A) s j) (T_mul_P M d n)
  simp only [smul_sub, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    ← Matrix.smul_mul] at this
  simpa [Ces, Matrix.sub_apply, mul_sub] using this

lemma P_mul_Ces_sub (M : Model S) (d : Rule M) (n : ℕ) (s j : S) :
    (transitionMatrix M d * Ces M d n) s j - Ces M d n s j =
      ((n : ℝ)⁻¹) * (((transitionMatrix M d) ^ n - 1) s j) := by
  have := congrArg (fun A : Matrix S S ℝ => (((n : ℝ)⁻¹) • A) s j) (P_mul_T M d n)
  simp only [smul_sub, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    ← Matrix.mul_smul] at this
  simpa [Ces, Matrix.sub_apply, mul_sub] using this

/-- entrywise limit of a matrix product with a constant matrix on the right -/
lemma tendsto_mul_right {A : ℕ → Matrix S S ℝ} {L : Matrix S S ℝ} (B : Matrix S S ℝ)
    (h : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (L i j))) (i j : S) :
    Tendsto (fun n => (A n * B) i j) atTop (𝓝 ((L * B) i j)) := by
  simp only [Matrix.mul_apply]
  exact tendsto_finset_sum _ (fun k _ => (h i k).mul_const _)

lemma tendsto_mul_left {A : ℕ → Matrix S S ℝ} {L : Matrix S S ℝ} (B : Matrix S S ℝ)
    (h : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (L i j))) (i j : S) :
    Tendsto (fun n => (B * A n) i j) atTop (𝓝 ((B * L) i j)) := by
  simp only [Matrix.mul_apply]
  exact tendsto_finset_sum _ (fun k _ => (h k j).const_mul _)

/-- a subsequential limit of the Cesaro averages is invariant on both sides -/
lemma cluster_inv (M : Model S) (d : Rule M) (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (L : Matrix S S ℝ) (hL : ∀ i j, Tendsto (fun n => Ces M d (ψ n) i j) atTop (𝓝 (L i j))) :
    L * transitionMatrix M d = L ∧ transitionMatrix M d * L = L := by
  have hz : ∀ i j, Tendsto (fun n => ((ψ n : ℕ) : ℝ)⁻¹ *
      (((transitionMatrix M d) ^ (ψ n) - 1) i j)) atTop (𝓝 0) := fun i j =>
    (inv_mul_tendsto_zero (fun n => ((transitionMatrix M d) ^ n - 1) i j)
      (fun n => pow_sub_one_abs M d n i j)).comp hψ
  constructor
  · ext i j
    have h1 := (tendsto_mul_right (transitionMatrix M d) hL i j).sub (hL i j)
    have h2 := hz i j
    simp_rw [Ces_mul_P_sub] at h1
    have := tendsto_nhds_unique h1 h2
    linarith
  · ext i j
    have h1 := (tendsto_mul_left (transitionMatrix M d) hL i j).sub (hL i j)
    have h2 := hz i j
    simp_rw [P_mul_Ces_sub] at h1
    have := tendsto_nhds_unique h1 h2
    linarith

lemma L_mul_pow (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (h : L * transitionMatrix M d = L) (k : ℕ) : L * (transitionMatrix M d) ^ k = L := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, h]

lemma pow_mul_L (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (h : transitionMatrix M d * L = L) (k : ℕ) : (transitionMatrix M d) ^ k * L = L := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, ih, h]

lemma L_mul_Ces (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (h : L * transitionMatrix M d = L) (n : ℕ) (hn : 1 ≤ n) : L * Ces M d n = L := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Ces, T, Matrix.mul_smul, Finset.mul_sum, L_mul_pow M d L h]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hn', one_smul]

lemma Ces_mul_L (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (h : transitionMatrix M d * L = L) (n : ℕ) (hn : 1 ≤ n) : Ces M d n * L = L := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Ces, T, Matrix.smul_mul, Finset.sum_mul, pow_mul_L M d L h]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hn', one_smul]

lemma cluster_unique (M : Model S) (d : Rule M) (ψ₁ ψ₂ : ℕ → ℕ)
    (h₁ : Tendsto ψ₁ atTop atTop) (h₂ : Tendsto ψ₂ atTop atTop) (L₁ L₂ : Matrix S S ℝ)
    (hL₁ : ∀ i j, Tendsto (fun n => Ces M d (ψ₁ n) i j) atTop (𝓝 (L₁ i j)))
    (hL₂ : ∀ i j, Tendsto (fun n => Ces M d (ψ₂ n) i j) atTop (𝓝 (L₂ i j))) :
    L₂ * L₁ = L₂ ∧ L₂ * L₁ = L₁ := by
  obtain ⟨_, hP₁⟩ := cluster_inv M d ψ₁ h₁ L₁ hL₁
  obtain ⟨hL₂P, _⟩ := cluster_inv M d ψ₂ h₂ L₂ hL₂
  have ev₁ : ∀ᶠ n in atTop, 1 ≤ ψ₁ n := h₁.eventually_ge_atTop 1
  have ev₂ : ∀ᶠ n in atTop, 1 ≤ ψ₂ n := h₂.eventually_ge_atTop 1
  constructor
  · ext i j
    have t := tendsto_mul_left L₂ hL₁ i j
    have t2 : Tendsto (fun n => (L₂ * Ces M d (ψ₁ n)) i j) atTop (𝓝 (L₂ i j)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev₁] with n hn
      rw [L_mul_Ces M d L₂ hL₂P _ hn]
    exact tendsto_nhds_unique t t2
  · ext i j
    have t := tendsto_mul_right L₁ hL₂ i j
    have t2 : Tendsto (fun n => (Ces M d (ψ₂ n) * L₁) i j) atTop (𝓝 (L₁ i j)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev₂] with n hn
      rw [Ces_mul_L M d L₁ hP₁ _ hn]
    exact tendsto_nhds_unique t t2

/-- the compact box of matrices with entries in [0,1], as functions -/
def box (S : Type*) : Set (S → S → ℝ) :=
  Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1))

lemma box_compact : IsCompact (box S) :=
  isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))

lemma Ces_mem_box (M : Model S) (d : Rule M) (n : ℕ) :
    (fun i j => Ces M d n i j) ∈ box S := by
  intro i _ j _
  exact ⟨Ces_nonneg M d n i j, Ces_le_one M d n i j⟩

lemma entrywise_of_pi {x : ℕ → S → S → ℝ} {a : S → S → ℝ}
    (h : Tendsto x atTop (𝓝 a)) (i j : S) : Tendsto (fun n => x n i j) atTop (𝓝 (a i j)) :=
  tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j

lemma pi_of_entrywise {x : ℕ → S → S → ℝ} {a : S → S → ℝ}
    (h : ∀ i j, Tendsto (fun n => x n i j) atTop (𝓝 (a i j))) : Tendsto x atTop (𝓝 a) :=
  tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => h i j))

/-- Cesaro convergence for a finite stochastic matrix -/
theorem ces_converges (M : Model S) (d : Rule M) :
    ∃ L : Matrix S S ℝ, ∀ i j, Tendsto (fun n => Ces M d n i j) atTop (𝓝 (L i j)) := by
  obtain ⟨L, -, φ, hφ, hL⟩ := (box_compact (S := S)).tendsto_subseq (Ces_mem_box M d)
  refine ⟨L, fun i j => ?_⟩
  have hL' : ∀ i j, Tendsto (fun n => Ces M d (φ n) i j) atTop (𝓝 (L i j)) :=
    fun i j => entrywise_of_pi hL i j
  have key : Tendsto (fun n => (fun i j => Ces M d n i j : S → S → ℝ)) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL2⟩ :=
      (box_compact (S := S)).tendsto_subseq (fun n => Ces_mem_box M d (ns n))
    refine ⟨ψ, ?_⟩
    have hL2' : ∀ i j, Tendsto (fun n => Ces M d (ns (ψ n)) i j) atTop (𝓝 (L' i j)) :=
      fun i j => entrywise_of_pi hL2 i j
    have hnsψ : Tendsto (fun n => ns (ψ n)) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨e1, e2⟩ := cluster_unique M d φ (fun n => ns (ψ n)) hφ.tendsto_atTop hnsψ
      L L' hL' hL2'
    have hEq : (L' : Matrix S S ℝ) = L := e1.symm.trans e2
    have : L' = L := hEq
    rw [← this]
    exact pi_of_entrywise hL2'
  exact entrywise_of_pi key i j

/-! ## Part 2: structure of the limit under unichain -/

lemma exists_pow_pos (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (hconv : ∀ i j, Tendsto (fun n => Ces M d n i j) atTop (𝓝 (L i j))) (i j : S)
    (h : 0 < L i j) : ∃ n, 0 < ((transitionMatrix M d) ^ n) i j := by
  by_contra hne
  simp only [not_exists, not_lt] at hne
  have h0 : ∀ n, Ces M d n i j = 0 := by
    intro n
    rw [Ces_apply, Finset.sum_eq_zero (fun k _ => le_antisymm (hne k) (P_nonneg M d k i j))]
    simp
  have h1 : Tendsto (fun n => Ces M d n i j) atTop (𝓝 0) := by
    simp_rw [h0]; exact tendsto_const_nhds
  have := tendsto_nhds_unique (hconv i j) h1
  linarith

lemma pow_mulVec (P : Matrix S S ℝ) (v : S → ℝ) (h : P *ᵥ v = v) (n : ℕ) :
    (P ^ n) *ᵥ v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, ih]

lemma max_closed (M : Model S) (d : Rule M) (v : S → ℝ)
    (hv : transitionMatrix M d *ᵥ v = v) (k : S) (hk : ∀ i, v i ≤ v k) (n : ℕ) (j : S)
    (hj : 0 < ((transitionMatrix M d) ^ n) k j) : v j = v k := by
  have e := congrFun (pow_mulVec _ v hv n) k
  simp only [Matrix.mulVec, dotProduct] at e
  have hs := P_rowsum M d n k
  have hz : ∑ x, ((transitionMatrix M d) ^ n) k x * (v k - v x) = 0 := by
    rw [Finset.sum_congr rfl (fun x _ => mul_sub _ _ _), Finset.sum_sub_distrib,
      ← Finset.sum_mul, hs, e]
    ring
  have hnn : ∀ x ∈ (Finset.univ : Finset S),
      0 ≤ ((transitionMatrix M d) ^ n) k x * (v k - v x) :=
    fun x _ => mul_nonneg (P_nonneg M d n k x) (sub_nonneg.2 (hk x))
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz j (Finset.mem_univ j)
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

lemma recurrent_of_pos (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (hconv : ∀ i j, Tendsto (fun n => Ces M d n i j) atTop (𝓝 (L i j))) (j : S)
    (h : 0 < L j j) : Recurrent M d j := by
  unfold Recurrent
  by_contra hne
  have hb : ∀ n : ℕ, Ces M d n j j ≤ (∑' n, epochLaw M d n j j).toReal / n := by
    intro n
    rw [Ces_apply]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc ∑ k ∈ Finset.range n, ((transitionMatrix M d) ^ k) j j
        = (∑ k ∈ Finset.range n, epochLaw M d k j j).toReal := by
          rw [ENNReal.toReal_sum (fun k _ => PMF.apply_ne_top _ _)]
          simp [epochLaw_toReal]
      _ ≤ (∑' n, epochLaw M d n j j).toReal := ENNReal.toReal_mono hne (ENNReal.sum_le_tsum _)
  have := le_of_tendsto_of_tendsto' (hconv j j)
    (tendsto_const_div_atTop_nhds_zero_nat ((∑' n, epochLaw M d n j j).toReal)) hb
  linarith

lemma pow_pos_of_accessible (M : Model S) (d : Rule M) (s j : S)
    (h : Accessible M d s j) : ∃ n, 0 < ((transitionMatrix M d) ^ n) s j := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← epochLaw_toReal]; exact ENNReal.toReal_pos (ne_of_gt hn) (PMF.apply_ne_top _ _)⟩

lemma exists_L_pos (L : Matrix S S ℝ) (hrow : ∀ i, ∑ j, L i j = 1) (i : S) :
    ∃ j, 0 < L i j := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have : ∑ j, L i j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
  linarith [hrow i]

lemma diag_pos (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (hconv : ∀ i j, Tendsto (fun n => Ces M d n i j) atTop (𝓝 (L i j)))
    (hPL : transitionMatrix M d * L = L) (k j : S) (h : 0 < L k j) : 0 < L j j := by
  let w : S → ℝ := fun i => L i j
  have hw : transitionMatrix M d *ᵥ w = w := by
    funext i
    have := congrFun (congrFun hPL i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, w] using this
  obtain ⟨k', -, hk'⟩ := Finset.exists_max_image Finset.univ w ⟨k, Finset.mem_univ k⟩
  have hk'' : ∀ i, w i ≤ w k' := fun i => hk' i (Finset.mem_univ i)
  have hpos : 0 < L k' j := lt_of_lt_of_le h (hk'' k)
  obtain ⟨n, hn⟩ := exists_pow_pos M d L hconv k' j hpos
  have := max_closed M d w hw k' hk'' n j hn
  show 0 < w j
  rw [this]; exact hpos

lemma harmonic_const [Nonempty S] (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (hconv : ∀ i j, Tendsto (fun n => Ces M d n i j) atTop (𝓝 (L i j)))
    (hPL : transitionMatrix M d * L = L) (hrow : ∀ i, ∑ j, L i j = 1)
    (hU : Unichain M d) (v : S → ℝ) (hv : transitionMatrix M d *ᵥ v = v) :
    ∀ s t, v s = v t := by
  obtain ⟨k1, -, hk1⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  obtain ⟨k2, -, hk2⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hk1' : ∀ i, v i ≤ v k1 := fun i => hk1 i (Finset.mem_univ i)
  have hk2' : ∀ i, v k2 ≤ v i := fun i => hk2 i (Finset.mem_univ i)
  obtain ⟨j1, hj1⟩ := exists_L_pos L hrow k1
  obtain ⟨n1, hn1⟩ := exists_pow_pos M d L hconv k1 j1 hj1
  have e1 : v j1 = v k1 := max_closed M d v hv k1 hk1' n1 j1 hn1
  have r1 : Recurrent M d j1 := recurrent_of_pos M d L hconv j1 (diag_pos M d L hconv hPL k1 j1 hj1)
  obtain ⟨j2, hj2⟩ := exists_L_pos L hrow k2
  obtain ⟨n2, hn2⟩ := exists_pow_pos M d L hconv k2 j2 hj2
  have hv' : transitionMatrix M d *ᵥ (-v) = -v := by rw [Matrix.mulVec_neg, hv]
  have e2' := max_closed M d (-v) hv' k2 (fun i => by simp only [Pi.neg_apply]; linarith [hk2' i]) n2 j2 hn2
  simp only [Pi.neg_apply, neg_inj] at e2'
  have r2 : Recurrent M d j2 := recurrent_of_pos M d L hconv j2 (diag_pos M d L hconv hPL k2 j2 hj2)
  obtain ⟨n3, hn3⟩ := pow_pos_of_accessible M d j1 j2 (hU.2 j1 j2 r1 r2)
  have e3 : v j2 = v j1 := max_closed M d v hv j1 (fun i => by rw [e1]; exact hk1' i) n3 j2 hn3
  intro s t
  have := hk1' s; have := hk2' s; have := hk1' t; have := hk2' t
  linarith

/-! ## Part 3: positive holding times -/

lemma ruleTime_ge (M : Model S) (d : Rule M) (hNE : Nonexplosive M) :
    ∃ c : ℝ, 0 < c ∧ ∀ s, c ≤ ruleTime M d s := by
  obtain ⟨ε, δ, hε, hδ, h⟩ := hNE
  refine ⟨δ * ε, mul_pos hδ hε, fun s => ?_⟩
  have hmt : ∀ a, δ * ε ≤ meanTime M s a := by
    intro a
    haveI := M.holding_probability s a
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := M.holding s a)
      (f := fun t : ℝ≥0 => (t : ℝ)) (Filter.Eventually.of_forall (fun t => t.2))
      (M.holding_integrable s a) δ
    have hA : MeasurableSet {x : ℝ≥0 | (x : ℝ) ≤ δ} :=
      measurableSet_le (by fun_prop) measurable_const
    have h1 : (M.holding s a).real {x : ℝ≥0 | (x : ℝ) ≤ δ} ≤ 1 - ε :=
      ENNReal.toReal_le_of_le_ofReal (by linarith [(h s a).2]) (h s a).1
    have h2 : (M.holding s a).real {x : ℝ≥0 | (x : ℝ) ≤ δ}ᶜ ≤
        (M.holding s a).real {x : ℝ≥0 | δ ≤ (x : ℝ)} := by
      refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      exact le_of_lt hx
    rw [measureReal_compl hA, probReal_univ] at h2
    have hmeas : ε ≤ (M.holding s a).real {x : ℝ≥0 | δ ≤ (x : ℝ)} := by linarith
    calc δ * ε ≤ δ * (M.holding s a).real {x : ℝ≥0 | δ ≤ (x : ℝ)} :=
          mul_le_mul_of_nonneg_left hmeas hδ.le
      _ ≤ meanTime M s a := hm
  have hsum1 : Summable (fun a => (d.action s a).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have htot : ∑' a, (d.action s a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top _ _), PMF.tsum_coe]
    simp
  calc δ * ε = ∑' a, (d.action s a).toReal * (δ * ε) := by
        rw [tsum_mul_right, htot, one_mul]
    _ ≤ ruleTime M d s := by
        unfold ruleTime
        exact Summable.tsum_le_tsum
          (fun a => mul_le_mul_of_nonneg_left (hmt a) ENNReal.toReal_nonneg)
          (hsum1.mul_right _) (d.time_summable s)

/-! ## Part 4: the gain -/

lemma Ces_mulVec (M : Model S) (d : Rule M) (v : S → ℝ) (n : ℕ) (s : S) :
    ∑ j, Ces M d n s j * v j =
      (∑ k ∈ Finset.range n, ∑ j, ((transitionMatrix M d) ^ k) s j * v j) / n := by
  simp_rw [Ces_apply, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

lemma sum_epoch (M : Model S) (d : Rule M) (v : S → ℝ) (n : ℕ) (s : S) :
    ∑ k ∈ Finset.range n, ∑' j, (epochLaw M d k s j).toReal * v j =
      n * ∑ j, Ces M d n s j * v j := by
  rw [Ces_mulVec]
  simp_rw [tsum_fintype, epochLaw_toReal]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [mul_div_cancel₀ _ hn']

lemma gain_eq (M : Model S) (d : Rule M) (L : Matrix S S ℝ)
    (hconv : ∀ i j, Tendsto (fun n => Ces M d n i j) atTop (𝓝 (L i j))) (s : S)
    (hβ : 0 < ∑ j, L s j * ruleTime M d j) :
    gain M d s = (((∑ j, L s j * ruleReward M d j) / (∑ j, L s j * ruleTime M d j) : ℝ) : EReal) := by
  have ha : ∀ v : S → ℝ, Tendsto (fun n => ∑ j, Ces M d n s j * v j) atTop
      (𝓝 (∑ j, L s j * v j)) := fun v =>
    tendsto_finset_sum _ (fun j _ => (hconv s j).mul_const _)
  have hratio : Tendsto (fun n => rewardRatio M d n s) atTop
      (𝓝 ((∑ j, L s j * ruleReward M d j) / (∑ j, L s j * ruleTime M d j))) := by
    have hnum := (ha (ruleReward M d)).comp (tendsto_add_atTop_nat 1)
    have hden := (ha (ruleTime M d)).mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [mul_one] at hden
    have hq := hnum.div hden hβ.ne'
    refine hq.congr' ?_
    have hpos := (ha (ruleTime M d)).eventually (lt_mem_nhds hβ)
    filter_upwards [hpos, eventually_ge_atTop 1] with n hB hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [Pi.div_apply, Function.comp, rewardRatio, expectedReward, expectedTime, sum_epoch]
    push_cast
    field_simp
  unfold gain
  exact ((continuous_coe_real_ereal.tendsto _).comp hratio).liminf_eq

/-! ## Part 5: assembly -/

theorem main {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M) (hU : Unichain M d) :
    (∃ scalar : ℝ, ∀ s, gain M d s = (scalar : EReal)) ∧
    ∀ s, ((1 - transitionMatrix M d + cesaroMatrix M d)⁻¹ * (1 - cesaroMatrix M d)).mulVec
        (fun s => ruleReward M d s - (gain M d s).toReal * ruleTime M d s) s =
      ruleReward M d s - (gain M d s).toReal * ruleTime M d s +
        ∑ j, transitionMatrix M d s j *
          ((1 - transitionMatrix M d + cesaroMatrix M d)⁻¹ * (1 - cesaroMatrix M d)).mulVec
            (fun s => ruleReward M d s - (gain M d s).toReal * ruleTime M d s) j := by
  obtain ⟨L, hconv⟩ := ces_converges M d
  obtain ⟨hLP, hPL⟩ := cluster_inv M d id tendsto_id L hconv
  have hLL : L * L = L := (cluster_unique M d id id tendsto_id tendsto_id L L hconv hconv).1
  have hrow : ∀ i, ∑ j, L i j = 1 := by
    intro i
    have t := tendsto_finset_sum (Finset.univ : Finset S) (fun j _ => hconv i j)
    have t2 : Tendsto (fun n => ∑ j, Ces M d n i j) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Ces_rowsum M d n hn i]
    exact tendsto_nhds_unique t t2
  have hnn : ∀ i j, 0 ≤ L i j := fun i j => ge_of_tendsto' (hconv i j) (fun n => Ces_nonneg M d n i j)
  have hPstar : cesaroMatrix M d = L := by
    ext i j
    show limitingMatrix M d i j = L i j
    unfold limitingMatrix
    simp_rw [cesaro_eq]
    exact (hconv i j).liminf_eq
  -- rows of L agree
  have hcols : ∀ s t j, L s j = L t j := by
    intro s t j
    have hw : transitionMatrix M d *ᵥ (fun i => L i j) = (fun i => L i j) := by
      funext i
      have := congrFun (congrFun hPL i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    exact harmonic_const M d L hconv hPL hrow hU _ hw s t
  obtain ⟨cy, hcy, hy⟩ := ruleTime_ge M d hNE
  have hβ : ∀ s, cy ≤ ∑ j, L s j * ruleTime M d j := by
    intro s
    calc cy = ∑ j, L s j * cy := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ ∑ j, L s j * ruleTime M d j :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (hnn s j))
  let s0 : S := Classical.arbitrary S
  set α := ∑ j, L s0 j * ruleReward M d j with hα
  set β := ∑ j, L s0 j * ruleTime M d j with hβdef
  have hβpos : 0 < β := lt_of_lt_of_le hcy (hβ s0)
  have hαs : ∀ s, ∑ j, L s j * ruleReward M d j = α := fun s =>
    Finset.sum_congr rfl (fun j _ => by rw [hcols s s0 j])
  have hβs : ∀ s, ∑ j, L s j * ruleTime M d j = β := fun s =>
    Finset.sum_congr rfl (fun j _ => by rw [hcols s s0 j])
  have hgain : ∀ s, gain M d s = ((α / β : ℝ) : EReal) := by
    intro s
    rw [gain_eq M d L hconv s (lt_of_lt_of_le hcy (hβ s)), hαs, hβs]
  refine ⟨⟨α / β, hgain⟩, ?_⟩
  have hg : ∀ s, (gain M d s).toReal = α / β := fun s => by rw [hgain s]; rfl
  simp only [hg, hPstar]
  set P := transitionMatrix M d with hP
  set f : S → ℝ := fun s => ruleReward M d s - α / β * ruleTime M d s with hf
  have hLf : L *ᵥ f = 0 := by
    funext s
    simp only [Matrix.mulVec, dotProduct, hf, Pi.zero_apply, mul_sub]
    rw [Finset.sum_sub_distrib, hαs]
    have : ∑ x, L s x * (α / β * ruleTime M d x) = α / β * β := by
      rw [← hβs s, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, div_mul_cancel₀ _ hβpos.ne', sub_self]
  have hLmat : L * (1 - P + L) = L := by
    rw [mul_add, mul_sub, mul_one, hLP, sub_self, zero_add, hLL]
  have hdet : IsUnit (1 - P + L).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hx0
    have hLx : L *ᵥ x = 0 := by
      rw [← hLmat, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have hPx : P *ᵥ x = x := by
      have h' := hx
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hLx, add_zero,
        sub_eq_zero] at h'
      exact h'.symm
    let X : Matrix S S ℝ := Matrix.of (fun i _ => x i)
    have hPX : P * X = X := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [X, Matrix.of_apply]
      have := congrFun hPx i
      simpa [Matrix.mulVec, dotProduct] using this
    funext s
    have t := tendsto_mul_right X hconv s s
    have t2 : Tendsto (fun n => (Ces M d n * X) s s) atTop (𝓝 (X s s)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Ces_mul_L M d X hPX n hn]
    have e := tendsto_nhds_unique t t2
    have e2 := congrFun hLx s
    rw [Matrix.mul_apply] at e
    simp only [X, Matrix.of_apply] at e
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at e2
    simp only [Pi.zero_apply]
    rw [← e]
    exact e2
  set Z := (1 - P + L)⁻¹ with hZdef
  have hZ : (1 - P + L) * Z = 1 := Matrix.mul_nonsing_inv _ hdet
  have hLZ : L * Z = L := by
    calc L * Z = (L * (1 - P + L)) * Z := by rw [hLmat]
      _ = L := by rw [mul_assoc, hZ, mul_one]
  have h1P : (1 - P) * Z = 1 - L := by
    have e : (1 - P) = (1 - P + L) - L := by abel
    rw [e, sub_mul, hZ, hLZ]
  have hmat : (1 - P) * (Z * (1 - L)) = 1 - L := by
    rw [← mul_assoc, h1P, sub_mul, one_mul, mul_sub, mul_one, hLL, sub_self, sub_zero]
  have key : (1 - P) *ᵥ ((Z * (1 - L)) *ᵥ f) = f := by
    rw [Matrix.mulVec_mulVec, hmat, Matrix.sub_mulVec, Matrix.one_mulVec, hLf, sub_zero]
  intro s
  have k2 := congrFun key s
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at k2
  simp only [Pi.sub_apply] at k2
  have e : (P *ᵥ ((Z * (1 - L)) *ᵥ f)) s = ∑ j, P s j * ((Z * (1 - L)) *ᵥ f) j := rfl
  linarith

end PutermanMDP.SemiMarkov.FEv

open PutermanMDP.SemiMarkov in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M) (hU : Unichain M d) :
    let P : Matrix S S ℝ := transitionMatrix M d
    let Pstar : Matrix S S ℝ := cesaroMatrix M d
    let H : Matrix S S ℝ := (1 - P + Pstar)⁻¹ * (1 - Pstar)
    let g : S → ℝ := fun s => (gain M d s).toReal
    let h : S → ℝ := H.mulVec (fun s => ruleReward M d s - g s * ruleTime M d s)
    (∃ scalar : ℝ, ∀ s, gain M d s = (scalar : EReal)) ∧
    ∀ s, h s = ruleReward M d s - g s * ruleTime M d s + ∑ j, P s j * h j := by
  intro P Pstar H g h
  exact PutermanMDP.SemiMarkov.FEv.main M d hNE hU
