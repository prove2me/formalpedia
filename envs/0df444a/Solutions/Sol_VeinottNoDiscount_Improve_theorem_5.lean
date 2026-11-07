-- Prove2me | solution 1 for VeinottNoDiscount.Improve.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:09:35.277349+00:00
-- url     : https://prove2.me/submissions/8200e896-414b-47cd-b2a9-35c049d1341b

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix


namespace BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false



section MarkovTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

instance bmk_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma bmk_mul {A B : Matrix n n ℝ} (hA : IsMarkovMatrix A) (hB : IsMarkovMatrix B) :
    IsMarkovMatrix (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma bmk_one : IsMarkovMatrix (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma bmk_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) : IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero => simpa using (bmk_one (n := n))
  | succ k ih => rw [pow_succ]; exact bmk_mul ih hP

lemma bmk_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)

lemma bmk_cesaro {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  unfold cesaroMean
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (bmk_pow hP k).1 i j)
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(bmk_pow hP _).2 i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp

lemma bmk_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma bmk_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma bmk_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, bmk_P_mul_sum, smul_add]
  abel

lemma bmk_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, bmk_sum_mul_P, smul_add]
  abel

lemma bmk_D_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (bmk_pow hP (N + 1)).1 i j
    have h2 := bmk_le_one (bmk_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := bmk_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := bmk_le_one bmk_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma bmk_clus {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (bmk_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma bmk_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma bmk_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem bmk_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(bmk_cesaro hP N).1 i j, bmk_le_one (bmk_cesaro hP N) i j⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := bmk_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := bmk_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := bmk_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := bmk_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [bmk_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [bmk_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

variable {P : Matrix n n ℝ}

lemma bmk_PL (hP : IsMarkovMatrix P) : P * limitMatrix P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).1

lemma bmk_LP (hP : IsMarkovMatrix P) : limitMatrix P * P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).2

lemma bmk_LL (hP : IsMarkovMatrix P) : limitMatrix P * limitMatrix P = limitMatrix P := by
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := (bmk_tendsto hP).mul_const _
  simp_rw [bmk_cesaro_mul_fix (bmk_PL hP)] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_fixvec (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hA : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_L_markov (hP : IsMarkovMatrix P) : IsMarkovMatrix (limitMatrix P) := by
  have hc : IsClosed {M : Matrix n n ℝ | IsMarkovMatrix M} := by
    have : {M : Matrix n n ℝ | IsMarkovMatrix M} =
        (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M : Matrix n n ℝ | ∑ j, M i j = 1} := by
      ext M; simp [IsMarkovMatrix]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_apply i)) continuous_const
  exact hc.mem_of_tendsto (bmk_tendsto hP) (Eventually.of_forall fun N => bmk_cesaro hP N)

lemma bmk_ZL_inj (hP : IsMarkovMatrix P) :
    Function.Injective (1 - P + limitMatrix P).mulVec := by
  set L := limitMatrix P
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  intro v w hvw
  set d := v - w
  have hd : (1 - P + L) *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hvw, sub_self]
  have hLd : L *ᵥ d = 0 := by
    have := congrArg (fun z => L *ᵥ z) hd
    simp only [Matrix.mulVec_mulVec, hLA, Matrix.mulVec_zero] at this
    exact this
  have hPd : P *ᵥ d = d := by
    have := hd
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, hLd, Matrix.one_mulVec, add_zero, sub_eq_zero] at this
    exact this.symm
  have : d = 0 := by rw [← bmk_fixvec hP hPd, hLd]
  exact sub_eq_zero.1 this

lemma bmk_Z_unit (hP : IsMarkovMatrix P) : IsUnit (1 - P + limitMatrix P).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 (bmk_ZL_inj hP))

lemma bmk_PH (hP : IsMarkovMatrix P) :
    P * deviationMatrix P = deviationMatrix P + limitMatrix P - 1 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    have hLA : L * (1 - P + L) = L := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  have h2 : (1 - P + L) * (1 - P + L)⁻¹ = (1 - P + L)⁻¹ - P * (1 - P + L)⁻¹ + L * (1 - P + L)⁻¹ := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [h1, hLZ] at h2
  unfold deviationMatrix
  rw [Matrix.mul_sub, bmk_PL hP]
  change P * (1 - P + L)⁻¹ - L = (1 - P + L)⁻¹ - L + L - 1
  generalize (1 - P + L)⁻¹ = Z at h2 ⊢
  have : P * Z = Z + L - 1 := by rw [h2]; abel
  rw [this]; abel

lemma bmk_LH (hP : IsMarkovMatrix P) : limitMatrix P * deviationMatrix P = 0 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  unfold deviationMatrix
  rw [Matrix.mul_sub, hLZ, bmk_LL hP, sub_self]

/-- maximum principle: if `w = c + β P w` and `c ≤ K` then `w ≤ K/(1-β)` -/
lemma bmk_upper (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, c s ≤ K) [Nonempty n] (s : n) :
    w s ≤ K / (1 - β) := by
  obtain ⟨s0, hs0⟩ := Finite.exists_max w
  have hPw : (P *ᵥ w) s0 ≤ w s0 := by
    show ∑ j, P s0 j * w j ≤ w s0
    calc ∑ j, P s0 j * w j ≤ ∑ j, P s0 j * w s0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hs0 j) (hP.1 s0 j)
      _ = w s0 := by rw [← Finset.sum_mul, hP.2 s0, one_mul]
  have h1 := hw s0
  have h2 : (1 - β) * w s0 ≤ K := by nlinarith [hc s0]
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hs0 s]

lemma bmk_lower (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, K ≤ c s) [Nonempty n] (s : n) :
    K / (1 - β) ≤ w s := by
  have := bmk_upper hP hβ0 hβ1 (w := -w) (c := -c) (K := -K)
    (fun s => by simp only [Pi.neg_apply, Matrix.mulVec_neg]; rw [hw s]; ring)
    (fun s => by simp only [Pi.neg_apply]; linarith [hc s]) s
  simp only [Pi.neg_apply, neg_div] at this
  linarith

lemma bmk_abs (hP : IsMarkovMatrix P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {w c : n → ℝ}
    (hw : ∀ s, w s = c s + β * (P *ᵥ w) s) {K : ℝ} (hc : ∀ s, |c s| ≤ K) [Nonempty n] (s : n) :
    |w s| ≤ K / (1 - β) := by
  rw [abs_le]
  constructor
  · have := bmk_lower hP hβ0 hβ1 hw (K := -K) (fun s => (abs_le.1 (hc s)).1) s
    rw [neg_div] at this; exact this
  · exact bmk_upper hP hβ0 hβ1 hw (fun s => (abs_le.1 (hc s)).2) s

theorem lemma_1b_core [Nonempty n] (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by
  have hker : LinearMap.ker (1 - Q).mulVecLin = LinearMap.range (limitMatrix Q).mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · intro h
      refine ⟨v, bmk_fixvec hQ ?_⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h.symm
    · rintro ⟨w, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, bmk_PL hQ, sub_self,
        Matrix.zero_mulVec]
  unfold Matrix.rank
  rw [← hker, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

end MarkovTheory


section Port


open Model

variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

def bwL (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) : St → ℝ :=
  M.r f + β • (M.Q f).mulVec w

def bwShift (π : Policy St Act) : Policy St Act := fun n => π (n + 1)

lemma bw_Qn_stoch (M : Model St Act) (π : Policy St Act) (n : ℕ) :
    (∀ i j, 0 ≤ M.Qn π n i j) ∧ ∀ i, ∑ j, M.Qn π n i j = 1 := by
  induction n with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Model.Qn, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Model.Qn, Matrix.one_apply]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp only [Model.Qn, Matrix.mul_apply, Model.Q, Matrix.of_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (h1 i k) (M.q_nonneg k (π n k) j)
    · simp only [Model.Qn, Matrix.mul_apply, Model.Q, Matrix.of_apply]
      rw [Finset.sum_comm]
      rw [← h2 i]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, M.q_sum_one k (π n k), mul_one]

/-- bound of a stochastic matrix applied to a vector -/
lemma bw_stoch_mulVec_le {A : Matrix St St ℝ} (h1 : ∀ i j, 0 ≤ A i j) (h2 : ∀ i, ∑ j, A i j = 1)
    {u v : St → ℝ} {c : ℝ} (huv : ∀ s, u s ≤ v s + c) (i : St) :
    (A.mulVec u) i ≤ (A.mulVec v) i + c := by
  show ∑ j, A i j * u j ≤ ∑ j, A i j * v j + c
  calc ∑ j, A i j * u j ≤ ∑ j, A i j * (v j + c) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (h1 i j)
    _ = ∑ j, A i j * v j + c := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h2 i, one_mul]

lemma bw_stoch_abs {A : Matrix St St ℝ} (h1 : ∀ i j, 0 ≤ A i j) (h2 : ∀ i, ∑ j, A i j = 1)
    {u : St → ℝ} {c : ℝ} (hu : ∀ s, |u s| ≤ c) (i : St) : |(A.mulVec u) i| ≤ c := by
  have e : ∀ v : St → ℝ, (A.mulVec v) i = ∑ j, A i j * v j := fun v => rfl
  rw [abs_le, e]
  constructor
  · calc -c = ∑ j, A i j * (-c) := by rw [← Finset.sum_mul, h2 i, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hu j)).1 (h1 i j)
  · calc ∑ j, A i j * u j ≤ ∑ j, A i j * c :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hu j)).2 (h1 i j)
      _ = c := by rw [← Finset.sum_mul, h2 i, one_mul]

noncomputable def bwR (M : Model St Act) : ℝ := ∑ s, ∑ a, |M.i s a|

lemma bw_r_abs (M : Model St Act) (f : St → Act) (s : St) : |M.r f s| ≤ bwR M := by
  unfold bwR Model.r
  calc |M.i s (f s)| ≤ ∑ a, |M.i s a| :=
        Finset.single_le_sum (f := fun a => |M.i s a|) (fun a _ => abs_nonneg _) (Finset.mem_univ _)
    _ ≤ ∑ s, ∑ a, |M.i s a| :=
        Finset.single_le_sum (f := fun s => ∑ a, |M.i s a|)
          (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ _)

lemma bwR_nonneg (M : Model St Act) : 0 ≤ bwR M :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _

lemma bw_term_abs (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (n : ℕ) (s : St) :
    |β ^ n * (M.Qn π n).mulVec (M.r (π n)) s| ≤ bwR M * β ^ n := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (bw_stoch_abs (bw_Qn_stoch M π n).1 (bw_Qn_stoch M π n).2 (bw_r_abs M (π n)) s)
    (pow_nonneg hβ0 n)

lemma bw_term_summable (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : Summable (fun n => β ^ n * (M.Qn π n).mulVec (M.r (π n)) s) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
    (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s)

lemma bw_V_apply (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : M.V β π s = ∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s := by
  unfold Model.V
  rw [tsum_apply]
  · rfl
  · exact Pi.summable.2 fun s => bw_term_summable M π β hβ0 hβ1 s

lemma bw_V_abs (M : Model St Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s : St) : |M.V β π s| ≤ bwR M / (1 - β) := by
  rw [bw_V_apply M π β hβ0 hβ1]
  have hs : Summable (fun n => ‖β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
  calc |∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s|
        = ‖∑' n, β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖β ^ n * (M.Qn π n).mulVec (M.r (π n)) s‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, bwR M * β ^ n := Summable.tsum_le_tsum
          (fun n => by rw [Real.norm_eq_abs]; exact bw_term_abs M π β hβ0 n s) hs
          ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (bwR M))
    _ = bwR M / (1 - β) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]

lemma bw_Qn_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (n : ℕ) :
    M.Qn (Policy.cons f π) (n + 1) = M.Q f * M.Qn π n := by
  induction n with
  | zero => simp [Model.Qn, Policy.cons]
  | succ n ih =>
    rw [Model.Qn, ih, Model.Qn, Matrix.mul_assoc]
    rfl

lemma bw_V_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : M.V β (Policy.cons f π) = bwL M β f (M.V β π) := by
  funext s
  rw [bw_V_apply M _ β hβ0 hβ1, (bw_term_summable M _ β hβ0 hβ1 s).tsum_eq_zero_add]
  simp only [bwL, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · simp [Model.Qn, Policy.cons]
  · have : ∀ n, β ^ (n + 1) * (M.Qn (Policy.cons f π) (n + 1)).mulVec (M.r (Policy.cons f π (n + 1))) s
        = β * ∑ s', M.Q f s s' * (β ^ n * (M.Qn π n).mulVec (M.r (π n)) s') := by
      intro n
      rw [bw_Qn_cons, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Policy.cons, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring_nf
    simp_rw [this]
    rw [tsum_mul_left, Summable.tsum_finsetSum (fun s' _ => (bw_term_summable M π β hβ0 hβ1 s').mul_left _)]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [tsum_mul_left, bw_V_apply M π β hβ0 hβ1]
    rfl

lemma bw_cons_stationary (f : St → Act) : Policy.cons f (Policy.stationary f) = Policy.stationary f := by
  funext n; cases n <;> rfl

lemma bw_V_fix (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    M.V β (Policy.stationary f) = bwL M β f (M.V β (Policy.stationary f)) := by
  conv_lhs => rw [← bw_cons_stationary f]
  exact bw_V_cons M f _ β hβ0 hβ1

lemma bw_Q_stoch (M : Model St Act) (f : St → Act) :
    (∀ i j, 0 ≤ M.Q f i j) ∧ ∀ i, ∑ j, M.Q f i j = 1 :=
  ⟨fun i j => M.q_nonneg i (f i) j, fun i => M.q_sum_one i (f i)⟩

lemma bw_L_apply (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) (s : St) :
    bwL M β f w s = M.i s (f s) + β * ∑ s', M.q s (f s) s' * w s' := rfl

lemma bw_L_le (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (f : St → Act) {u v : St → ℝ} {c : ℝ}
    (huv : ∀ s, u s ≤ v s + c) (s : St) : bwL M β f u s ≤ bwL M β f v s + β * c := by
  have := bw_stoch_mulVec_le (bw_Q_stoch M f).1 (bw_Q_stoch M f).2 huv s
  show M.r f s + β * (M.Q f).mulVec u s ≤ M.r f s + β * (M.Q f).mulVec v s + β * c
  nlinarith

lemma bw_L_mono (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (f : St → Act) {u v : St → ℝ}
    (huv : u ≤ v) : bwL M β f u ≤ bwL M β f v := by
  intro s
  have := bw_L_le M β hβ0 f (u := u) (v := v) (c := 0) (fun s => by simpa using huv s) s
  simpa using this

lemma bw_cons_shift (π : Policy St Act) : Policy.cons (π 0) (bwShift π) = π := by
  funext n; cases n <;> rfl

theorem bw_thm1 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (πstar : Policy St Act)
    (h : ∀ f : St → Act, M.V β (Policy.cons f πstar) ≤ M.V β πstar) :
    M.IsBetaOptimal β πstar := by
  set D := Set.range (fun p : Policy St Act × St => M.V β p.1 p.2 - M.V β πstar p.2) with hD
  have hbdd : BddAbove D := by
    refine ⟨2 * (bwR M / (1 - β)), ?_⟩
    rintro _ ⟨⟨π, s⟩, rfl⟩
    have h1 := (abs_le.1 (bw_V_abs M π β hβ0 hβ1 s)).2
    have h2 := (abs_le.1 (bw_V_abs M πstar β hβ0 hβ1 s)).1
    simp only; linarith
  have hne : D.Nonempty := ⟨_, ⟨(πstar, Classical.arbitrary St), rfl⟩⟩
  have hle : ∀ π s, M.V β π s - M.V β πstar s ≤ sSup D :=
    fun π s => le_csSup hbdd ⟨(π, s), rfl⟩
  have key : ∀ π s, M.V β π s - M.V β πstar s ≤ β * sSup D := by
    intro π s
    have e : M.V β π = bwL M β (π 0) (M.V β (bwShift π)) := by
      conv_lhs => rw [← bw_cons_shift π]
      exact bw_V_cons M _ _ β hβ0 hβ1
    have h1 := bw_L_le M β hβ0 (π 0) (u := M.V β (bwShift π)) (v := M.V β πstar)
      (c := sSup D) (fun s' => by linarith [hle (bwShift π) s']) s
    have h2 := h (π 0) s
    rw [bw_V_cons M _ _ β hβ0 hβ1] at h2
    rw [e]; linarith
  have hd : sSup D ≤ β * sSup D := csSup_le hne (by rintro _ ⟨⟨π, s⟩, rfl⟩; exact key π s)
  have hd0 : sSup D ≤ 0 := by nlinarith
  intro π s
  linarith [hle π s]

lemma bw_le_V_stat (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (w : St → ℝ) (hw : w ≤ bwL M β f w) : w ≤ M.V β (Policy.stationary f) := by
  set Vf := M.V β (Policy.stationary f)
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s => w s - Vf s)
  have h1 := bw_L_le M β hβ0 f (u := w) (v := Vf) (c := w s0 - Vf s0)
    (fun s => by have : w s - Vf s ≤ w s0 - Vf s0 := hs0 s; linarith) s0
  have hfix := congrFun (bw_V_fix M f β hβ0 hβ1) s0
  have h2 := hw s0
  have hd : w s0 - Vf s0 ≤ 0 := by nlinarith
  intro s
  have : w s - Vf s ≤ w s0 - Vf s0 := hs0 s; linarith

theorem bw_thm2 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (π : Policy St Act)
    (h : M.V β π ≤ M.V β (Policy.cons f π) ∧ M.V β (Policy.cons f π) ≠ M.V β π) :
    M.V β π ≤ M.V β (Policy.stationary f) ∧ M.V β (Policy.stationary f) ≠ M.V β π := by
  rw [bw_V_cons M f π β hβ0 hβ1] at h
  have hw := bw_le_V_stat M β hβ0 hβ1 f _ h.1
  refine ⟨hw, fun heq => h.2 ?_⟩
  have h3 : bwL M β f (M.V β π) ≤ M.V β π := by
    have := bw_L_mono M β hβ0 f hw
    rw [← bw_V_fix M f β hβ0 hβ1, heq] at this
    exact this
  exact le_antisymm h3 h.1

theorem bw_thm3 (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) :
    ((∀ s : St, M.betaImprovementSet β f s = ∅) → M.IsBetaOptimal β (Policy.stationary f)) ∧
    (∀ g : St → Act, (∃ s : St, g s ∈ M.betaImprovementSet β f s) →
        (∀ s : St, g s ∉ M.betaImprovementSet β f s → g s = f s) →
        M.V β (Policy.stationary f) ≤ M.V β (Policy.stationary g) ∧
          M.V β (Policy.stationary g) ≠ M.V β (Policy.stationary f)) := by
  constructor
  · intro hG
    apply bw_thm1 M β hβ0 hβ1
    intro g s
    rw [bw_V_cons M g _ β hβ0 hβ1, bw_L_apply]
    by_contra hlt
    push Not at hlt
    have : g s ∈ M.betaImprovementSet β f s := hlt
    rw [hG s] at this
    exact this
  · intro g ⟨s0, hs0⟩ hb
    apply bw_thm2 M β hβ0 hβ1 g (Policy.stationary f)
    rw [bw_V_cons M g _ β hβ0 hβ1]
    have hfix := bw_V_fix M f β hβ0 hβ1
    have hge : ∀ s, M.V β (Policy.stationary f) s ≤ bwL M β g (M.V β (Policy.stationary f)) s := by
      intro s
      by_cases hs : g s ∈ M.betaImprovementSet β f s
      · rw [bw_L_apply]; exact le_of_lt hs
      · have e : bwL M β g (M.V β (Policy.stationary f)) s = bwL M β f (M.V β (Policy.stationary f)) s := by
          simp only [bw_L_apply, hb s hs]
        rw [e, ← hfix]
    refine ⟨hge, fun heq => ?_⟩
    have := congrFun heq s0
    have hs0' : M.V β (Policy.stationary f) s0 < bwL M β g (M.V β (Policy.stationary f)) s0 := by
      rw [bw_L_apply]; exact hs0
    linarith

lemma bw_improve (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (hs : ∃ s, (M.betaImprovementSet β f s).Nonempty) :
    ∃ g : St → Act, M.V β (Policy.stationary f) ≤ M.V β (Policy.stationary g) ∧
          M.V β (Policy.stationary g) ≠ M.V β (Policy.stationary f) := by
  classical
  let g : St → Act := fun s => if h : (M.betaImprovementSet β f s).Nonempty then h.some else f s
  refine ⟨g, (bw_thm3 M β hβ0 hβ1 f).2 g ?_ ?_⟩
  · obtain ⟨s, hs⟩ := hs
    refine ⟨s, ?_⟩
    simp only [g, dif_pos hs]; exact hs.some_mem
  · intro s hgs
    by_cases h : (M.betaImprovementSet β f s).Nonempty
    · exfalso; apply hgs; simp only [g, dif_pos h]; exact h.some_mem
    · simp only [g, dif_neg h]

lemma bw_opt_of_stat (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act)
    (h : ∀ g : St → Act, M.V β (Policy.stationary g) ≤ M.V β (Policy.stationary f)) :
    M.IsBetaOptimal β (Policy.stationary f) := by
  by_cases hs : ∃ s, (M.betaImprovementSet β f s).Nonempty
  · obtain ⟨g, h1, h2⟩ := bw_improve M β hβ0 hβ1 f hs
    exact absurd (le_antisymm (h g) h1) h2
  · push Not at hs
    exact (bw_thm3 M β hβ0 hβ1 f).1 fun s => hs s

lemma bw_exists_opt (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : St → Act, M.IsBetaOptimal β (Policy.stationary f) := by
  obtain ⟨f, hf⟩ := Finite.exists_max (fun f : St → Act => ∑ s, M.V β (Policy.stationary f) s)
  refine ⟨f, ?_⟩
  by_cases hs : ∃ s, (M.betaImprovementSet β f s).Nonempty
  · obtain ⟨g, h1, h2⟩ := bw_improve M β hβ0 hβ1 f hs
    exfalso
    have hne : ∃ s, M.V β (Policy.stationary f) s < M.V β (Policy.stationary g) s := by
      by_contra hc
      push Not at hc
      exact h2 (funext fun s => le_antisymm (hc s) (h1 s))
    obtain ⟨s, hs⟩ := hne
    have := Finset.sum_lt_sum (fun i _ => h1 i) ⟨s, Finset.mem_univ s, hs⟩
    have := hf g
    linarith
  · push Not at hs
    exact (bw_thm3 M β hβ0 hβ1 f).1 fun s => hs s

theorem bw_frequently (M : Model St Act) :
    ∃ fstar : St → Act, ∀ β₀ : ℝ, β₀ < 1 →
      ∃ β : ℝ, β₀ < β ∧ β < 1 ∧ M.IsBetaOptimal β (Policy.stationary fstar) := by
  by_contra H
  push Not at H
  choose b hb1 hb using H
  set m := Finset.univ.sup' Finset.univ_nonempty b with hm
  have hm1 : m < 1 := by
    rw [hm, Finset.sup'_lt_iff]; exact fun f _ => hb1 f
  set B := max m 0
  have hB1 : B < 1 := max_lt hm1 one_pos
  obtain ⟨f, hf⟩ := bw_exists_opt M ((B + 1) / 2) (by have := le_max_right m 0; linarith)
    (by linarith)
  have hbf : b f ≤ m := Finset.le_sup' b (Finset.mem_univ f)
  exact hb f ((B + 1) / 2) (by have := le_max_left m 0; linarith) (by linarith) hf


end Port

section RealAsymptotics

lemma bev {c : ℝ} (hc : c < 1) : ∀ᶠ β in 𝓝[<] (1 : ℝ), c < β ∧ β < 1 := by
  filter_upwards [Ioo_mem_nhdsLT hc] with β hβ using hβ

lemma bsmallK {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) : ∀ᶠ β in 𝓝[<] (1 : ℝ), K * (1 - β) < ε := by
  have hc : 1 - ε / (K + 1) < 1 := by have : 0 < ε / (K + 1) := by positivity
                                      linarith
  filter_upwards [bev hc] with β ⟨h1, h2⟩
  have h3 : 1 - β < ε / (K + 1) := by linarith
  rw [lt_div_iff₀ (by linarith)] at h3
  nlinarith

lemma binv_tendsto : Tendsto (fun β : ℝ => (1 - β)⁻¹) (𝓝[<] (1 : ℝ)) atTop := by
  have h1 : Tendsto (fun β : ℝ => 1 - β) (𝓝[<] (1 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun β : ℝ => 1 - β) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact sub_pos.2 (show β < 1 from hβ)
  exact tendsto_inv_nhdsGT_zero.comp h1

lemma bneg_eventually {D : ℝ → ℝ} {A B K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ β, 0 ≤ β → β < 1 → |D β - (A * (β / (1 - β)) + B)| ≤ K * (1 - β))
    (h : A < 0 ∨ (A = 0 ∧ B < 0)) : ∀ᶠ β in 𝓝[<] (1 : ℝ), D β < 0 := by
  rcases h with hA | ⟨hA, hB⟩
  · have hg : Tendsto (fun β : ℝ => β / (1 - β)) (𝓝[<] (1 : ℝ)) atTop := by
      have : (fun β : ℝ => β / (1 - β)) =ᶠ[𝓝[<] (1 : ℝ)] (fun β => (1 - β)⁻¹ + (-1)) := by
        filter_upwards [self_mem_nhdsWithin] with β hβ
        have : (1 - β) ≠ 0 := by have := sub_pos.2 (show β < 1 from hβ); linarith
        field_simp; ring
      exact (tendsto_atTop_add_const_right _ _ binv_tendsto).congr' this.symm
    have hAg := (hg.const_mul_atTop_of_neg hA)
    filter_upwards [bev (show (0 : ℝ) < 1 by norm_num), tendsto_atBot.1 hAg (-(B + K + 1))]
      with β ⟨h0, h1⟩ h2
    have := (abs_le.1 (hD β h0.le h1)).2
    have : K * (1 - β) ≤ K := by nlinarith
    linarith
  · filter_upwards [bev (show (0 : ℝ) < 1 by norm_num), bsmallK hK (show 0 < -B by linarith)]
      with β ⟨h0, h1⟩ h2
    have := (abs_le.1 (hD β h0.le h1)).2
    rw [hA, zero_mul, zero_add] at this
    linarith

lemma bpos_eventually {D : ℝ → ℝ} {A B K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ β, 0 ≤ β → β < 1 → |D β - (A * (β / (1 - β)) + B)| ≤ K * (1 - β))
    (h : 0 < A ∨ (A = 0 ∧ 0 < B)) : ∀ᶠ β in 𝓝[<] (1 : ℝ), 0 < D β := by
  have := bneg_eventually (D := fun β => - D β) (A := -A) (B := -B) hK
    (fun β h0 h1 => by
      have := hD β h0 h1
      rw [← abs_neg]; convert this using 2; ring)
    (by rcases h with h | ⟨h1, h2⟩
        · left; linarith
        · right; exact ⟨by rw [h1]; ring, by linarith⟩)
  filter_upwards [this] with β hβ
  linarith

lemma bsmall_eventually {D : ℝ → ℝ} {A B K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ β, 0 ≤ β → β < 1 → |D β - (A * (β / (1 - β)) + B)| ≤ K * (1 - β))
    (h : A < 0 ∨ (A = 0 ∧ B ≤ 0)) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ β in 𝓝[<] (1 : ℝ), D β ≤ ε := by
  rcases h with hA | ⟨hA, hB⟩
  · filter_upwards [bneg_eventually hK hD (Or.inl hA)] with β hβ
    linarith
  · filter_upwards [bev (show (0 : ℝ) < 1 by norm_num), bsmallK hK hε] with β ⟨h0, h1⟩ h2
    have := (abs_le.1 (hD β h0.le h1)).2
    rw [hA, zero_mul, zero_add] at this
    linarith

/-- lexicographic extraction -/
lemma blex {X Y K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε > 0, ∃ᶠ β in 𝓝[<] (1 : ℝ), X * (1 - β)⁻¹ + Y ≤ ε + K * (1 - β)) :
    X ≤ 0 ∧ (X = 0 → Y ≤ 0) := by
  constructor
  · by_contra hX
    push Not at hX
    have hg := binv_tendsto.const_mul_atTop hX
    obtain ⟨β, h1, ⟨h0, h2⟩, h3⟩ := ((h 1 one_pos).and_eventually
      ((bev (show (0 : ℝ) < 1 by norm_num)).and (tendsto_atTop.1 hg (|Y| + K + 2)))).exists
    have : K * (1 - β) ≤ K := by nlinarith
    have := neg_abs_le Y
    linarith
  · intro hX
    by_contra hY
    push Not at hY
    obtain ⟨β, h1, h2⟩ := ((h (Y / 2) (by linarith)).and_eventually
      (bsmallK hK (show 0 < Y / 2 by linarith))).exists
    rw [hX, zero_mul, zero_add] at h1
    linarith

lemma bfreq_of {p : ℝ → Prop} (h : ∀ β₀ : ℝ, β₀ < 1 → ∃ β, β₀ < β ∧ β < 1 ∧ p β) :
    ∃ᶠ β in 𝓝[<] (1 : ℝ), p β := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hU
  obtain ⟨β, h1, h2, h3⟩ := h l hl
  exact ⟨β, hsub ⟨h1, h2⟩, h3⟩

lemma bex_of_ev {p : ℝ → Prop} (h : ∀ᶠ β in 𝓝[<] (1 : ℝ), p β) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 → p β := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h
  exact ⟨l, hl, fun β h1 h2 => hsub ⟨h1, h2⟩⟩

lemma bev_of_ex {p : ℝ → Prop} (h : ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 → p β) :
    ∀ᶠ β in 𝓝[<] (1 : ℝ), p β := by
  obtain ⟨l, hl, hsub⟩ := h
  exact mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨l, hl, fun β hβ => hsub β hβ.1 hβ.2⟩

end RealAsymptotics

section ModelTheory2
variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

lemma bQ_mk (M : Model St Act) (f : St → Act) : IsMarkovMatrix (M.Q f) :=
  ⟨fun i j => M.q_nonneg i (f i) j, fun i => M.q_sum_one i (f i)⟩

lemma bQx (M : Model St Act) (f : St → Act) : M.Q f *ᵥ M.x f = M.x f := by
  simp only [Model.x, Model.Qstar, Matrix.mulVec_mulVec, bmk_PL (bQ_mk M f)]

lemma bQy (M : Model St Act) (f : St → Act) : M.Q f *ᵥ M.y f = M.y f + M.x f - M.r f := by
  simp only [Model.y, Model.x, Model.Hf, Model.Qstar, Matrix.mulVec_mulVec, bmk_PH (bQ_mk M f),
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]

lemma bLx (M : Model St Act) (f : St → Act) : M.Qstar f *ᵥ M.x f = M.x f := by
  simp only [Model.x, Model.Qstar, Matrix.mulVec_mulVec, bmk_LL (bQ_mk M f)]

lemma bLy (M : Model St Act) (f : St → Act) : M.Qstar f *ᵥ M.y f = 0 := by
  simp only [Model.y, Model.Hf, Model.Qstar, Matrix.mulVec_mulVec, bmk_LH (bQ_mk M f),
    Matrix.zero_mulVec]

lemma bV_fix' (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s : St) :
    M.V β (Policy.stationary f) s =
      M.r f s + β * (M.Q f *ᵥ M.V β (Policy.stationary f)) s := by
  have := congrFun (bw_V_fix M f β hβ0 hβ1) s
  exact this

lemma bpDot_abs (M : Model St Act) (s : St) (a : Act) {w : St → ℝ} {C : ℝ}
    (hw : ∀ t, |w t| ≤ C) : |M.pDot s a w| ≤ C := by
  unfold Model.pDot
  rw [abs_le]; constructor
  · calc -C = ∑ t, M.q s a t * (-C) := by rw [← Finset.sum_mul, M.q_sum_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (abs_le.1 (hw t)).1 (M.q_nonneg s a t)
  · calc ∑ t, M.q s a t * w t ≤ ∑ t, M.q s a t * C := Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (abs_le.1 (hw t)).2 (M.q_nonneg s a t)
      _ = C := by rw [← Finset.sum_mul, M.q_sum_one, one_mul]

lemma babs_le_sum (w : St → ℝ) (s : St) : |w s| ≤ ∑ t, |w t| :=
  Finset.single_le_sum (f := fun t => |w t|) (fun t _ => abs_nonneg _) (Finset.mem_univ s)

theorem b_laurent (M : Model St Act) (f : St → Act) : ∃ K, 0 ≤ K ∧ ∀ β, 0 ≤ β → β < 1 → ∀ s,
    |M.V β (Policy.stationary f) s - M.x f s / (1 - β) - M.y f s| ≤ K * (1 - β) := by
  have hP := bQ_mk M f
  set u : St → ℝ := M.r f - M.x f - M.y f with hu
  set Hu := M.Hf f *ᵥ u with hHu
  have hLu : limitMatrix (M.Q f) *ᵥ u = 0 := by
    have h1 := bLx M f
    have h2 := bLy M f
    simp only [Model.Qstar] at h1 h2
    simp only [u, Matrix.mulVec_sub, h1, h2]
    simp [Model.x, Model.Qstar]
  have hQHu : M.Q f *ᵥ Hu = Hu - u := by
    simp only [Hu, Model.Hf, Matrix.mulVec_mulVec, bmk_PH hP, Matrix.sub_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, hLu, add_zero]
  refine ⟨∑ t, (|Hu t| + |u t - Hu t|), by positivity, ?_⟩
  intro β hβ0 hβ1 s
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set V := M.V β (Policy.stationary f) with hV
  set e : St → ℝ := V - (1 - β)⁻¹ • M.x f - M.y f - (1 - β) • Hu with he_def
  have he : ∀ t, e t = (1 - β) ^ 2 * (u t - Hu t) + β * (M.Q f *ᵥ e) t := by
    intro t
    have hPe : M.Q f *ᵥ e = M.Q f *ᵥ V - (1 - β)⁻¹ • (M.Q f *ᵥ M.x f) - M.Q f *ᵥ M.y f
        - (1 - β) • (M.Q f *ᵥ Hu) := by
      simp only [e, Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [hPe, bQx, bQy, hQHu]
    have hVt := bV_fix' M f β hβ0 hβ1 t
    rw [← hV] at hVt
    simp only [e, u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    have hinv : (1 - β)⁻¹ * (1 - β) = 1 := inv_mul_cancel₀ h1β.ne'
    linear_combination hVt - M.x f t * hinv
  have hbd := bmk_abs hP hβ0 hβ1 (w := e) (c := fun t => (1 - β) ^ 2 * (u t - Hu t)) he
    (K := (1 - β) ^ 2 * ∑ t, |u t - Hu t|) (fun t => by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (babs_le_sum (fun t => u t - Hu t) t) (by positivity)) s
  have e1 : ((1 - β) ^ 2 * ∑ t, |u t - Hu t|) / (1 - β) = (1 - β) * ∑ t, |u t - Hu t| := by
    field_simp
  rw [e1] at hbd
  have hes : V s - M.x f s / (1 - β) - M.y f s = e s + (1 - β) * Hu s := by
    simp only [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; rw [div_eq_inv_mul]; ring
  rw [hes, Finset.sum_add_distrib, add_mul]
  have h3 : |(1 - β) * Hu s| ≤ (1 - β) * ∑ t, |Hu t| := by
    rw [abs_mul, abs_of_pos h1β]
    exact mul_le_mul_of_nonneg_left (babs_le_sum Hu s) h1β.le
  calc |e s + (1 - β) * Hu s| ≤ |e s| + |(1 - β) * Hu s| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- the one-step advantage of action `a` at `s` against `V_β(f^∞)` -/
noncomputable def bδ (M : Model St Act) (β : ℝ) (f : St → Act) (s : St) (a : Act) : ℝ :=
  M.i s a + β * M.pDot s a (M.V β (Policy.stationary f)) - M.V β (Policy.stationary f) s

noncomputable def bA (M : Model St Act) (f : St → Act) (s : St) (a : Act) : ℝ :=
  M.pDot s a (M.x f) - M.x f s

noncomputable def bB (M : Model St Act) (f : St → Act) (s : St) (a : Act) : ℝ :=
  M.i s a + M.pDot s a (M.y f) - M.x f s - M.y f s

theorem b_delta (M : Model St Act) (f : St → Act) (s : St) (a : Act) :
    ∃ K, 0 ≤ K ∧ ∀ β, 0 ≤ β → β < 1 →
      |bδ M β f s a - (bA M f s a * (β / (1 - β)) + bB M f s a)| ≤ K * (1 - β) := by
  obtain ⟨K, hK, hL⟩ := b_laurent M f
  refine ⟨∑ t, |M.y f t| + 2 * K, by positivity, ?_⟩
  intro β hβ0 hβ1
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set V := M.V β (Policy.stationary f) with hV
  set E : St → ℝ := fun t => V t - M.x f t / (1 - β) - M.y f t with hE
  have hp : M.pDot s a V = M.pDot s a (M.x f) / (1 - β) + M.pDot s a (M.y f) + M.pDot s a E := by
    simp only [Model.pDot, E]
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    field_simp
    ring
  have hEs : |E s| ≤ K * (1 - β) := hL β hβ0 hβ1 s
  have hpE : |M.pDot s a E| ≤ K * (1 - β) := bpDot_abs M s a (fun t => hL β hβ0 hβ1 t)
  have hpy : |M.pDot s a (M.y f)| ≤ ∑ t, |M.y f t| := bpDot_abs M s a (fun t => babs_le_sum _ t)
  have key : bδ M β f s a - (bA M f s a * (β / (1 - β)) + bB M f s a) =
      -(1 - β) * M.pDot s a (M.y f) + β * M.pDot s a E - E s := by
    simp only [bδ, bA, bB]
    rw [← hV, hp]
    have : V s = M.x f s / (1 - β) + M.y f s + E s := by simp only [E]; ring
    rw [this]
    field_simp
    ring
  rw [key]
  have h4 : |-(1 - β) * M.pDot s a (M.y f)| ≤ (1 - β) * ∑ t, |M.y f t| := by
    rw [abs_mul, abs_neg, abs_of_pos h1β]
    exact mul_le_mul_of_nonneg_left hpy h1β.le
  have h5 : |β * M.pDot s a E| ≤ K * (1 - β) := by
    rw [abs_mul, abs_of_nonneg hβ0]
    calc β * |M.pDot s a E| ≤ 1 * |M.pDot s a E| :=
          mul_le_mul_of_nonneg_right hβ1.le (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hpE
  calc |-(1 - β) * M.pDot s a (M.y f) + β * M.pDot s a E - E s|
      ≤ |-(1 - β) * M.pDot s a (M.y f) + β * M.pDot s a E| + |E s| := abs_sub _ _
    _ ≤ |-(1 - β) * M.pDot s a (M.y f)| + |β * M.pDot s a E| + |E s| := by
        linarith [abs_add_le (-(1 - β) * M.pDot s a (M.y f)) (β * M.pDot s a E)]
    _ ≤ _ := by nlinarith

lemma bδ_self (M : Model St Act) (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s : St) :
    bδ M β f s (f s) = 0 := by
  have := bV_fix' M f β hβ0 hβ1 s
  simp only [bδ]
  have e : M.pDot s (f s) (M.V β (Policy.stationary f)) =
      (M.Q f *ᵥ M.V β (Policy.stationary f)) s := rfl
  rw [e]
  have e2 : M.r f s = M.i s (f s) := rfl
  rw [e2] at this
  linarith

lemma bdiff (M : Model St Act) (f g : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s : St) :
    (M.V β (Policy.stationary g) - M.V β (Policy.stationary f)) s =
      bδ M β f s (g s) + β * (M.Q g *ᵥ (M.V β (Policy.stationary g) - M.V β (Policy.stationary f))) s := by
  have h1 := bV_fix' M g β hβ0 hβ1 s
  simp only [bδ, Pi.sub_apply, Matrix.mulVec_sub]
  have e : M.pDot s (g s) (M.V β (Policy.stationary f)) =
      (M.Q g *ᵥ M.V β (Policy.stationary f)) s := rfl
  have e2 : M.r g s = M.i s (g s) := rfl
  rw [e]
  rw [e2] at h1
  linarith

lemma bE_self (M : Model St Act) (f : St → Act) (s : St) : f s ∈ M.gainBiasEqualSet f s := by
  have h1 := congrFun (bQx M f) s
  have h2 := congrFun (bQy M f) s
  refine ⟨h1, ?_⟩
  have e : M.pDot s (f s) (M.y f) = (M.Q f *ᵥ M.y f) s := rfl
  have e2 : M.r f s = M.i s (f s) := rfl
  rw [e, h2]
  simp only [Pi.add_apply, Pi.sub_apply, e2]
  ring

/-- difference expansion of two stationary policies -/
theorem b_laurent2 (M : Model St Act) (f g : St → Act) : ∃ K, 0 ≤ K ∧ ∀ β, 0 ≤ β → β < 1 → ∀ s,
    |(M.V β (Policy.stationary g) s - M.V β (Policy.stationary f) s)
      - ((M.x g s - M.x f s) * (1 - β)⁻¹ + (M.y g s - M.y f s))| ≤ K * (1 - β) := by
  obtain ⟨K1, hK1, h1⟩ := b_laurent M f
  obtain ⟨K2, hK2, h2⟩ := b_laurent M g
  refine ⟨K1 + K2, by positivity, fun β hβ0 hβ1 s => ?_⟩
  have a1 := h1 β hβ0 hβ1 s
  have a2 := h2 β hβ0 hβ1 s
  have : (M.V β (Policy.stationary g) s - M.V β (Policy.stationary f) s)
      - ((M.x g s - M.x f s) * (1 - β)⁻¹ + (M.y g s - M.y f s)) =
      (M.V β (Policy.stationary g) s - M.x g s / (1 - β) - M.y g s) -
      (M.V β (Policy.stationary f) s - M.x f s / (1 - β) - M.y f s) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [this]
  calc _ ≤ |M.V β (Policy.stationary g) s - M.x g s / (1 - β) - M.y g s| +
        |M.V β (Policy.stationary f) s - M.x f s / (1 - β) - M.y f s| := abs_sub _ _
    _ ≤ _ := by linarith

lemma bnear_of (M : Model St Act) (g : St → Act)
    (h : ∀ h' : St → Act, ∀ ε > 0, ∀ᶠ β in 𝓝[<] (1 : ℝ),
      ∀ s, M.V β (Policy.stationary h') s ≤ M.V β (Policy.stationary g) s + ε) :
    M.IsNearlyOptimal (Policy.stationary g) := by
  intro ε hε
  have H := (bev (show (0 : ℝ) < 1 by norm_num)).and (Filter.eventually_all.2 fun h' => h h' ε hε)
  obtain ⟨β₀, hβ₀, hsub⟩ := bex_of_ev H
  refine ⟨β₀, hβ₀, fun β h1 h2 π' s => ?_⟩
  obtain ⟨⟨hb0, hb1⟩, hall⟩ := hsub β h1 h2
  obtain ⟨f, hf⟩ := bw_exists_opt M β hb0.le hb1
  exact (hf π' s).trans (hall f s)

lemma bnear_to (M : Model St Act) (g : St → Act) (hg : M.IsNearlyOptimal (Policy.stationary g))
    (π' : Policy St Act) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ β in 𝓝[<] (1 : ℝ),
      ∀ s, M.V β π' s ≤ M.V β (Policy.stationary g) s + ε := by
  obtain ⟨β₀, hβ₀, h⟩ := hg ε hε
  exact bev_of_ex ⟨β₀, hβ₀, fun β h1 h2 => h β h1 h2 π'⟩

end ModelTheory2

section Theorems
variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

lemma b_notG (M : Model St Act) (f : St → Act) (s : St) (a : Act)
    (h : a ∉ M.gainBiasImprovementSet f s) :
    bA M f s a < 0 ∨ (bA M f s a = 0 ∧ bB M f s a ≤ 0) := by
  have h1 : ¬ (M.pDot s a (M.x f) > M.x f s) := fun hh => h (Or.inl hh)
  have h2 : M.pDot s a (M.x f) = M.x f s →
      ¬ (M.i s a + M.pDot s a (M.y f) > M.x f s + M.y f s) := fun he hb => h (Or.inr ⟨he, hb⟩)
  simp only [bA, bB]
  rcases lt_or_eq_of_le (not_lt.1 h1) with hl | he
  · left; linarith
  · right
    refine ⟨by linarith, ?_⟩
    have := not_lt.1 (h2 he)
    linarith

lemma b_notGE (M : Model St Act) (f : St → Act) (s : St) (a : Act)
    (h : a ∉ M.gainBiasImprovementSet f s) (h' : a ∉ M.gainBiasEqualSet f s) :
    bA M f s a < 0 ∨ (bA M f s a = 0 ∧ bB M f s a < 0) := by
  rcases b_notG M f s a h with hl | ⟨he, hb⟩
  · left; exact hl
  · right
    refine ⟨he, lt_of_le_of_ne hb ?_⟩
    intro hc
    apply h'
    simp only [bA, bB] at he hc
    exact ⟨by linarith, by linarith⟩

theorem lemma_2_core (M : Model St Act) (f g : St → Act)
    (hE : ∀ s, g s ∈ M.gainBiasEqualSet f s) :
    M.x g = M.x f ∧ (M.Qstar g * M.Qstar f = M.Qstar g → M.y g = M.y f) := by
  have hQx : M.Q g *ᵥ M.x f = M.x f := funext fun s => (hE s).1
  have hQy : M.Q g *ᵥ M.y f = M.x f + M.y f - M.r g := funext fun s => by
    have := (hE s).2
    show M.pDot s (g s) (M.y f) = M.x f s + M.y f s - M.i s (g s)
    linarith
  have hPg := bQ_mk M g
  have hLP : M.Qstar g * M.Q g = M.Qstar g := bmk_LP hPg
  have hxg : M.x g = M.x f := by
    have hr : M.r g = M.x f + M.y f - M.Q g *ᵥ M.y f := by rw [hQy]; abel
    have h1 : M.Qstar g *ᵥ M.x f = M.x f := bmk_fixvec hPg hQx
    calc M.x g = M.Qstar g *ᵥ M.r g := rfl
      _ = M.Qstar g *ᵥ M.x f + M.Qstar g *ᵥ M.y f - (M.Qstar g * M.Q g) *ᵥ M.y f := by
          rw [hr, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      _ = M.x f := by rw [hLP, h1]; abel
  refine ⟨hxg, fun hQQ => ?_⟩
  set d := M.y g - M.y f with hd_def
  have hd : M.Q g *ᵥ d = d := by
    simp only [d, Matrix.mulVec_sub, bQy M g, hQy, hxg]; abel
  have hLd : M.Qstar g *ᵥ d = 0 := by
    have e1 : M.Qstar g *ᵥ M.y f = 0 := by
      rw [← hQQ, ← Matrix.mulVec_mulVec, bLy M f, Matrix.mulVec_zero]
    simp only [d, Matrix.mulVec_sub, bLy M g, e1, sub_zero]
  have : d = 0 := by
    have h2 : limitMatrix (M.Q g) *ᵥ d = d := bmk_fixvec hPg hd
    rw [← h2]; exact hLd
  exact sub_eq_zero.1 this

theorem theorem_4b_core (M : Model St Act) (f g : St → Act)
    (hG : ∃ s, g s ∈ M.gainBiasImprovementSet f s)
    (hfix : ∀ s, g s ∉ M.gainBiasImprovementSet f s → g s = f s) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
      VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by
  obtain ⟨s0, hs0⟩ := hG
  have hev : ∀ s, g s ∈ M.gainBiasImprovementSet f s →
      ∀ᶠ β in 𝓝[<] (1 : ℝ), 0 < bδ M β f s (g s) := by
    intro s hs
    obtain ⟨K, hK, hD⟩ := b_delta M f s (g s)
    apply bpos_eventually hK hD
    rcases hs with h | ⟨h1, h2⟩
    · left; simp only [bA]; linarith
    · right; simp only [bA, bB]; constructor <;> linarith
  have hall : ∀ᶠ β in 𝓝[<] (1 : ℝ), ∀ s, g s ∈ M.gainBiasImprovementSet f s →
      0 < bδ M β f s (g s) := by
    refine Filter.eventually_all.2 fun s => ?_
    by_cases hs : g s ∈ M.gainBiasImprovementSet f s
    · filter_upwards [hev s hs] with β h _ using h
    · exact Eventually.of_forall fun β h => absurd h hs
  apply bex_of_ev
  filter_upwards [hall, bev (show (0 : ℝ) < 1 by norm_num)] with β hβ ⟨h0, h1⟩
  have hw := bdiff M f g β h0.le h1
  set w := M.V β (Policy.stationary g) - M.V β (Policy.stationary f) with hw_def
  have hδ : ∀ s, 0 ≤ bδ M β f s (g s) := by
    intro s
    by_cases hs : g s ∈ M.gainBiasImprovementSet f s
    · exact (hβ s hs).le
    · rw [hfix s hs, bδ_self M f β h0.le h1]
  have hw0 : ∀ s, 0 ≤ w s := fun s => by
    have := bmk_lower (bQ_mk M g) h0.le h1 hw (K := 0) hδ s
    rwa [zero_div] at this
  refine ⟨fun s => ?_, fun heq => ?_⟩
  · have := hw0 s
    simp only [w, Pi.sub_apply] at this
    linarith
  · have hpos : 0 < w s0 := by
      rw [hw s0]
      have : 0 ≤ (M.Q g *ᵥ w) s0 :=
        Finset.sum_nonneg fun j _ => mul_nonneg ((bQ_mk M g).1 s0 j) (hw0 j)
      have := hβ s0 hs0
      nlinarith
    have : w s0 = 0 := by simp [w, heq]
    linarith

theorem theorem_4c_core (M : Model St Act) (f : St → Act) :
    (∀ s, f s ∈ M.gainBiasEqualSet f s) ∧
      ((∀ s, M.gainBiasImprovementSet f s = ∅) → (∀ s, M.gainBiasEqualSet f s = {f s}) →
        M.IsOptimal (Policy.stationary f)) := by
  refine ⟨bE_self M f, fun hG hE => ?_⟩
  have hneg : ∀ s a, a ≠ f s → ∀ᶠ β in 𝓝[<] (1 : ℝ), bδ M β f s a < 0 := by
    intro s a ha
    obtain ⟨K, hK, hD⟩ := b_delta M f s a
    apply bneg_eventually hK hD
    apply b_notGE
    · rw [hG s]; exact Set.notMem_empty a
    · rw [hE s]; intro h; exact ha (Set.mem_singleton_iff.1 h)
  have hall : ∀ᶠ β in 𝓝[<] (1 : ℝ), ∀ s a, a ≠ f s → bδ M β f s a < 0 := by
    refine Filter.eventually_all.2 fun s => Filter.eventually_all.2 fun a => ?_
    by_cases ha : a = f s
    · exact Eventually.of_forall fun _ h => absurd ha h
    · filter_upwards [hneg s a ha] with β h _ using h
  obtain ⟨β₀, hβ₀, H⟩ := bex_of_ev (hall.and (bev (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨β₀, hβ₀, fun β h1 h2 => ?_⟩
  obtain ⟨hδ, h0, h1'⟩ := H β h1 h2
  apply (bw_thm3 M β h0.le h1' f).1
  intro s
  refine Set.eq_empty_iff_forall_notMem.2 fun a ha => ?_
  have ha' : M.i s a + β * M.pDot s a (M.V β (Policy.stationary f)) >
      M.V β (Policy.stationary f) s := ha
  have hpos : 0 < bδ M β f s a := by simp only [bδ]; linarith
  by_cases haf : a = f s
  · rw [haf, bδ_self M f β h0.le h1'] at hpos; exact lt_irrefl _ hpos
  · linarith [hδ s a haf]

theorem theorem_4d_core (M : Model St Act) (f : St → Act)
    (hG : ∀ s, M.gainBiasImprovementSet f s = ∅)
    (hE : ∀ g : St → Act, (∀ s, g s ∈ M.gainBiasEqualSet f s) →
      M.Qstar g * M.Qstar f = M.Qstar g) :
    M.IsNearlyOptimal (Policy.stationary f) := by
  classical
  apply bnear_of
  intro h ε hε
  let g : St → Act := fun s => if h s ∈ M.gainBiasEqualSet f s then h s else f s
  have hgE : ∀ s, g s ∈ M.gainBiasEqualSet f s := by
    intro s
    by_cases hs : h s ∈ M.gainBiasEqualSet f s
    · simp only [g, if_pos hs]; exact hs
    · simp only [g, if_neg hs]; exact bE_self M f s
  obtain ⟨hx, hy⟩ := lemma_2_core M f g hgE
  have hy' := hy (hE g hgE)
  obtain ⟨K, hK, hL2⟩ := b_laurent2 M f g
  have hneg : ∀ s, ∀ᶠ β in 𝓝[<] (1 : ℝ), bδ M β g s (h s) ≤ 0 := by
    intro s
    by_cases hs : h s ∈ M.gainBiasEqualSet f s
    · have hgs : g s = h s := by simp only [g, if_pos hs]
      filter_upwards [bev (show (0 : ℝ) < 1 by norm_num)] with β ⟨h0, h1⟩
      rw [← hgs, bδ_self M g β h0.le h1]
    · obtain ⟨K', hK', hD⟩ := b_delta M g s (h s)
      have hAB : bA M g s (h s) < 0 ∨ (bA M g s (h s) = 0 ∧ bB M g s (h s) < 0) := by
        have := b_notGE M f s (h s) (by rw [hG s]; exact Set.notMem_empty _) hs
        simpa only [bA, bB, hx, hy'] using this
      filter_upwards [bneg_eventually hK' hD hAB] with β hβ using hβ.le
  filter_upwards [Filter.eventually_all.2 hneg, bev (show (0 : ℝ) < 1 by norm_num),
    bsmallK hK hε] with β hδ ⟨h0, h1⟩ hsm
  intro s
  have hw := bdiff M g h β h0.le h1
  have hwle := bmk_upper (bQ_mk M h) h0.le h1 hw (K := 0) hδ s
  rw [zero_div] at hwle
  simp only [Pi.sub_apply] at hwle
  have := hL2 β h0.le h1 s
  rw [hx, hy', sub_self, sub_self, zero_mul, add_zero, sub_zero] at this
  have := (abs_le.1 this).2
  linarith

lemma blex2 {X Y K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε > 0, ∃ᶠ β in 𝓝[<] (1 : ℝ), X * (1 - β)⁻¹ + Y ≤ ε * (1 - β)⁻¹ + K * (1 - β)) :
    X ≤ 0 := by
  by_contra hX
  push Not at hX
  have hg := binv_tendsto.const_mul_atTop (show 0 < X / 2 by linarith)
  obtain ⟨β, h1, ⟨h0, h2⟩, h3⟩ := ((h (X / 2) (by linarith)).and_eventually
    ((bev (show (0 : ℝ) < 1 by norm_num)).and (tendsto_atTop.1 hg (|Y| + K + 2)))).exists
  have : K * (1 - β) ≤ K := by nlinarith
  have := neg_abs_le Y
  have e : X * (1 - β)⁻¹ = X / 2 * (1 - β)⁻¹ + X / 2 * (1 - β)⁻¹ := by ring
  linarith

theorem theorem_4e_core (M : Model St Act) (f₀ : St → Act)
    (hG : ∀ s, M.gainBiasImprovementSet f₀ s = ∅) :
    (∀ g : St → Act, M.x g ≤ M.x f₀) ∧
      ∃ fstar : St → Act, M.x fstar = M.x f₀ ∧
        (∀ g : St → Act, M.x g = M.x f₀ → M.y g ≤ M.y fstar) ∧
        ∀ g : St → Act,
          (M.IsNearlyOptimal (Policy.stationary g) ↔ M.x g = M.x fstar ∧ M.y g = M.y fstar) := by
  have part1 : ∀ g, M.x g ≤ M.x f₀ := by
    intro g s
    obtain ⟨K, hK, hL2⟩ := b_laurent2 M f₀ g
    have hsmall : ∀ ε > 0, ∀ᶠ β in 𝓝[<] (1 : ℝ), ∀ t, bδ M β f₀ t (g t) ≤ ε :=
      fun ε hε => Filter.eventually_all.2 fun t => by
        obtain ⟨K', hK', hD⟩ := b_delta M f₀ t (g t)
        exact bsmall_eventually hK' hD
          (b_notG M f₀ t (g t) (by rw [hG t]; exact Set.notMem_empty _)) hε
    have := blex2 (X := M.x g s - M.x f₀ s) (Y := M.y g s - M.y f₀ s) hK (fun ε hε => by
      refine Eventually.frequently ?_
      filter_upwards [hsmall ε hε, bev (show (0 : ℝ) < 1 by norm_num)] with β hδ ⟨h0, h1⟩
      have hw := bdiff M f₀ g β h0.le h1
      have hwle := bmk_upper (bQ_mk M g) h0.le h1 hw hδ s
      simp only [Pi.sub_apply] at hwle
      have := (abs_le.1 (hL2 β h0.le h1 s)).1
      rw [div_eq_mul_inv] at hwle
      linarith)
    linarith
  obtain ⟨fs, hfs⟩ := bw_frequently M
  have LEX : ∀ h s, M.x h s ≤ M.x fs s ∧ (M.x h s = M.x fs s → M.y h s ≤ M.y fs s) := by
    intro h s
    obtain ⟨K, hK, hL2⟩ := b_laurent2 M fs h
    have hb := blex (X := M.x h s - M.x fs s) (Y := M.y h s - M.y fs s) hK (fun ε hε => by
      have hfr := bfreq_of (p := fun β => 0 ≤ β ∧ M.IsBetaOptimal β (Policy.stationary fs))
        (fun β₀ hβ₀ => by
          obtain ⟨β, h1, h2, h3⟩ := hfs (max β₀ 0) (max_lt hβ₀ one_pos)
          exact ⟨β, lt_of_le_of_lt (le_max_left _ _) h1, h2,
            le_trans (le_max_right _ _) h1.le, h3⟩)
      refine (hfr.and_eventually (bev (show (0 : ℝ) < 1 by norm_num))).mono ?_
      rintro β ⟨⟨h0, hopt⟩, -, h1⟩
      have := hopt (Policy.stationary h) s
      have := (abs_le.1 (hL2 β h0 h1 s)).1
      have : 0 ≤ K * (1 - β) := mul_nonneg hK (by linarith)
      linarith)
    refine ⟨by linarith [hb.1], fun he => ?_⟩
    have := hb.2 (by rw [he]; ring)
    linarith
  have hxfs : M.x fs = M.x f₀ := funext fun s => le_antisymm (part1 fs s) (LEX f₀ s).1
  have nearopt : ∀ g, M.x g = M.x fs → M.y g = M.y fs →
      M.IsNearlyOptimal (Policy.stationary g) := by
    intro g hxg hyg
    apply bnear_of
    intro h' ε hε
    refine Filter.eventually_all.2 fun s => ?_
    obtain ⟨K, hK, hL2⟩ := b_laurent2 M g h'
    have hD : ∀ β, 0 ≤ β → β < 1 →
        |(M.V β (Policy.stationary h') s - M.V β (Policy.stationary g) s) -
          ((M.x h' s - M.x g s) * (β / (1 - β)) + ((M.x h' s - M.x g s) + (M.y h' s - M.y g s)))|
          ≤ K * (1 - β) := by
      intro β h0 h1
      have e : (M.x h' s - M.x g s) * (β / (1 - β)) + ((M.x h' s - M.x g s) + (M.y h' s - M.y g s))
          = (M.x h' s - M.x g s) * (1 - β)⁻¹ + (M.y h' s - M.y g s) := by
        have : (1 - β) ≠ 0 := by linarith
        field_simp
        ring
      rw [e]; exact hL2 β h0 h1 s
    have hAB : (M.x h' s - M.x g s) < 0 ∨ ((M.x h' s - M.x g s) = 0 ∧
        (M.x h' s - M.x g s) + (M.y h' s - M.y g s) ≤ 0) := by
      have l := LEX h' s
      rw [← hxg, ← hyg] at l
      rcases lt_or_eq_of_le l.1 with hl | he
      · left; linarith
      · right; have := l.2 he; constructor <;> linarith
    filter_upwards [bsmall_eventually hK hD hAB hε] with β hβ
    linarith
  refine ⟨part1, fs, hxfs, fun g hg => fun s => (LEX g s).2 ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · rw [congrFun hg s, congrFun hxfs s]
  · have hxy : ∀ s, M.x g s = M.x fs s ∧ M.y g s = M.y fs s := by
      intro s
      obtain ⟨K, hK, hL2⟩ := b_laurent2 M g fs
      have hb := blex (X := M.x fs s - M.x g s) (Y := M.y fs s - M.y g s) hK (fun ε hε => by
        refine Eventually.frequently ?_
        filter_upwards [bnear_to M g hg (Policy.stationary fs) hε,
          bev (show (0 : ℝ) < 1 by norm_num)] with β hv ⟨h0, h1⟩
        have := hv s
        have := (abs_le.1 (hL2 β h0.le h1 s)).1
        linarith)
      have l := LEX g s
      have hx : M.x g s = M.x fs s := le_antisymm l.1 (by linarith [hb.1])
      refine ⟨hx, le_antisymm (l.2 hx) ?_⟩
      have := hb.2 (by rw [hx]; ring)
      linarith
    exact ⟨funext fun s => (hxy s).1, funext fun s => (hxy s).2⟩
  · rintro ⟨h1, h2⟩
    exact nearopt g h1 h2

end Theorems

end BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

open BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section VMarkov
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma v_mono {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) {u v : n → ℝ} (h : u ≤ v) :
    A *ᵥ u ≤ A *ᵥ v := fun i =>
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hA i j)

/-- a subharmonic vector `e ≤ P e` satisfies `e ≤ Q* e` -/
lemma v_sub_harm {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {e : n → ℝ} (he : e ≤ P *ᵥ e) :
    e ≤ limitMatrix P *ᵥ e := by
  have hk : ∀ k : ℕ, e ≤ (P ^ k) *ᵥ e := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      exact ih.trans (v_mono (bmk_pow hP k).1 he)
  have hA : ∀ N, e ≤ cesaroMean P N *ᵥ e := by
    intro N i
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [le_inv_mul_iff₀ hpos]
    calc ((N : ℝ) + 1) * e i = ∑ k ∈ Finset.range (N + 1), e i := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hk k i
  have t : Tendsto (fun N => cesaroMean P N *ᵥ e) atTop (𝓝 (limitMatrix P *ᵥ e)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  exact ge_of_tendsto' t hA

lemma v_left_fix {P L : Matrix n n ℝ} (hP : IsMarkovMatrix P) (h : L * P = L) :
    L * limitMatrix P = L := by
  have t : Tendsto (fun N => L * cesaroMean P N) atTop (𝓝 (L * limitMatrix P)) :=
    (bmk_tendsto hP).const_mul L
  simp_rw [bmk_fix_mul_cesaro h] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma v_uniq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {v v' : n → ℝ}
    (h1 : (1 - P) *ᵥ v = (1 - P) *ᵥ v') (h2 : limitMatrix P *ᵥ v = limitMatrix P *ᵥ v') :
    v = v' := by
  have hd : P *ᵥ (v - v') = v - v' := by
    have : (1 - P) *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, h1, sub_self]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this.symm
  have h3 := bmk_fixvec hP hd
  rw [Matrix.mulVec_sub, h2, sub_self] at h3
  exact (sub_eq_zero.1 h3.symm)

end VMarkov

variable {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]

lemma v_pDot (M : Model St Act) (g : St → Act) (s : St) (v : St → ℝ) :
    M.pDot s (g s) v = (M.Q g *ᵥ v) s := rfl

lemma v_fE (M : Model St Act) (f : St → Act) (t : St) :
    M.pDot t (f t) (M.x f) = M.x f t ∧ M.r f t + M.pDot t (f t) (M.y f) = M.x f t + M.y f t :=
  bE_self M f t

/-- the equations (12) for `z(f)` -/
lemma v_z_eq (M : Model St Act) (f : St → Act) :
    (1 - M.Q f) *ᵥ z M f = -(M.y f) ∧ M.Qstar f *ᵥ z M f = 0 := by
  have hP := bQ_mk M f
  constructor
  · have hPH := bmk_PH hP
    have : (1 - M.Q f) * M.Hf f = 1 - M.Qstar f := by
      simp only [Model.Hf, Model.Qstar]
      rw [Matrix.sub_mul, Matrix.one_mul, hPH]; abel
    rw [z, Matrix.mulVec_mulVec, this, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg,
      bLy, neg_zero, sub_zero]
  · rw [z, Matrix.mulVec_mulVec]
    simp only [Model.Hf, Model.Qstar]
    rw [bmk_LH hP, Matrix.zero_mulVec]

lemma v_Qz (M : Model St Act) (f : St → Act) (t : St) :
    -(M.y f t) + M.pDot t (f t) (z M f) = z M f t := by
  have h := congrFun (v_z_eq M f).1 t
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
  simp only [Pi.sub_apply, Pi.neg_apply] at h
  rw [v_pDot]; linarith

theorem display_12_core (M : Model St Act) (f : St → Act) :
    ∀ v : St → ℝ, ((1 - M.Q f) *ᵥ v = -(M.y f) ∧ M.Qstar f *ᵥ v = 0) ↔ v = z M f := by
  intro v
  obtain ⟨h1, h2⟩ := v_z_eq M f
  constructor
  · rintro ⟨e1, e2⟩
    exact v_uniq (bQ_mk M f) (by rw [e1, h1]) (by
      change M.Qstar f *ᵥ v = M.Qstar f *ᵥ z M f; rw [e2, h2])
  · rintro rfl; exact ⟨h1, h2⟩

/-- Lemma 4 -/
theorem lemma_4_core (M : Model St Act) (f g : St → Act) (hg : g ∈ ESet M f) :
    (∀ v : St → ℝ,
        ((1 - M.Q g) *ᵥ v = 0 ∧ M.Qstar g *ᵥ v = M.Qstar g *ᵥ (-(M.y f))) ↔ v = w M f g) ∧
      M.y g = M.y f + w M f g := by
  have hP := bQ_mk M g
  have hPL : M.Q g * M.Qstar g = M.Qstar g := bmk_PL hP
  have hLL : M.Qstar g * M.Qstar g = M.Qstar g := bmk_LL hP
  have hLP : M.Qstar g * M.Q g = M.Qstar g := bmk_LP hP
  have hw1 : (1 - M.Q g) *ᵥ w M f g = 0 := by
    rw [w, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, hPL, sub_self,
      Matrix.zero_mulVec]
  have hw2 : M.Qstar g *ᵥ w M f g = M.Qstar g *ᵥ (-(M.y f)) := by
    rw [w, Matrix.mulVec_mulVec, hLL]
  refine ⟨fun v => ⟨fun ⟨e1, e2⟩ => v_uniq hP (by rw [e1, hw1]) (by
      change M.Qstar g *ᵥ v = M.Qstar g *ᵥ w M f g; rw [e2, hw2]), fun h => h ▸ ⟨hw1, hw2⟩⟩, ?_⟩
  obtain ⟨hx, -⟩ := lemma_2_core M f g hg
  have hQy : M.Q g *ᵥ M.y f = M.x f + M.y f - M.r g := funext fun s => by
    have := (hg s).2
    show M.pDot s (g s) (M.y f) = M.x f s + M.y f s - M.i s (g s)
    linarith
  apply v_uniq hP
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, bQy,
      Matrix.mulVec_add, hQy, hx]
    have : M.Q g *ᵥ w M f g = w M f g := by
      rw [w, Matrix.mulVec_mulVec, hPL]
    rw [this]; abel
  · change M.Qstar g *ᵥ M.y g = M.Qstar g *ᵥ (M.y f + w M f g)
    rw [bLy, Matrix.mulVec_add, hw2, Matrix.mulVec_neg, add_neg_cancel]

lemma w_self (M : Model St Act) (f : St → Act) : w M f f = 0 := by
  rw [w, Matrix.mulVec_neg, bLy, neg_zero]

/-- Veinott's `G(f)` from Blackwell's per-state sets -/
lemma gset_of_local (M : Model St Act) (f g : St → Act)
    (h : ∀ t, g t = f t ∨ g t ∈ M.gainBiasImprovementSet f t)
    (hex : ∃ t, g t ∈ M.gainBiasImprovementSet f t) : g ∈ GSet M f := by
  have hr : ∀ t, M.r g t = M.i t (g t) := fun t => rfl
  refine ⟨fun t => ?_, fun t ht => ?_, ?_, fun t h1 h2 => ?_⟩
  · rcases h t with e | hG
    · rw [e]; exact (v_fE M f t).1.ge
    · rcases hG with hG | ⟨hG, -⟩
      · exact hG.le
      · exact hG.ge
  · rcases h t with e | hG
    · rw [hr, e]; have := (v_fE M f t).2; exact this.ge
    · rcases hG with hG | ⟨-, hG⟩
      · rw [ht] at hG; exact absurd hG (lt_irrefl _)
      · rw [hr]; exact hG.le
  · obtain ⟨t, hG⟩ := hex
    refine ⟨t, ?_⟩
    rcases hG with hG | ⟨-, hG⟩
    · exact Or.inl hG
    · exact Or.inr (by rw [hr]; exact hG)
  · rcases h t with e | hG
    · exact e
    · rcases hG with hG | ⟨-, hG⟩
      · rw [h1] at hG; exact absurd hG (lt_irrefl _)
      · rw [hr] at h2; rw [h2] at hG; exact absurd hG (lt_irrefl _)

/-- membership in Veinott's `G(f)` gives Blackwell's hypotheses of Theorem 4(b) -/
lemma local_of_gset (M : Model St Act) (f g : St → Act) (hg : g ∈ GSet M f) :
    (∃ s, g s ∈ M.gainBiasImprovementSet f s) ∧
      (∀ s, g s ∉ M.gainBiasImprovementSet f s → g s = f s) := by
  obtain ⟨c1, c2, c3, c4⟩ := hg
  have hr : ∀ t, M.r g t = M.i t (g t) := fun t => rfl
  constructor
  · obtain ⟨s, hs⟩ := c3
    refine ⟨s, ?_⟩
    rcases lt_or_eq_of_le (c1 s) with hl | he
    · exact Or.inl hl
    · rcases hs with hs | hs
      · exact Or.inl hs
      · exact Or.inr ⟨he.symm, by rw [← hr]; exact hs⟩
  · intro s hs
    have e1 : M.pDot s (g s) (M.x f) = M.x f s := by
      rcases lt_or_eq_of_le (c1 s) with hl | he
      · exact absurd (Or.inl hl) hs
      · exact he.symm
    have e2 : M.r g s + M.pDot s (g s) (M.y f) = M.x f s + M.y f s := by
      rcases lt_or_eq_of_le (c2 s e1) with hl | he
      · exact absurd (Or.inr ⟨e1, by rw [← hr]; exact hl⟩) hs
      · exact he.symm
    exact c4 s e1 e2

/-- Theorem 5(b) -/
theorem theorem_5b_core (M : Model St Act) (f g : St → Act) (hg : g ∈ GSet M f) :
    ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
      VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by
  obtain ⟨h1, h2⟩ := local_of_gset M f g hg
  exact theorem_4b_core M f g h1 h2

lemma localG_empty (M : Model St Act) (f : St → Act) (hG : GSet M f = ∅) :
    ∀ s, M.gainBiasImprovementSet f s = ∅ := by
  intro s
  refine Set.eq_empty_iff_forall_notMem.2 fun a ha => ?_
  have hmem : Function.update f s a ∈ GSet M f := by
    apply gset_of_local
    · intro t
      by_cases ht : t = s
      · subst ht; right; rw [Function.update_self]; exact ha
      · left; exact Function.update_of_ne ht a f
    · exact ⟨s, by rw [Function.update_self]; exact ha⟩
  rw [hG] at hmem; exact hmem

/-- Theorem 5(a) -/
theorem theorem_5a_core (M : Model St Act) (f : St → Act) (hG : GSet M f = ∅) :
    f ∈ Fprime M :=
  fun g => (theorem_4e_core M f (localG_empty M f hG)).1 g

/-- Corollary 1 -/
theorem corollary_1_core (M : Model St Act) (f g : St → Act) (hg : g ∈ GSet M f) :
    VecGt (M.x g) (M.x f) ∨ (M.x g = M.x f ∧ VecGt (M.y g) (M.y f)) := by
  obtain ⟨β₀, hβ₀, hV⟩ := theorem_5b_core M f g hg
  obtain ⟨K, hK, hL2⟩ := b_laurent2 M g f
  have hev : ∀ᶠ β in 𝓝[<] (1 : ℝ), 0 ≤ β ∧ β < 1 ∧
      VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by
    filter_upwards [bev (show max β₀ 0 < 1 from max_lt hβ₀ one_pos)] with β ⟨h1, h2⟩
    exact ⟨le_trans (le_max_right _ _) h1.le, h2,
      hV β (lt_of_le_of_lt (le_max_left _ _) h1) h2⟩
  have LEX : ∀ s, M.x f s - M.x g s ≤ 0 ∧
      (M.x f s - M.x g s = 0 → M.y f s - M.y g s ≤ 0) := by
    intro s
    apply blex hK
    intro ε hε
    refine Eventually.frequently ?_
    filter_upwards [hev] with β ⟨h0, h1, hgt⟩
    have a := (abs_le.1 (hL2 β h0 h1 s)).1
    have b := hgt.1 s
    linarith
  have hxge : M.x f ≤ M.x g := fun s => by linarith [(LEX s).1]
  by_cases hx : M.x g = M.x f
  · right
    refine ⟨hx, fun s => ?_, fun hy => ?_⟩
    · have := (LEX s).2 (by rw [hx]; ring); linarith
    · obtain ⟨-, -, ⟨s, hs⟩, -⟩ := hg
      have e1 : M.pDot s (g s) (M.x f) = M.x f s := by
        rw [← hx, v_pDot, bQx]
      have e2 : M.r g s + M.pDot s (g s) (M.y f) = M.x f s + M.y f s := by
        rw [← hx, ← hy, v_pDot, bQy]; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rcases hs with hs | hs
      · rw [e1] at hs; exact lt_irrefl _ hs
      · rw [e2] at hs; exact lt_irrefl _ hs
  · left; exact ⟨hxge, hx⟩

/-! ### The reduced problem of p. 1289: action sets `E(s, f)`, rewards `−y(f)` -/

open Classical in
/-- actions outside `E(s, f)` are replaced by `f(s)` -/
noncomputable def auxAct (M : Model St Act) (f : St → Act) (s : St) (a : Act) : Act :=
  if a ∈ M.gainBiasEqualSet f s then a else f s

/-- the reduced model -/
noncomputable def auxM (M : Model St Act) (f : St → Act) : Model St Act where
  i := fun s _ => -(M.y f s)
  q := fun s a => M.q s (auxAct M f s a)
  q_nonneg := fun s a s' => M.q_nonneg _ _ _
  q_sum_one := fun s a => M.q_sum_one _ _

lemma auxAct_of_mem (M : Model St Act) (f : St → Act) (s : St) (a : Act)
    (h : a ∈ M.gainBiasEqualSet f s) : auxAct M f s a = a := by
  classical
  simp only [auxAct, if_pos h]

lemma auxAct_of_not (M : Model St Act) (f : St → Act) (s : St) (a : Act)
    (h : a ∉ M.gainBiasEqualSet f s) : auxAct M f s a = f s := by
  classical
  simp only [auxAct, if_neg h]

lemma aux_Q (M : Model St Act) (f g : St → Act) (hg : g ∈ ESet M f) :
    (auxM M f).Q g = M.Q g := by
  ext s s'
  simp only [Model.Q, auxM, Matrix.of_apply, auxAct_of_mem M f s (g s) (hg s)]

lemma fE (M : Model St Act) (f : St → Act) : f ∈ ESet M f := fun s => bE_self M f s

lemma aux_pDot (M : Model St Act) (f : St → Act) (s : St) (a : Act) (v : St → ℝ) :
    (auxM M f).pDot s a v = M.pDot s (auxAct M f s a) v := rfl

lemma aux_r (M : Model St Act) (f g : St → Act) : (auxM M f).r g = -(M.y f) := rfl

lemma aux_x (M : Model St Act) (f g : St → Act) (hg : g ∈ ESet M f) :
    (auxM M f).x g = w M f g := by
  simp only [Model.x, Model.Qstar, aux_Q M f g hg, aux_r, w]

lemma aux_y (M : Model St Act) (f g : St → Act) (hg : g ∈ ESet M f) :
    (auxM M f).y g = M.Hf g *ᵥ (-(M.y f)) := by
  simp only [Model.y, Model.Hf, aux_Q M f g hg, aux_r]

lemma aux_xf (M : Model St Act) (f : St → Act) : (auxM M f).x f = 0 := by
  rw [aux_x M f f (fE M f), w_self]

lemma aux_yf (M : Model St Act) (f : St → Act) : (auxM M f).y f = z M f := by
  rw [aux_y M f f (fE M f)]; rfl

lemma pDot_zero (M : Model St Act) (s : St) (a : Act) : M.pDot s a 0 = 0 := by
  simp [Model.pDot]

lemma hset_of_local (M : Model St Act) (f g : St → Act) (hg : g ∈ ESet M f)
    (h : ∀ t, g t = f t ∨ z M f t < -(M.y f t) + M.pDot t (g t) (z M f))
    (hex : ∃ t, z M f t < -(M.y f t) + M.pDot t (g t) (z M f)) : g ∈ HSet M f := by
  refine ⟨hg, fun t => ?_, hex, fun t ht => ?_⟩
  · rcases h t with e | e
    · rw [e, v_Qz]
    · exact e.le
  · rcases h t with e | e
    · exact e
    · rw [ht] at e; exact absurd e (lt_irrefl _)

/-- proof of Theorem 6(d) -/
theorem proof_6d_core (M : Model St Act) (f : St → Act) :
    ∀ g ∈ HSet M f, w M f f = 0 ∧
      (VecGt (w M f g) (w M f f) ∨ (w M f g = w M f f ∧ VecGt (z M g) (z M f))) := by
  intro g hg
  have hgE : g ∈ ESet M f := hg.1
  obtain ⟨-, c2, c3, c4⟩ := hg
  refine ⟨w_self M f, ?_⟩
  have hG : g ∈ GSet (auxM M f) f := by
    apply gset_of_local
    · intro t
      by_cases e : g t = f t
      · exact Or.inl e
      · right; right
        refine ⟨by rw [aux_xf, pDot_zero]; rfl, ?_⟩
        rw [aux_yf, aux_xf, aux_pDot, auxAct_of_mem M f t (g t) (hgE t)]
        have h1 := c2 t
        have h2 : -(M.y f t) + M.pDot t (g t) (z M f) ≠ z M f t := fun hh => e (c4 t hh)
        show _ < -(M.y f t) + _
        simp only [Pi.zero_apply, zero_add]
        exact lt_of_le_of_ne h1 (Ne.symm h2)
    · obtain ⟨t, ht⟩ := c3
      refine ⟨t, Or.inr ⟨by rw [aux_xf, pDot_zero]; rfl, ?_⟩⟩
      rw [aux_yf, aux_xf, aux_pDot, auxAct_of_mem M f t (g t) (hgE t)]
      show _ < -(M.y f t) + _
      simp only [Pi.zero_apply, zero_add]
      exact ht
  have hc := corollary_1_core (auxM M f) f g hG
  rw [aux_x M f g hgE, aux_xf, aux_y M f g hgE, aux_yf, ← w_self M f] at hc
  rcases hc with hc | ⟨he, hc⟩
  · exact Or.inl hc
  · right
    refine ⟨he, ?_⟩
    have hy : M.y g = M.y f := by
      rw [(lemma_4_core M f g hgE).2, he, w_self, add_zero]
    have : z M g = M.Hf g *ᵥ (-(M.y f)) := by rw [z, hy]
    rw [this]; exact hc

/-- proof of Theorem 6(b), first step -/
theorem proof_6b_core (M : Model St Act) (f : St → Act) :
    w M f f = 0 ∧ (HSet M f = ∅ → ∀ g ∈ ESet M f, M.y g ≤ M.y f) := by
  refine ⟨w_self M f, fun hH g hg => ?_⟩
  have hG : ∀ s, (auxM M f).gainBiasImprovementSet f s = ∅ := by
    intro s
    refine Set.eq_empty_iff_forall_notMem.2 fun a ha => ?_
    rcases ha with ha | ⟨-, ha⟩
    · rw [aux_xf, pDot_zero] at ha; exact lt_irrefl _ ha
    · rw [aux_yf, aux_xf, aux_pDot] at ha
      change -(M.y f s) + M.pDot s (auxAct M f s a) (z M f) > 0 + z M f s at ha
      rw [zero_add] at ha
      by_cases hE : a ∈ M.gainBiasEqualSet f s
      · rw [auxAct_of_mem M f s a hE] at ha
        have hmem : Function.update f s a ∈ HSet M f := by
          have hUE : Function.update f s a ∈ ESet M f := by
            intro t
            by_cases ht : t = s
            · subst ht; rw [Function.update_self]; exact hE
            · rw [Function.update_of_ne ht]; exact bE_self M f t
          apply hset_of_local M f _ hUE
          · intro t
            by_cases ht : t = s
            · subst ht; right; rw [Function.update_self]; exact ha
            · left; exact Function.update_of_ne ht a f
          · exact ⟨s, by rw [Function.update_self]; exact ha⟩
        rw [hH] at hmem; exact hmem
      · rw [auxAct_of_not M f s a hE, v_Qz] at ha; exact lt_irrefl _ ha
  have h1 := (theorem_4e_core (auxM M f) f hG).1 g
  rw [aux_x M f g hg, aux_xf] at h1
  rw [(lemma_4_core M f g hg).2]
  intro s
  have := h1 s
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  linarith

/-- Lemma 5 -/
theorem lemma_5_core (M : Model St Act) (f : St → Act) (hG : GSet M f = ∅)
    (hy : ∀ g ∈ ESet M f, M.y g ≤ M.y f) : f ∈ Fdprime M := by
  classical
  have hfF := theorem_5a_core M f hG
  have hloc := localG_empty M f hG
  refine ⟨hfF, fun h hh => ?_⟩
  have hx : M.x h = M.x f := le_antisymm (hfF h) (hh f)
  have hP := bQ_mk M h
  set L := M.Qstar h with hL
  have hLm : IsMarkovMatrix L := bmk_L_markov hP
  set u : St → ℝ := M.x f - M.Q h *ᵥ M.x f with hu
  set v : St → ℝ := M.r h + M.Q h *ᵥ M.y f - M.x f - M.y f with hv
  have huv : ∀ s, 0 ≤ u s ∧ (u s = 0 → v s ≤ 0) := by
    intro s
    have := b_notG M f s (h s) (by rw [hloc s]; exact Set.notMem_empty _)
    simp only [bA, bB] at this
    have e1 : u s = M.x f s - M.pDot s (h s) (M.x f) := rfl
    have e2 : v s = M.i s (h s) + M.pDot s (h s) (M.y f) - M.x f s - M.y f s := rfl
    rw [e1, e2]
    rcases this with h1 | ⟨h1, h2⟩
    · exact ⟨by linarith, fun h3 => by linarith⟩
    · exact ⟨by linarith, fun _ => by linarith⟩
  have hu0 : 0 ≤ u := fun s => (huv s).1
  -- `Q*(h) x(f) ≤ x(f)`
  have hLx : L *ᵥ M.x f ≤ M.x f := by
    have := v_sub_harm hP (e := -(M.x f)) (fun s => by
      have := hu0 s
      simp only [hu, Pi.sub_apply, Pi.zero_apply] at this
      simp only [Matrix.mulVec_neg, Pi.neg_apply]; linarith)
    change -(M.x f) ≤ L *ᵥ -(M.x f) at this
    intro s
    have := this s
    simp only [Matrix.mulVec_neg, Pi.neg_apply] at this
    linarith
  have hLQ : L * M.Q h = L := bmk_LP hP
  have hLu : L *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hLQ, sub_self]
  have hLv : L *ᵥ v = M.x f - L *ᵥ M.x f := by
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, hLQ]
    have : L *ᵥ M.r h = M.x f := by rw [← hx]; rfl
    rw [this]; abel
  -- columns of `Q*(h)` vanish where `u > 0`
  have hcolu : ∀ t s, L t s * u s = 0 := by
    intro t s
    have h0 : ∑ s, L t s * u s = 0 := congrFun hLu t
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_nonneg (hLm.1 t s) (hu0 s))).1 h0 s
      (Finset.mem_univ s)
  have hterm : ∀ t s, L t s * v s ≤ 0 := by
    intro t s
    by_cases h0 : u s = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hLm.1 t s) ((huv s).2 h0)
    · have : L t s = 0 := by
        rcases mul_eq_zero.1 (hcolu t s) with h1 | h1
        · exact h1
        · exact absurd h1 h0
      rw [this, zero_mul]
  have hLv0 : L *ᵥ v = 0 := by
    funext t
    apply le_antisymm
    · exact Finset.sum_nonpos fun s _ => hterm t s
    · have := hLx t
      have e := congrFun hLv t
      simp only [Pi.sub_apply] at e
      show 0 ≤ (L *ᵥ v) t
      linarith
  have hcolv : ∀ t s, L t s * v s = 0 := by
    intro t s
    have h0 : ∑ s, -(L t s * v s) = 0 := by
      rw [Finset.sum_neg_distrib]; have := congrFun hLv0 t; simp only [Pi.zero_apply] at this
      change -(L *ᵥ v) t = 0; rw [this, neg_zero]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => neg_nonneg.2 (hterm t s))).1 h0 s
      (Finset.mem_univ s)
    linarith
  have hsupp : ∀ t s, L t s ≠ 0 → h s ∈ M.gainBiasEqualSet f s := by
    intro t s hts
    have hu' : u s = 0 := by
      rcases mul_eq_zero.1 (hcolu t s) with h1 | h1
      · exact absurd h1 hts
      · exact h1
    have hv' : v s = 0 := by
      rcases mul_eq_zero.1 (hcolv t s) with h1 | h1
      · exact absurd h1 hts
      · exact h1
    have e1 : u s = M.x f s - M.pDot s (h s) (M.x f) := rfl
    have e2 : v s = M.i s (h s) + M.pDot s (h s) (M.y f) - M.x f s - M.y f s := rfl
    exact ⟨by linarith, by linarith⟩
  -- the rule `g` agreeing with `h` where `h(s) ∈ E(s, f)`
  let g : St → Act := fun s => if h s ∈ M.gainBiasEqualSet f s then h s else f s
  have hgE : g ∈ ESet M f := by
    intro s
    by_cases hs : h s ∈ M.gainBiasEqualSet f s
    · simp only [g, if_pos hs]; exact hs
    · simp only [g, if_neg hs]; exact bE_self M f s
  have hLg : L * M.Q g = L := by
    refine Eq.trans ?_ hLQ
    ext t s'
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hts : L t s = 0
    · rw [hts, zero_mul, zero_mul]
    · have hs := hsupp t s hts
      simp only [Model.Q, Matrix.of_apply, g, if_pos hs]
  have hLLg : L * M.Qstar g = L := v_left_fix (bQ_mk M g) hLg
  have hwg : 0 ≤ M.Qstar g *ᵥ M.y f := by
    have h1 := hy g hgE
    rw [(lemma_4_core M f g hgE).2] at h1
    intro s
    have := h1 s
    simp only [Pi.add_apply, w, Matrix.mulVec_neg, Pi.neg_apply] at this
    simp only [Pi.zero_apply]; linarith
  have hLyf : 0 ≤ L *ᵥ M.y f := by
    rw [← hLLg, ← Matrix.mulVec_mulVec]
    have := v_mono hLm.1 hwg
    rwa [Matrix.mulVec_zero] at this
  -- the constant `K` with `v ≤ K u`
  set K : ℝ := ∑ s, (if 0 < u s then |v s| / u s else 0) with hK
  have hvK : ∀ s, v s ≤ K * u s := by
    intro s
    by_cases hs : 0 < u s
    · have h1 : |v s| / u s ≤ K := by
        have := Finset.single_le_sum (f := fun s => if 0 < u s then |v s| / u s else 0)
          (fun s _ => by
            show 0 ≤ (if 0 < u s then |v s| / u s else 0)
            split_ifs with hh
            · exact div_nonneg (abs_nonneg _) hh.le
            · exact le_rfl) (Finset.mem_univ s)
        simpa only [if_pos hs] using this
      calc v s ≤ |v s| := le_abs_self _
        _ = |v s| / u s * u s := by field_simp
        _ ≤ K * u s := mul_le_mul_of_nonneg_right h1 hs.le
    · have h0 : u s = 0 := le_antisymm (not_lt.1 hs) (hu0 s)
      rw [h0, mul_zero]; exact (huv s).2 h0
  set d : St → ℝ := M.y h - M.y f with hd
  have hQd : M.Q h *ᵥ d = d - v := by
    rw [hd, Matrix.mulVec_sub, bQy, hx]
    funext s
    simp only [hv, Pi.sub_apply, Pi.add_apply]; ring
  set e : St → ℝ := d - K • M.x f with he
  have hee : e ≤ M.Q h *ᵥ e := by
    intro s
    have h1 : M.Q h *ᵥ e = d - v - K • (M.x f - u) := by
      rw [he, Matrix.mulVec_sub, hQd, Matrix.mulVec_smul, hu]; abel_nf
    rw [h1]
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := hvK s
    nlinarith
  have hLe := v_sub_harm hP hee
  change e ≤ L *ᵥ e at hLe
  have hLe' : L *ᵥ e = -(L *ᵥ M.y f) - K • M.x f := by
    have hLxf : L *ᵥ M.x f = M.x f := by
      have := congrArg (fun z => M.x f - z) hLv
      simp only [hLv0, sub_zero, sub_sub_cancel] at this
      exact this.symm
    change M.Qstar h *ᵥ e = _
    rw [he, Matrix.mulVec_sub, Matrix.mulVec_smul, hd, Matrix.mulVec_sub, bLy, ← hL, hLxf]
    abel
  rw [hLe'] at hLe
  intro s
  have h1 := hLe s
  have h2 := hLyf s
  simp only [he, hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
    Pi.zero_apply] at h1 h2
  linarith

/-- Theorem 6 -/
theorem theorem_6_core (M : Model St Act) (f : St → Act) :
    (GSet M f = ∅ → f ∈ Fprime M) ∧
      (GSet M f ∪ HSet M f = ∅ → f ∈ Fdprime M) ∧
      (∀ g ∈ GSet M f, VecGt (M.x g) (M.x f) ∨ (M.x g = M.x f ∧ VecGt (M.y g) (M.y f))) ∧
      (∀ g ∈ HSet M f, M.x g = M.x f ∧
        (VecGt (M.y g) (M.y f) ∨ (M.y g = M.y f ∧ VecGt (z M g) (z M f)))) := by
  refine ⟨theorem_5a_core M f, fun hGH => ?_, fun g hg => corollary_1_core M f g hg,
    fun g hg => ?_⟩
  · have hG : GSet M f = ∅ := Set.subset_eq_empty Set.subset_union_left hGH
    have hH : HSet M f = ∅ := Set.subset_eq_empty Set.subset_union_right hGH
    exact lemma_5_core M f hG ((proof_6b_core M f).2 hH)
  · have hgE : g ∈ ESet M f := hg.1
    refine ⟨(lemma_2_core M f g hgE).1, ?_⟩
    have hy := (lemma_4_core M f g hgE).2
    obtain ⟨hw0, hd⟩ := proof_6d_core M f g hg
    rcases hd with hd | ⟨he, hz⟩
    · left
      rw [hw0] at hd
      refine ⟨fun s => ?_, fun heq => hd.2 ?_⟩
      · rw [hy]; have := hd.1 s; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; linarith
      · rw [hy] at heq
        funext s; have := congrFun heq s; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
        linarith
    · right
      refine ⟨by rw [hy, he, hw0, add_zero], hz⟩

end VeinottNoDiscount.Improve

open BlackwellDiscreteDP.NearOne VeinottNoDiscount.Improve

theorem solution {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    (GSet M f = ∅ → f ∈ Fprime M) ∧
      ∀ g ∈ GSet M f, ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
        VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by
  exact ⟨theorem_5a_core M f, fun g hg => theorem_5b_core M f g hg⟩
