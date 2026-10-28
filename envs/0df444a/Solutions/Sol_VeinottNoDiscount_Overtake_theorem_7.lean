-- Prove2me | solution 1 for VeinottNoDiscount.Overtake.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T06:26:21.347833+00:00
-- url     : https://prove2.me/submissions/8caa15dc-a55b-43bf-94cf-f23506c69061

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Overtake_Criteria
import Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4b
import Theorems.Thm_BlackwellDiscreteDP_NearOne_theorem_4e

/-!
Veinott (1966), Theorem 7: `f ∈ F″` iff the Cesàro averages of `Vⁿ(f^∞) − Vⁿ(g^∞)` tend to a limit
`≥ 0` in `[−∞, +∞]` for every decision rule `g`.
Reduction to Blackwell (1962) Theorem 4(b) (`BlackwellDiscreteDP.NearOne.theorem_4b`) and
Theorem 4(e) (`BlackwellDiscreteDP.NearOne.theorem_4e`), both Proved. Proved below: Blackwell's
Lemma 1 (Cesàro limit `Q*` exists, `Q*P = PQ* = Q*Q* = Q*`, `I − P + Q*` invertible, deviation
matrix identities), Veinott's (28), the Laurent expansion `V_β = x/(1−β) + y + o(1)`, and the
assembly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

section Main
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VT7

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma markov_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) :
    IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero =>
    constructor
    · intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · intro i; rw [pow_zero]; simp [Matrix.one_apply]
  | succ k ih =>
    constructor
    · intro i j; rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih.1 i l) (hP.1 l j)
    · intro i; rw [pow_succ]; simp only [Matrix.mul_apply]; rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hP.2, mul_one]; exact ih.2 i

omit [DecidableEq n] in
lemma markov_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun l _ => hP.1 i l) (Finset.mem_univ j)

lemma cesaro_markov {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  constructor
  · intro i j
    simp only [cesaroMean, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hN.le)
      (Finset.sum_nonneg fun k _ => (markov_pow hP k).1 i j)
  · intro i
    simp only [cesaroMean, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [fun k => (markov_pow hP k).2 i]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; push_cast
    exact inv_mul_cancel₀ hN.ne'

/-- a bounded matrix sequence divided by `N+1` tends to zero -/
lemma tend_div {B : ℕ → Matrix n n ℝ} {C : ℝ} (hB : ∀ N i j, |B N i j| ≤ C) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • B N) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * B N i j) atTop (𝓝 0)
  have h0 : Tendsto (fun N : ℕ => C * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  refine squeeze_zero_norm (fun N => ?_) h0
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 (by positivity : (0:ℝ) < (N:ℝ)+1))]
  rw [one_div, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hB N i j) (inv_nonneg.2 (by positivity))

lemma cesaro_mul_sub {P : Matrix n n ℝ} (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  simp_rw [← pow_succ]
  rw [Finset.sum_range_sub (fun k => P ^ k)]; simp

lemma mul_cesaro_sub {P : Matrix n n ℝ} (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  simp_rw [← pow_succ']
  rw [Finset.sum_range_sub (fun k => P ^ k)]; simp

lemma bound_pow_sub {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) (i j : n) :
    |(P ^ (N + 1) - 1) i j| ≤ 1 := by
  have h1 := (markov_pow hP (N + 1)).1 i j
  have h2 := markov_le_one (markov_pow hP (N + 1)) i j
  have h3 := (markov_pow hP 0).1 i j
  have h4 := markov_le_one (markov_pow hP 0) i j
  rw [pow_zero] at h3 h4
  rw [Matrix.sub_apply, abs_le]; constructor <;> linarith

lemma clusterPt_eq {X : Type*} [TopologicalSpace X] [T2Space X] {u : ℕ → X} {x y : X}
    (hx : MapClusterPt x atTop u) (hy : Tendsto u atTop (𝓝 y)) : x = y := by
  apply eq_of_nhds_neBot
  have : ClusterPt x (𝓝 y) := ClusterPt.mono hx hy
  exact this

lemma const_mul_cesaro {P L : Matrix n n ℝ} (hL : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hL]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]; simp_rw [hk]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma cesaro_mul_const {P L : Matrix n n ℝ} (hL : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, hL]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]; simp_rw [hk]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

/-- Blackwell Lemma 1(a): the Cesàro means of a Markov matrix converge, and the limit `Q*`
satisfies `Q* P = P Q* = Q* Q* = Q*`. -/
lemma limit_props {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) ∧
      limitMatrix P * P = limitMatrix P ∧ P * limitMatrix P = limitMatrix P ∧
      limitMatrix P * limitMatrix P = limitMatrix P := by
  set K : Set (Matrix n n ℝ) := Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => Set.Icc (0:ℝ) 1
    with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ N, cesaroMean P N ∈ K := by
    intro N i _ j _
    exact ⟨(cesaro_markov hP N).1 i j, markov_le_one (cesaro_markov hP N) i j⟩
  -- every cluster point is P-invariant on both sides
  have hinv : ∀ L, MapClusterPt L atTop (cesaroMean P) → L * P = L ∧ P * L = L := by
    intro L hL
    have hT := tend_div (C := 1) (B := fun N => P ^ (N + 1) - 1) (bound_pow_sub hP)
    constructor
    · have hc : MapClusterPt (L * P - L) atTop (fun N => cesaroMean P N * P - cesaroMean P N) :=
        hL.tendsto_comp (f := fun M : Matrix n n ℝ => M * P - M)
          (((continuous_id.matrix_mul continuous_const).sub continuous_id).tendsto L)
      have := clusterPt_eq hc (by simpa only [cesaro_mul_sub] using hT)
      exact sub_eq_zero.1 this
    · have hc : MapClusterPt (P * L - L) atTop (fun N => P * cesaroMean P N - cesaroMean P N) :=
        hL.tendsto_comp (f := fun M : Matrix n n ℝ => P * M - M)
          (((continuous_const.matrix_mul continuous_id).sub continuous_id).tendsto L)
      have := clusterPt_eq hc (by simpa only [mul_cesaro_sub] using hT)
      exact sub_eq_zero.1 this
  have huniq : ∀ L L', MapClusterPt L atTop (cesaroMean P) →
      MapClusterPt L' atTop (cesaroMean P) → L = L' := by
    intro L L' hL hL'
    have h1 : L * L' = L := by
      have hc : MapClusterPt (L * L') atTop (fun N => L * cesaroMean P N) :=
        hL'.tendsto_comp (f := fun M : Matrix n n ℝ => L * M)
          ((continuous_const.matrix_mul continuous_id).tendsto L')
      exact clusterPt_eq hc (by simp only [const_mul_cesaro (hinv L hL).1]; exact tendsto_const_nhds)
    have h2 : L * L' = L' := by
      have hc : MapClusterPt (L * L') atTop (fun N => cesaroMean P N * L') :=
        hL.tendsto_comp (f := fun M : Matrix n n ℝ => M * L')
          ((continuous_id.matrix_mul continuous_const).tendsto L)
      exact clusterPt_eq hc (by simp only [cesaro_mul_const (hinv L' hL').2]; exact tendsto_const_nhds)
    rw [← h1, h2]
  obtain ⟨L0, -, hL0⟩ := hK.exists_mapClusterPt (f := atTop) (u := cesaroMean P)
    (by rw [Filter.le_principal_iff, Filter.mem_map]; exact Filter.Eventually.of_forall hmem)
  have hT : Tendsto (cesaroMean P) atTop (𝓝 L0) :=
    hK.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hmem)
      (fun L _ hL => huniq L L0 hL hL0)
  have hlim : limitMatrix P = L0 := hT.limUnder_eq
  have hP0 := hinv L0 hL0
  refine ⟨hlim ▸ hT, hlim ▸ hP0.1, hlim ▸ hP0.2, ?_⟩
  rw [hlim]
  have hc : Tendsto (fun N => L0 * cesaroMean P N) atTop (𝓝 (L0 * L0)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto L0).comp hT
  simp only [const_mul_cesaro hP0.1] at hc
  exact (tendsto_nhds_unique tendsto_const_nhds hc).symm

section Dev
variable {P : Matrix n n ℝ}

lemma pow_mul_limit (hP : IsMarkovMatrix P) (k : ℕ) : P ^ k * limitMatrix P = limitMatrix P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, (limit_props hP).2.2.1, ih]

lemma mulVec_fix_limit (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hc : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N; unfold cesaroMean
    rw [Matrix.smul_mulVec, Matrix.sum_mulVec]; simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have hcont : Continuous fun A : Matrix n n ℝ => A *ᵥ v := continuous_id.matrix_mulVec continuous_const
  have hT : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    (hcont.tendsto _).comp (limit_props hP).1
  simp only [hc] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

lemma W_det (hP : IsMarkovMatrix P) : IsUnit (1 - P + limitMatrix P).det := by
  obtain ⟨-, hQP, hPQ, hQQ⟩ := limit_props hP
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv0
  have hQW : limitMatrix P * (1 - P + limitMatrix P) = limitMatrix P := by
    rw [mul_add, mul_sub, mul_one, hQP, hQQ]; abel
  have h1 : limitMatrix P *ᵥ v = 0 := by
    rw [← hQW, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : P *ᵥ v = v := by
    have := hv
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h1, add_zero, sub_eq_zero] at this
    exact this.symm
  rw [← mulVec_fix_limit hP h2, h1]

lemma dev_props (hP : IsMarkovMatrix P) :
    limitMatrix P * deviationMatrix P = 0 ∧ deviationMatrix P * limitMatrix P = 0 ∧
    (1 - P) * deviationMatrix P = 1 - limitMatrix P ∧
    deviationMatrix P * (1 - P) = 1 - limitMatrix P := by
  obtain ⟨-, hQP, hPQ, hQQ⟩ := limit_props hP
  have hd := W_det hP
  have hD : deviationMatrix P = (1 - P + limitMatrix P)⁻¹ - limitMatrix P := rfl
  rw [hD]
  generalize hQ : limitMatrix P = Q at hQP hPQ hQQ hd ⊢
  generalize hW : 1 - P + Q = W at hd ⊢
  have hWZ : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hd
  have hZW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hd
  have hQW : Q * W = Q := by rw [← hW, mul_add, mul_sub, mul_one, hQP, hQQ]; abel
  have hWQ : W * Q = Q := by rw [← hW, add_mul, sub_mul, one_mul, hPQ, hQQ]; abel
  have hQZ : Q * W⁻¹ = Q := calc Q * W⁻¹ = (Q * W) * W⁻¹ := by rw [hQW]
    _ = Q := by rw [mul_assoc, hWZ, mul_one]
  have hZQ : W⁻¹ * Q = Q := calc W⁻¹ * Q = W⁻¹ * (W * Q) := by rw [hWQ]
    _ = Q := by rw [← mul_assoc, hZW, one_mul]
  have h1P : 1 - P = W - Q := by rw [← hW]; abel
  rw [h1P]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_sub, hQZ, hQQ, sub_self]
  · rw [sub_mul, hZQ, hQQ, sub_self]
  · rw [sub_mul, mul_sub, mul_sub, hWZ, hWQ, hQZ, hQQ]; abel
  · rw [sub_mul, mul_sub, mul_sub, hZW, hZQ, hQW, hQQ]; abel

lemma sum_pow_eq (hP : IsMarkovMatrix P) (m : ℕ) :
    ∑ i ∈ Finset.range m, P ^ i =
      (m : ℝ) • limitMatrix P + deviationMatrix P - P ^ m * deviationMatrix P := by
  obtain ⟨-, -, h3, -⟩ := dev_props hP
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hPH : P * deviationMatrix P = deviationMatrix P - (1 - limitMatrix P) := by
      rw [← h3, sub_mul, one_mul]; abel
    have e : P ^ (m + 1) * deviationMatrix P =
        P ^ m * deviationMatrix P - P ^ m + limitMatrix P := by
      rw [pow_succ, mul_assoc, hPH, mul_sub, mul_sub, mul_one, pow_mul_limit hP]; abel
    rw [e]; push_cast; rw [add_smul, one_smul]; abel

lemma sum_Icc_eq {V : Type*} [AddCommGroup V] (g : ℕ → V) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k = ∑ k ∈ Finset.range (N + 1), g k - g 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega), ih, Finset.sum_range_succ _ (N + 1)]
    abel

lemma avg_pow_tend (hP : IsMarkovMatrix P) (v : n → ℝ) (hv : limitMatrix P *ᵥ v = 0) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N, (P ^ k) *ᵥ v) atTop (𝓝 0) := by
  have hcont : Continuous fun A : Matrix n n ℝ => A *ᵥ v := continuous_id.matrix_mulVec continuous_const
  have hA : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 0) := by
    rw [← hv]; exact (hcont.tendsto _).comp (limit_props hP).1
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => 1 + (N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hlim := (hc.smul hA).sub (hinv.smul (tendsto_const_nhds (x := v)))
  simp only [smul_zero, zero_smul, sub_zero] at hlim
  refine hlim.congr' (Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  have hN : (N : ℝ) ≠ 0 := by positivity
  have hsum : ∑ k ∈ Finset.range (N + 1), P ^ k = ((N : ℝ) + 1) • cesaroMean P N := by
    unfold cesaroMean; rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hr : (N : ℝ)⁻¹ * ((N : ℝ) + 1) = 1 + (N : ℝ)⁻¹ := by
    rw [mul_add, mul_one, inv_mul_cancel₀ hN]
  show _ = (N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N, P ^ k *ᵥ v
  rw [sum_Icc_eq (fun k => P ^ k *ᵥ v), ← Matrix.sum_mulVec, pow_zero, Matrix.one_mulVec, hsum,
    Matrix.smul_mulVec, smul_sub, smul_smul, hr]

end Dev

section MDP
variable {St Act : Type*} [Fintype St] [DecidableEq St]

lemma markovQ (M : Model St Act) (f : St → Act) : IsMarkovMatrix (M.Q f) :=
  ⟨fun i j => M.q_nonneg i (f i) j, fun i => M.q_sum_one i (f i)⟩

lemma Qn_stat (M : Model St Act) (f : St → Act) (k : ℕ) :
    M.Qn (Policy.stationary f) k = M.Q f ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ← ih]; rfl

lemma Vn_stat (M : Model St Act) (f : St → Act) (m : ℕ) :
    VeinottNoDiscount.Overtake.Vn M (Policy.stationary f) m =
      (m : ℝ) • M.x f + M.y f - (M.Q f ^ m) *ᵥ M.y f := by
  have hP := markovQ M f
  unfold VeinottNoDiscount.Overtake.Vn
  simp_rw [Qn_stat]
  have : ∀ i, M.r (Policy.stationary f i) = M.r f := fun _ => rfl
  simp_rw [this]
  rw [← Matrix.sum_mulVec, sum_pow_eq hP, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

lemma Qstar_y (M : Model St Act) (f : St → Act) : M.Qstar f *ᵥ M.y f = 0 := by
  have h := (dev_props (markovQ M f)).1
  show limitMatrix (M.Q f) *ᵥ (deviationMatrix (M.Q f) *ᵥ M.r f) = 0
  rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

lemma sum_diff (M : Model St Act) (f g : St → Act) (s : St) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (VeinottNoDiscount.Overtake.Vn M (Policy.stationary f) n s -
        VeinottNoDiscount.Overtake.Vn M (Policy.stationary g) n s) =
      (N : ℝ) * (N + 1) / 2 * (M.x f s - M.x g s) + N * (M.y f s - M.y g s)
      - ((∑ k ∈ Finset.Icc 1 N, (M.Q f ^ k) *ᵥ M.y f) s -
        (∑ k ∈ Finset.Icc 1 N, (M.Q g ^ k) *ᵥ M.y g) s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega),
      Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega),
      Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega), ih, Vn_stat, Vn_stat]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring

end MDP

lemma ereal_tri {u w : ℕ → ℝ} {c d : ℝ} (hw : Tendsto w atTop (𝓝 0))
    (hu : ∀ N : ℕ, 1 ≤ N → u N = ((N : ℝ) + 1) / 2 * c + d - w N) :
    (0 < c → Tendsto (fun N => (u N : EReal)) atTop (𝓝 ⊤)) ∧
    (c < 0 → Tendsto (fun N => (u N : EReal)) atTop (𝓝 ⊥)) ∧
    (c = 0 → Tendsto (fun N => (u N : EReal)) atTop (𝓝 (d : EReal))) := by
  have hev : (fun N : ℕ => ((N : ℝ) + 1) / 2 * c + d - w N) =ᶠ[atTop] u :=
    Filter.eventually_atTop.2 ⟨1, fun N hN => (hu N hN).symm⟩
  have hlin : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / 2) atTop atTop := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))
    exact this.atTop_div_const (by norm_num)
  have hdw : Tendsto (fun N => d - w N) atTop (𝓝 (d - 0)) := tendsto_const_nhds.sub hw
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · rw [EReal.tendsto_coe_nhds_top_iff]
    refine Tendsto.congr' hev ?_
    have := (Tendsto.atTop_mul_const hc hlin).atTop_add hdw
    simpa only [add_sub_assoc] using this
  · rw [EReal.tendsto_coe_nhds_bot_iff]
    refine Tendsto.congr' hev ?_
    have := (Tendsto.atTop_mul_const_of_neg hc hlin).atBot_add hdw
    simpa only [add_sub_assoc] using this
  · rw [EReal.tendsto_coe]
    refine Tendsto.congr' hev ?_
    subst hc
    simpa using hdw

theorem main_of_key {St Act : Type*} [Fintype St] [DecidableEq St]
    (M : Model St Act) (f : St → Act)
    (hkey : f ∈ VeinottNoDiscount.Improve.Fdprime M →
      ∀ g : St → Act, ∀ s, M.x g s = M.x f s → M.y g s ≤ M.y f s) :
    f ∈ VeinottNoDiscount.Improve.Fdprime M ↔
      ∀ g : St → Act, ∀ s : St, ∃ L : EReal,
        Tendsto (fun N : ℕ => ((((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            (VeinottNoDiscount.Overtake.Vn M (Policy.stationary f) n s -
              VeinottNoDiscount.Overtake.Vn M (Policy.stationary g) n s)) : ℝ) : EReal))
          atTop (𝓝 L) ∧ 0 ≤ L := by
  have hE : ∀ h : St → Act, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
      ∑ k ∈ Finset.Icc 1 N, (M.Q h ^ k) *ᵥ M.y h) atTop (𝓝 0) :=
    fun h => avg_pow_tend (markovQ M h) _ (Qstar_y M h)
  have hT : ∀ g s, _ := fun g s => ereal_tri (c := M.x f s - M.x g s) (d := M.y f s - M.y g s)
    (w := fun N => ((N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N, (M.Q f ^ k) *ᵥ M.y f) s -
      ((N : ℝ)⁻¹ • ∑ k ∈ Finset.Icc 1 N, (M.Q g ^ k) *ᵥ M.y g) s)
    (u := fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            (VeinottNoDiscount.Overtake.Vn M (Policy.stationary f) n s -
              VeinottNoDiscount.Overtake.Vn M (Policy.stationary g) n s))
    (by simpa using (tendsto_pi_nhds.1 ((hE f).sub (hE g))) s)
    (fun N hN => by
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      simp only [sum_diff, Pi.smul_apply, smul_eq_mul]
      field_simp)
  constructor
  · intro hf g s
    have hc : M.x g s ≤ M.x f s := hf.1 g s
    rcases lt_or_eq_of_le hc with hlt | heq
    · exact ⟨⊤, (hT g s).1 (sub_pos.2 hlt), le_top⟩
    · exact ⟨_, (hT g s).2.2 (by rw [heq, sub_self]),
        EReal.coe_nonneg.2 (sub_nonneg.2 (hkey hf g s heq))⟩
  · intro h
    have hF' : f ∈ VeinottNoDiscount.Improve.Fprime M := by
      intro g s
      by_contra hlt'
      have hlt := not_le.1 hlt'
      obtain ⟨L, hL, hL0⟩ := h g s
      have := tendsto_nhds_unique hL ((hT g s).2.1 (sub_neg.2 hlt))
      rw [this] at hL0
      exact absurd (le_bot_iff.1 hL0) EReal.zero_ne_bot
    refine ⟨hF', fun g hg s => ?_⟩
    have heq : M.x g s = M.x f s := le_antisymm (hF' g s) (hg f s)
    obtain ⟨L, hL, hL0⟩ := h g s
    have := tendsto_nhds_unique hL ((hT g s).2.2 (by rw [heq, sub_self]))
    rw [this] at hL0
    exact sub_nonneg.1 (EReal.coe_nonneg.1 hL0)

section Laurent
variable {P : Matrix n n ℝ}

lemma norm_mulVec_le (hP : IsMarkovMatrix P) (u : n → ℝ) : ‖P *ᵥ u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, P i j * u j| ≤ ∑ j, |P i j * u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, P i j * ‖u‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hP.1 i j)]
        exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u j)
          (hP.1 i j)
    _ = ‖u‖ := by rw [← Finset.sum_mul, hP.2 i, one_mul]

/-- the resolvent series `S_β(u) = Σ β^k P^k u` -/
noncomputable def Sres (P : Matrix n n ℝ) (β : ℝ) (u : n → ℝ) : n → ℝ :=
  ∑' k : ℕ, β ^ k • ((P ^ k) *ᵥ u)

lemma Sres_summable (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (u : n → ℝ) :
    Summable fun k : ℕ => β ^ k • ((P ^ k) *ᵥ u) := by
  refine Summable.of_norm_bounded (g := fun k => β ^ k * ‖u‖)
    ((summable_geometric_of_lt_one h0 h1).mul_right _) fun k => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (norm_mulVec_le (markov_pow hP k) u) (pow_nonneg h0 k)

lemma Sres_bound (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (u : n → ℝ) :
    (1 - β) * ‖Sres P β u‖ ≤ ‖u‖ := by
  have hb : ‖Sres P β u‖ ≤ (1 - β)⁻¹ * ‖u‖ :=
    tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h0 h1).mul_right ‖u‖) fun k => by
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_left (norm_mulVec_le (markov_pow hP k) u) (pow_nonneg h0 k)
  have hpos : 0 < 1 - β := by linarith
  calc (1 - β) * ‖Sres P β u‖ ≤ (1 - β) * ((1 - β)⁻¹ * ‖u‖) :=
        mul_le_mul_of_nonneg_left hb hpos.le
    _ = ‖u‖ := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

lemma Sres_hasSum_P (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (u : n → ℝ) :
    HasSum (fun k : ℕ => P *ᵥ (β ^ k • ((P ^ k) *ᵥ u))) (P *ᵥ Sres P β u) := by
  have h := (Sres_summable hP h0 h1 u).hasSum.map (Matrix.mulVecLin P)
    (Matrix.mulVecLin P).continuous_of_finiteDimensional
  exact h

lemma Sres_shift (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (u : n → ℝ) :
    Sres P β u = u + β • (P *ᵥ Sres P β u) := by
  have hs := Sres_summable hP h0 h1 u
  have h2 := (Sres_hasSum_P hP h0 h1 u).const_smul β
  conv_lhs => rw [show Sres P β u = _ from hs.tsum_eq_zero_add]
  congr 1
  · simp
  · rw [← h2.tsum_eq]
    congr 1; funext k
    rw [Matrix.mulVec_smul, smul_smul, ← pow_succ', Matrix.mulVec_mulVec, ← pow_succ']

lemma Sres_P (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (u : n → ℝ) :
    Sres P β (P *ᵥ u) = P *ᵥ Sres P β u := by
  rw [← (Sres_hasSum_P hP h0 h1 u).tsum_eq]
  unfold Sres
  congr 1; funext k
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_succ, ← pow_succ']

lemma Sres_sub (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (u w : n → ℝ) :
    Sres P β (u - w) = Sres P β u - Sres P β w := by
  unfold Sres
  rw [← (Sres_summable hP h0 h1 u).tsum_sub (Sres_summable hP h0 h1 w)]
  congr 1; funext k
  rw [Matrix.mulVec_sub, smul_sub]

lemma Sres_fix (hP : IsMarkovMatrix P) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {u : n → ℝ}
    (hu : P *ᵥ u = u) : Sres P β u = (1 - β)⁻¹ • u := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ u = u := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hu, ih]
  unfold Sres
  simp_rw [hk]
  rw [(summable_geometric_of_lt_one h0 h1).tsum_smul_const, tsum_geometric_of_lt_one h0 h1]

/-- Laurent expansion (Blackwell Theorem 4(a), third part), vector form. -/
lemma laurent_vec (hP : IsMarkovMatrix P) (r : n → ℝ) :
    Tendsto (fun β : ℝ => Sres P β r - (1 - β)⁻¹ • (limitMatrix P *ᵥ r) - deviationMatrix P *ᵥ r)
      (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨-, hQP, hPQ, hQQ⟩ := limit_props hP
  obtain ⟨hQH, -, h1H, -⟩ := dev_props hP
  set Q := limitMatrix P
  set H := deviationMatrix P
  set x := Q *ᵥ r
  set y := H *ᵥ r
  set u := H *ᵥ y
  have hx : P *ᵥ x = x := by simp only [x, Matrix.mulVec_mulVec, hPQ]
  have hr : r = x + (y - P *ᵥ y) := by
    have : (1 - P) *ᵥ y = r - x := by
      simp only [y, x, Matrix.mulVec_mulVec, h1H, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    rw [this]; abel
  have hQy : Q *ᵥ y = 0 := by simp only [y, Matrix.mulVec_mulVec, hQH, Matrix.zero_mulVec]
  have hyu : y = u - P *ᵥ u := by
    have : (1 - P) *ᵥ u = y - Q *ᵥ y := by
      simp only [u, Matrix.mulVec_mulVec, h1H, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hQy, sub_zero, Matrix.sub_mulVec, Matrix.one_mulVec] at this
    exact this.symm
  set C := ‖y‖ + 2 * ‖u‖
  have hev : ∀ᶠ β in 𝓝[<] (1:ℝ), ‖Sres P β r - (1 - β)⁻¹ • x - y‖ ≤ (1 - β) * C / β ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT (show (1/2 : ℝ) < 1 by norm_num)] with β hβ
    obtain ⟨hb0, hb1⟩ := hβ
    have h0 : 0 ≤ β := by linarith
    have hpos : 0 < 1 - β := by linarith
    have hSr : Sres P β r = (1 - β)⁻¹ • x + (Sres P β y - P *ᵥ Sres P β y) := by
      conv_lhs => rw [hr]
      rw [← Sres_P hP h0 hb1, ← Sres_sub hP h0 hb1, ← Sres_fix hP h0 hb1 hx]
      unfold Sres
      rw [← (Sres_summable hP h0 hb1 x).tsum_add (Sres_summable hP h0 hb1 _)]
      congr 1; funext k; rw [Matrix.mulVec_add, smul_add]
    have hy := Sres_shift hP h0 hb1 y
    have hu := Sres_shift hP h0 hb1 u
    have hy2 : Sres P β y = Sres P β u - P *ᵥ Sres P β u := by
      conv_lhs => rw [hyu]
      rw [Sres_sub hP h0 hb1, Sres_P hP h0 hb1]
    have key : β ^ 2 • (Sres P β r - (1 - β)⁻¹ • x - y) =
        (1 - β) • (β • y - u + (1 - β) • Sres P β u) := by
      rw [hSr]
      linear_combination (norm := module) β • hy + (β ^ 2 - β) • hy2 - (1 - β) • hu
    have hb2 : 0 < β ^ 2 := by positivity
    have hnorm : β ^ 2 * ‖Sres P β r - (1 - β)⁻¹ • x - y‖ ≤ (1 - β) * C := by
      have := congrArg norm key
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb2,
        abs_of_pos hpos] at this
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ hpos.le
      have hSu := Sres_bound hP h0 hb1 u
      calc ‖β • y - u + (1 - β) • Sres P β u‖ ≤ ‖β • y‖ + ‖u‖ + ‖(1 - β) • Sres P β u‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ ≤ ‖y‖ + ‖u‖ + ‖u‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos,
              abs_of_nonneg h0]
            gcongr
            nlinarith [norm_nonneg y]
        _ = C := by ring
    rw [le_div_iff₀ hb2, mul_comm]; exact hnorm
  have hlim : Tendsto (fun β : ℝ => (1 - β) * C / β ^ 2) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun β : ℝ => (1 - β) * C / β ^ 2) (𝓝 1) (𝓝 ((1 - 1) * C / 1 ^ 2)) :=
      ((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).div (tendsto_id.pow 2)
        (by norm_num)
    simp only [sub_self, zero_mul, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm' hev hlim

end Laurent

section Key
variable {St Act : Type*} [Fintype St] [DecidableEq St]

lemma V_stat (M : Model St Act) (f : St → Act) (β : ℝ) :
    M.V β (Policy.stationary f) = Sres (M.Q f) β (M.r f) := by
  unfold Model.V Sres
  simp_rw [Qn_stat]
  rfl

lemma laurent (M : Model St Act) (f : St → Act) (s : St) :
    Tendsto (fun β : ℝ => M.V β (Policy.stationary f) s - (1 - β)⁻¹ * M.x f s - M.y f s)
      (𝓝[<] 1) (𝓝 0) := by
  have h := tendsto_pi_nhds.1 (laurent_vec (markovQ M f) (M.r f)) s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  simp only [V_stat]
  exact h

theorem key_of [Nonempty St] [Fintype Act] [Nonempty Act] (M : Model St Act)
    (h4b : ∀ f g : St → Act, (∃ s, g s ∈ M.gainBiasImprovementSet f s) →
      (∀ s, g s ∉ M.gainBiasImprovementSet f s → g s = f s) →
      ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
        VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)))
    (h4e : ∀ f₀ : St → Act, (∀ s, M.gainBiasImprovementSet f₀ s = ∅) →
      (∀ g : St → Act, M.x g ≤ M.x f₀) ∧
      ∃ fstar : St → Act, M.x fstar = M.x f₀ ∧
        (∀ g : St → Act, M.x g = M.x f₀ → M.y g ≤ M.y fstar) ∧
        ∀ g : St → Act,
          (M.IsNearlyOptimal (Policy.stationary g) ↔ M.x g = M.x fstar ∧ M.y g = M.y fstar))
    (f : St → Act) (hf : f ∈ VeinottNoDiscount.Improve.Fdprime M) (g : St → Act) (s : St)
    (hs : M.x g s = M.x f s) : M.y g s ≤ M.y f s := by
  classical
  let R : (St → Act) → (St → Act) → Prop := fun a b => ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
    VecGt (M.V β (Policy.stationary a)) (M.V β (Policy.stationary b))
  have hirr : ∀ a, ¬ R a a := by
    rintro a ⟨β₀, hβ₀, h⟩
    exact (h ((β₀ + 1) / 2) (by linarith) (by linarith)).2 rfl
  have htr : ∀ a b c, R a b → R b c → R a c := by
    rintro a b c ⟨β₁, hβ₁, h1⟩ ⟨β₂, hβ₂, h2⟩
    refine ⟨max β₁ β₂, max_lt hβ₁ hβ₂, fun β hβ hβ1 => ?_⟩
    obtain ⟨hab, hne⟩ := h1 β (lt_of_le_of_lt (le_max_left _ _) hβ) hβ1
    obtain ⟨hbc, -⟩ := h2 β (lt_of_le_of_lt (le_max_right _ _) hβ) hβ1
    refine ⟨hbc.trans hab, fun heq => hne (le_antisymm ?_ hab)⟩
    rw [heq]; exact hbc
  have : IsTrans (St → Act) R := ⟨htr⟩
  have : Std.Irrefl R := ⟨hirr⟩
  have wf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  obtain ⟨f₀, -, hmax⟩ := wf.has_min Set.univ ⟨f, trivial⟩
  have hG0 : ∀ s, M.gainBiasImprovementSet f₀ s = ∅ := by
    by_contra hne
    obtain ⟨s0, hs0⟩ := not_forall.1 hne
    have hs0' : (M.gainBiasImprovementSet f₀ s0).Nonempty := Set.nonempty_iff_ne_empty.2 hs0
    let g' : St → Act := fun s =>
      if h : (M.gainBiasImprovementSet f₀ s).Nonempty then h.some else f₀ s
    have hR : R g' f₀ := h4b f₀ g' ⟨s0, by simp only [g', dif_pos hs0']; exact hs0'.some_mem⟩
      (fun s hs => by
        by_cases h : (M.gainBiasImprovementSet f₀ s).Nonempty
        · exact absurd (by simp only [g', dif_pos h]; exact h.some_mem) hs
        · simp only [g', dif_neg h])
    exact hmax g' trivial hR
  obtain ⟨hx, fstar, hxs, hy, hno⟩ := h4e f₀ hG0
  have hNO : M.IsNearlyOptimal (Policy.stationary fstar) := (hno fstar).2 ⟨rfl, rfl⟩
  have hfsF' : fstar ∈ VeinottNoDiscount.Improve.Fprime M := fun g => hxs ▸ hx g
  have hxf : M.x f = M.x fstar := le_antisymm (hxs ▸ hx f) (hf.1 fstar)
  have hyle : M.y fstar ≤ M.y f := hf.2 fstar hfsF'
  refine le_trans ?_ (hyle s)
  have hgs : M.x g s = M.x fstar s := by rw [hs, hxf]
  have hd := (laurent M g s).sub (laurent M fstar s)
  rw [sub_zero] at hd
  have hd' : Tendsto (fun β : ℝ => M.V β (Policy.stationary g) s -
      M.V β (Policy.stationary fstar) s) (𝓝[<] 1) (𝓝 (M.y g s - M.y fstar s)) := by
    have := hd.add (tendsto_const_nhds (x := M.y g s - M.y fstar s))
    rw [zero_add] at this
    refine this.congr fun β => ?_
    rw [hgs]; ring
  rw [← sub_nonpos]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨β₀, hβ₀, hb⟩ := hNO ε hε
  have hev : ∀ᶠ β in 𝓝[<] (1:ℝ), M.V β (Policy.stationary g) s -
      M.V β (Policy.stationary fstar) s ≤ ε := by
    filter_upwards [Ioo_mem_nhdsLT hβ₀] with β hβ
    have := hb β hβ.1 hβ.2 (Policy.stationary g) s
    linarith
  have := le_of_tendsto hd' hev
  linarith

end Key

end VT7

end Main

open Filter Topology Matrix BlackwellDiscreteDP.NearOne VeinottNoDiscount.Overtake in
theorem solution {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    f ∈ VeinottNoDiscount.Improve.Fdprime M ↔
      ∀ g : St → Act, ∀ s : St, ∃ L : EReal,
        Tendsto (fun N : ℕ => ((((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            (Vn M (Policy.stationary f) n s - Vn M (Policy.stationary g) n s)) : ℝ) : EReal))
          atTop (𝓝 L) ∧ 0 ≤ L := by
  exact VT7.main_of_key M f (fun hf g s hs =>
    VT7.key_of M (fun f g hG hfix => BlackwellDiscreteDP.NearOne.theorem_4b M f g hG hfix)
      (fun f₀ hG => BlackwellDiscreteDP.NearOne.theorem_4e M f₀ hG) f hf g s hs)
