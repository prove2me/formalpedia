-- Prove2me | solution 1 for RelaxedEqMDP.Discrete.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:37.992107+00:00
-- url     : https://prove2.me/submissions/cf933fd2-8a20-4c9d-b719-274d4537ddba

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_Discretization

open MeasureTheory Filter Topology Matrix

open RelaxedEqMDP
open RelaxedEqMDP.Discrete
open RelaxedEqMDP.Discrete.Supplement

/-- Theorem 5.1, p. 18 (corrected): under Assumptions 3.1, 2.2 (with `q^u_i` for `p^u_i`) and 2.3,
with `f(·,i,u)` and `δ(·)` continuous on `[0,∞)`, take `h_n ∈ (0,1]` with `h_n ↓ 0` such that every
`p_{h_n} = h_n q + 1` is a transition matrix, and (added) the rewards have uniform Riemann tails along
`h_n`.
(a) Given `λ > 0`, if each `π^n ∈ Π_r` is a regular relaxed equilibrium for `J^{h_n,π}_λ` (5.4), with
the discount sampled as `δ(k h_n)`, then along a subsequence the densities of `π^n(i)` converge a.e.
on `U` to the density of some `π^∞(i)`, and `π^∞ ∈ Π_r` is a regular relaxed equilibrium for (3.2).
(b) If each `π^n ∈ Π` is a relaxed equilibrium for `J^{h_n,π}` (5.3), then along a subsequence
`π^n(i) → π^∞(i)` weakly for every `i`, and `π^∞ ∈ Π` is a relaxed equilibrium for (3.1). -/
theorem solution {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (Theta iota vartheta : ℝ) (hS : StandingCT U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (h22 : Assumption22CT U f q Theta)
    (h23 : Assumption23 U iota vartheta)
    (hfc : ∀ i, ∀ u ∈ U, ContinuousOn (fun s => f s i u) (Set.Ici 0))
    (hδc : ContinuousOn δ (Set.Ici 0))
    (h : ℕ → ℝ) (hh : IsLamSeq h) (hph : ∀ n, Standing U (ph q (h n)))
    (htail : UniformRiemannTail U f h) :
    (∀ lam : ℝ, 0 < lam → ∀ pol : ℕ → Control d ℓ,
        (∀ n, IsRegularRelaxedEq U (ph q (h n)) (fh f (h n)) (deltah δ (h n)) (h n * lam)
          (pol n)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ polInf : Control d ℓ, IsRegular U polInf ∧
          (∀ i, ∀ᵐ u ∂(volume.restrict U),
            Tendsto (fun k => density U (pol (φ k) i) u) atTop (𝓝 (density U (polInf i) u))) ∧
          IsRegularRelaxedEqCT U q f δ lam polInf) ∧
      ∀ pol : ℕ → Control d ℓ,
        (∀ n, IsRelaxedEq U (ph q (h n)) (fh f (h n)) (pol n)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ polInf : Control d ℓ, IsRelaxed U polInf ∧
          (∀ i, WeakTendsto (fun k => pol (φ k) i) (polInf i)) ∧
          IsRelaxedEqCT U q f polInf := by
            have L0 : ∀ (d : ℕ) (P : Matrix (Fin d) (Fin d) ℝ), (∀ i j, 0 ≤ P i j) → (∀ i, ∑ j, P i j = 1) →
                ∀ (k : ℕ), (∀ i j, |(P ^ k) i j| ≤ 1) ∧
                ∀ (v : Fin d → ℝ) (c : ℝ) (i : Fin d), (∀ j, |v j| ≤ c) → |((P ^ k) *ᵥ v) i| ≤ c := by
              clear! δ Theta iota vartheta h d ℓ
              intro d P hP0 hP1 k
              have key : ∀ k : ℕ, (∀ i j, 0 ≤ (P ^ k) i j) ∧ ∀ i, ∑ j, (P ^ k) i j = 1 := by
                intro k
                induction k with
                | zero =>
                  refine ⟨fun i j => ?_, fun i => ?_⟩
                  · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
                  · rw [pow_zero]; simp [Matrix.one_apply]
                | succ k ih =>
                  refine ⟨fun i j => ?_, fun i => ?_⟩
                  · rw [pow_succ, Matrix.mul_apply]
                    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih.1 i l) (hP0 l j)
                  · rw [pow_succ]
                    simp only [Matrix.mul_apply]
                    rw [Finset.sum_comm]
                    simp only [← Finset.mul_sum, hP1, mul_one]
                    exact ih.2 i
              obtain ⟨h0, h1⟩ := key k
              refine ⟨fun i j => ?_, fun v c i hv => ?_⟩
              · rw [abs_of_nonneg (h0 i j), ← h1 i]
                exact Finset.single_le_sum (f := fun j => (P ^ k) i j) (fun l _ => h0 i l) (Finset.mem_univ j)
              · have e : ((P ^ k) *ᵥ v) i = ∑ j, (P ^ k) i j * v j := rfl
                rw [e]
                calc |∑ j, (P ^ k) i j * v j| ≤ ∑ j, |(P ^ k) i j * v j| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ j, (P ^ k) i j * c := by
                      refine Finset.sum_le_sum fun j _ => ?_
                      rw [abs_mul, abs_of_nonneg (h0 i j)]
                      exact mul_le_mul_of_nonneg_left (hv j) (h0 i j)
                  _ = c := by rw [← Finset.sum_mul, h1 i, one_mul]
            have L1 : ∀ (d : ℕ) (Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (Qi : Matrix (Fin d) (Fin d) ℝ)
                (h : ℕ → ℝ) (k : ℕ → ℕ) (s : ℝ), Tendsto Q atTop (𝓝 Qi) → Tendsto h atTop (𝓝 0) →
                Tendsto (fun n => (k n : ℝ) * h n) atTop (𝓝 s) →
                Tendsto (fun n => (h n • Q n + 1) ^ (k n)) atTop (𝓝 (NormedSpace.exp (s • Qi))) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0
              have gen : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [NormedAlgebra ℚ E] [CompleteSpace E]
                  (hone : ‖(1 : E)‖ ≤ 1) (Q : ℕ → E) (Qi : E)
                  (h : ℕ → ℝ) (k : ℕ → ℕ) (s : ℝ), Tendsto Q atTop (𝓝 Qi) → Tendsto h atTop (𝓝 0) →
                  Tendsto (fun n => (k n : ℝ) * h n) atTop (𝓝 s) →
                  Tendsto (fun n => (h n • Q n + 1) ^ (k n)) atTop (𝓝 (NormedSpace.exp (s • Qi))) := by
                intro E _ _ _ _ hone Q Qi h k s hQ hh hk
                have tele : ∀ (a b : E) (M : ℝ), 1 ≤ M → ‖a‖ ≤ M → ‖b‖ ≤ M → ∀ m : ℕ,
                    ‖a ^ m - b ^ m‖ ≤ m * M ^ m * ‖a - b‖ := by
                  intro a b M hM ha hb m
                  have hpow : ∀ m : ℕ, ‖a ^ m‖ ≤ M ^ m := by
                    intro m
                    induction m with
                    | zero => rw [pow_zero, pow_zero]; exact hone
                    | succ m ih =>
                      rw [pow_succ, pow_succ]
                      exact (norm_mul_le _ _).trans (mul_le_mul ih ha (norm_nonneg _) (pow_nonneg (zero_le_one.trans hM) m))
                  have hMp : ∀ m : ℕ, 0 ≤ M ^ m := fun m => pow_nonneg (zero_le_one.trans hM) m
                  induction m with
                  | zero => rw [pow_zero, pow_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, zero_mul]
                  | succ m ih =>
                    have e : a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b := by
                      rw [pow_succ, pow_succ, mul_sub, sub_mul, sub_add_sub_cancel]
                    rw [e]
                    have hp2 : 0 ≤ M ^ m * ‖a - b‖ := mul_nonneg (hMp m) (norm_nonneg _)
                    have h1 : ‖a ^ m * (a - b)‖ ≤ M ^ m * ‖a - b‖ :=
                      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hpow m) (norm_nonneg _))
                    have h2 : ‖(a ^ m - b ^ m) * b‖ ≤ (m * M ^ m * ‖a - b‖) * M :=
                      (norm_mul_le _ _).trans (mul_le_mul ih hb (norm_nonneg _) (by rw [mul_assoc]; exact mul_nonneg m.cast_nonneg hp2))
                    have h3 : M ^ m * ‖a - b‖ ≤ M ^ m * ‖a - b‖ * M :=
                      le_mul_of_one_le_right hp2 hM
                    have h4 : ((m + 1 : ℕ) : ℝ) * M ^ (m + 1) * ‖a - b‖
                        = M ^ m * ‖a - b‖ * M + (m * M ^ m * ‖a - b‖) * M := by
                      rw [Nat.cast_succ, pow_succ]; ring
                    rw [h4]
                    exact (norm_add_le _ _).trans (add_le_add (h1.trans h3) h2)
                set x : ℕ → E := fun n => h n • Q n with hx
                have hx0 : Tendsto x atTop (𝓝 0) := by
                  have := hh.smul hQ
                  rw [zero_smul] at this
                  exact this
                have hkx : Tendsto (fun n => (k n : ℝ) • x n) atTop (𝓝 (s • Qi)) := by
                  have := hk.smul hQ
                  refine this.congr fun n => ?_
                  simp only [hx, smul_smul]
                have hlo : (fun n => NormedSpace.exp (x n) - 1 - x n) =o[atTop] x := by
                  have h1 := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := E)).isLittleO
                  have h2 := h1.comp_tendsto hx0
                  refine (h2.congr (fun n => ?_) (fun n => ?_))
                  · simp only [Function.comp_apply, NormedSpace.exp_zero, sub_zero, one_apply_eq_self]
                  · simp only [Function.comp_apply, sub_zero]
                have hlo2 : Tendsto (fun n => (k n : ℝ) • (NormedSpace.exp (x n) - 1 - x n)) atTop (𝓝 0) := by
                  have h1 := (Asymptotics.isBigO_refl (fun n => (k n : ℝ)) atTop).smul_isLittleO hlo
                  have h2 : (fun n => (k n : ℝ) • x n) =O[atTop] (fun _ => (1 : ℝ)) := hkx.isBigO_one ℝ
                  exact (Asymptotics.isLittleO_one_iff ℝ).1 (h1.trans_isBigO h2)
                have hM : Tendsto (fun n => Real.exp (2 * ‖(k n : ℝ) • x n‖)) atTop
                    (𝓝 (Real.exp (2 * ‖s • Qi‖))) :=
                  (Real.continuous_exp.tendsto _).comp (hkx.norm.const_mul 2)
                have hprod : Tendsto (fun n => Real.exp (2 * ‖(k n : ℝ) • x n‖) *
                    ‖(k n : ℝ) • (NormedSpace.exp (x n) - 1 - x n)‖) atTop (𝓝 0) := by
                  have := hM.mul hlo2.norm
                  rw [norm_zero, mul_zero] at this
                  exact this
                have hsmall : ∀ᶠ n in atTop, ‖NormedSpace.exp (x n) - 1 - x n‖ ≤ ‖x n‖ := by
                  have := hlo.bound (one_pos)
                  filter_upwards [this] with n hn
                  rw [one_mul] at hn
                  exact hn
                have hdiff : Tendsto (fun n => (x n + 1) ^ (k n) - NormedSpace.exp (x n) ^ (k n)) atTop (𝓝 0) := by
                  refine squeeze_zero_norm' ?_ hprod
                  filter_upwards [hsmall] with n hn
                  have hb1 : ‖x n + 1‖ ≤ Real.exp (2 * ‖x n‖) := by
                    have h1 := norm_add_le (x n) (1 : E)
                    have h2 := Real.add_one_le_exp (2 * ‖x n‖)
                    have h3 := norm_nonneg (x n)
                    linarith only [h1, h2, h3, hone]
                  have hb2 : ‖NormedSpace.exp (x n)‖ ≤ Real.exp (2 * ‖x n‖) := by
                    have e : NormedSpace.exp (x n) = (NormedSpace.exp (x n) - 1 - x n) + (x n + 1) := by
                      rw [sub_sub, add_comm 1, sub_add_cancel]
                    have h1 := norm_add_le (NormedSpace.exp (x n) - 1 - x n) (x n + 1)
                    rw [← e] at h1
                    have h4 := norm_add_le (x n) (1 : E)
                    have h2 := Real.add_one_le_exp (2 * ‖x n‖)
                    linarith only [h1, h2, h4, hn, hone]
                  have hM1 : 1 ≤ Real.exp (2 * ‖x n‖) := Real.one_le_exp (mul_nonneg zero_le_two (norm_nonneg _))
                  refine (tele _ _ _ hM1 hb1 hb2 (k n)).trans (le_of_eq ?_)
                  have e1 : ‖x n + 1 - NormedSpace.exp (x n)‖ = ‖NormedSpace.exp (x n) - 1 - x n‖ := by
                    rw [← norm_neg, neg_sub, add_comm, sub_sub]
                  have e3 : ‖(k n : ℝ) • x n‖ = (k n : ℝ) * ‖x n‖ := by
                    rw [norm_smul (k n : ℝ) (x n), Real.norm_natCast]
                  have e4 : ‖(k n : ℝ) • (NormedSpace.exp (x n) - 1 - x n)‖
                      = (k n : ℝ) * ‖NormedSpace.exp (x n) - 1 - x n‖ := by
                    rw [norm_smul (k n : ℝ) (NormedSpace.exp (x n) - 1 - x n), Real.norm_natCast]
                  rw [e1, e3, e4, ← Real.exp_nat_mul]
                  have e2 : (k n : ℝ) * (2 * ‖x n‖) = 2 * ((k n : ℝ) * ‖x n‖) := by ring
                  rw [e2]
                  ring
                have hexp : Tendsto (fun n => NormedSpace.exp (x n) ^ (k n)) atTop
                    (𝓝 (NormedSpace.exp (s • Qi))) := by
                  have h1 : Tendsto (fun n => NormedSpace.exp ((k n : ℝ) • x n)) atTop
                      (𝓝 (NormedSpace.exp (s • Qi))) :=
                    (NormedSpace.exp_continuous.tendsto _).comp hkx
                  refine h1.congr fun n => ?_
                  rw [← NormedSpace.exp_nsmul, Nat.cast_smul_eq_nsmul]
                have := hdiff.add hexp
                rw [zero_add] at this
                refine this.congr fun n => ?_
                rw [add_comm (x n) 1, sub_add_cancel, add_comm]
              intro d Q Qi h k s hQ hh hk
              let i1 : NormedRing (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedRing
              let i2 : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedAlgebra
              let i3 : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedAlgebra
              have hone : ‖(1 : Matrix (Fin d) (Fin d) ℝ)‖ ≤ 1 := by
                rcases Nat.eq_zero_or_pos d with hd0 | hd0
                · subst hd0
                  rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) ℝ) 0, norm_zero]
                  exact zero_le_one
                · have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
                  have := Matrix.linfty_opNormOneClass (n := Fin d) (α := ℝ)
                  exact norm_one.le
              have : CompleteSpace (Matrix (Fin d) (Fin d) ℝ) := inferInstance
              exact gen (Matrix (Fin d) (Fin d) ℝ) hone Q Qi h k s hQ hh hk
            have L2 : ∀ (d : ℕ) (Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (Qi : Matrix (Fin d) (Fin d) ℝ)
                (h : ℕ → ℝ), Tendsto Q atTop (𝓝 Qi) → (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
                (∀ n i j, 0 ≤ (h n • Q n + 1) i j) → (∀ n i, ∑ j, (h n • Q n + 1) i j = 1) →
                ∀ (r : ℕ → ℝ → Fin d → ℝ) (ri : ℝ → Fin d → ℝ) (B : ℝ → ℝ),
                (∀ s, 0 ≤ s → 0 ≤ B s) → (∀ T, ∃ C, ∀ s, 0 ≤ s → s ≤ T → B s ≤ C) →
                (∀ n, Summable (fun k : ℕ => B ((k : ℝ) * h n))) →
                (∀ η > 0, ∃ T : ℝ, ∀ n, h n * ∑' k : ℕ,
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => B ((k : ℝ) * h n)) k ≤ η) →
                (∀ n s j, 0 ≤ s → |r n s j| ≤ B s) →
                (∀ j s, 0 ≤ s → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → Tendsto t atTop (𝓝 s) →
                  Tendsto (fun n => r n (t n) j) atTop (𝓝 (ri s j))) →
                (∀ j, ContinuousOn (fun s => ri s j) (Set.Ici 0)) →
                (∀ j, IntegrableOn (fun s => ri s j) (Set.Ioi 0)) →
                (∀ s : ℝ, 0 ≤ s → ∀ i j, |(NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1) ∧
                ∀ i, Tendsto (fun n => ∑' k : ℕ,
                    (((h n • Q n + 1) ^ k) *ᵥ (fun j => h n * r n ((1 + (k : ℝ)) * h n) j)) i) atTop
                  (𝓝 (∫ s in Set.Ioi 0, ((NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ) *ᵥ ri s) i)) := by
              clear! δ Theta iota vartheta h d ℓ
              intro d Q Qi h hQ hpos h0 hP0 hP1 r ri B hB0 hBb hBs hBt hrB hrc hric hrii
              -- the grid index of a time
              have hk : ∀ n s, 0 ≤ s → |((⌈s / h n⌉₊ - 1 : ℕ) : ℝ) * h n - s| ≤ h n := by
                intro n s hs
                have hn := hpos n
                rcases hs.eq_or_lt with hs | hs
                · subst hs
                  rw [zero_div, Nat.ceil_zero, Nat.zero_sub, Nat.cast_zero, zero_mul, sub_zero, abs_zero]
                  exact hn.le
                · have hq : 0 < s / h n := div_pos hs hn
                  have h1 : 1 ≤ ⌈s / h n⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hq).ne'
                  have h2 := Nat.le_ceil (s / h n)
                  have h3 := Nat.ceil_lt_add_one hq.le
                  have h4 : s / h n * h n = s := div_mul_cancel₀ _ hn.ne'
                  rw [Nat.cast_sub h1, Nat.cast_one, abs_le]
                  constructor
                  · have h5 := mul_le_mul_of_nonneg_right h2 hn.le
                    rw [h4] at h5
                    linarith only [h5]
                  · have h5 := mul_lt_mul_of_pos_right h3 hn
                    rw [add_mul, h4] at h5
                    linarith only [h5, hn]
              have hkt : ∀ s, 0 ≤ s → Tendsto (fun n => ((⌈s / h n⌉₊ - 1 : ℕ) : ℝ) * h n) atTop (𝓝 s) := by
                intro s hs
                rw [tendsto_iff_dist_tendsto_zero]
                refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) h0
                rw [Real.dist_eq]; exact hk n s hs
              have hpow : ∀ s : ℝ, 0 ≤ s → Tendsto (fun n => (h n • Q n + 1) ^ (⌈s / h n⌉₊ - 1 : ℕ)) atTop
                  (𝓝 (NormedSpace.exp (s • Qi))) := fun s hs =>
                L1 d Q Qi h (fun n => ⌈s / h n⌉₊ - 1) s hQ h0 (hkt s hs)
              have hexp1 : ∀ s : ℝ, 0 ≤ s → ∀ i j, |(NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1 := by
                intro s hs i j
                have h1 : Tendsto (fun n => ((h n • Q n + 1) ^ (⌈s / h n⌉₊ - 1 : ℕ)) i j) atTop
                    (𝓝 ((NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ) i j)) :=
                  tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hpow s hs) i) j
                exact le_of_tendsto h1.abs (Eventually.of_forall fun n =>
                  (L0 d (h n • Q n + 1) (hP0 n) (hP1 n) _).1 i j)
              refine ⟨hexp1, fun i => ?_⟩
              have hexpc : Continuous (fun s : ℝ => (NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ)) := by
                let _ : NormedRing (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedRing
                let _ : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedAlgebra
                let _ : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
                have hs : Continuous (fun s : ℝ => s • Qi) := continuous_id.smul continuous_const
                exact NormedSpace.exp_continuous.comp hs
              obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ → ℝ, X = fun n s => (((h n • Q n + 1) ^ (⌈s / h n⌉₊ - 1 : ℕ)) *ᵥ
                  (fun j => r n ((1 + ((⌈s / h n⌉₊ - 1 : ℕ) : ℝ)) * h n) j)) i := ⟨_, rfl⟩
              obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun s =>
                  ((NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ) *ᵥ ri s) i := ⟨_, rfl⟩
              obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ → ℝ, a = fun n (k : ℕ) =>
                  (((h n • Q n + 1) ^ k) *ᵥ (fun j => h n * r n ((1 + (k : ℝ)) * h n) j)) i := ⟨_, rfl⟩
              have hXB : ∀ n s, 0 ≤ s → |X n s| ≤ B ((1 + ((⌈s / h n⌉₊ - 1 : ℕ) : ℝ)) * h n) := by
                intro n s hs
                rw [hX]
                refine (L0 d (h n • Q n + 1) (hP0 n) (hP1 n) _).2 _ _ i (fun j => hrB n _ j ?_)
                exact mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) (hpos n).le
              have hXb : ∀ S, ∃ C, 0 ≤ C ∧ ∀ n s, 0 ≤ s → s + h n ≤ S → |X n s| ≤ C := by
                intro S
                obtain ⟨C, hC⟩ := hBb S
                refine ⟨max C 0, le_max_right _ _, fun n s hs hS => le_trans (hXB n s hs) (le_trans (hC _ ?_ ?_) (le_max_left C 0))⟩
                · exact mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) (hpos n).le
                · rcases hs.eq_or_lt with hs | hs
                  · subst hs
                    rw [zero_add] at hS
                    rw [zero_div, Nat.ceil_zero, Nat.zero_sub, Nat.cast_zero, add_zero, one_mul]
                    exact hS
                  · have hn := hpos n
                    have hq : 0 < s / h n := div_pos hs hn
                    have h1 : 1 ≤ ⌈s / h n⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hq).ne'
                    have h3 := Nat.ceil_lt_add_one hq.le
                    have h4 : s / h n * h n = s := div_mul_cancel₀ _ hn.ne'
                    rw [Nat.cast_sub h1, Nat.cast_one]
                    have h5 := mul_lt_mul_of_pos_right h3 hn
                    rw [add_mul, h4] at h5
                    linarith only [h5, hS]
              have hXm : ∀ n, Measurable (X n) := by
                intro n
                have e : X n = (fun k : ℕ => (((h n • Q n + 1) ^ k) *ᵥ
                  (fun j => r n ((1 + (k : ℝ)) * h n) j)) i) ∘ (fun s => ⌈s / h n⌉₊ - 1) := by
                  rw [hX]; rfl
                rw [e]
                refine (measurable_from_nat).comp ?_
                exact (measurable_from_nat (f := fun k : ℕ => k - 1)).comp
                  (Nat.measurable_ceil.comp (measurable_id.div_const _))
              have hXi0 : ∀ n S, 0 ≤ S → IntervalIntegrable (X n) volume 0 S := by
                intro n S hS
                obtain ⟨C, hC0, hC⟩ := hXb (S + h n)
                rw [intervalIntegrable_iff, Set.uIoc_of_le hS]
                refine Measure.integrableOn_of_bounded (M := C) ?_ (hXm n).aestronglyMeasurable ?_
                · exact measure_Ioc_lt_top.ne
                · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
                  rw [Real.norm_eq_abs]
                  exact hC n s hs.1.le (add_le_add_left hs.2 _)
              have hXi : ∀ n u v, 0 ≤ u → 0 ≤ v → IntervalIntegrable (X n) volume u v := fun n u v hu hv =>
                (hXi0 n u hu).symm.trans (hXi0 n v hv)
              have hpiece : ∀ n (k : ℕ), ∫ s in ((k : ℝ) * h n)..(((k + 1 : ℕ) : ℝ) * h n), X n s = a n k := by
                intro n k
                have hn := hpos n
                have e : ∫ s in ((k : ℝ) * h n)..(((k + 1 : ℕ) : ℝ) * h n), X n s =
                    ∫ s in ((k : ℝ) * h n)..(((k + 1 : ℕ) : ℝ) * h n), (((h n • Q n + 1) ^ k) *ᵥ
                  (fun j => r n ((1 + (k : ℝ)) * h n) j)) i := by
                  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
                  rw [Set.uIoc_of_le (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ k)) hn.le)] at hs
                  have hc : ⌈s / h n⌉₊ = k + 1 := by
                    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero k)]
                    constructor
                    · rw [lt_div_iff₀ hn]; exact hs.1
                    · rw [div_le_iff₀ hn]; exact hs.2
                  rw [hX]
                  simp only [hc, Nat.add_sub_cancel]
                rw [e, intervalIntegral.integral_const, ha]
                have e2 : (((k + 1 : ℕ) : ℝ) * h n - (k : ℝ) * h n) = h n := by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_sub_cancel_left]
                rw [e2]
                have e3 : (fun j => h n * r n ((1 + (k : ℝ)) * h n) j) =
                    h n • (fun j => r n ((1 + (k : ℝ)) * h n) j) := rfl
                simp only [e3, Matrix.mulVec_smul, Pi.smul_apply]
              have hsum : ∀ n (N : ℕ), ∑ k ∈ Finset.range N, a n k = ∫ s in (0 : ℝ)..((N : ℝ) * h n), X n s := by
                intro n N
                have := intervalIntegral.sum_integral_adjacent_intervals (f := X n) (μ := volume)
                  (a := fun k : ℕ => (k : ℝ) * h n) (n := N) (fun k _ => hXi n _ _
                    (mul_nonneg (Nat.cast_nonneg _) (hpos n).le) (mul_nonneg (Nat.cast_nonneg _) (hpos n).le))
                simp only [Nat.cast_zero, zero_mul] at this
                rw [← this]
                exact Finset.sum_congr rfl fun k _ => (hpiece n k).symm
              have hab : ∀ n k, |a n k| ≤ h n * B (((k + 1 : ℕ) : ℝ) * h n) := by
                intro n k
                have hn := hpos n
                rw [ha]
                refine (L0 d (h n • Q n + 1) (hP0 n) (hP1 n) k).2 _ _ i (fun j => ?_)
                rw [abs_mul, abs_of_pos hn]
                have e : (((k + 1 : ℕ) : ℝ) * h n) = (1 + (k : ℝ)) * h n := by rw [Nat.cast_add, Nat.cast_one, add_comm]
                rw [e]
                exact mul_le_mul_of_nonneg_left (hrB n _ j (mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) hn.le)) hn.le
              have hBs1 : ∀ n, Summable (fun k : ℕ => h n * B (((k + 1 : ℕ) : ℝ) * h n)) := fun n =>
                ((summable_nat_add_iff (f := fun k : ℕ => B ((k : ℝ) * h n)) 1).mpr (hBs n)).mul_left _
              have has : ∀ n, Summable (a n) := fun n =>
                Summable.of_norm_bounded (hBs1 n) (fun k => by rw [Real.norm_eq_abs]; exact hab n k)
              have htail : ∀ n T (N : ℕ) η, T ≤ (N : ℝ) * h n → h n * ∑' k : ℕ,
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => B ((k : ℝ) * h n)) k ≤ η →
                  |∑' k, a n (k + N)| ≤ η := by
                intro n T N η hT hη
                have hn := hpos n
                obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, I = fun k =>
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => B ((k : ℝ) * h n)) k := ⟨_, rfl⟩
                have hBn : ∀ k : ℕ, 0 ≤ B ((k : ℝ) * h n) := fun k => hB0 _ (mul_nonneg (Nat.cast_nonneg _) hn.le)
                have hI0 : ∀ k, 0 ≤ I k := fun k => by
                  rw [hI]; exact Set.indicator_nonneg (fun k _ => hBn k) k
                have hIs : Summable I := by rw [hI]; exact (hBs n).indicator _
                have hI1 : ∑' k, I (k + (N + 1)) ≤ ∑' k, I k := by
                  rw [← hIs.sum_add_tsum_nat_add (N + 1)]
                  have := Finset.sum_nonneg (s := Finset.range (N + 1)) fun k _ => hI0 k
                  exact le_add_of_nonneg_left this
                have hIs' : Summable fun k => I (k + (N + 1)) := (summable_nat_add_iff (N + 1)).mpr hIs
                have hb : ∀ k, ‖a n (k + N)‖ ≤ h n * I (k + (N + 1)) := by
                  intro k
                  rw [Real.norm_eq_abs]
                  refine (hab n (k + N)).trans (le_of_eq ?_)
                  rw [hI]
                  have hm : k + (N + 1) ∈ {k : ℕ | T ≤ (k : ℝ) * h n} := by
                    simp only [Set.mem_ofPred_eq]
                    refine hT.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?_) hn.le)
                    exact (Nat.le_succ N).trans (Nat.le_add_left _ _)
                  simp only [Set.indicator_of_mem hm, Nat.add_assoc]
                have h1 := tsum_of_norm_bounded ((hIs'.mul_left (h n)).hasSum) hb
                rw [Real.norm_eq_abs, tsum_mul_left] at h1
                refine h1.trans ((mul_le_mul_of_nonneg_left hI1 hn.le).trans ?_)
                rw [hI]; exact hη
              have hXG : ∀ s, 0 ≤ s → Tendsto (fun n => X n s) atTop (𝓝 (G s)) := by
                intro s hs
                rw [hX, hG]
                simp only [Matrix.mulVec, dotProduct]
                refine tendsto_finsetSum Finset.univ fun j _ => ?_
                have hA : Tendsto (fun n => ((h n • Q n + 1) ^ (⌈s / h n⌉₊ - 1 : ℕ)) i j) atTop
                    (𝓝 ((NormedSpace.exp (s • Qi) : Matrix (Fin d) (Fin d) ℝ) i j)) :=
                  tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hpow s hs) i) j
                have hB : Tendsto (fun n => r n ((1 + ((⌈s / h n⌉₊ - 1 : ℕ) : ℝ)) * h n) j) atTop
                    (𝓝 (ri s j)) := by
                  refine hrc j s hs (fun n => (1 + ((⌈s / h n⌉₊ - 1 : ℕ) : ℝ)) * h n) (fun n => ?_) ?_
                  · exact mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) (hpos n).le
                  · have := h0.add (hkt s hs)
                    rw [zero_add] at this
                    refine this.congr fun n => ?_
                    rw [add_mul, one_mul]
                exact hA.mul hB
              have hGc : ContinuousOn G (Set.Ici 0) := by
                rw [hG]
                simp only [Matrix.mulVec, dotProduct]
                refine continuousOn_finsetSum _ fun j _ => ContinuousOn.mul ?_ (hric j)
                exact ((continuous_apply j).comp ((continuous_apply i).comp hexpc)).continuousOn
              have hGi : IntegrableOn G (Set.Ioi 0) := by
                have hb : IntegrableOn (fun s => ∑ j, |ri s j|) (Set.Ioi 0) :=
                  integrable_finsetSum _ fun j _ => (hrii j).abs
                refine Integrable.mono' hb
                  ((hGc.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
                refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
                rw [Real.norm_eq_abs, hG]
                simp only [Matrix.mulVec, dotProduct]
                refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
                rw [abs_mul]
                exact mul_le_of_le_one_left (abs_nonneg _) (hexp1 s (le_of_lt hs) i j)
              have hXint : ∀ T, 0 ≤ T → Tendsto (fun n => ∫ s in (0 : ℝ)..T, X n s) atTop
                  (𝓝 (∫ s in (0 : ℝ)..T, G s)) := by
                intro T hT
                obtain ⟨C, hC0, hC⟩ := hXb (T + 1)
                have hev : ∀ᶠ n in atTop, h n ≤ 1 := h0.eventually (ge_mem_nhds one_pos)
                refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
                  (Eventually.of_forall fun n => (hXm n).aestronglyMeasurable) ?_ intervalIntegrable_const ?_
                · filter_upwards [hev] with n hn
                  refine Eventually.of_forall fun s hs => ?_
                  rw [Set.uIoc_of_le hT] at hs
                  rw [Real.norm_eq_abs]
                  exact hC n s hs.1.le (add_le_add hs.2 hn)
                · refine Eventually.of_forall fun s hs => ?_
                  rw [Set.uIoc_of_le hT] at hs
                  exact hXG s hs.1.le
              have hGT : Tendsto (fun T : ℝ => ∫ s in (0 : ℝ)..T, G s) atTop (𝓝 (∫ s in Set.Ioi 0, G s)) :=
                intervalIntegral_tendsto_integral_Ioi 0 hGi tendsto_id
              have key : Tendsto (fun n => ∑' k, a n k) atTop (𝓝 (∫ s in Set.Ioi 0, G s)) := by
                rw [Metric.tendsto_atTop']
                intro ε hε
                have hε4 : 0 < ε / 4 := div_pos hε four_pos
                obtain ⟨T1, hT1⟩ := hBt (ε / 4) hε4
                obtain ⟨T, hT0, hTT, hTG⟩ : ∃ T, 0 ≤ T ∧ T1 ≤ T ∧
                    |(∫ s in (0 : ℝ)..T, G s) - ∫ s in Set.Ioi 0, G s| < ε / 4 := by
                  have e1 := (Metric.tendsto_nhds.mp hGT) (ε / 4) hε4
                  obtain ⟨T, h1, h2, h3⟩ := (e1.and ((eventually_ge_atTop 0).and (eventually_ge_atTop T1))).exists
                  exact ⟨T, h2, h3, by rwa [Real.dist_eq] at h1⟩
                obtain ⟨C, hC0, hC⟩ := hXb (T + 2)
                have ev1 : ∀ᶠ n in atTop, h n ≤ 1 := h0.eventually (ge_mem_nhds one_pos)
                have ev2 : ∀ᶠ n in atTop, C * h n < ε / 4 := by
                  have : Tendsto (fun n => C * h n) atTop (𝓝 0) := by
                    have := h0.const_mul C
                    rwa [mul_zero] at this
                  exact this.eventually (gt_mem_nhds hε4)
                have ev3 := (Metric.tendsto_nhds.mp (hXint T hT0)) (ε / 4) hε4
                obtain ⟨n0, hn0⟩ := eventually_atTop.mp (ev1.and (ev2.and ev3))
                refine ⟨n0, fun n hn => ?_⟩
                obtain ⟨h1, h2, h3⟩ := hn0 n (le_of_lt hn)
                have hn := hpos n
                have hN1 : T ≤ (⌈T / h n⌉₊ : ℝ) * h n := by
                  rw [← div_le_iff₀ hn]; exact Nat.le_ceil _
                have hN2 : (⌈T / h n⌉₊ : ℝ) * h n ≤ T + h n := by
                  have e1 := Nat.ceil_lt_add_one (div_nonneg hT0 hn.le)
                  have e2 : T / h n * h n = T := div_mul_cancel₀ _ hn.ne'
                  have e3 := mul_lt_mul_of_pos_right e1 hn
                  rw [add_mul, e2, one_mul] at e3
                  exact e3.le
                generalize ⌈T / h n⌉₊ = N at hN1 hN2
                have t1 := htail n T1 N (ε / 4) (hTT.trans hN1) (hT1 n)
                have t2 := (has n).sum_add_tsum_nat_add N
                have t3 := hsum n N
                have t4 := intervalIntegral.integral_add_adjacent_intervals
                  (hXi n 0 T le_rfl hT0) (hXi n T ((N : ℝ) * h n) hT0 (hT0.trans hN1))
                have t5 : |∫ s in T..((N : ℝ) * h n), X n s| ≤ C * h n := by
                  have hb2 : (N : ℝ) * h n + h n ≤ T + 2 := by linarith only [hN2, h1]
                  have := intervalIntegral.norm_integral_le_of_norm_le_const (f := X n) (a := T)
                    (b := (N : ℝ) * h n) (C := C) (fun s hs => by
                      rw [Set.uIoc_of_le hN1] at hs
                      rw [Real.norm_eq_abs]
                      exact hC n s (hT0.trans hs.1.le) ((add_le_add_left hs.2 _).trans hb2))
                  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hN1)] at this
                  exact this.trans (mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mpr hN2) hC0)
                rw [Real.dist_eq, abs_lt] at h3
                rw [Real.dist_eq, abs_lt]
                have u1 := abs_lt.mp hTG
                have u2 := abs_le.mp t1
                have u3 := abs_le.mp t5
                rw [← t2, t3, ← t4]
                exact ⟨by linarith only [h3.1, u1.1, u2.1, u3.1, h2], by linarith only [h3.2, u1.2, u2.2, u3.2, h2]⟩
              rw [ha, hG] at key
              exact key
            have L3 : ∀ (δ : ℝ → ℝ), IsDiscountCT δ → IntegrableOn δ (Set.Ici 0) →
                ∀ (h : ℕ → ℝ), (∀ n, 0 < h n ∧ h n ≤ 1) →
                (∀ n, Summable (fun k : ℕ => δ ((k : ℝ) * h n))) ∧
                (∀ η > 0, ∃ T : ℝ, ∀ n, h n * ∑' k : ℕ,
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => δ ((k : ℝ) * h n)) k ≤ η) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2
              intro δ hδ hint h hh
              have hanti : AntitoneOn δ (Set.Ici 0) := hδ.anti
              have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable δ volume a b := by
                intro a b ha hab
                rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
                exact hint.mono_set (fun x hx => ha.trans hx.1.le)
              -- one step
              have hstep : ∀ x s : ℝ, 0 ≤ x → 0 < s → s * δ (x + s) ≤ ∫ t in x..(x + s), δ t := by
                intro x s hx hs
                have hle : x ≤ x + s := le_add_of_nonneg_right hs.le
                have h1 : ∫ t in x..(x + s), δ (x + s) ≤ ∫ t in x..(x + s), δ t := by
                  refine intervalIntegral.integral_mono_on hle intervalIntegrable_const (hII _ _ hx hle) ?_
                  intro t ht
                  exact hanti (hx.trans ht.1) (Set.mem_Ici.2 (add_nonneg hx hs.le)) ht.2
                rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] at h1
                exact h1
              -- partial sums
              have hpart : ∀ x s : ℝ, 0 ≤ x → 0 < s → ∀ m : ℕ,
                  s * ∑ k ∈ Finset.range m, δ (x + ((k : ℝ) + 1) * s) ≤ ∫ t in x..(x + m * s), δ t := by
                intro x s hx hs m
                induction m with
                | zero =>
                  rw [Finset.sum_range_zero, mul_zero, Nat.cast_zero, zero_mul, add_zero, intervalIntegral.integral_same]
                | succ m ih =>
                  rw [Finset.sum_range_succ, mul_add]
                  have hms : 0 ≤ (m : ℝ) * s := mul_nonneg m.cast_nonneg hs.le
                  have hxm : 0 ≤ x + m * s := add_nonneg hx hms
                  have e := hstep (x + m * s) s hxm hs
                  have e1 : x + m * s + s = x + ((m : ℝ) + 1) * s := by ring
                  have i1 := hII x (x + m * s) hx (le_add_of_nonneg_right hms)
                  have i2 := hII (x + m * s) (x + m * s + s) hxm (le_add_of_nonneg_right hs.le)
                  rw [e1] at e i2
                  have hadd := intervalIntegral.integral_add_adjacent_intervals i1 i2
                  rw [Nat.cast_succ, ← hadd]
                  exact add_le_add ih e
              -- bound by the tail integral
              have hbound : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ∫ t in x..y, δ t ≤ ∫ t in Set.Ioi x, δ t := by
                intro x y hx hxy
                rw [intervalIntegral.integral_of_le hxy]
                refine setIntegral_mono_set (hint.mono_set (fun t ht => hx.trans (le_of_lt ht))) ?_ ?_
                · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
                  exact hδ.nonneg t (hx.trans (le_of_lt ht))
                · exact Filter.Eventually.of_forall (fun t ht => ht.1)
              have hsum : ∀ n, Summable (fun k : ℕ => δ ((k : ℝ) * h n)) := by
                intro n
                have h0 := (hh n).1
                have hkn : ∀ k : ℕ, 0 ≤ (k : ℝ) * h n := fun k => mul_nonneg k.cast_nonneg h0.le
                rw [← summable_nat_add_iff 1]
                refine summable_of_sum_range_le (f := fun k : ℕ => δ (((k + 1 : ℕ) : ℝ) * h n)) (c := (∫ t in Set.Ioi 0, δ t) / h n) ?_ ?_
                · intro k
                  exact hδ.nonneg _ (hkn _)
                · intro m
                  rw [le_div_iff₀ h0, mul_comm]
                  have e := hpart 0 (h n) le_rfl h0 m
                  have e' := hbound 0 (0 + m * h n) le_rfl (add_nonneg le_rfl (hkn m))
                  refine le_trans (le_of_eq ?_) (e.trans e')
                  simp only [zero_add, Nat.cast_succ]
              refine ⟨hsum, ?_⟩
              intro η hη
              have htl : Tendsto (fun x : ℝ => ∫ t in Set.Ioi x, δ t) atTop (𝓝 0) := by
                have hi : IntegrableOn δ (Set.Ioi 0) := hint.mono_set Set.Ioi_subset_Ici_self
                have e := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
                have e2 : Tendsto (fun x : ℝ => (∫ t in Set.Ioi 0, δ t) - ∫ t in (0:ℝ)..x, δ t) atTop (𝓝 0) := by
                  have := e.const_sub (∫ t in Set.Ioi 0, δ t)
                  rw [sub_self] at this
                  exact this
                refine e2.congr' ?_
                filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
                have hi2 : IntegrableOn δ (Set.Ioi x) := hi.mono_set (Set.Ioi_subset_Ioi hx)
                have := intervalIntegral.integral_interval_add_Ioi hi hi2
                rw [← this, add_sub_cancel_left]
              obtain ⟨X, hX⟩ := (htl.eventually (ge_mem_nhds hη)).exists_forall_of_atTop
              set x0 : ℝ := max X 0 with hx0
              have hx0n : 0 ≤ x0 := le_max_right _ _
              refine ⟨x0 + 1, fun n => ?_⟩
              obtain ⟨h0, h1⟩ := hh n
              have hI := hX x0 (le_max_left _ _)
              have hkn : ∀ k : ℕ, 0 ≤ (k : ℝ) * h n := fun k => mul_nonneg k.cast_nonneg h0.le
              -- first grid index past x0
              set N : ℕ := ⌈x0 / h n⌉₊ with hN
              have hNx : x0 ≤ N * h n := by
                have := Nat.le_ceil (x0 / h n)
                rwa [div_le_iff₀ h0] at this
              have hNx2 : (N : ℝ) * h n < x0 + 1 := by
                have := Nat.ceil_lt_add_one (a := x0 / h n) (div_nonneg hx0n h0.le)
                have h3 := mul_lt_mul_of_pos_right this h0
                rw [add_mul, div_mul_cancel₀ _ h0.ne'] at h3
                exact h3.trans_le (by rw [one_mul]; exact add_le_add le_rfl h1)
              set F : ℕ → ℝ := Set.indicator {k : ℕ | x0 + 1 ≤ (k : ℝ) * h n} (fun k : ℕ => δ ((k : ℝ) * h n)) with hF
              have hF0 : ∀ k, 0 ≤ F k := by
                intro k
                exact Set.indicator_nonneg (fun k _ => hδ.nonneg _ (hkn k)) k
              have hFle : ∀ k, F k ≤ δ ((k : ℝ) * h n) := by
                intro k
                exact Set.indicator_le_self' (fun k _ => hδ.nonneg _ (hkn k)) k
              have hFs : Summable F := (hsum n).indicator _
              have hFz : ∀ k < N + 1, F k = 0 := by
                intro k hk
                refine Set.indicator_of_notMem ?_ _
                intro hm
                have hm' : x0 + 1 ≤ (k : ℝ) * h n := hm
                have : (k : ℝ) ≤ N := Nat.cast_le.mpr (Nat.lt_succ_iff.1 hk)
                have := mul_le_mul_of_nonneg_right this h0.le
                exact absurd (hm'.trans this) (not_le.2 hNx2)
              have hFsum : ∑' k, F k = ∑' k, F (k + (N + 1)) := by
                rw [← hFs.sum_add_tsum_nat_add (N + 1), Finset.sum_eq_zero, zero_add]
                intro k hk
                exact hFz k (Finset.mem_range.1 hk)
              have hle : ∑' k, F (k + (N + 1)) ≤ η / h n := by
                refine Real.tsum_le_of_sum_range_le (fun k => hF0 _) ?_
                intro m
                rw [le_div_iff₀ h0, mul_comm]
                have e := hpart (N * h n) (h n) (hkn N) h0 m
                have e' := hbound (N * h n) (N * h n + m * h n) (hkn N) (le_add_of_nonneg_right (hkn m))
                have e'' := hX (N * h n) ((le_max_left _ _).trans hNx)
                refine le_trans ?_ (e.trans (e'.trans e''))
                refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) h0.le
                refine (hFle _).trans (le_of_eq ?_)
                congr 1
                push_cast; ring
              rw [hFsum]
              have := mul_le_mul_of_nonneg_left hle h0.le
              rwa [mul_div_cancel₀ _ h0.ne'] at this
            have L4 : ∀ (h : ℕ → ℝ), (∀ n, 0 < h n ∧ h n ≤ 1) → ∀ (B : ℝ → ℝ),
                (∀ s, 0 ≤ s → 0 ≤ B s) → (∀ T, ∃ C, ∀ s, 0 ≤ s → s ≤ T → B s ≤ C) →
                (∀ n, Summable (fun k : ℕ => B ((k : ℝ) * h n))) →
                (∀ η > 0, ∃ T : ℝ, ∀ n, h n * ∑' k : ℕ,
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => B ((k : ℝ) * h n)) k ≤ η) →
                ∃ M, ∀ n, h n * ∑' k : ℕ, B ((1 + (k : ℝ)) * h n) ≤ M := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3
              intro h hh B hB0 hBb hsum htail
              obtain ⟨T, hT⟩ := htail 1 one_pos
              obtain ⟨C, hC⟩ := hBb (max T 0)
              have hC0 : 0 ≤ C := (hB0 0 le_rfl).trans (hC 0 le_rfl (le_max_right _ _))
              refine ⟨(max T 0 + 1) * C + 1, fun n => ?_⟩
              obtain ⟨h0, h1⟩ := hh n
              set a : ℕ → ℝ := fun k => B ((k : ℝ) * h n) with ha
              have hkn : ∀ k : ℕ, 0 ≤ (k : ℝ) * h n := fun k => mul_nonneg k.cast_nonneg h0.le
              have hmax : 0 ≤ max T 0 / h n := div_nonneg (le_max_right T 0) h0.le
              have ha0 : ∀ k, 0 ≤ a k := fun k => hB0 _ (hkn k)
              set S : Set ℕ := {k : ℕ | T ≤ (k : ℝ) * h n} with hS
              have hshift : ∑' k : ℕ, B ((1 + (k : ℝ)) * h n) ≤ ∑' k, a k := by
                have e := (hsum n).tsum_eq_zero_add
                have e2 : ∑' k : ℕ, B ((1 + (k : ℝ)) * h n) = ∑' k : ℕ, a (k + 1) := by
                  refine tsum_congr fun k => ?_
                  simp only [ha]
                  congr 1
                  rw [Nat.cast_succ, add_comm (1:ℝ)]
                rw [e2]
                have e3 : ∑' k, a k = a 0 + ∑' k : ℕ, a (k + 1) := e
                rw [e3]
                exact le_add_of_nonneg_left (ha0 0)
              have hsplit : ∑' k, a k = ∑' k, S.indicator a k + ∑' k, Sᶜ.indicator a k := by
                rw [← ((hsum n).indicator S).tsum_add ((hsum n).indicator Sᶜ)]
                refine tsum_congr fun k => ?_
                have := congrFun (Set.indicator_self_add_compl S a) k
                exact this.symm
              set N : ℕ := ⌊max T 0 / h n⌋₊ + 1 with hN
              have hzero : ∀ k ∉ Finset.range N, Sᶜ.indicator a k = 0 := by
                intro k hk
                have hk' : N ≤ k := not_lt.1 fun hl => hk (Finset.mem_range.2 hl)
                refine Set.indicator_of_notMem ?_ _
                intro hmem
                have hmem' : ¬ (T ≤ (k : ℝ) * h n) := hmem
                apply hmem'
                have hlt : max T 0 / h n < N := by
                  have := Nat.lt_floor_add_one (max T 0 / h n)
                  rw [hN, Nat.cast_succ]; exact this
                have : max T 0 / h n < k := hlt.trans_le (Nat.cast_le.mpr hk')
                rw [div_lt_iff₀ h0] at this
                exact (le_max_left _ _).trans this.le
              have hfin : ∑' k, Sᶜ.indicator a k ≤ N * C := by
                rw [tsum_eq_sum hzero]
                have : ∀ k ∈ Finset.range N, Sᶜ.indicator a k ≤ C := by
                  intro k _
                  by_cases hk : k ∈ Sᶜ
                  · rw [Set.indicator_of_mem hk]
                    have hk' : ¬ (T ≤ (k : ℝ) * h n) := hk
                    exact hC _ (hkn k) ((not_le.1 hk').le.trans (le_max_left _ _))
                  · rw [Set.indicator_of_notMem hk]; exact hC0
                have := Finset.sum_le_card_nsmul _ _ _ this
                rw [Finset.card_range, nsmul_eq_mul] at this
                exact this
              have hNh : h n * N ≤ max T 0 + 1 := by
                have h2 : (⌊max T 0 / h n⌋₊ : ℝ) ≤ max T 0 / h n := Nat.floor_le hmax
                have h3 : h n * (⌊max T 0 / h n⌋₊ : ℝ) ≤ max T 0 := by
                  have := mul_le_mul_of_nonneg_left h2 h0.le
                  rwa [mul_div_cancel₀ _ h0.ne'] at this
                rw [hN, Nat.cast_succ, mul_add, mul_one]
                exact add_le_add h3 h1
              have hT' : h n * ∑' k, S.indicator a k ≤ 1 := hT n
              calc h n * ∑' k : ℕ, B ((1 + (k : ℝ)) * h n) ≤ h n * ∑' k, a k := mul_le_mul_of_nonneg_left hshift h0.le
                _ = h n * ∑' k, S.indicator a k + h n * ∑' k, Sᶜ.indicator a k := by rw [hsplit, mul_add]
                _ ≤ 1 + h n * (N * C) := add_le_add hT' (mul_le_mul_of_nonneg_left hfin h0.le)
                _ = 1 + (h n * N) * C := by rw [mul_assoc]
                _ ≤ 1 + (max T 0 + 1) * C := add_le_add le_rfl (mul_le_mul_of_nonneg_right hNh hC0)
                _ = (max T 0 + 1) * C + 1 := add_comm _ _
            have L5 : ∀ (ℓ : ℕ) (U : Set (A ℓ)) (iota vartheta : ℝ), 0 < ℓ → IsCompact U → 0 < volume U →
                Assumption23 U iota vartheta →
                ∀ ε > 0, ∃ C : ℝ, ∀ (L : ℝ) (g : A ℓ → ℝ), 0 ≤ L →
                (∀ u ∈ U, ∀ v ∈ U, |g u - g v| ≤ L * ‖u - v‖) →
                |∫ u in U, (Real.exp (g u) / ∫ v in U, Real.exp (g v)) *
                    Real.log (Real.exp (g u) / ∫ v in U, Real.exp (g v))| ≤ C + ε * L := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4
              intro ℓ U iota vartheta _ hUc hUv hA ε hε
              obtain ⟨hvt, hi0, hi1, hcone⟩ := hA
              have hc0 : 0 ≤ Real.cos iota :=
                Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hi0, Real.pi_pos], hi1⟩
              have hc1 : Real.cos iota < 1 := by
                have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl (0:ℝ)) hi1 hi0
                simpa using this
              obtain ⟨c, hc⟩ : ∃ c, c = Real.cos iota := ⟨_, rfl⟩
              rw [← hc] at hc0 hc1
              obtain ⟨κ, hκ⟩ : ∃ κ, κ = (1 - c) / 2 := ⟨_, rfl⟩
              have hκ0 : 0 < κ := by rw [hκ]; linarith only [hc0, hc1]
              have hκ1 : κ ≤ 1 / 2 := by rw [hκ]; linarith only [hc0, hc1]
              have hκ2 : (1 + κ) * c ≤ 1 - κ := by
                rw [hκ]
                have := mul_self_nonneg (1 - c)
                linarith only [this]
              obtain ⟨s, hs⟩ : ∃ s, s = min ε vartheta / 2 := ⟨_, rfl⟩
              have hmin : 0 < min ε vartheta := lt_min hε hvt
              have hs0 : 0 < s := by rw [hs]; linarith only [hmin]
              have hs1 : (1 + κ) * s < ε := by
                have h1 := min_le_left ε vartheta
                have h2 := mul_le_mul_of_nonneg_right hκ1 hs0.le
                linarith only [h1, hs, h2, hs0]
              have hs2 : (1 + κ) * s < vartheta := by
                have h1 := min_le_right ε vartheta
                have h2 := mul_le_mul_of_nonneg_right hκ1 hs0.le
                linarith only [h1, hs, h2, hs0]
              have hball : ∀ u ∈ U, ∃ w : A ℓ, ∀ v ∈ Metric.closedBall w (κ * s), v ∈ U ∧ ‖v - u‖ ≤ ε := by
                intro u hu
                obtain ⟨a, ha, hcu⟩ := hcone u hu
                refine ⟨u + s • a, fun v hv => ?_⟩
                rw [Metric.mem_closedBall, dist_eq_norm] at hv
                have hsa : ‖s • a‖ = s := by rw [norm_smul, ha, Real.norm_of_nonneg hs0.le, mul_one]
                have e1 : v - u = (v - (u + s • a)) + s • a := by abel
                have n1 : ‖v - u‖ ≤ (1 + κ) * s := by
                  rw [e1]
                  calc _ ≤ ‖v - (u + s • a)‖ + ‖s • a‖ := norm_add_le _ _
                    _ ≤ κ * s + s := by rw [hsa]; exact add_le_add hv le_rfl
                    _ = _ := by ring
                refine ⟨hcu v (lt_of_le_of_lt n1 hs2) ?_, n1.trans hs1.le⟩
                rw [← hc]
                have i1 : inner ℝ (v - u) a = inner ℝ (v - (u + s • a)) a + s := by
                  conv_lhs => rw [e1]
                  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ha]; ring
                have i2 : |inner ℝ (v - (u + s • a)) a| ≤ κ * s := by
                  refine (abs_real_inner_le_norm _ _).trans ?_
                  rw [ha, mul_one]; exact hv
                have i3 := (abs_le.mp i2).1
                rw [i1]
                have : ‖v - u‖ * c ≤ (1 + κ) * s * c := mul_le_mul_of_nonneg_right n1 hc0
                have h5 := mul_le_mul_of_nonneg_right hκ2 hs0.le
                linarith only [this, h5, i3]
              obtain ⟨m, hm⟩ : ∃ m, m = volume.real (Metric.closedBall (0 : A ℓ) (κ * s)) := ⟨_, rfl⟩
              have hm0 : 0 < m := by
                rw [hm]
                exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (mul_pos hκ0 hs0)).ne'
                  (measure_closedBall_lt_top).ne
              have hUm : MeasurableSet U := hUc.isClosed.measurableSet
              have hUfin : volume U ≠ ⊤ := hUc.measure_lt_top.ne
              have hUne : U.Nonempty := nonempty_of_measure_ne_zero hUv.ne'
              refine ⟨|Real.log m| + volume.real U, fun L g hL hg => ?_⟩
              have hgc : ContinuousOn g U := by
                have : LipschitzOnWith L.toNNReal g U := by
                  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
                  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
                  exact hg u hu v hv
                exact this.continuousOn
              have hec : ContinuousOn (fun u => Real.exp (g u)) U := Real.continuous_exp.comp_continuousOn hgc
              have heint : IntegrableOn (fun u => Real.exp (g u)) U := hec.integrableOn_compact hUc
              obtain ⟨us, hus, hmax⟩ := hUc.exists_isMaxOn hUne hgc
              obtain ⟨w, hw⟩ := hball us hus
              obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ v in U, Real.exp (g v) := ⟨_, rfl⟩
              have hZm : m * Real.exp (g us - L * ε) ≤ Z := by
                have h1 : ∫ v in Metric.closedBall w (κ * s), Real.exp (g us - L * ε)
                    ≤ ∫ v in Metric.closedBall w (κ * s), Real.exp (g v) := by
                  refine setIntegral_mono_on (integrableOn_const (measure_closedBall_lt_top).ne)
                    (heint.mono_set fun v hv => (hw v hv).1) Metric.isClosed_closedBall.measurableSet
                    fun v hv => ?_
                  have hv' := hw v hv
                  have := (abs_le.mp (hg us hus v hv'.1)).2
                  have h3 : L * ‖us - v‖ ≤ L * ε := by
                    rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hv'.2 hL
                  exact Real.exp_le_exp.mpr (by linarith only [this, h3])
                have h2 : ∫ v in Metric.closedBall w (κ * s), Real.exp (g v) ≤ Z := by
                  rw [hZ]
                  exact setIntegral_mono_set heint (Eventually.of_forall fun v => (Real.exp_pos _).le)
                    (Eventually.of_forall fun v hv => (hw v hv).1)
                rw [setIntegral_const] at h1
                have h3 : volume.real (Metric.closedBall w (κ * s)) = m := by
                  rw [hm, Measure.real, Measure.real, Measure.addHaar_closedBall_center]
                rw [h3, smul_eq_mul] at h1
                exact h1.trans h2
              have hZ0 : 0 < Z := lt_of_lt_of_le (mul_pos hm0 (Real.exp_pos _)) hZm
              rw [← hZ]
              have hρ0 : ∀ u, 0 < Real.exp (g u) / Z := fun u => div_pos (Real.exp_pos _) hZ0
              have hρint : IntegrableOn (fun u => Real.exp (g u) / Z) U := heint.div_const Z
              have hρ1 : ∫ u in U, Real.exp (g u) / Z = 1 := by
                rw [integral_div, ← hZ, div_self hZ0.ne']
              have hρc : ContinuousOn (fun u => Real.exp (g u) / Z) U := hec.div_const Z
              have hlint : IntegrableOn (fun u => Real.exp (g u) / Z * Real.log (Real.exp (g u) / Z)) U :=
                (hρc.mul (hρc.log fun u _ => (hρ0 u).ne')).integrableOn_compact hUc
              have hlog : ∀ u ∈ U, Real.log (Real.exp (g u) / Z) ≤ L * ε - Real.log m := by
                intro u hu
                rw [Real.log_div (Real.exp_pos _).ne' hZ0.ne', Real.log_exp]
                have h1 := Real.log_le_log (mul_pos hm0 (Real.exp_pos _)) hZm
                rw [Real.log_mul hm0.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
                have h2 : g u ≤ g us := hmax hu
                linarith only [h1, h2]
              have hup : ∫ u in U, Real.exp (g u) / Z * Real.log (Real.exp (g u) / Z)
                  ≤ L * ε - Real.log m := by
                calc _ ≤ ∫ u in U, Real.exp (g u) / Z * (L * ε - Real.log m) :=
                      setIntegral_mono_on hlint (hρint.mul_const _) hUm
                        fun u hu => mul_le_mul_of_nonneg_left (hlog u hu) (hρ0 u).le
                  _ = _ := by rw [integral_mul_const, hρ1, one_mul]
              have hlow : -volume.real U ≤ ∫ u in U, Real.exp (g u) / Z * Real.log (Real.exp (g u) / Z) := by
                calc -volume.real U = ∫ u in U, (-1 : ℝ) := by rw [setIntegral_const]; simp
                  _ ≤ _ := by
                    refine setIntegral_mono_on (integrableOn_const hUfin) hlint hUm fun u _ => ?_
                    have hx := hρ0 u
                    have h1 := Real.one_sub_inv_le_log_of_pos hx
                    have h2 := mul_le_mul_of_nonneg_left h1 hx.le
                    rw [mul_sub, mul_inv_cancel₀ hx.ne'] at h2
                    linarith only [h2, hx]
              have hv0 : 0 ≤ volume.real U := measureReal_nonneg
              have hLε : 0 ≤ ε * L := mul_nonneg (le_of_lt hε) hL
              have ha1 := neg_abs_le (Real.log m)
              have ha2 := abs_nonneg (Real.log m)
              rw [abs_le]
              constructor
              · linarith only [hlow, hLε, ha2]
              · linarith only [hup, ha1, hv0]
            have L6a : ∀ (ℓ : ℕ) (U : Set (A ℓ)), IsCompact U → 0 < volume U →
                ∀ (g : A ℓ → ℝ), ContinuousOn g U → ∀ γ : Measure (A ℓ),
                γ = (volume.restrict U).withDensity
                  (fun u => ENNReal.ofReal (Real.exp (g u) / ∫ v in U, Real.exp (g v))) →
                IsProbabilityMeasure γ ∧ γ Uᶜ = 0 ∧ γ ≪ volume.restrict U ∧
                IntegrableOn (fun u => density U γ u * Real.log (density U γ u)) U ∧
                (∀ᵐ u ∂(volume.restrict U), density U γ u = Real.exp (g u) / ∫ v in U, Real.exp (g v)) ∧
                ent U γ = -∫ u in U, (Real.exp (g u) / ∫ v in U, Real.exp (g v)) *
                    Real.log (Real.exp (g u) / ∫ v in U, Real.exp (g v)) ∧
                (∀ φ : A ℓ → ℝ, ∫ u, φ u ∂γ = ∫ u in U, (Real.exp (g u) / ∫ v in U, Real.exp (g v)) * φ u) ∧
                ∫ u, g u ∂γ + ent U γ = Real.log (∫ v in U, Real.exp (g v)) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5
              intro ℓ U hU hpos g hg γ hγ
              have hUm : MeasurableSet U := hU.measurableSet
              have hfin : IsFiniteMeasure (volume.restrict U) :=
                ⟨by rw [Measure.restrict_apply_univ]; exact hU.measure_lt_top⟩
              have hnz : NeZero (volume.restrict U) :=
                ⟨by rw [Ne, Measure.restrict_eq_zero]; exact hpos.ne'⟩
              have hexpc : ContinuousOn (fun u => Real.exp (g u)) U := Real.continuous_exp.comp_continuousOn hg
              have hexpi : IntegrableOn (fun u => Real.exp (g u)) U := hexpc.integrableOn_compact hU
              have hZ : 0 < ∫ v in U, Real.exp (g v) := integral_exp_pos hexpi
              generalize hZdef : (∫ v in U, Real.exp (g v)) = Z at hZ hγ ⊢
              have hρc : ContinuousOn (fun u => Real.exp (g u) / Z) U := hexpc.div_const Z
              have hρi : IntegrableOn (fun u => Real.exp (g u) / Z) U := hρc.integrableOn_compact hU
              have hρpos : ∀ u, 0 < Real.exp (g u) / Z := fun u => div_pos (Real.exp_pos _) hZ
              have hρint : ∫ u in U, Real.exp (g u) / Z = 1 := by
                rw [integral_div, hZdef, div_self hZ.ne']
              have hρm : AEMeasurable (fun u => ENNReal.ofReal (Real.exp (g u) / Z)) (volume.restrict U) :=
                hρi.aemeasurable.ennreal_ofReal
              have hac : γ ≪ volume.restrict U := by rw [hγ]; exact withDensity_absolutelyContinuous _ _
              have hUc : γ Uᶜ = 0 := hac (by rw [Measure.restrict_apply hUm.compl, Set.compl_inter_self]; exact measure_empty)
              have hdens : ∀ᵐ u ∂(volume.restrict U), density U γ u = Real.exp (g u) / Z := by
                have h1 : γ.rnDeriv (volume.restrict U) =ᵐ[volume.restrict U]
                    fun u => ENNReal.ofReal (Real.exp (g u) / Z) := by
                  rw [hγ]; exact Measure.rnDeriv_withDensity₀ _ hρm
                filter_upwards [h1] with u hu
                show (γ.rnDeriv (volume.restrict U) u).toReal = _
                rw [hu, ENNReal.toReal_ofReal (hρpos u).le]
              have hlogc : ContinuousOn (fun u => (Real.exp (g u) / Z) * Real.log (Real.exp (g u) / Z)) U :=
                hρc.mul (hρc.log fun u _ => (hρpos u).ne')
              have hlogi : IntegrableOn (fun u => (Real.exp (g u) / Z) * Real.log (Real.exp (g u) / Z)) U :=
                hlogc.integrableOn_compact hU
              have hdl : (fun u => density U γ u * Real.log (density U γ u)) =ᵐ[volume.restrict U]
                  fun u => (Real.exp (g u) / Z) * Real.log (Real.exp (g u) / Z) := by
                filter_upwards [hdens] with u hu
                rw [hu]
              have hent : ent U γ = -∫ u in U, (Real.exp (g u) / Z) * Real.log (Real.exp (g u) / Z) := by
                show -(∫ u in U, density U γ u * Real.log (density U γ u)) = _
                rw [integral_congr_ae hdl]
              have hint : ∀ φ : A ℓ → ℝ, ∫ u, φ u ∂γ = ∫ u in U, (Real.exp (g u) / Z) * φ u := by
                intro φ
                rw [hγ, integral_withDensity_eq_integral_toReal_smul₀ hρm
                  (Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
                refine integral_congr_ae (Eventually.of_forall fun u => ?_)
                show (ENNReal.ofReal (Real.exp (g u) / Z)).toReal • φ u = _
                rw [ENNReal.toReal_ofReal (hρpos u).le, smul_eq_mul]
              have hgi : IntegrableOn (fun u => (Real.exp (g u) / Z) * g u) U :=
                (hρc.mul hg).integrableOn_compact hU
              have hprob : IsProbabilityMeasure γ := by
                refine ⟨?_⟩
                rw [hγ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
                  ← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall fun u => (hρpos u).le), hρint,
                  ENNReal.ofReal_one]
              refine ⟨hprob, hUc, hac, (integrableOn_congr_fun_ae hdl).2 hlogi, hdens, hent, hint, ?_⟩
              rw [hint, hent, ← sub_eq_add_neg, ← integral_sub hgi hlogi]
              have h2 : ∀ u, (Real.exp (g u) / Z) * g u - (Real.exp (g u) / Z) * Real.log (Real.exp (g u) / Z)
                  = (Real.exp (g u) / Z) * Real.log Z := by
                intro u
                rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]; ring
              simp_rw [h2]
              rw [integral_mul_const, hρint, one_mul]
            have L6b : ∀ (ℓ : ℕ) (U : Set (A ℓ)), IsCompact U → 0 < volume U →
                ∀ (g : A ℓ → ℝ), ContinuousOn g U → ∀ μ : Measure (A ℓ), IsProbabilityMeasure μ →
                μ Uᶜ = 0 → μ ≪ volume.restrict U →
                IntegrableOn (fun u => density U μ u * Real.log (density U μ u)) U →
                ∫ u, g u ∂μ + ent U μ ≤ Real.log (∫ v in U, Real.exp (g v)) ∧
                (Real.log (∫ v in U, Real.exp (g v)) ≤ ∫ u, g u ∂μ + ent U μ →
                  ∀ᵐ u ∂(volume.restrict U), density U μ u = Real.exp (g u) / ∫ v in U, Real.exp (g v)) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5 L6a
              intro ℓ U hU hpos g hg μ hμ hμU hac hlog
              have hUm : MeasurableSet U := hU.measurableSet
              have hfin : IsFiniteMeasure (volume.restrict U) :=
                ⟨by rw [Measure.restrict_apply_univ]; exact hU.measure_lt_top⟩
              have hnz : NeZero (volume.restrict U) :=
                ⟨by rw [Ne, Measure.restrict_eq_zero]; exact hpos.ne'⟩
              have hexpc : ContinuousOn (fun u => Real.exp (g u)) U := Real.continuous_exp.comp_continuousOn hg
              have hexpi : IntegrableOn (fun u => Real.exp (g u)) U := hexpc.integrableOn_compact hU
              have hZ : 0 < ∫ v in U, Real.exp (g v) := integral_exp_pos hexpi
              generalize hZdef : (∫ v in U, Real.exp (g v)) = Z at hZ ⊢
              have hρi : IntegrableOn (fun u => Real.exp (g u) / Z) U := hexpi.div_const Z
              have hρpos : ∀ u, 0 < Real.exp (g u) / Z := fun u => div_pos (Real.exp_pos _) hZ
              have hρint : ∫ u in U, Real.exp (g u) / Z = 1 := by
                rw [integral_div, hZdef, div_self hZ.ne']
              have hd0 : ∀ u, 0 ≤ density U μ u := fun u => ENNReal.toReal_nonneg
              have hdi : IntegrableOn (density U μ) U := Measure.integrable_toReal_rnDeriv
              have hgen : ∀ φ : A ℓ → ℝ, ∫ u, φ u ∂μ = ∫ u in U, density U μ u * φ u := fun φ =>
                (integral_rnDeriv_smul (f := φ) hac).symm
              have hd1 : ∫ u in U, density U μ u = 1 := by
                have h1 := hgen (fun _ => 1)
                simp only [mul_one] at h1
                rw [← h1, integral_const, smul_eq_mul, mul_one]
                exact probReal_univ
              have hgi : IntegrableOn (fun u => density U μ u * g u) U := by
                obtain ⟨C, hC⟩ := hU.exists_bound_of_continuousOn hg
                refine Integrable.mul_bdd (c := C) hdi (hg.aestronglyMeasurable hUm) ?_
                filter_upwards [ae_restrict_mem hUm] with u hu using hC u hu
              have hgint : ∫ u, g u ∂μ = ∫ u in U, density U μ u * g u := hgen g
              have hent : ent U μ = -∫ u in U, density U μ u * Real.log (density U μ u) := rfl
              -- pointwise
              have hpt : ∀ u, 0 ≤ density U μ u * Real.log (density U μ u) - density U μ u * g u
                  + density U μ u * Real.log Z - density U μ u + Real.exp (g u) / Z ∧
                  (density U μ u * Real.log (density U μ u) - density U μ u * g u
                  + density U μ u * Real.log Z - density U μ u + Real.exp (g u) / Z = 0 →
                    density U μ u = Real.exp (g u) / Z) := by
                intro u
                have ha := hd0 u
                have hb := hρpos u
                have hlb : Real.log (Real.exp (g u) / Z) = g u - Real.log Z := by
                  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
                generalize density U μ u = a at ha ⊢
                generalize Real.exp (g u) / Z = b at hb hlb ⊢
                generalize g u = x at hlb ⊢
                have hx : x = Real.log b + Real.log Z := by
                  linarith only [hlb]
                subst hx
                rcases ha.eq_or_lt with h0 | h0
                · subst h0
                  refine ⟨by
                    rw [zero_mul, zero_mul, zero_mul, sub_zero, add_zero, sub_zero, zero_add]; exact hb.le, fun h => ?_⟩
                  rw [zero_mul, zero_mul, zero_mul, sub_zero, add_zero, sub_zero, zero_add] at h
                  exact h.symm
                · have hl : Real.log (b / a) = Real.log b - Real.log a := Real.log_div hb.ne' h0.ne'
                  have key : a * Real.log a - a * (Real.log b + Real.log Z) + a * Real.log Z - a + b
                      = a * (b / a - 1 - Real.log (b / a)) := by
                    have e : a * (b / a) = b := mul_div_cancel₀ b h0.ne'
                    rw [hl, mul_sub, mul_sub, e]; ring
                  rw [key]
                  have hba : 0 < b / a := div_pos hb h0
                  refine ⟨mul_nonneg h0.le (sub_nonneg.2 (Real.log_le_sub_one_of_pos hba)), fun h => ?_⟩
                  by_contra hne
                  have hba1 : b / a ≠ 1 := by
                    intro h1
                    rw [div_eq_one_iff_eq h0.ne'] at h1
                    exact hne h1.symm
                  have hlt := Real.log_lt_sub_one_of_pos hba hba1
                  have : 0 < a * (b / a - 1 - Real.log (b / a)) := mul_pos h0 (sub_pos.2 hlt)
                  exact this.ne' h
              have hi1 : IntegrableOn (fun u => density U μ u * Real.log (density U μ u)
                  - density U μ u * g u) U := hlog.sub hgi
              have hi2 : IntegrableOn (fun u => density U μ u * Real.log (density U μ u)
                  - density U μ u * g u + density U μ u * Real.log Z) U := hi1.add (hdi.mul_const _)
              have hi3 : IntegrableOn (fun u => density U μ u * Real.log (density U μ u)
                  - density U μ u * g u + density U μ u * Real.log Z - density U μ u) U := hi2.sub hdi
              have hi4 : IntegrableOn (fun u => density U μ u * Real.log (density U μ u)
                  - density U μ u * g u + density U μ u * Real.log Z - density U μ u
                  + Real.exp (g u) / Z) U := hi3.add hρi
              have hval : ∫ u in U, (density U μ u * Real.log (density U μ u)
                  - density U μ u * g u + density U μ u * Real.log Z - density U μ u
                  + Real.exp (g u) / Z) = Real.log Z - (∫ u, g u ∂μ + ent U μ) := by
                rw [integral_add hi3 hρi, integral_sub hi2 hdi, integral_add hi1 (hdi.mul_const _),
                  integral_sub hlog hgi, integral_mul_const, hd1, hρint, hgint, hent]
                ring
              have hnn : 0 ≤ ∫ u in U, (density U μ u * Real.log (density U μ u)
                  - density U μ u * g u + density U μ u * Real.log Z - density U μ u
                  + Real.exp (g u) / Z) := integral_nonneg fun u => (hpt u).1
              rw [hval] at hnn
              refine ⟨sub_nonneg.1 hnn, fun hle => ?_⟩
              have hz : ∫ u in U, (density U μ u * Real.log (density U μ u)
                  - density U μ u * g u + density U μ u * Real.log Z - density U μ u
                  + Real.exp (g u) / Z) = 0 := by
                rw [hval]; exact le_antisymm (sub_nonpos.2 hle) hnn
              have hae := (integral_eq_zero_iff_of_nonneg (fun u => (hpt u).1) hi4).1 hz
              filter_upwards [hae] with u hu
              exact (hpt u).2 hu
            have L7 : ∀ (d ℓ : ℕ) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (pol pol' : Control d ℓ)
                (r : ℕ → Control d ℓ → Fin d → ℝ) (i : Fin d),
                (∀ j, Summable (fun k : ℕ => ((Pbar p pol ^ k) *ᵥ r (k + 1) pol) j)) →
                seqValue p (concat pol' pol) r i = r 0 pol' i +
                  ∑ j, Pbar p pol' i j * ∑' k : ℕ, ((Pbar p pol ^ k) *ᵥ r (k + 1) pol) j := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5 L6a L6b
              intro d ℓ p pol pol' r i hs
              have hterm : ∀ k : ℕ, ((List.ofFn (fun m : Fin (k + 1) => Pbar p (concat pol' pol m))).prod *ᵥ
                  r (k + 1) (concat pol' pol (k + 1))) i =
                  ∑ j, Pbar p pol' i j * ((Pbar p pol ^ k) *ᵥ r (k + 1) pol) j := by
                intro k
                have e1 : (List.ofFn (fun m : Fin (k + 1) => Pbar p (concat pol' pol m))).prod =
                    Pbar p pol' * Pbar p pol ^ k := by
                  rw [List.ofFn_succ, List.prod_cons]
                  have e2 : (fun m : Fin k => Pbar p (concat pol' pol ((Fin.succ m : Fin (k + 1)) : ℕ))) =
                      fun _ => Pbar p pol := by
                    funext m
                    simp [concat]
                  rw [e2, List.ofFn_const, List.prod_replicate]
                  simp [concat]
                have e3 : concat pol' pol (k + 1) = pol := by simp [concat]
                rw [e1, e3, ← Matrix.mulVec_mulVec]
                rfl
              have hs1 : Summable (fun k : ℕ => ∑ j, Pbar p pol' i j * ((Pbar p pol ^ k) *ᵥ r (k + 1) pol) j) :=
                summable_sum fun j _ => (hs j).mul_left _
              have hs2 : Summable (fun k : ℕ => ((List.ofFn (fun m : Fin k => Pbar p (concat pol' pol m))).prod *ᵥ
                  r k (concat pol' pol k)) i) := by
                rw [← summable_nat_add_iff 1]
                exact hs1.congr fun k => (hterm k).symm
              unfold seqValue
              rw [hs2.tsum_eq_zero_add]
              congr 1
              · simp [concat]
              · rw [tsum_congr hterm, Summable.tsum_finsetSum fun j _ => (hs j).mul_left _]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [tsum_mul_left]
            have L8 : ∀ (d : ℕ) (Q Q' : Matrix (Fin d) (Fin d) ℝ) (r r' : ℝ → Fin d → ℝ),
                (∀ j, ContinuousOn (fun s => r s j) (Set.Ici 0)) →
                (∀ j, ContinuousOn (fun s => r' s j) (Set.Ici 0)) →
                (∀ j, IntegrableOn (fun s => r s j) (Set.Ioi 0)) →
                (∀ s, 0 ≤ s → ∀ i j, |(NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1) →
                ∀ (J : Fin d → ℝ) (V : ℝ → Fin d → ℝ),
                (J = fun i => ∫ s in Set.Ioi 0, ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) i) →
                (V = fun t i => ∫ s in Set.Ioi 0,
                  ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r (t + s)) i) →
                ∀ i, r' 0 i + (Q' *ᵥ J) i ≤ r 0 i + (Q *ᵥ J) i →
                ∀ η > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
                  ((∫ s in (0 : ℝ)..ε, ((NormedSpace.exp (s • Q') : Matrix (Fin d) (Fin d) ℝ) *ᵥ r' s) i) +
                    ((NormedSpace.exp (ε • Q') : Matrix (Fin d) (Fin d) ℝ) *ᵥ V ε) i - J i) / ε ≤ η := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5 L6a L6b L7
              intro d Q Q' r r' hr hr' hint hexp J V hJ hV i hineq η hη
              have hder : ∀ M : Matrix (Fin d) (Fin d) ℝ, ∀ a b t,
                  HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • M) : Matrix (Fin d) (Fin d) ℝ) a b)
                    (((NormedSpace.exp (t • M) : Matrix (Fin d) (Fin d) ℝ) * M) a b) t := by
                intro M a b t
                let _ : NormedRing (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedRing
                let _ : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℝ) := Matrix.linftyOpNormedAlgebra
                have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) M t
                let Φ : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] ℝ := Matrix.entryLinearMap ℝ ℝ a b
                let Φc : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
                  { toLinearMap := Φ, cont := (continuous_apply b).comp (continuous_apply a) }
                exact Φc.hasFDerivAt.comp_hasDerivAt t h1
              have hadd : ∀ M : Matrix (Fin d) (Fin d) ℝ, ∀ a b : ℝ,
                  (NormedSpace.exp ((a + b) • M) : Matrix (Fin d) (Fin d) ℝ) =
                    NormedSpace.exp (a • M) * NormedSpace.exp (b • M) := by
                intro M a b
                rw [add_smul]
                exact Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left a).smul_right b)
              have hzero : ∀ M : Matrix (Fin d) (Fin d) ℝ,
                  (NormedSpace.exp ((0 : ℝ) • M) : Matrix (Fin d) (Fin d) ℝ) = 1 := by
                intro M
                rw [zero_smul]
                exact NormedSpace.exp_zero
              have hcont : ∀ M : Matrix (Fin d) (Fin d) ℝ, ∀ a b,
                  Continuous (fun s : ℝ => (NormedSpace.exp (s • M) : Matrix (Fin d) (Fin d) ℝ) a b) := by
                intro M a b
                exact continuous_iff_continuousAt.2 fun t => (hder M a b t).continuousAt
              have hder0 : ∀ M : Matrix (Fin d) (Fin d) ℝ, ∀ a b,
                  HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • M) : Matrix (Fin d) (Fin d) ℝ) a b)
                    (M a b) 0 := by
                intro M a b
                have h1 := hder M a b 0
                rwa [hzero, one_mul] at h1
              have hderneg : ∀ M : Matrix (Fin d) (Fin d) ℝ, ∀ a b,
                  HasDerivAt (fun s : ℝ => (NormedSpace.exp ((-s) • M) : Matrix (Fin d) (Fin d) ℝ) a b)
                    (-M a b) 0 := by
                intro M a b
                have h1 := hder0 (-M) a b
                have e : (fun s : ℝ => (NormedSpace.exp ((-s) • M) : Matrix (Fin d) (Fin d) ℝ) a b) =
                    fun s : ℝ => (NormedSpace.exp (s • (-M)) : Matrix (Fin d) (Fin d) ℝ) a b := by
                  funext s; rw [smul_neg, neg_smul]
                rw [e]
                exact h1
              have hKc : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ → Fin d → ℝ),
                  (∀ j, ContinuousOn (fun s => ρ s j) (Set.Ici 0)) → ∀ l,
                  ContinuousOn (fun s => ((NormedSpace.exp (s • M) : Matrix (Fin d) (Fin d) ℝ) *ᵥ ρ s) l)
                    (Set.Ici 0) := by
                intro M ρ hρ l
                simp only [Matrix.mulVec, dotProduct]
                exact continuousOn_finsetSum _ fun j _ => (hcont M l j).continuousOn.mul (hρ j)
              have hbd : ∀ a b, ∃ C, ∀ s : ℝ, 0 ≤ s →
                  |(NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) a b| ≤ C := by
                intro a b
                have h1 : ∀ l, ∃ C, ∀ x ∈ Set.Icc (0 : ℝ) 1,
                    ‖(NormedSpace.exp (x • Q) : Matrix (Fin d) (Fin d) ℝ) l b‖ ≤ C := fun l =>
                  isCompact_Icc.exists_bound_of_continuousOn (hcont Q l b).continuousOn
                choose C hC using h1
                refine ⟨∑ l, C l, fun s hs => ?_⟩
                have e1 : (NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) =
                    NormedSpace.exp ((⌊s⌋₊ : ℕ) • Q) * NormedSpace.exp ((s - (⌊s⌋₊ : ℝ)) • Q) := by
                  rw [← Nat.cast_smul_eq_nsmul ℝ, ← hadd]; congr 2; ring
                rw [e1, Matrix.mul_apply]
                refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
                rw [abs_mul]
                have h2 := hexp ⌊s⌋₊ (Nat.zero_le _) a l
                have h3 := hC l (s - (⌊s⌋₊ : ℝ)) ⟨sub_nonneg.2 (Nat.floor_le hs),
                  (sub_lt_iff_lt_add'.2 (Nat.lt_floor_add_one s)).le⟩
                rw [Real.norm_eq_abs] at h3
                calc _ ≤ 1 * |(NormedSpace.exp ((s - (⌊s⌋₊ : ℝ)) • Q) : Matrix (Fin d) (Fin d) ℝ) l b| :=
                      mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
                  _ ≤ _ := by rw [one_mul]; exact h3
              have hKi : ∀ l, IntegrableOn
                  (fun s => ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l) (Set.Ioi 0) := by
                intro l
                simp only [Matrix.mulVec, dotProduct]
                refine integrable_finsetSum _ fun j _ => ?_
                obtain ⟨C, hC⟩ := hbd l j
                refine Integrable.bdd_mul (c := C) (hint j) (hcont Q l j).aestronglyMeasurable ?_
                refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_)
                rw [Real.norm_eq_abs]
                exact hC s (le_of_lt hs)
              have hIder : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ → Fin d → ℝ),
                  (∀ j, ContinuousOn (fun s => ρ s j) (Set.Ici 0)) → ∀ l,
                  HasDerivWithinAt (fun ε : ℝ => ∫ s in (0 : ℝ)..ε,
                    ((NormedSpace.exp (s • M) : Matrix (Fin d) (Fin d) ℝ) *ᵥ ρ s) l) (ρ 0 l) (Set.Ici 0) 0 := by
                intro M ρ hρ l
                have hc := hKc M ρ hρ l
                have h1 := intervalIntegral.integral_hasDerivWithinAt_right (a := (0 : ℝ)) (b := (0 : ℝ))
                  (f := fun s => ((NormedSpace.exp (s • M) : Matrix (Fin d) (Fin d) ℝ) *ᵥ ρ s) l)
                  (s := Set.Ici 0) (t := Set.Ioi 0) IntervalIntegrable.refl
                  ((hc.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
                  ((hc 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self)
                rw [hzero, Matrix.one_mulVec] at h1
                exact h1
              -- formula for V
              have hVf : ∀ t, 0 ≤ t → ∀ a, V t a = ∑ l,
                  (NormedSpace.exp ((-t) • Q) : Matrix (Fin d) (Fin d) ℝ) a l *
                    (J l - ∫ s in (0 : ℝ)..t,
                      ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l) := by
                intro t ht a
                have e1 : ∀ s, ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r (t + s)) a =
                    ∑ l, (NormedSpace.exp ((-t) • Q) : Matrix (Fin d) (Fin d) ℝ) a l *
                      ((NormedSpace.exp ((t + s) • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r (t + s)) l := by
                  intro s
                  have e2 : (NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) =
                      NormedSpace.exp ((-t) • Q) * NormedSpace.exp ((t + s) • Q) := by
                    rw [← hadd]; congr 2; ring
                  rw [e2, ← Matrix.mulVec_mulVec]
                  rfl
                have hshift : ∀ l, IntegrableOn (fun s =>
                    ((NormedSpace.exp ((t + s) • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r (t + s)) l) (Set.Ioi 0) ∧
                    ∫ s in Set.Ioi 0,
                      ((NormedSpace.exp ((t + s) • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r (t + s)) l =
                    J l - ∫ s in (0 : ℝ)..t,
                      ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l := by
                  intro l
                  have hpre : (fun s : ℝ => t + s) ⁻¹' (Set.Ioi t) = Set.Ioi 0 := by
                    ext x; exact lt_add_iff_pos_right t
                  have mp := measurePreserving_add_left (volume : Measure ℝ) t
                  have me := measurableEmbedding_addLeft t
                  have hon : IntegrableOn
                      (fun s => ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l) (Set.Ioi t) :=
                    (hKi l).mono_set (Set.Ioi_subset_Ioi ht)
                  refine ⟨?_, ?_⟩
                  · have h1 := (mp.integrableOn_comp_preimage me).2 hon
                    rw [hpre] at h1
                    exact h1
                  · have h1 := mp.setIntegral_preimage_emb me
                      (fun s => ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l) (Set.Ioi t)
                    rw [hpre] at h1
                    rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi (hKi l) ht, hJ]
                    ring
                rw [hV]
                simp only [e1]
                rw [integral_finsetSum _ fun l _ => (hshift l).1.const_mul _]
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [integral_const_mul, (hshift l).2]
              -- the explicit function
              obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun ε =>
                  (∫ s in (0 : ℝ)..ε, ((NormedSpace.exp (s • Q') : Matrix (Fin d) (Fin d) ℝ) *ᵥ r' s) i) +
                  ∑ a, (NormedSpace.exp (ε • Q') : Matrix (Fin d) (Fin d) ℝ) i a * ∑ l,
                  (NormedSpace.exp ((-ε) • Q) : Matrix (Fin d) (Fin d) ℝ) a l *
                    (J l - ∫ s in (0 : ℝ)..ε,
                      ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l) := ⟨_, rfl⟩
              have hone : ∀ (w : Fin d → ℝ) a, ∑ l, (1 : Matrix (Fin d) (Fin d) ℝ) a l * w l = w a := by
                intro w a
                exact congrFun (Matrix.one_mulVec w) a
              have hG0 : G 0 = J i := by
                rw [hG]
                simp only [neg_zero, hzero, intervalIntegral.integral_same, sub_zero, hone, zero_add]
              have hVder : ∀ a, HasDerivWithinAt (fun ε : ℝ => ∑ l,
                  (NormedSpace.exp ((-ε) • Q) : Matrix (Fin d) (Fin d) ℝ) a l *
                    (J l - ∫ s in (0 : ℝ)..ε,
                      ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l))
                  (-(Q *ᵥ J) a - r 0 a) (Set.Ici 0) 0 := by
                intro a
                have h1 : HasDerivWithinAt (fun ε : ℝ => ∑ l,
                  (NormedSpace.exp ((-ε) • Q) : Matrix (Fin d) (Fin d) ℝ) a l *
                    (J l - ∫ s in (0 : ℝ)..ε,
                      ((NormedSpace.exp (s • Q) : Matrix (Fin d) (Fin d) ℝ) *ᵥ r s) l)) _ (Set.Ici 0) 0 :=
                  HasDerivWithinAt.fun_sum (u := Finset.univ) fun l _ =>
                    (hderneg Q a l).hasDerivWithinAt.fun_mul ((hIder Q r hr l).const_sub (J l))
                refine h1.congr_deriv (Eq.symm ?_)
                simp only [neg_zero, hzero, intervalIntegral.integral_same, sub_zero, Finset.sum_add_distrib,
                  hone, Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib, mul_neg]
                ring
              have hGder : HasDerivWithinAt G (r' 0 i + ((Q' *ᵥ J) i + (-(Q *ᵥ J) i - r 0 i)))
                  (Set.Ici 0) 0 := by
                have h1 := (hIder Q' r' hr' i).fun_add (HasDerivWithinAt.fun_sum (u := Finset.univ)
                  fun a _ => (hder0 Q' i a).hasDerivWithinAt.fun_mul (hVder a))
                rw [hG]
                refine h1.congr_deriv (Eq.symm ?_)
                simp only [neg_zero, hzero, intervalIntegral.integral_same, sub_zero, Finset.sum_add_distrib,
                  hone]
                rfl
              have hslope := (hasDerivWithinAt_iff_tendsto_slope' (Set.self_notMem_Ioi)).1
                (hGder.mono Set.Ioi_subset_Ici_self)
              have hlt : r' 0 i + ((Q' *ᵥ J) i + (-(Q *ᵥ J) i - r 0 i)) < η := by
                linarith only [hineq, hη]
              filter_upwards [hslope.eventually_lt_const hlt, self_mem_nhdsWithin] with ε h1 h2
              have h3 : slope G 0 ε = (G ε - J i) / ε := by
                rw [slope_def_field, hG0, sub_zero]
              rw [h3] at h1
              refine le_of_eq_of_le ?_ h1.le
              congr 2
              rw [hG]
              simp only [Matrix.mulVec, dotProduct, add_right_inj]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [hVf ε (le_of_lt h2) a]
              simp only [Matrix.mulVec, dotProduct]
            have L9 : ∀ (d ℓ : ℕ) (U : Set (A ℓ)), IsCompact U → ∀ (pol : ℕ → Control d ℓ),
                (∀ n, IsRelaxed U (pol n)) →
                ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ polInf : Control d ℓ, IsRelaxed U polInf ∧
                  ∀ i, ∀ g : A ℓ → ℝ, ContinuousOn g U →
                    Tendsto (fun k => ∫ u, g u ∂(pol (φ k) i)) atTop (𝓝 (∫ u, g u ∂(polInf i))) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5 L6a L6b L7 L8
              intro d ℓ U hU pol hpol
              have hUm : MeasurableSet U := hU.measurableSet
              haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
              have hres : ∀ n i, (pol n i).restrict U = pol n i := by
                intro n i
                refine Measure.restrict_eq_self_of_ae_mem ?_
                rw [ae_iff]
                exact (hpol n i).2
              have hmap : ∀ n i, Measure.map (Subtype.val : U → A ℓ)
                  (Measure.comap (Subtype.val : U → A ℓ) (pol n i)) = pol n i := by
                intro n i
                rw [map_comap_subtype_coe hUm, hres]
              have hprob : ∀ n i, IsProbabilityMeasure (Measure.comap (Subtype.val : U → A ℓ) (pol n i)) := by
                intro n i
                haveI := (hpol n i).1
                constructor
                have h1 : Measure.map (Subtype.val : U → A ℓ)
                  (Measure.comap (Subtype.val : U → A ℓ) (pol n i)) Set.univ = 1 := by
                  rw [hmap]; exact measure_univ
                rwa [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ] at h1
              obtain ⟨m, hm⟩ : ∃ m : ℕ → Fin d → ProbabilityMeasure U, ∀ n i, (m n i : Measure U) =
                  Measure.comap (Subtype.val : U → A ℓ) (pol n i) :=
                ⟨fun n i => ⟨_, hprob n i⟩, fun n i => rfl⟩
              obtain ⟨x, -, φ, hφ, hx⟩ := (isCompact_univ : IsCompact
                (Set.univ : Set (Fin d → ProbabilityMeasure U))).tendsto_subseq
                (x := m) (fun n => Set.mem_univ _)
              refine ⟨φ, hφ, fun i => Measure.map (Subtype.val : U → A ℓ) (x i : Measure U), ?_, ?_⟩
              · intro i
                refine ⟨Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable, ?_⟩
                rw [Measure.map_apply measurable_subtype_coe hUm.compl]
                have : (Subtype.val : U → A ℓ) ⁻¹' Uᶜ = ∅ := by
                  ext z; simp
                rw [this]; exact measure_empty
              · intro i g hg
                have hxi := (tendsto_pi_nhds.mp hx) i
                rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hxi
                have hgc : Continuous (U.restrict g) := continuousOn_iff_continuous_restrict.mp hg
                have h1 := hxi (BoundedContinuousFunction.mkOfCompact ⟨U.restrict g, hgc⟩)
                have hemb : MeasurableEmbedding (Subtype.val : U → A ℓ) := MeasurableEmbedding.subtype_coe hUm
                have h2 : ∀ k, ∫ u, g u ∂(pol (φ k) i) =
                    ∫ u : U, g u ∂(Measure.comap (Subtype.val : U → A ℓ) (pol (φ k) i)) := by
                  intro k
                  rw [← hemb.integral_map, hmap]
                have h3 : ∫ u, g u ∂(Measure.map (Subtype.val : U → A ℓ) (x i : Measure U)) =
                    ∫ u : U, g u ∂(x i : Measure U) := hemb.integral_map _
                rw [h3]
                simp_rw [h2]
                simp only [Function.comp_apply, hm] at h1
                exact h1
            have L10 : ∀ (ℓ : ℕ) (U : Set (A ℓ)), IsCompact U → ∀ (f : ℝ → A ℓ → ℝ) (Theta : ℝ),
                (∀ u ∈ U, ContinuousOn (fun s => f s u) (Set.Ici 0)) →
                (∀ t, 0 ≤ t → ∀ u ∈ U, ∀ v ∈ U, |f t u - f t v| ≤ Theta * ‖u - v‖) →
                (∀ T, ∃ C, ∀ s, 0 ≤ s → s ≤ T → ∀ u ∈ U, |f s u| ≤ C) ∧
                (∀ (μ : ℕ → Measure (A ℓ)) (ν : Measure (A ℓ)), (∀ n, IsProbabilityMeasure (μ n)) →
                  (∀ n, μ n Uᶜ = 0) →
                  (∀ g : A ℓ → ℝ, ContinuousOn g U → Tendsto (fun n => ∫ u, g u ∂(μ n)) atTop (𝓝 (∫ u, g u ∂ν))) →
                  ∀ (t : ℕ → ℝ) (s : ℝ), 0 ≤ s → (∀ n, 0 ≤ t n) → Tendsto t atTop (𝓝 s) →
                  Tendsto (fun n => ∫ u, f (t n) u ∂(μ n)) atTop (𝓝 (∫ u, f s u ∂ν))) ∧
                (∀ ν : Measure (A ℓ), IsProbabilityMeasure ν → ν Uᶜ = 0 →
                  ContinuousOn (fun s => ∫ u, f s u ∂ν) (Set.Ici 0)) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5 L6a L6b L7 L8 L9
              intro ℓ U hU f Theta hfc hlip
              have hUm : MeasurableSet U := hU.measurableSet
              have hlipOn : ∀ t ∈ Set.Ici (0:ℝ), LipschitzOnWith (Real.toNNReal |Theta|) (fun u => f t u) U := by
                intro t ht
                refine LipschitzOnWith.of_dist_le_mul ?_
                intro u hu v hv
                rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg _)]
                exact (hlip t ht u hu v hv).trans
                  (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
              have hjoint : ContinuousOn (Function.uncurry f) (Set.Ici (0:ℝ) ×ˢ U) :=
                continuousOn_prod_of_continuousOn_lipschitzOnWith' (Function.uncurry f)
                  (Real.toNNReal |Theta|) hlipOn hfc
              have hcu : ∀ t, 0 ≤ t → ContinuousOn (fun u => f t u) U := fun t ht =>
                (hlipOn t ht).continuousOn
              have hint : ∀ (ν : Measure (A ℓ)), IsProbabilityMeasure ν → ν Uᶜ = 0 →
                  ∀ g : A ℓ → ℝ, ContinuousOn g U → Integrable g ν := by
                intro ν hν hνU g hg
                have h1 : IntegrableOn g U ν := hg.integrableOn_compact hU
                have h2 : ν.restrict U = ν := by
                  refine Measure.restrict_eq_self_of_ae_mem ?_
                  rw [ae_iff]
                  exact hνU
                rwa [IntegrableOn, h2] at h1
              have hunif : ∀ (t : ℕ → ℝ) (s : ℝ), 0 ≤ s → (∀ n, 0 ≤ t n) → Tendsto t atTop (𝓝 s) →
                  ∀ e > 0, ∀ᶠ n in atTop, ∀ u ∈ U, |f (t n) u - f s u| ≤ e := by
                intro t s hs ht hts e he
                obtain ⟨v, hv, hv2⟩ := hU.mem_uniformity_of_prod hjoint (Set.mem_Ici.mpr hs)
                  (Metric.dist_mem_uniformity he)
                have h1 : Tendsto t atTop (𝓝[Set.Ici 0] s) :=
                  tendsto_nhdsWithin_iff.mpr ⟨hts, Eventually.of_forall ht⟩
                filter_upwards [h1 hv] with n hn u hu
                have h2 := hv2 (t n) hn u hu
                have h3 : dist (f (t n) u) (f s u) < e := h2
                rw [Real.dist_eq] at h3
                exact h3.le
              have hmain : ∀ (μ : ℕ → Measure (A ℓ)) (ν : Measure (A ℓ)), (∀ n, IsProbabilityMeasure (μ n)) →
                  (∀ n, μ n Uᶜ = 0) →
                  (∀ g : A ℓ → ℝ, ContinuousOn g U → Tendsto (fun n => ∫ u, g u ∂(μ n)) atTop (𝓝 (∫ u, g u ∂ν))) →
                  ∀ (t : ℕ → ℝ) (s : ℝ), 0 ≤ s → (∀ n, 0 ≤ t n) → Tendsto t atTop (𝓝 s) →
                  Tendsto (fun n => ∫ u, f (t n) u ∂(μ n)) atTop (𝓝 (∫ u, f s u ∂ν)) := by
                intro μ ν hμ hμU hw t s hs ht hts
                have h1 := hw (fun u => f s u) (hcu s hs)
                have h2 : Tendsto (fun n => (∫ u, f (t n) u ∂(μ n)) - ∫ u, f s u ∂(μ n)) atTop (𝓝 0) := by
                  rw [Metric.tendsto_atTop]
                  intro e he
                  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif t s hs ht hts (e/2) (by positivity))
                  refine ⟨N, fun n hn => ?_⟩
                  rw [Real.dist_eq, sub_zero]
                  haveI := hμ n
                  rw [← integral_sub (hint (μ n) (hμ n) (hμU n) _ (hcu (t n) (ht n)))
                    (hint (μ n) (hμ n) (hμU n) _ (hcu s hs))]
                  have h3 : ‖∫ u, (f (t n) u - f s u) ∂(μ n)‖ ≤ (e/2) * (μ n).real Set.univ := by
                    refine norm_integral_le_of_norm_le_const ?_
                    have h4 : ∀ᵐ u ∂(μ n), u ∈ U := by
                      rw [ae_iff]
                      exact hμU n
                    filter_upwards [h4] with u hu
                    rw [Real.norm_eq_abs]
                    exact hN n hn u hu
                  rw [Real.norm_eq_abs] at h3
                  simp at h3
                  linarith
                have h5 := h2.add h1
                simpa using h5
              refine ⟨?_, hmain, ?_⟩
              · intro T
                have hK : IsCompact (Set.Icc (0:ℝ) T ×ˢ U) := isCompact_Icc.prod hU
                obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hjoint.mono
                  (Set.prod_mono (fun x hx => hx.1) (le_refl U)))
                refine ⟨C, fun s hs hsT u hu => ?_⟩
                have := hC (s, u) ⟨⟨hs, hsT⟩, hu⟩
                simpa [Function.uncurry] using this
              · intro ν hν hνU s hs
                have hs0 : 0 ≤ s := hs
                rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
                intro t ht
                rw [tendsto_nhdsWithin_iff] at ht
                obtain ⟨ht1, ht2⟩ := ht
                have h1 := hmain (fun _ => ν) ν (fun _ => hν) (fun _ => hνU) (fun g _ => tendsto_const_nhds)
                  (fun n => max (t n) 0) s hs0 (fun n => le_max_right _ _) (by
                    have := ht1.max (tendsto_const_nhds (x := (0:ℝ)))
                    rwa [max_eq_left hs0] at this)
                refine h1.congr' ?_
                filter_upwards [ht2] with n hn
                have hn0 : 0 ≤ t n := hn
                simp only [Function.comp, max_eq_left hn0]
            have L11 : ∀ (ℓ : ℕ) (U : Set (A ℓ)), IsCompact U → 0 < volume U →
                ∀ (g : ℕ → A ℓ → ℝ) (gi : A ℓ → ℝ) (C : ℝ), (∀ n, ContinuousOn (g n) U) → ContinuousOn gi U →
                (∀ n, ∀ u ∈ U, |g n u| ≤ C) →
                (∀ u ∈ U, Tendsto (fun n => g n u) atTop (𝓝 (gi u))) →
                (∀ u ∈ U, Tendsto (fun n => Real.exp (g n u) / ∫ v in U, Real.exp (g n v)) atTop
                  (𝓝 (Real.exp (gi u) / ∫ v in U, Real.exp (gi v)))) ∧
                (∀ φ : A ℓ → ℝ, ContinuousOn φ U →
                  Tendsto (fun n => ∫ u in U, (Real.exp (g n u) / ∫ v in U, Real.exp (g n v)) * φ u) atTop
                  (𝓝 (∫ u in U, (Real.exp (gi u) / ∫ v in U, Real.exp (gi v)) * φ u))) ∧
                Tendsto (fun n => -∫ u in U, (Real.exp (g n u) / ∫ v in U, Real.exp (g n v)) *
                    Real.log (Real.exp (g n u) / ∫ v in U, Real.exp (g n v))) atTop
                  (𝓝 (-∫ u in U, (Real.exp (gi u) / ∫ v in U, Real.exp (gi v)) *
                    Real.log (Real.exp (gi u) / ∫ v in U, Real.exp (gi v)))) := by
              clear! δ Theta iota vartheta h d ℓ
              clear L0 L1 L2 L3 L4 L5 L6a L6b L7 L8 L9 L10
              intro ℓ U hU hvol g gi C hg hgi hb hlim
              have hUm : MeasurableSet U := hU.measurableSet
              have hUf : volume U < ⊤ := hU.measure_lt_top
              haveI : IsFiniteMeasure (volume.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact hUf⟩
              have hV : 0 < volume.real U := ENNReal.toReal_pos hvol.ne' hUf.ne
              have hne : U.Nonempty := nonempty_of_measure_ne_zero hvol.ne'
              have hbi : ∀ u ∈ U, |gi u| ≤ C := fun u hu =>
                le_of_tendsto (hlim u hu).abs (Eventually.of_forall fun n => hb n u hu)
              -- lower and upper bound for Z
              have hZ : ∀ G : A ℓ → ℝ, ContinuousOn G U → (∀ u ∈ U, |G u| ≤ C) →
                  Real.exp (-C) * volume.real U ≤ ∫ v in U, Real.exp (G v) ∧
                  ∫ v in U, Real.exp (G v) ≤ Real.exp C * volume.real U := by
                intro G hG hGb
                have hi : IntegrableOn (fun v => Real.exp (G v)) U :=
                  (Real.continuous_exp.comp_continuousOn hG).integrableOn_compact hU
                have hc : ∀ c : ℝ, ∫ v in U, (fun _ : A ℓ => c) v = c * volume.real U := by
                  intro c; rw [setIntegral_const, smul_eq_mul, mul_comm]
                constructor
                · rw [← hc]
                  refine setIntegral_mono_on (integrable_const _) hi hUm fun u hu => ?_
                  exact Real.exp_le_exp.2 (neg_le_of_abs_le (hGb u hu))
                · rw [← hc]
                  refine setIntegral_mono_on hi (integrable_const _) hUm fun u hu => ?_
                  exact Real.exp_le_exp.2 (le_of_abs_le (hGb u hu))
              have hZpos : ∀ G : A ℓ → ℝ, ContinuousOn G U → (∀ u ∈ U, |G u| ≤ C) →
                  0 < ∫ v in U, Real.exp (G v) := fun G hG hGb =>
                lt_of_lt_of_le (mul_pos (Real.exp_pos _) hV) (hZ G hG hGb).1
              have hZt : Tendsto (fun n => ∫ v in U, Real.exp (g n v)) atTop (𝓝 (∫ v in U, Real.exp (gi v))) := by
                refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp C) ?_ (integrable_const _) ?_ ?_
                · intro n
                  exact (Real.continuous_exp.comp_continuousOn (hg n)).aestronglyMeasurable hUm
                · intro n
                  refine (ae_restrict_iff' hUm).2 (Eventually.of_forall fun u hu => ?_)
                  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                  exact Real.exp_le_exp.2 (le_of_abs_le (hb n u hu))
                · refine (ae_restrict_iff' hUm).2 (Eventually.of_forall fun u hu => ?_)
                  exact (Real.continuous_exp.tendsto _).comp (hlim u hu)
              have hρ : ∀ u ∈ U, Tendsto (fun n => Real.exp (g n u) / ∫ v in U, Real.exp (g n v)) atTop
                  (𝓝 (Real.exp (gi u) / ∫ v in U, Real.exp (gi v))) := fun u hu =>
                ((Real.continuous_exp.tendsto _).comp (hlim u hu)).div hZt (hZpos gi hgi hbi).ne'
              obtain ⟨R, hRdef⟩ : ∃ R, R = Real.exp C / (Real.exp (-C) * volume.real U) := ⟨_, rfl⟩
              have hR0 : 0 ≤ R := by
                rw [hRdef]; exact div_nonneg (Real.exp_pos _).le (mul_pos (Real.exp_pos _) hV).le
              have hρb : ∀ n, ∀ u ∈ U, |Real.exp (g n u) / ∫ v in U, Real.exp (g n v)| ≤ R := by
                intro n u hu
                have hp := hZpos _ (hg n) (hb n)
                rw [abs_of_pos (div_pos (Real.exp_pos _) hp), hRdef]
                exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.2 (le_of_abs_le (hb n u hu)))
                  (mul_pos (Real.exp_pos _) hV) (hZ _ (hg n) (hb n)).1
              have hlogb : ∀ n, ∀ u ∈ U, |Real.log (Real.exp (g n u) / ∫ v in U, Real.exp (g n v))| ≤
                  C + (C + |Real.log (volume.real U)|) := by
                intro n u hu
                have hp := hZpos _ (hg n) (hb n)
                rw [Real.log_div (Real.exp_pos _).ne' hp.ne', Real.log_exp]
                have h1 : Real.log (∫ v in U, Real.exp (g n v)) ≤ C + Real.log (volume.real U) := by
                  have := Real.log_le_log hp (hZ _ (hg n) (hb n)).2
                  rwa [Real.log_mul (Real.exp_pos _).ne' hV.ne', Real.log_exp] at this
                have h2 : -C + Real.log (volume.real U) ≤ Real.log (∫ v in U, Real.exp (g n v)) := by
                  have := Real.log_le_log (mul_pos (Real.exp_pos _) hV) (hZ _ (hg n) (hb n)).1
                  rwa [Real.log_mul (Real.exp_pos _).ne' hV.ne', Real.log_exp] at this
                have h3 := abs_le.1 (hb n u hu)
                have h4 := le_abs_self (Real.log (volume.real U))
                have h5 := neg_abs_le (Real.log (volume.real U))
                rw [abs_le]
                constructor
                · linarith only [h3.1, h1, h4]
                · linarith only [h3.2, h2, h5]
              have hρc : ∀ n, ContinuousOn (fun u => Real.exp (g n u) / ∫ v in U, Real.exp (g n v)) U := fun n =>
                (Real.continuous_exp.comp_continuousOn (hg n)).div_const _
              refine ⟨hρ, fun φ hφ => ?_, Tendsto.neg ?_⟩
              · obtain ⟨Cφ, hCφ⟩ := hU.exists_bound_of_continuousOn hφ
                refine tendsto_integral_of_dominated_convergence (fun _ => R * Cφ) ?_ (integrable_const _) ?_ ?_
                · intro n
                  exact ((hρc n).mul hφ).aestronglyMeasurable hUm
                · intro n
                  refine (ae_restrict_iff' hUm).2 (Eventually.of_forall fun u hu => ?_)
                  rw [norm_mul]
                  exact mul_le_mul (hρb n u hu) (hCφ u hu) (norm_nonneg _) hR0
                · refine (ae_restrict_iff' hUm).2 (Eventually.of_forall fun u hu => ?_)
                  exact (hρ u hu).mul_const _
              · refine tendsto_integral_of_dominated_convergence
                  (fun _ => R * (C + (C + |Real.log (volume.real U)|))) ?_ (integrable_const _) ?_ ?_
                · intro n
                  have hl : ContinuousOn (fun u => Real.log (Real.exp (g n u) / ∫ v in U, Real.exp (g n v))) U :=
                    (hρc n).log fun u _ => (div_pos (Real.exp_pos _) (hZpos _ (hg n) (hb n))).ne'
                  exact ((hρc n).mul hl).aestronglyMeasurable hUm
                · intro n
                  refine (ae_restrict_iff' hUm).2 (Eventually.of_forall fun u hu => ?_)
                  rw [norm_mul]
                  exact mul_le_mul (hρb n u hu) (hlogb n u hu) (norm_nonneg _) hR0
                · refine (ae_restrict_iff' hUm).2 (Eventually.of_forall fun u hu => ?_)
                  exact (hρ u hu).mul ((hρ u hu).log
                    (div_pos (Real.exp_pos _) (hZpos gi hgi hbi)).ne')
            have hcpt : IsCompact U := hS.compact
            have hUm : MeasurableSet U := hcpt.measurableSet
            have hvol := hS.vol_pos
            have hTh : 0 < Theta := h22.pos
            have hne : U.Nonempty := nonempty_of_measure_ne_zero hvol.ne'
            have hhpos : ∀ n, 0 < h n := fun n => (hh.1 n).1
            have hh0 : Tendsto h atTop (𝓝 0) := hh.2.2
            have hδ0 : ∀ s, 0 ≤ s → 0 ≤ δ s := h31.discount.nonneg
            have hδ1 : ∀ s, 0 ≤ s → δ s ≤ 1 := h31.discount.le_one
            have hflip : ∀ t, 0 ≤ t → ∀ i, ∀ u ∈ U, ∀ v ∈ U, |f t i u - f t i v| ≤ Theta * ‖u - v‖ := by
              intro t ht i u hu v hv
              have h1 := h22.lip t ht i u hu v hv
              have h2 : 0 ≤ enorm2 (q u i - q v i) := Real.sqrt_nonneg _
              linarith only [h1, h2]
            have hqlip : ∀ i j, ∀ u ∈ U, ∀ v ∈ U, |q u i j - q v i j| ≤ Theta * ‖u - v‖ := by
              intro i j u hu v hv
              have h1 := h22.lip 0 le_rfl i u hu v hv
              have h2 : |q u i j - q v i j| ≤ enorm2 (q u i - q v i) := by
                unfold enorm2
                apply Real.abs_le_sqrt
                exact Finset.single_le_sum (f := fun j => (q u i - q v i) j ^ 2)
                  (fun j _ => sq_nonneg _) (Finset.mem_univ j)
              have h3 := abs_nonneg (f 0 i u - f 0 i v)
              linarith only [h1, h2, h3]
            have hlipcont : ∀ g : A ℓ → ℝ, (∀ u ∈ U, ∀ v ∈ U, |g u - g v| ≤ Theta * ‖u - v‖) →
                ContinuousOn g U := by
              intro g hg
              have : LipschitzOnWith (Real.toNNReal Theta) g U := by
                apply LipschitzOnWith.of_dist_le_mul
                intro u hu v hv
                rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hTh.le]
                exact hg u hu v hv
              exact this.continuousOn
            have hfcont : ∀ t, 0 ≤ t → ∀ i, ContinuousOn (f t i) U := fun t ht i =>
              hlipcont _ (hflip t ht i)
            have hqcont : ∀ i j, ContinuousOn (fun u => q u i j) U := fun i j => hlipcont _ (hqlip i j)
            have hL10 := fun i => L10 ℓ U hcpt (fun s u => f s i u) Theta (hfc i)
              (fun t ht u hu v hv => hflip t ht i u hu v hv)
            have haeU : ∀ μ : Measure (A ℓ), μ Uᶜ = 0 → ∀ᵐ u ∂μ, u ∈ U := by
              intro μ hμ
              exact mem_ae_iff.mpr hμ
            have hint : ∀ μ : Measure (A ℓ), IsProbabilityMeasure μ → μ Uᶜ = 0 → ∀ g : A ℓ → ℝ,
                ContinuousOn g U → Integrable g μ := by
              intro μ hμp hμ g hg
              have h1 : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem (haeU μ hμ)
              have h2 : IntegrableOn g U μ := hg.integrableOn_compact hcpt
              rw [IntegrableOn, h1] at h2
              exact h2
            have hPbar : ∀ (c : ℝ) (pol : Control d ℓ), IsRelaxed U pol →
                Pbar (ph q c) pol = c • Qbar q pol + 1 := by
              intro c pol hpol
              ext i j
              have := (hpol i).1
              have h1 := hint (pol i) (hpol i).1 (hpol i).2 _ (hqcont i j)
              simp only [Pbar, ph, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
              rw [integral_add (h1.const_mul c) (integrable_const _), integral_const_mul]
              simp
            have hst0 : ∀ n (pol : Control d ℓ), IsRelaxed U pol → ∀ i j,
                0 ≤ (h n • Qbar q pol + 1) i j := by
              intro n pol hpol i j
              rw [← hPbar _ pol hpol]
              apply integral_nonneg_of_ae
              filter_upwards [haeU _ (hpol i).2] with u hu
              exact (hph n).nonneg u hu i j
            have hst1 : ∀ n (pol : Control d ℓ), IsRelaxed U pol → ∀ i,
                ∑ j, (h n • Qbar q pol + 1) i j = 1 := by
              intro n pol hpol i
              rw [← hPbar _ pol hpol]
              have := (hpol i).1
              simp only [Pbar]
              rw [← integral_finsetSum]
              · rw [integral_congr_ae (g := fun _ => (1:ℝ))]
                · simp
                · filter_upwards [haeU _ (hpol i).2] with u hu
                  exact (hph n).row_sum u hu i
              · intro j _
                apply hint (pol i) (hpol i).1 (hpol i).2
                have : (fun u => ph q (h n) u i j) =
                    fun u => h n * q u i j + (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
                  ext u; simp [ph]
                rw [this]
                exact (continuousOn_const.mul (hqcont i j)).add continuousOn_const
            have hfbar : ∀ (c : ℝ) (μ : Measure (A ℓ)) (k : ℕ) (i : Fin d),
                fbar (fh f c) μ k i = c * fbarCT f μ ((k:ℝ) * c) i := by
              intro c μ k i
              simp only [fbar, fh, fbarCT]
              rw [integral_mul_const, mul_comm]
            obtain ⟨B0, hB0n, hB0b, hB0s, hB0t, hB0f⟩ : ∃ B0 : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ B0 s) ∧
                (∀ T, ∃ C, ∀ s, 0 ≤ s → s ≤ T → B0 s ≤ C) ∧
                (∀ n, Summable (fun k : ℕ => B0 ((k : ℝ) * h n))) ∧
                (∀ η > 0, ∃ T : ℝ, ∀ n, h n * ∑' k : ℕ,
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => B0 ((k : ℝ) * h n)) k ≤ η) ∧
                (∀ s, 0 ≤ s → ∀ i, ∀ u ∈ U, |f s i u| ≤ B0 s) := by
              obtain ⟨b, hb, hbs, hbt⟩ := htail
              choose C hC using fun i => (hL10 i).1
              have hDex : ∀ N : ℕ, ∀ i, ∀ s : ℝ, 0 ≤ s → s ≤ N → ∀ u ∈ U,
                  |f s i u| ≤ ∑ m ∈ Finset.range (N+1), ∑ i, |C i m| := by
                intro N i s hs hsN u hu
                have h1 := hC i N s hs hsN u hu
                have h2 : |C i N| ≤ ∑ i, |C i N| := Finset.single_le_sum (f := fun i => |C i N|)
                  (fun i _ => abs_nonneg _) (Finset.mem_univ i)
                have h3 : ∑ i, |C i N| ≤ ∑ m ∈ Finset.range (N+1), ∑ i, |C i m| :=
                  Finset.single_le_sum (f := fun m : ℕ => ∑ i, |C i m|)
                    (fun m _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
                    (Finset.mem_range.mpr (Nat.lt_succ_self N))
                exact h1.trans ((le_abs_self _).trans (h2.trans h3))
              have hbn : ∀ s, 0 ≤ s → 0 ≤ b s := by
                intro s hs
                obtain ⟨u, hu⟩ := hne
                exact (abs_nonneg _).trans (hb s hs ⟨0, hd⟩ u hu)
              have hmin0 : ∀ s, 0 ≤ s → 0 ≤ min (b s) (∑ m ∈ Finset.range (⌈s⌉₊+1), ∑ i, |C i m|) := by
                intro s hs
                exact le_min (hbn s hs) (Finset.sum_nonneg fun m _ =>
                  Finset.sum_nonneg fun i _ => abs_nonneg _)
              have hsumm : ∀ n, Summable (fun k : ℕ => min (b ((k:ℝ) * h n))
                  (∑ m ∈ Finset.range (⌈(k:ℝ) * h n⌉₊+1), ∑ i, |C i m|)) := by
                intro n
                refine Summable.of_nonneg_of_le (fun k => hmin0 _ ?_) (fun k => min_le_left _ _) (hbs n)
                exact mul_nonneg (Nat.cast_nonneg _) (hhpos n).le
              refine ⟨fun s => min (b s) (∑ m ∈ Finset.range (⌈s⌉₊+1), ∑ i, |C i m|), hmin0, ?_, hsumm,
                ?_, ?_⟩
              · intro T
                refine ⟨∑ m ∈ Finset.range (⌈T⌉₊+1), ∑ i, |C i m|, fun s hs hsT => ?_⟩
                refine (min_le_right _ _).trans ?_
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · exact Finset.range_mono (Nat.succ_le_succ (Nat.ceil_mono hsT))
                · intro m _ _
                  exact Finset.sum_nonneg fun i _ => abs_nonneg _
              · intro η hη
                obtain ⟨T, hT⟩ := hbt η hη
                refine ⟨T, fun n => le_trans ?_ (hT n)⟩
                apply mul_le_mul_of_nonneg_left _ (hhpos n).le
                apply Summable.tsum_le_tsum _ ((hsumm n).indicator _) ((hbs n).indicator _)
                intro k
                apply Set.indicator_le_indicator
                exact min_le_left _ _
              · intro s hs i u hu
                exact le_min (hb s hs i u hu) (hDex _ i s hs (Nat.le_ceil s) u hu)
            have hGM : ∀ K : ℝ, 0 ≤ K → (∀ s, 0 ≤ s → 0 ≤ B0 s + K * δ s) ∧
                (∀ T, ∃ C, ∀ s, 0 ≤ s → s ≤ T → B0 s + K * δ s ≤ C) ∧
                (∀ n, Summable (fun k : ℕ => B0 ((k : ℝ) * h n) + K * δ ((k : ℝ) * h n))) ∧
                (∀ η > 0, ∃ T : ℝ, ∀ n, h n * ∑' k : ℕ,
                  Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n}
                    (fun k : ℕ => B0 ((k : ℝ) * h n) + K * δ ((k : ℝ) * h n)) k ≤ η) := by
              intro K hK
              obtain ⟨hδs, hδt⟩ := L3 δ h31.discount h31.integrable_delta h hh.1
              refine ⟨fun s hs => add_nonneg (hB0n s hs) (mul_nonneg hK (hδ0 s hs)), ?_,
                fun n => (hB0s n).add ((hδs n).mul_left K), ?_⟩
              · intro T
                obtain ⟨C, hC⟩ := hB0b T
                refine ⟨C + K, fun s hs hsT => ?_⟩
                have e1 := mul_le_mul_of_nonneg_left (hδ1 s hs) hK
                have e2 := hC s hs hsT
                linarith only [e1, e2]
              · intro η hη
                obtain ⟨T1, hT1⟩ := hB0t (η/2) (half_pos hη)
                obtain ⟨T2, hT2⟩ := hδt (η/(2*(K+1))) (div_pos hη (mul_pos two_pos (add_pos_of_nonneg_of_pos hK one_pos)))
                refine ⟨max T1 T2, fun n => ?_⟩
                have hh1 := hT1 n
                have hh2 := hT2 n
                have e1 : ∑' k : ℕ, Set.indicator {k : ℕ | max T1 T2 ≤ (k : ℝ) * h n}
                    (fun k : ℕ => B0 ((k : ℝ) * h n) + K * δ ((k : ℝ) * h n)) k ≤
                    ∑' k : ℕ, (Set.indicator {k : ℕ | T1 ≤ (k : ℝ) * h n}
                      (fun k : ℕ => B0 ((k : ℝ) * h n)) k + K * Set.indicator {k : ℕ | T2 ≤ (k : ℝ) * h n}
                      (fun k : ℕ => δ ((k : ℝ) * h n)) k) := by
                  apply Summable.tsum_le_tsum
                  · intro k
                    have hk : 0 ≤ (k:ℝ) * h n := mul_nonneg (Nat.cast_nonneg _) (hhpos n).le
                    have p1 := hB0n _ hk
                    have p2 := hδ0 _ hk
                    have p3 := mul_nonneg hK p2
                    by_cases c : max T1 T2 ≤ (k:ℝ) * h n
                    · have c1 : T1 ≤ (k:ℝ) * h n := (le_max_left _ _).trans c
                      have c2 : T2 ≤ (k:ℝ) * h n := (le_max_right _ _).trans c
                      rw [Set.indicator_of_mem (by exact c), Set.indicator_of_mem (by exact c1),
                        Set.indicator_of_mem (by exact c2)]
                    · rw [Set.indicator_of_notMem (by exact c)]
                      apply add_nonneg
                      · rw [Set.indicator_apply]; split_ifs; exacts [p1, le_rfl]
                      · apply mul_nonneg hK; rw [Set.indicator_apply]; split_ifs; exacts [p2, le_rfl]
                  · exact ((hB0s n).add ((hδs n).mul_left K)).indicator _
                  · exact ((hB0s n).indicator _).add (((hδs n).indicator _).mul_left K)
                rw [Summable.tsum_add ((hB0s n).indicator _) (((hδs n).indicator _).mul_left K),
                  tsum_mul_left] at e1
                have e2 := mul_le_mul_of_nonneg_left e1 (hhpos n).le
                have e3 : K * (η/(2*(K+1))) ≤ η/2 := by
                  rw [mul_div_assoc', div_le_div_iff₀ (mul_pos two_pos (add_pos_of_nonneg_of_pos hK one_pos))
                    two_pos]
                  linarith only [hη, hK, mul_nonneg hK (le_of_lt hη)]
                have e4 := mul_le_mul_of_nonneg_left hh2 hK
                refine e2.trans ?_
                rw [mul_add]
                have e5 : h n * (K * ∑' k : ℕ, Set.indicator {k : ℕ | T2 ≤ (k : ℝ) * h n}
                      (fun k : ℕ => δ ((k : ℝ) * h n)) k) = K * (h n * ∑' k : ℕ,
                      Set.indicator {k : ℕ | T2 ≤ (k : ℝ) * h n}
                      (fun k : ℕ => δ ((k : ℝ) * h n)) k) := by ring
                rw [e5]
                linarith only [hh1, e3, e4]
            have hfbd : ∀ (pol : Control d ℓ), IsRelaxed U pol → ∀ s, 0 ≤ s → ∀ j,
                |fbarCT f (pol j) s j| ≤ B0 s := by
              intro pol hpol s hs j
              have := (hpol j).1
              have h1 : ∀ᵐ u ∂(pol j), ‖f s j u‖ ≤ B0 s := by
                filter_upwards [haeU _ (hpol j).2] with u hu
                exact hB0f s hs j u hu
              have h2 := norm_integral_le_of_norm_le_const h1
              simpa [fbarCT] using h2
            obtain ⟨bb, hbbi, hbb⟩ := h31.bound
            have hrew : ∀ (pol : Control d ℓ), IsRelaxed U pol → ∀ (lam : ℝ) (e : Fin d → ℝ) (j : Fin d),
                ContinuousOn (fun s => fbarCT f (pol j) s j + lam * δ s * e j) (Set.Ici 0) ∧
                IntegrableOn (fun s => fbarCT f (pol j) s j + lam * δ s * e j) (Set.Ioi 0) := by
              intro pol hpol lam e j
              have hc1 : ContinuousOn (fun s => fbarCT f (pol j) s j) (Set.Ici 0) :=
                (hL10 j).2.2 (pol j) (hpol j).1 (hpol j).2
              have hc2 : ContinuousOn (fun s => lam * δ s * e j) (Set.Ici 0) :=
                (continuousOn_const.mul hδc).mul continuousOn_const
              refine ⟨hc1.add hc2, ?_⟩
              have hi1 : IntegrableOn (fun s => fbarCT f (pol j) s j) (Set.Ioi 0) := by
                apply Integrable.mono' (hbbi.mono_set Set.Ioi_subset_Ici_self)
                · exact (hc1.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
                · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
                  have := (hpol j).1
                  have h1 : ∀ᵐ u ∂(pol j), ‖f s j u‖ ≤ bb s := by
                    filter_upwards [haeU _ (hpol j).2] with u hu
                    exact hbb s (le_of_lt hs) j u hu
                  have h2 := norm_integral_le_of_norm_le_const h1
                  simpa [fbarCT] using h2
              have hi2 : IntegrableOn (fun s => lam * δ s * e j) (Set.Ioi 0) :=
                ((h31.integrable_delta.mono_set Set.Ioi_subset_Ici_self).const_mul lam).mul_const (e j)
              exact hi1.add hi2
            obtain ⟨Vd, hVd⟩ : ∃ Vd : ℕ → Control d ℓ → ℝ → (Fin d → ℝ) → Fin d → ℝ, ∀ n pol lam e i,
                Vd n pol lam e i = ∑' k : ℕ, (((h n • Qbar q pol + 1) ^ k) *ᵥ (fun j => h n *
                  (fbarCT f (pol j) ((1 + (k : ℝ)) * h n) j + lam * δ ((1 + (k : ℝ)) * h n) * e j))) i :=
              ⟨_, fun _ _ _ _ _ => rfl⟩
            have hM : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (pol : ℕ → Control d ℓ) (polInf : Control d ℓ),
                (∀ n, IsRelaxed U (pol n)) → IsRelaxed U polInf →
                (∀ i, ∀ g : A ℓ → ℝ, ContinuousOn g U →
                  Tendsto (fun k => ∫ u, g u ∂(pol (φ k) i)) atTop (𝓝 (∫ u, g u ∂(polInf i)))) →
                ∀ (lam : ℝ) (e : ℕ → Fin d → ℝ) (ei : Fin d → ℝ) (K : ℝ), (∀ n j, |e n j| ≤ K) →
                (∀ j, Tendsto (fun k => e (φ k) j) atTop (𝓝 (ei j))) →
                (∀ s : ℕ, 0 ≤ s → ∀ i j, |(NormedSpace.exp (s • Qbar q polInf) : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1) ∧
                (Tendsto (fun k => Qbar q (pol (φ k))) atTop (𝓝 (Qbar q polInf))) ∧
                ∀ i, Tendsto (fun k => Vd (φ k) (pol (φ k)) lam (e (φ k)) i) atTop
                  (𝓝 (∫ s in Set.Ioi 0, (trans q polInf s *ᵥ
                    (fun j => fbarCT f (polInf j) s j + lam * δ s * ei j)) i)) := by
              intro φ hφ pol polInf hpol hpolInf hw lam e ei K hK hei
              have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨0, hd⟩)
              have hQ : Tendsto (fun k => Qbar q (pol (φ k))) atTop (𝓝 (Qbar q polInf)) := by
                refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
                exact hw i _ (hqcont i j)
              obtain ⟨G1, G2, G3, G4⟩ := hGM (|lam| * K) (mul_nonneg (abs_nonneg lam) hK0)
              have hL2 := L2 d (fun k => Qbar q (pol (φ k))) (Qbar q polInf) (fun k => h (φ k)) hQ
                (fun k => hhpos _) (hh0.comp hφ.tendsto_atTop) (fun k => hst0 _ _ (hpol _))
                (fun k => hst1 _ _ (hpol _))
                (fun k s j => fbarCT f (pol (φ k) j) s j + lam * δ s * e (φ k) j)
                (fun s j => fbarCT f (polInf j) s j + lam * δ s * ei j)
                (fun s => B0 s + |lam| * K * δ s) G1 G2 (fun k => G3 _)
                (fun η hη => by
                  obtain ⟨T, hT⟩ := G4 η hη
                  exact ⟨T, fun k => hT _⟩)
                (fun k s j hs => by
                  have h1 := hfbd (pol (φ k)) (hpol _) s hs j
                  have h2 : |lam * δ s * e (φ k) j| ≤ |lam| * K * δ s := by
                    rw [abs_mul, abs_mul, abs_of_nonneg (hδ0 s hs)]
                    have := mul_le_mul_of_nonneg_left (hK (φ k) j)
                      (mul_nonneg (abs_nonneg lam) (hδ0 s hs))
                    linarith only [this]
                  exact (abs_add_le _ _).trans (add_le_add h1 h2))
                (fun j s hs t ht hts => by
                  have h1 := (hL10 j).2.1 (fun k => pol (φ k) j) (polInf j) (fun k => (hpol _ j).1)
                    (fun k => (hpol _ j).2) (hw j) t s hs ht hts
                  have h2 : Tendsto (fun k => δ (t k)) atTop (𝓝 (δ s)) := by
                    have := hδc s hs
                    exact this.tendsto.comp (tendsto_nhdsWithin_iff.mpr
                      ⟨hts, Eventually.of_forall ht⟩)
                  exact h1.add ((tendsto_const_nhds.mul h2).mul (hei j)))
                (fun j => (hrew polInf hpolInf lam ei j).1)
                (fun j => (hrew polInf hpolInf lam ei j).2)
              refine ⟨fun m _ i j => by
                have := hL2.1 (m:ℝ) (Nat.cast_nonneg _) i j
                rwa [Nat.cast_smul_eq_nsmul] at this, hQ, fun i => ?_⟩
              refine Tendsto.congr (fun k => ?_) (hL2.2 i)
              rw [hVd]
            have hgen : ∀ n (pol pol' : Control d ℓ), IsRelaxed U pol → IsRelaxed U pol' → ∀ (lam : ℝ)
                (E : Measure (A ℓ) → ℝ) (i : Fin d),
                seqValue (ph q (h n)) (concat pol' pol) (fun k c j => fbar (fh f (h n)) (c j) k j +
                  h n * lam * deltah δ (h n) k * E (c j)) i =
                h n * (fbarCT f (pol' i) 0 i + lam * E (pol' i)) +
                  ∑ j, (h n • Qbar q pol' + 1) i j * Vd n pol lam (fun j => E (pol j)) j := by
              intro n pol pol' hpol hpol' lam E i
              have hterm : ∀ (k : ℕ) (j : Fin d), fbar (fh f (h n)) (pol j) (k+1) j +
                  h n * lam * deltah δ (h n) (k+1) * E (pol j) = h n *
                  (fbarCT f (pol j) ((1 + (k : ℝ)) * h n) j + lam * δ ((1 + (k : ℝ)) * h n) * E (pol j)) := by
                intro k j
                rw [hfbar]
                simp only [deltah]
                push_cast
                rw [add_comm (k:ℝ) 1]
                ring
              obtain ⟨K, hK⟩ : ∃ K, ∀ j, |E (pol j)| ≤ K := by
                refine ⟨∑ j, |E (pol j)|, fun j => ?_⟩
                exact Finset.single_le_sum (f := fun j => |E (pol j)|) (fun _ _ => abs_nonneg _)
                  (Finset.mem_univ j)
              have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK ⟨0, hd⟩)
              obtain ⟨G1, G2, G3, G4⟩ := hGM (|lam| * K) (mul_nonneg (abs_nonneg lam) hK0)
              have hP := hPbar (h n) pol hpol
              have hL0 := L0 d (h n • Qbar q pol + 1) (hst0 n pol hpol) (hst1 n pol hpol)
              have hsum : ∀ j, Summable (fun k : ℕ => ((Pbar (ph q (h n)) pol ^ k) *ᵥ
                  (fun j => fbar (fh f (h n)) (pol j) (k+1) j +
                    h n * lam * deltah δ (h n) (k+1) * E (pol j))) j) := by
                intro j
                rw [hP]
                have hs1 : Summable (fun k : ℕ => h n * (B0 (((k+1 : ℕ) : ℝ) * h n) +
                    |lam| * K * δ (((k+1 : ℕ):ℝ) * h n))) :=
                  ((summable_nat_add_iff 1).mpr (G3 n)).mul_left (h n)
                refine Summable.of_norm_bounded hs1 (fun k => ?_)
                rw [Real.norm_eq_abs]
                apply (hL0 k).2
                intro j
                rw [hterm, abs_mul, abs_of_pos (hhpos n)]
                apply mul_le_mul_of_nonneg_left _ (hhpos n).le
                have hs : 0 ≤ (1 + (k:ℝ)) * h n := mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg k)) (hhpos n).le
                have h1 := hfbd pol hpol _ hs j
                have h2 : |lam * δ ((1 + (k:ℝ)) * h n) * E (pol j)| ≤
                    |lam| * K * δ ((1 + (k:ℝ)) * h n) := by
                  rw [abs_mul, abs_mul, abs_of_nonneg (hδ0 _ hs)]
                  have := mul_le_mul_of_nonneg_left (hK j)
                    (mul_nonneg (abs_nonneg lam) (hδ0 _ hs))
                  linarith only [this]
                have h3 : (((k+1 : ℕ) : ℝ) * h n) = (1 + (k:ℝ)) * h n := by push_cast; ring
                rw [h3]
                exact (abs_add_le _ _).trans (add_le_add h1 h2)
              have hL7 := L7 d ℓ (ph q (h n)) pol pol' (fun k c j => fbar (fh f (h n)) (c j) k j +
                  h n * lam * deltah δ (h n) k * E (c j)) i hsum
              rw [hL7, hPbar (h n) pol' hpol', hP]
              congr 1
              · rw [hfbar]
                simp only [deltah, Nat.cast_zero, zero_mul, h31.discount.zero]
                ring
              · apply Finset.sum_congr rfl
                intro j _
                rw [hVd]
                congr 1
                apply tsum_congr
                intro k
                congr 2
                ext j
                exact hterm k j
            have hconc : ∀ pol : Control d ℓ, concat pol pol = fun _ => pol := by
              intro pol
              ext k
              simp [concat]
            have hdisc : ∀ n (pol pol' : Control d ℓ), IsRelaxed U pol → IsRelaxed U pol' → ∀ (lam : ℝ)
                (E : Measure (A ℓ) → ℝ) (i : Fin d),
                seqValue (ph q (h n)) (concat pol' pol) (fun k c j => fbar (fh f (h n)) (c j) k j +
                  h n * lam * deltah δ (h n) k * E (c j)) i -
                seqValue (ph q (h n)) (fun _ => pol) (fun k c j => fbar (fh f (h n)) (c j) k j +
                  h n * lam * deltah δ (h n) k * E (c j)) i ≤ 0 →
                fbarCT f (pol' i) 0 i + lam * E (pol' i) +
                  (Qbar q pol' *ᵥ Vd n pol lam (fun j => E (pol j))) i ≤
                fbarCT f (pol i) 0 i + lam * E (pol i) +
                  (Qbar q pol *ᵥ Vd n pol lam (fun j => E (pol j))) i := by
              intro n pol pol' hpol hpol' lam E i hle
              have e1 := hgen n pol pol' hpol hpol' lam E i
              have e2 := hgen n pol pol hpol hpol lam E i
              rw [hconc] at e2
              rw [e1, e2] at hle
              have hs : ∀ (Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ),
                  ∑ j, (h n • Q + 1) i j * v j = h n * (Q *ᵥ v) i + v i := by
                intro Q v
                have : ∑ j, (h n • Q + 1) i j * v j = ((h n • Q + 1) *ᵥ v) i := rfl
                rw [this, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
                simp
              rw [hs, hs] at hle
              have hpos := hhpos n
              by_contra hcon
              push Not at hcon
              have := mul_lt_mul_of_pos_left hcon hpos
              linarith only [this, hle]
            have hgform : ∀ (pol : Control d ℓ), IsRelaxed U pol → ∀ (y : Fin d → ℝ) (i : Fin d),
                fbarCT f (pol i) 0 i + (Qbar q pol *ᵥ y) i = ∫ u, (f 0 i u + q u i ⬝ᵥ y) ∂(pol i) := by
              intro pol hpol y i
              have i1 := hint (pol i) (hpol i).1 (hpol i).2 _ (hfcont 0 le_rfl i)
              have i2 := fun j => hint (pol i) (hpol i).1 (hpol i).2 _ (hqcont i j)
              have e1 : (Qbar q pol *ᵥ y) i = ∫ u, q u i ⬝ᵥ y ∂(pol i) := by
                simp only [Matrix.mulVec, dotProduct, Pbar]
                rw [integral_finsetSum]
                · apply Finset.sum_congr rfl
                  intro j _
                  rw [integral_mul_const]
                · intro j _
                  exact (i2 j).mul_const _
              have i3 : Integrable (fun u => q u i ⬝ᵥ y) (pol i) := by
                simp only [dotProduct]
                exact integrable_finsetSum _ fun j _ => (i2 j).mul_const _
              rw [e1, integral_add i1 i3]
              rfl
            refine ⟨?_, ?_⟩
            · intro lam hlam pol hpol
              have hrel : ∀ n, IsRelaxed U (pol n) := fun n => (hpol n).1.1
              obtain ⟨V, hV⟩ : ∃ V : ℕ → Fin d → ℝ, ∀ n, V n = Vd n (pol n) lam (fun j => ent U (pol n j)) :=
                ⟨_, fun _ => rfl⟩
              obtain ⟨G, hG⟩ : ∃ G : (Fin d → ℝ) → Fin d → A ℓ → ℝ, ∀ y i u,
                  G y i u = (f 0 i u + q u i ⬝ᵥ y) / lam := ⟨_, fun _ _ _ => rfl⟩
              have hGcont : ∀ y i, ContinuousOn (G y i) U := by
                intro y i
                have h1 : G y i = fun u => (f 0 i u + ∑ j, q u i j * y j) / lam := by
                  ext u; rw [hG]; rfl
                rw [h1]
                refine ContinuousOn.div_const ?_ _
                refine (hfcont 0 le_rfl i).add ?_
                exact continuousOn_finsetSum _ fun j _ => (hqcont i j).mul continuousOn_const
              have hgibbs : ∀ y i, gibbsCtrlCT U q f lam y i = (volume.restrict U).withDensity
                  (fun u => ENNReal.ofReal (Real.exp (G y i u) / ∫ v in U, Real.exp (G y i v))) := by
                intro y i
                simp only [gibbsCtrlCT, gibbsCtrl, gibbsDensity, gibbsWeight, hG]
              have h6a := fun y i => L6a ℓ U hcpt hvol (G y i) (hGcont y i) _ (hgibbs y i)
              have hgreg : ∀ y, IsRegular U (gibbsCtrlCT U q f lam y) := fun y =>
                ⟨fun i => ⟨(h6a y i).1, (h6a y i).2.1⟩, fun i => ⟨(h6a y i).2.2.1, (h6a y i).2.2.2.1⟩⟩
              have hGint : ∀ (p' : Control d ℓ) y i, fbarCT f (p' i) 0 i + lam * ent U (p' i) +
                  ((Qbar q p') *ᵥ y) i = fbarCT f (p' i) 0 i + ((Qbar q p') *ᵥ y) i + lam * ent U (p' i) := by
                intro p' y i
                ring
              have hGint2 : ∀ (p' : Control d ℓ), IsRelaxed U p' → ∀ y i, fbarCT f (p' i) 0 i +
                  lam * ent U (p' i) + ((Qbar q p') *ᵥ y) i =
                  lam * (∫ u, G y i u ∂(p' i) + ent U (p' i)) := by
                intro p' hp' y i
                rw [hGint, hgform p' hp', mul_add]
                congr 1
                rw [← integral_const_mul]
                apply integral_congr_ae
                refine Eventually.of_forall fun u => ?_
                show f 0 i u + q u i ⬝ᵥ y = lam * G y i u
                rw [hG, mul_div_cancel₀ _ hlam.ne']
              have hpolg : ∀ n, pol n = gibbsCtrlCT U q f lam (V n) := by
                intro n
                funext i
                have hreg := (hpol n).1
                have h1 := (hpol n).2 i (gibbsCtrlCT U q f lam (V n)) (hgreg (V n))
                have h2 := hdisc n (pol n) (gibbsCtrlCT U q f lam (V n)) (hrel n) (hgreg (V n)).1 lam
                  (ent U) i h1
                rw [← hV, hGint2 _ (hgreg (V n)).1, hGint2 _ (hrel n)] at h2
                have h3 := le_of_mul_le_mul_left h2 hlam
                rw [(h6a (V n) i).2.2.2.2.2.2.2] at h3
                have h4 := (L6b ℓ U hcpt hvol (G (V n) i) (hGcont _ _) (pol n i) (hrel n i).1 (hrel n i).2
                  (hreg.2 i).1 (hreg.2 i).2).2 h3
                have := (hrel n i).1
                have : IsFiniteMeasure (volume.restrict U) :=
                  isFiniteMeasure_restrict.mpr hcpt.measure_lt_top.ne
                have h5 := Measure.withDensity_rnDeriv_eq (pol n i) (volume.restrict U) (hreg.2 i).1
                rw [← h5, hgibbs]
                apply withDensity_congr_ae
                filter_upwards [h4, Measure.rnDeriv_lt_top (pol n i) (volume.restrict U)] with u hu hu2
                rw [← hu, density, ENNReal.ofReal_toReal hu2.ne]
              have hentb : ∀ ε > 0, ∃ C : ℝ, ∀ n i, |ent U (pol n i)| ≤
                  C + ε * (Theta * (1 + ∑ j, |V n j|) / lam) := by
                intro ε hε
                obtain ⟨C, hC⟩ := L5 ℓ U iota vartheta hℓ hcpt hvol h23 ε hε
                refine ⟨C, fun n i => ?_⟩
                have hp : 0 ≤ Theta * (1 + ∑ j, |V n j|) / lam :=
                  div_nonneg (mul_nonneg hTh.le (add_nonneg zero_le_one
                    (Finset.sum_nonneg fun j _ => abs_nonneg _))) hlam.le
                have hl : ∀ u ∈ U, ∀ v ∈ U, |G (V n) i u - G (V n) i v| ≤
                    Theta * (1 + ∑ j, |V n j|) / lam * ‖u - v‖ := by
                  intro u hu v hv
                  rw [hG, hG, ← sub_div, abs_div, abs_of_pos hlam, div_mul_eq_mul_div]
                  refine div_le_div_of_nonneg_right ?_ hlam.le
                  have e1 := hflip 0 le_rfl i u hu v hv
                  have e2 : |q u i ⬝ᵥ V n - q v i ⬝ᵥ V n| ≤ ∑ j, Theta * ‖u - v‖ * |V n j| := by
                    rw [← sub_dotProduct]
                    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                    refine Finset.sum_le_sum fun j _ => ?_
                    rw [abs_mul]
                    exact mul_le_mul_of_nonneg_right (hqlip i j u hu v hv) (abs_nonneg _)
                  rw [← Finset.mul_sum] at e2
                  rw [add_sub_add_comm]
                  refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
                  rw [mul_add, mul_one, add_mul, mul_right_comm]
                have h1 := hC _ _ hp hl
                have h2 := (h6a (V n) i).2.2.2.2.2.1
                rw [← hpolg n] at h2
                rw [h2, abs_neg]
                exact h1
              obtain ⟨M0, hM0⟩ := L4 h hh.1 B0 hB0n hB0b hB0s hB0t
              obtain ⟨hδs, hδt⟩ := L3 δ h31.discount h31.integrable_delta h hh.1
              obtain ⟨M1', hM1'⟩ := L4 h hh.1 δ hδ0 (fun T => ⟨1, fun s hs _ => hδ1 s hs⟩) hδs hδt
              obtain ⟨M1, hM10, hM1⟩ : ∃ M1 : ℝ, 0 ≤ M1 ∧ ∀ n, h n * ∑' k : ℕ,
                  δ ((1 + (k : ℝ)) * h n) ≤ M1 :=
                ⟨max M1' 0, le_max_right _ _, fun n => (hM1' n).trans (le_max_left _ _)⟩
              have hshift : ∀ (c : ℝ → ℝ) n, Summable (fun k : ℕ => c ((k : ℝ) * h n)) →
                  Summable (fun k : ℕ => c ((1 + (k : ℝ)) * h n)) := by
                intro c n hc
                have := (summable_nat_add_iff 1).mpr hc
                refine this.congr fun k => ?_
                congr 1
                push_cast
                ring
              have hVb1 : ∀ n K, (∀ j, |ent U (pol n j)| ≤ K) → ∀ i, |V n i| ≤ M0 + lam * K * M1 := by
                intro n K hK i
                have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK i)
                have hs0 := hshift B0 n (hB0s n)
                have hs1 := hshift δ n (hδs n)
                have hs2 : Summable (fun k : ℕ => h n * (B0 ((1 + (k : ℝ)) * h n) +
                    lam * K * δ ((1 + (k : ℝ)) * h n))) := (hs0.add (hs1.mul_left (lam * K))).mul_left (h n)
                have hL0 := L0 d (h n • Qbar q (pol n) + 1) (hst0 n _ (hrel n)) (hst1 n _ (hrel n))
                rw [hV, hVd]
                have hb : ∀ k : ℕ, ‖(((h n • Qbar q (pol n) + 1) ^ k) *ᵥ (fun j => h n *
                  (fbarCT f (pol n j) ((1 + (k : ℝ)) * h n) j + lam * δ ((1 + (k : ℝ)) * h n) *
                    ent U (pol n j)))) i‖ ≤ h n * (B0 ((1 + (k : ℝ)) * h n) +
                    lam * K * δ ((1 + (k : ℝ)) * h n)) := by
                  intro k
                  rw [Real.norm_eq_abs]
                  apply (hL0 k).2
                  intro j
                  rw [abs_mul, abs_of_pos (hhpos n)]
                  apply mul_le_mul_of_nonneg_left _ (hhpos n).le
                  have hs : 0 ≤ (1 + (k:ℝ)) * h n := mul_nonneg
                    (add_nonneg zero_le_one (Nat.cast_nonneg k)) (hhpos n).le
                  have h1 := hfbd (pol n) (hrel n) _ hs j
                  have h2 : |lam * δ ((1 + (k:ℝ)) * h n) * ent U (pol n j)| ≤
                      lam * K * δ ((1 + (k:ℝ)) * h n) := by
                    rw [abs_mul, abs_mul, abs_of_nonneg (hδ0 _ hs), abs_of_pos hlam]
                    have := mul_le_mul_of_nonneg_left (hK j) (mul_nonneg hlam.le (hδ0 _ hs))
                    rwa [mul_right_comm lam K]
                  exact (abs_add_le _ _).trans (add_le_add h1 h2)
                have e1 := tsum_of_norm_bounded hs2.hasSum hb
                rw [Real.norm_eq_abs] at e1
                refine e1.trans ?_
                rw [tsum_mul_left, Summable.tsum_add hs0 (hs1.mul_left _), tsum_mul_left, mul_add]
                have e2 := hM0 n
                have e3 := mul_le_mul_of_nonneg_left (hM1 n) (mul_nonneg hlam.le hK0)
                have e4 : h n * (lam * K * ∑' k : ℕ, δ ((1 + (k:ℝ)) * h n)) =
                  lam * K * (h n * ∑' k : ℕ, δ ((1 + (k:ℝ)) * h n)) := by ring
                rw [e4]
                exact add_le_add e2 e3
              obtain ⟨Y0, hY0⟩ : ∃ Y0, ∀ n, ∑ j, |V n j| ≤ Y0 := by
                have hdR : (0:ℝ) ≤ d := Nat.cast_nonneg _
                have hD : (0:ℝ) < 2 * (d * M1 * Theta + 1) := mul_pos two_pos
                  (add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg hdR hM10) hTh.le) one_pos)
                obtain ⟨C, hC⟩ := hentb (1 / (2 * (d * M1 * Theta + 1))) (one_div_pos.mpr hD)
                refine ⟨2 * (d * (M0 + lam * M1 * C) + 1), fun n => ?_⟩
                obtain ⟨Y, hY⟩ : ∃ Y, Y = ∑ j, |V n j| := ⟨_, rfl⟩
                have hYn : 0 ≤ Y := hY ▸ Finset.sum_nonneg fun j _ => abs_nonneg _
                have h1 := hVb1 n _ (hC n)
                have h2 : ∑ j, |V n j| ≤ ∑ j : Fin d, (M0 + lam * (C + 1 / (2 * (d * M1 * Theta + 1)) *
                  (Theta * (1 + ∑ j, |V n j|) / lam)) * M1) := Finset.sum_le_sum fun j _ => h1 j
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hY] at h2
                rw [← hY]
                have h3 : (d:ℝ) * (M0 + lam * (C + 1 / (2 * (d * M1 * Theta + 1)) *
                  (Theta * (1 + Y) / lam)) * M1) = d * (M0 + lam * M1 * C) +
                    (d * M1 * Theta) / (2 * (d * M1 * Theta + 1)) * (1 + Y) := by
                  have e1 : lam * (C + 1 / (2 * (d * M1 * Theta + 1)) * (Theta * (1 + Y) / lam)) =
                      lam * C + 1 / (2 * (d * M1 * Theta + 1)) * (Theta * (1 + Y)) := by
                    rw [mul_add, mul_left_comm, mul_div_cancel₀ _ hlam.ne']
                  rw [e1, div_eq_mul_one_div (d * M1 * Theta)]
                  ring
                rw [h3] at h2
                have h4 : (d * M1 * Theta) / (2 * (d * M1 * Theta + 1)) ≤ 1/2 := by
                  rw [div_le_iff₀ hD]
                  linarith only
                have h5 := mul_le_mul_of_nonneg_right h4 (add_nonneg zero_le_one hYn : (0:ℝ) ≤ 1 + Y)
                linarith only [h2, h5]
              have hVle : ∀ n j, |V n j| ≤ Y0 := fun n j =>
                (Finset.single_le_sum (f := fun j => |V n j|) (fun _ _ => abs_nonneg _)
                  (Finset.mem_univ j)).trans (hY0 n)
              have hY00 : 0 ≤ Y0 := (abs_nonneg _).trans (hVle 0 ⟨0, hd⟩)
              obtain ⟨y, -, φ, hφ, hφy⟩ := tendsto_subseq_of_bounded
                (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := Y0)) (x := V) (fun n => by
                  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hY00]
                  exact fun j => hVle n j)
              have hGb : ∃ C, ∀ n i, ∀ u ∈ U, |G (V n) i u| ≤ C := by
                have hq : ∀ i j, ∃ C, ∀ u ∈ U, ‖q u i j‖ ≤ C := fun i j =>
                  hcpt.exists_bound_of_continuousOn (hqcont i j)
                choose Cq hCq using hq
                refine ⟨(B0 0 + ∑ i, ∑ j, |Cq i j| * Y0) / lam, fun n i u hu => ?_⟩
                rw [hG, abs_div, abs_of_pos hlam]
                apply div_le_div_of_nonneg_right _ hlam.le
                refine (abs_add_le _ _).trans (add_le_add (hB0f 0 le_rfl i u hu) ?_)
                have e1 : |q u i ⬝ᵥ V n| ≤ ∑ j, |Cq i j| * Y0 := by
                  simp only [dotProduct]
                  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                  apply Finset.sum_le_sum
                  intro j _
                  rw [abs_mul]
                  exact mul_le_mul ((hCq i j u hu).trans (le_abs_self _)) (hVle n j) (abs_nonneg _)
                    (abs_nonneg _)
                refine e1.trans ?_
                exact Finset.single_le_sum (f := fun i => ∑ j, |Cq i j| * Y0)
                  (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) hY00)
                  (Finset.mem_univ i)
              obtain ⟨CG, hCG⟩ := hGb
              have h11 := fun i => L11 ℓ U hcpt hvol (fun k => G (V (φ k)) i) (G y i) CG
                (fun k => hGcont _ _) (hGcont _ _) (fun k u hu => hCG _ i u hu) (fun u hu => by
                  simp only [hG]
                  refine Tendsto.div_const (tendsto_const_nhds.add ?_) _
                  simp only [dotProduct]
                  refine tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul ?_
                  exact (tendsto_pi_nhds.mp hφy) j)
              have hw : ∀ i, ∀ g : A ℓ → ℝ, ContinuousOn g U → Tendsto (fun k => ∫ u, g u ∂(pol (φ k) i))
                  atTop (𝓝 (∫ u, g u ∂(gibbsCtrlCT U q f lam y i))) := by
                intro i g hg
                have e1 := (h11 i).2.1 g hg
                rw [(h6a y i).2.2.2.2.2.2.1 g]
                refine e1.congr fun k => ?_
                rw [hpolg (φ k), (h6a (V (φ k)) i).2.2.2.2.2.2.1 g]
              have hent : ∀ i, Tendsto (fun k => ent U (pol (φ k) i)) atTop
                  (𝓝 (ent U (gibbsCtrlCT U q f lam y i))) := by
                intro i
                have e1 := (h11 i).2.2
                rw [(h6a y i).2.2.2.2.2.1]
                refine e1.congr fun k => ?_
                rw [hpolg (φ k), (h6a (V (φ k)) i).2.2.2.2.2.1]
              obtain ⟨K, hK⟩ : ∃ K, ∀ n j, |ent U (pol n j)| ≤ K := by
                obtain ⟨C, hC⟩ := hentb 1 one_pos
                refine ⟨C + 1 * (Theta * (1 + Y0) / lam), fun n j => (hC n j).trans ?_⟩
                have e1 : Theta * (1 + ∑ j, |V n j|) / lam ≤ Theta * (1 + Y0) / lam :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right (hY0 n) 1)
                    hTh.le) hlam.le
                rw [one_mul, one_mul]
                exact add_le_add_right e1 C
              have hlim := hM φ hφ pol (gibbsCtrlCT U q f lam y) hrel (hgreg y).1 hw lam
                (fun n j => ent U (pol n j)) (fun j => ent U (gibbsCtrlCT U q f lam y j)) K hK hent
              have hyJ : y = Jlamt U q f δ lam (gibbsCtrlCT U q f lam y) := by
                funext i
                have e1 := hlim.2.2 i
                have e2 := (tendsto_pi_nhds.mp hφy) i
                refine tendsto_nhds_unique e2 ?_
                refine Tendsto.congr (fun k => ?_) e1
                simp only [Function.comp, hV]
              refine ⟨φ, hφ, gibbsCtrlCT U q f lam y, hgreg y, ?_, hgreg y, ?_⟩
              · intro i
                have e1 : ∀ᵐ u ∂(volume.restrict U), ∀ k, density U (pol (φ k) i) u =
                    Real.exp (G (V (φ k)) i u) / ∫ v in U, Real.exp (G (V (φ k)) i v) := by
                  rw [ae_all_iff]
                  intro k
                  rw [hpolg (φ k)]
                  exact (h6a (V (φ k)) i).2.2.2.2.1
                filter_upwards [e1, (h6a y i).2.2.2.2.1, ae_restrict_mem hUm] with u hu1 hu2 hu3
                rw [hu2]
                simp only [hu1]
                exact (h11 i).1 u hu3
              · intro i pol' hpol' η hη
                have hrw := hrew (gibbsCtrlCT U q f lam y) (hgreg y).1 lam
                  (fun j => ent U (gibbsCtrlCT U q f lam y j))
                have hrw' := hrew pol' hpol'.1 lam (fun j => ent U (pol' j))
                refine L8 d (Qbar q (gibbsCtrlCT U q f lam y)) (Qbar q pol')
                  (rewLam U f δ lam (gibbsCtrlCT U q f lam y)) (rewLam U f δ lam pol')
                  (fun j => (hrw j).1) (fun j => (hrw' j).1) (fun j => (hrw j).2) hlim.1
                  (Jlamt U q f δ lam (gibbsCtrlCT U q f lam y))
                  (Vlamt U q f δ lam (gibbsCtrlCT U q f lam y)) rfl rfl i ?_ η hη
                rw [← hyJ]
                simp only [rewLam, h31.discount.zero, mul_one]
                rw [hGint2 _ hpol'.1, hGint2 _ (hgreg y).1, (h6a y i).2.2.2.2.2.2.2]
                apply mul_le_mul_of_nonneg_left _ hlam.le
                exact (L6b ℓ U hcpt hvol (G y i) (hGcont _ _) (pol' i) (hpol'.1 i).1 (hpol'.1 i).2
                  (hpol'.2 i).1 (hpol'.2 i).2).1
            · intro pol hpol
              have hrel : ∀ n, IsRelaxed U (pol n) := fun n => (hpol n).1
              obtain ⟨φ, hφ, polInf, hInf, hw⟩ := L9 d ℓ U hcpt pol hrel
              refine ⟨φ, hφ, polInf, hInf, fun i g => hw i g g.continuous.continuousOn, hInf, ?_⟩
              intro i pol' hpol' η hη
              have hlim := hM φ hφ pol polInf hrel hInf hw 0 (fun _ _ => 0) (fun _ => 0) 0 (by simp)
                (fun j => tendsto_const_nhds)
              have hrw := fun j => hrew polInf hInf 0 (fun _ => 0) j
              have hrw' := fun j => hrew pol' hpol' 0 (fun _ => 0) j
              simp only [mul_zero, add_zero] at hrw hrw'
              have hJ : ∀ i, Tendsto (fun k => Vd (φ k) (pol (φ k)) 0 (fun _ => 0) i) atTop
                  (𝓝 (Jt q f polInf i)) := by
                intro i
                have e1 := hlim.2.2 i
                simp only [mul_zero, add_zero] at e1
                exact e1
              refine L8 d (Qbar q polInf) (Qbar q pol')
                  (rew f polInf) (rew f pol')
                  (fun j => (hrw j).1) (fun j => (hrw' j).1) (fun j => (hrw j).2) hlim.1
                  (Jt q f polInf) (Vt q f polInf) rfl rfl i ?_ η hη
              have hineq : ∀ k, fbarCT f (pol' i) 0 i +
                  (Qbar q pol' *ᵥ Vd (φ k) (pol (φ k)) 0 (fun _ => 0)) i ≤
                  fbarCT f (pol (φ k) i) 0 i +
                  (Qbar q (pol (φ k)) *ᵥ Vd (φ k) (pol (φ k)) 0 (fun _ => 0)) i := by
                intro k
                have h1 := (hpol (φ k)).2 i pol' hpol'
                have h2 := hdisc (φ k) (pol (φ k)) pol' (hrel _) hpol' 0 (fun _ => 0) i (by
                  simp only [mul_zero, add_zero]
                  exact h1)
                simpa using h2
              have hlhs : Tendsto (fun k => fbarCT f (pol' i) 0 i +
                  (Qbar q pol' *ᵥ Vd (φ k) (pol (φ k)) 0 (fun _ => 0)) i) atTop
                  (𝓝 (fbarCT f (pol' i) 0 i + (Qbar q pol' *ᵥ Jt q f polInf) i)) := by
                refine tendsto_const_nhds.add ?_
                simp only [Matrix.mulVec, dotProduct]
                exact tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hJ j)
              have hrhs : Tendsto (fun k => fbarCT f (pol (φ k) i) 0 i +
                  (Qbar q (pol (φ k)) *ᵥ Vd (φ k) (pol (φ k)) 0 (fun _ => 0)) i) atTop
                  (𝓝 (fbarCT f (polInf i) 0 i + (Qbar q polInf *ᵥ Jt q f polInf) i)) := by
                refine (hw i _ (hfcont 0 le_rfl i)).add ?_
                simp only [Matrix.mulVec, dotProduct]
                refine tendsto_finsetSum _ fun j _ => Tendsto.mul ?_ (hJ j)
                exact hw i _ (hqcont i j)
              exact le_of_tendsto_of_tendsto' hlhs hrhs hineq
