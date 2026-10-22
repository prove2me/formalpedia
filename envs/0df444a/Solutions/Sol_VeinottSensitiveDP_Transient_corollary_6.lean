-- Prove2me | solution 1 for VeinottSensitiveDP.Transient.corollary_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T22:12:09.877528+00:00
-- url     : https://prove2.me/submissions/50e92132-269c-4e8f-a6f0-4d6423b41927

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

set_option autoImplicit false

namespace P2MVeinottC6

open Matrix Filter Topology VeinottSensitiveDP.Transient

variable {St : Type} [Fintype St] [DecidableEq St] {A : St → Type}

lemma mulVec_mono_of_nonneg {M : Matrix St St ℝ} (hM : ∀ i j, 0 ≤ M i j) {x y : St → ℝ}
    (h : x ≤ y) : M *ᵥ x ≤ M *ᵥ y := by
  intro i
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hM i j)

lemma mulVec_nonneg_of_nonneg {M : Matrix St St ℝ} (hM : ∀ i j, 0 ≤ M i j) {x : St → ℝ}
    (h : 0 ≤ x) : 0 ≤ M *ᵥ x := by
  have := mulVec_mono_of_nonneg hM h
  simpa using this

lemma Pmat_nonneg (D : Program St A) (g : DecisionRule St A) : ∀ i j, 0 ≤ D.Pmat g i j :=
  fun i j => by simp only [Program.Pmat, Matrix.of_apply]; exact D.p_nonneg _ _ _

lemma PN_nonneg (D : Program St A) (π : Policy St A) : ∀ N i j, 0 ≤ D.PN N π i j := by
  intro N
  induction N with
  | zero =>
    intro i j
    simp only [Program.PN]
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  | succ N ih =>
    intro i j
    simp only [Program.PN, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (Pmat_nonneg D _ k j)

lemma PN_stationary (D : Program St A) (g : DecisionRule St A) (N : ℕ) :
    D.PN N (stationary g) = D.Pmat g ^ N := by
  induction N with
  | zero => simp [Program.PN]
  | succ N ih => simp [Program.PN, ih, stationary, pow_succ]

lemma partial_le (D : Program St A) (u : St → ℝ)
    (hu : ∀ g : DecisionRule St A, D.rvec g + D.Pmat g *ᵥ u ≤ u) (π : Policy St A) :
    ∀ N, (∑ n ∈ Finset.range N, D.PN n π *ᵥ D.rvec (π n)) + D.PN N π *ᵥ u ≤ u := by
  intro N
  induction N with
  | zero => simp [Program.PN]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 : D.PN (N + 1) π *ᵥ u = D.PN N π *ᵥ (D.Pmat (π N) *ᵥ u) := by
      simp only [Program.PN]
      rw [Matrix.mulVec_mulVec]
    have h2 : D.PN N π *ᵥ D.rvec (π N) + D.PN N π *ᵥ (D.Pmat (π N) *ᵥ u) ≤ D.PN N π *ᵥ u := by
      rw [← Matrix.mulVec_add]
      exact mulVec_mono_of_nonneg (PN_nonneg D π N) (hu (π N))
    calc (∑ n ∈ Finset.range N, D.PN n π *ᵥ D.rvec (π n)) + D.PN N π *ᵥ D.rvec (π N)
          + D.PN (N + 1) π *ᵥ u
        = (∑ n ∈ Finset.range N, D.PN n π *ᵥ D.rvec (π n))
          + (D.PN N π *ᵥ D.rvec (π N) + D.PN N π *ᵥ (D.Pmat (π N) *ᵥ u)) := by
          rw [h1]; abel
      _ ≤ (∑ n ∈ Finset.range N, D.PN n π *ᵥ D.rvec (π n)) + D.PN N π *ᵥ u :=
          add_le_add le_rfl h2
      _ ≤ u := ih

lemma hasSum_mulVec {f : ℕ → Matrix St St ℝ} {T : Matrix St St ℝ} (h : HasSum f T)
    (v : St → ℝ) : HasSum (fun n => f n *ᵥ v) (T *ᵥ v) := by
  have := h.map (Matrix.mulVec.addMonoidHomLeft v)
    (continuous_id.matrix_mulVec continuous_const)
  exact this

lemma tsum_pow_eq (P : Matrix St St ℝ) (hs : Summable fun N => P ^ N) :
    (∑' N, P ^ N) = 1 + P * ∑' N, P ^ N := by
  conv_lhs => rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, pow_succ']
  rw [hs.tsum_mul_left]

lemma tsum_pow_eq' (P : Matrix St St ℝ) (hs : Summable fun N => P ^ N) :
    (∑' N, P ^ N) = 1 + (∑' N, P ^ N) * P := by
  conv_lhs => rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, pow_succ]
  rw [hs.tsum_mul_right]

lemma pow_nonneg_entries (P : Matrix St St ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ N i j, 0 ≤ (P ^ N) i j := by
  intro N
  induction N with
  | zero => intro i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
  | succ N ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hP k j)

lemma tsum_pow_nonneg (P : Matrix St St ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hs : Summable fun N => P ^ N) : ∀ i j, 0 ≤ (∑' N, P ^ N) i j := by
  intro i j
  have h1 := Pi.hasSum.1 (Pi.hasSum.1 hs.hasSum i) j
  exact h1.nonneg fun N => pow_nonneg_entries P hP N i j

lemma V_stationary (D : Program St A) (g : DecisionRule St A)
    (hs : Summable fun N => D.Pmat g ^ N) :
    D.V (stationary g) = (∑' N, D.Pmat g ^ N) *ᵥ D.rvec g := by
  have h := (hasSum_mulVec hs.hasSum (D.rvec g)).tsum_eq
  rw [← h]
  unfold Program.V
  congr 1
  funext N
  rw [PN_stationary]
  rfl

lemma summable_stat (D : Program St A) (g : DecisionRule St A)
    (hT : D.IsTransient (stationary g)) : Summable fun N => D.Pmat g ^ N := by
  have := hT
  unfold Program.IsTransient at this
  simpa [PN_stationary] using this

lemma rowval_congr (D : Program St A) (u : St → ℝ) (k k' : DecisionRule St A) (s : St)
    (hks : k s = k' s) :
    (D.rvec k + D.Pmat k *ᵥ u) s = (D.rvec k' + D.Pmat k' *ᵥ u) s := by
  simp [Program.rvec, Program.Pmat, mulVec, dotProduct, hks]

lemma exists_opt (D : Program St A) [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
    [∀ s, Nonempty (A s)] (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    ∃ f : DecisionRule St A, ∀ g : DecisionRule St A,
      D.rvec g + D.Pmat g *ᵥ D.V (stationary f) ≤ D.V (stationary f) := by
  obtain ⟨f, -, hfmax⟩ := Finset.exists_max_image (Finset.univ : Finset (DecisionRule St A))
    (fun f => ∑ s, D.V (stationary f) s) Finset.univ_nonempty
  refine ⟨f, fun g => ?_⟩
  by_contra hneg
  rw [Pi.le_def] at hneg
  push_neg at hneg
  obtain ⟨s0, hs0⟩ := hneg
  set u := D.V (stationary f) with hu_def
  have hsf := summable_stat D f (hT f)
  -- fixed point
  have hfix : u = D.rvec f + D.Pmat f *ᵥ u := by
    rw [hu_def, V_stationary D f hsf]
    conv_lhs => rw [tsum_pow_eq _ hsf]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  let h : DecisionRule St A := Function.update f s0 (g s0)
  set δ := D.rvec h + D.Pmat h *ᵥ u - u with hδ
  have hδ0 : ∀ s, s ≠ s0 → δ s = 0 := by
    intro s hs
    have hk : h s = f s := by simp [h, Function.update_of_ne hs]
    have := rowval_congr D u h f s hk
    rw [hδ, Pi.sub_apply, this]
    have h2 := congrFun hfix s
    linarith
  have hδs0 : 0 < δ s0 := by
    have hk : h s0 = g s0 := by simp [h]
    have := rowval_congr D u h g s0 hk
    rw [hδ, Pi.sub_apply, this]
    linarith
  have hδnn : 0 ≤ δ := by
    intro s
    by_cases hs : s = s0
    · subst hs; exact hδs0.le
    · simp [hδ0 s hs]
  have hsh := summable_stat D h (hT h)
  set T := ∑' N, D.Pmat h ^ N with hT_def
  have hTnn := tsum_pow_nonneg (D.Pmat h) (Pmat_nonneg D h) hsh
  have hT1 : T * (1 - D.Pmat h) = 1 := by
    have := tsum_pow_eq' (D.Pmat h) hsh
    rw [mul_sub, mul_one]
    rw [← hT_def] at this
    calc T - T * D.Pmat h = (1 + T * D.Pmat h) - T * D.Pmat h := by rw [← this]
      _ = 1 := by abel
  have hVh : D.V (stationary h) = u + T *ᵥ δ := by
    rw [V_stationary D h hsh, ← hT_def]
    have hr : D.rvec h = (1 - D.Pmat h) *ᵥ u + δ := by
      rw [hδ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hr, Matrix.mulVec_add, Matrix.mulVec_mulVec, hT1, Matrix.one_mulVec]
  have hTδ : δ ≤ T *ᵥ δ := by
    have := tsum_pow_eq (D.Pmat h) hsh
    rw [← hT_def] at this
    have hPT : ∀ i j, 0 ≤ (D.Pmat h * T) i j := by
      intro i j
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (Pmat_nonneg D h i k) (hTnn k j)
    have hnn := mulVec_nonneg_of_nonneg hPT hδnn
    calc δ = δ + 0 := (add_zero _).symm
      _ ≤ δ + (D.Pmat h * T) *ᵥ δ := add_le_add le_rfl hnn
      _ = T *ᵥ δ := by
          conv_rhs => rw [this]
          rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hle := hfmax h (Finset.mem_univ _)
  rw [hVh] at hle
  have hsum1 : ∑ s, (u + T *ᵥ δ) s ≥ ∑ s, u s + δ s0 := by
    have e : ∑ s, (u + T *ᵥ δ) s = ∑ s, u s + ∑ s, (T *ᵥ δ) s := by
      simp [Finset.sum_add_distrib]
    rw [e]
    have h3 : δ s0 ≤ ∑ s, (T *ᵥ δ) s :=
      le_trans (hTδ s0) (Finset.single_le_sum (fun s _ => le_trans (hδnn s) (hTδ s))
        (Finset.mem_univ s0))
    linarith
  linarith

/-- The same program with every reward equal to one. -/
def unitProg (D : Program St A) : Program St A := ⟨fun _ _ => 1, D.p, D.p_nonneg⟩

lemma unitProg_PN (D : Program St A) (π : Policy St A) (N : ℕ) :
    (unitProg D).PN N π = D.PN N π := by
  induction N with
  | zero => simp [Program.PN]
  | succ N ih => simp only [Program.PN, ih]; rfl

lemma all_transient (D : Program St A) [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
    [∀ s, Nonempty (A s)] (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g))
    (π : Policy St A) : D.IsTransient π := by
  have hT1 : ∀ g : DecisionRule St A, (unitProg D).IsTransient (stationary g) := by
    intro g
    have := hT g
    unfold Program.IsTransient at this ⊢
    simpa [unitProg_PN] using this
  obtain ⟨f1, hf1⟩ := exists_opt (unitProg D) hT1
  set w := (unitProg D).V (stationary f1) with hw
  have hr1 : ∀ k : DecisionRule St A, (unitProg D).rvec k = fun _ => 1 := by
    intro k; funext s; simp [Program.rvec, unitProg]
  have hwnn : 0 ≤ w := by
    rw [hw]
    unfold Program.V
    refine tsum_nonneg fun N => ?_
    rw [hr1]
    exact mulVec_nonneg_of_nonneg (PN_nonneg _ _ N) (fun _ => zero_le_one)
  have hpl := partial_le (unitProg D) w hf1 π
  have hbound : ∀ N i j, ∑ n ∈ Finset.range N, D.PN n π i j ≤ w i := by
    intro N i j
    have h1 := hpl N
    have h2 : 0 ≤ (unitProg D).PN N π *ᵥ w :=
      mulVec_nonneg_of_nonneg (PN_nonneg _ _ N) hwnn
    have h3 := (show (∑ n ∈ Finset.range N, (unitProg D).PN n π *ᵥ
        (unitProg D).rvec (π n)) ≤ w from le_trans (le_add_of_nonneg_right h2) h1) i
    simp only [Finset.sum_apply, hr1, unitProg_PN] at h3
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) h3
    simp only [mulVec, dotProduct, mul_one]
    exact Finset.single_le_sum (fun k _ => PN_nonneg D π n i k) (Finset.mem_univ j)
  unfold Program.IsTransient
  refine Pi.summable.2 fun i => Pi.summable.2 fun j => ?_
  exact summable_of_sum_range_le (fun n => PN_nonneg D π n i j) (hbound · i j)

theorem main (D : Program St A) [Nonempty St] [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
    [∀ s, Nonempty (A s)] (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    ∃ f : DecisionRule St A, ∀ π : Policy St A, D.V π ≤ D.V (stationary f) := by
  obtain ⟨f, hf⟩ := exists_opt D hT
  refine ⟨f, fun π => ?_⟩
  have hπ := all_transient D hT π
  set u := D.V (stationary f)
  have hent : ∀ i j, Summable fun n => D.PN n π i j := fun i j =>
    Pi.summable.1 (Pi.summable.1 hπ i) j
  set C : ℝ := ∑ s, ∑ a, |D.r s a| with hC
  have hrC : ∀ (k : DecisionRule St A) j, |D.rvec k j| ≤ C := by
    intro k j
    simp only [Program.rvec]
    calc |D.r j (k j)| ≤ ∑ a, |D.r j a| :=
          Finset.single_le_sum (f := fun a => |D.r j a|) (fun a _ => abs_nonneg _)
            (Finset.mem_univ (k j))
      _ ≤ C := Finset.single_le_sum (f := fun s => ∑ a, |D.r s a|)
            (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ j)
  have hsum : Summable fun n => D.PN n π *ᵥ D.rvec (π n) := by
    refine Pi.summable.2 fun i => ?_
    simp only [mulVec, dotProduct]
    refine summable_sum fun j _ => ?_
    refine ((hent i j).mul_right C).of_norm_bounded ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (PN_nonneg D π n i j)]
    exact mul_le_mul_of_nonneg_left (hrC (π n) j) (PN_nonneg D π n i j)
  have hlim1 : Tendsto (fun N => ∑ n ∈ Finset.range N, D.PN n π *ᵥ D.rvec (π n)) atTop
      (𝓝 (D.V π)) := hsum.hasSum.tendsto_sum_nat
  have hlim2 : Tendsto (fun N => D.PN N π *ᵥ u) atTop (𝓝 0) := by
    have := ((continuous_id.matrix_mulVec continuous_const :
      Continuous fun M : Matrix St St ℝ => M *ᵥ u).tendsto 0).comp hπ.tendsto_atTop_zero
    simpa [Function.comp_def] using this
  have hlim := hlim1.add hlim2
  rw [add_zero] at hlim
  exact le_of_tendsto' hlim (partial_le D u hf π)

end P2MVeinottC6

open Matrix VeinottSensitiveDP.Transient in
theorem solution {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
    [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (D : Program St A)
    (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    ∃ f : DecisionRule St A, ∀ π : Policy St A, D.V π ≤ D.V (stationary f) := by
  exact P2MVeinottC6.main D hT
