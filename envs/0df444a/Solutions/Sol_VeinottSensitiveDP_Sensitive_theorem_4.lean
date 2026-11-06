-- Prove2me | solution 1 for VeinottSensitiveDP.Sensitive.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:21:19.617334+00:00
-- url     : https://prove2.me/submissions/aa798510-7210-4d06-b4e6-5631ef603089

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
import Theorems.Thm_VeinottSensitiveDP_Sensitive_display_15
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace VeinottT4Aux
open VeinottSensitiveDP.Sensitive

section Gen
variable {St : Type} [Fintype St] [DecidableEq St]

def NonnegM (B : Matrix St St ℝ) : Prop := ∀ i j, 0 ≤ B i j

lemma mulVec_mono {B : Matrix St St ℝ} (hB : NonnegM B) {x y : St → ℝ} (h : ∀ t, x t ≤ y t)
    (s : St) : (B *ᵥ x) s ≤ (B *ᵥ y) s := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (hB s t)

lemma mulVec_nonneg' {B : Matrix St St ℝ} (hB : NonnegM B) {x : St → ℝ} (h : ∀ t, 0 ≤ x t)
    (s : St) : 0 ≤ (B *ᵥ x) s := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (hB s t) (h t)

lemma mulVec_abs_le {B : Matrix St St ℝ} (hB : NonnegM B) (x : St → ℝ) (s : St) :
    |(B *ᵥ x) s| ≤ (B *ᵥ fun t => |x t|) s := by
  simp only [mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [abs_mul, abs_of_nonneg (hB s t)]

lemma mulVec_wbound {B : Matrix St St ℝ} (hB : NonnegM B) {w x : St → ℝ} {K c : ℝ}
    (hK : 0 ≤ K) (hx : ∀ t, |x t| ≤ K * w t) (s : St) (hBw : (B *ᵥ w) s ≤ c * w s) :
    |(B *ᵥ x) s| ≤ K * (c * w s) := by
  calc |(B *ᵥ x) s| ≤ (B *ᵥ fun t => |x t|) s := mulVec_abs_le hB x s
    _ ≤ (B *ᵥ (K • w)) s := mulVec_mono hB (fun t => by simpa using hx t) s
    _ = K * (B *ᵥ w) s := by rw [Matrix.mulVec_smul]; rfl
    _ ≤ K * (c * w s) := mul_le_mul_of_nonneg_left hBw hK

/-- weighted bound for a solution of `x = β(b + Px)`. -/
lemma fixed_bound [Nonempty St] {P : Matrix St St ℝ} (hP : NonnegM P) {w : St → ℝ}
    (hw : ∀ s, 0 < w s) {lam : ℝ} (hPw : ∀ s, (P *ᵥ w) s ≤ lam * w s) {β : ℝ} (hβ : 0 < β)
    (hβl : β * lam < 1) {b x : St → ℝ} {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |b s| ≤ K * w s)
    (hx : x = β • (b + P *ᵥ x)) :
    ∀ s, |x s| ≤ β * K / (1 - β * lam) * w s := by
  obtain ⟨s0, -, hs0⟩ := Finset.exists_max_image Finset.univ (fun s => |x s| / w s)
    Finset.univ_nonempty
  set m := |x s0| / w s0 with hm_def
  have hm0 : 0 ≤ m := div_nonneg (abs_nonneg _) (hw s0).le
  have hxm : ∀ t, |x t| ≤ m * w t := fun t => by
    have := hs0 t (Finset.mem_univ t); rwa [div_le_iff₀ (hw t)] at this
  have key : |x s0| ≤ β * K * w s0 + β * lam * (m * w s0) := by
    have e : x s0 = β * (b s0 + (P *ᵥ x) s0) := by
      conv_lhs => rw [hx]
      simp
    rw [e, abs_mul, abs_of_pos hβ]
    have h1 : |(P *ᵥ x) s0| ≤ m * (lam * w s0) := mulVec_wbound hP hm0 hxm s0 (hPw s0)
    calc β * |b s0 + (P *ᵥ x) s0| ≤ β * (|b s0| + |(P *ᵥ x) s0|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hβ.le
      _ ≤ β * (K * w s0 + m * (lam * w s0)) := by gcongr; exact hb s0
      _ = _ := by ring
  have h1m : 0 < 1 - β * lam := by linarith
  have hm : m * (1 - β * lam) ≤ β * K := by
    have hxs : |x s0| = m * w s0 := by rw [hm_def, div_mul_cancel₀ _ (hw s0).ne']
    rw [hxs] at key
    have hw0 := hw s0
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos (sub_pos.mpr hcon) hw0]
  intro s
  calc |x s| ≤ m * w s := hxm s
    _ ≤ β * K / (1 - β * lam) * w s := by
        apply mul_le_mul_of_nonneg_right _ (hw s).le
        rw [le_div_iff₀ h1m]; exact hm

/-- shift identity for a vector series with `F (N+1) = B F N`. -/
lemma hasSum_fix (B : Matrix St St ℝ) {F : ℕ → St → ℝ} {a : St → ℝ} (hF : HasSum F a)
    (hrec : ∀ N, F (N + 1) = B *ᵥ F N) : a = F 0 + B *ᵥ a := by
  have h1 : HasSum (fun N => F (N + 1)) (a - ∑ i ∈ Finset.range 1, F i) :=
    (hasSum_nat_add_iff' 1).mpr hF
  have hc : Continuous fun x : St → ℝ => B *ᵥ x := continuous_const.matrix_mulVec continuous_id
  let φ : (St → ℝ) →+ (St → ℝ) :=
    { toFun := fun x => B *ᵥ x, map_zero' := Matrix.mulVec_zero B,
      map_add' := fun x y => Matrix.mulVec_add B x y }
  have h2 : HasSum (fun N => B *ᵥ F N) (B *ᵥ a) := hF.map φ hc
  simp only [hrec] at h1
  have := h1.unique h2
  simp at this
  rw [← this]; abel

end Gen

section ModelSec
variable {St : Type} [Fintype St] [DecidableEq St] {A : St → Type}
variable (M : Model St A)

lemma P_nonneg (g : DecisionRule A) : NonnegM (M.P g) := fun i j => M.p_nonneg i (g i) j

lemma P_sub (g : DecisionRule A) : IsSubstochastic (M.P g) :=
  ⟨fun i j => M.p_nonneg _ _ _, fun i => M.p_rowsum_le_one i (g i)⟩

lemma P_one_le (g : DecisionRule A) (s : St) : (M.P g *ᵥ fun _ => (1:ℝ)) s ≤ 1 * 1 := by
  have := M.p_rowsum_le_one s (g s)
  simpa [mulVec, dotProduct, Model.P] using this

lemma Pmat_nonneg (π : Policy A) : ∀ N, NonnegM (M.Pmat π N)
  | 0 => fun i j => by
      simp only [Model.Pmat, Matrix.one_apply]; split_ifs <;> norm_num
  | N + 1 => fun i j => by
      simp only [Model.Pmat, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (Pmat_nonneg π N i k) (M.p_nonneg _ _ _)

lemma Pmat_stationary (f : DecisionRule A) : ∀ N, M.Pmat (stationary f) N = M.P f ^ N
  | 0 => by simp [Model.Pmat]
  | N + 1 => by
      simp only [Model.Pmat, Pmat_stationary f N, pow_succ]; rfl

lemma Pmat_w {w : St → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hPw : ∀ g s, (M.P g *ᵥ w) s ≤ lam * w s) (π : Policy A) :
    ∀ N s, (M.Pmat π N *ᵥ w) s ≤ lam ^ N * w s
  | 0, s => by simp [Model.Pmat]
  | N + 1, s => by
      have e : M.Pmat π (N + 1) *ᵥ w = M.Pmat π N *ᵥ (M.P (π N) *ᵥ w) := by
        simp [Model.Pmat, Matrix.mulVec_mulVec]
      rw [e]
      calc (M.Pmat π N *ᵥ (M.P (π N) *ᵥ w)) s ≤ (M.Pmat π N *ᵥ (lam • w)) s :=
            mulVec_mono (Pmat_nonneg M π N) (fun t => by simpa using hPw (π N) t) s
        _ = lam * (M.Pmat π N *ᵥ w) s := by rw [Matrix.mulVec_smul]; rfl
        _ ≤ lam * (lam ^ N * w s) := mul_le_mul_of_nonneg_left (Pmat_w hlam hPw π N s) hlam
        _ = lam ^ (N + 1) * w s := by ring

lemma Pmat_bound {w : St → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hPw : ∀ g s, (M.P g *ᵥ w) s ≤ lam * w s) (π : Policy A) {x : St → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hx : ∀ t, |x t| ≤ K * w t) (N : ℕ) (s : St) :
    |(M.Pmat π N *ᵥ x) s| ≤ K * (lam ^ N * w s) :=
  mulVec_wbound (Pmat_nonneg M π N) hK hx s (Pmat_w M hlam hPw π N s)

/-- the test quantity for a vector `u`. -/
noncomputable def vf (ρ : ℝ) (g : DecisionRule A) (u : St → ℝ) : St → ℝ :=
  M.rv g + M.Q g *ᵥ u - ρ • u

lemma vf_local (ρ : ℝ) {g g' : DecisionRule A} (u : St → ℝ) (s : St) (h : g s = g' s) :
    vf M ρ g u s = vf M ρ g' u s := by
  simp [vf, Model.rv, Model.Q, Model.P, mulVec, dotProduct, Matrix.sub_apply, h]

lemma tele (π : Policy A) (ρ β : ℝ) (hβ : β * (1 + ρ) = 1) (u : St → ℝ) :
    ∀ N, (∑ k ∈ Finset.range N, β ^ (k + 1) • (M.Pmat π k *ᵥ M.rv (π k)))
        + β ^ N • (M.Pmat π N *ᵥ u) - u
      = ∑ k ∈ Finset.range N, β ^ (k + 1) • (M.Pmat π k *ᵥ vf M ρ (π k) u)
  | 0 => by simp [Model.Pmat]
  | N + 1 => by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← tele π ρ β hβ u N]
      have e : M.Pmat π (N + 1) *ᵥ u = M.Pmat π N *ᵥ (M.P (π N) *ᵥ u) := by
        simp [Model.Pmat, Matrix.mulVec_mulVec]
      rw [e]
      ext s
      simp only [vf, Model.Q, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      have hb : β ^ N = β ^ (N + 1) * (1 + ρ) := by rw [pow_succ, mul_assoc, hβ, mul_one]
      rw [hb]; ring


section Series
variable [Fintype (DecisionRule A)]

lemma rv_bound (g : DecisionRule A) (w : St → ℝ) (hw1 : ∀ s, 1 ≤ w s) (t : St) :
    |M.rv g t| ≤ (∑ g', ∑ t', |M.rv g' t'|) * w t := by
  have h1 : |M.rv g t| ≤ ∑ g', ∑ t', |M.rv g' t'| := by
    calc |M.rv g t| ≤ ∑ t', |M.rv g t'| :=
          Finset.single_le_sum (f := fun t' => |M.rv g t'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ t)
      _ ≤ ∑ g', ∑ t', |M.rv g' t'| :=
          Finset.single_le_sum (f := fun g' => ∑ t', |M.rv g' t'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ g)
  have h0 : 0 ≤ ∑ g', ∑ t', |M.rv g' t'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [hw1 t]

variable {w : St → ℝ} {lam : ℝ} (hw1 : ∀ s, 1 ≤ w s) (hlam0 : 0 ≤ lam)
  (hPw : ∀ g s, (M.P g *ᵥ w) s ≤ lam * w s)
include hw1 hlam0 hPw

lemma hasSumV {β : ℝ} (hβ0 : 0 < β) (hβl : β * lam < 1) (π : Policy A) :
    HasSum (fun N => β ^ (N + 1) • (M.Pmat π N *ᵥ M.rv (π N)))
      (∑' N, β ^ (N + 1) • (M.Pmat π N *ᵥ M.rv (π N))) := by
  apply Summable.hasSum
  refine Pi.summable.mpr fun s => ?_
  set Kr := ∑ g', ∑ t', |M.rv g' t'|
  have hKr : 0 ≤ Kr := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Summable.of_norm_bounded (g := fun N => (β * Kr * w s) * (β * lam) ^ N) ?_ ?_
  · exact (summable_geometric_of_lt_one (mul_nonneg hβ0.le hlam0) hβl).mul_left _
  · intro N
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
    have := Pmat_bound M hlam0 hPw π hKr (rv_bound M (π N) w hw1) N s
    calc β ^ (N + 1) * |(M.Pmat π N *ᵥ M.rv (π N)) s| ≤ β ^ (N + 1) * (Kr * (lam ^ N * w s)) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le _)
      _ = (β * Kr * w s) * (β * lam) ^ N := by ring

lemma tendsto_pow_term {β : ℝ} (hβ0 : 0 < β) (hβl : β * lam < 1) (π : Policy A)
    (u : St → ℝ) : Tendsto (fun N => β ^ N • (M.Pmat π N *ᵥ u)) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro s
  set Ku := ∑ t, |u t|
  have hKu : 0 ≤ Ku := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hu : ∀ t, |u t| ≤ Ku * w t := fun t => by
    have : |u t| ≤ Ku := Finset.single_le_sum (f := fun t => |u t|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ t)
    nlinarith [hw1 t]
  have hg : Tendsto (fun N : ℕ => (Ku * w s) * (β * lam) ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hβ0.le hlam0) hβl).const_mul
      (Ku * w s)
  refine squeeze_zero_norm (fun N => ?_) hg
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
  have := Pmat_bound M hlam0 hPw π hKu hu N s
  calc β ^ N * |(M.Pmat π N *ᵥ u) s| ≤ β ^ N * (Ku * (lam ^ N * w s)) :=
        mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le _)
    _ = (Ku * w s) * (β * lam) ^ N := by ring

lemma tendsto_vsum {ρ : ℝ} (hρ : -1 < ρ) (hβl : beta ρ * lam < 1) (π : Policy A)
    (u : St → ℝ) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, beta ρ ^ (k + 1) • (M.Pmat π k *ᵥ vf M ρ (π k) u))
      atTop (𝓝 (M.V ρ π - u)) := by
  have hβ0 : 0 < beta ρ := by unfold beta; exact inv_pos.mpr (by linarith)
  have hβ : beta ρ * (1 + ρ) = 1 := by unfold beta; exact inv_mul_cancel₀ (by linarith)
  have h1 := (hasSumV M hw1 hlam0 hPw hβ0 hβl π).tendsto_sum_nat
  have h2 := tendsto_pow_term M hw1 hlam0 hPw hβ0 hβl π u
  have h3 := (h1.add h2).sub_const u
  simp only [add_zero] at h3
  refine (h3.congr fun N => ?_)
  exact tele M π ρ (beta ρ) hβ u N

lemma V_upper {ρ : ℝ} (hρ : -1 < ρ) (hβl : beta ρ * lam < 1) (π : Policy A)
    (u : St → ℝ) {e : ℝ} (he : 0 ≤ e) (hv : ∀ g s, vf M ρ g u s ≤ e) (s : St) :
    M.V ρ π s - u s ≤ e * (beta ρ / (1 - beta ρ * lam)) * w s := by
  have hβ0 : 0 < beta ρ := by unfold beta; exact inv_pos.mpr (by linarith)
  have hq0 : 0 ≤ beta ρ * lam := mul_nonneg hβ0.le hlam0
  have h := (tendsto_pi_nhds.mp (tendsto_vsum M hw1 hlam0 hPw hρ hβl π u)) s
  refine le_of_tendsto h (Eventually.of_forall fun N => ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ k ∈ Finset.range N, beta ρ ^ (k + 1) * (M.Pmat π k *ᵥ vf M ρ (π k) u) s ≤
      (e * beta ρ * w s) * (beta ρ * lam) ^ k := by
    intro k _
    have h1 : (M.Pmat π k *ᵥ vf M ρ (π k) u) s ≤ (M.Pmat π k *ᵥ (e • w)) s :=
      mulVec_mono (Pmat_nonneg M π k) (fun t => by
        have := hv (π k) t; simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hw1 t]) s
    have h2 : (M.Pmat π k *ᵥ (e • w)) s ≤ e * (lam ^ k * w s) := by
      rw [Matrix.mulVec_smul]
      exact mul_le_mul_of_nonneg_left (Pmat_w M hlam0 hPw π k s) he
    calc beta ρ ^ (k + 1) * (M.Pmat π k *ᵥ vf M ρ (π k) u) s
        ≤ beta ρ ^ (k + 1) * (e * (lam ^ k * w s)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hβ0.le _)
      _ = (e * beta ρ * w s) * (beta ρ * lam) ^ k := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hgeo : ∑ k ∈ Finset.range N, (beta ρ * lam) ^ k ≤ (1 - beta ρ * lam)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hq0 hβl]
    exact Summable.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
      (summable_geometric_of_lt_one hq0 hβl)
  have hews : 0 ≤ e * beta ρ * w s := by
    have := hw1 s; positivity
  calc e * beta ρ * w s * ∑ k ∈ Finset.range N, (beta ρ * lam) ^ k
      ≤ e * beta ρ * w s * (1 - beta ρ * lam)⁻¹ := mul_le_mul_of_nonneg_left hgeo hews
    _ = e * (beta ρ / (1 - beta ρ * lam)) * w s := by ring

lemma V_lower {ρ : ℝ} (hρ : -1 < ρ) (hβl : beta ρ * lam < 1) (g : DecisionRule A)
    (u : St → ℝ) (hv : ∀ s, 0 ≤ vf M ρ g u s) (s : St) :
    beta ρ * vf M ρ g u s ≤ M.V ρ (stationary g) s - u s := by
  have hβ0 : 0 < beta ρ := by unfold beta; exact inv_pos.mpr (by linarith)
  have h := (tendsto_pi_nhds.mp (tendsto_vsum M hw1 hlam0 hPw hρ hβl (stationary g) u)) s
  refine ge_of_tendsto h ?_
  rw [eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hrest : 0 ≤ ∑ k ∈ Finset.range N', beta ρ ^ (k + 1 + 1) *
      (M.Pmat (stationary g) (k + 1) *ᵥ vf M ρ (stationary g (k + 1)) u) s :=
    Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hβ0.le _)
      (mulVec_nonneg' (Pmat_nonneg M _ _) (fun t => hv t) s)
  have h0 : beta ρ ^ (0 + 1) * (M.Pmat (stationary g) 0 *ᵥ vf M ρ (stationary g 0) u) s
      = beta ρ * vf M ρ g u s := by simp [Model.Pmat, stationary]
  linarith

lemma V_fixed {ρ : ℝ} (hρ : -1 < ρ) (hβl : beta ρ * lam < 1) (f : DecisionRule A) :
    vf M ρ f (M.V ρ (stationary f)) = 0 := by
  have hβ0 : 0 < beta ρ := by unfold beta; exact inv_pos.mpr (by linarith)
  have hβ : beta ρ * (1 + ρ) = 1 := by unfold beta; exact inv_mul_cancel₀ (by linarith)
  have hS := hasSumV M hw1 hlam0 hPw hβ0 hβl (stationary f)
  have hfix := hasSum_fix (beta ρ • M.P f) hS (fun N => by
    simp only [Pmat_stationary, stationary]
    rw [pow_succ' (M.P f) N, ← Matrix.mulVec_mulVec]
    ext s
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring)
  change M.V ρ (stationary f) = _ + _ *ᵥ M.V ρ (stationary f) at hfix
  set u := M.V ρ (stationary f)
  simp only [Pmat_stationary, pow_zero, zero_add, pow_one, Matrix.one_mulVec, stationary,
    Matrix.smul_mulVec] at hfix
  have : (1 + ρ) • u = M.rv f + M.P f *ᵥ u := by
    conv_lhs => rw [hfix]
    rw [← smul_add, smul_smul, mul_comm, hβ, one_smul]
  ext s
  have hs := congrFun this s
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hs
  simp only [vf, Model.Q, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  linarith

end Series

section Alg

lemma dev_facts (P : Matrix St St ℝ) (hP : IsSubstochastic P) :
    (P - 1) * limitMatrix P = 0 ∧ limitMatrix P * deviationMatrix P = 0 ∧
    (P - 1) * deviationMatrix P = limitMatrix P - 1 := by
  obtain ⟨hT, h1, h2, h3⟩ := display_15 P hP
  set L := limitMatrix P with hL
  have hQL : (P - 1) * L = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  have hLZ : L * (1 - P + L) = L := by
    rw [mul_add, mul_sub, mul_one, h2, h3, sub_self, zero_add]
  have hdet : (1 - P + L).det ≠ 0 := by
    intro hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    apply hx0
    have hLx : L *ᵥ x = 0 := by
      have := congrArg (fun v => L *ᵥ v) hx
      simpa [Matrix.mulVec_mulVec, hLZ] using this
    have hPx : P *ᵥ x = x := by
      have e : (1 - P + L) *ᵥ x = x - P *ᵥ x + L *ᵥ x := by
        simp [Matrix.add_mulVec, Matrix.sub_mulVec]
      rw [hx, hLx, add_zero] at e
      exact (sub_eq_zero.mp e.symm).symm
    have hpow : ∀ k : ℕ, (P ^ k) *ᵥ x = x := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hPx, ih]
    have hces : ∀ N, cesaroMean P N *ᵥ x = x := by
      intro N
      simp only [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec, hpow, Finset.sum_const,
        Finset.card_range]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ (by positivity), one_smul]
    have hc : Continuous fun B : Matrix St St ℝ => B *ᵥ x :=
      continuous_id.matrix_mulVec continuous_const
    have hlim : Tendsto (fun N => cesaroMean P N *ᵥ x) atTop (𝓝 (L *ᵥ x)) :=
      (hc.tendsto _).comp hT
    simp only [hces] at hlim
    have := tendsto_nhds_unique tendsto_const_nhds hlim
    rw [this, hLx]
  have hU : IsUnit (1 - P + L).det := isUnit_iff_ne_zero.mpr hdet
  have hZ1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hLZi : L * (1 - P + L)⁻¹ = L := by
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLZ]
      _ = L := by rw [mul_assoc, hZ1, mul_one]
  have hdev : deviationMatrix P = (1 - P + L)⁻¹ - L := rfl
  refine ⟨hQL, ?_, ?_⟩
  · rw [hdev, mul_sub, hLZi, h3, sub_self]
  · rw [hdev, mul_sub, hQL, sub_zero]
    have e : P - 1 = L - (1 - P + L) := by abel
    rw [e, sub_mul, hLZi, hZ1]

variable (σ : ℝ)

lemma y_lt (f : DecisionRule A) {k : ℤ} (hk : k < -1) : M.y σ f k = 0 := by
  simp [Model.y, hk]

lemma y_m1 (f : DecisionRule A) : M.y σ f (-1) = σ • (M.Pstar f *ᵥ M.rv f) := by
  simp [Model.y]

lemma y_nat (f : DecisionRule A) (m : ℕ) :
    M.y σ f (m : ℤ) = (-σ) ^ m • (M.H f ^ (m + 1) *ᵥ M.rv f) := by
  simp only [Model.y]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

noncomputable def Yv (f : DecisionRule A) (j : ℕ) : St → ℝ := M.y σ f ((j : ℤ) - 1)

lemma psi0 (g f : DecisionRule A) :
    M.ψ σ g f (((0 : ℕ) : ℤ) - 1) = M.rn g (((0 : ℕ) : ℤ) - 1) + M.Q g *ᵥ Yv M σ f 0 := by
  simp only [Model.ψ, Yv]
  rw [if_neg (by norm_num), y_lt M σ f (show ((0 : ℕ) : ℤ) - 1 - 1 < -1 by norm_num)]
  simp

lemma psiS (g f : DecisionRule A) (m : ℕ) :
    M.ψ σ g f (((m + 1 : ℕ) : ℤ) - 1) = M.rn g (((m + 1 : ℕ) : ℤ) - 1)
      + M.Q g *ᵥ Yv M σ f (m + 1) - σ • Yv M σ f m := by
  have h1 : ((m + 1 : ℕ) : ℤ) - 1 - 1 = (m : ℤ) - 1 := by push_cast; ring
  simp only [Model.ψ, Yv, h1]
  rw [if_neg (by omega)]

lemma psi_local {g g' : DecisionRule A} (f : DecisionRule A) (k : ℤ) (s : St) (h : g s = g' s) :
    M.ψ σ g f k s = M.ψ σ g' f k s := by
  simp only [Model.ψ, Model.rn]
  split_ifs <;> simp [Model.rv, Model.Q, Model.P, mulVec, dotProduct, Matrix.sub_apply, h]

lemma psi_ff (hσ : σ = 1 ∨ σ = -1) (f : DecisionRule A) {k : ℤ} (hk : -1 ≤ k) :
    M.ψ σ f f k = 0 := by
  obtain ⟨hQL0, hLH0, hQH0⟩ := dev_facts (M.P f) (P_sub M f)
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hQL : M.Q f * M.Pstar f = 0 := hQL0
  have hLH : M.Pstar f * M.H f = 0 := hLH0
  have hQH : M.Q f * M.H f = M.Pstar f - 1 := hQH0
  rcases (show k = -1 ∨ 0 ≤ k by omega) with rfl | hk0
  · simp only [Model.ψ]
    rw [if_neg (by omega), y_m1, y_lt M σ f (by omega)]
    simp [Model.rn, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQL]
  lift k to ℕ using hk0
  rcases k with _ | m
  · simp only [Model.ψ]
    rw [if_neg (by omega)]
    have e : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
    rw [e, y_m1, y_nat]
    simp only [Model.rn, Nat.cast_zero, if_true, pow_zero, one_smul, zero_add, pow_one,
      Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    rw [hQH]
    ext s
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination (-(M.Pstar f *ᵥ M.rv f) s) * hσσ
  · simp only [Model.ψ]
    rw [if_neg (by omega)]
    have e : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rw [e, y_nat, y_nat]
    have hk : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
    have hQHk : M.Q f * M.H f ^ (m + 1 + 1) = -(M.H f ^ (m + 1)) := by
      rw [pow_succ', ← mul_assoc, hQH, sub_mul, one_mul, pow_succ', ← mul_assoc,
        hLH, zero_mul, zero_sub]
    simp only [Model.rn, hk, if_false, zero_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQHk,
      Matrix.neg_mulVec]
    ext s
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
    ring

noncomputable def Wv (f : DecisionRule A) (t : ℝ) (J : ℕ) : St → ℝ :=
  ∑ j ∈ Finset.range (J + 1), t ^ j • Yv M σ f j

lemma Dg (g f : DecisionRule A) (t : ℝ) : ∀ J : ℕ,
    M.Q g *ᵥ Wv M σ f t J - (σ * t) • Wv M σ f t J
      + ∑ j ∈ Finset.range (J + 1), t ^ j • M.rn g ((j : ℤ) - 1)
      - ∑ j ∈ Finset.range (J + 1), t ^ j • M.ψ σ g f ((j : ℤ) - 1)
      = -(σ * t ^ (J + 1)) • Yv M σ f J
  | 0 => by
      simp only [Wv, zero_add, Finset.sum_range_one, pow_zero, one_smul, pow_one]
      rw [psi0]
      module
  | J + 1 => by
      have ih := Dg g f t J
      simp only [Wv] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => t ^ j • M.rn g _),
        Finset.sum_range_succ (fun j => t ^ j • M.ψ σ g f _), psiS]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
      linear_combination (norm := module) ih

lemma rn_sum (g : DecisionRule A) (t : ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.range (J + 1), t ^ j • M.rn g ((j : ℤ) - 1) = t • M.rv g := by
  rw [Finset.sum_eq_single 1]
  · simp [Model.rn]
  · intro j _ hj
    have : ((j : ℤ) - 1) ≠ 0 := by omega
    simp [Model.rn, this]
  · intro h; exfalso; apply h; simp; omega


lemma expansion [Nonempty St] [Fintype (DecisionRule A)] (hσ : σ = 1 ∨ σ = -1)
    {w : St → ℝ} {lam C0 δ0 : ℝ} (hw1 : ∀ s, 1 ≤ w s) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hPw : ∀ g s, (M.P g *ᵥ w) s ≤ lam * w s) (hC0 : 0 < C0) (hδ1 : δ0 ≤ 1)
    (hB : ∀ ρ, 0 < σ * ρ → σ * ρ < δ0 →
      (-1 < ρ ∧ beta ρ * lam < 1 ∧ beta ρ / (1 - beta ρ * lam) ≤ C0 / (σ * ρ)))
    (f : DecisionRule A) (J : ℕ) (hJ : 1 ≤ J) :
    ∃ C, 0 ≤ C ∧ ∀ ρ, 0 < σ * ρ → σ * ρ < δ0 → ∀ g s,
      |(σ * ρ) * vf M ρ g (M.V ρ (stationary f)) s
        - (∑ j ∈ Finset.range (J + 1), (σ * ρ) ^ j • M.ψ σ g f ((j : ℤ) - 1)) s|
        ≤ C * (σ * ρ) ^ J := by
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have habsσ : |σ| = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  set Y := Yv M σ f J
  set SY := ∑ s, |Y s|
  set Ws := ∑ s, w s
  have hSY : 0 ≤ SY := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw0 : ∀ s, 0 < w s := fun s => lt_of_lt_of_le one_pos (hw1 s)
  have hWs : ∀ s, w s ≤ Ws := fun s =>
    Finset.single_le_sum (f := w) (fun t _ => (hw0 t).le) (Finset.mem_univ s)
  have hWs0 : 0 ≤ Ws := Finset.sum_nonneg fun t _ => (hw0 t).le
  refine ⟨SY + 3 * (C0 * SY) * Ws, by positivity, ?_⟩
  intro ρ ht0 htδ g s
  obtain ⟨hρ1, hβl, hβC⟩ := hB ρ ht0 htδ
  set t := σ * ρ with ht_def
  have ht1 : t ≤ 1 := by linarith
  have hρt : σ * t = ρ := by rw [ht_def, ← mul_assoc, hσσ, one_mul]
  have hβ0 : 0 < beta ρ := by unfold beta; exact inv_pos.mpr (by linarith)
  have hβ : beta ρ * (1 + ρ) = 1 := by unfold beta; exact inv_mul_cancel₀ (by linarith)
  set u := M.V ρ (stationary f)
  have hfix := V_fixed M hw1 hlam0 hPw hρ1 hβl f
  set W := Wv M σ f t J
  set E := t • u - W with hE
  -- identity for f
  have hDf := Dg M σ f f t J
  rw [rn_sum M f t hJ, hρt] at hDf
  have hψf : ∑ j ∈ Finset.range (J + 1), t ^ j • M.ψ σ f f ((j : ℤ) - 1) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [psi_ff M σ hσ f (by omega)]; simp
  rw [hψf, sub_zero] at hDf
  -- equation for E
  have hEq : E = beta ρ • (-(σ * t ^ (J + 1)) • Y + M.P f *ᵥ E) := by
    have h1 : M.Q f *ᵥ E - ρ • E = (σ * t ^ (J + 1)) • Y := by
      have hv : M.rv f + M.Q f *ᵥ u - ρ • u = 0 := hfix
      rw [hE, Matrix.mulVec_sub, Matrix.mulVec_smul]
      linear_combination (norm := module) t • hv - hDf
    have hQ : M.Q f *ᵥ E = M.P f *ᵥ E - E := by
      simp [Model.Q, Matrix.sub_mulVec]
    rw [hQ] at h1
    have h2 : (1 + ρ) • E = -(σ * t ^ (J + 1)) • Y + M.P f *ᵥ E := by
      linear_combination (norm := module) -h1
    calc E = (beta ρ * (1 + ρ)) • E := by rw [hβ, one_smul]
      _ = beta ρ • ((1 + ρ) • E) := by rw [smul_smul]
      _ = _ := by rw [h2]
  have hb : ∀ s, |(-(σ * t ^ (J + 1)) • Y) s| ≤ t ^ (J + 1) * SY * w s := by
    intro s
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, habsσ, one_mul,
      abs_of_pos (pow_pos ht0 _)]
    have : |Y s| ≤ SY := Finset.single_le_sum (f := fun s => |Y s|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)
    have h0 : 0 ≤ t ^ (J + 1) := (pow_pos ht0 _).le
    calc t ^ (J + 1) * |Y s| ≤ t ^ (J + 1) * SY := mul_le_mul_of_nonneg_left this h0
      _ = t ^ (J + 1) * SY * 1 := by ring
      _ ≤ t ^ (J + 1) * SY * w s := mul_le_mul_of_nonneg_left (hw1 s) (mul_nonneg h0 hSY)
  have hEb0 := fixed_bound (P_nonneg M f) hw0 (hPw f) hβ0 hβl
    (mul_nonneg (pow_pos ht0 _).le hSY) hb hEq
  set c := C0 * SY * t ^ J with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hEb : ∀ s, |E s| ≤ c * w s := by
    intro s
    refine (hEb0 s).trans (mul_le_mul_of_nonneg_right ?_ (hw0 s).le)
    have : beta ρ * (t ^ (J + 1) * SY) / (1 - beta ρ * lam)
        = (t ^ (J + 1) * SY) * (beta ρ / (1 - beta ρ * lam)) := by ring
    rw [this]
    calc (t ^ (J + 1) * SY) * (beta ρ / (1 - beta ρ * lam))
        ≤ (t ^ (J + 1) * SY) * (C0 / t) :=
          mul_le_mul_of_nonneg_left hβC (mul_nonneg (pow_pos ht0 _).le hSY)
      _ = c := by rw [pow_succ, hc_def]; field_simp
  -- identity for g
  have hDg := Dg M σ g f t J
  rw [rn_sum M g t hJ, hρt] at hDg
  have key : t • vf M ρ g u - ∑ j ∈ Finset.range (J + 1), t ^ j • M.ψ σ g f ((j : ℤ) - 1)
      = -(σ * t ^ (J + 1)) • Y + (M.P g *ᵥ E - E - ρ • E) := by
    have hQg : M.Q g *ᵥ E = M.P g *ᵥ E - E := by simp [Model.Q, Matrix.sub_mulVec]
    rw [← hQg, hE, Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [vf]
    linear_combination (norm := module) hDg
  have key_s := congrFun key s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at key_s
  rw [key_s]
  have h1 := hb s
  have h2 : |(M.P g *ᵥ E) s| ≤ c * (lam * w s) := mulVec_wbound (P_nonneg M g) hc0 hEb s (hPw g s)
  have h3 := hEb s
  have hρabs : |ρ| = t := by
    have : |ρ| = |σ * ρ| := by rw [abs_mul, habsσ, one_mul]
    rw [this, abs_of_pos ht0]
  have h4 : |ρ * E s| ≤ c * w s := by
    rw [abs_mul, hρabs]
    calc t * |E s| ≤ 1 * |E s| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ ≤ c * w s := by linarith
  have htJ : t ^ (J + 1) ≤ t ^ J := pow_le_pow_of_le_one ht0.le ht1 (Nat.le_succ J)
  have hlw : c * (lam * w s) ≤ c * w s := by
    apply mul_le_mul_of_nonneg_left _ hc0; nlinarith [hw0 s]
  have hcw : c * w s ≤ c * Ws := mul_le_mul_of_nonneg_left (hWs s) hc0
  have hY1 : |(-(σ * t ^ (J + 1)) • Y) s| ≤ t ^ J * SY := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, habsσ, one_mul,
      abs_of_pos (pow_pos ht0 _)]
    have : |Y s| ≤ SY := Finset.single_le_sum (f := fun s => |Y s|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)
    calc t ^ (J + 1) * |Y s| ≤ t ^ J * |Y s| := mul_le_mul_of_nonneg_right htJ (abs_nonneg _)
      _ ≤ t ^ J * SY := mul_le_mul_of_nonneg_left this (pow_pos ht0 _).le
  calc |(-(σ * t ^ (J + 1)) • Y) s + ((M.P g *ᵥ E) s - E s - ρ * E s)|
      ≤ |(-(σ * t ^ (J + 1)) • Y) s| + (|(M.P g *ᵥ E) s| + |E s| + |ρ * E s|) := by
        have := abs_add_le ((-(σ * t ^ (J + 1)) • Y) s) ((M.P g *ᵥ E) s - E s - ρ * E s)
        have h' := abs_sub ((M.P g *ᵥ E) s - E s) (ρ * E s)
        have h'' := abs_sub ((M.P g *ᵥ E) s) (E s)
        linarith
    _ ≤ t ^ J * SY + (c * Ws + c * Ws + c * Ws) := by linarith
    _ = (SY + 3 * (C0 * SY) * Ws) * t ^ J := by ring

end Alg

section Weight

lemma pow_nonnegM (f : DecisionRule A) (N : ℕ) : NonnegM (M.P f ^ N) := by
  rw [← Pmat_stationary]; exact Pmat_nonneg M _ N

lemma transient_weight [Nonempty St] [Fintype (DecisionRule A)] [Nonempty (DecisionRule A)]
    (htr : M.TransientCase) :
    ∃ w : St → ℝ, ∃ lam : ℝ, (∀ s, 1 ≤ w s) ∧ 0 ≤ lam ∧ lam < 1 ∧
      ∀ g s, (M.P g *ᵥ w) s ≤ lam * w s := by
  have hS : ∀ f : DecisionRule A, Summable (fun N => M.P f ^ N) := fun f => by
    have := htr f
    unfold Model.IsTransient at this
    have e : M.Pmat (stationary f) = fun N => M.P f ^ N := funext (Pmat_stationary M f)
    rwa [e] at this
  let one : St → ℝ := fun _ => 1
  have hc : Continuous fun B : Matrix St St ℝ => B *ᵥ one :=
    continuous_id.matrix_mulVec continuous_const
  let φ : Matrix St St ℝ →+ (St → ℝ) :=
    { toFun := fun B => B *ᵥ one, map_zero' := Matrix.zero_mulVec _,
      map_add' := fun a b => Matrix.add_mulVec a b _ }
  let wv : DecisionRule A → St → ℝ := fun f => ∑' N, M.P f ^ N *ᵥ one
  have hW : ∀ f, HasSum (fun N => M.P f ^ N *ᵥ one) (wv f) := fun f =>
    ((hS f).hasSum.map φ hc).summable.hasSum
  have hfixW : ∀ f, wv f = one + M.P f *ᵥ wv f := fun f => by
    have := hasSum_fix (M.P f) (hW f) (fun N => by rw [pow_succ', ← Matrix.mulVec_mulVec])
    simpa using this
  have hW0 : ∀ f s, 0 ≤ wv f s := fun f s =>
    (Pi.hasSum.mp (hW f) s).nonneg fun N =>
      mulVec_nonneg' (pow_nonnegM M f N) (fun _ => zero_le_one) s
  have hW1 : ∀ f s, 1 ≤ wv f s := fun f s => by
    have e := congrFun (hfixW f) s
    simp only [Pi.add_apply] at e
    have := mulVec_nonneg' (P_nonneg M f) (hW0 f) s
    simp only [one] at e
    linarith
  obtain ⟨fs, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun f => ∑ s, wv f s)
    Finset.univ_nonempty
  set ws := wv fs
  have claim : ∀ g s, (M.P g *ᵥ ws) s + 1 ≤ ws s := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨g, s, hgs⟩ := hcon
    set g' : DecisionRule A := Function.update fs s (g s)
    have hrow_s : ∀ x : St → ℝ, (M.P g' *ᵥ x) s = (M.P g *ᵥ x) s := fun x => by
      simp [g', Model.P, mulVec, dotProduct]
    have hrow_t : ∀ t, t ≠ s → ∀ x : St → ℝ, (M.P g' *ᵥ x) t = (M.P fs *ᵥ x) t :=
      fun t ht x => by simp [g', Model.P, mulVec, dotProduct, Function.update_of_ne ht]
    set d : St → ℝ := one + M.P g' *ᵥ ws - ws
    have hds : 0 < d s := by
      simp only [d, Pi.add_apply, Pi.sub_apply, one, hrow_s]; linarith
    have hdt : ∀ t, t ≠ s → d t = 0 := fun t ht => by
      have e := congrFun (hfixW fs) t
      simp only [d, Pi.add_apply, Pi.sub_apply, hrow_t t ht]
      simp only [Pi.add_apply] at e
      change ws t = one t + (M.P fs *ᵥ ws) t at e
      linarith
    have hd0 : ∀ t, 0 ≤ d t := fun t => by
      by_cases ht : t = s
      · rw [ht]; exact hds.le
      · rw [hdt t ht]
    set z := wv g' - ws
    have hz : z = d + M.P g' *ᵥ z := by
      have e := hfixW g'
      simp only [z, d, Matrix.mulVec_sub]
      conv_lhs => rw [e]
      abel
    have hiter : ∀ N : ℕ, z = (∑ k ∈ Finset.range N, M.P g' ^ k *ᵥ d) + M.P g' ^ N *ᵥ z := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, pow_succ, ← Matrix.mulVec_mulVec]
        conv_lhs => rw [ih]
        conv_lhs => rw [hz]
        rw [Matrix.mulVec_add]
        abel
    have hlim0 : Tendsto (fun N => M.P g' ^ N *ᵥ z) atTop (𝓝 0) := by
      have h1 := (hS g').tendsto_atTop_zero
      have hcz : Continuous fun B : Matrix St St ℝ => B *ᵥ z :=
        continuous_id.matrix_mulVec continuous_const
      have := (hcz.tendsto 0).comp h1
      simpa [Function.comp_def] using this
    have hpart : Tendsto (fun N => ∑ k ∈ Finset.range N, M.P g' ^ k *ᵥ d) atTop (𝓝 z) := by
      have : (fun N => ∑ k ∈ Finset.range N, M.P g' ^ k *ᵥ d) =
          fun N => z - M.P g' ^ N *ᵥ z := by
        funext N; rw [eq_sub_iff_add_eq]; exact (hiter N).symm
      rw [this]; simpa using (tendsto_const_nhds (x := z)).sub hlim0
    have hzd : ∀ t, d t ≤ z t := fun t => by
      refine ge_of_tendsto ((tendsto_pi_nhds.mp hpart) t) ?_
      rw [eventually_atTop]
      refine ⟨1, fun N hN => ?_⟩
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [Finset.sum_range_succ']
      have : 0 ≤ ∑ k ∈ Finset.range N', (M.P g' ^ (k + 1) *ᵥ d) t :=
        Finset.sum_nonneg fun k _ => mulVec_nonneg' (pow_nonnegM M g' _) hd0 t
      simp only [Pi.add_apply, Finset.sum_apply, pow_zero, Matrix.one_mulVec]
      linarith
    have hlt : ∑ t, ws t < ∑ t, wv g' t := by
      apply Finset.sum_lt_sum
      · intro t _
        have := (hd0 t).trans (hzd t)
        simp only [z, Pi.sub_apply] at this; linarith
      · refine ⟨s, Finset.mem_univ s, ?_⟩
        have := hds.trans_le (hzd s)
        simp only [z, Pi.sub_apply] at this; linarith
    have := hmax g' (Finset.mem_univ _)
    linarith
  set Wt := ∑ t, ws t
  obtain ⟨s0⟩ := (inferInstance : Nonempty St)
  have hws_le : ∀ s, ws s ≤ Wt := fun s =>
    Finset.single_le_sum (f := ws) (fun t _ => hW0 fs t) (Finset.mem_univ s)
  have hWt1 : 1 ≤ Wt := (hW1 fs s0).trans (hws_le s0)
  refine ⟨ws, 1 - 1 / Wt, hW1 fs, ?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one (by linarith)]; exact hWt1
  · have : 0 < 1 / Wt := by positivity
    linarith
  · intro g s
    have h1 := claim g s
    have h2 : ws s / Wt ≤ 1 := by rw [div_le_one (by linarith)]; exact hws_le s
    have e : (1 - 1 / Wt) * ws s = ws s - ws s / Wt := by ring
    rw [e]; linarith

lemma setup [Nonempty St] [Fintype (DecisionRule A)] [Nonempty (DecisionRule A)]
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (htr : σ = -1 → M.TransientCase) :
    ∃ w : St → ℝ, ∃ lam C0 δ0 : ℝ, (∀ s, 1 ≤ w s) ∧ 0 ≤ lam ∧ lam ≤ 1 ∧
      (∀ g s, (M.P g *ᵥ w) s ≤ lam * w s) ∧ 0 < C0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧
      ∀ ρ, 0 < σ * ρ → σ * ρ < δ0 →
        (-1 < ρ ∧ beta ρ * lam < 1 ∧ beta ρ / (1 - beta ρ * lam) ≤ C0 / (σ * ρ)) := by
  rcases hσ with rfl | rfl
  · refine ⟨fun _ => 1, 1, 1, 1, fun _ => le_rfl, zero_le_one, le_rfl, fun g s => P_one_le M g s,
      one_pos, one_pos, le_rfl, fun ρ h0 h1 => ?_⟩
    rw [one_mul] at h0 ⊢
    have hβ : beta ρ = (1 + ρ)⁻¹ := rfl
    refine ⟨by linarith, ?_, ?_⟩
    · rw [mul_one, hβ]; exact inv_lt_one_of_one_lt₀ (by linarith)
    · rw [mul_one, hβ]
      have : 1 - (1 + ρ)⁻¹ = ρ / (1 + ρ) := by field_simp; ring
      rw [this, div_div_eq_mul_div, inv_mul_eq_div, div_div, mul_comm]
      rw [div_mul_cancel_right₀ (by linarith)]
      ring_nf; exact le_rfl
  · obtain ⟨w, lam, hw1, hl0, hl1, hPw⟩ := transient_weight M (htr rfl)
    refine ⟨w, lam, 2 / (1 - lam), (1 - lam) / 2, hw1, hl0, hl1.le, hPw,
      by apply div_pos two_pos; linarith, by apply div_pos _ two_pos; linarith,
      by linarith, fun ρ h0 h1 => ?_⟩
    have ht : 0 < -ρ := by linarith
    have hβ : beta ρ = (1 + ρ)⁻¹ := rfl
    have h1ρ : 0 < 1 + ρ := by linarith
    have hden : 0 < 1 + ρ - lam := by linarith
    refine ⟨by linarith, ?_, ?_⟩
    · rw [hβ, inv_mul_eq_div, div_lt_one h1ρ]; linarith
    · rw [hβ]
      have e : (1 + ρ)⁻¹ / (1 - (1 + ρ)⁻¹ * lam) = 1 / (1 + ρ - lam) := by
        field_simp
      rw [e]
      have e2 : -1 * ρ = -ρ := by ring
      rw [e2, div_le_div_iff₀ hden ht]
      have : -ρ < 1 := by linarith
      have h2 : 1 ≤ 2 / (1 - lam) * (1 + ρ - lam) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
      linarith

end Weight
end ModelSec

section Real

lemma approx {c : ℕ → ℝ} {x t C : ℝ} {J j0 : ℕ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (hj : j0 < J) (hz : ∀ j < j0, c j = 0)
    (h : |x - ∑ j ∈ Finset.range (J + 1), t ^ j * c j| ≤ C * t ^ J) :
    |x - t ^ j0 * c j0| ≤ t ^ (j0 + 1) * (∑ j ∈ Finset.range (J + 1), |c j| + C) := by
  have hmem : j0 ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  have hsplit := Finset.add_sum_erase (Finset.range (J + 1)) (fun j => t ^ j * c j) hmem
  have hrest : |∑ j ∈ (Finset.range (J + 1)).erase j0, t ^ j * c j| ≤
      t ^ (j0 + 1) * ∑ j ∈ Finset.range (J + 1), |c j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun j hj => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun j _ _ => mul_nonneg (pow_pos ht0 _).le (abs_nonneg _))
    have hj0 : j ≠ j0 := Finset.ne_of_mem_erase hj
    rw [abs_mul, abs_of_pos (pow_pos ht0 _)]
    rcases lt_or_gt_of_ne hj0 with hlt | hgt
    · rw [hz j hlt]; simp
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1 (by omega))
        (abs_nonneg _)
  have hCt : C * t ^ J ≤ C * t ^ (j0 + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1 (by omega)) hC
  have e : x - t ^ j0 * c j0 = (x - ∑ j ∈ Finset.range (J + 1), t ^ j * c j)
      + ∑ j ∈ (Finset.range (J + 1)).erase j0, t ^ j * c j := by
    rw [← hsplit]; ring
  rw [e]
  calc _ ≤ |x - ∑ j ∈ Finset.range (J + 1), t ^ j * c j|
        + |∑ j ∈ (Finset.range (J + 1)).erase j0, t ^ j * c j| := abs_add_le _ _
    _ ≤ C * t ^ (j0 + 1) + t ^ (j0 + 1) * ∑ j ∈ Finset.range (J + 1), |c j| := by linarith
    _ = _ := by ring

lemma first_nonzero (c : ℤ → ℝ) (m : ℤ) :
    (∀ k ∈ Set.Icc (-1 : ℤ) m, c k = 0) ∨
      ∃ k ∈ Set.Icc (-1 : ℤ) m, c k ≠ 0 ∧ ∀ j ∈ Set.Ico (-1 : ℤ) k, c j = 0 := by
  classical
  by_cases h : ∀ k ∈ Set.Icc (-1 : ℤ) m, c k = 0
  · exact Or.inl h
  push_neg at h
  right
  obtain ⟨lb, ⟨hlb, hne⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun k => k ∈ Set.Icc (-1 : ℤ) m ∧ c k ≠ 0) ⟨-1, fun z hz => hz.1.1⟩ h
  refine ⟨lb, hlb, hne, fun j hj => ?_⟩
  by_contra hcj
  have := hmin j ⟨⟨hj.1, by linarith [hj.2, hlb.2]⟩, hcj⟩
  linarith [hj.2]

lemma final2 {t c0 v β u0 V0 : ℝ} {n : ℤ} {j0 : ℕ} (ht0 : 0 < t) (ht1 : t < 1) (hc0 : 0 < c0)
    (hj0 : (j0 : ℤ) ≤ n + 1) (hβ : 1 / 2 ≤ β) (h0 : t ^ j0 * c0 / 2 ≤ t * v)
    (hlow : β * v ≤ V0 - u0) (hopt : -(c0 / 8) ≤ t ^ (-n) * (u0 - V0)) : False := by
  have hv : t ^ j0 * c0 / 2 / t ≤ v := by
    rw [div_le_iff₀ ht0]; linarith only [h0]
  have hX0 : 0 ≤ t ^ j0 * c0 / 2 / t :=
    div_nonneg (div_nonneg (mul_nonneg (pow_pos ht0 _).le hc0.le) zero_le_two) ht0.le
  have hgap : t ^ j0 * c0 / 2 / t / 2 ≤ V0 - u0 := by
    have hvv : 0 ≤ v := hX0.trans hv
    have h1 : 1 / 2 * v ≤ β * v := mul_le_mul_of_nonneg_right hβ hvv
    linarith only [h1, hv, hlow]
  have hexp1 : 1 ≤ t ^ (-n) * (t ^ j0 / t) := by
    have : t ^ (-n) * (t ^ j0 / t) = t ^ ((j0 : ℤ) - 1 - n) := by
      rw [sub_sub, sub_eq_add_neg, zpow_add₀ ht0.ne', _root_.zpow_neg, _root_.zpow_neg, zpow_natCast,
        zpow_add₀ ht0.ne', zpow_one]
      field_simp
    rw [this]; exact one_le_zpow_of_nonpos₀ ht0 ht1.le (by omega)
  have htn : 0 < t ^ (-n) := zpow_pos ht0 _
  have h4 : t ^ (-n) * (t ^ j0 * c0 / 2 / t / 2) = (t ^ (-n) * (t ^ j0 / t)) * (c0 / 4) := by
    ring
  have h3 := mul_le_mul_of_nonneg_left hgap htn.le
  have h5 : c0 / 4 ≤ (t ^ (-n) * (t ^ j0 / t)) * (c0 / 4) :=
    le_mul_of_one_le_left (div_nonneg hc0.le zero_le_four) hexp1
  have h6 : t ^ (-n) * (u0 - V0) = -(t ^ (-n) * (V0 - u0)) := by ring
  rw [h6] at hopt
  linarith only [hopt, h3, h4, h5, hc0]

end Real

end VeinottT4Aux

open VeinottSensitiveDP.Sensitive VeinottT4Aux in
theorem solution {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (htr : σ = -1 → M.TransientCase) (n : ℤ) (hn1 : -2 ≤ n)
    (hn2 : n ≤ (Fintype.card St : ℤ) - 1) (f : DecisionRule A) :
    (M.G σ (n + 1) f = ∅ → f ∈ M.D σ n) ∧ (f ∈ M.D σ n → M.G σ n f = ∅) := by
  classical
  rcases (show n = -2 ∨ -1 ≤ n by omega) with rfl | hn
  · refine ⟨fun _ => by simp [Model.D], fun _ => ?_⟩
    ext g
    simp only [Model.G, LexPos, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨k, hk, -⟩
    simp only [Set.mem_Icc] at hk
    omega
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have habsσ : |σ| = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  obtain ⟨w, lam, C0, δ0, hw1, hl0, hl1, hPw, hC0, hδ0, hδ1, hB⟩ := setup M σ hσ htr
  set L := 𝓝[{ρ : ℝ | 0 < σ * ρ}] (0 : ℝ) with hL
  have hL0 : ∀ᶠ ρ in L, 0 < σ * ρ := self_mem_nhdsWithin
  have hLsmall : ∀ η : ℝ, 0 < η → ∀ᶠ ρ in L, σ * ρ < η := by
    intro η hη
    have h1 : Tendsto (fun ρ : ℝ => σ * ρ) (𝓝 0) (𝓝 0) := by
      have := (continuous_mul_left σ).tendsto 0
      simpa using this
    exact (h1.eventually (eventually_lt_nhds hη)).filter_mono nhdsWithin_le_nhds
  have hLne : L.NeBot := by
    rcases hσ with rfl | rfl
    · have : {ρ : ℝ | 0 < 1 * ρ} = Set.Ioi 0 := by ext; simp
      rw [hL, this]; infer_instance
    · have : {ρ : ℝ | 0 < -1 * ρ} = Set.Iio 0 := by ext; simp
      rw [hL, this]; infer_instance
  have hρabs : ∀ ρ : ℝ, 0 < σ * ρ → |ρ| = σ * ρ := fun ρ h => by
    have : |ρ| = |σ * ρ| := by rw [abs_mul, habsσ, one_mul]
    rw [this, abs_of_pos h]
  set J := (n + 4).toNat with hJdef
  have hJ : (J : ℤ) = n + 4 := by rw [hJdef]; omega
  have hJ1 : 1 ≤ J := by omega
  obtain ⟨C, hC, hexp⟩ := expansion M σ hσ hw1 hl0 hl1 hPw hC0 hδ1 hB f J hJ1
  set Dall := (∑ g : DecisionRule A, ∑ s : St, ∑ j ∈ Finset.range (J + 1),
    |M.ψ σ g f ((j : ℤ) - 1) s|) + C with hDall
  have hD0 : 0 ≤ Dall := by positivity
  have hDle : ∀ g s, ∑ j ∈ Finset.range (J + 1), |M.ψ σ g f ((j : ℤ) - 1) s| + C ≤ Dall := by
    intro g s
    have h1 : ∑ j ∈ Finset.range (J + 1), |M.ψ σ g f ((j : ℤ) - 1) s| ≤
        ∑ s' : St, ∑ j ∈ Finset.range (J + 1), |M.ψ σ g f ((j : ℤ) - 1) s'| :=
      Finset.single_le_sum (f := fun s' => ∑ j ∈ Finset.range (J + 1),
        |M.ψ σ g f ((j : ℤ) - 1) s'|) (fun _ _ => by positivity) (Finset.mem_univ s)
    have h2 : ∑ s' : St, ∑ j ∈ Finset.range (J + 1), |M.ψ σ g f ((j : ℤ) - 1) s'| ≤
        ∑ g' : DecisionRule A, ∑ s' : St, ∑ j ∈ Finset.range (J + 1),
          |M.ψ σ g' f ((j : ℤ) - 1) s'| :=
      Finset.single_le_sum (f := fun g' => ∑ s' : St, ∑ j ∈ Finset.range (J + 1),
        |M.ψ σ g' f ((j : ℤ) - 1) s'|) (fun _ _ => by positivity) (Finset.mem_univ g)
    rw [hDall]; linarith
  -- row expansion, real form
  have hrow : ∀ g s, ∀ ρ, 0 < σ * ρ → σ * ρ < δ0 → ∀ j0 : ℕ, j0 < J →
      (∀ j < j0, M.ψ σ g f ((j : ℤ) - 1) s = 0) →
      |(σ * ρ) * vf M ρ g (M.V ρ (stationary f)) s
        - (σ * ρ) ^ j0 * M.ψ σ g f ((j0 : ℤ) - 1) s| ≤ (σ * ρ) ^ (j0 + 1) * Dall := by
    intro g s ρ ht0 htδ j0 hj0 hz
    have h := hexp ρ ht0 htδ g s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    have := approx (c := fun j => M.ψ σ g f ((j : ℤ) - 1) s) ht0 (by linarith) hC hj0 hz h
    exact this.trans (mul_le_mul_of_nonneg_left (hDle g s) (pow_pos ht0 _).le)
  have hΨ : ∀ (g : DecisionRule A) (m k : ℤ), k ∈ Set.Icc (-1 : ℤ) m →
      M.Ψ σ g f m k = M.ψ σ g f k := fun g m k hk => by
    simp [Model.Ψ, hk.1, hk.2]
  constructor
  ------------------------------------------------------------------ 1°
  · intro hG
    -- every row of Ψ_{n+1}(g,f) is lexicographically nonpositive
    have hlex : ∀ g s, (∀ k ∈ Set.Icc (-1 : ℤ) (n + 1), M.ψ σ g f k s = 0) ∨
        ∃ k ∈ Set.Icc (-1 : ℤ) (n + 1), M.ψ σ g f k s < 0 ∧
          ∀ j ∈ Set.Ico (-1 : ℤ) k, M.ψ σ g f j s = 0 := by
      intro g s
      rcases first_nonzero (fun k => M.ψ σ g f k s) (n + 1) with h | ⟨k, hk, hne, hprev⟩
      · exact Or.inl h
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inr ⟨k, hk, hneg, hprev⟩
      exfalso
      let g' : DecisionRule A := fun t => if t = s then g t else f t
      have hloc : ∀ k' t, M.ψ σ g' f k' t = if t = s then M.ψ σ g f k' t else M.ψ σ f f k' t := by
        intro k' t
        by_cases ht : t = s
        · rw [if_pos ht]; exact psi_local M σ f k' t (by simp [g', ht])
        · rw [if_neg ht]; exact psi_local M σ f k' t (by simp [g', ht])
      have hmem : g' ∈ M.G σ (n + 1) f := by
        refine ⟨fun t => ?_, k, hk, s, ?_⟩
        · by_cases ht : t = s
          · subst ht
            refine Or.inr ⟨k, hk, ?_, fun j hj => ?_⟩
            · rw [hΨ g' _ k hk, hloc, if_pos rfl]; exact hpos
            · rw [hΨ g' _ j ⟨hj.1, by linarith [hj.2, hk.2]⟩, hloc, if_pos rfl]
              exact hprev j hj
          · refine Or.inl fun k' hk' => ?_
            rw [hΨ g' _ k' hk', hloc, if_neg ht, psi_ff M σ hσ f hk'.1]
            rfl
        · rw [hΨ g' _ k hk, hloc, if_pos rfl]; exact hne
      rw [hG] at hmem; exact hmem
    simp only [Model.D, if_neg (show ¬ n < -1 by omega), Set.mem_setOf_eq]
    intro π s ε hε
    set m := (n + 2).toNat with hmdef
    have hm : (m : ℤ) = n + 2 := by rw [hmdef]; omega
    have hmJ : m + 2 = J := by omega
    set Ws := ∑ t, w t
    have hw0 : ∀ s, 0 < w s := fun s => lt_of_lt_of_le one_pos (hw1 s)
    have hWs : w s ≤ Ws := Finset.single_le_sum (f := w) (fun t _ => (hw0 t).le) (Finset.mem_univ s)
    set K1 := C0 * Ws + 1
    have hK1 : 0 < K1 := by
      have : 0 ≤ Ws := Finset.sum_nonneg fun t _ => (hw0 t).le
      positivity
    set ε' := ε / K1
    have hε' : 0 < ε' := div_pos hε hK1
    -- each row eventually small
    have hper : ∀ g s', ∀ᶠ ρ in L, (σ * ρ) * vf M ρ g (M.V ρ (stationary f)) s'
        ≤ ε' * (σ * ρ) ^ m := by
      intro g s'
      rcases hlex g s' with hz | ⟨k, hk, hneg, hprev⟩
      · -- zero row: first possibly nonzero index is m + 1
        have hz' : ∀ j < m + 1, M.ψ σ g f ((j : ℤ) - 1) s' = 0 := fun j hj =>
          hz _ ⟨by omega, by omega⟩
        have hη : 0 < ε' / (2 * Dall + 1) := by positivity
        filter_upwards [hL0, hLsmall δ0 hδ0, hLsmall _ hη] with ρ ht0 htδ htη
        have h := hrow g s' ρ ht0 htδ (m + 1) (by omega) hz'
        set t := σ * ρ
        have ht1 : t ≤ 1 := by linarith
        have hc : |M.ψ σ g f (((m + 1 : ℕ) : ℤ) - 1) s'| ≤ Dall := by
          have := hDle g s'
          have h2 : |M.ψ σ g f (((m + 1 : ℕ) : ℤ) - 1) s'| ≤
              ∑ j ∈ Finset.range (J + 1), |M.ψ σ g f ((j : ℤ) - 1) s'| :=
            Finset.single_le_sum (f := fun j : ℕ => |M.ψ σ g f ((j : ℤ) - 1) s'|)
              (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
          linarith
        have hx : t * vf M ρ g (M.V ρ (stationary f)) s' ≤ t ^ (m + 1) * (2 * Dall) := by
          have h3 := le_abs_self (t ^ (m + 1) * M.ψ σ g f (((m + 1 : ℕ) : ℤ) - 1) s')
          rw [abs_mul, abs_of_pos (pow_pos ht0 _)] at h3
          have h4 : t ^ (m + 1 + 1) ≤ t ^ (m + 1) := pow_le_pow_of_le_one ht0.le ht1 (by omega)
          have h5 := (abs_le.mp h).2
          nlinarith [mul_le_mul_of_nonneg_left hc (pow_pos ht0 (m + 1)).le,
            mul_le_mul_of_nonneg_right h4 hD0]
        have htD : t * (2 * Dall) ≤ ε' := by
          have : t * (2 * Dall + 1) < ε' := by rwa [lt_div_iff₀ (by positivity)] at htη
          nlinarith
        calc t * vf M ρ g (M.V ρ (stationary f)) s' ≤ t ^ (m + 1) * (2 * Dall) := hx
          _ = t ^ m * (t * (2 * Dall)) := by ring
          _ ≤ t ^ m * ε' := mul_le_mul_of_nonneg_left htD (pow_pos ht0 _).le
          _ = ε' * t ^ m := by ring
      · -- negative first coefficient
        have hka := hk.1
        have hkb := hk.2
        set j1 := (k + 1).toNat with hj1def
        have hj1 : (j1 : ℤ) = k + 1 := by rw [hj1def]; omega
        have hz' : ∀ j < j1, M.ψ σ g f ((j : ℤ) - 1) s' = 0 := fun j hj =>
          hprev _ ⟨by omega, by omega⟩
        have hcj : M.ψ σ g f ((j1 : ℤ) - 1) s' = M.ψ σ g f k s' := by
          congr 1; omega
        set c := M.ψ σ g f k s'
        have hη : 0 < -c / (Dall + 1) := div_pos (by linarith) (by positivity)
        filter_upwards [hL0, hLsmall δ0 hδ0, hLsmall _ hη] with ρ ht0 htδ htη
        have h := hrow g s' ρ ht0 htδ j1 (by omega) hz'
        rw [hcj] at h
        set t := σ * ρ
        have h5 := (abs_le.mp h).2
        have htD : t * Dall ≤ -c := by
          have : t * (Dall + 1) < -c := by rwa [lt_div_iff₀ (by positivity)] at htη
          nlinarith
        have hx : t * vf M ρ g (M.V ρ (stationary f)) s' ≤ 0 := by
          have : t ^ (j1 + 1) * Dall = t ^ j1 * (t * Dall) := by ring
          nlinarith [mul_le_mul_of_nonneg_left htD (pow_pos ht0 j1).le]
        exact hx.trans (by positivity)
    have hall : ∀ᶠ ρ in L, ∀ g s', (σ * ρ) * vf M ρ g (M.V ρ (stationary f)) s'
        ≤ ε' * (σ * ρ) ^ m := by
      rw [eventually_all]; intro g; rw [eventually_all]; exact hper g
    filter_upwards [hall, hL0, hLsmall δ0 hδ0] with ρ hall ht0 htδ
    obtain ⟨hρ1, hβl, hβC⟩ := hB ρ ht0 htδ
    rw [hρabs ρ ht0]
    set t := σ * ρ
    set u := M.V ρ (stationary f)
    set e := ε' * t ^ m / t
    have he : 0 ≤ e := by positivity
    have hv : ∀ g s', vf M ρ g u s' ≤ e := fun g s' => by
      rw [le_div_iff₀ ht0, mul_comm]; exact hall g s'
    have hup := V_upper M hw1 hl0 hPw hρ1 hβl π u he hv s
    have hβC' : beta ρ / (1 - beta ρ * lam) * w s ≤ C0 / t * Ws := by
      have h0 : 0 ≤ beta ρ / (1 - beta ρ * lam) := by
        have : 0 < beta ρ := by unfold beta; exact inv_pos.mpr (by linarith)
        have : 0 < 1 - beta ρ * lam := by linarith
        positivity
      calc beta ρ / (1 - beta ρ * lam) * w s ≤ C0 / t * w s :=
            mul_le_mul_of_nonneg_right hβC (hw0 s).le
        _ ≤ C0 / t * Ws := mul_le_mul_of_nonneg_left hWs (by positivity)
    have hup2 : M.V ρ π s - u s ≤ e * (C0 / t * Ws) := by
      calc M.V ρ π s - u s ≤ e * (beta ρ / (1 - beta ρ * lam)) * w s := hup
        _ = e * (beta ρ / (1 - beta ρ * lam) * w s) := by ring
        _ ≤ e * (C0 / t * Ws) := mul_le_mul_of_nonneg_left hβC' he
    have hz : t ^ (-n) * t ^ m = t ^ 2 := by
      rw [← zpow_natCast, ← zpow_add₀ ht0.ne']
      have : -n + (m : ℤ) = ((2 : ℕ) : ℤ) := by omega
      rw [this, zpow_natCast]
    have htn : 0 < t ^ (-n) := zpow_pos ht0 _
    have hkey : t ^ (-n) * (e * (C0 / t * Ws)) = ε' * (C0 * Ws) := by
      have : t ^ (-n) * (e * (C0 / t * Ws)) = (t ^ (-n) * t ^ m) * ε' * C0 * Ws / (t * t) := by
        simp only [e]; field_simp
      rw [this, hz]; field_simp
    have hfin : ε' * (C0 * Ws) ≤ ε := by
      have : ε' * K1 = ε := by simp only [ε']; field_simp
      have h0 : 0 ≤ ε' := hε'.le
      nlinarith
    have := mul_le_mul_of_nonneg_left hup2 htn.le
    nlinarith
  ------------------------------------------------------------------ 2°
  · intro hD
    simp only [Model.D, if_neg (show ¬ n < -1 by omega), Set.mem_setOf_eq] at hD
    ext g
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hg
    obtain ⟨hnn, k1, hk1, s0, hne⟩ := hg
    rw [hΨ g n k1 hk1] at hne
    let T : St → Prop := fun s => ∃ k ∈ Set.Icc (-1 : ℤ) n, M.ψ σ g f k s ≠ 0
    let g' : DecisionRule A := fun s => if T s then g s else f s
    have hT0 : T s0 := ⟨k1, hk1, hne⟩
    -- rows in T have a positive first coefficient
    have hpos : ∀ s, T s → ∃ k ∈ Set.Icc (-1 : ℤ) n, 0 < M.ψ σ g f k s ∧
        ∀ j ∈ Set.Ico (-1 : ℤ) k, M.ψ σ g f j s = 0 := by
      intro s ⟨k, hk, hk0⟩
      rcases hnn s with h | ⟨k', hk', hpos', hprev'⟩
      · exact absurd (by rw [← hΨ g n k hk]; exact h k hk) hk0
      · refine ⟨k', hk', by rwa [hΨ g n k' hk'] at hpos', fun j hj => ?_⟩
        have := hprev' j hj
        rwa [hΨ g n j ⟨hj.1, by linarith [hj.2, hk'.2]⟩] at this
    -- eventual lower bound for rows in T
    have hlow : ∀ s, T s → ∃ c : ℝ, 0 < c ∧ ∃ j : ℕ, (j : ℤ) ≤ n + 1 ∧
        ∀ᶠ ρ in L, (σ * ρ) ^ j * c / 2 ≤ (σ * ρ) * vf M ρ g (M.V ρ (stationary f)) s := by
      intro s hs
      obtain ⟨k, hk, hkpos, hprev⟩ := hpos s hs
      have hka := hk.1
      have hkb := hk.2
      set j1 := (k + 1).toNat with hj1def
      have hj1 : (j1 : ℤ) = k + 1 := by rw [hj1def]; omega
      have hz' : ∀ j < j1, M.ψ σ g f ((j : ℤ) - 1) s = 0 := fun j hj =>
        hprev _ ⟨by omega, by omega⟩
      have hcj : M.ψ σ g f ((j1 : ℤ) - 1) s = M.ψ σ g f k s := by congr 1; omega
      set c := M.ψ σ g f k s
      refine ⟨c, hkpos, j1, by omega, ?_⟩
      have hη : 0 < c / (2 * Dall + 1) := div_pos hkpos (by linarith)
      filter_upwards [hL0, hLsmall δ0 hδ0, hLsmall _ hη] with ρ ht0 htδ htη
      have h := hrow g s ρ ht0 htδ j1 (by omega) hz'
      rw [hcj] at h
      set t := σ * ρ
      have h5 := (abs_le.mp h).1
      have htD : t * Dall ≤ c / 2 := by
        have h7 : t * (2 * Dall + 1) < c := by rwa [lt_div_iff₀ (by linarith)] at htη
        have e : t * (2 * Dall + 1) = 2 * (t * Dall) + t := by ring
        linarith only [h7, e, ht0]
      have h8 : t ^ (j1 + 1) * Dall = t ^ j1 * (t * Dall) := by ring
      have h6 := mul_le_mul_of_nonneg_left htD (pow_pos ht0 j1).le
      have e2 : t ^ j1 * (c / 2) = t ^ j1 * c / 2 := by ring
      linarith only [h5, h6, h8, e2]
    obtain ⟨c0, hc0, j0, hj0n, hev0⟩ := hlow s0 hT0
    have hnonneg : ∀ s, ∀ᶠ ρ in L, 0 ≤ vf M ρ g' (M.V ρ (stationary f)) s := by
      intro s
      by_cases hs : T s
      · obtain ⟨c, hc, j, -, hev⟩ := hlow s hs
        filter_upwards [hev, hL0] with ρ h ht0
        rw [vf_local M ρ _ s (show g' s = g s from if_pos hs)]
        have : 0 ≤ (σ * ρ) * vf M ρ g (M.V ρ (stationary f)) s :=
          le_trans (by positivity) h
        exact (mul_nonneg_iff_of_pos_left ht0).mp this
      · filter_upwards [hL0, hLsmall δ0 hδ0] with ρ ht0 htδ
        obtain ⟨hρ1, hβl, -⟩ := hB ρ ht0 htδ
        rw [vf_local M ρ _ s (show g' s = f s from if_neg hs),
          V_fixed M hw1 hl0 hPw hρ1 hβl f]
        simp
    have hnn_all : ∀ᶠ ρ in L, ∀ s, 0 ≤ vf M ρ g' (M.V ρ (stationary f)) s := by
      rw [eventually_all]; exact hnonneg
    have hopt := hD (stationary g') s0 (c0 / 8) (by positivity)
    have hfalse : ∀ᶠ ρ in L, False := by
      filter_upwards [hnn_all, hev0, hL0, hLsmall δ0 hδ0, hopt] with ρ hnn' h0 ht0 htδ hopt'
      obtain ⟨hρ1, hβl, -⟩ := hB ρ ht0 htδ
      rw [hρabs ρ ht0] at hopt'
      have hlow' := V_lower M hw1 hl0 hPw hρ1 hβl g' (M.V ρ (stationary f)) hnn' s0
      rw [vf_local M ρ _ s0 (show g' s0 = g s0 from if_pos hT0)] at hlow'
      have ht1 : σ * ρ < 1 := by linarith
      have hρ' : |ρ| < 1 := by rw [hρabs ρ ht0]; exact ht1
      have hβ : 1 / 2 ≤ beta ρ := by
        unfold beta
        have h1 : 0 < 1 + ρ := by linarith
        have h2 : 1 + ρ ≤ 2 := by linarith [le_abs_self ρ]
        rw [le_inv_comm₀ (by norm_num) h1]; linarith
      exact final2 ht0 ht1 hc0 hj0n hβ h0 hlow' hopt'
    obtain ⟨_, h⟩ := hfalse.exists
    exact h
