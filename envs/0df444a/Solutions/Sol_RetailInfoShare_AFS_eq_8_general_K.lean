-- Prove2me | solution 1 for RetailInfoShare.AFS.eq_8_general_K
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:02:00.577204+00:00
-- url     : https://prove2.me/submissions/6096be82-678a-4b95-ac17-6f7b8387ae20

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
import Theorems.Thm_RetailInfoShare_AFS_eq_4
import Theorems.Thm_RetailInfoShare_AFS_eq_5
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS.MeanAux

open RetailInfoShare.AFS

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma u_memLp (Z : Primitives P Ω μ) : MemLp Z.u 2 μ := by
  have h := Z.law_u
  have hm : MemLp (id : ℝ → ℝ) 2 (μ.map Z.u) := by
    rw [h.map_eq]; exact memLp_id_gaussianReal' 2 (by simp)
  exact (memLp_map_measure_iff aestronglyMeasurable_id h.aemeasurable).1 hm

lemma u_integral (Z : Primitives P Ω μ) : ∫ ω, Z.u ω ∂μ = 0 := by
  rw [Z.law_u.integral_eq, integral_id_gaussianReal]

/-- The "residual demand" `a − b Σ_{d≠i} q_d + u` faced by seller `i`. -/
noncomputable def resid (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) : Ω → ℝ :=
  fun ω => P.a - P.b * ∑ d ∈ Finset.univ.erase i, Q d ω + Z.u ω

lemma resid_memLp (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (hQ : ∀ d, MemLp (Q d) 2 μ)
    (i : Fin P.N) : MemLp (resid Z Q i) 2 μ := by
  haveI := Z.isProb
  have h1 : MemLp (fun ω => ∑ d ∈ Finset.univ.erase i, Q d ω) 2 μ :=
    memLp_finsetSum _ (fun d _ => hQ d)
  exact ((memLp_const P.a).sub (h1.const_mul P.b)).add (u_memLp Z)

lemma resid_integral (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (hQ : ∀ d, MemLp (Q d) 2 μ)
    (i : Fin P.N) :
    ∫ ω, resid Z Q i ω ∂μ = P.a - P.b * ∑ d ∈ Finset.univ.erase i, ∫ ω, Q d ω ∂μ := by
  haveI := Z.isProb
  have hI : ∀ d, Integrable (Q d) μ := fun d => (hQ d).integrable (by norm_num)
  have h1 : Integrable (fun ω => ∑ d ∈ Finset.univ.erase i, Q d ω) μ :=
    integrable_finsetSum _ (fun d _ => hI d)
  have hu : Integrable Z.u μ := (u_memLp Z).integrable (by norm_num)
  have h2 : Integrable (fun ω => P.b * ∑ d ∈ Finset.univ.erase i, Q d ω) μ := h1.const_mul _
  have h3 : Integrable (fun ω => P.a - P.b * ∑ d ∈ Finset.univ.erase i, Q d ω) μ :=
    (integrable_const _).sub h2
  unfold resid
  rw [integral_add h3 hu,
    integral_sub (integrable_const _) h2, integral_const_mul,
    integral_finsetSum _ (fun d _ => hI d), u_integral Z]
  simp

lemma resid_update (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) (q : Ω → ℝ) :
    resid Z (Function.update Q i q) i = resid Z Q i := by
  funext ω
  unfold resid
  congr 3
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]

lemma price_eq (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) :
    price Z Q i = fun ω => resid Z Q i ω - Q i ω := by
  funext ω; unfold price resid; ring

lemma sellerProfit_eq (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) :
    sellerProfit Z Q i = ∫ ω, (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω)) ∂μ := by
  unfold sellerProfit; rw [price_eq]

lemma sellerProfit_update (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ) (i : Fin P.N)
    (q : Ω → ℝ) :
    sellerProfit Z (Function.update Q i q) i =
      ∫ ω, (1 - P.alpha) * (q ω * (resid Z Q i ω - q ω)) ∂μ := by
  rw [sellerProfit_eq, resid_update]; simp

/-- Profit of seller `i` playing the constant `c`. -/
lemma sellerProfit_update_const (Z : Primitives P Ω μ) (Q : Fin P.N → Ω → ℝ)
    (hQ : ∀ d, MemLp (Q d) 2 μ) (i : Fin P.N) (c : ℝ) :
    sellerProfit Z (Function.update Q i (fun _ => c)) i =
      (1 - P.alpha) * (c * (∫ ω, resid Z Q i ω ∂μ - c)) := by
  haveI := Z.isProb
  rw [sellerProfit_update]
  have hr : Integrable (resid Z Q i) μ := (resid_memLp Z Q hQ i).integrable (by norm_num)
  rw [integral_const_mul, integral_const_mul, integral_sub hr (integrable_const c)]
  simp

/-- Constant perturbations: in any equilibrium, `2 E[q_i] = E[a − b Σ_{d≠i} q_d + u]`. -/
lemma eq_mean (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (i : Fin P.N) :
    2 * ∫ ω, Q i ω ∂μ = ∫ ω, resid Z Q i ω ∂μ := by
  haveI := Z.isProb
  have hL : ∀ d, MemLp (Q d) 2 μ := fun d => (hQ.1 d).2
  set EA := ∫ ω, resid Z Q i ω ∂μ
  set EQ := ∫ ω, Q i ω ∂μ
  set c := (EA - 2 * EQ) / 2
  have hadm : IsAdmissible Z M i (fun ω => Q i ω + c) :=
    ⟨(hQ.1 i).1.add stronglyMeasurable_const, (hQ.1 i).2.add (memLp_const c)⟩
  have hle := hQ.2 i _ hadm
  rw [sellerProfit_update, sellerProfit_eq] at hle
  have hr : MemLp (resid Z Q i) 2 μ := resid_memLp Z Q hL i
  have hQi : MemLp (Q i) 2 μ := hL i
  have i1 : Integrable (fun ω => Q i ω * resid Z Q i ω) μ := hQi.integrable_mul hr
  have i2 : Integrable (fun ω => Q i ω * Q i ω) μ := hQi.integrable_mul hQi
  have iQ : Integrable (Q i) μ := hQi.integrable (by norm_num)
  have iR : Integrable (resid Z Q i) μ := hr.integrable (by norm_num)
  have e1 : (fun ω => (1 - P.alpha) * ((Q i ω + c) * (resid Z Q i ω - (Q i ω + c)))) =
      fun ω => (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω)) +
        (1 - P.alpha) * (c * resid Z Q i ω - 2 * c * Q i ω - c ^ 2) := by
    funext ω; ring
  have j1 : Integrable (fun ω => (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω))) μ := by
    have : (fun ω => (1 - P.alpha) * (Q i ω * (resid Z Q i ω - Q i ω))) =
        fun ω => (1 - P.alpha) * (Q i ω * resid Z Q i ω - Q i ω * Q i ω) := by
      funext ω; ring
    rw [this]; exact (i1.sub i2).const_mul _
  have j2 : Integrable (fun ω => (1 - P.alpha) * (c * resid Z Q i ω - 2 * c * Q i ω - c ^ 2))
      μ := (((iR.const_mul c).sub (iQ.const_mul (2 * c))).sub (integrable_const _)).const_mul _
  rw [e1, integral_add j1 j2] at hle
  have hval : ∫ ω, (1 - P.alpha) * (c * resid Z Q i ω - 2 * c * Q i ω - c ^ 2) ∂μ =
      (1 - P.alpha) * (c * EA - 2 * c * EQ - c ^ 2) := by
    have k1 : Integrable (fun ω => c * resid Z Q i ω) μ := iR.const_mul c
    have k2 : Integrable (fun ω => 2 * c * Q i ω) μ := iQ.const_mul (2 * c)
    have k3 : Integrable (fun ω => c * resid Z Q i ω - 2 * c * Q i ω) μ := k1.sub k2
    rw [integral_const_mul, integral_sub k3 (integrable_const _), integral_sub k1 k2,
      integral_const_mul, integral_const_mul]
    simp [EA, EQ]
  rw [hval] at hle
  have ha : 0 < 1 - P.alpha := by linarith [hP.2.2.2.2.2.2]
  have : (1 - P.alpha) * (c * EA - 2 * c * EQ - c ^ 2) ≤ 0 := by linarith
  have hc2 : c * EA - 2 * c * EQ - c ^ 2 = c ^ 2 := by simp only [c]; ring
  rw [hc2] at this
  have : c ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have : c = 0 := by nlinarith [sq_nonneg c]
  simp only [c] at this
  linarith

/-- The linear system `2 x_i = a − b Σ_{d≠i} x_d` has the unique solution `qNS`. -/
lemma linear_system (P : Params) (hP : P.Standing) (x : Fin P.N → ℝ)
    (hx : ∀ i, 2 * x i = P.a - P.b * ∑ d ∈ Finset.univ.erase i, x d) (i : Fin P.N) :
    x i = qNS P := by
  obtain ⟨hN, hb0, hb1, -⟩ := hP
  set T := ∑ d, x d
  have hx' : ∀ i, (2 - P.b) * x i = P.a - P.b * T := by
    intro i
    have := hx i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at this
    linarith
  have hsum : (2 - P.b) * T = P.N * P.a - P.N * P.b * T := by
    have : ∑ i, (2 - P.b) * x i = ∑ _i : Fin P.N, (P.a - P.b * T) :=
      Finset.sum_congr rfl (fun i _ => hx' i)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    rw [this]; ring
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hN
  have hD : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have h2b : (2 - P.b) ≠ 0 := by intro h; linarith
  unfold qNS
  rw [eq_div_iff hD.ne']
  have key : (2 - P.b) * (x i * (2 + P.b * ((P.N : ℝ) - 1))) = (2 - P.b) * P.a := by
    have h1 := hx' i
    have : (2 - P.b) * (x i * (2 + P.b * ((P.N : ℝ) - 1))) =
        ((2 - P.b) * x i) * (2 - P.b) + ((2 - P.b) * x i) * (P.b * P.N) := by ring
    rw [this, h1]
    nlinarith [hsum]
  exact mul_left_cancel₀ h2b key

/-- In every equilibrium, every seller's mean quantity is `qNS`. -/
lemma mean_eq_qNS (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (i : Fin P.N) : ∫ ω, Q i ω ∂μ = qNS P := by
  refine linear_system P hP (fun i => ∫ ω, Q i ω ∂μ) (fun i => ?_) i
  rw [eq_mean P hP Z M Q hQ i, resid_integral Z Q (fun d => (hQ.1 d).2) i]

lemma info_bot (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (j : Fin P.N)
    (hj : ∀ i, M i j = ⊤) : info Z M j = ⊥ := by
  simp [info, hj]

/-- An uninformed seller plays the constant `qNS` in every equilibrium. -/
lemma uninformed_const (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (j : Fin P.N) (hj : ∀ i, M i j = ⊤) :
    Q j = fun _ => qNS P := by
  haveI := Z.isProb
  have hm := (hQ.1 j).1
  rw [info_bot Z M j hj] at hm
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp hm
  have := mean_eq_qNS P hP Z M Q hQ j
  rw [hc] at this ⊢
  simp at this
  rw [this]

/-- An uninformed seller earns `(1 − α) qNS²` in every equilibrium. -/
lemma uninformed_profit (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z M Q) (j : Fin P.N) (hj : ∀ i, M i j = ⊤) :
    sellerProfit Z Q j = (1 - P.alpha) * qNS P ^ 2 := by
  have hc := uninformed_const P hP Z M Q hQ j hj
  have hmean := eq_mean P hP Z M Q hQ j
  have hQQ : Q = Function.update Q j (fun _ => qNS P) := by
    rw [← hc]; simp
  have hL : ∀ d, MemLp (Q d) 2 μ := fun d => (hQ.1 d).2
  have := sellerProfit_update_const Z Q hL j (qNS P)
  rw [← hQQ] at this
  rw [this, ← hmean, hc]
  haveI := Z.isProb
  simp only [integral_const, probReal_univ, one_smul]; ring

end RetailInfoShare.AFS.MeanAux

namespace RetailInfoShare.AFS.GaussAux

open RetailInfoShare.AFS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Covariance of two linear combinations of independent centered Gaussians. -/
lemma cov_lin [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hlaw : ∀ k, HasLaw (Y k) (gaussianReal 0 (v k)) μ) (hind : iIndepFun Y μ)
    (α β : ι → ℝ) :
    cov[fun ω => ∑ k, α k * Y k ω, fun ω => ∑ k, β k * Y k ω; μ] =
      ∑ k, α k * β k * (v k : ℝ) := by
  have hmem : ∀ k, MemLp (Y k) 2 μ := fun k =>
    (hlaw k).hasGaussianLaw.memLp_two
  rw [covariance_fun_sum_fun_sum (fun k => (hmem k).const_mul (α k))
    (fun k => (hmem k).const_mul (β k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hlaw k).aemeasurable, (hlaw k).variance_eq, variance_id_gaussianReal]
    ring
  · intro l _ hlk
    rw [covariance_const_mul_left, covariance_const_mul_right,
      (hind.indepFun (Ne.symm hlk)).covariance_eq_zero (hmem k) (hmem l)]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

end RetailInfoShare.AFS.GaussAux

namespace RetailInfoShare.AFS.Eq5Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.GaussAux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The primitives relevant to seller `j`: `u`, the `e i`, and the `ξ i j`. -/
def idx (j : Fin P.N) : Option (Fin P.N ⊕ Fin P.N) → Prim P.N
  | none => .u
  | some (.inl i) => .e i
  | some (.inr i) => .ξ i j

lemma idx_injective (j : Fin P.N) : Function.Injective (idx (P := P) j) := by
  intro x y h
  rcases x with _ | x | x <;> rcases y with _ | y | y <;> simp_all [idx]

/-- The random variables indexed by `idx j`. -/
def Yv (Z : Primitives P Ω μ) (j : Fin P.N) : Option (Fin P.N ⊕ Fin P.N) → Ω → ℝ
  | none => Z.u
  | some (.inl i) => Z.e i
  | some (.inr i) => Z.ξ i j

def vv (P : Params) : Option (Fin P.N ⊕ Fin P.N) → ℝ≥0
  | none => P.sig
  | some (.inl _) => P.t
  | some (.inr _) => 1

lemma Yv_law (Z : Primitives P Ω μ) (j : Fin P.N) :
    ∀ k, HasLaw (Yv Z j k) (gaussianReal 0 (vv P k)) μ := by
  intro k
  rcases k with _ | i | i
  · exact Z.law_u
  · exact Z.law_e i
  · exact Z.law_ξ i j

lemma Yv_indep (Z : Primitives P Ω μ) (j : Fin P.N) : iIndepFun (Yv Z j) μ := by
  have h := Z.indep.precomp (idx_injective (P := P) j)
  convert h using 2 with k
  rcases k with _ | i | i <;> rfl

end RetailInfoShare.AFS.Eq5Aux

namespace RetailInfoShare.AFS.Eq8Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux RetailInfoShare.AFS.GaussAux
  RetailInfoShare.AFS.Eq5Aux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Posterior weight `σ / (σ + t/N)` under truthful full sharing. -/
noncomputable def lam (P : Params) : ℝ := (P.sig : ℝ) / ((P.sig : ℝ) + (P.t : ℝ) / P.N)

/-- `2 + b(K − 1)`. -/
noncomputable def Dk (P : Params) (K : ℕ) : ℝ := 2 + P.b * ((K : ℝ) - 1)

/-- Average of the (unperturbed) signals `x_i = u + e_i`. -/
noncomputable def xbar (Z : Primitives P Ω μ) : Ω → ℝ :=
  fun ω => (1 / (P.N : ℝ)) * ∑ i, (Z.u ω + Z.e i ω)

/-- The candidate equilibrium under truthful sharing with sellers `0, …, K − 1`. -/
noncomputable def Qc (Z : Primitives P Ω μ) (K : ℕ) : Fin P.N → Ω → ℝ :=
  fun d ω => if (d : ℕ) < K then qNS P + lam P * xbar Z ω / Dk P K else qNS P

lemma sum_ite_lt (K : ℕ) (hK : K ≤ P.N) (A B : ℝ) :
    ∑ d : Fin P.N, (if (d : ℕ) < K then A else B) = K * A + ((P.N : ℝ) - K) * B := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h1 : (Finset.univ.filter (fun d : Fin P.N => (d : ℕ) < K)).card = K := by
    rw [Fin.card_filter_val_lt]; exact min_eq_right hK
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun d : Fin P.N => (d : ℕ) < K)
  rw [Finset.card_univ, Fintype.card_fin, h1] at h2
  have h3 : (Finset.univ.filter (fun d : Fin P.N => ¬ (d : ℕ) < K)).card = P.N - K := by
    omega
  rw [h1, h3, Nat.cast_sub hK]

lemma xhat_tg (Z : Primitives P Ω μ) (K : ℕ) (i j : Fin P.N) (hj : (j : ℕ) < K) :
    xhat Z (truthfulGroup P.N K) i j = fun ω => Z.u ω + Z.e i ω := by
  funext ω; simp [xhat, truthfulGroup, hj]

lemma info_tg_eq (Z : Primitives P Ω μ) (K : ℕ) (j j' : Fin P.N) (hj : (j : ℕ) < K)
    (hj' : (j' : ℕ) < K) :
    info Z (truthfulGroup P.N K) j = info Z (truthfulGroup P.N K) j' := by
  unfold info
  refine iSup_congr fun i => ?_
  rw [xhat_tg Z K i j hj, xhat_tg Z K i j' hj']
  simp [truthfulGroup, hj, hj']

lemma info_tg_bot (Z : Primitives P Ω μ) (K : ℕ) (j : Fin P.N) (hj : ¬ (j : ℕ) < K) :
    info Z (truthfulGroup P.N K) j = ⊥ :=
  info_bot Z _ j (fun i => by simp [truthfulGroup, hj])

lemma tg_top (K : ℕ) (j : Fin P.N) (hj : ¬ (j : ℕ) < K) :
    ∀ i, truthfulGroup P.N K i j = ⊤ := fun i => by simp [truthfulGroup, hj]

lemma info_tg_le (Z : Primitives P Ω μ) (K : ℕ) (j : Fin P.N) :
    info Z (truthfulGroup P.N K) j ≤ ‹MeasurableSpace Ω› := by
  refine iSup_le fun i => iSup_le fun _ => ?_
  unfold xhat
  exact ((Z.meas_u.add (Z.meas_e i)).add ((Z.meas_ξ i j).const_mul _)).comap_le

lemma xbar_meas (Z : Primitives P Ω μ) (K : ℕ) (j : Fin P.N) (hj : (j : ℕ) < K) :
    Measurable[info Z (truthfulGroup P.N K) j] (xbar Z) := by
  have hx : ∀ i, Measurable[info Z (truthfulGroup P.N K) j] (fun ω => Z.u ω + Z.e i ω) := by
    intro i
    have hle : MeasurableSpace.comap (xhat Z (truthfulGroup P.N K) i j) inferInstance ≤
        info Z (truthfulGroup P.N K) j := by
      unfold info
      exact le_iSup₂ (f := fun i (_ : truthfulGroup P.N K i j ≠ ⊤) =>
        MeasurableSpace.comap (xhat Z (truthfulGroup P.N K) i j) inferInstance) i
        (by simp [truthfulGroup, hj])
    have := (Measurable.of_comap_le (le_refl (MeasurableSpace.comap
      (xhat Z (truthfulGroup P.N K) i j) inferInstance))).mono hle le_rfl
    rwa [xhat_tg Z K i j hj] at this
  unfold xbar
  exact (Finset.measurable_sum _ (fun i _ => hx i)).const_mul _

lemma xbar_memLp (Z : Primitives P Ω μ) : MemLp (xbar Z) 2 μ := by
  haveI := Z.isProb
  have he : ∀ i, MemLp (Z.e i) 2 μ := fun i => (Z.law_e i).hasGaussianLaw.memLp_two
  unfold xbar
  exact (memLp_finsetSum _ (fun i _ => (u_memLp Z).add (he i))).const_mul _

/-- Moments of `xbar` and `u`. -/
lemma moments (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) :
    ∫ ω, xbar Z ω ∂μ = 0 ∧ ∫ ω, xbar Z ω * xbar Z ω ∂μ = (P.sig : ℝ) + (P.t : ℝ) / P.N ∧
      ∫ ω, xbar Z ω * Z.u ω ∂μ = P.sig := by
  classical
  haveI := Z.isProb
  have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.1
  let j0 : Fin P.N := ⟨0, hP.1⟩
  let β : Option (Fin P.N ⊕ Fin P.N) → ℝ := fun k =>
    match k with
    | none => 1
    | some (.inl _) => 1 / (P.N : ℝ)
    | some (.inr _) => 0
  let α : Option (Fin P.N ⊕ Fin P.N) → ℝ := fun k =>
    match k with
    | none => 1
    | some (.inl _) => 0
    | some (.inr _) => 0
  have hx : xbar Z = fun ω => ∑ k, β k * Yv Z j0 k ω := by
    funext ω
    simp only [xbar, Fintype.sum_option, Fintype.sum_sum_type, β, Yv,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, zero_mul, Finset.sum_const_zero, add_zero]
    field_simp
    ring
  have hu : Z.u = fun ω => ∑ k, α k * Yv Z j0 k ω := by
    funext ω
    simp [Fintype.sum_option, Fintype.sum_sum_type, α, Yv]
  have hint : ∀ γ : Option (Fin P.N ⊕ Fin P.N) → ℝ,
      ∫ ω, ∑ k, γ k * Yv Z j0 k ω ∂μ = 0 := by
    intro γ
    rw [integral_finsetSum _ (fun k _ =>
      ((Yv_law Z j0 k).hasGaussianLaw.integrable).const_mul _)]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [integral_const_mul, (Yv_law Z j0 k).integral_eq, integral_id_gaussianReal, mul_zero]
  have hcov : ∀ γ δ : Option (Fin P.N ⊕ Fin P.N) → ℝ,
      ∫ ω, (∑ k, γ k * Yv Z j0 k ω) * (∑ k, δ k * Yv Z j0 k ω) ∂μ =
        ∑ k, γ k * δ k * (vv P k : ℝ) := by
    intro γ δ
    have := cov_lin (Yv Z j0) (vv P) (Yv_law Z j0) (Yv_indep Z j0) γ δ
    rw [covariance] at this
    simp only [hint, sub_zero] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact hint β
  · rw [hx, hcov]
    simp only [Fintype.sum_option, Fintype.sum_sum_type, β, vv, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_one]
    field_simp
    ring
  · rw [hx, hu]
    conv_lhs => rw [hcov]
    simp [Fintype.sum_option, Fintype.sum_sum_type, β, α, vv]

lemma posterior (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (K : ℕ) (j : Fin P.N) (hj : (j : ℕ) < K) :
    μ[Z.u | info Z (truthfulGroup P.N K) j] =ᵐ[μ] fun ω => lam P * xbar Z ω := by
  have h := eq_5 P hP μ Z (truthfulGroup P.N K) j 0 (fun i => by simp [truthfulGroup, hj])
  filter_upwards [h] with ω hω
  rw [hω]
  simp only [xhat_tg Z K _ j hj, lam, xbar, NNReal.coe_zero, add_zero]

/-- Pointwise solution of the informed sellers' linear system. -/
lemma solve (P : Params) (hP : P.Standing) (K : ℕ) (hK : K ≤ P.N) (p : ℝ)
    (x : Fin P.N → ℝ) (hout : ∀ d : Fin P.N, ¬ (d : ℕ) < K → x d = qNS P)
    (hin : ∀ i : Fin P.N, (i : ℕ) < K →
      x i = (P.a - P.b * ∑ d ∈ Finset.univ.erase i, x d + p) / 2) :
    ∀ i : Fin P.N, (i : ℕ) < K → x i = qNS P + p / Dk P K := by
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hP.1
  have hD0 : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have hKr : (K : ℝ) ≤ P.N := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hDK : 0 < Dk P K := by unfold Dk; nlinarith
  set T := ∑ d, x d
  have h1 : ∀ i : Fin P.N, (i : ℕ) < K → (2 - P.b) * x i = P.a - P.b * T + p := by
    intro i hi
    have := hin i hi
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at this
    linarith
  set y := (P.a - P.b * T + p) / (2 - P.b)
  have h2b : 0 < 2 - P.b := by linarith
  have hy : ∀ i : Fin P.N, (i : ℕ) < K → x i = y := by
    intro i hi
    rw [eq_div_iff h2b.ne']; linarith [h1 i hi]
  have hx : x = fun d : Fin P.N => if (d : ℕ) < K then y else qNS P := by
    funext d
    split_ifs with h
    · exact hy d h
    · exact hout d h
  have hT : T = K * y + ((P.N : ℝ) - K) * qNS P := by
    simp only [T]; rw [hx]; exact sum_ite_lt K hK y (qNS P)
  have hyeq : (2 - P.b) * y = P.a - P.b * T + p := by
    simp only [y]; field_simp
  intro i hi
  rw [hy i hi]
  have hq : qNS P * (2 + P.b * ((P.N : ℝ) - 1)) = P.a := by
    unfold qNS; field_simp
  rw [hT] at hyeq
  unfold Dk at hDK ⊢
  rw [eq_comm, ← sub_eq_zero]
  have : (y - (qNS P + p / (2 + P.b * ((K : ℝ) - 1)))) * (2 + P.b * ((K : ℝ) - 1)) = 0 := by
    field_simp
    nlinarith [hyeq, hq]
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

lemma Qc_apply_in (Z : Primitives P Ω μ) (K : ℕ) (d : Fin P.N) (hd : (d : ℕ) < K) :
    Qc Z K d = fun ω => qNS P + lam P * xbar Z ω / Dk P K := by
  funext ω; simp [Qc, hd]

lemma Qc_apply_out (Z : Primitives P Ω μ) (K : ℕ) (d : Fin P.N) (hd : ¬ (d : ℕ) < K) :
    Qc Z K d = fun _ => qNS P := by
  funext ω; simp [Qc, hd]

lemma Qc_memLp (Z : Primitives P Ω μ) (K : ℕ) (d : Fin P.N) : MemLp (Qc Z K d) 2 μ := by
  haveI := Z.isProb
  have h1 : MemLp (fun ω => (lam P / Dk P K) * xbar Z ω) 2 μ := (xbar_memLp Z).const_mul _
  have h2 : MemLp (fun ω => qNS P + (lam P / Dk P K) * xbar Z ω) 2 μ :=
    (memLp_const (qNS P)).add h1
  have e : (fun ω => qNS P + lam P * xbar Z ω / Dk P K) =
      fun ω => qNS P + (lam P / Dk P K) * xbar Z ω := by funext ω; ring
  by_cases hd : (d : ℕ) < K
  · rw [Qc_apply_in Z K d hd, e]
    exact h2
  · rw [Qc_apply_out Z K d hd]; exact memLp_const _

lemma Qc_meas (Z : Primitives P Ω μ) (K : ℕ) (i d : Fin P.N) (hi : (i : ℕ) < K) :
    StronglyMeasurable[info Z (truthfulGroup P.N K) i] (Qc Z K d) := by
  by_cases hd : (d : ℕ) < K
  · rw [Qc_apply_in Z K d hd]
    exact (measurable_const.add (((xbar_meas Z K i hi).const_mul _).div_const _)).stronglyMeasurable
  · rw [Qc_apply_out Z K d hd]; exact stronglyMeasurable_const

lemma Qc_integral (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (K : ℕ) (d : Fin P.N) :
    ∫ ω, Qc Z K d ω ∂μ = qNS P := by
  haveI := Z.isProb
  by_cases hd : (d : ℕ) < K
  · rw [Qc_apply_in Z K d hd]
    have : (fun ω => qNS P + lam P * xbar Z ω / Dk P K) =
        fun ω => qNS P + (lam P / Dk P K) * xbar Z ω := by funext ω; ring
    rw [this, integral_add (integrable_const _)
      (((xbar_memLp Z).integrable (by norm_num)).const_mul _), integral_const_mul,
      (moments P hP Z).1]
    simp
  · rw [Qc_apply_out Z K d hd]; simp

/-- The candidate is an equilibrium. -/
lemma Qc_equilibrium (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (K : ℕ) (hK : K ≤ P.N) :
    IsEquilibrium Z (truthfulGroup P.N K) (Qc Z K) := by
  haveI := Z.isProb
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hP.1
  have hD0 : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have hKr : (K : ℝ) ≤ P.N := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hDK : 0 < Dk P K := by unfold Dk; nlinarith
  have hadm : ∀ j, IsAdmissible Z (truthfulGroup P.N K) j (Qc Z K j) := by
    intro j
    refine ⟨?_, Qc_memLp Z K j⟩
    by_cases hj : (j : ℕ) < K
    · exact Qc_meas Z K j j hj
    · rw [Qc_apply_out Z K j hj]; exact stronglyMeasurable_const
  refine (eq_4 P hP μ Z _ (Qc Z K) hadm).2 (fun i => ?_)
  by_cases hi : (i : ℕ) < K
  · have hc : ∀ d, μ[Qc Z K d | info Z (truthfulGroup P.N K) i] = Qc Z K d := fun d =>
      condExp_of_stronglyMeasurable (info_tg_le Z K i) (Qc_meas Z K i d hi)
        ((Qc_memLp Z K d).integrable (by norm_num))
    filter_upwards [posterior P hP Z K i hi] with ω hω
    simp only [hc, hω]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have hs : ∑ d, Qc Z K d ω = K * (qNS P + lam P * xbar Z ω / Dk P K) +
        ((P.N : ℝ) - K) * qNS P := by
      simp only [Qc]; exact sum_ite_lt K hK _ _
    rw [hs]
    simp only [Qc, hi, if_true]
    have hq : qNS P * (2 + P.b * ((P.N : ℝ) - 1)) = P.a := by unfold qNS; field_simp
    unfold Dk at hDK ⊢
    rw [← hq]
    field_simp
    ring
  · have hbot := info_tg_bot Z K i hi
    have hc : ∀ d, μ[Qc Z K d | info Z (truthfulGroup P.N K) i] = fun _ => qNS P := by
      intro d
      rw [hbot, condExp_bot', Qc_integral P hP Z K d]
      simp
    have hcu : μ[Z.u | info Z (truthfulGroup P.N K) i] = fun _ => 0 := by
      rw [hbot, condExp_bot', u_integral Z]
      simp
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [hc, hcu, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hP.1, Nat.cast_one]
    simp only [Qc, hi, if_false]
    unfold qNS
    field_simp
    ring

/-- Every equilibrium coincides a.e. with the candidate. -/
lemma eq_ae (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (K : ℕ) (hK : K ≤ P.N)
    (Q : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z (truthfulGroup P.N K) Q) :
    ∀ᵐ ω ∂μ, ∀ i, Q i ω = Qc Z K i ω := by
  haveI := Z.isProb
  have hout : ∀ d : Fin P.N, ¬ (d : ℕ) < K → Q d = fun _ => qNS P := fun d hd =>
    uninformed_const P hP Z _ Q hQ d (tg_top K d hd)
  have hfoc := (eq_4 P hP μ Z _ Q hQ.1).1 hQ
  have hc : ∀ i d : Fin P.N, (i : ℕ) < K → μ[Q d | info Z (truthfulGroup P.N K) i] = Q d := by
    intro i d hi
    refine condExp_of_stronglyMeasurable (info_tg_le Z K i) ?_
      (((hQ.1 d).2).integrable (by norm_num))
    by_cases hd : (d : ℕ) < K
    · rw [info_tg_eq Z K i d hi hd]; exact (hQ.1 d).1
    · rw [hout d hd]; exact stronglyMeasurable_const
  have hall : ∀ i : Fin P.N, ∀ᵐ ω ∂μ, (i : ℕ) < K →
      Q i ω = (P.a - P.b * ∑ d ∈ Finset.univ.erase i, Q d ω + lam P * xbar Z ω) / 2 := by
    intro i
    by_cases hi : (i : ℕ) < K
    · filter_upwards [hfoc i, posterior P hP Z K i hi] with ω h1 h2 _
      rw [h1]
      simp only [hc i _ hi, h2]
    · exact Filter.Eventually.of_forall (fun ω h => absurd h hi)
  filter_upwards [ae_all_iff.2 hall] with ω hω
  have hsol := solve P hP K hK (lam P * xbar Z ω) (fun d => Q d ω)
    (fun d hd => by rw [hout d hd]) hω
  intro i
  by_cases hi : (i : ℕ) < K
  · rw [hsol i hi]; simp [Qc, hi]
  · rw [hout i hi]; simp [Qc, hi]

lemma platformProfit_congr (Z : Primitives P Ω μ) (Q Q' : Fin P.N → Ω → ℝ)
    (h : ∀ᵐ ω ∂μ, ∀ i, Q i ω = Q' i ω) : platformProfit Z Q = platformProfit Z Q' := by
  unfold platformProfit
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  simp only [price, hω]

lemma sellerProfit_congr (Z : Primitives P Ω μ) (Q Q' : Fin P.N → Ω → ℝ)
    (h : ∀ᵐ ω ∂μ, ∀ i, Q i ω = Q' i ω) (j : Fin P.N) :
    sellerProfit Z Q j = sellerProfit Z Q' j := by
  unfold sellerProfit
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  simp only [price, hω]

end RetailInfoShare.AFS.Eq8Aux
namespace RetailInfoShare.AFS.Eq8Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.MeanAux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integral of a quadratic polynomial in `(xbar, u)`. -/
lemma integral_quad (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (Z : Primitives P Ω μ) (C0 C1 C2 C3 C4 : ℝ) :
    ∫ ω, (C0 + C1 * xbar Z ω + C2 * Z.u ω + C3 * (xbar Z ω * xbar Z ω) +
        C4 * (xbar Z ω * Z.u ω)) ∂μ =
      C0 + C3 * ((P.sig : ℝ) + (P.t : ℝ) / P.N) + C4 * P.sig := by
  haveI := Z.isProb
  obtain ⟨m1, m2, m3⟩ := moments P hP Z
  have hX := xbar_memLp Z
  have hU := u_memLp Z
  have iX : Integrable (fun ω => C1 * xbar Z ω) μ := (hX.integrable (by norm_num)).const_mul _
  have iU : Integrable (fun ω => C2 * Z.u ω) μ := (hU.integrable (by norm_num)).const_mul _
  have iXX : Integrable (fun ω => C3 * (xbar Z ω * xbar Z ω)) μ :=
    (hX.integrable_mul hX).const_mul _
  have iXU : Integrable (fun ω => C4 * (xbar Z ω * Z.u ω)) μ :=
    (hX.integrable_mul hU).const_mul _
  have s1 : Integrable (fun ω => C0 + C1 * xbar Z ω) μ := (integrable_const _).add iX
  have s2 : Integrable (fun ω => C0 + C1 * xbar Z ω + C2 * Z.u ω) μ := s1.add iU
  have s3 : Integrable (fun ω => C0 + C1 * xbar Z ω + C2 * Z.u ω +
      C3 * (xbar Z ω * xbar Z ω)) μ := s2.add iXX
  rw [integral_add s3 iXU, integral_add s2 iXX, integral_add s1 iU,
    integral_add (integrable_const _) iX, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, m1, m2, m3, u_integral Z]
  simp

/-- Pointwise sum over sellers of a function of the candidate quantities. -/
lemma sum_Qc (Z : Primitives P Ω μ) (K : ℕ) (hK : K ≤ P.N) (g : ℝ → ℝ) (ω : Ω) :
    ∑ i, g (Qc Z K i ω) =
      K * g (qNS P + lam P * xbar Z ω / Dk P K) + ((P.N : ℝ) - K) * g (qNS P) := by
  rw [← sum_ite_lt K hK]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Qc]; split_ifs <;> rfl

lemma price_Qc (Z : Primitives P Ω μ) (K : ℕ) (hK : K ≤ P.N) (i : Fin P.N) (ω : Ω) :
    price Z (Qc Z K) i ω = P.a - Qc Z K i ω -
      P.b * (P.N * qNS P + K * (lam P * xbar Z ω / Dk P K) - Qc Z K i ω) + Z.u ω := by
  unfold price
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have hs : ∑ d, Qc Z K d ω = P.N * qNS P + K * (lam P * xbar Z ω / Dk P K) := by
    have := sum_Qc Z K hK (fun v => v) ω
    try simp only at this
    rw [this]; ring
  rw [hs]

lemma profit_Qc (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (K : ℕ) (hK : K ≤ P.N) :
    platformProfit Z (Qc Z K) = PiNS P + sharingGain P K := by
  have hb0 := hP.2.1
  have hb1 := hP.2.2.1
  have hN' : (1 : ℝ) ≤ P.N := by exact_mod_cast hP.1
  have hD0 : 0 < 2 + P.b * ((P.N : ℝ) - 1) := by nlinarith
  have hKr : (K : ℝ) ≤ P.N := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hDK : 0 < Dk P K := by unfold Dk; nlinarith
  have hs : (0 : ℝ) < P.sig := NNReal.coe_pos.mpr hP.2.2.2.1
  have ht : (0 : ℝ) < P.t := NNReal.coe_pos.mpr hP.2.2.2.2.1
  have hS : (0 : ℝ) < (P.sig : ℝ) + (P.t : ℝ) / P.N := by positivity
  set q0 := qNS P with hq0
  set r := lam P / Dk P K with hr
  set A0 := P.a - (1 - P.b) * q0 - P.b * P.N * q0 with hA0
  set E1 := 1 - P.b + P.b * K with hE1
  have hpt : ∀ ω, P.alpha * ∑ i, Qc Z K i ω * price Z (Qc Z K) i ω =
      P.alpha * (P.N * q0 * A0) + P.alpha * (r * (K * (A0 - q0 * E1) - (P.N - K) * q0 * P.b * K))
        * xbar Z ω + P.alpha * (P.N * q0) * Z.u ω + P.alpha * (-(K * E1 * r ^ 2)) *
        (xbar Z ω * xbar Z ω) + P.alpha * (K * r) * (xbar Z ω * Z.u ω) := by
    intro ω
    simp_rw [price_Qc Z K hK]
    have := sum_Qc Z K hK (fun v => v * (P.a - v - P.b * (P.N * q0 + K * (lam P * xbar Z ω /
      Dk P K) - v) + Z.u ω)) ω
    try simp only at this
    rw [this]
    have hY : lam P * xbar Z ω / Dk P K = r * xbar Z ω := by rw [hr]; ring
    rw [hY]
    ring
  unfold platformProfit
  simp_rw [hpt]
  rw [integral_quad P hP Z]
  -- algebra
  have hq : q0 * (2 + P.b * ((P.N : ℝ) - 1)) = P.a := by rw [hq0]; unfold qNS; field_simp
  have hA : A0 = q0 := by rw [hA0, ← hq]; ring
  rw [hA, hr, hE1]
  unfold PiNS sharingGain lam Dk
  unfold Dk at hDK
  rw [← hq]
  field_simp
  ring

end RetailInfoShare.AFS.Eq8Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.Eq8Aux in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (K : ℕ) (hK : K ≤ P.N) :
    (∃ Q, IsEquilibrium Z (truthfulGroup P.N K) Q) ∧
    ∀ Q, IsEquilibrium Z (truthfulGroup P.N K) Q →
      platformProfit Z Q = PiNS P + sharingGain P K := by
  refine ⟨⟨Qc Z K, Qc_equilibrium P hP μ Z K hK⟩, fun Q hQ => ?_⟩
  rw [platformProfit_congr Z Q (Qc Z K) (eq_ae P hP μ Z K hK Q hQ)]
  exact profit_Qc P hP μ Z K hK
