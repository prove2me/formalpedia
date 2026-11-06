-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.theorem_8_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:58:48.988744+00:00
-- url     : https://prove2.me/submissions/114be88a-d2ba-4fa7-9c67-3fb07b0d70cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_3_1
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_3_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_1
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_corollary_4_1
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_5_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_proposition_4_1
import Theorems.Thm_SelfScaledLongStep_PrimalDual_eq_4_9
import Theorems.Thm_SelfScaledLongStep_PrimalDual_dual_isSelfScaledBarrier
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SSB82Aux

variable {n : ℕ}

lemma grad_diff (F : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (h : ContDiffAt ℝ 3 F w) :
    DifferentiableAt ℝ (gradient F) w := by
  have e : gradient F = fun y => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ F y) := rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ F) w := by
    have := h.fderiv_right (m := 2) (by norm_num)
    exact this.differentiableAt (by norm_num)
  rw [e]
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun f => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp
      cont := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous }
  exact L.differentiableAt.comp w hd

lemma hess_apply_eq (F : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (h : ContDiffAt ℝ 3 F w)
    (u v : EuclideanSpace ℝ (Fin n)) : ⟪hess F w u, v⟫_ℝ = fderiv ℝ (fderiv ℝ F) w u v := by
  have hg : HasFDerivAt (gradient F) (hess F w) w := (grad_diff F w h).hasFDerivAt
  have hd : DifferentiableAt ℝ (fderiv ℝ F) w := by
    have := h.fderiv_right (m := 2) (by norm_num)
    exact this.differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y => innerSL ℝ v (gradient F y)) ((innerSL ℝ v).comp (hess F w)) w :=
    (innerSL ℝ v).hasFDerivAt.comp w hg
  have h2 : HasFDerivAt (fun y => (ContinuousLinearMap.apply ℝ ℝ v) (fderiv ℝ F y))
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ F) w)) w :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp w hd.hasFDerivAt
  have hfun : (fun y => innerSL ℝ v (gradient F y)) = (fun y => (ContinuousLinearMap.apply ℝ ℝ v) (fderiv ℝ F y)) := by
    funext y; simp [innerSL_apply_apply]
  rw [hfun] at h1
  have := congrArg (fun L => L u) (h1.unique h2)
  simpa [innerSL_apply_apply, real_inner_comm] using this

lemma hess_symm' (F : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (h : ContDiffAt ℝ 3 F w)
    (a b : EuclideanSpace ℝ (Fin n)) : ⟪hess F w a, b⟫_ℝ = ⟪a, hess F w b⟫_ℝ := by
  have hsymm : IsSymmSndFDerivAt ℝ F w := h.isSymmSndFDerivAt (by simp; norm_num)
  rw [hess_apply_eq F w h, real_inner_comm, hess_apply_eq F w h]
  exact hsymm a b

/-- Hessian symmetry at an interior point. -/
lemma hess_symm (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF3 : ContDiffOn ℝ 3 F (interior K)) (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K)
    (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F w a, b⟫_ℝ = ⟪a, hess F w b⟫_ℝ :=
  hess_symm' F w (hF3.contDiffAt (isOpen_interior.mem_nhds hw)) a b

/-- Euler identity `⟨F'(x), x⟩ = -ν`. -/
lemma euler (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (hF : IsLogHomBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    ⟪gradient F x, x⟫_ℝ = -ν := by
  have hF3 : ContDiffOn ℝ 3 F (interior K) := hF.1.2.1
  have hd : DifferentiableAt ℝ F x :=
    (hF3.contDiffAt (isOpen_interior.mem_nhds hx)).differentiableAt (by norm_num)
  have h1 : HasDerivAt (fun τ : ℝ => F (τ • x)) (fderiv ℝ F x x) 1 := by
    have hl : HasDerivAt (fun τ : ℝ => τ • x) x 1 := by
      simpa using (hasDerivAt_id (1:ℝ)).smul_const x
    have hd' : HasFDerivAt F (fderiv ℝ F x) ((1:ℝ) • x) := by simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt 1 hl
  have h2 : HasDerivAt (fun τ : ℝ => F x - ν * Real.log τ) (-ν) 1 := by
    have := ((Real.hasDerivAt_log (by norm_num : (1:ℝ) ≠ 0)).const_mul ν).const_sub (F x)
    simpa using this
  have heq : (fun τ : ℝ => F (τ • x)) =ᶠ[nhds 1] (fun τ : ℝ => F x - ν * Real.log τ) := by
    filter_upwards [lt_mem_nhds (by norm_num : (0:ℝ) < 1)] with τ hτ
    exact hF.2.2.2.1 x hx τ hτ
  have := (h1.congr_of_eventuallyEq heq.symm).unique h2
  have hg : ⟪gradient F x, x⟫_ℝ = fderiv ℝ F x x := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [hg]
  have h1' := h1
  exact (h1'.unique (h2.congr_of_eventuallyEq heq))

/-- Interior points of `K` are nonzero (logarithmic homogeneity with `ν > 0`). -/
lemma ne_zero_of_mem (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (hν : 1 ≤ ν) (hF : IsLogHomBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    x ≠ 0 := by
  rintro rfl
  have h := hF.2.2.2.1 0 hx 2 (by norm_num)
  simp only [smul_zero] at h
  have : ν * Real.log 2 = 0 := by linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

lemma hess_nonneg (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (hF : IsLogHomBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (h : EuclideanSpace ℝ (Fin n)) : 0 ≤ ⟪hess F x h, h⟫_ℝ := by
  by_cases h0 : h = 0
  · simp [h0]
  · exact (hF.2.2.2.2 x hx h h0).le

lemma lnorm_sq (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (hF : IsLogHomBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (h : EuclideanSpace ℝ (Fin n)) : (lnorm F x h) ^ 2 = ⟪hess F x h, h⟫_ℝ := by
  unfold lnorm
  exact Real.sq_sqrt (hess_nonneg K F ν hF x hx h)

/-- Pairing of interior points of `K*` and `K` is positive. -/
lemma pairing_pos (K : Set (EuclideanSpace ℝ (Fin n))) (x s : EuclideanSpace ℝ (Fin n))
    (hx0 : x ≠ 0) (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hxK : x ∈ K) :
    0 < ⟪s, x⟫_ℝ := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hball⟩ := hs
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set c : ℝ := ε / (2 * ‖x‖) with hc
  have hcpos : 0 < c := by positivity
  have hmem : s - c • x ∈ Metric.ball s ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hc]; field_simp; linarith
  have h := hball hmem x hxK
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have : 0 < c * ‖x‖ ^ 2 := by positivity
  rw [real_inner_comm]; linarith

lemma sigma_nonneg (C : Set (EuclideanSpace ℝ (Fin n))) (c u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sigma C c u := Real.sInf_nonneg (fun _ h => h.1)

/-- If `σ_x(p) = 0` for `x ∈ int C`, `C` a closed cone, then `-p ∈ C`. -/
lemma neg_mem_of_sigma_zero (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsClosed C)
    (hcone : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior C) (h0 : sigma C x p = 0) : -p ∈ C := by
  set S : Set ℝ := {β : ℝ | 0 ≤ β ∧ β • x - p ∈ C} with hS
  have hne : S.Nonempty := by
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
    obtain ⟨ε, hε, hball⟩ := hx
    set β : ℝ := 2 * ‖p‖ / ε + 1 with hβ
    have hβpos : 0 < β := by positivity
    refine ⟨β, hβpos.le, ?_⟩
    have hm : x - β⁻¹ • p ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hβpos]
      rw [inv_mul_lt_iff₀ hβpos, hβ]
      have : 0 ≤ ‖p‖ := norm_nonneg p
      rw [add_mul, div_mul_cancel₀ _ hε.ne']; nlinarith
    have := hcone _ (hball hm) β hβpos.le
    rwa [smul_sub, smul_smul, mul_inv_cancel₀ hβpos.ne', one_smul] at this
  have hcl : IsClosed S := by
    have : S = Set.Ici 0 ∩ (fun β : ℝ => β • x - p) ⁻¹' C := by
      ext β; simp [hS]
    rw [this]
    exact isClosed_Ici.inter (hC.preimage (by fun_prop))
  have hbdd : BddBelow S := ⟨0, fun _ h => h.1⟩
  have hmem := hcl.csInf_mem hne hbdd
  have : sInf S = 0 := h0
  rw [this] at hmem
  simpa using hmem.2


/-- The function `(−τ − ln(1 − τ))/τ²` (`1/2` at `τ = 0`) of Proposition 4.1 (iii). -/
noncomputable def hfun (τ : ℝ) : ℝ := if τ = 0 then 1 / 2 else (-τ - Real.log (1 - τ)) / τ ^ 2

lemma hfun_mono : MonotoneOn hfun (Set.Iio 1) :=
  SelfScaledLongStep.PrimalDual.proposition_4_1.2.2.monotoneOn

lemma hfun_nonneg (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ < 1) : 0 ≤ hfun τ := by
  have := hfun_mono (show (0:ℝ) ∈ Set.Iio 1 by norm_num) (show τ ∈ Set.Iio 1 from h1) h0
  have h : hfun 0 = 1 / 2 := by simp [hfun]
  linarith

/-- (4.8) of Theorem 4.2 in the form valid also when `σ_x(p) = 0` (then via (4.9)). -/
lemma gen42 (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : α * sigma K x p < 1) :
    F (x - α • p) ≤ F x - α * ⟪gradient F x, p⟫_ℝ +
      α ^ 2 * ⟪hess F x p, p⟫_ℝ * hfun (α * sigma K x p) := by
  rcases (sigma_nonneg K x p).eq_or_lt with h0 | hpos
  · have hmem : -p ∈ K := neg_mem_of_sigma_zero K hK.1 hK.2.2.1 x p hx h0.symm
    have h := SelfScaledLongStep.PrimalDual.eq_4_9 K hK F ν hν hF x (-p) hx hmem α hα0
    rw [lnorm_sq K F ν hF.1 x hx] at h
    rw [← h0, mul_zero]
    have hh : hfun 0 = 1 / 2 := by simp [hfun]
    rw [hh]
    have e1 : x + α • -p = x - α • p := by rw [smul_neg, ← sub_eq_add_neg]
    rw [e1] at h
    simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg] at h
    linarith
  · rcases hα0.eq_or_lt with h0 | hαpos
    · subst h0; simp
    · have h := SelfScaledLongStep.PrimalDual.theorem_4_2 K hK F ν hν hF x p hx hpos α hα0 hα
      rw [lnorm_sq K F ν hF.1 x hx] at h
      have hne : α * sigma K x p ≠ 0 := by positivity
      have hh : hfun (α * sigma K x p) =
          (-(α * sigma K x p) - Real.log (1 - α * sigma K x p)) / (α * sigma K x p) ^ 2 := by
        simp [hfun, hne]
      rw [hh]
      have e : ⟪hess F x p, p⟫_ℝ / sigma K x p ^ 2 *
            (-(α * sigma K x p) - Real.log (1 - α * sigma K x p)) =
          α ^ 2 * ⟪hess F x p, p⟫_ℝ *
            ((-(α * sigma K x p) - Real.log (1 - α * sigma K x p)) / (α * sigma K x p) ^ 2) := by
        field_simp
      linarith

/-- The scalar part of the proof of Theorem 8.2. -/
lemma final_real (σ σb M : ℝ) (hσ : 0 < σ) (hσb : 0 ≤ σb) (hM : 0 ≤ M)
    (hb : σb ≤ σ * Real.sqrt M) (h34 : 3 / 4 * σ ^ 2 ≤ M) :
    -(1 / (σ ^ 2 + σb)) * M + (1 / (σ ^ 2 + σb)) ^ 2 * σ ^ 2 * M * hfun (1 / (σ ^ 2 + σb) * σb)
      ≤ -(Real.sqrt 3 / 2) + Real.log (1 + Real.sqrt 3 / 2) := by
  obtain ⟨P1, P2, -⟩ := SelfScaledLongStep.PrimalDual.proposition_4_1
  set r := Real.sqrt M / σ with hrdef
  have hsq3 : Real.sqrt (3 / 4 * σ ^ 2) = Real.sqrt 3 / 2 * σ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hσ.le, Real.sqrt_div (by norm_num)]
    have : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
  have hr : Real.sqrt 3 / 2 ≤ r := by
    rw [hrdef, le_div_iff₀ hσ, ← hsq3]
    exact Real.sqrt_le_sqrt h34
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hMr : M = r ^ 2 * σ ^ 2 := by
    rw [hrdef, div_pow, Real.sq_sqrt hM]; field_simp
  set k : ℝ → ℝ := fun τ => if τ = 0 then 1 / 2 else (τ - Real.log (1 + τ)) / τ ^ 2 with hk
  have hkr : k r = (r - Real.log (1 + r)) / r ^ 2 := by simp [hk, hr0.ne']
  set τ := σb / σ ^ 2 with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hτr : τ ≤ r := by
    rw [hτdef, hrdef, div_le_div_iff₀ (by positivity) hσ]
    nlinarith
  have hkτ : k r ≤ k τ :=
    P2.antitoneOn (show τ ∈ Set.Ioi (-1) by simp only [Set.mem_Ioi]; linarith)
      (show r ∈ Set.Ioi (-1) by simp only [Set.mem_Ioi]; linarith) hτr
  have hLHS : -(1 / (σ ^ 2 + σb)) * M + (1 / (σ ^ 2 + σb)) ^ 2 * σ ^ 2 * M *
      hfun (1 / (σ ^ 2 + σb) * σb) = -(r ^ 2 * k τ) := by
    rcases hσb.eq_or_lt with h0 | hpos
    · subst h0
      have e1 : τ = 0 := by simp [hτdef]
      rw [e1]
      have ea : hfun (1 / (σ ^ 2 + 0) * 0) = 1 / 2 := by simp [hfun]
      have eb : k 0 = 1 / 2 := by simp [hk]
      rw [ea, eb, hMr]; field_simp; ring
    · have hτpos : 0 < τ := by positivity
      have hq : 1 / (σ ^ 2 + σb) * σb ≠ 0 := by positivity
      have hlog : Real.log (1 - 1 / (σ ^ 2 + σb) * σb) = -Real.log (1 + τ) := by
        have : 1 - 1 / (σ ^ 2 + σb) * σb = (1 + τ)⁻¹ := by
          rw [hτdef]; field_simp; ring
        rw [this, Real.log_inv]
      simp only [hfun, hq, if_false, hk, hτpos.ne', hlog]
      rw [hMr]
      have hτ' : σb = τ * σ ^ 2 := by rw [hτdef]; field_simp
      rw [hτ']
      field_simp
      ring
  rw [hLHS]
  have h1 : -(r ^ 2 * k τ) ≤ -(r - Real.log (1 + r)) := by
    have : r ^ 2 * k r = r - Real.log (1 + r) := by rw [hkr]; field_simp
    nlinarith [sq_nonneg r]
  have h2 : Real.sqrt 3 / 2 - Real.log (1 + Real.sqrt 3 / 2) ≤ r - Real.log (1 + r) :=
    P1.monotoneOn (show Real.sqrt 3 / 2 ∈ Set.Ici 0 by simp only [Set.mem_Ici]; positivity)
      (show r ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith) hr
  linarith

end SSB82Aux

set_option maxHeartbeats 1000000 in
open SSB82Aux in
theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hx : IsPrimalStrict K A b x) (hys : IsDualStrict K A c y s)
    (ρ : ℝ) (hρ : Real.sqrt ν ≤ ρ)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w)
    (dx : EuclideanSpace ℝ (Fin n)) (dy : EuclideanSpace ℝ (Fin m)) (ds : EuclideanSpace ℝ (Fin n))
    (hdir : SelfScaledLongStep.PrimalDual.IsJointScalingDir F A ν ρ x s w dx dy ds) :
    (x - SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds • dx ∈ interior K ∧
      s - SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds • ds ∈ interior (ConvexOptimization.dualCone K) ∧
      SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ (x - SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds • dx) (s - SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds • ds) ≤
        SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ x s - Real.sqrt 3 / 2 + Real.log (1 + Real.sqrt 3 / 2)) ∧
    ∀ α : ℝ, x - α • dx ∈ interior K → s - α • ds ∈ interior (ConvexOptimization.dualCone K) →
      SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ (x - α • dx) (s - α • ds) ≤
        SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ (x - SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds • dx)
          (s - SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds • ds) →
      IsPrimalStrict K A b (x - α • dx) ∧ IsDualStrict K A c (y - α • dy) (s - α • ds) ∧
        SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ (x - α • dx) (s - α • ds) ≤
          SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ x s - Real.sqrt 3 / 2 + Real.log (1 + Real.sqrt 3 / 2) := by
  classical
  obtain ⟨hK', hG⟩ := SelfScaledLongStep.PrimalDual.dual_isSelfScaledBarrier K hK F ν hν hF
  obtain ⟨hxK, hAx⟩ := hx
  obtain ⟨hsK, hys⟩ := hys
  obtain ⟨hwK, hHx⟩ := hw
  obtain ⟨h1, h2, h3⟩ := hdir
  set K' := ConvexOptimization.dualCone K with hK'def
  set G := conj K F with hGdef
  set H := hess F w with hHdef
  have hFlh := hF.1
  have hGlh := hG.1
  have hsym : ∀ a b, ⟪H a, b⟫_ℝ = ⟪a, H b⟫_ℝ := hess_symm K F hFlh.1.2.1 w hwK
  have hHpd : ∀ v, v ≠ 0 → 0 < ⟪H v, v⟫_ℝ := hFlh.2.2.2.2 w hwK
  have hHinj : Function.Injective H := by
    intro u v huv
    by_contra hne
    have h0 : H (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have := hHpd (u - v) (sub_ne_zero.mpr hne)
    rw [h0, inner_zero_left] at this
    exact lt_irrefl _ this
  have hHsurj : Function.Surjective H :=
    (LinearMap.injective_iff_surjective (f := (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _))).mp hHinj
  have hker : (H : EuclideanSpace ℝ (Fin n) →L[ℝ] _).ker = ⊥ := LinearMap.ker_eq_bot.mpr hHinj
  have hran : (H : EuclideanSpace ℝ (Fin n) →L[ℝ] _).range = ⊤ := LinearMap.range_eq_top.mpr hHsurj
  set e := ContinuousLinearEquiv.ofBijective H hker hran with he
  have hHe : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] _) = H := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hinvR : ∀ v, H (H.inverse v) = v := by
    intro v; rw [← hHe, ContinuousLinearMap.inverse_equiv]; simp
  have hinvL : ∀ v, H.inverse (H v) = v := by
    intro v; rw [← hHe, ContinuousLinearMap.inverse_equiv]; simp
  -- basic scalar facts
  have hx0 : x ≠ 0 := ne_zero_of_mem K F ν hν hFlh x hxK
  set γ := ⟪s, x⟫_ℝ with hγdef
  have hγ : 0 < γ := pairing_pos K x s hx0 hsK (interior_subset hxK)
  have heuF : ⟪gradient F x, x⟫_ℝ = -ν := euler K F ν hFlh x hxK
  have heuG : ⟪gradient G s, s⟫_ℝ = -ν := euler K' G ν hGlh s hsK
  have h32 := (SelfScaledLongStep.PrimalDual.theorem_3_2 K hK F ν hν hF x s hxK hsK).2 w ⟨hwK, hHx⟩
  have hgF : gradient F x = H (gradient G s) := h32.1
  have hds_eq : ds = -(ContinuousLinearMap.adjoint A dy) := eq_neg_of_add_eq_zero_right h3
  have hdsdx : ⟪ds, dx⟫_ℝ = 0 := by
    rw [hds_eq, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, h2, inner_zero_right,
      neg_zero]
  set cc := (ν + ρ) / γ with hcc
  set z := H.inverse ds with hzdef
  have hHz : H z = ds := hinvR ds
  set g := ⟪gradient F x, gradient G s⟫_ℝ with hgdef
  set a := ⟪H dx, dx⟫_ℝ with hadef
  set bb := ⟪H z, z⟫_ℝ with hbdef
  have ha : 0 ≤ a := hess_nonneg K F ν hFlh w hwK dx
  have hb : 0 ≤ bb := hess_nonneg K F ν hFlh w hwK z
  have hu : H dx + ds = cc • s + gradient F x := h1
  have hv : dx + z = cc • x + gradient G s := by
    apply hHinj
    rw [map_add, hHz, hu, map_add, map_smul, hHx, ← hgF]
  set M := a + bb with hMdef
  have hM0 : 0 ≤ M := add_nonneg ha hb
  have hMg : M = g + (ρ ^ 2 - ν ^ 2) / γ := by
    have e1 : ⟪H (dx + z), dx + z⟫_ℝ = a + bb := by
      have c1 : ⟪H dx, z⟫_ℝ = 0 := by rw [hsym, hHz, real_inner_comm, hdsdx]
      have c2 : ⟪H z, dx⟫_ℝ = 0 := by rw [hHz, hdsdx]
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, c1, c2]; ring
    have e2 : ⟪H (dx + z), dx + z⟫_ℝ = ⟪cc • s + gradient F x, cc • x + gradient G s⟫_ℝ := by
      rw [map_add, hHz, hu, hv]
    rw [e1] at e2
    rw [hMdef, e2]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [heuF, real_inner_comm (gradient G s) s, heuG, ← hγdef, ← hgdef, hcc]
    field_simp
    ring
  have hΔ0 : ρ * (ν + ρ) / γ + ⟪gradient F x, dx⟫_ℝ + ⟪gradient G s, ds⟫_ℝ = M := by
    have hds' : ds = cc • s + gradient F x - H dx := by rw [← hu]; abel
    have : ⟪gradient G s, ds⟫_ℝ = cc * (-ν) + g - ⟪gradient F x, dx⟫_ℝ := by
      rw [hds', inner_sub_right, inner_add_right, inner_smul_right,
        heuG, real_inner_comm (gradient F x), ← hgdef, ← hsym, ← hgF]
    rw [this, hMg, hcc]
    field_simp
    ring
  have hgap : ∀ α : ℝ, ⟪s - α • ds, x - α • dx⟫_ℝ = γ - α * ρ := by
    intro α
    have hdsx : ⟪ds, x⟫_ℝ = ρ - ⟪s, dx⟫_ℝ := by
      have hds' : ds = cc • s + gradient F x - H dx := by rw [← hu]; abel
      rw [hds', inner_sub_left, inner_add_left, inner_smul_left, heuF, hsym, hHx,
        RCLike.conj_to_real, ← hγdef, ← real_inner_comm dx s, hcc]
      field_simp
      ring
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [hdsx, hdsdx, ← hγdef]
    ring
  -- σ facts
  set σ := sigma K x w with hσdef
  set t := H w with htdef
  have ht : t ∈ interior K' := (hF.2 w hwK w hwK).1
  have h31 := SelfScaledLongStep.PrimalDual.theorem_3_1 K hK F ν hν hF
  have hKimg : K' = H '' K := h31.2.2 w hwK
  have hσ' : sigma K' s t = σ := by
    unfold sigma
    congr 1
    ext β
    simp only [Set.mem_ofPred_eq]
    have : β • s - t = H (β • x - w) := by rw [map_sub, map_smul, hHx]
    rw [this, hKimg, hHinj.mem_set_image]
  have hGt : ∀ u, ⟪hess G t u, u⟫_ℝ = ⟪H.inverse u, u⟫_ℝ := by
    intro u
    rw [htdef, (h31.1 w hwK w hwK).2]
    show ⟪H.inverse (H (H.inverse u)), u⟫_ℝ = _
    rw [hinvL]
  have hc41 := SelfScaledLongStep.PrimalDual.corollary_4_1 K hK F ν hν hF
  have hc41G := SelfScaledLongStep.PrimalDual.corollary_4_1 K' hK' G ν hν hG
  have hxdx : ⟪hess F x dx, dx⟫_ℝ ≤ σ ^ 2 * a := hc41.2 x hxK w hwK dx
  have hsds : ⟪hess G s ds, ds⟫_ℝ ≤ σ ^ 2 * bb := by
    have := hc41G.2 s hsK t ht ds
    have hGds : ⟪hess G t ds, ds⟫_ℝ = bb := by
      rw [hGt]
      show ⟪z, ds⟫_ℝ = ⟪H z, z⟫_ℝ
      rw [hHz, real_inner_comm]
    rw [hσ', hGds] at this
    exact this
  have hσ0 : 0 ≤ σ := sigma_nonneg K x w
  have hσpos : 0 < σ := by
    rcases hσ0.eq_or_lt with h0 | h0
    · exfalso
      have h1' := hc41.2 x hxK w hwK x
      have h2' := hFlh.2.2.2.2 x hxK x hx0
      rw [← hσdef, ← h0] at h1'
      simp at h1'
      linarith
    · exact h0
  have hM34 : 3 / 4 * σ ^ 2 ≤ M := by
    have h52 := SelfScaledLongStep.PrimalDual.theorem_5_2 K hK F ν hν hF x s w hxK hsK ⟨hwK, hHx⟩
    have hρ2 : ν ≤ ρ ^ 2 := by
      have hs0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
      have : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt (by linarith)
      nlinarith
    have : (ν - ν ^ 2) / γ ≤ (ρ ^ 2 - ν ^ 2) / γ :=
      div_le_div_of_nonneg_right (by linarith) hγ.le
    have e : ν * (ν - 1) / γ = -((ν - ν ^ 2) / γ) := by ring
    rw [hMg]
    rw [e] at h52
    linarith
  set μ := Real.sqrt M with hμdef
  have hsqσ : Real.sqrt (σ ^ 2 * M) = σ * μ := by
    rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ0]
  have hP35 := SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF
  have hσdx : sigma K x dx ≤ σ * μ := by
    have h1' : sigma K x dx ≤ absn K x dx := le_max_left _ _
    have h2' := (hP35.1 x hxK dx).1
    have h3' : lnorm F x dx ≤ σ * μ := by
      rw [← hsqσ]; unfold lnorm
      exact Real.sqrt_le_sqrt (le_trans hxdx
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb) (sq_nonneg σ)))
    linarith
  have hσds : sigma K' s ds ≤ σ * μ := by
    have h1' : sigma K' s ds ≤ absn K' s ds := le_max_left _ _
    have h2' := (hP35.2.2.1 s hsK ds).1
    have h3' : lnorm G s ds ≤ σ * μ := by
      rw [← hsqσ]; unfold lnorm
      exact Real.sqrt_le_sqrt (le_trans hsds
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha) (sq_nonneg σ)))
    linarith
  set σb := SelfScaledLongStep.PrimalDual.sigmaBar K x s dx ds with hσbdef
  have hσb_eq : σb = max (sigma K x dx) (sigma K' s ds) := rfl
  have hσb0 : 0 ≤ σb := le_trans (sigma_nonneg K x dx) (by rw [hσb_eq]; exact le_max_left _ _)
  have hσbμ : σb ≤ σ * μ := by rw [hσb_eq]; exact max_le hσdx hσds
  set αb := SelfScaledLongStep.PrimalDual.alphaBar K x s w dx ds with hαbdef
  have hαb_eq : αb = 1 / (σ ^ 2 + σb) := rfl
  have hden : 0 < σ ^ 2 + σb := by positivity
  have hαbpos : 0 < αb := by rw [hαb_eq]; positivity
  have hαbσb : αb * σb < 1 := by
    rw [hαb_eq, div_mul_eq_mul_div, one_mul, div_lt_one hden]; nlinarith
  have hαdx : αb * sigma K x dx < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by rw [hσb_eq]; exact le_max_left _ _) hαbpos.le)
      hαbσb
  have hαds : αb * sigma K' s ds < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by rw [hσb_eq]; exact le_max_right _ _) hαbpos.le)
      hαbσb
  have hint1 := (SelfScaledLongStep.PrimalDual.theorem_4_1 K hK F ν hν hF x dx hxK αb
    hαbpos.le hαdx).1
  have hint2 := (SelfScaledLongStep.PrimalDual.theorem_4_1 K' hK' G ν hν hG s ds hsK αb
    hαbpos.le hαds).1
  have hbound : SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ (x - αb • dx) (s - αb • ds) ≤
      SelfScaledLongStep.PrimalDual.pdPotential K F ν ρ x s - Real.sqrt 3 / 2 +
        Real.log (1 + Real.sqrt 3 / 2) := by
    unfold SelfScaledLongStep.PrimalDual.pdPotential
    rw [hgap αb, ← hγdef]
    have hpos' : 0 < γ - αb * ρ := by
      rw [← hgap αb]
      exact pairing_pos K _ _ (ne_zero_of_mem K F ν hν hFlh _ hint1) hint2 (interior_subset hint1)
    have hlog : Real.log (γ - αb * ρ) ≤ Real.log γ - αb * ρ / γ := by
      have := Real.log_le_sub_one_of_pos (div_pos hpos' hγ)
      rw [Real.log_div hpos'.ne' hγ.ne'] at this
      have e : (γ - αb * ρ) / γ - 1 = -(αb * ρ / γ) := by field_simp; ring
      linarith
    have hνρ : 0 < ν + ρ := by
      have : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
      linarith
    have hFb := gen42 K hK F ν hν hF x dx hxK αb hαbpos.le hαdx
    have hGb := gen42 K' hK' G ν hν hG s ds hsK αb hαbpos.le hαds
    have hm1 : hfun (αb * sigma K x dx) ≤ hfun (αb * σb) :=
      hfun_mono (show αb * sigma K x dx ∈ Set.Iio 1 from hαdx) (show αb * σb ∈ Set.Iio 1 from hαbσb)
        (mul_le_mul_of_nonneg_left (by rw [hσb_eq]; exact le_max_left _ _) hαbpos.le)
    have hm2 : hfun (αb * sigma K' s ds) ≤ hfun (αb * σb) :=
      hfun_mono (show αb * sigma K' s ds ∈ Set.Iio 1 from hαds) (show αb * σb ∈ Set.Iio 1 from hαbσb)
        (mul_le_mul_of_nonneg_left (by rw [hσb_eq]; exact le_max_right _ _) hαbpos.le)
    have hn1 : 0 ≤ hfun (αb * sigma K x dx) :=
      hfun_nonneg _ (mul_nonneg hαbpos.le (sigma_nonneg _ _ _)) hαdx
    have hn2 : 0 ≤ hfun (αb * sigma K' s ds) :=
      hfun_nonneg _ (mul_nonneg hαbpos.le (sigma_nonneg _ _ _)) hαds
    have hnb : 0 ≤ hfun (αb * σb) := le_trans hn1 hm1
    have hq1 : ⟪hess F x dx, dx⟫_ℝ * hfun (αb * sigma K x dx) ≤ σ ^ 2 * a * hfun (αb * σb) :=
      mul_le_mul hxdx hm1 hn1 (by positivity)
    have hq2 : ⟪hess G s ds, ds⟫_ℝ * hfun (αb * sigma K' s ds) ≤ σ ^ 2 * bb * hfun (αb * σb) :=
      mul_le_mul hsds hm2 hn2 (by positivity)
    have hR := final_real σ σb M hσpos hσb0 hM0 hσbμ hM34
    rw [← hαb_eq] at hR
    have hα2 : 0 ≤ αb ^ 2 := sq_nonneg αb
    have hq1' := mul_le_mul_of_nonneg_left hq1 hα2
    have hq2' := mul_le_mul_of_nonneg_left hq2 hα2
    have hlog' := mul_le_mul_of_nonneg_left hlog hνρ.le
    have eΔ : (ν + ρ) * (Real.log γ - αb * ρ / γ) =
        (ν + ρ) * Real.log γ - αb * (ρ * (ν + ρ) / γ) := by ring
    have eM : αb ^ 2 * (σ ^ 2 * a * hfun (αb * σb)) + αb ^ 2 * (σ ^ 2 * bb * hfun (αb * σb)) =
        αb ^ 2 * σ ^ 2 * M * hfun (αb * σb) := by rw [hMdef]; ring
    have eΔ0 : αb * (ρ * (ν + ρ) / γ) + αb * ⟪gradient F x, dx⟫_ℝ + αb * ⟪gradient G s, ds⟫_ℝ
        = αb * M := by rw [← hΔ0]; ring
    nlinarith [hFb, hGb, hq1', hq2', hlog', eΔ, eM, eΔ0, hR]
  refine ⟨⟨hint1, hint2, hbound⟩, ?_⟩
  intro α hα1 hα2 hle
  refine ⟨⟨hα1, ?_⟩, ⟨hα2, ?_⟩, le_trans hle hbound⟩
  · rw [map_sub, map_smul, hAx, h2, smul_zero, sub_zero]
  · rw [map_sub, map_smul]
    have : ContinuousLinearMap.adjoint A y - α • ContinuousLinearMap.adjoint A dy + (s - α • ds)
        = (ContinuousLinearMap.adjoint A y + s) - α • (ContinuousLinearMap.adjoint A dy + ds) := by
      rw [smul_add]; abel
    rw [this, hys, h3, smul_zero, sub_zero]
