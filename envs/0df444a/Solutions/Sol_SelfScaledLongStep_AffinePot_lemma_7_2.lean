-- Prove2me | solution 1 for SelfScaledLongStep.AffinePot.lemma_7_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:05:31.27875+00:00
-- url     : https://prove2.me/submissions/0df8246b-7673-4a44-9ceb-6a05a39634cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_AffinePot_Defs
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep
open SelfScaledLongStep.AffinePot
open Filter Topology
open scoped Pointwise

namespace AffPotLemma72Aux

variable {n : ℕ}

lemma inner_gradient (F : EuclideanSpace ℝ (Fin n) → ℝ) (y v : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient F y, v⟫_ℝ = fderiv ℝ F y v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

lemma smul_mem_interior (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (τ : ℝ) (hτ : 0 < τ) :
    τ • x ∈ interior K := by
  have hsub : τ • interior K ⊆ interior K :=
    interior_maximal (by rintro _ ⟨y, hy, rfl⟩; exact hK.2.2.1 y (interior_subset hy) τ hτ.le)
      (isOpen_interior.smul₀ hτ.ne')
  exact hsub (Set.smul_mem_smul_set hx)

lemma diffAt (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ interior K) :
    ContDiffAt ℝ 3 F y :=
  hF.1.1.2.1.contDiffAt (isOpen_interior.mem_nhds hy)

lemma hasFDerivAt_F (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ interior K) : HasFDerivAt F (fderiv ℝ F y) y :=
  ((diffAt K F ν hF y hy).differentiableAt (by norm_num)).hasFDerivAt

lemma hasFDerivAt_grad (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ interior K) : HasFDerivAt (gradient F) (hess F y) y := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ F) y := (diffAt K F ν hF y hy).fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) y := h1.differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (gradient F) y := by
    have e : gradient F = fun z => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ F z) := rfl
    rw [e]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.differentiableAt.comp
      y h2
  exact h3.hasFDerivAt

/-- `⟨F'(y), y⟩ = −ν` on `int K` (differentiate (2.6) in `τ` at `τ = 1`). -/
lemma inner_grad_self (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ interior K) : ⟪gradient F y, y⟫_ℝ = -ν := by
  have hhom := hF.1.2.2.2.1 y hy
  have hL : HasDerivAt (fun τ : ℝ => F (τ • y)) (fderiv ℝ F y ((1 : ℝ) • y)) 1 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) (hasFDerivAt_F K F ν hF y hy)
      ((hasDerivAt_id (1 : ℝ)).smul_const y) (by simp)
  have hR : HasDerivAt (fun τ : ℝ => F y - ν * Real.log τ) (-(ν * (1 : ℝ)⁻¹)) 1 :=
    ((Real.hasDerivAt_log one_ne_zero).const_mul ν).const_sub (F y)
  have hev : (fun τ : ℝ => F (τ • y)) =ᶠ[𝓝 1] (fun τ : ℝ => F y - ν * Real.log τ) :=
    (lt_mem_nhds one_pos).mono fun τ hτ => hhom τ hτ
  have := (hL.congr_of_eventuallyEq hev.symm).unique hR
  rw [inner_gradient, ← one_smul ℝ y]
  rw [one_smul] at this ⊢
  simpa using this

/-- `F'(τx) = τ⁻¹ F'(x)`. -/
lemma grad_smul (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (τ : ℝ) (hτ : 0 < τ) :
    gradient F (τ • x) = τ⁻¹ • gradient F x := by
  have hτx := smul_mem_interior K hK x hx τ hτ
  have hL : HasFDerivAt (fun y => F (τ • y))
      ((fderiv ℝ F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ _)) x :=
    (hasFDerivAt_F K F ν hF _ hτx).comp x ((hasFDerivAt_id x).const_smul τ)
  have hR : HasFDerivAt (fun y => F y - ν * Real.log τ) (fderiv ℝ F x) x :=
    (hasFDerivAt_F K F ν hF x hx).sub_const _
  have hev : (fun y => F (τ • y)) =ᶠ[𝓝 x] (fun y => F y - ν * Real.log τ) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hx) fun y hy => hF.1.2.2.2.1 y hy τ hτ
  have heq := (hL.congr_of_eventuallyEq hev.symm).unique hR
  apply ext_inner_right ℝ
  intro v
  rw [real_inner_smul_left, inner_gradient, inner_gradient, ← heq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  field_simp

/-- `F''(x)x = −F'(x)`. -/
lemma hess_self (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    hess F x x = -gradient F x := by
  have hL : HasDerivAt (fun τ : ℝ => gradient F (τ • x)) (hess F x ((1 : ℝ) • x)) 1 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) (hasFDerivAt_grad K F ν hF x hx)
      ((hasDerivAt_id (1 : ℝ)).smul_const x) (by simp)
  have hR : HasDerivAt (fun τ : ℝ => τ⁻¹ • gradient F x) ((-((1 : ℝ) ^ 2)⁻¹) • gradient F x) 1 :=
    (hasDerivAt_inv one_ne_zero).smul_const _
  have hev : (fun τ : ℝ => gradient F (τ • x)) =ᶠ[𝓝 1] (fun τ : ℝ => τ⁻¹ • gradient F x) :=
    (lt_mem_nhds one_pos).mono fun τ hτ => grad_smul K hK F ν hF x hx τ hτ
  have := (hL.congr_of_eventuallyEq hev.symm).unique hR
  simpa using this

/-- `⟨F''(x)p, x⟩ = −⟨F'(x), p⟩` (differentiate `⟨F'(y), y⟩ = −ν`). -/
lemma inner_hess_self (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    ⟪hess F x p, x⟫_ℝ = -⟪gradient F x, p⟫_ℝ := by
  have hline : HasDerivAt (fun t : ℝ => x + t • p) ((1 : ℝ) • p) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add x
  have hg : HasDerivAt (fun t : ℝ => gradient F (x + t • p)) (hess F x ((1 : ℝ) • p)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasFDerivAt_grad K F ν hF x hx) hline (by simp)
  have hφ := hg.inner ℝ hline
  have hc : ContinuousAt (fun t : ℝ => x + t • p) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hmem : (fun t : ℝ => x + t • p) ⁻¹' interior K ∈ 𝓝 (0 : ℝ) :=
    hc.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx)
  have hev : (fun t : ℝ => ⟪gradient F (x + t • p), x + t • p⟫_ℝ) =ᶠ[𝓝 0] (fun _ => -ν) :=
    Filter.mem_of_superset hmem fun t ht => inner_grad_self K F ν hF _ ht
  have h0 := (hφ.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const (0 : ℝ) (-ν))
  simp only [one_smul, zero_smul, add_zero] at h0
  linarith

/-- `F''(x)v ∈ K*` for `x ∈ int K`, `v ∈ K` (closure of (2.18)). -/
lemma hess_mem_dual (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hv : v ∈ K) :
    hess F x v ∈ ConvexOptimization.dualCone K := by
  intro z hz
  by_contra hneg
  push Not at hneg
  set a := ⟪z, hess F x v⟫_ℝ
  set bb := ⟪z, hess F x x⟫_ℝ
  set t : ℝ := (-a) / (2 * (|bb| + (-a))) with ht
  have hden : 0 < 2 * (|bb| + (-a)) := by have := abs_nonneg bb; linarith
  have htpos : 0 < t := div_pos (by linarith) hden
  have htle : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ hden]; have := abs_nonneg bb; nlinarith
  have hw : t • x + (1 - t) • v ∈ interior K :=
    hK.2.1.combo_interior_self_mem_interior hx hv htpos (by linarith) (by ring)
  have hmem := interior_subset (hF.2 x hx _ hw).1 z hz
  rw [map_add, map_smul, map_smul, inner_add_right, real_inner_smul_right,
    real_inner_smul_right] at hmem
  have h1 : t * bb ≤ t * |bb| := mul_le_mul_of_nonneg_left (le_abs_self bb) htpos.le
  have hne0 : |bb| + (-a) ≠ 0 := by have := abs_nonneg bb; linarith
  have h2 : t * (|bb| + (-a)) = -a / 2 := by rw [ht]; field_simp
  nlinarith

lemma sigma_mem (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x u : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    0 ≤ sigma K x u ∧ sigma K x u • x - u ∈ K := by
  obtain ⟨hKc, -, hcone, -, -⟩ := hK
  set S : Set ℝ := {β : ℝ | 0 ≤ β ∧ β • x - u ∈ K} with hS
  have hne : S.Nonempty := by
    have hc : Continuous (fun t : ℝ => x - t • u) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have ho : IsOpen ((fun t : ℝ => x - t • u) ⁻¹' interior K) := isOpen_interior.preimage hc
    have h0 : (0 : ℝ) ∈ (fun t : ℝ => x - t • u) ⁻¹' interior K := by simpa using hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ho 0 h0
    have hmem : x - (r / 2) • u ∈ K := by
      refine interior_subset (hball ?_)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith
    have ht : 0 < r / 2 := by positivity
    refine ⟨(r / 2)⁻¹, inv_nonneg.2 ht.le, ?_⟩
    have := hcone _ hmem (r / 2)⁻¹ (inv_nonneg.2 ht.le)
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
  have hcl : IsClosed S := by
    have : S = {β : ℝ | 0 ≤ β} ∩ (fun β : ℝ => β • x - u) ⁻¹' K := by
      ext β; simp [hS]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter
      (hKc.preimage ((continuous_id.smul continuous_const).sub continuous_const))
  exact hcl.csInf_mem hne ⟨0, fun b hb => hb.1⟩

lemma add_mem (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : u ∈ K) (hv : v ∈ K) : u + v ∈ K := by
  have hmid := hK.2.1 hu hv (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have := hK.2.2.1 _ hmid 2 (by norm_num)
  convert this using 1
  rw [smul_add, smul_smul, smul_smul]; norm_num

end AffPotLemma72Aux

open AffPotLemma72Aux

theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ y s, IsDualStrict K A c y s)
    (hnc : ∃ x₁ x₂, (x₁ ∈ K ∧ A x₁ = b) ∧ (x₂ ∈ K ∧ A x₂ = b) ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (μ : ℝ) (hμ : ν < μ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsPrimalStrict K A b xh) (ζh : ℝ) (hζh : ζh ≤ zetaStar K A b c)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F A xh c yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F A xh (gradient F xh) yd pd) :
    let ζp := zetaPlus K F c xh pc pd ζh
    let p := affDir K F μ c xh pc pd ζh
    (ν + Real.sqrt ν ≤ μ → lam μ c xh ζp ≤ lnorm F xh p) ∧
    (2 * ν ≤ μ → lam μ c xh ζp ≤ absn K xh p) := by
  intro ζp p
  have hνpos : 0 < ν := by linarith
  have hμpos : 0 < μ := by linarith
  have hxi := hxh.1
  set l := lam μ c xh ζp with hl
  have hlG : μ * l = ⟪c, xh⟫_ℝ - ζp := by
    rw [hl]; unfold lam; field_simp
  have hpdef : p = pc + l • pd := rfl
  have hHx := hess_self K hK F ν hF xh hxi
  have hgx := inner_grad_self K F ν hF xh hxi
  -- key consequence of `l > σ(−p)`
  have key : sigma K xh (-p) < l → μ * l ≤ l * ν - ⟪gradient F xh, p⟫_ℝ := by
    intro hlt
    have hm := (sigma_mem K hK xh (-p) hxi).2
    rw [sub_neg_eq_add] at hm
    have hv : l • xh + p ∈ K := by
      have h2 := hK.2.2.1 xh (interior_subset hxi) (l - sigma K xh (-p)) (by linarith)
      have := add_mem K hK _ _ hm h2
      convert this using 1
      rw [sub_smul]; abel
    have hsT : sTilde F xh pc pd l = hess F xh (l • xh + p) := by
      unfold sTilde
      rw [hpdef]
      simp only [map_add, map_smul]
      rw [hHx]
      module
    have hdual : sTilde F xh pc pd l ∈ ConvexOptimization.dualCone K := by
      rw [hsT]; exact hess_mem_dual K hK F ν hF xh _ hxi hv
    have hz : ⟪c, xh⟫_ℝ - ⟪sTilde F xh pc pd l, xh⟫_ℝ ∈ dualBounds K F c xh pc pd :=
      ⟨l, hdual, rfl⟩
    have hbdd : BddAbove (dualBounds K F c xh pc pd) := by
      refine ⟨⟪c, xh⟫_ℝ, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have := ht xh (interior_subset hxi)
      rw [real_inner_comm] at this
      linarith
    have hζ : ⟪c, xh⟫_ℝ - ⟪sTilde F xh pc pd l, xh⟫_ℝ ≤ ζp := by
      show _ ≤ zetaPlus K F c xh pc pd ζh
      unfold zetaPlus
      rw [if_pos ⟨_, hz⟩]
      exact le_trans (le_csSup hbdd hz) (le_max_right _ _)
    have hgap : ⟪sTilde F xh pc pd l, xh⟫_ℝ = l * ν - ⟪gradient F xh, p⟫_ℝ := by
      rw [hsT, map_add, map_smul, inner_add_left, real_inner_smul_left, hHx, inner_neg_left, hgx,
        inner_hess_self K F ν hF xh p hxi]
      ring
    linarith
  -- (4.3)-type bound and the norm
  have hposdef := hF.1.2.2.2.2 xh hxi
  have hLnn : 0 ≤ ⟪hess F xh p, p⟫_ℝ := by
    by_cases hp : p = 0
    · rw [hp, map_zero, inner_zero_left]
    · exact (hposdef p hp).le
  have h35 := ((SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).1 xh hxi p).1
  have hsig_abs : sigma K xh (-p) ≤ absn K xh p := le_max_right _ _
  have hsig_abs' : sigma K xh p ≤ absn K xh p := le_max_left _ _
  refine ⟨fun hμ1 => ?_, fun hμ2 => ?_⟩
  · by_contra hcon
    push Not at hcon
    have h43 : -⟪gradient F xh, p⟫_ℝ ≤ Real.sqrt ν * lnorm F xh p := by
      have hpar := hF.1.2.2.1 xh hxi p
      rw [← inner_gradient] at hpar
      have := Real.abs_le_sqrt hpar
      rw [Real.sqrt_mul hνpos.le] at this
      unfold lnorm
      linarith [neg_le_abs ⟪gradient F xh, p⟫_ℝ]
    have hk := key (by linarith)
    have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hνpos
    have := mul_lt_mul_of_pos_left hcon hsq
    have hl0 : 0 ≤ l := le_trans (Real.sqrt_nonneg _) hcon.le
    have := mul_le_mul_of_nonneg_right hμ1 hl0
    nlinarith
  · by_contra hcon
    push Not at hcon
    have h44 : -⟪gradient F xh, p⟫_ℝ ≤ ν * sigma K xh p := by
      have hm := (sigma_mem K hK xh p hxi).2
      have hd := interior_subset (hF.2 xh hxi xh hxi).1 _ hm
      rw [hHx, inner_neg_right, inner_sub_left, real_inner_smul_left] at hd
      have e1 : ⟪xh, gradient F xh⟫_ℝ = -ν := by rw [real_inner_comm]; exact hgx
      have e2 : ⟪p, gradient F xh⟫_ℝ = ⟪gradient F xh, p⟫_ℝ := real_inner_comm _ _
      rw [e1, e2] at hd
      linarith
    have hk := key (by linarith)
    have hs0 : 0 ≤ sigma K xh p := Real.sInf_nonneg (fun b hb => hb.1)
    have hl0 : 0 < l := by linarith
    have := mul_lt_mul_of_pos_left (hsig_abs'.trans_lt hcon) hνpos
    have := mul_le_mul_of_nonneg_right hμ2 hl0.le
    nlinarith
