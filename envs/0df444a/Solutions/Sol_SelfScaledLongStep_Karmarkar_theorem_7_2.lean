-- Prove2me | solution 1 for SelfScaledLongStep.Karmarkar.theorem_7_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:35:26.4418+00:00
-- url     : https://prove2.me/submissions/27fa5103-74c2-4a4b-876d-7bd943f5a188
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_Karmarkar_Defs
import Theorems.Thm_SelfScaledLongStep_Karmarkar_lemma_7_1
import Theorems.Thm_SelfScaledLongStep_Karmarkar_eq_7_8
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_proposition_4_1
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep
open SelfScaledLongStep.Karmarkar

namespace KarmarkarThm72Aux

/-- From an interior point one can move a little in any direction and stay in `K`. -/
lemma exists_pos_sub_smul_mem {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x u : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    ∃ t : ℝ, 0 < t ∧ x - t • u ∈ K := by
  have hc : Continuous (fun t : ℝ => x - t • u) := continuous_const.sub (continuous_id.smul continuous_const)
  have ho : IsOpen ((fun t : ℝ => x - t • u) ⁻¹' interior K) := isOpen_interior.preimage hc
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x - t • u) ⁻¹' interior K := by simpa using hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ho 0 h0
  refine ⟨r / 2, by positivity, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

/-- The infimum defining `σ_x(u)` is attained. -/
lemma sigma_mem {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x u : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    0 ≤ sigma K x u ∧ sigma K x u • x - u ∈ K := by
  obtain ⟨hKc, -, hcone, -, -⟩ := hK
  set S : Set ℝ := {β : ℝ | 0 ≤ β ∧ β • x - u ∈ K} with hS
  have hne : S.Nonempty := by
    obtain ⟨t, ht, hmem⟩ := exists_pos_sub_smul_mem K x u hx
    refine ⟨t⁻¹, inv_nonneg.2 ht.le, ?_⟩
    have := hcone _ hmem t⁻¹ (inv_nonneg.2 ht.le)
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
  have hcl : IsClosed S := by
    have : S = {β : ℝ | 0 ≤ β} ∩ (fun β : ℝ => β • x - u) ⁻¹' K := by
      ext β; simp [hS]
    rw [this]
    exact (isClosed_le continuous_const continuous_id).inter
      (hKc.preimage ((continuous_id.smul continuous_const).sub continuous_const))
  have hmem := hcl.csInf_mem hne ⟨0, fun b hb => hb.1⟩
  exact hmem

lemma sigma_zero {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x : EuclideanSpace ℝ (Fin n)) : sigma K x 0 = 0 := by
  obtain ⟨hKc, -, hcone, -, ⟨z, hz⟩⟩ := hK
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := by
    simpa using hcone z (interior_subset hz) 0 le_rfl
  apply le_antisymm
  · apply csInf_le ⟨0, fun b hb => hb.1⟩
    exact ⟨le_rfl, by simpa using h0K⟩
  · exact Real.sInf_nonneg (fun b hb => hb.1)

lemma sigma_nonneg {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x u : EuclideanSpace ℝ (Fin n)) : 0 ≤ sigma K x u :=
  Real.sInf_nonneg (fun b hb => hb.1)

/-- `int K + K ⊆ int K` for a convex cone. -/
lemma add_mem_interior {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hy : y ∈ K) :
    x + y ∈ interior K := by
  obtain ⟨-, hconv, hcone, -, -⟩ := hK
  have h2y : x + (2 : ℝ) • y ∈ K := by
    have hmid := hconv (interior_subset hx) (hcone y hy 2 (by norm_num))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have := hcone _ hmid 2 (by norm_num)
    convert this using 1
    rw [smul_add, smul_smul, smul_smul]; norm_num
  have := hconv.combo_interior_self_mem_interior hx h2y
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert this using 1
  rw [smul_add, smul_smul, ← add_assoc, ← add_smul]; norm_num

end KarmarkarThm72Aux

open KarmarkarThm72Aux

theorem solution
    {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hB : Function.Surjective B)
    (c d : EuclideanSpace ℝ (Fin n)) (hd : d ∈ ConvexOptimization.dualCone K)
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (ζ : ℝ) (s : EuclideanSpace ℝ (Fin n)),
      s ∈ interior (ConvexOptimization.dualCone K) ∧
        ContinuousLinearMap.adjoint B y + ζ • d + s = c)
    (hnc : ∃ x₁ x₂ : EuclideanSpace ℝ (Fin n),
      KarFeasible K B d x₁ ∧ KarFeasible K B d x₂ ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : KarStrict K B d xh)
    (ζh : ℝ) (hζh : ζh ≤ zetaStar K B c d)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F B xh (cHat F ν c xh) yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F B xh (dHat F ν d xh) yd pd) :
    let ζp := zetaPlus K ν c d xh pc pd ζh
    let p := karDir pc pd ζp
    ∃ α : ℝ, 0 < α ∧ xh - α • p ∈ interior K ∧ B (xh - α • p) = 0 ∧
      0 < ⟪c - ζp • d, xh - α • p⟫_ℝ ∧
      karPotential F ν c d ζp (xh - α • p) ≤
        karPotential F ν c d ζh xh - (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ∧
      karPotential F ν c d ζh xh - (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ≤
        karPotential F ν c d ζh xh - (1 - Real.log 2) := by
  intro ζp p
  obtain ⟨hxi, hBx, hdx⟩ := hxh
  have hνpos : 0 < ν := by linarith
  -- Lemma 7.1
  obtain ⟨hζs, h77⟩ := SelfScaledLongStep.Karmarkar.lemma_7_1 K hK F ν hν hF B hB c d hd hD hnc
    xh ⟨hxi, hBx, hdx⟩ ζh hζh yc pc hpc yd pd hpd
  -- (7.8)
  have h78 := SelfScaledLongStep.Karmarkar.eq_7_8 K hK F ν hν hF B hB c d hd hD hnc
    xh ⟨hxi, hBx, hdx⟩ yc pc hpc yd pd hpd ζp
  change lnorm F xh p ^ 2 = ⟪c - ζp • d, p⟫_ℝ at h78
  have hposdef := hF.1.2.2.2.2 xh hxi
  have hconv : Convex ℝ K := hK.2.1
  have hcone := hK.2.2.1
  -- notation
  have hGeq : ⟪c - ζp • d, xh⟫_ℝ = ⟪c, xh⟫_ℝ - ζp := by
    rw [inner_sub_left, real_inner_smul_left, hdx]; ring
  have hBp : B p = 0 := by
    show B (pc - ζp • pd) = 0
    rw [map_sub, map_smul, hpc.1, hpd.1, smul_zero, sub_zero]
  -- ζ* is a genuine infimum
  obtain ⟨y0, ζ0, s0, hs0, hc0⟩ := hD
  have hbdd : BddBelow ((fun x => ⟪c, x⟫_ℝ) '' {x | KarFeasible K B d x}) := by
    refine ⟨ζ0, ?_⟩
    rintro _ ⟨x, ⟨hxK, hxB, hxd⟩, rfl⟩
    have hsx : 0 ≤ ⟪x, s0⟫_ℝ :=
      (interior_subset hs0 : s0 ∈ ConvexOptimization.dualCone K) x hxK
    have hcomm := real_inner_comm x s0
    show ζ0 ≤ ⟪c, x⟫_ℝ
    rw [← hc0, inner_add_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hxB,
      inner_zero_right, real_inner_smul_left, hxd]
    linarith
  have hd0 : d ≠ 0 := by rintro rfl; simp at hdx
  have hdpos : ∀ w, w ∈ interior K → 0 < ⟪d, w⟫_ℝ := by
    intro w hw
    obtain ⟨t, ht, hmem⟩ := exists_pos_sub_smul_mem K w d hw
    have h1 := hd _ hmem
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
    have : 0 < ‖d‖ := norm_pos_iff.2 hd0
    have hc := real_inner_comm d w
    nlinarith [mul_pos ht (pow_pos this 2)]
  obtain ⟨x₁, x₂, ⟨h1K, h1B, h1d⟩, ⟨h2K, h2B, h2d⟩, hne⟩ := hnc
  -- interior points with `Bw = 0` have objective strictly above `⟨d,w⟩ ζ*`
  have hstrict : ∀ w, w ∈ interior K → B w = 0 →
      ⟪d, w⟫_ℝ * zetaStar K B c d < ⟪c, w⟫_ℝ := by
    intro w hw hBw
    have hT := hdpos w hw
    have key : ∀ v : EuclideanSpace ℝ (Fin n), B v = 0 → ⟪d, v⟫_ℝ = 0 → ∀ t : ℝ,
        w - t • v ∈ K → ⟪d, w⟫_ℝ * zetaStar K B c d ≤ ⟪c, w⟫_ℝ - t * ⟪c, v⟫_ℝ := by
      intro v hBv hdv t hmem
      have hfeas : KarFeasible K B d ((⟪d, w⟫_ℝ)⁻¹ • (w - t • v)) := by
        refine ⟨hcone _ hmem _ (inv_nonneg.2 hT.le), ?_, ?_⟩
        · rw [map_smul, map_sub, map_smul, hBw, hBv, smul_zero, sub_zero, smul_zero]
        · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, hdv, mul_zero,
            sub_zero, inv_mul_cancel₀ hT.ne']
      have hle : zetaStar K B c d ≤ ⟪c, (⟪d, w⟫_ℝ)⁻¹ • (w - t • v)⟫_ℝ :=
        csInf_le hbdd ⟨_, hfeas, rfl⟩
      rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right] at hle
      have := mul_le_mul_of_nonneg_left hle hT.le
      rwa [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at this
    have hBv : B (x₁ - x₂) = 0 := by rw [map_sub, h1B, h2B, sub_zero]
    have hdv : ⟪d, x₁ - x₂⟫_ℝ = 0 := by rw [inner_sub_right, h1d, h2d, sub_self]
    obtain ⟨t1, ht1, hm1⟩ := exists_pos_sub_smul_mem K w (x₁ - x₂) hw
    obtain ⟨t2, ht2, hm2⟩ := exists_pos_sub_smul_mem K w (-(x₁ - x₂)) hw
    have k1 := key _ hBv hdv t1 hm1
    have k2 := key _ (by rw [map_neg, hBv, neg_zero]) (by rw [inner_neg_right, hdv, neg_zero])
      t2 hm2
    have hcv : ⟪c, x₁ - x₂⟫_ℝ ≠ 0 := by rw [inner_sub_right]; exact sub_ne_zero.2 hne
    rw [inner_neg_right] at k2
    rcases lt_or_gt_of_ne hcv with h | h
    · nlinarith
    · nlinarith
  have hpos : ∀ w, w ∈ interior K → B w = 0 → 0 < ⟪c - ζp • d, w⟫_ℝ := by
    intro w hw hBw
    have h1 := hstrict w hw hBw
    have h2 := hdpos w hw
    rw [inner_sub_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hζs h2.le]
  have hGpos : 0 < ⟪c - ζp • d, xh⟫_ℝ := hpos xh hxi hBx
  -- the local norm
  have hL : lnorm F xh p ^ 2 = ⟪hess F xh p, p⟫_ℝ := by
    unfold lnorm
    rw [Real.sq_sqrt]
    by_cases hp : p = 0
    · rw [hp, map_zero, inner_zero_left]
    · exact (hposdef p hp).le
  have hp0 : p ≠ 0 := by
    intro h0
    have : sigma K xh (-p) = 0 := by rw [h0, neg_zero]; exact sigma_zero K hK xh
    rw [this, mul_zero] at h77
    linarith
  have hLpos : 0 < lnorm F xh p ^ 2 := by rw [hL]; exact hposdef p hp0
  have hGp : 0 < ⟪c - ζp • d, p⟫_ℝ := by rw [← h78]; exact hLpos
  -- σ_x̂(p) > 0
  have hσpos : 0 < sigma K xh p := by
    rcases (sigma_nonneg K xh p).lt_or_eq with h | h
    · exact h
    exfalso
    have hm := (sigma_mem K hK xh p hxi).2
    rw [← h, zero_smul, zero_sub] at hm
    set t := ⟪c - ζp • d, xh⟫_ℝ / ⟪c - ζp • d, p⟫_ℝ with ht
    have htn : 0 ≤ t := div_nonneg hGpos.le hGp.le
    have hw := add_mem_interior K hK xh (t • -p) hxi (hcone _ hm t htn)
    have := hpos _ hw (by rw [map_add, map_smul, map_neg, hBx, hBp, neg_zero, smul_zero,
      add_zero])
    rw [inner_add_right, real_inner_smul_right, inner_neg_right] at this
    have e : t * ⟪c - ζp • d, p⟫_ℝ = ⟪c - ζp • d, xh⟫_ℝ := div_mul_cancel₀ _ hGp.ne'
    linarith
  set σ := sigma K xh p with hσ
  have hτ := sigma_nonneg K xh (-p)
  set A := absn K xh p with hA
  have hσA : σ ≤ A := le_max_left _ _
  have hτA : sigma K xh (-p) ≤ A := le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le hσpos hσA
  set α := 1 / (2 * A) with hα
  have hαpos : 0 < α := by positivity
  have hαs : α * σ ≤ 1 / 2 := by
    rw [hα, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hαs0 : 0 < α * σ := mul_pos hαpos hσpos
  -- x⁺ is interior
  have hxplus : xh - α • p ∈ interior K := by
    have hy : σ⁻¹ • (σ • xh - p) ∈ K :=
      hcone _ (sigma_mem K hK xh p hxi).2 _ (inv_nonneg.2 hσpos.le)
    have := hconv.combo_interior_self_mem_interior hxi hy (by linarith : 0 < 1 - α * σ)
      hαs0.le (by ring)
    convert this using 1
    rw [smul_smul]
    have e : α * σ * σ⁻¹ = α := by field_simp
    rw [e]; module
  have hBxplus : B (xh - α • p) = 0 := by
    rw [map_sub, map_smul, hBx, hBp, smul_zero, sub_zero]
  have hGplus := hpos _ hxplus hBxplus
  have hGplus_eq : ⟪c - ζp • d, xh - α • p⟫_ℝ = ⟪c - ζp • d, xh⟫_ℝ - α * ⟪c - ζp • d, p⟫_ℝ := by
    rw [inner_sub_right, real_inner_smul_right]
  -- ⟨F'(x̂), p⟩ = 0
  have hcp : ⟪cHat F ν c xh, p⟫_ℝ = ⟪hess F xh pc, p⟫_ℝ := by
    rw [← hpc.2, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hBp, inner_zero_right,
      zero_add]
  have hdp : ⟪dHat F ν d xh, p⟫_ℝ = ⟪hess F xh pd, p⟫_ℝ := by
    rw [← hpd.2, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hBp, inner_zero_right,
      zero_add]
  have hhp : ⟪hess F xh p, p⟫_ℝ = ⟪hess F xh pc, p⟫_ℝ - ζp * ⟪hess F xh pd, p⟫_ℝ := by
    have : hess F xh p = hess F xh pc - ζp • hess F xh pd := by
      show hess F xh (pc - ζp • pd) = _
      rw [map_sub, map_smul]
    rw [this, inner_sub_left, real_inner_smul_left]
  have hcp' : ⟪cHat F ν c xh, p⟫_ℝ = ⟪c, p⟫_ℝ + ⟪c, xh⟫_ℝ / ν * ⟪gradient F xh, p⟫_ℝ := by
    simp only [cHat, inner_add_left, real_inner_smul_left]
  have hdp' : ⟪dHat F ν d xh, p⟫_ℝ = ⟪d, p⟫_ℝ + 1 / ν * ⟪gradient F xh, p⟫_ℝ := by
    simp only [dHat, inner_add_left, real_inner_smul_left, hdx]
  have hGpe : ⟪c - ζp • d, p⟫_ℝ = ⟪c, p⟫_ℝ - ζp * ⟪d, p⟫_ℝ := by
    rw [inner_sub_left, real_inner_smul_left]
  have hDz : (⟪c, xh⟫_ℝ - ζp) / ν * ⟪gradient F xh, p⟫_ℝ = 0 := by
    linear_combination (-1 : ℝ) * hhp + hcp - ζp * hdp - hcp' + ζp * hdp' - hL + h78 + hGpe
  have hD0 : ⟪gradient F xh, p⟫_ℝ = 0 := by
    rcases mul_eq_zero.1 hDz with h | h
    · exfalso
      have : 0 < (⟪c, xh⟫_ℝ - ζp) / ν := div_pos (by linarith) hνpos
      linarith
    · exact h
  -- Theorem 4.2
  have h42 := SelfScaledLongStep.PrimalDual.theorem_4_2 K hK F ν hν hF xh p hxi hσpos α
    hαpos.le (by linarith)
  -- monotonicity of (−τ − ln(1−τ))/τ² (Proposition 4.1 (iii))
  have h41 := (SelfScaledLongStep.PrimalDual.proposition_4_1).2.2
  have hmono := h41.monotoneOn (show α * σ ∈ Set.Iio (1 : ℝ) by simp; linarith)
    (show (1 / 2 : ℝ) ∈ Set.Iio (1 : ℝ) by norm_num) hαs
  try dsimp only at hmono
  rw [if_neg hαs0.ne', if_neg (by norm_num)] at hmono
  have hlog2 : Real.log (1 - 1 / 2) = - Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [hlog2, div_le_iff₀ (by positivity)] at hmono
  set L := lnorm F xh p ^ 2 with hLdef
  have hWbound : L / σ ^ 2 * (-(α * σ) - Real.log (1 - α * σ)) ≤
      L / A ^ 2 * (-(1 / 2) + Real.log 2) := by
    have h1 : L / σ ^ 2 * (-(α * σ) - Real.log (1 - α * σ)) ≤
        L / σ ^ 2 * ((-(1 / 2) - -Real.log 2) / (1 / 2) ^ 2 * (α * σ) ^ 2) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have h2 : L / σ ^ 2 * ((-(1 / 2) - -Real.log 2) / (1 / 2) ^ 2 * (α * σ) ^ 2) =
        L / A ^ 2 * (-(1 / 2) + Real.log 2) := by
      rw [hα]; field_simp; ring
    linarith
  -- the logarithmic part
  set G := ⟪c - ζp • d, xh⟫_ℝ with hG
  set Gp := ⟪c - ζp • d, p⟫_ℝ with hGpdef
  have hlogpart : ν * Real.log ⟪c - ζp • d, xh - α • p⟫_ℝ ≤
      ν * Real.log G - ν * (α * Gp / G) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hGplus hGpos)
    rw [Real.log_div hGplus.ne' hGpos.ne', hGplus_eq] at h1
    have h2 : (G - α * Gp) / G - 1 = -(α * Gp / G) := by field_simp; ring
    have h3 : Real.log (G - α * Gp) ≤ Real.log G - α * Gp / G := by linarith
    rw [hGplus_eq]
    have := mul_le_mul_of_nonneg_left h3 hνpos.le
    rw [mul_sub] at this
    exact this
  have hνG : 1 / A ≤ ν / G := by
    rw [div_le_div_iff₀ hApos hGpos]
    have : ⟪c, xh⟫_ℝ - ζp ≤ ν * A := le_trans h77 (mul_le_mul_of_nonneg_left hτA hνpos.le)
    linarith
  have hνterm : L / A ^ 2 * (1 / 2) ≤ ν * (α * Gp / G) := by
    have := mul_le_mul_of_nonneg_left hνG (by positivity : 0 ≤ α * Gp)
    have e1 : ν * (α * Gp / G) = α * Gp * (ν / G) := by ring
    have e2 : L / A ^ 2 * (1 / 2) = α * Gp * (1 / A) := by
      simp only [hα, ← h78]; field_simp
    linarith
  -- ζ̂ ≤ ζ⁺
  have hζle : ζh ≤ ζp := by
    show ζh ≤ zetaPlus K ν c d xh pc pd ζh
    unfold zetaPlus
    split_ifs
    · have := one_div_nonneg.2 (sigma_nonneg K (xTilde ν c d xh pc pd ζh) (pd + (1 / ν) • xh))
      linarith
    · exact le_rfl
  have hGh : G ≤ ⟪c - ζh • d, xh⟫_ℝ := by
    rw [hGeq, inner_sub_left, real_inner_smul_left, hdx]; linarith
  have hlogmono := Real.log_le_log hGpos hGh
  have hLA : 1 ≤ L / A ^ 2 := by
    have h35 := ((SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).1 xh hxi p).1
    rw [le_div_iff₀ (by positivity), one_mul, hLdef]
    exact pow_le_pow_left₀ hApos.le h35 2
  have hln2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  refine ⟨α, hαpos, hxplus, hBxplus, hGplus, ?_, ?_⟩
  · unfold karPotential
    rw [hD0, mul_zero, sub_zero] at h42
    have hm := mul_le_mul_of_nonneg_left hlogmono hνpos.le
    linarith
  · have := mul_le_mul_of_nonneg_right hLA (by linarith : (0 : ℝ) ≤ 1 - Real.log 2)
    linarith
