-- Prove2me | solution 1 for SelfScaledLongStep.AffinePot.theorem_7_4_b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:57:14.621191+00:00
-- url     : https://prove2.me/submissions/2506f82f-aa69-4557-b5e3-3294d818402f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_AffinePot_Defs
import Theorems.Thm_SelfScaledLongStep_AffinePot_lemma_7_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_2
import Theorems.Thm_SelfScaledLongStep_PrimalDual_eq_4_9
import Theorems.Thm_SelfScaledLongStep_PrimalDual_proposition_4_1
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep
open SelfScaledLongStep.AffinePot

namespace AffPotThm74bAux

lemma exists_pos_sub_smul_mem {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x u : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    ∃ t : ℝ, 0 < t ∧ x - t • u ∈ K := by
  have hc : Continuous (fun t : ℝ => x - t • u) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have ho : IsOpen ((fun t : ℝ => x - t • u) ⁻¹' interior K) := isOpen_interior.preimage hc
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x - t • u) ⁻¹' interior K := by simpa using hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ho 0 h0
  refine ⟨r / 2, by positivity, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith

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
  exact hcl.csInf_mem hne ⟨0, fun b hb => hb.1⟩

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

end AffPotThm74bAux

open AffPotThm74bAux

theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ y s, IsDualStrict K A c y s)
    (hnc : ∃ x₁ x₂, (x₁ ∈ K ∧ A x₁ = b) ∧ (x₂ ∈ K ∧ A x₂ = b) ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (μ : ℝ) (hμ : 2 * ν ≤ μ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsPrimalStrict K A b xh) (ζh : ℝ) (hζh : ζh ≤ zetaStar K A b c)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F A xh c yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F A xh (gradient F xh) yd pd) :
    let ζp := zetaPlus K F c xh pc pd ζh
    let p := affDir K F μ c xh pc pd ζh
    (∃ α : ℝ, 0 < α ∧ IsPrimalStrict K A b (xh - α • p) ∧ 0 < ⟪c, xh - α • p⟫_ℝ - ζp ∧
      affPotential F μ c ζp (xh - α • p) ≤ affPotential F μ c ζh xh -
        (lnorm F xh p) ^ 2 / (max (sigma K xh p) (absn K xh p)) ^ 2 * (1 - Real.log 2)) ∧
    (lnorm F xh p) ^ 2 / (max (sigma K xh p) (absn K xh p)) ^ 2 * (1 - Real.log 2) =
      (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ∧
    affPotential F μ c ζh xh - (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ≤
      affPotential F μ c ζh xh - (1 - Real.log 2) := by
  intro ζp p
  have hνpos : 0 < ν := by linarith
  have hμpos : 0 < μ := by linarith
  obtain ⟨hxi, hAx⟩ := hxh
  have hposdef := hF.1.2.2.2.2 xh hxi
  have hconv : Convex ℝ K := hK.2.1
  have hcone := hK.2.2.1
  -- Lemma 7.2
  have h72 := (SelfScaledLongStep.AffinePot.lemma_7_2 K hK F ν hν hF A hA b c hD hnc μ
    (by linarith) xh ⟨hxi, hAx⟩ ζh hζh yc pc hpc yd pd hpd).2 hμ
  change lam μ c xh ζp ≤ absn K xh p at h72
  -- the objective is bounded below on the feasible set
  obtain ⟨y0, s0, hs0, hc0⟩ := hD
  have hfeas_ge : ∀ x, x ∈ K → A x = b → ⟪y0, b⟫_ℝ ≤ ⟪c, x⟫_ℝ := by
    intro x hxK hxA
    have hsx : 0 ≤ ⟪x, s0⟫_ℝ :=
      (interior_subset hs0 : s0 ∈ ConvexOptimization.dualCone K) x hxK
    have hcomm := real_inner_comm x s0
    rw [← hc0, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hxA]
    linarith
  have hbdd : BddBelow ((fun x => ⟪c, x⟫_ℝ) '' {x | x ∈ K ∧ A x = b}) := by
    refine ⟨⟪y0, b⟫_ℝ, ?_⟩
    rintro _ ⟨x, ⟨hxK, hxA⟩, rfl⟩
    exact hfeas_ge x hxK hxA
  -- interior feasible points have objective strictly above ζ*
  obtain ⟨x₁, x₂, ⟨h1K, h1A⟩, ⟨h2K, h2A⟩, hne⟩ := hnc
  have hstrict : ∀ w, w ∈ interior K → A w = b → zetaStar K A b c < ⟪c, w⟫_ℝ := by
    intro w hw hAw
    have key : ∀ v : EuclideanSpace ℝ (Fin n), A v = 0 → ∀ t : ℝ,
        w - t • v ∈ K → zetaStar K A b c ≤ ⟪c, w⟫_ℝ - t * ⟪c, v⟫_ℝ := by
      intro v hAv t hmem
      have hle : zetaStar K A b c ≤ ⟪c, w - t • v⟫_ℝ := by
        refine csInf_le hbdd ⟨_, ⟨hmem, ?_⟩, rfl⟩
        rw [map_sub, map_smul, hAv, smul_zero, sub_zero, hAw]
      rwa [inner_sub_right, real_inner_smul_right] at hle
    have hAv : A (x₁ - x₂) = 0 := by rw [map_sub, h1A, h2A, sub_self]
    obtain ⟨t1, ht1, hm1⟩ := exists_pos_sub_smul_mem K w (x₁ - x₂) hw
    obtain ⟨t2, ht2, hm2⟩ := exists_pos_sub_smul_mem K w (-(x₁ - x₂)) hw
    have k1 := key _ hAv t1 hm1
    have k2 := key _ (by rw [map_neg, hAv, neg_zero]) t2 hm2
    have hcv : ⟪c, x₁ - x₂⟫_ℝ ≠ 0 := by rw [inner_sub_right]; exact sub_ne_zero.2 hne
    rw [inner_neg_right] at k2
    rcases lt_or_gt_of_ne hcv with h | h
    · nlinarith
    · nlinarith
  -- ζ⁺ ≤ ζ* and ζ̂ ≤ ζ⁺
  have hζle : ζh ≤ ζp := by
    show ζh ≤ zetaPlus K F c xh pc pd ζh
    unfold zetaPlus
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hζs : ζp ≤ zetaStar K A b c := by
    show zetaPlus K F c xh pc pd ζh ≤ zetaStar K A b c
    unfold zetaPlus
    split_ifs with hne'
    · refine max_le hζh (csSup_le hne' ?_)
      rintro z ⟨t, hst, rfl⟩
      refine le_csInf ⟨_, ⟨xh, ⟨interior_subset hxi, hAx⟩, rfl⟩⟩ ?_
      rintro _ ⟨x, ⟨hxK, hxA⟩, rfl⟩
      have hs : sTilde F xh pc pd t = c - ContinuousLinearMap.adjoint A (yc + t • yd) := by
        unfold sTilde
        have e1 := hpc.2
        have e2 := hpd.2
        rw [map_add, map_smul, map_add, map_smul]
        rw [← e1, ← e2]
        module
      have hsx : 0 ≤ ⟪x, sTilde F xh pc pd t⟫_ℝ := hst x hxK
      rw [real_inner_comm] at hsx
      have hx1 : ⟪c, x⟫_ℝ = ⟪sTilde F xh pc pd t, x⟫_ℝ + ⟪yc + t • yd, b⟫_ℝ := by
        rw [hs, inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hxA]; ring
      have hx2 : ⟪c, xh⟫_ℝ = ⟪sTilde F xh pc pd t, xh⟫_ℝ + ⟪yc + t • yd, b⟫_ℝ := by
        rw [hs, inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hAx]; ring
      show ⟪c, xh⟫_ℝ - ⟪sTilde F xh pc pd t, xh⟫_ℝ ≤ ⟪c, x⟫_ℝ
      linarith
    · exact hζh
  have hpos : ∀ w, w ∈ interior K → A w = b → 0 < ⟪c, w⟫_ℝ - ζp := by
    intro w hw hAw
    have := hstrict w hw hAw
    linarith
  set G := ⟪c, xh⟫_ℝ - ζp with hG
  have hGpos : 0 < G := hpos xh hxi hAx
  set lp := lam μ c xh ζp with hlp
  have hlpeq : lp = G / μ := rfl
  have hlpos : 0 < lp := div_pos hGpos hμpos
  set Ab := absn K xh p with hAb
  have hApos : 0 < Ab := lt_of_lt_of_le hlpos h72
  -- p ≠ 0
  have hp0 : p ≠ 0 := by
    intro h0
    have : Ab = 0 := by
      rw [hAb, h0]; unfold absn; rw [neg_zero, sigma_zero K hK xh, max_self]
    linarith
  have hAp : A p = 0 := by
    show A (pc + lam μ c xh (zetaPlus K F c xh pc pd ζh) • pd) = 0
    rw [map_add, map_smul, hpc.1, hpd.1, smul_zero, add_zero]
  -- local norm
  have hL : lnorm F xh p ^ 2 = ⟪hess F xh p, p⟫_ℝ := by
    unfold lnorm
    rw [Real.sq_sqrt (hposdef p hp0).le]
  set L := lnorm F xh p ^ 2 with hLdef
  have hLpos : 0 < L := by rw [hL]; exact hposdef p hp0
  -- ⟨c,p⟩ + λ⁺⟨F'(x̂),p⟩ = ‖p‖²
  have hcp : ⟪c, p⟫_ℝ = ⟪hess F xh pc, p⟫_ℝ := by
    rw [← hpc.2, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hAp, inner_zero_right,
      zero_add]
  have hdp : ⟪gradient F xh, p⟫_ℝ = ⟪hess F xh pd, p⟫_ℝ := by
    rw [← hpd.2, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hAp, inner_zero_right,
      zero_add]
  have hhp : ⟪hess F xh p, p⟫_ℝ = ⟪hess F xh pc, p⟫_ℝ + lp * ⟪hess F xh pd, p⟫_ℝ := by
    have : hess F xh p = hess F xh pc + lp • hess F xh pd := by
      show hess F xh (pc + lam μ c xh (zetaPlus K F c xh pc pd ζh) • pd) = _
      rw [map_add, map_smul]
    rw [this, inner_add_left, real_inner_smul_left]
  have hkey : ⟪c, p⟫_ℝ + lp * ⟪gradient F xh, p⟫_ℝ = L := by
    rw [hcp, hdp, hL, hhp]
  -- generic decrease estimate, given an upper bound on F along the step
  have hLA : 1 ≤ L / Ab ^ 2 := by
    have h35 := ((SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).1 xh hxi p).1
    rw [le_div_iff₀ (by positivity), one_mul, hLdef]
    exact pow_le_pow_left₀ hApos.le h35 2
  have hln2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hln2' : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hsA : sigma K xh p ≤ Ab := le_max_left _ _
  have hmaxeq : max (sigma K xh p) Ab = Ab := max_eq_right hsA
  have hlogmono : Real.log G ≤ Real.log (⟪c, xh⟫_ℝ - ζh) :=
    Real.log_le_log hGpos (by linarith)
  -- core: for any admissible α with an F-bound R, potential decreases by αL/λ − R
  have core : ∀ α : ℝ, 0 < α → xh - α • p ∈ interior K → ∀ R : ℝ,
      F (xh - α • p) ≤ F xh - α * ⟪gradient F xh, p⟫_ℝ + R →
      α * L / Ab - R ≥ L / Ab ^ 2 * (1 - Real.log 2) →
      (∃ α : ℝ, 0 < α ∧ IsPrimalStrict K A b (xh - α • p) ∧ 0 < ⟪c, xh - α • p⟫_ℝ - ζp ∧
        affPotential F μ c ζp (xh - α • p) ≤ affPotential F μ c ζh xh -
          L / (max (sigma K xh p) Ab) ^ 2 * (1 - Real.log 2)) := by
    intro α hα hxint R hR hdec
    have hAxp : A (xh - α • p) = b := by rw [map_sub, map_smul, hAp, smul_zero, sub_zero, hAx]
    have hGp := hpos _ hxint hAxp
    refine ⟨α, hα, ⟨hxint, hAxp⟩, hGp, ?_⟩
    rw [hmaxeq]
    have hGeq : ⟪c, xh - α • p⟫_ℝ - ζp = G - α * ⟪c, p⟫_ℝ := by
      rw [inner_sub_right, real_inner_smul_right, hG]; ring
    rw [hGeq] at hGp
    have h1 := Real.log_le_sub_one_of_pos (div_pos hGp hGpos)
    rw [Real.log_div hGp.ne' hGpos.ne'] at h1
    have h2 : (G - α * ⟪c, p⟫_ℝ) / G - 1 = -(α * ⟪c, p⟫_ℝ / G) := by field_simp; ring
    have h3 : μ * Real.log (G - α * ⟪c, p⟫_ℝ) ≤ μ * Real.log G - α * ⟪c, p⟫_ℝ / lp := by
      have := mul_le_mul_of_nonneg_left (show Real.log (G - α * ⟪c, p⟫_ℝ) ≤
        Real.log G - α * ⟪c, p⟫_ℝ / G by linarith) hμpos.le
      have e : μ * (α * ⟪c, p⟫_ℝ / G) = α * ⟪c, p⟫_ℝ / lp := by
        rw [hlpeq]; field_simp
      linarith [show μ * (Real.log G - α * ⟪c, p⟫_ℝ / G) =
        μ * Real.log G - μ * (α * ⟪c, p⟫_ℝ / G) by ring]
    have h4 : α * ⟪c, p⟫_ℝ / lp + α * ⟪gradient F xh, p⟫_ℝ = α * L / lp := by
      rw [← hkey]; field_simp
    have h5 : α * L / Ab ≤ α * L / lp :=
      div_le_div_of_nonneg_left (by positivity) hlpos h72
    have hm := mul_le_mul_of_nonneg_left hlogmono hμpos.le
    unfold affPotential
    rw [hGeq]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rcases (sigma_nonneg K xh p).lt_or_eq with hσpos | hσ0
    · -- σ_x̂(p) > 0: Theorem 4.2 with α = 1/(2|p|)
      set σ := sigma K xh p with hσ
      set α := 1 / (2 * Ab) with hα
      have hαpos : 0 < α := by positivity
      have hαs : α * σ ≤ 1 / 2 := by
        rw [hα, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
      have hαs0 : 0 < α * σ := mul_pos hαpos hσpos
      have hxplus : xh - α • p ∈ interior K := by
        have hy : σ⁻¹ • (σ • xh - p) ∈ K :=
          hcone _ (sigma_mem K hK xh p hxi).2 _ (inv_nonneg.2 hσpos.le)
        have := hconv.combo_interior_self_mem_interior hxi hy (by linarith : 0 < 1 - α * σ)
          hαs0.le (by ring)
        convert this using 1
        rw [smul_smul]
        have e : α * σ * σ⁻¹ = α := by field_simp
        rw [e]; module
      have h42 := SelfScaledLongStep.PrimalDual.theorem_4_2 K hK F ν hν hF xh p hxi hσpos α
        hαpos.le (by linarith)
      have h41 := (SelfScaledLongStep.PrimalDual.proposition_4_1).2.2
      have hmono := h41.monotoneOn (show α * σ ∈ Set.Iio (1 : ℝ) by simp; linarith)
        (show (1 / 2 : ℝ) ∈ Set.Iio (1 : ℝ) by norm_num) hαs
      try dsimp only at hmono
      rw [if_neg hαs0.ne', if_neg (by norm_num)] at hmono
      have hlog2 : Real.log (1 - 1 / 2) = - Real.log 2 := by
        rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
      rw [hlog2, div_le_iff₀ (by positivity)] at hmono
      have hWbound : L / σ ^ 2 * (-(α * σ) - Real.log (1 - α * σ)) ≤
          L / Ab ^ 2 * (-(1 / 2) + Real.log 2) := by
        have h1 : L / σ ^ 2 * (-(α * σ) - Real.log (1 - α * σ)) ≤
            L / σ ^ 2 * ((-(1 / 2) - -Real.log 2) / (1 / 2) ^ 2 * (α * σ) ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
        have h2 : L / σ ^ 2 * ((-(1 / 2) - -Real.log 2) / (1 / 2) ^ 2 * (α * σ) ^ 2) =
            L / Ab ^ 2 * (-(1 / 2) + Real.log 2) := by
          rw [hα]; field_simp; ring
        linarith
      refine core α hαpos hxplus _ h42 ?_
      have e : α * L / Ab = L / Ab ^ 2 * (1 / 2) := by rw [hα]; field_simp
      linarith
    · -- σ_x̂(p) = 0: then −p ∈ K, use (4.9) with α = 1/|p|
      have hm := (sigma_mem K hK xh p hxi).2
      rw [← hσ0, zero_smul, zero_sub] at hm
      set α := 1 / Ab with hα
      have hαpos : 0 < α := by positivity
      have hxplus : xh - α • p ∈ interior K := by
        have := add_mem_interior K hK xh (α • -p) hxi (hcone _ hm α hαpos.le)
        rwa [smul_neg, ← sub_eq_add_neg] at this
      have h49 := SelfScaledLongStep.PrimalDual.eq_4_9 K hK F ν hν hF xh (-p) hxi hm α hαpos.le
      have hln : lnorm F xh (-p) = lnorm F xh p := by
        unfold lnorm; rw [map_neg, inner_neg_left, inner_neg_right, neg_neg]
      rw [hln, smul_neg, ← sub_eq_add_neg, inner_neg_right] at h49
      refine core α hαpos hxplus (α ^ 2 / 2 * L) (by linarith) ?_
      have e1 : α * L / Ab = L / Ab ^ 2 := by rw [hα]; field_simp
      have e2 : α ^ 2 / 2 * L = L / Ab ^ 2 * (1 / 2) := by rw [hα]; field_simp
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left hln2'.le (by positivity : (0 : ℝ) ≤ L / Ab ^ 2)
      nlinarith
  · rw [hmaxeq]
  · have := mul_le_mul_of_nonneg_right hLA (by linarith : (0 : ℝ) ≤ 1 - Real.log 2)
    linarith
