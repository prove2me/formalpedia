-- Prove2me | solution 1 for SelfScaledLongStep.Karmarkar.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:40:05.492506+00:00
-- url     : https://prove2.me/submissions/50daa19f-a21e-485d-8d86-b097e4da66b0

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_Karmarkar_Defs
import Theorems.Thm_ExpConeIPM_Corrector_homogeneity_identities

open scoped InnerProductSpace Pointwise
open SelfScaledIPM.ShortStep
open SelfScaledLongStep.Karmarkar

namespace KarmarkarLem71Aux

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


/-- A positive multiple of an interior point of a cone is interior. -/
lemma smul_mem_interior {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (t : ℝ) (ht : 0 < t) :
    t • x ∈ interior K := by
  have hcone := hK.2.2.1
  refine mem_interior.2 ⟨t • interior K, ?_, isOpen_interior.smul₀ ht.ne', Set.smul_mem_smul_set hx⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hcone z (interior_subset hz) t ht.le

lemma isClosed_dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (ConvexOptimization.dualCone K) := by
  have : ConvexOptimization.dualCone K = ⋂ x ∈ K, {y | 0 ≤ ⟪x, y⟫_ℝ} := by
    ext y; simp [ConvexOptimization.dualCone]
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_le continuous_const (continuous_const.inner continuous_id)

end KarmarkarLem71Aux

open KarmarkarLem71Aux

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
    ζp ≤ zetaStar K B c d ∧ ⟪c, xh⟫_ℝ - ζp ≤ ν * sigma K xh (-p) := by
  intro ζp p
  obtain ⟨hxi, hBx, hdx⟩ := hxh
  have hνpos : 0 < ν := by linarith
  have hcone := hK.2.2.1
  have hhom := (ExpConeIPM.Corrector.homogeneity_identities K F ν hK hF.1 xh hxi 1 one_pos).2.2.1
  -- the dual slack attached to `x̃(ζ)`
  have hdual : ∀ ζ : ℝ, hess F xh (xTilde ν c d xh pc pd ζ) =
      c - ζ • d - ContinuousLinearMap.adjoint B (yc - ζ • yd) := by
    intro ζ
    have e1 : hess F xh pc = cHat F ν c xh - ContinuousLinearMap.adjoint B yc :=
      eq_sub_of_add_eq' hpc.2
    have e2 : hess F xh pd = dHat F ν d xh - ContinuousLinearMap.adjoint B yd :=
      eq_sub_of_add_eq' hpd.2
    simp only [xTilde, map_add, map_sub, map_smul, e1, e2, hhom, cHat, dHat, hdx,
      inner_sub_left, real_inner_smul_left]
    module
  -- linearity of `x̃` in `ζ`
  have hlin : ∀ ζ ζ' : ℝ, xTilde ν c d xh pc pd ζ' =
      xTilde ν c d xh pc pd ζ - (ζ' - ζ) • (pd + (1 / ν) • xh) := by
    intro ζ ζ'
    simp only [xTilde, inner_sub_left, real_inner_smul_left, hdx]
    module
  -- the Hessian maps `K` into `K*`
  have hmapK : ∀ z ∈ K, hess F xh z ∈ ConvexOptimization.dualCone K := by
    have hS : IsClosed {z | hess F xh z ∈ ConvexOptimization.dualCone K} :=
      (isClosed_dualCone K).preimage (hess F xh).continuous
    have hsub : interior K ⊆ {z | hess F xh z ∈ ConvexOptimization.dualCone K} :=
      fun z hz => by
        simp only [Set.mem_setOf_eq]; exact interior_subset (hF.2 xh hxi z hz).1
    have hcl := closure_minimal hsub hS
    rw [hK.2.1.closure_interior_eq_closure_of_nonempty_interior hK.2.2.2.2,
      hK.1.closure_eq] at hcl
    exact hcl
  -- weak duality
  have hfeasne : ({x | KarFeasible K B d x} : Set _).Nonempty :=
    ⟨xh, interior_subset hxi, hBx, hdx⟩
  have hweak : ∀ ζ : ℝ, xTilde ν c d xh pc pd ζ ∈ K → ζ ≤ zetaStar K B c d := by
    intro ζ hz
    have hs := hmapK _ hz
    rw [hdual ζ] at hs
    apply le_csInf (hfeasne.image _)
    rintro _ ⟨x, ⟨hxK, hxB, hxd⟩, rfl⟩
    have h1 := hs x hxK
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right, hxB, inner_zero_left] at h1
    have e1 := real_inner_comm x c
    have e2 := real_inner_comm x d
    show ζ ≤ ⟪c, x⟫_ℝ
    rw [← e2, hxd] at h1
    linarith
  -- upper bound on ζ*
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
  have hζup : zetaStar K B c d ≤ ⟪c, xh⟫_ℝ :=
    csInf_le hbdd ⟨xh, ⟨interior_subset hxi, hBx, hdx⟩, rfl⟩
  set pt := pd + (1 / ν) • xh with hpt
  set x0 := xTilde ν c d xh pc pd ζh with hx0
  -- `x̃(ζ⁺)` is in `K` but not in `int K`, and `ζ⁺ ≤ ζ*`
  have key : ζp ≤ zetaStar K B c d ∧ xTilde ν c d xh pc pd ζp ∉ interior K := by
    show zetaPlus K ν c d xh pc pd ζh ≤ zetaStar K B c d ∧
      xTilde ν c d xh pc pd (zetaPlus K ν c d xh pc pd ζh) ∉ interior K
    unfold zetaPlus
    split_ifs with hin
    · obtain ⟨hσ0, hσmem⟩ := sigma_mem K hK x0 pt hin
      rcases hσ0.lt_or_eq with hσ | hσ
      · have hK1 : xTilde ν c d xh pc pd (ζh + 1 / sigma K x0 pt) ∈ K := by
          rw [hlin ζh, add_sub_cancel_left]
          have := hcone _ hσmem (sigma K x0 pt)⁻¹ (inv_nonneg.2 hσ.le)
          convert this using 1
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hσ.ne', one_smul, one_div]
        refine ⟨hweak _ hK1, ?_⟩
        intro hint
        obtain ⟨ε, hε, hεmem⟩ := exists_pos_sub_smul_mem K _ pt hint
        rw [hlin ζh, add_sub_cancel_left, sub_sub, ← add_smul] at hεmem
        set s := 1 / sigma K x0 pt + ε with hs
        have hspos : 0 < s := by positivity
        have hmem' : s⁻¹ • x0 - pt ∈ K := by
          have := hcone _ hεmem s⁻¹ (inv_nonneg.2 hspos.le)
          convert this using 1
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        have hle : sigma K x0 pt ≤ s⁻¹ :=
          csInf_le ⟨0, fun b hb => hb.1⟩ ⟨inv_nonneg.2 hspos.le, hmem'⟩
        have : s⁻¹ < sigma K x0 pt := by
          rw [inv_lt_comm₀ hspos hσ, hs]
          have : (sigma K x0 pt)⁻¹ = 1 / sigma K x0 pt := (one_div _).symm
          linarith
        linarith
      · exfalso
        rw [← hσ, zero_smul, zero_sub] at hσmem
        have hz : xTilde ν c d xh pc pd (⟪c, xh⟫_ℝ + 1) ∈ K := by
          rw [hlin ζh, sub_eq_add_neg, ← smul_neg]
          exact interior_subset (add_mem_interior K hK _ _ hin
            (hcone _ hσmem _ (by linarith)))
        have := hweak _ hz
        linarith
    · exact ⟨hζh, hin⟩
  refine ⟨key.1, ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨hτ0, hτmem⟩ := sigma_mem K hK xh (-p) hxi
  rw [sub_neg_eq_add] at hτmem
  have hgap : 0 < (⟪c, xh⟫_ℝ - ζp) / ν - sigma K xh (-p) := by
    rw [sub_pos, lt_div_iff₀ hνpos]; linarith
  apply key.2
  have heq : xTilde ν c d xh pc pd ζp =
      ((⟪c, xh⟫_ℝ - ζp) / ν - sigma K xh (-p)) • xh + (sigma K xh (-p) • xh + p) := by
    show (⟪c - ζp • d, xh⟫_ℝ / ν) • xh + (pc - ζp • pd) = _
    rw [inner_sub_left, real_inner_smul_left, hdx]
    show _ = _ • xh + (_ • xh + (pc - ζp • pd))
    module
  rw [heq]
  exact add_mem_interior K hK _ _ (smul_mem_interior K hK xh hxi _ hgap) hτmem
