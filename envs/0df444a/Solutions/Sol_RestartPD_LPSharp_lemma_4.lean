-- Prove2me | solution 1 for RestartPD.LPSharp.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T11:47:04.267119+00:00
-- url     : https://prove2.me/submissions/525801a4-84d8-4227-a3a7-9f7d9d1eccaa

import Mathlib
import Definitions.Def_RestartPD_LPSharp_LP
set_option autoImplicit false
open scoped InnerProductSpace Matrix
open RestartPD.LPSharp
namespace LPSharpProof
variable {n m : ℕ}
lemma le_rho (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z w : PDSpace n m)
    (r : ℝ) (hr : 0 < r) (hw : w ∈ Wball lpX Set.univ r z) :
    ((gapAt (lpL A b c) z w / r : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by
  rw [rho, if_neg hr.ne']
  exact le_iSup_of_le w (le_iSup_of_le hw le_rfl)
lemma rho_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (hz : z.1 ∈ lpX)
    (r : ℝ) (hr : 0 < r) : 0 ≤ rho (lpL A b c) lpX Set.univ r z := by
  have hw : z ∈ Wball lpX Set.univ r z := ⟨⟨hz,Set.mem_univ _⟩,by simpa using hr.le⟩
  simpa [gapAt] using le_rho A b c z z r hr hw
lemma gap_shrink (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z ((1-t) • z) = t * (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ) := by
  simp only [gapAt,lpL,Prod.smul_fst,Prod.smul_snd,map_smul,real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm z.2 b]
  ring
end LPSharpProof
namespace LPSharpProof
variable {n m : ℕ}
lemma eucl_sq (z : PDSpace n m) :
    eucl n m z ^ 2 = ‖z.1‖^2 + ‖z.2‖^2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 z)
lemma transpose_inner (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    ⟪Matrix.toEuclideanLin Aᵀ y,x⟫_ℝ = ⟪y,Matrix.toEuclideanLin A x⟫_ℝ := by
  simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    LinearMap.adjoint_inner_left (Matrix.toEuclideanLin A) x y
lemma inner_pos (u : EuclideanSpace ℝ (Fin n)) :
    ⟪u,WithLp.toLp 2 (fun i => max (u i) 0)⟫_ℝ =
      ‖(WithLp.toLp 2 (fun i => max (u i) 0) : EuclideanSpace ℝ (Fin n))‖^2 := by
  rw [PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.inner_apply]
  change u i * max (u i) 0 = max (u i) 0 ^ 2
  by_cases hi : 0 ≤ u i
  · rw [max_eq_left hi]; ring
  · rw [max_eq_right (le_of_not_ge hi)]; ring
lemma gap_forward (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z v : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z (z + t • v) =
      t * (⟪Matrix.toEuclideanLin Aᵀ z.2-c,v.1⟫_ℝ +
        ⟪b-Matrix.toEuclideanLin A z.1,v.2⟫_ℝ) := by
  simp only [gapAt,lpL,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,inner_sub_left,transpose_inner]
  rw [real_inner_comm b v.2,real_inner_comm (Matrix.toEuclideanLin A z.1) v.2]
  ring
lemma gap_v (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z (z+t • vvec A b c z) = t * eucl n m (vvec A b c z)^2 := by
  rw [gap_forward,eucl_sq]
  have h := inner_pos (Matrix.toEuclideanLin Aᵀ z.2-c)
  simpa only [vvec,PiLp.sub_apply,real_inner_self_eq_norm_sq] using
    congrArg (fun q => t * (q + ‖b-Matrix.toEuclideanLin A z.1‖^2)) h
end LPSharpProof
theorem LPSharpProof.eq22 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m)
    (hz : z ∈ (lpX : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Set.univ)
    (r : ℝ) (hr : 0 < r) :
    ((eucl n m (vvec A b c z) : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by
  let v := vvec A b c z
  let q := eucl n m v
  have hq : 0 ≤ q := apply_nonneg _ _
  by_cases hq0 : q = 0
  · change (q : EReal) ≤ _
    rw [hq0,EReal.coe_zero]
    exact LPSharpProof.rho_nonneg A b c z hz.1 r hr
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have ht : 0 ≤ r/q := (div_pos hr hqp).le
  have hw : z+(r/q) • v ∈ Wball lpX Set.univ r z := by
    refine ⟨⟨?_,Set.mem_univ _⟩,?_⟩
    · intro i
      change 0 ≤ z.1 i + (r/q)*max ((Matrix.toEuclideanLin Aᵀ z.2) i-c i) 0
      exact add_nonneg (hz.1 i) (mul_nonneg ht (le_max_right _ _))
    · have he : z-(z+(r/q) • v) = -((r/q) • v) := by abel
      rw [he,map_neg_eq_map,map_smul_eq_mul,Real.norm_of_nonneg ht]
      change r/q*q ≤ r
      rw [div_mul_cancel₀ r hq0]
  have h := LPSharpProof.le_rho A b c z (z+(r/q) • v) r hr hw
  rw [LPSharpProof.gap_v] at h
  have he : r/q * q^2/r = q := by field_simp
  change ((r/q*q^2/r : ℝ) : EReal) ≤ _ at h
  rw [he] at h
  exact h

theorem LPSharpProof.eq25 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R) (z : PDSpace n m)
    (hz : z ∈ Wball lpX Set.univ R 0) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ((max (⟪c, z.1⟫_ℝ - ⟪b, z.2⟫_ℝ) 0 / R : ℝ) : EReal) ≤
      rho (lpL A b c) lpX Set.univ r z := by
  have ht0 : 0 ≤ r/R := (div_pos hr hR).le
  have ht1 : r/R ≤ 1 := (div_le_one hR).2 hrR
  have hn : eucl n m z ≤ R := by simpa only [zero_sub,map_neg_eq_map] using hz.2
  have hw : (1-r/R) • z ∈ Wball lpX Set.univ r z := by
    refine ⟨⟨?_,Set.mem_univ _⟩,?_⟩
    · intro i
      change 0 ≤ (1-r/R) * z.1 i
      exact mul_nonneg (sub_nonneg.mpr ht1) (hz.1.1 i)
    · have he : z - (1-r/R) • z = (r/R) • z := by module
      rw [he,map_smul_eq_mul,Real.norm_of_nonneg ht0]
      calc
        r/R * eucl n m z ≤ r/R * R := mul_le_mul_of_nonneg_left hn ht0
        _ = r := div_mul_cancel₀ r hR.ne'
  have h := LPSharpProof.le_rho A b c z ((1-r/R) • z) r hr hw
  rw [LPSharpProof.gap_shrink] at h
  have he : r/R * (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ) / r =
      (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ)/R := by field_simp
  rw [he] at h
  by_cases hg : 0 ≤ ⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ
  · simpa only [max_eq_left hg] using h
  · simpa only [max_eq_right (le_of_not_ge hg),zero_div,EReal.coe_zero] using
      LPSharpProof.rho_nonneg A b c z hz.1.1 r hr

set_option autoImplicit false
open RestartPD.LPSharp
open scoped InnerProductSpace Matrix
namespace LPSharpProof
variable {n m : ℕ}
lemma pos_parts_sq (a : ℝ) : max a 0 ^ 2 + max (-a) 0 ^ 2 = a^2 := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
    ring
lemma kkt_sq (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (hz : z.1 ∈ lpX) :
    kktRes A b c z ^ 2 = eucl n m (vvec A b c z)^2 +
      max (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ) 0 ^ 2 := by
  have hz0 (i : Fin n) : max (-z.1 i) 0 = 0 := max_eq_right (neg_nonpos.mpr (hz i))
  simp only [kktRes,EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type,
    hvec,Kz,eucl_sq,vvec]
  simp only [zero_sub,hz0,zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero,zero_add,sub_neg_eq_add,Finset.univ_unique,
    Finset.sum_singleton,PiLp.sub_apply]
  have hsum :
      (∑ j, max (-b j+(Matrix.toEuclideanLin A z.1) j) 0 ^ 2) +
        (∑ j, max (b j-(Matrix.toEuclideanLin A z.1) j) 0 ^ 2) =
      ∑ j, (b j-(Matrix.toEuclideanLin A z.1) j)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have he : -b j+(Matrix.toEuclideanLin A z.1) j =
        -(b j-(Matrix.toEuclideanLin A z.1) j) := by ring
    rw [he,add_comm]
    exact pos_parts_sq _
  simp only [neg_add_eq_sub,neg_sub] at hsum ⊢
  linear_combination hsum
end LPSharpProof
theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (hsol : (Zstar (lpL A b c) lpX Set.univ).Nonempty)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) (z : PDSpace n m)
    (hz : z ∈ Wball lpX Set.univ R 0) :
    ((kktRes A b c z : ℝ) : EReal) ≤
      rho (lpL A b c) lpX Set.univ r z * ((Real.sqrt (1 + R ^ 2) : ℝ) : EReal) := by
  have h1 := LPSharpProof.eq22 A b c z hz.1 r hr
  have h2 := LPSharpProof.eq25 A b c R hR z hz r hr hrR
  have hn : 0 ≤ eucl n m (vvec A b c z) := apply_nonneg _ _
  have hk : 0 ≤ kktRes A b c z := norm_nonneg _
  have hs : 0 < Real.sqrt (1+R^2) := Real.sqrt_pos.2 (by positivity)
  have hsq := LPSharpProof.kkt_sq A b c z hz.1.1
  generalize he : rho (lpL A b c) lpX Set.univ r z = e at h1 h2 ⊢
  cases e using EReal.rec with
  | bot => exact False.elim ((not_le_of_gt (EReal.bot_lt_coe _)) h1)
  | coe q =>
    have h1' : eucl n m (vvec A b c z) ≤ q := EReal.coe_le_coe_iff.1 h1
    have h2' : max (⟪c,z.1⟫_ℝ-⟪b,z.2⟫_ℝ) 0 / R ≤ q := EReal.coe_le_coe_iff.1 h2
    have hq : 0 ≤ q := hn.trans h1'
    have hg : max (⟪c,z.1⟫_ℝ-⟪b,z.2⟫_ℝ) 0 ≤ q*R := (div_le_iff₀ hR).1 h2'
    have hv2 := (sq_le_sq₀ hn hq).2 h1'
    have hg2 := (sq_le_sq₀ (le_max_right (⟪c,z.1⟫_ℝ-⟪b,z.2⟫_ℝ) 0)
      (mul_nonneg hq hR.le)).2 hg
    rw [← EReal.coe_mul,EReal.coe_le_coe_iff]
    apply (sq_le_sq₀ hk (mul_nonneg hq hs.le)).1
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith
  | top =>
    rw [EReal.top_mul_of_pos (EReal.coe_pos.2 hs)]
    exact le_top
