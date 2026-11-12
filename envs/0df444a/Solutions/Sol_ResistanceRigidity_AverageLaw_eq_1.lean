-- Prove2me | solution 1 for ResistanceRigidity.AverageLaw.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:22:52.444228+00:00
-- url     : https://prove2.me/submissions/e8457fac-4193-462b-b000-b1f824c2f598

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Matrices

section
set_option autoImplicit false

open Matrix

namespace ResistanceRigidity.Dev.Found

open ResistanceRigidity.AverageLaw IncrementalER

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lap_eq (c : V → V → ℝ) (hc : IsGraph c) :
    lap c = Matrix.diagonal (fun u => ∑ w, c u w) - Matrix.of c := by
  ext u v
  by_cases h : u = v
  · subst h
    simp only [lap, if_true, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.of_apply, hc.2 u,
      sub_zero]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u), hc.2 u, add_zero]
  · simp [lap, h, Matrix.diagonal_apply_ne _ h]

/-- `(L x)_u = ∑_v c u v (x u - x v)`. -/
theorem lap_mulVec_apply (c : V → V → ℝ) (hc : IsGraph c) (x : V → ℝ) (u : V) :
    (lap c *ᵥ x) u = ∑ v, c u v * (x u - x v) := by
  rw [lap_eq c hc, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  simp only [Pi.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

/-- `L 1 = 0`. -/
theorem lap_mulVec_one (c : V → V → ℝ) (hc : IsGraph c) :
    lap c *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext u
  rw [lap_mulVec_apply c hc]
  simp

theorem lap_symm (c : V → V → ℝ) (hc : IsGraph c) : (lap c)ᵀ = lap c := by
  rw [lap_eq c hc]
  ext u v
  by_cases h : u = v
  · subst h; rfl
  · simp [Matrix.transpose_apply, Matrix.diagonal_apply, h, Ne.symm h, hc.1.2 u v]

theorem lap_quad (c : V → V → ℝ) (hc : IsGraph c) (f : V → ℝ) :
    2 * (f ⬝ᵥ (lap c *ᵥ f)) = ∑ u, ∑ v, c u v * (f u - f v) ^ 2 := by
  have h1 : f ⬝ᵥ (lap c *ᵥ f) = ∑ u, ∑ v, c u v * (f u * (f u - f v)) := by
    simp only [dotProduct, lap_mulVec_apply c hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∑ u, ∑ v, c u v * (f u * (f u - f v))
      = ∑ u, ∑ v, c u v * (f v * (f v - f u)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hc.1.2 v u]
  have : 2 * (f ⬝ᵥ (lap c *ᵥ f)) = (∑ u, ∑ v, c u v * (f u * (f u - f v)))
      + ∑ u, ∑ v, c u v * (f v * (f v - f u)) := by
    rw [h1, ← h2]; ring
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => by ring

theorem lap_const_of_quad (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (f : V → ℝ)
    (hf : f ⬝ᵥ (lap c *ᵥ f) = 0) (u v : V) : f u = f v := by
  have hq := lap_quad c hc f
  rw [hf] at hq
  simp only [mul_zero] at hq
  have hnn : ∀ a b, 0 ≤ c a b * (f a - f b) ^ 2 := fun a b =>
    mul_nonneg (hc.1.1 a b) (sq_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg fun b _ => hnn a b)).1 hq.symm
  have hedge : ∀ a b, 0 < c a b → f a = f b := by
    intro a b hab
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn a b)).1 (h0 a (Finset.mem_univ a))
      b (Finset.mem_univ b)
    have : (f a - f b) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hab.ne'
      · exact h
    linarith [pow_eq_zero_iff (two_ne_zero) |>.1 this]
  obtain ⟨w⟩ := hconn.preconnected u v
  induction w with
  | nil => rfl
  | @cons a b _ h _ ih =>
    have : f a = f b := by
      simp only [adj, SimpleGraph.fromRel_adj] at h
      rcases h.2 with h | h
      · exact hedge a b h
      · exact (hedge b a h).symm
    rw [this, ih]

theorem lap_const (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (f : V → ℝ)
    (hf : lap c *ᵥ f = 0) (u v : V) : f u = f v :=
  lap_const_of_quad c hc hconn f (by rw [hf, dotProduct_zero]) u v

theorem lap_vecMul (c : V → V → ℝ) (hc : IsGraph c) (w : V → ℝ) :
    w ᵥ* lap c = lap c *ᵥ w := by
  conv_lhs => rw [← lap_symm c hc]
  rw [Matrix.vecMul_transpose]

theorem pinv_spec (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (y : V → ℝ) :
    (∑ v, (pinvLap c *ᵥ y) v = 0) ∧
      lap c *ᵥ (pinvLap c *ᵥ y) = projOnes V *ᵥ y := by
  classical
  set L := lap c with hL
  set T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V := Matrix.toEuclideanLin L with hT
  set y' : EuclideanSpace ℝ V := WithLp.toLp 2 y with hy'
  set K := (LinearMap.ker T)ᗮ with hK
  set x := pinvLap c *ᵥ y with hxdef
  set R := LinearMap.range (T ∘ₗ K.subtype) with hR
  have hx : (WithLp.toLp 2 x : EuclideanSpace ℝ V) = HarmonicGames.Decomposition.pinv T y' := by
    show Matrix.toEuclideanLin (pinvMat L) y' = _
    unfold pinvMat
    rw [LinearEquiv.apply_symm_apply]
  obtain ⟨a, hax, hTa⟩ : ∃ a : K, (a : EuclideanSpace ℝ V) = WithLp.toLp 2 x ∧
      T (a : EuclideanSpace ℝ V) = ((R.orthogonalProjectionOnto y' : R) : EuclideanSpace ℝ V) := by
    refine ⟨(LinearEquiv.ofInjective _
      (HarmonicGames.Decomposition.pinv_restrict_injective T)).symm
        (R.orthogonalProjectionOnto y'), ?_, ?_⟩
    · rw [hx]; rfl
    · have := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective _
        (HarmonicGames.Decomposition.pinv_restrict_injective T))
        (R.orthogonalProjectionOnto y')
      exact congrArg Subtype.val this
  -- (a) sum zero
  have hsum : ∑ v, x v = 0 := by
    have hmem : WithLp.toLp 2 x ∈ K := by rw [← hax]; exact a.2
    have h1 : (WithLp.toLp 2 (fun _ : V => (1 : ℝ)) : EuclideanSpace ℝ V) ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      have h0 : L *ᵥ (fun _ : V => (1 : ℝ)) = 0 := lap_mulVec_one c hc
      change WithLp.toLp 2 (L *ᵥ (fun _ : V => (1 : ℝ))) = 0
      rw [h0]; rfl
    have := (Submodule.mem_orthogonal (LinearMap.ker T) _).1 hmem _ h1
    rw [EuclideanSpace.inner_toLp_toLp] at this
    simpa [dotProduct] using this
  set w : V → ℝ := y - L *ᵥ x with hw
  have hA : ∀ z : V → ℝ, (L *ᵥ z) ⬝ᵥ w = 0 := by
    intro z
    have htop : LinearMap.ker T ⊔ K = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have hz : (WithLp.toLp 2 z : EuclideanSpace ℝ V) ∈ LinearMap.ker T ⊔ K := by
      rw [htop]; trivial
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.1 hz
    have hTz : T (WithLp.toLp 2 z) = T b := by
      rw [← hkb, map_add, LinearMap.mem_ker.1 hk, zero_add]
    have hmem : T b ∈ R := ⟨⟨b, hb⟩, rfl⟩
    have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := R) ⟨T b, hmem⟩ y'
    rw [Submodule.coe_inner] at h
    have hTax : T (a : EuclideanSpace ℝ V) = WithLp.toLp 2 (L *ᵥ x) := by rw [hax]; rfl
    have hww : (WithLp.toLp 2 w : EuclideanSpace ℝ V) = y' - T a := by
      rw [hTax]; rfl
    have h2 : inner ℝ (WithLp.toLp 2 w : EuclideanSpace ℝ V) (T (WithLp.toLp 2 z)) = 0 := by
      rw [hTz, hww, inner_sub_left, hTa]
      exact sub_eq_zero.2 h.symm
    have h3 : T (WithLp.toLp 2 z) = WithLp.toLp 2 (L *ᵥ z) := rfl
    rw [h3, EuclideanSpace.inner_toLp_toLp] at h2
    simpa using h2
  have hLw : L *ᵥ w = 0 := by
    have := hA (L *ᵥ w)
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, lap_vecMul c hc] at this
    exact dotProduct_self_eq_zero.1 this
  have hconst : ∀ u v, w u = w v := lap_const c hc hconn w hLw
  have hLx : ∑ u, (L *ᵥ x) u = 0 := by
    have h := Matrix.dotProduct_mulVec (fun _ : V => (1 : ℝ)) L x
    rw [lap_vecMul c hc, lap_mulVec_one c hc] at h
    simpa [dotProduct] using h
  have : Nonempty V := hconn.nonempty
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    exact_mod_cast this.ne'
  refine ⟨hsum, ?_⟩
  ext v
  have hsw : ∑ u, w u = ∑ u, y u := by
    simp only [hw, Pi.sub_apply, Finset.sum_sub_distrib, hLx, sub_zero]
  have hwv : w v = (Fintype.card V : ℝ)⁻¹ * ∑ u, y u := by
    have : ∑ u, w u = (Fintype.card V : ℝ) * w v := by
      rw [Finset.sum_congr rfl (fun u _ => hconst u v)]; simp
    rw [← hsw, this]; field_simp
  have : (L *ᵥ x) v = y v - w v := by simp [hw]
  rw [this, hwv]
  rw [projOnes, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, dotProduct]

theorem proj_apply (y : V → ℝ) (v : V) :
    (projOnes V *ᵥ y) v = y v - (Fintype.card V : ℝ)⁻¹ * ∑ u, y u := by
  rw [projOnes, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, dotProduct]

theorem pinv_dot_symm (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (y1 y2 : V → ℝ) :
    (pinvLap c *ᵥ y1) ⬝ᵥ y2 = y1 ⬝ᵥ (pinvLap c *ᵥ y2) := by
  obtain ⟨s1, l1⟩ := pinv_spec c hc hconn y1
  obtain ⟨s2, l2⟩ := pinv_spec c hc hconn y2
  set x1 := pinvLap c *ᵥ y1
  set x2 := pinvLap c *ᵥ y2
  have e1 : lap c *ᵥ x1 = y1 - ((Fintype.card V : ℝ)⁻¹ * ∑ u, y1 u) • (fun _ => (1 : ℝ)) := by
    funext v; rw [l1, Pi.sub_apply, proj_apply]; simp
  have e2 : y2 = lap c *ᵥ x2 + ((Fintype.card V : ℝ)⁻¹ * ∑ u, y2 u) • (fun _ => (1 : ℝ)) := by
    funext v; rw [l2, Pi.add_apply, proj_apply]; simp
  have d1 : x1 ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by simpa [dotProduct] using s1
  have d2 : x2 ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by simpa [dotProduct] using s2
  have a1 : x1 ⬝ᵥ y2 = x1 ⬝ᵥ (lap c *ᵥ x2) := by
    conv_lhs => rw [e2]
    rw [dotProduct_add, dotProduct_smul, d1]; simp
  have a2 : x1 ⬝ᵥ (lap c *ᵥ x2) = (lap c *ᵥ x1) ⬝ᵥ x2 := by
    rw [Matrix.dotProduct_mulVec, ← lap_vecMul c hc, dotProduct_comm]
  have a3 : (lap c *ᵥ x1) ⬝ᵥ x2 = y1 ⬝ᵥ x2 := by
    rw [e1, sub_dotProduct, smul_dotProduct, dotProduct_comm (fun _ => (1 : ℝ)) x2, d2]; simp
  rw [a1, a2, a3, dotProduct_comm]

theorem pinv_symm (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) :
    (pinvLap c)ᵀ = pinvLap c := by
  ext u v
  have := pinv_dot_symm c hc hconn (Pi.single u 1) (Pi.single v 1)
  simpa [Matrix.mulVec_single_one, single_dotProduct] using this

theorem reff_eq (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (u v : V) :
    reff c u v = pinvLap c u u + pinvLap c v v - 2 * pinvLap c u v := by
  have hs : pinvLap c v u = pinvLap c u v := by
    have := congrFun (congrFun (pinv_symm c hc hconn) u) v
    simpa using this
  have : reff c u v = (Pi.single u 1 - Pi.single v 1 : V → ℝ) ⬝ᵥ
      (pinvLap c *ᵥ (Pi.single u 1 - Pi.single v 1 : V → ℝ)) := rfl
  rw [this, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [Matrix.mulVec_single_one, dotProduct_single_one, single_dotProduct]
  simp [hs]
  ring

theorem resMat_eq (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) :
    resMat c = vecMulVec (diagPinv c) (fun _ => (1 : ℝ)) + vecMulVec (fun _ => (1 : ℝ)) (diagPinv c)
        - (2 : ℝ) • pinvLap c := by
  ext u v
  simp [resMat, vecMulVec, diagPinv, reff_eq c hc hconn]

end ResistanceRigidity.Dev.Found
end

section
set_option autoImplicit false

open Matrix

namespace ResistanceRigidity.AverageLaw

theorem chk_eq_1 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 2 ≤ Fintype.card V) :
    resMat c = vecMulVec (diagPinv c) (fun _ => (1 : ℝ)) + vecMulVec (fun _ => (1 : ℝ)) (diagPinv c)
        - (2 : ℝ) • pinvLap c ∧
      ∀ x : V → ℝ, ∑ v, x v = 0 →
        x ⬝ᵥ (pinvLap c *ᵥ x) = -(1 / 2 : ℝ) * (x ⬝ᵥ (resMat c *ᵥ x)) := by
  have hR := ResistanceRigidity.Dev.Found.resMat_eq c hc hconn
  refine ⟨hR, fun x hx => ?_⟩
  rw [hR]
  have h1 : (fun _ : V => (1:ℝ)) ⬝ᵥ x = 0 := by simpa [dotProduct] using hx
  have h2 : x ⬝ᵥ (fun _ : V => (1:ℝ)) = 0 := by simpa [dotProduct] using hx
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_smul, Matrix.vecMulVec_mulVec, dotProduct_smul, h1, h2]
  simp [smul_eq_mul]

end ResistanceRigidity.AverageLaw
end

theorem solution : type_of% @ResistanceRigidity.AverageLaw.chk_eq_1 := @ResistanceRigidity.AverageLaw.chk_eq_1
