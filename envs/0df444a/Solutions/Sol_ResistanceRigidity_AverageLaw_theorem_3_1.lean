-- Prove2me | solution 1 for ResistanceRigidity.AverageLaw.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:08.359384+00:00
-- url     : https://prove2.me/submissions/7cb6eb32-f434-48a4-9e29-b093b47855b1

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Matrices
import Definitions.Def_ResistanceRigidity_AverageLaw_Local
import Definitions.Def_ResistanceRigidity_AverageLaw_Spread
import Theorems.Thm_ResistanceRigidity_AverageLaw_eq_4
import Definitions.Def_ResistanceRigidity_AverageLaw_Classes
import Theorems.Thm_ResistanceRigidity_AverageLaw_eq_8
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

theorem lap_mul_pinv (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) :
    lap c * pinvLap c = projOnes V := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [← Matrix.mulVec_mulVec]
  exact (pinv_spec c hc hconn y).2

theorem pinv_symm (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) :
    (pinvLap c)ᵀ = pinvLap c := by
  ext u v
  have := pinv_dot_symm c hc hconn (Pi.single u 1) (Pi.single v 1)
  simpa [Matrix.mulVec_single_one, single_dotProduct] using this

theorem pinv_mulVec_one (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) :
    pinvLap c *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  obtain ⟨s, l⟩ := pinv_spec c hc hconn (fun _ => (1 : ℝ))
  set x := pinvLap c *ᵥ (fun _ => (1 : ℝ))
  have h0 : lap c *ᵥ x = 0 := by
    rw [l]; funext v
    have hN : (Fintype.card V : ℝ) ≠ 0 := by
      have : Nonempty V := hconn.nonempty
      exact_mod_cast Fintype.card_pos.ne'
    rw [proj_apply]; simp [hN]
  have hc' := lap_const c hc hconn x h0
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    have : Nonempty V := hconn.nonempty
    exact_mod_cast Fintype.card_pos.ne'
  funext v
  have : ∑ u, x u = (Fintype.card V : ℝ) * x v := by
    rw [Finset.sum_congr rfl (fun u _ => hc' u v)]; simp
  rw [s] at this
  simpa [hN] using this.symm

theorem reff_self (c : V → V → ℝ) (u : V) : reff c u u = 0 := by
  simp [reff, energy]

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

theorem reff_symm (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (u v : V) :
    reff c u v = reff c v u := by
  have hs : pinvLap c v u = pinvLap c u v := by
    have := congrFun (congrFun (pinv_symm c hc hconn) u) v
    simpa using this
  rw [reff_eq c hc hconn, reff_eq c hc hconn, hs]; ring

theorem reff_pos (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) {u v : V} (h : u ≠ v) :
    0 < reff c u v := by
  set d : V → ℝ := Pi.single u 1 - Pi.single v 1 with hd
  have hre : reff c u v = d ⬝ᵥ (pinvLap c *ᵥ d) := rfl
  obtain ⟨s, l⟩ := pinv_spec c hc hconn d
  set x := pinvLap c *ᵥ d
  have hsd : ∑ w, d w = 0 := by
    simp [hd, Pi.single_apply, Finset.sum_sub_distrib]
  have hLx : lap c *ᵥ x = d := by
    rw [l]; funext w; rw [proj_apply, hsd]; simp
  have hq : 0 ≤ x ⬝ᵥ (lap c *ᵥ x) := by
    have := lap_quad c hc x
    have h0 : 0 ≤ ∑ a, ∑ b, c a b * (x a - x b) ^ 2 :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
        mul_nonneg (hc.1.1 a b) (sq_nonneg _)
    linarith
  rw [hre, ← hLx, dotProduct_comm]
  refine lt_of_le_of_ne hq fun h0 => ?_
  have hc' := lap_const_of_quad c hc hconn x h0.symm
  have : lap c *ᵥ x = 0 := by
    funext w; rw [lap_mulVec_apply c hc, Pi.zero_apply]
    exact Finset.sum_eq_zero fun b _ => by rw [hc' w b]; ring
  rw [hLx] at this
  have := congrFun this u
  simp [hd, Pi.single_apply, h] at this

theorem capDeg_pos (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 2 ≤ Fintype.card V) (u : V) : 0 < capDeg c u := by
  obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card (by omega) u
  obtain ⟨w⟩ := hconn.preconnected u v
  cases w with
  | nil => exact absurd rfl hv
  | @cons _ b _ hadj _ =>
    have hb : 0 < c u b := by
      simp only [adj, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact h
      · rwa [hc.1.2 u b]
    exact lt_of_lt_of_le hb (Finset.single_le_sum (f := fun w => c u w)
      (fun w _ => hc.1.1 u w) (Finset.mem_univ b))

end ResistanceRigidity.Dev.Found
end

section
set_option autoImplicit false

open Matrix

namespace ResistanceRigidity.Dev.Eq7

open ResistanceRigidity.AverageLaw IncrementalER

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem minmax (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) :
    0 < minRes c ∧ (∀ v x, v ≠ x → minRes c ≤ reff c v x ∧ reff c v x ≤ maxRes c) := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
  have hne : (Finset.univ.offDiag : Finset (V × V)).Nonempty := ⟨(a, b), by simp [hab]⟩
  have hmin : minRes c = Finset.univ.offDiag.inf' hne (fun p => reff c p.1 p.2) := by
    simp [minRes, hne]
  have hmax : maxRes c = Finset.univ.offDiag.sup' hne (fun p => reff c p.1 p.2) := by
    simp [maxRes, hne]
  refine ⟨?_, fun v x hvx => ⟨?_, ?_⟩⟩
  · obtain ⟨p, hp, hp2⟩ := Finset.exists_mem_eq_inf' hne (fun p : V × V => reff c p.1 p.2)
    rw [hmin, hp2]
    have : p.1 ≠ p.2 := by simpa using hp
    exact ResistanceRigidity.Dev.Found.reff_pos c hc hconn this
  · rw [hmin]
    exact Finset.inf'_le (fun p : V × V => reff c p.1 p.2) (by simp [hvx] : (v, x) ∈ Finset.univ.offDiag)
  · rw [hmax]
    exact Finset.le_sup' (fun p : V × V => reff c p.1 p.2) (by simp [hvx] : (v, x) ∈ Finset.univ.offDiag)

theorem main (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (hε : spread c < 1) (u : V) :
    levDeg c u ≤
        1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (deg c u : ℝ))) ∧
      1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (deg c u : ℝ))) =
        2 * (deg c u : ℝ) / ((1 - spread c) * (deg c u : ℝ) + 1 + spread c) := by
  have hN2 : 2 ≤ Fintype.card V := by omega
  have hδ := ResistanceRigidity.Dev.Found.capDeg_pos c hc hconn hN2 u
  obtain ⟨hm, hmM⟩ := minmax c hc hconn hN
  set m := minRes c with hmdef
  set M := maxRes c with hMdef
  set ε := spread c with hεdef
  have hεeq : ε = M / m - 1 := rfl
  have hMm : M = (1 + ε) * m := by rw [hεeq]; field_simp; ring
  have hsym : ∀ x y, c x y = c y x := hc.1.2
  have hnn : ∀ x y, 0 ≤ c x y := hc.1.1
  have hdiag : c u u = 0 := hc.2 u
  obtain ⟨h4a, h4b⟩ := ResistanceRigidity.AverageLaw.eq_4 c hc hconn hN2 u
  set δ := capDeg c u with hδdef
  set p : V → ℝ := fun v => nbrProb c u v with hp
  have hp0 : ∀ v, 0 ≤ p v := fun v => div_nonneg (hnn _ _) hδ.le
  have hpu : p u = 0 := by simp [hp, nbrProb, hdiag]
  have hsump : ∑ v, p v = 1 := by
    simp only [hp, nbrProb, ← Finset.sum_div]
    have : ∑ v, c u v = δ := rfl
    rw [this]; exact div_self hδ.ne'
  set S : Finset V := Finset.univ.filter fun w => w ≠ u ∧ 0 < c u w with hS
  have hk : (deg c u : ℝ) = (S.card : ℝ) := rfl
  have hpS : ∀ v, v ∉ S → p v = 0 := by
    intro v hv
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hv
    by_cases h : v = u
    · rw [h]; exact hpu
    · have := le_antisymm (hv h) (hnn _ _)
      simp [hp, nbrProb, this]
  have hSsum : ∑ v ∈ S, p v = 1 := by
    rw [← hsump]
    exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hpS v hv)
  have hkpos : (1 : ℝ) ≤ S.card := by
    have : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hSsum; simp at hSsum
    exact_mod_cast this.card_pos
  have hSq : ∑ v, p v ^ 2 = ∑ v ∈ S, p v ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ S) (fun v _ hv => by rw [hpS v hv]; ring)).symm
  have hCS : 1 ≤ (S.card : ℝ) * ∑ v, p v ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := p)
    rw [hSsum] at this
    rw [hSq]; simpa using this
  -- a ≥ m
  have ha : m ≤ avgRes c u := by
    have : ∑ v, p v * m ≤ ∑ v, p v * reff c u v := by
      refine Finset.sum_le_sum fun v _ => ?_
      by_cases h : v = u
      · rw [h, hpu]; simp
      · exact mul_le_mul_of_nonneg_left (hmM u v (Ne.symm h)).1 (hp0 v)
    rw [← Finset.sum_mul, hsump, one_mul] at this
    exact this
  have hMnn : 0 ≤ M := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
    have := hmM a b hab
    linarith [this.1, this.2]
  have hsymR : ∀ v x, reff c v x = reff c x v := ResistanceRigidity.Dev.Found.reff_symm c hc hconn
  have ht : pairRes c u ≤ M * (1 - ∑ v, p v ^ 2) := by
    have h1 : pairRes c u ≤ ∑ v, ∑ x, (M * (p v * p x) - if v = x then M * (p v * p v) else 0) := by
      refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun x _ => ?_
      by_cases h : v = x
      · subst h; simp [ResistanceRigidity.Dev.Found.reff_self]
      · simp only [h, if_false, sub_zero]
        have := hmM v x h
        have h0 : 0 ≤ p v * p x := mul_nonneg (hp0 v) (hp0 x)
        calc p v * p x * reff c v x = (p v * p x) * reff c v x := rfl
          _ ≤ (p v * p x) * M := mul_le_mul_of_nonneg_left this.2 h0
          _ = M * (p v * p x) := by ring
    refine h1.trans (le_of_eq ?_)
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ v, ∑ x, M * (p v * p x) = M := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hsump]; ring
    have e2 : ∑ v, M * (p v * p v) = M * ∑ v, p v ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [e1, e2]; ring
  have hk0 : (0 : ℝ) < S.card := by linarith
  have hinv : 1 / (S.card : ℝ) ≤ ∑ v, p v ^ 2 := by
    rw [div_le_iff₀ hk0]; linarith
  have ht2 : pairRes c u ≤ M * (1 - 1 / (S.card : ℝ)) := by
    have : M * (1 - ∑ v, p v ^ 2) ≤ M * (1 - 1 / (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hMnn
    linarith
  rw [hk]
  set k : ℝ := (S.card : ℝ) with hkdef
  have hk1 : 0 ≤ 1 - 1 / k := by
    rw [sub_nonneg, div_le_one hk0]; exact hkpos
  have hk2 : 0 < 1 / k := one_div_pos.mpr hk0
  have hB : 0 < 1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k) := by
    have : (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k) < 1 := by
      have h1 : 1 + ε < 2 := by linarith
      have h2 : (1 + ε) * (1 - 1 / k) < 2 := by
        nlinarith [mul_nonneg (show 0 ≤ 2 - (1 + ε) by linarith) hk1]
      linarith
    linarith
  refine ⟨?_, ?_⟩
  · rw [h4a, le_div_iff₀ hB]
    have hone : δ * (avgRes c u - pairRes c u / 2) = 1 := by rw [← h4b]; field_simp
    have key : avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k)) ≤ avgRes c u - pairRes c u / 2 := by
      have h1 : M ≤ avgRes c u * (1 + ε) := by rw [hMm]; nlinarith
      have h2 : M * (1 - 1 / k) ≤ avgRes c u * (1 + ε) * (1 - 1 / k) :=
        mul_le_mul_of_nonneg_right h1 hk1
      nlinarith
    calc δ * avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k))
        = δ * (avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k))) := by ring
      _ ≤ δ * (avgRes c u - pairRes c u / 2) := mul_le_mul_of_nonneg_left key hδ.le
      _ = 1 := hone
  · have hD : 0 < (1 - ε) * k + 1 + ε := by nlinarith
    rw [div_eq_div_iff hB.ne' hD.ne']
    field_simp
    ring

end ResistanceRigidity.Dev.Eq7

namespace ResistanceRigidity.AverageLaw

end ResistanceRigidity.AverageLaw
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The right side of (6). -/
noncomputable def rhs (c : V → V → ℝ) : ℝ :=
  ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1))

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartA
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem levDeg_eq (c : V → V → ℝ) (u : V) :
    levDeg c u = ∑ w, c u w * reff c u w := by
  unfold levDeg
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u), ResistanceRigidity.Dev.Found.reff_self]
  simp

theorem sum_rule (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 2 ≤ Fintype.card V) (u y : V) (huy : u ≠ y) :
    ∑ x, c u x * (reff c u y + reff c u x - reff c x y) = 2 := by
  obtain ⟨h1, h2, -⟩ := ResistanceRigidity.AverageLaw.eq_8 c hc hconn hN
  have hNpos : (Fintype.card V : ℝ) ≠ 0 := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this.ne'
  have e1 := congrFun (congrFun h1 u) y
  have e2 := h2 u
  have hL : (lap c * resMat c) u y = capDeg c u * reff c u y - ∑ x, c u x * reff c x y := by
    rw [ResistanceRigidity.Dev.Found.lap_eq c hc]
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply, resMat, sub_mul,
      Finset.sum_sub_distrib, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rfl
  rw [hL] at e1
  simp [vecMulVec, projOnes, Matrix.one_apply, huy, Matrix.sub_apply] at e1
  have e3 := levDeg_eq c u
  have hexp : ∑ x, c u x * (reff c u y + reff c u x - reff c x y)
      = capDeg c u * reff c u y + levDeg c u - ∑ x, c u x * reff c x y := by
    rw [e3]
    unfold capDeg MarkovMixing.vertexConductance
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hexp]
  field_simp at e1 e2
  have h0 : (Fintype.card V : ℝ) * (capDeg c u * reff c u y + levDeg c u
      - ∑ x, c u x * reff c x y - 2) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hNpos
  · linarith

end ResistanceRigidity.Dev.Thm31.PartA
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
/-! ### Stubs (each to be proved by a Part) -/

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartA
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem sum_levDeg (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 2 ≤ Fintype.card V) :
    ∑ u, levDeg c u = 2 * ((Fintype.card V : ℝ) - 1) := by
  obtain ⟨-, h2, -⟩ := ResistanceRigidity.AverageLaw.eq_8 c hc hconn hN
  have hNpos : (Fintype.card V : ℝ) ≠ 0 := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this.ne'
  have hz : ∑ u, (lap c *ᵥ diagPinv c) u = 0 := by
    simp only [ResistanceRigidity.Dev.Found.lap_mulVec_apply c hc, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hc.1.2 u v]
  have : ∀ u, levDeg c u = 2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)
      - (lap c *ᵥ diagPinv c) u := fun u => by linarith [h2 u]
  rw [Finset.sum_congr rfl fun u _ => this u, Finset.sum_sub_distrib, hz]
  simp
  field_simp

end ResistanceRigidity.Dev.Thm31.PartA
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartA
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem edge_ge (c : V → V → ℝ) (hconn : Connected c) :
    Fintype.card V ≤ edgeCount c + 1 := by
  classical
  have := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn
  simp only [Nat.card_eq_fintype_card] at this
  unfold edgeCount
  convert this using 2
  simp [SimpleGraph.edgeFinset]

theorem deg_eq (c : V → V → ℝ) (hc : IsGraph c) (u : V) :
    deg c u = (by classical exact (adj c).degree u) := by
  classical
  unfold deg
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, adj, SimpleGraph.fromRel_adj, hc.1.2 w u,
    or_self]
  tauto

theorem sum_deg (c : V → V → ℝ) (hc : IsGraph c) :
    ∑ u, (deg c u : ℝ) = 2 * (edgeCount c : ℝ) := by
  classical
  have := (adj c).sum_degrees_eq_twice_card_edges
  have h2 : ∑ u, deg c u = 2 * edgeCount c := by
    unfold edgeCount
    rw [← this]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [deg_eq c hc]
  exact_mod_cast h2

theorem basic (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) : 0 ≤ spread c ∧ rhs c ≤ 1 := by
  obtain ⟨hm, hmM⟩ := ResistanceRigidity.Dev.Eq7.minmax c hc hconn hN
  constructor
  · obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
    have := hmM a b hab
    unfold spread
    rw [sub_nonneg, one_le_div hm]
    linarith [this.1, this.2]
  · have hE := edge_ge c hconn
    have hE' : (Fintype.card V : ℝ) ≤ edgeCount c + 1 := by exact_mod_cast hE
    have hN' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    set N : ℝ := (Fintype.card V : ℝ)
    have hd : avgDeg c = 2 * (edgeCount c : ℝ) / N := rfl
    have hd1 : 1 < avgDeg c := by
      rw [hd, lt_div_iff₀ (by linarith)]; linarith
    have hdN : avgDeg c * N = 2 * edgeCount c := by rw [hd]; field_simp
    unfold rhs
    rw [div_le_one (by apply mul_pos <;> linarith)]
    nlinarith

end ResistanceRigidity.Dev.Thm31.PartA
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias basic := ResistanceRigidity.Dev.Thm31.PartA.basic

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartA
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1600000 in
theorem local_bound (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (hε : spread c ≤ 1) (u : V) :
    levDeg c u ≤ 1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (deg c u : ℝ))) ∧
      (levDeg c u = 1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (deg c u : ℝ))) →
        2 ≤ deg c u →
        (∀ v, 0 < c u v → reff c u v = minRes c) ∧
        (∀ v x, 0 < c u v → 0 < c u x → v ≠ x → reff c v x = maxRes c) ∧
        (∀ v, 0 < c u v → c u v = capDeg c u / (deg c u : ℝ))) := by
  have hN2 : 2 ≤ Fintype.card V := by omega
  have hδ := ResistanceRigidity.Dev.Found.capDeg_pos c hc hconn hN2 u
  obtain ⟨hm, hmM⟩ := ResistanceRigidity.Dev.Eq7.minmax c hc hconn hN
  have hε0 : 0 ≤ spread c := (basic c hc hconn hN).1
  set m := minRes c with hmdef
  set M := maxRes c with hMdef
  set ε := spread c with hεdef
  have hεeq : ε = M / m - 1 := rfl
  have hMm : M = (1 + ε) * m := by rw [hεeq]; field_simp; ring
  have hnn : ∀ x y, 0 ≤ c x y := hc.1.1
  have hdiag : c u u = 0 := hc.2 u
  obtain ⟨h4a, h4b⟩ := ResistanceRigidity.AverageLaw.eq_4 c hc hconn hN2 u
  set δ := capDeg c u with hδdef
  set p : V → ℝ := fun v => nbrProb c u v with hp
  have hp0 : ∀ v, 0 ≤ p v := fun v => div_nonneg (hnn _ _) hδ.le
  have hpu : p u = 0 := by simp [hp, nbrProb, hdiag]
  have hsump : ∑ v, p v = 1 := by
    simp only [hp, nbrProb, ← Finset.sum_div]
    have : ∑ v, c u v = δ := rfl
    rw [this]; exact div_self hδ.ne'
  set S : Finset V := Finset.univ.filter fun w => w ≠ u ∧ 0 < c u w with hS
  have hk : (deg c u : ℝ) = (S.card : ℝ) := rfl
  have hpS : ∀ v, v ∉ S → p v = 0 := by
    intro v hv
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hv
    by_cases h : v = u
    · rw [h]; exact hpu
    · have := le_antisymm (hv h) (hnn _ _)
      simp [hp, nbrProb, this]
  have hSsum : ∑ v ∈ S, p v = 1 := by
    rw [← hsump]
    exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hpS v hv)
  have hkpos : (1 : ℝ) ≤ S.card := by
    have : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hSsum; simp at hSsum
    exact_mod_cast this.card_pos
  have hSq : ∑ v, p v ^ 2 = ∑ v ∈ S, p v ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ S) (fun v _ hv => by rw [hpS v hv]; ring)).symm
  have hCS : 1 ≤ (S.card : ℝ) * ∑ v, p v ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := p)
    rw [hSsum] at this
    rw [hSq]; simpa using this
  have ha : m ≤ avgRes c u := by
    have : ∑ v, p v * m ≤ ∑ v, p v * reff c u v := by
      refine Finset.sum_le_sum fun v _ => ?_
      by_cases h : v = u
      · rw [h, hpu]; simp
      · exact mul_le_mul_of_nonneg_left (hmM u v (Ne.symm h)).1 (hp0 v)
    rw [← Finset.sum_mul, hsump, one_mul] at this
    exact this
  have hMnn : 0 ≤ M := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
    have := hmM a b hab
    linarith [this.1, this.2]
  have hterm : ∀ v x, p v * p x * reff c v x ≤
      M * (p v * p x) - (if v = x then M * (p v * p v) else 0) := by
    intro v x
    by_cases h : v = x
    · subst h; simp [ResistanceRigidity.Dev.Found.reff_self]
    · simp only [h, if_false, sub_zero]
      have := hmM v x h
      have h0 : 0 ≤ p v * p x := mul_nonneg (hp0 v) (hp0 x)
      calc p v * p x * reff c v x = (p v * p x) * reff c v x := rfl
        _ ≤ (p v * p x) * M := mul_le_mul_of_nonneg_left this.2 h0
        _ = M * (p v * p x) := by ring
  have hsumT : ∑ v, ∑ x, (M * (p v * p x) - if v = x then M * (p v * p v) else 0)
      = M * (1 - ∑ v, p v ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ v, ∑ x, M * (p v * p x) = M := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hsump]; ring
    have e2 : ∑ v, M * (p v * p v) = M * ∑ v, p v ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [e1, e2]; ring
  have ht : pairRes c u ≤ M * (1 - ∑ v, p v ^ 2) := by
    rw [← hsumT]
    exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun x _ => hterm v x
  have hk0 : (0 : ℝ) < S.card := by linarith
  have hinv : 1 / (S.card : ℝ) ≤ ∑ v, p v ^ 2 := by
    rw [div_le_iff₀ hk0]; linarith
  have ht2 : M * (1 - ∑ v, p v ^ 2) ≤ M * (1 - 1 / (S.card : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hMnn
  rw [hk]
  set k : ℝ := (S.card : ℝ) with hkdef
  have hk1 : 0 ≤ 1 - 1 / k := by
    rw [sub_nonneg, div_le_one hk0]; exact hkpos
  have hk2 : 0 < 1 / k := one_div_pos.mpr hk0
  have hB : 0 < 1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k) := by
    nlinarith [mul_pos (show 0 < 1 + ε by linarith) hk2]
  have hone : δ * (avgRes c u - pairRes c u / 2) = 1 := by rw [← h4b]; field_simp
  have h1 : M ≤ avgRes c u * (1 + ε) := by rw [hMm]; nlinarith
  have h2 : M * (1 - 1 / k) ≤ avgRes c u * (1 + ε) * (1 - 1 / k) :=
    mul_le_mul_of_nonneg_right h1 hk1
  have key : avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k)) ≤
      avgRes c u - pairRes c u / 2 := by nlinarith
  refine ⟨?_, fun heq hk2' => ?_⟩
  · rw [h4a, le_div_iff₀ hB]
    calc δ * avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k))
        = δ * (avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k))) := by ring
      _ ≤ δ * (avgRes c u - pairRes c u / 2) := mul_le_mul_of_nonneg_left key hδ.le
      _ = 1 := hone
  · have hk2'' : (2 : ℝ) ≤ (deg c u : ℝ) := by exact_mod_cast hk2'
    rw [hk] at hk2''
    have hk2' := hk2''
    have hw1 : 0 < 1 - 1 / k := by
      have : 1 / k < 1 := by rw [div_lt_one hk0]; linarith
      linarith
    rw [h4a] at heq
    have hδaB : δ * (avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k))) = δ * (avgRes c u - pairRes c u / 2) := by
      rw [hone]
      have : δ * avgRes c u * (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / k)) = 1 := by
        rw [heq]; exact one_div_mul_cancel hB.ne'
      linarith only [hone, this]
    have heq2 := mul_left_cancel₀ hδ.ne' hδaB
    -- chain: t = a(1+ε)(1-w)
    have hta : pairRes c u = avgRes c u * (1 + ε) * (1 - 1 / k) := by linear_combination 2 * heq2
    have hMpos : 0 < M := by rw [hMm]; exact mul_pos (by linarith only [hε0]) hm
    have E3 : M * (1 - 1 / k) = avgRes c u * (1 + ε) * (1 - 1 / k) := by
      linarith only [ht, ht2, h2, hta]
    have E1 : pairRes c u = M * (1 - ∑ v, p v ^ 2) := by linarith only [ht, ht2, h2, hta]
    have E2 : M * (1 - ∑ v, p v ^ 2) = M * (1 - 1 / k) := by linarith only [ht, ht2, h2, hta]
    have hMa : M = avgRes c u * (1 + ε) := mul_right_cancel₀ hw1.ne' E3
    have haeq : avgRes c u = m := by
      rw [hMm] at hMa
      have : (1 + ε) * (avgRes c u - m) = 0 := by linarith only [hMa]
      rcases mul_eq_zero.mp this with h | h
      · linarith only [h, hε0]
      · linarith only [h]
    have hsq : ∑ v, p v ^ 2 = 1 / k := by
      have := mul_left_cancel₀ hMpos.ne' E2
      linarith only [this]
    have hpos : ∀ v, 0 < c u v → 0 < p v := fun v hv => div_pos hv hδ
    have hvS : ∀ v, 0 < c u v → v ∈ S := by
      intro v hv
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => by rw [h, hdiag] at hv; exact lt_irrefl _ hv, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      have hsum0 : ∑ v, p v * (reff c u v - m) = 0 := by
        have : ∑ v, p v * (reff c u v - m) = avgRes c u - m := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsump]
          simp [avgRes, hp]
        rw [this, haeq]; ring
      have hnn' : ∀ v ∈ (Finset.univ : Finset V), 0 ≤ p v * (reff c u v - m) := by
        intro v _
        by_cases h : v = u
        · rw [h, hpu]; simp
        · exact mul_nonneg (hp0 v) (by linarith [(hmM u v (Ne.symm h)).1])
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp hsum0 v (Finset.mem_univ v)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (hpos v hv).ne'
      · linarith
    · intro v x hv hx hvx
      by_contra hne
      have hlt : reff c v x < M := lt_of_le_of_ne (hmM v x hvx).2 hne
      have hstrict : p v * p x * reff c v x <
          M * (p v * p x) - (if v = x then M * (p v * p v) else 0) := by
        simp only [hvx, if_false, sub_zero]
        have := mul_pos (hpos v hv) (hpos x hx)
        have := mul_lt_mul_of_pos_left hlt this
        linarith only [this]
      have : pairRes c u < ∑ v, ∑ x, (M * (p v * p x) - if v = x then M * (p v * p v) else 0) :=
        Finset.sum_lt_sum (fun v _ => Finset.sum_le_sum fun x _ => hterm v x)
          ⟨v, Finset.mem_univ _, Finset.sum_lt_sum (fun x _ => hterm v x)
            ⟨x, Finset.mem_univ _, hstrict⟩⟩
      rw [hsumT] at this
      linarith
    · intro v hv
      have hsq0 : ∑ v ∈ S, (p v - 1 / k) ^ 2 = 0 := by
        have : ∑ v ∈ S, (p v - 1 / k) ^ 2 = ∑ v ∈ S, p v ^ 2 - 2 * (1 / k) * ∑ v ∈ S, p v
            + k * (1 / k) ^ 2 := by
          simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          rw [hkdef]; ring
        rw [this, hSsum, ← hSq, hsq]
        field_simp
        ring
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => sq_nonneg (p v - 1 / k))).mp hsq0 v
        (hvS v hv)
      have hpv : p v = 1 / k := by
        have := pow_eq_zero_iff (two_ne_zero) |>.mp this
        linarith only [this]
      have : c u v / δ = 1 / k := hpv
      rw [div_eq_div_iff hδ.ne' hk0.ne'] at this
      field_simp
      linarith

end ResistanceRigidity.Dev.Thm31.PartA
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartA
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem tangent (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    2 * x / (a * x + b) ≤ 2 * d / (a * d + b) + 2 * b / (a * d + b) ^ 2 * (x - d) := by
  have hD : 0 < a * d + b := by positivity
  have hX : 0 < a * x + b := by positivity
  rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ hX (by positivity)]
  have : 0 ≤ a * b * (x - d) ^ 2 := by positivity
  have e : 2 * d * (a * d + b) ^ 2 / (a * d + b) = 2 * d * (a * d + b) := by field_simp
  field_simp
  nlinarith [this]

theorem ineq (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) : rhs c ≤ spread c := by
  obtain ⟨hε0, hle⟩ := basic c hc hconn hN
  by_cases hε : 1 ≤ spread c
  · linarith
  push_neg at hε
  have hN2 : 2 ≤ Fintype.card V := by omega
  have hE := edge_ge c hconn
  have hE' : (Fintype.card V : ℝ) ≤ edgeCount c + 1 := by exact_mod_cast hE
  have hN' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set ε := spread c with hεdef
  set d := avgDeg c with hddef
  have hd : d = 2 * (edgeCount c : ℝ) / N := rfl
  have hd1 : 1 < d := by
    rw [hd, lt_div_iff₀ (by linarith)]; linarith
  have hdN : d * N = 2 * edgeCount c := by rw [hd]; field_simp
  have hsumk : ∑ u, (deg c u : ℝ) = N * d := by rw [sum_deg c hc]; linarith
  set a : ℝ := 1 - ε with ha
  set b : ℝ := 1 + ε with hb
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hD : 0 < a * d + b := by positivity
  have hloc : ∀ u, levDeg c u ≤ 2 * d / (a * d + b) + 2 * b / (a * d + b) ^ 2 * ((deg c u : ℝ) - d) := by
    intro u
    obtain ⟨h1, h2⟩ := ResistanceRigidity.Dev.Eq7.main c hc hconn hN hε u
    have e : (1 - ε) * (deg c u : ℝ) + 1 + ε = a * (deg c u : ℝ) + b := by rw [ha, hb]; ring
    refine h1.trans (h2.le.trans ?_)
    rw [e]
    exact tangent a b d (deg c u : ℝ) ha0 hb0 (by linarith) (Nat.cast_nonneg _)
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hloc u)
  rw [sum_levDeg c hc hconn hN2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    hsumk] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hz : N * d - (Fintype.card V : ℝ) * d = 0 := by rw [← hNdef]; ring
  rw [hz, mul_zero, add_zero] at hsum
  rw [← mul_div_assoc, le_div_iff₀ hD] at hsum
  have hr : 0 < N - 1 := by linarith
  have key : (N - 1) - d ≤ ε * ((N - 1) * (d - 1)) := by
    simp only [ha, hb] at hsum
    nlinarith [hsum]
  unfold rhs
  rw [div_le_iff₀ (mul_pos hr (by linarith))]
  linarith [key]

end ResistanceRigidity.Dev.Thm31.PartA
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias ineq := ResistanceRigidity.Dev.Thm31.PartA.ineq

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartB
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem capDeg_eq (c : V → V → ℝ) (u : V) : capDeg c u = ∑ x, c u x := rfl

/-- Equality with `ε = 0`: complete graph, equal conductances. -/
theorem eq_zero (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (h : spread c = rhs c) (h0 : spread c = 0) :
    EqualConductances c ∧ IsComplete c := by
  obtain ⟨hm, hmM⟩ := ResistanceRigidity.Dev.Eq7.minmax c hc hconn hN
  have hN2 : 2 ≤ Fintype.card V := by omega
  set m := minRes c with hmdef
  have hMm : maxRes c = m := by
    unfold spread at h0
    have : maxRes c / m = 1 := by linarith
    rwa [div_eq_one_iff_eq hm.ne', ] at this
  have hR : ∀ x y, x ≠ y → reff c x y = m := fun x y hxy =>
    le_antisymm (hMm ▸ (hmM x y hxy).2) (hmM x y hxy).1
  have key : ∀ u y, u ≠ y → m * capDeg c u + m * c u y = 2 := by
    intro u y huy
    have hs := PartA.sum_rule c hc hconn hN2 u y huy
    have : ∀ x, c u x * (reff c u y + reff c u x - reff c x y)
        = m * c u x + (if x = y then m * c u y else 0) := by
      intro x
      by_cases hxu : x = u
      · subst hxu; simp [hc.2]; intro h; exact absurd h huy
      · by_cases hxy : x = y
        · subst hxy; simp [hR u x huy, ResistanceRigidity.Dev.Found.reff_self]; ring
        · simp [hxy, hR u y huy, hR u x (Ne.symm hxu), hR x y hxy]; ring
    rw [Finset.sum_congr rfl (fun x _ => this x)] at hs
    simp [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    rw [capDeg_eq]; linarith
  have hcap : ∀ u y, capDeg c u = capDeg c y := by
    intro u y
    by_cases huy : u = y
    · rw [huy]
    · have h1 := key u y huy
      have h2 := key y u (Ne.symm huy)
      rw [hc.1.2 y u] at h2
      have : m * (capDeg c u - capDeg c y) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hm.ne'
      · linarith
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
  set w := c a b with hw
  have hcw : ∀ x y, x ≠ y → c x y = w := by
    intro x y hxy
    have h1 := key x y hxy
    have h2 := key a b hab
    rw [hcap x a] at h1
    linarith [mul_left_cancel₀ hm.ne' (show m * c x y = m * w by nlinarith)]
  have hw0 : 0 ≤ w := hc.1.1 a b
  have hwpos : 0 < w := by
    refine hw0.lt_of_ne fun h => ?_
    have := ResistanceRigidity.Dev.Found.capDeg_pos c hc hconn hN2 a
    rw [capDeg_eq] at this
    have : ∑ x, c a x = 0 := Finset.sum_eq_zero fun x _ => by
      by_cases hx : a = x
      · rw [← hx, hc.2]
      · rw [hcw a x hx, ← h]
    linarith
  have hadj : ∀ x y, (adj c).Adj x y ↔ x ≠ y := by
    intro x y
    simp only [adj, SimpleGraph.fromRel_adj]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, Or.inl (by rw [hcw x y h]; exact hwpos)⟩
  refine ⟨⟨w, hwpos, fun u v huv => hcw u v ((hadj u v).1 huv)⟩, ?_⟩
  ext x y
  rw [hadj]; simp

end ResistanceRigidity.Dev.Thm31.PartB
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias eq_zero := ResistanceRigidity.Dev.Thm31.PartB.eq_zero

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartB
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem deg_pos (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 2 ≤ Fintype.card V) (u : V) : 1 ≤ deg c u := by
  have h := ResistanceRigidity.Dev.Found.capDeg_pos c hc hconn hN u
  rw [capDeg_eq] at h
  by_contra hlt
  have h0 : deg c u = 0 := by omega
  unfold deg at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have : ∑ x, c u x ≤ 0 := Finset.sum_nonpos fun x _ => by
    by_cases hx : x = u
    · rw [hx, hc.2]
    · exact not_lt.1 fun hp => h0 (Finset.mem_univ x) ⟨hx, hp⟩
  linarith

theorem deg_ge2 (c : V → V → ℝ) (hc : IsGraph c) (x a b : V) (ha : 0 < c x a) (hb : 0 < c x b)
    (hab : a ≠ b) : 2 ≤ deg c x := by
  unfold deg
  have hax : a ≠ x := fun h => by rw [h, hc.2] at ha; exact lt_irrefl _ ha
  have hbx : b ≠ x := fun h => by rw [h, hc.2] at hb; exact lt_irrefl _ hb
  exact Finset.one_lt_card.2 ⟨a, by simp [hax, ha], b, by simp [hbx, hb], hab⟩

theorem exists_other (c : V → V → ℝ) (hc : IsGraph c) (v x : V) (hx : 0 < c v x)
    (h2 : 2 ≤ deg c v) : ∃ x', 0 < c v x' ∧ x' ≠ x := by
  unfold deg at h2
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (show 1 < (Finset.univ.filter fun w => w ≠ v ∧ 0 < c v w).card by omega) x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
  exact ⟨y, hy.2, hyx⟩

theorem closed_all (c : V → V → ℝ) (hconn : Connected c) (S : Set V) (v : V) (hv : v ∈ S)
    (hcl : ∀ a b, a ∈ S → (adj c).Adj a b → b ∈ S) : ∀ z, z ∈ S := by
  intro z
  have : ∀ (a z : V) (p : (adj c).Walk a z), a ∈ S → z ∈ S := by
    intro a z p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun ha => ih (hcl _ _ ha h)
  obtain ⟨w⟩ := hconn.preconnected v z
  exact this _ _ w hv

theorem adj_pos (c : V → V → ℝ) (hc : IsGraph c) (x y : V) :
    (adj c).Adj x y ↔ 0 < c x y := by
  simp only [adj, SimpleGraph.fromRel_adj, hc.1.2 y x, or_self]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fun e => by rw [e, hc.2] at h; exact lt_irrefl _ h, h⟩

/-- Equality with `ε = 1`: star, equal conductances. -/
theorem eq_one (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (h : spread c = rhs c) (h1 : spread c = 1) :
    EqualConductances c ∧ IsStar c := by
  classical
  obtain ⟨hm, hmM⟩ := ResistanceRigidity.Dev.Eq7.minmax c hc hconn hN
  have hN2 : 2 ≤ Fintype.card V := by omega
  set m := minRes c with hmdef
  have hMm : maxRes c = 2 * m := by
    unfold spread at h1
    have : maxRes c / m = 2 := by linarith
    rw [div_eq_iff hm.ne'] at this
    linarith
  have hRle : ∀ x y, reff c x y ≤ 2 * m := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy, ResistanceRigidity.Dev.Found.reff_self]; linarith
    · exact hMm ▸ (hmM x y hxy).2
  have hRge : ∀ x y, x ≠ y → m ≤ reff c x y := fun x y hxy => (hmM x y hxy).1
  have hsymm := ResistanceRigidity.Dev.Found.reff_symm c hc hconn
  have hN' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  -- degree sum
  have hsumk : ∑ u, (deg c u : ℝ) = 2 * (N - 1) := by
    rw [PartA.sum_deg c hc]
    have hr1 : rhs c = 1 := by rw [← h, h1]
    unfold rhs at hr1
    have hb : ((N - 1) * (avgDeg c - 1)) ≠ 0 := by
      intro hb; rw [hb, div_zero] at hr1; exact zero_ne_one hr1
    rw [div_eq_one_iff_eq hb] at hr1
    have hdN : avgDeg c * N = 2 * edgeCount c := by
      unfold avgDeg; field_simp; rfl
    nlinarith
  have hk1 : ∀ u, (1 : ℝ) ≤ deg c u := fun u => by exact_mod_cast deg_pos c hc hconn hN2 u
  have hle : ∀ u, levDeg c u ≤ deg c u := by
    intro u
    have := (PartA.local_bound c hc hconn hN h1.le u).1
    rw [h1] at this
    have hk : (deg c u : ℝ) ≠ 0 := by linarith [hk1 u]
    have e : 1 / (1 - (1 / 2 : ℝ) * (1 + 1) * (1 - 1 / (deg c u : ℝ))) = deg c u := by
      field_simp; ring
    rwa [e] at this
  have heq : ∀ u, levDeg c u = deg c u := by
    have hs : ∑ u, levDeg c u = ∑ u, (deg c u : ℝ) := by
      rw [PartA.sum_levDeg c hc hconn hN2, hsumk]
    exact fun u => (Finset.sum_eq_sum_iff_of_le (fun u _ => hle u)).1 hs u (Finset.mem_univ u)
  have hbig : ∀ u, 2 ≤ deg c u →
      (∀ v, 0 < c u v → reff c u v = m) ∧
      (∀ v x, 0 < c u v → 0 < c u x → v ≠ x → reff c v x = 2 * m) ∧
      (∀ v, 0 < c u v → c u v = 1 / m) := by
    intro u hu
    have hk : (deg c u : ℝ) ≠ 0 := by linarith [hk1 u]
    have hspec : levDeg c u = 1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (deg c u : ℝ))) := by
      rw [h1, heq u]
      field_simp; ring
    obtain ⟨e1, e2, e3⟩ := (PartA.local_bound c hc hconn hN h1.le u).2 hspec hu
    refine ⟨e1, fun v x hv hx hvx => by rw [e2 v x hv hx hvx, hMm], ?_⟩
    -- levDeg = m * capDeg
    have hlev : levDeg c u = m * capDeg c u := by
      rw [PartA.levDeg_eq, capDeg_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : 0 < c u v
      · rw [e1 v hv]; ring
      · have : c u v = 0 := le_antisymm (not_lt.1 hv) (hc.1.1 u v)
        rw [this]; ring
    have hcap : capDeg c u = deg c u / m := by
      rw [eq_div_iff hm.ne']; linarith [heq u]
    intro v hv
    rw [e3 v hv, hcap]; field_simp
  have hedge : ∀ u v, 0 < c u v → c u v = 1 / m ∧ reff c u v = m := by
    intro u v huv
    have hvu : 0 < c v u := by rw [hc.1.2 v u]; exact huv
    by_cases h2u : 2 ≤ deg c u
    · obtain ⟨e1, -, e3⟩ := hbig u h2u
      exact ⟨e3 v huv, e1 v huv⟩
    by_cases h2v : 2 ≤ deg c v
    · obtain ⟨e1, -, e3⟩ := hbig v h2v
      refine ⟨?_, ?_⟩
      · rw [hc.1.2 u v]; exact e3 u hvu
      · rw [hsymm]; exact e1 u hvu
    exfalso
    have hcl : ∀ a b, a ∈ ({u, v} : Set V) → (adj c).Adj a b → b ∈ ({u, v} : Set V) := by
      intro a b ha hab
      rw [adj_pos c hc] at hab
      rcases ha with rfl | rfl
      · by_cases hbv : b = v
        · simp [hbv]
        · exfalso; exact h2u (deg_ge2 c hc a b v hab huv hbv)
      · by_cases hbu : b = u
        · simp [hbu]
        · exfalso; exact h2v (deg_ge2 c hc a b u hab hvu hbu)
    have hall := closed_all c hconn {u, v} u (by simp) hcl
    obtain ⟨a, b, d, hab, had, hbd⟩ := Fintype.two_lt_card_iff.1 (by omega : 2 < Fintype.card V)
    have ha := hall a
    have hb := hall b
    have hd := hall d
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hd
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
  have hF4 : ∀ v, 2 ≤ deg c v → ∀ x u, 0 < c v x → 0 < c x u → u = v := by
    intro v hv2 x u hvx hxu
    by_contra huv
    have hxv : 0 < c x v := by rw [hc.1.2 x v]; exact hvx
    have hx2 : 2 ≤ deg c x := deg_ge2 c hc x v u hxv hxu (Ne.symm huv)
    obtain ⟨-, e2, -⟩ := hbig x hx2
    have hRvu : reff c v u = 2 * m := e2 v u hxv hxu (Ne.symm huv)
    have hRxu := (hedge x u hxu).2
    have hnadj : ¬ 0 < c v u := fun hp => by
      have := (hedge v u hp).2
      linarith
    have hs := PartA.sum_rule c hc hconn hN2 v u (Ne.symm huv)
    obtain ⟨x', hx', hx'x⟩ := exists_other c hc v x hvx hv2
    have hnbr : ∀ w, 0 < c v w →
        c v w * (reff c v u + reff c v w - reff c w u) = 1 / m * (2 * m + m - reff c w u) := by
      intro w hw
      rw [(hedge v w hw).1, (hedge v w hw).2, hRvu]
    have h1 : ∀ w, 0 < c v w → 1 ≤ c v w * (reff c v u + reff c v w - reff c w u) := by
      intro w hw
      rw [hnbr w hw, show 1 / m * (2 * m + m - reff c w u) = (2 * m + m - reff c w u) / m by ring,
        le_div_iff₀ hm]
      linarith [hRle w u]
    have h0 : ∀ w, 0 ≤ c v w * (reff c v u + reff c v w - reff c w u) := by
      intro w
      by_cases hw : 0 < c v w
      · linarith [h1 w hw]
      · have : c v w = 0 := le_antisymm (not_lt.1 hw) (hc.1.1 v w)
        rw [this]; simp
    have hx2' : c v x * (reff c v u + reff c v x - reff c x u) = 2 := by
      rw [hnbr x hvx, hRxu]; field_simp; ring
    have hsub : ∑ w ∈ ({x, x'} : Finset V), c v w * (reff c v u + reff c v w - reff c w u) ≤
        ∑ w, c v w * (reff c v u + reff c v w - reff c w u) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => h0 w)
    rw [Finset.sum_pair (Ne.symm hx'x), hs] at hsub
    linarith [h1 x' hx', hx2']
  obtain ⟨v, hv2⟩ : ∃ v, 2 ≤ deg c v := by
    by_contra hcon
    push_neg at hcon
    have : ∑ u, (deg c u : ℝ) ≤ ∑ _u : V, (1 : ℝ) := Finset.sum_le_sum fun u _ => by
      have : deg c u ≤ 1 := by have := hcon u; omega
      exact_mod_cast this
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  refine ⟨⟨1 / m, by positivity, fun x y hxy => (hedge x y ((adj_pos c hc x y).1 hxy)).1⟩, v, ?_⟩
  have hcl : ∀ a b, a ∈ {z | z = v ∨ 0 < c v z} → (adj c).Adj a b → b ∈ {z | z = v ∨ 0 < c v z} := by
    intro a b ha hab
    rw [adj_pos c hc] at hab
    rcases ha with rfl | ha
    · exact Or.inr hab
    · exact Or.inl (hF4 v hv2 a b ha hab)
  have hall := closed_all c hconn {z | z = v ∨ 0 < c v z} v (Or.inl rfl) hcl
  intro x y
  rw [adj_pos c hc]
  constructor
  · intro hxy
    have hne : x ≠ y := fun e => by rw [e, hc.2] at hxy; exact lt_irrefl _ hxy
    refine ⟨hne, ?_⟩
    by_contra hcon
    push_neg at hcon
    rcases hall x with hx | hx
    · exact hcon.1 hx
    · exact hcon.2 (hF4 v hv2 x y hx hxy)
  · rintro ⟨hne, hxv | hyv⟩
    · subst hxv
      rcases hall y with hy | hy
      · exact absurd hy.symm hne
      · exact hy
    · subst hyv
      rcases hall x with hx | hx
      · exact absurd hx hne
      · rw [hc.1.2 x y]; exact hx

end ResistanceRigidity.Dev.Thm31.PartB
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias eq_one := ResistanceRigidity.Dev.Thm31.PartB.eq_one

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartD
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem adj_iff_pos (c : V → V → ℝ) (hc : IsGraph c) (u v : V) :
    (adj c).Adj u v ↔ 0 < c u v := by
  simp only [adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rwa [hc.1.2 u v]
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [hc.2] at h
    exact lt_irrefl _ h

theorem tangent_diff (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    2 * d / (a * d + b) + 2 * b / (a * d + b) ^ 2 * (x - d) - 2 * x / (a * x + b)
      = 2 * a * b * (x - d) ^ 2 / ((a * d + b) ^ 2 * (a * x + b)) := by
  have hD : 0 < a * d + b := by positivity
  have hX : 0 < a * x + b := by positivity
  field_simp
  ring

theorem tangent_eq (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 ≤ d) (hx : 0 ≤ x)
    (h : 2 * d / (a * d + b) + 2 * b / (a * d + b) ^ 2 * (x - d) = 2 * x / (a * x + b)) :
    x = d := by
  have hD : 0 < a * d + b := by positivity
  have hX : 0 < a * x + b := by positivity
  have := tangent_diff a b d x ha hb hd hx
  rw [h, sub_self, eq_comm, div_eq_zero_iff] at this
  rcases this with h | h
  · have : (x - d) ^ 2 = 0 := by
      have h2 : 2 * a * b ≠ 0 := by positivity
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h h2
      · exact h
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  · exfalso
    have : 0 < (a * d + b) ^ 2 * (a * x + b) := by positivity
    linarith

theorem step1 (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (h : spread c = rhs c) (h0 : 0 < spread c) (h1 : spread c < 1) :
    ∀ u, (deg c u : ℝ) = avgDeg c ∧
      levDeg c u = 1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (deg c u : ℝ))) := by
  have hN2 : 2 ≤ Fintype.card V := by omega
  have hE := PartA.edge_ge c hconn
  have hE' : (Fintype.card V : ℝ) ≤ edgeCount c + 1 := by exact_mod_cast hE
  have hN' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set ε := spread c with hεdef
  set d := avgDeg c with hddef
  have hd : d = 2 * (edgeCount c : ℝ) / N := rfl
  have hd1 : 1 < d := by
    rw [hd, lt_div_iff₀ (by linarith)]; linarith
  have hdN : d * N = 2 * edgeCount c := by rw [hd]; field_simp
  have hsumk : ∑ u, (deg c u : ℝ) = N * d := by rw [PartA.sum_deg c hc]; linarith
  set a : ℝ := 1 - ε with ha
  set b : ℝ := 1 + ε with hb
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hD : 0 < a * d + b := by positivity
  have hr : 0 < N - 1 := by linarith
  have hh : ε * ((N - 1) * (d - 1)) = N - 1 - d := by
    have h' := h
    unfold rhs at h'
    rw [eq_div_iff (mul_pos hr (by linarith)).ne'] at h'
    exact h'
  have hf : N * (2 * d / (a * d + b)) = 2 * (N - 1) := by
    rw [← mul_div_assoc, div_eq_iff hD.ne']
    simp only [ha, hb]
    linear_combination 2 * hh
  set A : ℝ := 2 * d / (a * d + b) with hA
  set B : ℝ := 2 * b / (a * d + b) ^ 2 with hBdef
  have hq : ∑ u, (A + B * ((deg c u : ℝ) - d) - levDeg c u) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hsumk, PartA.sum_levDeg c hc hconn hN2]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hNdef]
    linarith
  have hpar : ∀ u, 0 ≤ A + B * ((deg c u : ℝ) - d) - 2 * (deg c u : ℝ) / (a * (deg c u : ℝ) + b) ∧
      0 ≤ 2 * (deg c u : ℝ) / (a * (deg c u : ℝ) + b) - levDeg c u ∧
      1 / (1 - (1 / 2 : ℝ) * (1 + ε) * (1 - 1 / (deg c u : ℝ))) =
        2 * (deg c u : ℝ) / (a * (deg c u : ℝ) + b) := by
    intro u
    obtain ⟨h1', h2'⟩ := ResistanceRigidity.Dev.Eq7.main c hc hconn hN h1 u
    have e : (1 - ε) * (deg c u : ℝ) + 1 + ε = a * (deg c u : ℝ) + b := by rw [ha, hb]; ring
    rw [e] at h2'
    refine ⟨?_, ?_, h2'⟩
    · rw [tangent_diff a b d _ ha0 hb0 (by linarith) (Nat.cast_nonneg _)]
      positivity
    · rw [← h2']; linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => by
      obtain ⟨p1, p2, -⟩ := hpar u; linarith)).mp hq
  intro u
  obtain ⟨p1, p2, p3⟩ := hpar u
  have hzu := hz u (Finset.mem_univ u)
  have e1 : A + B * ((deg c u : ℝ) - d) - 2 * (deg c u : ℝ) / (a * (deg c u : ℝ) + b) = 0 := by
    linarith
  refine ⟨?_, ?_⟩
  · exact tangent_eq a b d _ ha0 hb0 (by linarith) (Nat.cast_nonneg _) (by linarith)
  · rw [p3]; linarith

theorem eq_mid (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (h : spread c = rhs c) (h0 : 0 < spread c) (h1 : spread c < 1) :
    EqualConductances c ∧ IsTriangleFreeSRG c := by
  classical
  have hN2 : 2 ≤ Fintype.card V := by omega
  have hs1 := step1 c hc hconn hN h h0 h1
  have hdeg : ∀ u, (deg c u : ℝ) = avgDeg c := fun u => (hs1 u).1
  have hlev := fun u => (hs1 u).2
  have hE := PartA.edge_ge c hconn
  have hE' : (Fintype.card V : ℝ) ≤ edgeCount c + 1 := by exact_mod_cast hE
  have hN' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hd1 : 1 < avgDeg c := by
    show 1 < 2 * (edgeCount c : ℝ) / (Fintype.card V : ℝ)
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hF : ∀ u, 2 ≤ deg c u := by
    intro u
    have : (1 : ℝ) < (deg c u : ℝ) := by rw [(hdeg u)]; exact hd1
    have : 1 < deg c u := by exact_mod_cast this
    omega
  have hloc := fun u => (PartA.local_bound c hc hconn hN h1.le u).2 (hlev u) (hF u)
  obtain ⟨hmpos, hmM⟩ := ResistanceRigidity.Dev.Eq7.minmax c hc hconn hN
  have hMm : maxRes c = (1 + spread c) * minRes c := by
    unfold spread; field_simp; ring
  have hMgt : minRes c < maxRes c := by
    rw [hMm]; nlinarith
  have hpos_of : ∀ u v, 0 < c u v → 0 < c v u := fun u v huv => by rwa [hc.1.2 v u]
  have hcnn := hc.1.1
  have hNpos : (0 : ℝ) < Fintype.card V := by linarith
  -- degrees constant
  obtain ⟨u0⟩ : Nonempty V := hconn.nonempty
  -- Step 2
  have hδ : ∀ u v, 0 < c u v → capDeg c u = capDeg c v := by
    intro u v huv
    have e1 := (hloc u).2.2 v huv
    have e2 := (hloc v).2.2 u (hpos_of u v huv)
    rw [hc.1.2 v u] at e2
    rw [e1] at e2
    have hk : (deg c u : ℝ) = deg c v := by rw [(hdeg u), (hdeg v)]
    rw [hk] at e2
    have : (0 : ℝ) < deg c v := by
      have := hF v
      have : (2 : ℝ) ≤ deg c v := by exact_mod_cast this
      linarith
    rw [div_left_inj' this.ne'] at e2
    exact e2
  have hδc : ∀ u, capDeg c u = capDeg c u0 := by
    intro u
    have hr := hconn.preconnected u0 u
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => rfl
    | @tail b' c' _ hab ih =>
      rw [← ih]
      exact (hδ b' c' ((adj_iff_pos c hc _ _).1 hab)).symm
  have hk0 : (0 : ℝ) < avgDeg c := by linarith
  have hw : ∀ u v, 0 < c u v → c u v = capDeg c u0 / avgDeg c := by
    intro u v huv
    rw [(hloc u).2.2 v huv, hδc u, (hdeg u)]
  have hδpos := ResistanceRigidity.Dev.Found.capDeg_pos c hc hconn hN2 u0
  have hwpos : 0 < capDeg c u0 / avgDeg c := div_pos hδpos hk0
  set w := capDeg c u0 / avgDeg c with hwdef
  have hcw : ∀ u v, c u v = if 0 < c u v then w else 0 := by
    intro u v
    split_ifs with hh
    · exact hw u v hh
    · exact le_antisymm (not_lt.1 hh) (hcnn u v)
  refine ⟨⟨w, hwpos, fun u v huv => hw u v ((adj_iff_pos c hc _ _).1 huv)⟩, ?_⟩
  set m := minRes c with hmdef
  set M := maxRes c with hMdef
  have hRm : ∀ u v, 0 < c u v → reff c u v = m := fun u v huv => (hloc u).1 v huv
  have hRM : ∀ u v x, 0 < c u v → 0 < c u x → v ≠ x → reff c v x = M :=
    fun u v x hv hx hvx => (hloc u).2.1 v x hv hx hvx
  have htri : ∀ u v x, 0 < c u v → 0 < c u x → v ≠ x → 0 < c v x → False := by
    intro u v x hv hx hvx hvx'
    have := hRM u v x hv hx hvx
    rw [hRm v x hvx'] at this
    linarith
  have hnc : ∃ u v, u ≠ v ∧ ¬ 0 < c u v := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, b, x, hab, hax, hbx⟩ := Fintype.two_lt_card_iff.1 (show 2 < Fintype.card V by omega)
    exact htri a b x (hcon a b hab) (hcon a x hax) hbx (hcon b x hbx)
  -- Step 3
  have hlevc : ∀ u, levDeg c u = 2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ) := by
    intro u
    have h2 := PartA.sum_levDeg c hc hconn hN2
    have hall : ∀ v, levDeg c v = levDeg c u := by
      intro v
      rw [hlev v, hlev u, (hdeg v), (hdeg u)]
    rw [Finset.sum_congr rfl (fun v _ => hall v)] at h2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    field_simp
    linarith
  obtain ⟨-, -, h8⟩ := ResistanceRigidity.AverageLaw.eq_8 c hc hconn hN2
  obtain ⟨-, hLR⟩ := h8 hlevc
  have hsum : ∀ u v, u ≠ v → ∑ x, c u x * (reff c u v - reff c x v) = 2 / (Fintype.card V : ℝ) := by
    intro u v huv
    have e := congrFun (congrFun hLR u) v
    have hL : (lap c * resMat c) u v = capDeg c u * reff c u v - ∑ x, c u x * reff c x v := by
      rw [ResistanceRigidity.Dev.Found.lap_eq c hc]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply, resMat, sub_mul,
        Finset.sum_sub_distrib, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rfl
    rw [hL] at e
    simp [projOnes, huv, Matrix.sub_apply] at e
    have hexp : ∑ x, c u x * (reff c u v - reff c x v)
        = capDeg c u * reff c u v - ∑ x, c u x * reff c x v := by
      unfold capDeg MarkovMixing.vertexConductance
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hexp, e]
    field_simp
  -- Step 4
  have hmin : ∀ u v, u ≠ v → ¬ 0 < c u v → (∀ u' v', u' ≠ v' → ¬ 0 < c u' v' →
      reff c u v ≤ reff c u' v') → reff c u v = M := by
    intro u v huv hnuv hle
    have hs := hsum u v huv
    have hgt : 0 < ∑ x, c u x * (reff c u v - reff c x v) := by
      rw [hs]; positivity
    have : ∃ x, 0 < c u x * (reff c u v - reff c x v) := by
      by_contra hno
      push_neg at hno
      exact absurd (Finset.sum_nonpos fun x _ => hno x) (not_le.2 hgt)
    obtain ⟨x, hx⟩ := this
    have hux : 0 < c u x := by
      rcases (hcnn u x).eq_or_lt with h | h
      · rw [← h] at hx; simp at hx
      · exact h
    have hlt : reff c x v < reff c u v := by
      have := (mul_pos_iff_of_pos_left hux).1 hx
      linarith
    have hxv : x ≠ v := by
      rintro rfl; exact hnuv hux
    have hxv' : 0 < c x v := by
      by_contra hn
      have := hle x v hxv hn
      linarith
    exact hRM x u v (hpos_of u x hux) hxv' huv
  have hall : ∀ u v, u ≠ v → ¬ 0 < c u v → reff c u v = M := by
    obtain ⟨a, b, hab, hnab⟩ := hnc
    set S : Finset (V × V) := Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ¬ 0 < c p.1 p.2) with hS
    have hne : S.Nonempty := ⟨(a, b), by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hab, hnab⟩⟩
    obtain ⟨p, hpS, hpmin⟩ := Finset.exists_min_image S (fun p => reff c p.1 p.2) hne
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hpS
    have hpM := hmin p.1 p.2 hpS.1 hpS.2 (fun u' v' h1' h2' =>
      hpmin (u', v') (by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1', h2'⟩))
    intro u v huv hnuv
    have := hpmin (u, v) (by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨huv, hnuv⟩)
    have h2 := (hmM u v huv).2
    simp only at this
    linarith
  have hnb : ∀ u v, u ≠ v → ¬ 0 < c u v →
      ((Finset.univ.filter fun x => 0 < c u x ∧ 0 < c v x).card : ℝ) *
        (w * (M - m)) = 2 / (Fintype.card V : ℝ) := by
    intro u v huv hnuv
    rw [← hsum u v huv]
    have hRuv := hall u v huv hnuv
    have hterm : ∀ x, c u x * (reff c u v - reff c x v) =
        if (0 < c u x ∧ 0 < c v x) then w * (M - m) else 0 := by
      intro x
      by_cases hux : 0 < c u x
      · have hxv : x ≠ v := by rintro rfl; exact hnuv hux
        by_cases hvx : 0 < c v x
        · rw [if_pos ⟨hux, hvx⟩, hw u x hux, hRuv, hRm x v (hpos_of v x hvx)]
        · have := hall x v hxv (fun h => hvx (hpos_of x v h))
          rw [if_neg (fun h => hvx h.2), hRuv, this]; ring
      · have : c u x = 0 := le_antisymm (not_lt.1 hux) (hcnn _ _)
        rw [if_neg (fun h => hux h.1), this]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
  -- Step 5
  have hnbadj : ∀ u v, 0 < c u v → (Finset.univ.filter fun x => 0 < c u x ∧ 0 < c v x) = ∅ := by
    intro u v huv
    refine Finset.filter_eq_empty_iff.2 fun x _ hx => ?_
    have hvx' : v ≠ x := by
      rintro rfl; have := hx.2; rw [hc.2] at this; exact lt_irrefl _ this
    exact htri u v x huv hx.1 hvx' hx.2
  obtain ⟨a, b, hab, hnab⟩ := hnc
  set μ : ℕ := (Finset.univ.filter fun x => 0 < c a x ∧ 0 < c b x).card with hμdef
  have hK : w * (M - m) ≠ 0 := (mul_pos hwpos (sub_pos.2 hMgt)).ne'
  have hμ : ∀ u v, u ≠ v → ¬ 0 < c u v →
      (Finset.univ.filter fun x => 0 < c u x ∧ 0 < c v x).card = μ := by
    intro u v huv hnuv
    have := (hnb u v huv hnuv).trans (hnb a b hab hnab).symm
    have := mul_right_cancel₀ hK this
    exact_mod_cast this
  have hcn : ∀ u v, Fintype.card ((adj c).commonNeighbors u v) =
      (Finset.univ.filter fun x => 0 < c u x ∧ 0 < c v x).card := by
    intro u v
    exact Fintype.card_of_subtype _ (fun x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_commonNeighbors,
        adj_iff_pos c hc])
  have hdeg' : ∀ u, deg c u = deg c u0 := fun u => by
    have : (deg c u : ℝ) = deg c u0 := by rw [hdeg u, hdeg u0]
    exact_mod_cast this
  unfold IsTriangleFreeSRG
  refine ⟨hconn, ?_, ?_, deg c u0, 0, μ, ?_⟩
  · intro htop
    have : (adj c).Adj a b := by rw [htop]; exact hab
    exact hnab ((adj_iff_pos c hc _ _).1 this)
  · intro t ht
    rw [SimpleGraph.is3Clique_iff] at ht
    obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := ht
    exact htri x y z ((adj_iff_pos c hc _ _).1 hxy) ((adj_iff_pos c hc _ _).1 hxz) hyz.ne
      ((adj_iff_pos c hc _ _).1 hyz)
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro v
      rw [← PartA.deg_eq c hc v, hdeg' v]
    · intro v x hvx
      rw [hcn, hnbadj v x ((adj_iff_pos c hc _ _).1 hvx)]
      simp
    · intro v x hvx hn
      rw [hcn]
      exact hμ v x hvx (fun h => hn ((adj_iff_pos c hc _ _).2 h))

end ResistanceRigidity.Dev.Thm31.PartD
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias eq_mid := ResistanceRigidity.Dev.Thm31.PartD.eq_mid

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartC
open ResistanceRigidity.AverageLaw IncrementalER ResistanceRigidity.Dev.Found
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem lap_mul_apply (c : V → V → ℝ) (hc : IsGraph c) (M : Matrix V V ℝ) (x y : V) :
    (lap c * M) x y = ∑ z, c x z * (M x y - M z y) := by
  rw [lap_eq c hc, Matrix.sub_mul, Matrix.sub_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem uniq (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (Q' : Matrix V V ℝ)
    (hs : ∀ x y, Q' x y = Q' y x) (hL : lap c * Q' = projOnes V)
    (h1 : ∀ x, ∑ y, Q' x y = 0) : Q' = pinvLap c := by
  set D := Q' - pinvLap c with hD
  have hLD : lap c * D = 0 := by
    rw [hD, Matrix.mul_sub, hL, lap_mul_pinv c hc hconn, sub_self]
  have hcol : ∀ y x x', D x y = D x' y := by
    intro y x x'
    refine lap_const c hc hconn (fun x => D x y) ?_ x x'
    ext a
    have := congrFun (congrFun hLD a) y
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hDs : ∀ x y, D x y = D y x := by
    intro x y
    have := congrFun (congrFun (pinv_symm c hc hconn) x) y
    simp only [hD, Matrix.sub_apply, hs x y]
    simp only [Matrix.transpose_apply] at this
    rw [this]
  have hrow : ∀ x, ∑ y, D x y = 0 := by
    intro x
    simp only [hD, Matrix.sub_apply, Finset.sum_sub_distrib, h1 x, zero_sub, neg_eq_zero]
    have := congrFun (pinv_mulVec_one c hc hconn) x
    simpa [Matrix.mulVec, dotProduct] using this
  have hconst : ∀ x y, D x y = D x x := by
    intro x y
    rw [hDs x y, hcol x y x, hDs]
  have hz : ∀ x y, D x y = 0 := by
    intro x y
    have := hrow x
    rw [Finset.sum_congr rfl (fun y _ => hconst x y)] at this
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    have hN : (Fintype.card V : ℝ) ≠ 0 := by
      have : Nonempty V := hconn.nonempty
      exact_mod_cast Fintype.card_pos.ne'
    have h0 : D x x = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hN
      · exact h
    rw [hconst, h0]
  have : D = 0 := by ext x y; exact hz x y
  exact sub_eq_zero.1 this

theorem generic (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c) (R' : V → V → ℝ)
    (hsym : ∀ x y, R' x y = R' y x) (hdiag : ∀ x, R' x x = 0) (u : V → ℝ)
    (hH : ∀ x y, ∑ z, c x z * (R' x y - R' z y) =
      u x - 2 * (if x = y then 1 else 0) + 2 / (Fintype.card V : ℝ)) :
    ∀ x y, reff c x y = R' x y := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    have : Nonempty V := hconn.nonempty
    exact_mod_cast Fintype.card_pos.ne'
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set m : V → ℝ := fun x => N⁻¹ * ∑ z, R' z x with hm
  set s : ℝ := N⁻¹ * ∑ x, m x with hsdef
  have hrowsum : ∀ x, ∑ y, R' x y = N * m x := by
    intro x
    simp only [hm]
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
    exact Finset.sum_congr rfl (fun y _ => hsym x y)
  have hsumH : ∀ x, N * u x = N * ∑ z, c x z * (m x - m z) := by
    intro x
    have h1 : ∑ y, ∑ z, c x z * (R' x y - R' z y) = N * u x := by
      rw [Finset.sum_congr rfl (fun y _ => hH x y)]
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hNdef]
      have h1 : (Fintype.card V : ℝ) * (2 / (Fintype.card V : ℝ)) = 2 := by
        exact mul_div_cancel₀ _ hN
      rw [h1]; ring
    rw [← h1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hrowsum, hrowsum]
    ring
  have hLm : ∀ x, ∑ z, c x z * (m x - m z) = u x := by
    intro x
    have := hsumH x
    exact (mul_left_cancel₀ hN this).symm
  set Q' : Matrix V V ℝ := Matrix.of fun x y => -(1 / 2 : ℝ) * (R' x y - m x - m y + s) with hQ'
  have hQs : ∀ x y, Q' x y = Q' y x := by
    intro x y; simp only [hQ', Matrix.of_apply]; rw [hsym x y]; ring
  have hQL : lap c * Q' = projOnes V := by
    ext x y
    rw [lap_mul_apply c hc]
    have : ∀ z, c x z * (Q' x y - Q' z y) =
        -(1 / 2 : ℝ) * (c x z * (R' x y - R' z y) - c x z * (m x - m z)) := by
      intro z; simp only [hQ', Matrix.of_apply]; ring
    rw [Finset.sum_congr rfl (fun z _ => this z), ← Finset.mul_sum, Finset.sum_sub_distrib, hH,
      hLm]
    simp only [projOnes, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, mul_one]
    split_ifs <;> ring
  have hQ1 : ∀ x, ∑ y, Q' x y = 0 := by
    intro x
    simp only [hQ', Matrix.of_apply]
    rw [← Finset.mul_sum]
    have : ∑ y, (R' x y - m x - m y + s) = 0 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, hrowsum]
      have : ∑ y, m y = N * s := by
        rw [hsdef, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
      rw [this]; ring
    rw [this, mul_zero]
  have hQ := uniq c hc hconn Q' hQs hQL hQ1
  intro x y
  rw [reff_eq c hc hconn, ← hQ]
  simp only [hQ', Matrix.of_apply, hdiag]
  ring

theorem c_eq (c : V → V → ℝ) [DecidableRel (adj c).Adj] (hc : IsGraph c) (he : EqualConductances c) :
    ∃ w : ℝ, 0 < w ∧ ∀ x z, c x z = if (adj c).Adj x z then w else 0 := by
  obtain ⟨w, hw, h⟩ := he
  refine ⟨w, hw, fun x z => ?_⟩
  split_ifs with hxz
  · exact h x z hxz
  · by_cases hx : x = z
    · subst hx; exact hc.2 x
    · have h1 : ¬ 0 < c x z := fun hp => hxz (by
        simp only [adj, SimpleGraph.fromRel_adj]; exact ⟨hx, Or.inl hp⟩)
      exact le_antisymm (not_lt.1 h1) (hc.1.1 x z)

theorem maxmin (c : V → V → ℝ) (m M : ℝ)
    (hle : ∀ x y, x ≠ y → m ≤ reff c x y ∧ reff c x y ≤ M)
    (hm : ∃ x y, x ≠ y ∧ reff c x y = m) (hM : ∃ x y, x ≠ y ∧ reff c x y = M) :
    minRes c = m ∧ maxRes c = M := by
  obtain ⟨a, b, hab, hab'⟩ := hm
  obtain ⟨a2, b2, hab2, hab2'⟩ := hM
  have hne : (Finset.univ.offDiag : Finset (V × V)).Nonempty :=
    ⟨(a, b), by simp [hab]⟩
  unfold minRes maxRes
  rw [dif_pos hne, dif_pos hne]
  constructor
  · apply le_antisymm
    · rw [← hab']
      exact Finset.inf'_le _ (by simp [hab] : (a, b) ∈ Finset.univ.offDiag)
    · apply Finset.le_inf'
      intro p hp
      simp only [Finset.mem_offDiag] at hp
      exact (hle p.1 p.2 hp.2.2).1
  · apply le_antisymm
    · apply Finset.sup'_le
      intro p hp
      simp only [Finset.mem_offDiag] at hp
      exact (hle p.1 p.2 hp.2.2).2
    · rw [← hab2']
      exact Finset.le_sup' (fun p : V × V => reff c p.1 p.2)
        (by simp [hab2] : (a2, b2) ∈ Finset.univ.offDiag)

theorem twice_edges (c : V → V → ℝ) [DecidableRel (adj c).Adj] :
    2 * edgeCount c = ∑ v, (adj c).degree v := by
  unfold edgeCount
  convert (SimpleGraph.sum_degrees_eq_twice_card_edges (adj c)).symm

theorem degree_eq (c : V → V → ℝ) [DecidableRel (adj c).Adj] (v : V) :
    (adj c).degree v = (Finset.univ.filter fun w => (adj c).Adj v w).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w; simp

theorem exists_ne (hN : 3 ≤ Fintype.card V) : ∃ x y : V, x ≠ y := by
  obtain ⟨x⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
  exact ⟨y, x, hy⟩

theorem conv_complete (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (he : EqualConductances c) (hk : IsComplete c) :
    spread c = 0 ∧ rhs c = 0 := by
  classical
  obtain ⟨w, hw, hcw⟩ := c_eq c hc he
  have hadj : ∀ x z, (adj c).Adj x z ↔ x ≠ z := by
    intro x z; rw [hk]; simp
  have hNpos : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  set κ : ℝ := 2 / (w * N) with hκ
  have hκpos : 0 < κ := by positivity
  have hwκ : w * κ = 2 / N := by rw [hκ]; field_simp
  have hG := generic c hc hconn (fun x y => if x = y then 0 else κ)
    (fun x y => by simp only [eq_comm]) (fun x => by simp) (fun _ => 0) (by
    intro x y
    simp_rw [hcw, hadj]
    by_cases hxy : x = y
    · subst hxy
      have : ∀ z : V, (if x ≠ z then w else 0) * ((if x = x then (0:ℝ) else κ) - (if z = x then 0 else κ))
          = -(w * κ) + (if x = z then w * κ else 0) := by
        intro z
        by_cases h : x = z
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl (fun z _ => this z)]
      simp [Finset.sum_add_distrib]
      rw [hwκ]; field_simp; ring
    · have : ∀ z : V, (if x ≠ z then w else 0) * ((if x = y then (0:ℝ) else κ) - (if z = y then 0 else κ))
          = if z = y then w * κ else 0 := by
        intro z
        by_cases h : z = y
        · subst h; simp [hxy]
        · by_cases h2 : x = z <;> simp [h, h2, hxy]
      rw [Finset.sum_congr rfl (fun z _ => this z)]
      simp [hxy, hwκ]; rfl)
  have hR : ∀ x y, x ≠ y → reff c x y = κ := by
    intro x y hxy; rw [hG x y]; simp [hxy]
  have hmm := maxmin c κ κ (fun x y hxy => by rw [hR x y hxy]; exact ⟨le_rfl, le_rfl⟩)
    (by obtain ⟨x, y, h⟩ := exists_ne hN; exact ⟨x, y, h, hR x y h⟩)
    (by obtain ⟨x, y, h⟩ := exists_ne hN; exact ⟨x, y, h, hR x y h⟩)
  refine ⟨?_, ?_⟩
  · unfold spread; rw [hmm.1, hmm.2, div_self hκpos.ne']; ring
  · have hd : avgDeg c = N - 1 := by
      have h2 := twice_edges c
      have : ∀ v, (adj c).degree v = Fintype.card V - 1 := by
        intro v
        rw [degree_eq]
        have : (Finset.univ.filter fun w => (adj c).Adj v w) = Finset.univ.erase v := by
          ext w; simp [hadj, eq_comm]
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
      simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
      unfold avgDeg
      have h3 : (2 * (edgeCount c : ℝ)) = N * (N - 1) := by
        have : (2 * edgeCount c : ℕ) = Fintype.card V * (Fintype.card V - 1) := h2
        have h4 : (1:ℕ) ≤ Fintype.card V := by omega
        have := congrArg (fun n : ℕ => (n : ℝ)) this
        simpa [Nat.cast_sub h4] using this
      have hN0 : (Fintype.card V : ℝ) ≠ 0 := hNpos.ne'
      rw [h3, hNdef]; field_simp
    rw [hNdef] at hd
    unfold rhs
    rw [hd]; simp

end ResistanceRigidity.Dev.Thm31.PartC
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias conv_complete := ResistanceRigidity.Dev.Thm31.PartC.conv_complete

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartC
open ResistanceRigidity.AverageLaw IncrementalER ResistanceRigidity.Dev.Found
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem two_leaves (v : V) (hN : 3 ≤ Fintype.card V) : ∃ x y : V, x ≠ v ∧ y ≠ v ∧ x ≠ y := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 (by omega : 2 < Fintype.card V)
  by_cases ha : a = v
  · subst ha; exact ⟨b, c, hab.symm, hac.symm, hbc⟩
  · by_cases hb : b = v
    · subst hb; exact ⟨a, c, ha, hbc.symm, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

theorem conv_star (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (he : EqualConductances c) (hk : IsStar c) :
    spread c = 1 ∧ rhs c = 1 := by
  classical
  obtain ⟨w, hw, hcw⟩ := c_eq c hc he
  obtain ⟨v, hv⟩ := hk
  have hNpos : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have hN3 : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  have hcs : ∀ x z, c x z = if x ≠ z ∧ (x = v ∨ z = v) then w else 0 := by
    intro x z; rw [hcw]; simp only [hv]
  set R' : V → V → ℝ := fun x y => if x = y then 0 else if x = v ∨ y = v then 1 / w else 2 / w
    with hR'
  have hG := generic c hc hconn R'
    (fun x y => by
      simp only [hR']
      by_cases h : x = y
      · subst h; rfl
      · simp [h, Ne.symm h, or_comm])
    (fun x => by simp [hR'])
    (fun x => if x = v then 3 - N - 2 / N else 1 - 2 / N) (by
    intro x y
    simp_rw [hcs]
    by_cases hxv : x = v
    · subst hxv
      by_cases hyv : y = x
      · subst hyv
        have : ∀ z : V, (if y ≠ z ∧ (y = y ∨ z = y) then w else 0) * (R' y y - R' z y)
            = -1 + (if y = z then 1 else 0) := by
          intro z
          by_cases h : y = z
          · subst h; simp [hR']
          · simp [hR', h, Ne.symm h]; field_simp
        rw [Finset.sum_congr rfl (fun z _ => this z)]
        simp [Finset.sum_add_distrib]
        rw [hNdef]; ring
      · have : ∀ z : V, (if x ≠ z ∧ (x = x ∨ z = x) then w else 0) * (R' x y - R' z y)
            = -1 + (if x = z then 1 else 0) + (if z = y then 2 else 0) := by
          intro z
          by_cases h : x = z
          · subst h; simp [hR', Ne.symm hyv]
          · by_cases h2 : z = y
            · subst h2; simp [hR', h, Ne.symm h]; field_simp; ring
            · simp [hR', h, Ne.symm h, h2, hyv, Ne.symm hyv]; field_simp; ring
        rw [Finset.sum_congr rfl (fun z _ => this z)]
        simp [Finset.sum_add_distrib, hyv, Ne.symm hyv]
        rw [hNdef]; ring
    · have : ∀ z : V, (if x ≠ z ∧ (x = v ∨ z = v) then w else 0) * (R' x y - R' z y)
          = if z = v then w * (R' x y - R' v y) else 0 := by
        intro z
        by_cases h : z = v
        · subst h; simp [hxv, Ne.symm hxv]
        · simp [h, hxv]
      rw [Finset.sum_congr rfl (fun z _ => this z)]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hxv, if_false]
      by_cases hyx : y = x
      · subst hyx; simp [hR', hxv, Ne.symm hxv]; field_simp; rw [hNdef]; ring
      · by_cases hyv : y = v
        · subst hyv; simp [hR', hxv, Ne.symm hxv]; field_simp; rw [hNdef]; ring
        · simp [hR', hxv, hyx, hyv, Ne.symm hxv, Ne.symm hyx, Ne.symm hyv]
          field_simp; rw [hNdef]; ring)
  have hR : ∀ x y, x ≠ y → reff c x y = R' x y := fun x y _ => hG x y
  have hw1 : 1 / w ≤ 2 / w := by gcongr; norm_num
  have hwpos : 1 / w < 2 / w := by gcongr; norm_num
  obtain ⟨a, b, ha, hb, hab⟩ := two_leaves v hN
  have hmm := maxmin c (1 / w) (2 / w)
    (by
      intro x y hxy
      rw [hR x y hxy]
      refine ⟨?_, ?_⟩ <;> (simp only [hR', if_neg hxy]; split_ifs <;> linarith))
    ⟨v, a, Ne.symm ha, by rw [hR v a (Ne.symm ha)]; simp [hR', Ne.symm ha]⟩
    ⟨a, b, hab, by rw [hR a b hab]; simp [hR', hab, ha, hb]⟩
  have hdeg : ∀ x, (adj c).degree x = if x = v then Fintype.card V - 1 else 1 := by
    intro x
    rw [degree_eq]
    by_cases hx : x = v
    · subst hx
      have : (Finset.univ.filter fun z => (adj c).Adj x z) = Finset.univ.erase x := by
        ext z; simp [hv, eq_comm]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]; simp
    · have : (Finset.univ.filter fun z => (adj c).Adj x z) = {v} := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hv]
        constructor
        · rintro ⟨_, h | h⟩
          · exact absurd h hx
          · exact h
        · rintro rfl; exact ⟨hx, Or.inr rfl⟩
      rw [this]; simp [hx]
  have h2 := twice_edges c
  simp only [hdeg] at h2
  have hsum : ∑ x : V, (if x = v then Fintype.card V - 1 else 1) = 2 * (Fintype.card V - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    simp only [if_true]
    rw [Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx))]
    simp [Finset.card_erase_of_mem]
    omega
  rw [hsum] at h2
  have h3 : 2 * (edgeCount c : ℝ) = 2 * (N - 1) := by
    have h4 : (1:ℕ) ≤ Fintype.card V := by omega
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_sub h4, Nat.cast_ofNat, Nat.cast_one] at this
    rw [this]
  have hd : avgDeg c = 2 * (N - 1) / N := by unfold avgDeg; rw [h3]
  refine ⟨?_, ?_⟩
  · unfold spread; rw [hmm.1, hmm.2]
    field_simp; norm_num
  · unfold rhs
    rw [← hNdef, hd]
    have h1 : N - 1 ≠ 0 := by linarith
    have h2 : N - 2 ≠ 0 := by linarith
    have hN0 : N ≠ 0 := hNpos.ne'
    have e1 : N - 1 - 2 * (N - 1) / N = (N - 1) * (N - 2) / N := by field_simp
    have e2 : 2 * (N - 1) / N - 1 = (N - 2) / N := by field_simp; ring
    rw [e1, e2]
    field_simp

end ResistanceRigidity.Dev.Thm31.PartC
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias conv_star := ResistanceRigidity.Dev.Thm31.PartC.conv_star

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31.PartC
open ResistanceRigidity.AverageLaw IncrementalER ResistanceRigidity.Dev.Found
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem degree_eq' (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = (Finset.univ.filter fun w => G.Adj v w).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w; simp

theorem sum_a (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    ∑ z, (if G.Adj x z then (1:ℝ) else 0) = (G.degree x : ℝ) := by
  rw [Finset.sum_boole, degree_eq']

theorem sum_aa (G : SimpleGraph V) [DecidableRel G.Adj] (k l μ : ℕ)
    (h : G.IsSRGWith (Fintype.card V) k l μ) (x y : V) :
    ∑ z, (if G.Adj x z then (1:ℝ) else 0) * (if G.Adj z y then 1 else 0) =
      if x = y then (k:ℝ) else if G.Adj x y then (l:ℝ) else (μ:ℝ) := by
  have e : ∑ z, (if G.Adj x z then (1:ℝ) else 0) * (if G.Adj z y then 1 else 0)
      = ((Finset.univ.filter fun z => G.Adj x z ∧ G.Adj y z).card : ℝ) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases h1 : G.Adj x z
    · by_cases h2 : G.Adj y z
      · simp [h1, h2, h2.symm]
      · have : ¬ G.Adj z y := fun hh => h2 hh.symm
        simp [h1, h2, this]
    · simp [h1]
  rw [e]
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true, and_self]
    rw [← degree_eq', show G.degree x = k from h.regular x]
  · have hc : (Finset.univ.filter fun z => G.Adj x z ∧ G.Adj y z).card
        = Fintype.card (G.commonNeighbors x y) :=
      (Fintype.card_of_subtype _ (fun z => by simp [SimpleGraph.mem_commonNeighbors])).symm
    rw [hc, if_neg hxy]
    by_cases ha : G.Adj x y
    · rw [if_pos ha, h.of_adj x y ha]
    · rw [if_neg ha, h.of_not_adj hxy ha]

theorem srg_facts (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (hne : G ≠ ⊤)
    (hcf : G.CliqueFree 3) (hN : 3 ≤ Fintype.card V) (k l μ : ℕ)
    (h : G.IsSRGWith (Fintype.card V) k l μ) :
    l = 0 ∧ 1 ≤ μ ∧ 2 ≤ k ∧ k < Fintype.card V ∧
      (k:ℝ) * (k - 1) = ((Fintype.card V : ℝ) - k - 1) * μ := by
  obtain ⟨x⟩ : Nonempty V := hconn.nonempty
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
  obtain ⟨b, hb⟩ : ∃ b, G.Adj x b := by
    obtain ⟨w⟩ := hconn.preconnected x y
    cases w with
    | nil => exact absurd rfl hy
    | @cons _ b _ hadj _ => exact ⟨b, hadj⟩
  have hk1 : 1 ≤ k := by
    have : 0 < G.degree x := by
      rw [degree_eq']; exact Finset.card_pos.2 ⟨b, by simp [hb]⟩
    rw [show G.degree x = k from h.regular x] at this; exact this
  have hl : l = 0 := by
    rw [← h.of_adj x b hb, Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨z, hz⟩ => ?_⟩
    rw [SimpleGraph.mem_commonNeighbors] at hz
    exact hcf {x, b, z} (SimpleGraph.is3Clique_triple_iff.2 ⟨hb, hz.1, hz.2⟩)
  have hklt : k < Fintype.card V := by
    have := G.degree_lt_card_verts x
    rwa [show G.degree x = k from h.regular x] at this
  have hp := SimpleGraph.IsSRGWith.param_eq G h (by omega)
  subst hl
  have hpR : (k:ℝ) * (k - 1) = ((Fintype.card V : ℝ) - k - 1) * μ := by
    have e1 : ((k - 0 - 1 : ℕ):ℝ) = k - 1 := by
      rw [Nat.sub_zero, Nat.cast_sub hk1]; simp
    have e2 : ((Fintype.card V - k - 1 : ℕ) : ℝ) = Fintype.card V - k - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have := congrArg (Nat.cast : ℕ → ℝ) hp
    rw [Nat.cast_mul, Nat.cast_mul, e1, e2] at this
    exact this
  have hμ : 1 ≤ μ := by
    by_contra hμ0
    have hμ0 : μ = 0 := by omega
    subst hμ0
    have hk : k = 1 := by
      have : (k:ℝ) * (k - 1) = 0 := by rw [hpR]; simp
      rcases mul_eq_zero.1 this with h0 | h0
      · have : (k:ℝ) = 0 := h0
        have : k = 0 := by exact_mod_cast this
        omega
      · have : (k:ℝ) = 1 := by linarith
        exact_mod_cast this
    subst hk
    have huniq : ∀ v, ∃! z, G.Adj v z := fun v =>
      (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1 (h.regular v)
    obtain ⟨z, hz⟩ : ∃ z, z ≠ x ∧ z ≠ b := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ : Finset V) ⊆ {x, b} := by
        intro z _
        by_cases hzx : z = x
        · simp [hzx]
        · simp [hcon z hzx]
      have := Finset.card_le_card this
      have := Finset.card_le_two (a := x) (b := b)
      rw [Finset.card_univ] at *
      omega
    obtain ⟨w⟩ := hconn.preconnected x z
    obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart ({x, b} : Set V)
      (by simp) (by simp [hz.1, hz.2])
    have hadj := d.adj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd1 hd2
    rcases hd1 with h1 | h1
    · rw [h1] at hadj
      obtain ⟨u, _, hu⟩ := huniq x
      exact hd2 (Or.inr ((hu _ hadj).trans (hu _ hb).symm))
    · rw [h1] at hadj
      obtain ⟨u, _, hu⟩ := huniq b
      exact hd2 (Or.inl ((hu _ hadj).trans (hu _ hb.symm).symm))
  have hk2 : 2 ≤ k := by
    by_contra hk0
    have hk : k = 1 := by omega
    subst hk
    have hN3 : (3:ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    have hμR : (1:ℝ) ≤ μ := by exact_mod_cast hμ
    norm_num at hpR
    rcases hpR with h0 | h0
    · linarith
    · omega
  exact ⟨rfl, hμ, hk2, hklt, hpR⟩

theorem conv_srg (c : V → V → ℝ) (hc : IsGraph c) (hconn : Connected c)
    (hN : 3 ≤ Fintype.card V) (he : EqualConductances c) (hk : IsTriangleFreeSRG c) :
    0 < spread c ∧ spread c < 1 ∧ spread c = rhs c := by
  classical
  obtain ⟨w, hw, hcw⟩ := c_eq c hc he
  obtain ⟨hcon', hne, hcf, k, l, μ, hsrg⟩ := hk
  obtain ⟨hl0, hμ1, hk2, hklt, hpR⟩ := srg_facts (adj c) hcon' hne hcf hN k l μ hsrg
  subst hl0
  have hNpos : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
  have hμR : (1:ℝ) ≤ μ := by exact_mod_cast hμ1
  set kR : ℝ := (k : ℝ) with hkRdef
  set μR : ℝ := (μ : ℝ) with hμRdef
  have hkk : kR * (kR + μR - 1) = (N - 1) * μR := by linear_combination hpR
  set a : V → V → ℝ := fun x z => if (adj c).Adj x z then 1 else 0 with ha
  have hca : ∀ x z, c x z = w * a x z := by
    intro x z; rw [hcw]; simp only [ha]; split_ifs <;> simp
  have ha0 : ∀ x, a x x = 0 := by intro x; simp [ha]
  have hsa : ∀ x, ∑ z, a x z = kR := by
    intro x; simp only [ha]; rw [sum_a, show (adj c).degree x = k from hsrg.regular x]
  have hcn : ∀ x y, ∑ z, a x z * a z y = if x = y then kR else if (adj c).Adj x y then 0 else μR := by
    intro x y
    have := sum_aa (adj c) k 0 μ hsrg x y
    simpa [ha] using this
  set β : ℝ := 2 / (w * N * μR) with hβ
  set α : ℝ := β * (kR + μR) with hα
  have hβpos : 0 < β := by positivity
  have hwβ : w * β * μR = 2 / N := by rw [hβ]; field_simp
  set R' : V → V → ℝ := fun x y => if x = y then 0 else α - β * a x y with hR'
  have hRz : ∀ z y, R' z y = α - α * (if z = y then 1 else 0) - β * a z y := by
    intro z y
    by_cases h : z = y
    · subst h; simp [hR', ha0]
    · simp [hR', h]
  have hE : w * β * (kR * (kR + μR - 1)) = 2 - 2 / N := by
    rw [hkk]
    have : w * β * ((N - 1) * μR) = (N - 1) * (w * β * μR) := by ring
    rw [this, hwβ]
    have hN0 : N ≠ 0 := hNpos.ne'
    field_simp
  have hG := generic c hc hconn R'
    (fun x y => by
      by_cases h : x = y
      · subst h; rfl
      · have : ¬ (adj c).Adj x y ↔ ¬ (adj c).Adj y x := by rw [(adj c).adj_comm]
        simp only [hR', h, Ne.symm h, if_false, ha]
        by_cases h1 : (adj c).Adj x y
        · simp [h1, h1.symm]
        · have h1' : ¬ (adj c).Adj y x := fun hh => h1 hh.symm
          simp [h1, h1'])
    (fun x => by simp [hR'])
    (fun _ => 0) (by
    intro x y
    have hterm : ∀ z, c x z * (R' x y - R' z y) = w * R' x y * a x z - w * α * a x z
        + w * α * (a x z * (if z = y then 1 else 0)) + w * β * (a x z * a z y) := by
      intro z; rw [hca, hRz z y]; ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    have hy' : ∑ z, a x z * (if z = y then (1:ℝ) else 0) = a x y := by simp
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsa, hy', hcn]
    by_cases hxy : x = y
    · subst hxy
      simp only [hR', if_true, ha0]
      rw [← hNdef, hα]
      linear_combination (-1) * hE
    · by_cases hadj : (adj c).Adj x y
      · simp only [hR', hxy, if_false, hadj, ha, if_true]
        rw [← hNdef, hα]
        linear_combination hwβ
      · simp only [hR', hxy, if_false, hadj, ha]
        rw [← hNdef]
        linear_combination hwβ)
  have hR : ∀ x y, x ≠ y → reff c x y = α - β * a x y := by
    intro x y hxy; rw [hG x y]; simp [hR', hxy]
  have hDpos : 2 ≤ kR + μR - 1 := by linarith
  have hαβ : α - β = β * (kR + μR - 1) := by rw [hα]; ring
  obtain ⟨x0⟩ : Nonempty V := hconn.nonempty
  obtain ⟨y1, hy1⟩ : ∃ y, (adj c).Adj x0 y := by
    have : 0 < (adj c).degree x0 := by
      rw [show (adj c).degree x0 = k from hsrg.regular x0]; omega
    rw [degree_eq'] at this
    obtain ⟨y, hy⟩ := Finset.card_pos.1 this
    exact ⟨y, by simpa using hy⟩
  obtain ⟨x2, y2, hxy2, hna2⟩ := SimpleGraph.ne_top_iff_exists_not_adj.1 hne
  have hmm := maxmin c (α - β) α
    (by
      intro x y hxy
      rw [hR x y hxy]
      by_cases hh : (adj c).Adj x y
      · simp only [ha, hh, if_true]; constructor <;> linarith
      · simp only [ha, hh, if_false]; constructor <;> linarith)
    ⟨x0, y1, hy1.ne, by rw [hR x0 y1 hy1.ne]; simp [ha, hy1]⟩
    ⟨x2, y2, hxy2, by rw [hR x2 y2 hxy2]; simp [ha, hna2]⟩
  have hspread : spread c = 1 / (kR + μR - 1) := by
    unfold spread; rw [hmm.1, hmm.2, hαβ, hα]
    have hD : kR + μR - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hd : avgDeg c = kR := by
    have h2 := twice_edges c
    simp only [show ∀ v, (adj c).degree v = k from hsrg.regular, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] at h2
    unfold avgDeg
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_ofNat] at this
    rw [this, ← hNdef]
    field_simp
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hspread]; apply one_div_pos.2; linarith
  · rw [hspread, div_lt_one (by linarith)]; linarith
  · rw [hspread]
    unfold rhs
    rw [← hNdef, hd]
    have hD : kR + μR - 1 ≠ 0 := by linarith
    have hN3 : (3:ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
    have hN1 : N - 1 ≠ 0 := by linarith
    have hk1 : kR - 1 ≠ 0 := by linarith
    rw [div_eq_div_iff hD (mul_ne_zero hN1 hk1)]
    linear_combination hkk

end ResistanceRigidity.Dev.Thm31.PartC
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.Dev.Thm31
open ResistanceRigidity.AverageLaw IncrementalER
variable {V : Type*} [Fintype V] [DecidableEq V]
alias conv_srg := ResistanceRigidity.Dev.Thm31.PartC.conv_srg

end ResistanceRigidity.Dev.Thm31
end

section
set_option autoImplicit false
open Matrix
namespace ResistanceRigidity.AverageLaw
open ResistanceRigidity.Dev.Thm31 in
theorem chk_theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 3 ≤ Fintype.card V) :
    ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) ≤
        spread c ∧
      (spread c =
          ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) ↔
        EqualConductances c ∧ (IsComplete c ∨ IsTriangleFreeSRG c ∨ IsStar c)) ∧
      (EqualConductances c → IsComplete c → spread c = 0) ∧
      (EqualConductances c → IsTriangleFreeSRG c → 0 < spread c ∧ spread c < 1) ∧
      (EqualConductances c → IsStar c → spread c = 1) := by
  have hI := ineq c hc hconn hN
  obtain ⟨hnn, hle⟩ := basic c hc hconn hN
  have e : rhs c = ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) := rfl
  rw [e] at hI hle
  refine ⟨hI, ⟨fun h => ?_, fun ⟨he, hk⟩ => ?_⟩, fun he hk => (conv_complete c hc hconn hN he hk).1,
    fun he hk => (conv_srg c hc hconn hN he hk).imp_right (fun h => h.1), fun he hk => (conv_star c hc hconn hN he hk).1⟩
  · have h' : spread c = rhs c := h
    have h1 : spread c ≤ 1 := by rw [h]; exact hle
    rcases hnn.eq_or_lt with h0 | h0
    · exact ⟨(eq_zero c hc hconn hN h' h0.symm).1, Or.inl (eq_zero c hc hconn hN h' h0.symm).2⟩
    rcases h1.eq_or_lt with h1 | h1
    · exact ⟨(eq_one c hc hconn hN h' h1).1, Or.inr (Or.inr (eq_one c hc hconn hN h' h1).2)⟩
    · exact ⟨(eq_mid c hc hconn hN h' h0 h1).1, Or.inr (Or.inl (eq_mid c hc hconn hN h' h0 h1).2)⟩
  · show spread c = rhs c
    rcases hk with hk | hk | hk
    · rw [(conv_complete c hc hconn hN he hk).1, (conv_complete c hc hconn hN he hk).2]
    · exact (conv_srg c hc hconn hN he hk).2.2
    · rw [(conv_star c hc hconn hN he hk).1, (conv_star c hc hconn hN he hk).2]

end ResistanceRigidity.AverageLaw
end

section
set_option autoImplicit false
open Matrix
open ResistanceRigidity
open ResistanceRigidity.AverageLaw
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 3 ≤ Fintype.card V) :
    ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) ≤
        spread c ∧
      (spread c =
          ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) ↔
        EqualConductances c ∧ (IsComplete c ∨ IsTriangleFreeSRG c ∨ IsStar c)) ∧
      (EqualConductances c → IsComplete c → spread c = 0) ∧
      (EqualConductances c → IsTriangleFreeSRG c → 0 < spread c ∧ spread c < 1) ∧
      (EqualConductances c → IsStar c → spread c = 1) := by
  exact ResistanceRigidity.AverageLaw.chk_theorem_3_1 c hc hconn hN
end
