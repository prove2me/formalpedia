-- Prove2me | solution 1 for ResistanceRigidity.AverageLaw.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:22:52.664203+00:00
-- url     : https://prove2.me/submissions/fd69c671-052c-4e69-8f86-bb24c17411f9

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Matrices
import Definitions.Def_ResistanceRigidity_AverageLaw_Local
import Definitions.Def_ResistanceRigidity_AverageLaw_Spread
import Theorems.Thm_ResistanceRigidity_AverageLaw_eq_4

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

theorem chk_eq_7 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 3 ≤ Fintype.card V) (hε : spread c < 1) (u : V) :
    IncrementalER.levDeg c u ≤
        1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (IncrementalER.deg c u : ℝ))) ∧
      1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (IncrementalER.deg c u : ℝ))) =
        2 * (IncrementalER.deg c u : ℝ) /
          ((1 - spread c) * (IncrementalER.deg c u : ℝ) + 1 + spread c) :=
  ResistanceRigidity.Dev.Eq7.main c hc hconn hN hε u

end ResistanceRigidity.AverageLaw
end

theorem solution : type_of% @ResistanceRigidity.AverageLaw.chk_eq_7 := @ResistanceRigidity.AverageLaw.chk_eq_7
