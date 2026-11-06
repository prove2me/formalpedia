-- Prove2me | solution 1 for SunNLSDP.Equiv.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:57:21.065974+00:00
-- url     : https://prove2.me/submissions/a78e4b5d-e81d-42af-aece-4887880efc1f

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDPLemma2Aux

open SunNLSDP.Equiv

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

theorem proj_spec (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty) (y : Z) :
    metricProj D y ∈ D ∧ ∀ w ∈ D, ‖metricProj D y - y‖ ≤ ‖w - y‖ := by
  have hex : ∃ z ∈ D, ∀ w ∈ D, ‖z - y‖ ≤ ‖w - y‖ := by
    obtain ⟨v, hv, hvi⟩ := exists_norm_eq_iInf_of_complete_convex hDne hD.isComplete hDc y
    refine ⟨v, hv, fun w hw => ?_⟩
    rw [norm_sub_rev v, norm_sub_rev w, hvi]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨w, hw⟩ : D)
  unfold metricProj
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem proj_vi (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty) (y : Z) :
    ∀ w ∈ D, ⟪y - metricProj D y, w - metricProj D y⟫ ≤ 0 := by
  obtain ⟨hm, hmin⟩ := proj_spec D hD hDc hDne y
  haveI : Nonempty D := hDne.to_subtype
  refine (norm_eq_iInf_iff_real_inner_le_zero hDc hm).1 ?_
  apply le_antisymm
  · apply le_ciInf
    rintro ⟨w, hw⟩
    rw [norm_sub_rev y, norm_sub_rev y]
    exact hmin w hw
  · exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨_, hm⟩ : D)

theorem proj_firm (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty) (a b : Z) :
    ‖metricProj D a - metricProj D b‖ ^ 2 ≤ ⟪metricProj D a - metricProj D b, a - b⟫ := by
  set pa := metricProj D a
  set pb := metricProj D b
  have h1 : ⟪a - pa, pb - pa⟫ ≤ 0 := proj_vi D hD hDc hDne a pb (proj_spec D hD hDc hDne b).1
  have h2 : ⟪b - pb, pa - pb⟫ ≤ 0 := proj_vi D hD hDc hDne b pa (proj_spec D hD hDc hDne a).1
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
  have e1 := real_inner_comm a pb
  have e2 := real_inner_comm pa pb
  have e3 := real_inner_comm a pa
  have e4 := real_inner_comm b pa
  have e5 := real_inner_comm b pb
  linarith

theorem proj_lip (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty) (a b : Z) :
    ‖metricProj D a - metricProj D b‖ ≤ ‖a - b‖ := by
  have h := proj_firm D hD hDc hDne a b
  have hcs := real_inner_le_norm (metricProj D a - metricProj D b) (a - b)
  have h0 := norm_nonneg (metricProj D a - metricProj D b)
  have h0' := norm_nonneg (a - b)
  by_contra hc
  push Not at hc
  nlinarith

/-- the potential `φ(y) = ½‖y‖² - ½‖y - Π y‖²` -/
noncomputable def pot (D : Set Z) (y : Z) : ℝ :=
  (1 / 2 : ℝ) * ‖y‖ ^ 2 - (1 / 2 : ℝ) * ‖y - metricProj D y‖ ^ 2

theorem pot_bound (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty) (y h : Z) :
    |pot D (y + h) - pot D y - ⟪metricProj D y, h⟫| ≤ ‖h‖ ^ 2 := by
  set z := y + h
  set py := metricProj D y
  set pz := metricProj D z
  set a := y - py
  set q := pz - py
  have hz1 : ‖pz - z‖ ≤ ‖py - z‖ := (proj_spec D hD hDc hDne z).2 py (proj_spec D hD hDc hDne y).1
  have hy1 : ‖py - y‖ ≤ ‖pz - y‖ := (proj_spec D hD hDc hDne y).2 pz (proj_spec D hD hDc hDne z).1
  have hlip : ‖q‖ ≤ ‖h‖ := by
    have := proj_lip D hD hDc hDne z y
    simpa [z, q] using this
  have hcs : ⟪q, h⟫ ≤ ‖h‖ ^ 2 := by
    have := real_inner_le_norm q h
    nlinarith [norm_nonneg q, norm_nonneg h]
  -- squared versions
  have hz2 : ‖pz - z‖ ^ 2 ≤ ‖py - z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz1 2
  have hy2 : ‖py - y‖ ^ 2 ≤ ‖pz - y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy1 2
  have ez : pz - z = q - a - h := by simp only [q, a, z]; abel
  have ez' : py - z = -a - h := by simp only [a, z]; abel
  have ey : py - y = -a := by simp only [a]; abel
  have ey' : pz - y = q - a := by simp only [q, a]; abel
  have ezz : z - pz = a + h - q := by simp only [q, a, z]; abel
  have hpy : py = y - a := by simp only [a]; abel
  rw [ez, ez'] at hz2
  rw [ey, ey'] at hy2
  unfold pot
  rw [show y + h - metricProj D (y + h) = a + h - q from ezz, show y - metricProj D y = a from rfl, hpy]
  rw [show z = y + h from rfl]
  simp only [← real_inner_self_eq_norm_sq] at hz2 hy2 hcs ⊢
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left,
    inner_neg_right] at hz2 hy2 hcs ⊢
  have e1 := real_inner_comm a h
  have e2 := real_inner_comm a q
  have e3 := real_inner_comm h q
  have e4 := real_inner_comm y h
  have e5 := real_inner_comm y a
  rw [abs_le]
  constructor <;> nlinarith

theorem pot_hasFDerivAt (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty)
    (y : Z) : HasFDerivAt (pot D) (innerSL ℝ (metricProj D y)) y := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : Z => ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
  rw [innerSL_apply_apply, Real.norm_eq_abs, one_mul, norm_pow, norm_norm]
  exact pot_bound D hD hDc hDne y h

/-- the target property set -/
def Good : Set (Z →L[ℝ] Z) :=
  {V | (∀ u w : Z, ⟪V u, w⟫ = ⟪u, V w⟫) ∧ ∀ d : Z, ‖V d‖ ^ 2 ≤ ⟪V d, d⟫}

theorem good_of_hasFDerivAt (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty)
    (u : Z) (V : Z →L[ℝ] Z) (hV : HasFDerivAt (metricProj D) V u) : V ∈ (Good : Set (Z →L[ℝ] Z)) := by
  constructor
  · intro v w
    have hf' : HasFDerivAt (fun y => innerSL ℝ (metricProj D y)) ((innerSL ℝ).comp V) u :=
      (innerSL ℝ).hasFDerivAt.comp u hV
    have := second_derivative_symmetric (f := pot D)
      (fun y => pot_hasFDerivAt D hD hDc hDne y) hf' v w
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply] at this
    rw [this, real_inner_comm]
  · intro d
    let c : ℕ → ℝ := fun k => (k : ℝ) + 1
    have hc : Tendsto (fun k => ‖c k‖) atTop atTop := by
      have : Tendsto c atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      refine this.congr' (Eventually.of_forall fun k => ?_)
      simp only [c, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
    have hlim := hV.lim d hc
    set x : ℕ → Z := fun k => c k • (metricProj D (u + (c k)⁻¹ • d) - metricProj D u)
    have hx : ∀ k, 0 ≤ ⟪x k, d⟫ - ‖x k‖ ^ 2 := by
      intro k
      have hck : 0 < c k := by simp only [c]; positivity
      have hf := proj_firm D hD hDc hDne (u + (c k)⁻¹ • d) u
      set Δ := metricProj D (u + (c k)⁻¹ • d) - metricProj D u
      have : u + (c k)⁻¹ • d - u = (c k)⁻¹ • d := by abel
      rw [this, inner_smul_right] at hf
      simp only [x]
      rw [inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hck]
      simp only [conj_trivial]
      have hinv : c k * (c k)⁻¹ = 1 := mul_inv_cancel₀ hck.ne'
      have : (c k * ‖Δ‖) ^ 2 = c k * c k * ‖Δ‖ ^ 2 := by ring
      rw [this]
      have h2 : c k * c k * ‖Δ‖ ^ 2 ≤ c k * c k * ((c k)⁻¹ * ⟪Δ, d⟫) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      have h3 : c k * c k * ((c k)⁻¹ * ⟪Δ, d⟫) = c k * ⟪Δ, d⟫ := by
        rw [← mul_assoc, mul_assoc (c k), hinv, mul_one]
      linarith
    have ht : Tendsto (fun k => ⟪x k, d⟫ - ‖x k‖ ^ 2) atTop (𝓝 (⟪V d, d⟫ - ‖V d‖ ^ 2)) :=
      (hlim.inner tendsto_const_nhds).sub (hlim.norm.pow 2)
    have := ge_of_tendsto' ht hx
    linarith

theorem good_closed_mem (V : Z →L[ℝ] Z) (Dk : ℕ → Z →L[ℝ] Z) (hT : Tendsto Dk atTop (𝓝 V))
    (hk : ∀ k, Dk k ∈ (Good : Set (Z →L[ℝ] Z))) : V ∈ (Good : Set (Z →L[ℝ] Z)) := by
  have happ : ∀ v : Z, Tendsto (fun k => Dk k v) atTop (𝓝 (V v)) := fun v =>
    ((ContinuousLinearMap.apply ℝ Z v).continuous.tendsto V).comp hT
  constructor
  · intro v w
    have t1 : Tendsto (fun k => ⟪Dk k v, w⟫ - ⟪v, Dk k w⟫) atTop (𝓝 (⟪V v, w⟫ - ⟪v, V w⟫)) :=
      ((happ v).inner tendsto_const_nhds).sub (tendsto_const_nhds.inner (happ w))
    have t0 : (fun k => ⟪Dk k v, w⟫ - ⟪v, Dk k w⟫) = fun _ => (0 : ℝ) := by
      funext k; rw [(hk k).1 v w]; ring
    rw [t0] at t1
    have := tendsto_nhds_unique tendsto_const_nhds t1
    linarith
  · intro d
    have t1 : Tendsto (fun k => ⟪Dk k d, d⟫ - ‖Dk k d‖ ^ 2) atTop (𝓝 (⟪V d, d⟫ - ‖V d‖ ^ 2)) :=
      ((happ d).inner tendsto_const_nhds).sub ((happ d).norm.pow 2)
    have := ge_of_tendsto' t1 (fun k => sub_nonneg.2 ((hk k).2 d))
    linarith

theorem good_convex : Convex ℝ (Good : Set (Z →L[ℝ] Z)) := by
  intro V1 h1 V2 h2 a b ha hb hab
  constructor
  · intro u w
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, h1.1 u w, h2.1 u w]
  · intro d
    have hconv := ((convexOn_norm (E := Z) convex_univ).pow (fun _ _ => norm_nonneg _) 2).2
      (Set.mem_univ (V1 d)) (Set.mem_univ (V2 d)) ha hb hab
    simp only [Pi.pow_apply, smul_eq_mul] at hconv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      inner_smul_left, conj_trivial]
    have q1 := h1.2 d
    have q2 := h2.2 d
    nlinarith

end SunNLSDPLemma2Aux

open SunNLSDPLemma2Aux in
theorem solution {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (D : Set Z) (hD : IsClosed D) (hDc : Convex ℝ D) (hDne : D.Nonempty)
    (y : Z) (V : Z →L[ℝ] Z) (hV : V ∈ clarkeJac (SunNLSDP.Equiv.metricProj D) y) :
    (∀ u w : Z, ⟪V u, w⟫ = ⟪u, V w⟫) ∧
    (∀ d : Z, 0 ≤ ⟪d, V d⟫) ∧
    (∀ d : Z, 0 ≤ ⟪V d, d - V d⟫) := by
  have hsub : bJac (SunNLSDP.Equiv.metricProj D) y ⊆ (Good : Set (Z →L[ℝ] Z)) := by
    rintro W ⟨u, -, hdiff, hT⟩
    exact good_closed_mem W _ hT fun k =>
      good_of_hasFDerivAt D hD hDc hDne (u k) _ (hdiff k).hasFDerivAt
  have hG : V ∈ (Good : Set (Z →L[ℝ] Z)) := convexHull_min hsub good_convex hV
  refine ⟨hG.1, fun d => ?_, fun d => ?_⟩
  · have := hG.2 d
    rw [real_inner_comm]
    nlinarith [sq_nonneg ‖V d‖]
  · have := hG.2 d
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    linarith
