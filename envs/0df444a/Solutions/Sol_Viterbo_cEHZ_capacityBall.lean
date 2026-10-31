-- Prove2me | solution 1 for Viterbo.cEHZ_capacityBall
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:38:06.208374+00:00
-- url     : https://prove2.me/submissions/7c171098-5136-4b90-b563-3d811eeca224

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo.EHZBall

open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo

variable {n : ℕ}

/-! ## Algebra of `phaseInner` and `J` -/

lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_add_left (x y w : Phase n) :
    phaseInner (x + y) w = phaseInner x w + phaseInner y w := by
  simp [phaseInner, inner_add_left]; ring

lemma pI_add_right (w x y : Phase n) :
    phaseInner w (x + y) = phaseInner w x + phaseInner w y := by
  simp [phaseInner, inner_add_right]; ring

lemma pI_sub_left (x y w : Phase n) :
    phaseInner (x - y) w = phaseInner x w - phaseInner y w := by
  simp [phaseInner, inner_sub_left]; ring

lemma pI_sub_right (w x y : Phase n) :
    phaseInner w (x - y) = phaseInner w x - phaseInner w y := by
  simp [phaseInner, inner_sub_right]; ring

lemma pI_smul_left (c : ℝ) (x w : Phase n) :
    phaseInner (c • x) w = c * phaseInner x w := by
  simp [phaseInner, real_inner_smul_left]; ring

lemma pI_smul_right (c : ℝ) (w x : Phase n) :
    phaseInner w (c • x) = c * phaseInner w x := by
  simp [phaseInner, real_inner_smul_right]; ring

lemma pI_self (z : Phase n) : phaseInner z z = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp [phaseInner, real_inner_self_eq_norm_sq]

lemma pI_self_nonneg (z : Phase n) : 0 ≤ phaseInner z z := by
  rw [pI_self]; positivity

lemma pI_self_eq_zero {z : Phase n} (h : phaseInner z z = 0) : z = 0 := by
  rw [pI_self] at h
  have h1 : ‖z.1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  have h2 : ‖z.2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at h1 h2
  exact Prod.ext h1 h2

lemma J_smul (c : ℝ) (z : Phase n) : J (c • z) = c • J z := by
  simp [J]

lemma pI_J_J (x y : Phase n) : phaseInner (J x) (J y) = phaseInner x y := by
  simp [phaseInner, J]; ring

lemma pI_J_left (x y : Phase n) : phaseInner (J x) y = -phaseInner x (J y) := by
  simp [phaseInner, J, inner_neg_left, inner_neg_right, real_inner_comm]

lemma pI_J_self (x : Phase n) : phaseInner x (J x) = 0 := by
  simp [phaseInner, J, inner_neg_right, real_inner_comm]

lemma abs_pI_le (x y : Phase n) : |phaseInner x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold phaseInner
  have h1 := abs_real_inner_le_norm x.1 y.1
  have h2 := abs_real_inner_le_norm x.2 y.2
  have a1 := norm_fst_le x
  have a2 := norm_snd_le x
  have b1 := norm_fst_le y
  have b2 := norm_snd_le y
  calc |inner ℝ x.1 y.1 + inner ℝ x.2 y.2| ≤ |inner ℝ x.1 y.1| + |inner ℝ x.2 y.2| := abs_add_le _ _
    _ ≤ ‖x.1‖ * ‖y.1‖ + ‖x.2‖ * ‖y.2‖ := add_le_add h1 h2
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by gcongr
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- `phaseInner · w` as a continuous linear functional. -/
noncomputable def pIL (w : Phase n) : Phase n →L[ℝ] ℝ :=
  (innerSL ℝ w.1).comp (ContinuousLinearMap.fst ℝ (Position n) (Position n)) +
    (innerSL ℝ w.2).comp (ContinuousLinearMap.snd ℝ (Position n) (Position n))

lemma pIL_apply (w z : Phase n) : pIL w z = phaseInner z w := by
  simp [pIL, phaseInner, real_inner_comm]

/-! ## The ball, its boundary, its normal cones -/

lemma mem_ball_iff {r : ℝ} (z : Phase n) :
    z ∈ capacityBall n (Real.pi * r ^ 2) ↔ phaseInner z z < r ^ 2 := by
  rw [pI_self]
  show Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < Real.pi * r ^ 2 ↔ _
  exact mul_lt_mul_iff_right₀ Real.pi_pos

lemma isOpen_ball (r : ℝ) : IsOpen (capacityBall n (Real.pi * r ^ 2)) := by
  show IsOpen {z : Phase n | Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < Real.pi * r ^ 2}
  exact isOpen_lt (by fun_prop) continuous_const

lemma mem_frontier_iff {r : ℝ} (hr : 0 < r) (z : Phase n) :
    z ∈ frontier (capacityBall n (Real.pi * r ^ 2)) ↔ phaseInner z z = r ^ 2 := by
  rw [(isOpen_ball r).frontier_eq]
  constructor
  · rintro ⟨hcl, hn⟩
    rw [mem_ball_iff] at hn
    have hsub : closure (capacityBall n (Real.pi * r ^ 2)) ⊆ {z : Phase n | phaseInner z z ≤ r ^ 2} := by
      apply closure_minimal
      · intro y hy; exact le_of_lt ((mem_ball_iff y).1 hy)
      · apply isClosed_le _ continuous_const
        simp only [pI_self]; fun_prop
    have := hsub hcl
    simp only [mem_setOf_eq] at this
    linarith [not_lt.1 hn]
  · intro h
    refine ⟨?_, ?_⟩
    · have ht : Tendsto (fun s : ℝ => s • z) (𝓝[<] 1) (𝓝 z) := by
        have : Tendsto (fun s : ℝ => s • z) (𝓝 1) (𝓝 ((1 : ℝ) • z)) :=
          ((continuous_id.smul continuous_const).tendsto 1)
        rw [one_smul] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      apply mem_closure_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      rw [mem_ball_iff, pI_smul_left, pI_smul_right, h]
      have h1 : s * s < 1 := by nlinarith [hs.1, hs.2]
      nlinarith [sq_nonneg r, pow_pos hr 2]
    · rw [mem_ball_iff, h]; exact lt_irrefl _

lemma smul_mem_normalCone {r : ℝ} {z : Phase n} (hz : phaseInner z z = r ^ 2) {c : ℝ}
    (hc : 0 ≤ c) : c • z ∈ normalCone phaseInner (capacityBall n (Real.pi * r ^ 2)) z := by
  intro y hy
  rw [mem_ball_iff] at hy
  have h0 := pI_self_nonneg (z - y)
  rw [pI_sub_left, pI_sub_right, pI_sub_right, pI_comm y z] at h0
  rw [pI_smul_left, pI_sub_right, hz]
  have : phaseInner z y - r ^ 2 ≤ 0 := by nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos hc this

lemma normalCone_ball {r : ℝ} (hr : 0 < r) {z u : Phase n} (hz : phaseInner z z = r ^ 2)
    (hu : u ∈ normalCone phaseInner (capacityBall n (Real.pi * r ^ 2)) z) :
    u = (phaseInner u z / r ^ 2) • z ∧ 0 ≤ phaseInner u z := by
  have hR : 0 < r ^ 2 := pow_pos hr 2
  set R := r ^ 2 with hRdef
  set A := phaseInner u z with hA
  have hA0 : 0 ≤ A := by
    have := hu 0 (by rw [mem_ball_iff]; simp [phaseInner]; exact hR)
    rw [zero_sub, show -z = (-1 : ℝ) • z by simp, pI_smul_right] at this
    linarith
  refine ⟨?_, hA0⟩
  set μ := A / R with hμ
  set w := u - μ • z with hw
  have hwz : phaseInner w z = 0 := by
    rw [hw, pI_sub_left, pI_smul_left, hz, ← hA, hμ, div_mul_cancel₀ _ hR.ne', sub_self]
  have huw : phaseInner u w = phaseInner w w := by
    have : u = w + μ • z := by rw [hw]; abel
    conv_lhs => rw [this]
    rw [pI_add_left, pI_smul_left, pI_comm z w, hwz]; ring
  by_contra hne
  have hw0 : w ≠ 0 := by
    intro h; apply hne; rw [hw] at h; exact sub_eq_zero.1 h
  set p := phaseInner w w with hp
  have hp0 : 0 < p := lt_of_le_of_ne (pI_self_nonneg w) (fun h => hw0 (pI_self_eq_zero h.symm))
  set c := 1 / (A + 1) with hc
  have hc0 : 0 < c := by positivity
  set ε := c * R / (p * c ^ 2 * R + 1) with hε
  have hε0 : 0 < ε := by positivity
  set δ := ε * p * c with hδ
  have hεeq : ε * (p * c ^ 2 * R + 1) = c * R := by
    rw [hε]; field_simp
  set y := (1 - δ) • z + ε • w with hy
  have hzw : phaseInner z w = 0 := by rw [pI_comm]; exact hwz
  have hyS : y ∈ capacityBall n (Real.pi * r ^ 2) := by
    rw [mem_ball_iff, hy]
    simp only [pI_add_left, pI_add_right, pI_smul_left, pI_smul_right, hz, hwz, hzw]
    rw [← hp, ← hRdef]
    -- (1-δ)^2 R + ε^2 p < R
    have key : ε * (p * p * c ^ 2 * R + p) = p * c * R := by
      have := hεeq; nlinarith [this]
    have : (1 - δ) * ((1 - δ) * R + ε * 0) + ε * ((1 - δ) * 0 + ε * p) - R
        = ε * (ε * (p * p * c ^ 2 * R + p) - 2 * p * c * R) := by
      rw [hδ]; ring
    have h2 : ε * (ε * (p * p * c ^ 2 * R + p) - 2 * p * c * R) < 0 := by
      apply mul_neg_of_pos_of_neg hε0
      rw [key]; nlinarith [mul_pos (mul_pos hp0 hc0) hR]
    linarith
  have := hu y hyS
  rw [hy, show (1 - δ) • z + ε • w - z = (-δ) • z + ε • w by
    module] at this
  rw [pI_add_right, pI_smul_right, pI_smul_right, ← hA, huw] at this
  -- -δ A + ε p ≤ 0, but δ A = ε p c A < ε p
  have hcA : c * A < 1 := by
    rw [hc]; rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
  have : ε * p * (1 - c * A) ≤ 0 := by rw [hδ] at this; nlinarith
  have : 0 < ε * p * (1 - c * A) := by
    apply mul_pos (mul_pos hε0 hp0); linarith
  linarith

/-! ## Upper bound: the great circle -/

section Circle

variable (hn : 1 ≤ n) (r : ℝ)

noncomputable def e0 : Position n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1

lemma norm_e0 : ‖e0 hn‖ = 1 := by simp [e0]

noncomputable def circ (t : ℝ) : Phase n :=
  ((r * Real.cos (2 * Real.pi * t)) • e0 hn, (r * Real.sin (2 * Real.pi * t)) • e0 hn)

noncomputable def circV (t : ℝ) : Phase n := (2 * Real.pi) • J (circ hn r t)

lemma circ_hasDerivAt (t : ℝ) : HasDerivAt (circ hn r) (circV hn r t) t := by
  have hc : HasDerivAt (fun t => r * Real.cos (2 * Real.pi * t))
      (r * (-Real.sin (2 * Real.pi * t) * (2 * Real.pi))) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).cos
    simpa using this.const_mul r
  have hs : HasDerivAt (fun t => r * Real.sin (2 * Real.pi * t))
      (r * (Real.cos (2 * Real.pi * t) * (2 * Real.pi))) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).sin
    simpa using this.const_mul r
  have := (hc.smul_const (e0 hn)).prodMk (hs.smul_const (e0 hn))
  refine this.congr_deriv ?_
  refine Prod.ext ?_ ?_ <;> simp only [circV, circ, J, Prod.smul_fst, Prod.smul_snd] <;> module

lemma circ_sphere (t : ℝ) : phaseInner (circ hn r t) (circ hn r t) = r ^ 2 := by
  rw [pI_self]
  simp only [circ, norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
  rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]

lemma circ_periodic : Function.Periodic (circ hn r) 1 := by
  intro t
  simp only [circ, mul_add, mul_one]
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma circ_gcc (hr : 0 < r) :
    IsGeneralizedClosedCharacteristic (capacityBall n (Real.pi * r ^ 2)) (circ hn r) := by
  refine ⟨circ_periodic hn r, fun t => (mem_frontier_iff hr _).2 (circ_sphere hn r t),
    circV hn r, ?_, ?_, ?_⟩
  · have : Continuous (circV hn r) := by
      unfold circV circ J; fun_prop
    exact this.locallyIntegrable
  · intro a b
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => circ_hasDerivAt hn r x)]
    have : Continuous (circV hn r) := by
      unfold circV circ J; fun_prop
    exact this.intervalIntegrable a b
  · refine Filter.Eventually.of_forall (fun t => ⟨(2 * Real.pi) • circ hn r t, ?_, ?_⟩)
    · exact smul_mem_normalCone (circ_sphere hn r t) (by positivity)
    · simp [circV, J_smul]

lemma circ_nonconst (hr : 0 < r) : circ hn r 0 ≠ circ hn r (1 / 4) := by
  intro h
  have h2 := congrArg (fun z : Phase n => z.2) h
  simp only [circ, mul_zero, Real.sin_zero, zero_smul] at h2
  have : 2 * Real.pi * (1 / 4) = Real.pi / 2 := by ring
  rw [this, Real.sin_pi_div_two, mul_one] at h2
  have := congrArg norm h2
  rw [norm_zero, norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_of_pos hr] at this
  linarith

lemma circ_action : action (circ hn r) = Real.pi * r ^ 2 := by
  unfold action
  have : ∀ t, phaseInner (J (circ hn r t)) (deriv (circ hn r) t) = 2 * Real.pi * r ^ 2 := by
    intro t
    rw [(circ_hasDerivAt hn r t).deriv, circV, pI_smul_right, pI_J_J, circ_sphere]
  simp only [this, intervalIntegral.integral_const, sub_zero, one_smul, smul_eq_mul]
  ring

end Circle

/-! ## Lower bound -/

/-- An absolutely continuous function composed with a Lipschitz function. -/
lemma ac_comp_lip {f g : ℝ → ℝ} {K : NNReal} {a b : ℝ} (hg : LipschitzWith K g)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have h1 := h E hE hsum
  calc ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, K * dist (f (E.2 i).1) (f (E.2 i).2) :=
        Finset.sum_le_sum (fun i _ => hg.dist_le_mul _ _)
    _ = K * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by
        gcongr; linarith
    _ = ε := by field_simp

/-- The standing hypotheses of the lower bound, after extracting `λ`. -/
structure Data (r : ℝ) (γ v : ℝ → Phase n) (lam : ℝ → ℝ) : Prop where
  hr : 0 < r
  per : Function.Periodic γ 1
  sph : ∀ t, phaseInner (γ t) (γ t) = r ^ 2
  vint : LocallyIntegrable v volume
  ftc : ∀ a b, γ b - γ a = ∫ s in a..b, v s
  lamv : ∀ᵐ t, v t = lam t • J (γ t)
  lam0 : ∀ᵐ t, 0 ≤ lam t
  lamI : IntervalIntegrable lam volume 0 1

lemma Data.gamma_eq {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam) :
    γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
  funext x; rw [← H.ftc 0 x]; abel

lemma Data.ae_hasDerivAt {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam) :
    ∀ᵐ x, HasDerivAt γ (v x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral H.vint] with x hx
  rw [H.gamma_eq]
  simpa using (hx 0).const_add (γ 0)

lemma Data.action_eq {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam) :
    action γ = r ^ 2 / 2 * ∫ t in (0 : ℝ)..1, lam t := by
  unfold action
  have : ∫ t in (0 : ℝ)..1, phaseInner (J (γ t)) (deriv γ t) =
      ∫ t in (0 : ℝ)..1, lam t * r ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [H.ae_hasDerivAt, H.lamv] with x hx hl _
    rw [hx.deriv, hl, pI_smul_right, pI_J_J, H.sph]
  rw [this, intervalIntegral.integral_mul_const]
  ring

lemma Data.ac_clm {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam)
    (L : Phase n →L[ℝ] ℝ) : AbsolutelyContinuousOnInterval (fun t => L (γ t)) 0 1 := by
  have hvI : ∀ a b : ℝ, IntervalIntegrable v volume a b := fun a b =>
    (H.vint.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have heq : (fun t => L (γ t)) = fun t => L (γ 0) + ∫ s in (0 : ℝ)..t, L (v s) := by
    funext t
    have h := H.ftc 0 t
    rw [L.intervalIntegral_comp_comm (hvI 0 t), ← h, map_sub]; ring
  rw [heq]
  have h1 : AbsolutelyContinuousOnInterval (fun t => ∫ s in (0 : ℝ)..t, L (v s)) 0 1 :=
    (show IntervalIntegrable (fun s => L (v s)) volume 0 1 from
      ⟨L.integrable_comp (hvI 0 1).1, L.integrable_comp (hvI 0 1).2⟩).absolutelyContinuousOnInterval_intervalIntegral
      (by simp)
  have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => L (γ 0)) 0 1 :=
    (LipschitzWith.const (L (γ 0))).lipschitzOnWith.absolutelyContinuousOnInterval
  exact h0.add h1

lemma Data.cos_eq_one {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam) :
    Real.cos (∫ t in (0 : ℝ)..1, lam t) = 1 := by
  set z0 := γ 0
  set Θ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, lam s with hΘ
  set F : ℝ → ℝ := fun t =>
    Real.cos (Θ t) * pIL z0 (γ t) + Real.sin (Θ t) * pIL (J z0) (γ t) with hF
  have hΘac : AbsolutelyContinuousOnInterval Θ 0 1 :=
    H.lamI.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hFac : AbsolutelyContinuousOnInterval F 0 1 :=
    ((ac_comp_lip Real.lipschitzWith_cos hΘac).mul (H.ac_clm (pIL z0))).add
      ((ac_comp_lip Real.lipschitzWith_sin hΘac).mul (H.ac_clm (pIL (J z0))))
  have hder : ∀ᵐ x, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F 0 x := by
    filter_upwards [H.ae_hasDerivAt, H.lamv, H.lamI.ae_hasDerivAt_integral] with x hγ hl hΘ' hx
    have hT : HasDerivAt Θ (lam x) x := hΘ' hx 0 (by simp)
    have ha := (pIL z0).hasFDerivAt.comp_hasDerivAt x hγ
    have hb := (pIL (J z0)).hasFDerivAt.comp_hasDerivAt x hγ
    have := ((hT.cos.mul ha).add (hT.sin.mul hb))
    refine this.congr_deriv ?_
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, pIL_apply, hl, pI_smul_left,
      pI_J_J]
    rw [pI_J_left]
    ring
  obtain ⟨C, hC⟩ := hFac.const_of_ae_hasDerivAt_zero hder
  have hF0 := hC 0 (by simp)
  have hF1 := hC 1 (by simp)
  have hγ1 : γ 1 = z0 := by simpa using H.per 0
  simp only [hF, hΘ, intervalIntegral.integral_same, Real.cos_zero, Real.sin_zero, one_mul,
    zero_mul, add_zero, pIL_apply, hγ1, pI_J_self, mul_zero] at hF0 hF1
  have hR := H.sph 0
  have hr2 : 0 < r ^ 2 := pow_pos H.hr 2
  rw [← hF0, hR] at hF1
  have := mul_right_cancel₀ hr2.ne' (hF1.trans (one_mul _).symm)
  exact this

lemma Data.integral_ne_zero {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam)
    (hnc : ∃ s t, γ s ≠ γ t) : ∫ t in (0 : ℝ)..1, lam t ≠ 0 := by
  intro h0
  rw [intervalIntegral.integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae H.lam0) H.lamI] at h0
  have hz : ∀ᵐ x, x ∈ Ioc (0 : ℝ) 1 → lam x = 0 := by
    have := (ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioc)).1 h0
    filter_upwards [this] with x hx hx'
    exact hx (Or.inl hx')
  have hconst : ∀ t ∈ Icc (0 : ℝ) 1, γ t = γ 0 := by
    intro t ht
    have := H.ftc 0 t
    have hi : ∫ s in (0 : ℝ)..t, v s = ∫ s in (0 : ℝ)..t, (0 : Phase n) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hz, H.lamv] with x hx hl hxI
      rw [uIoc_of_le ht.1] at hxI
      rw [hl, hx ⟨hxI.1, hxI.2.trans ht.2⟩, zero_smul]
    rw [hi, intervalIntegral.integral_zero] at this
    exact sub_eq_zero.1 this
  have hall : ∀ s, γ s = γ 0 := by
    intro s
    have h1 : γ (s - (⌊s⌋ : ℝ) * 1) = γ s := H.per.sub_int_mul_eq ⌊s⌋
    rw [← h1]
    apply hconst
    rw [mul_one]
    exact ⟨sub_nonneg.2 (Int.floor_le s), (sub_lt_iff_lt_add'.2 (Int.lt_floor_add_one s)).le⟩
  obtain ⟨s, t, hst⟩ := hnc
  exact hst ((hall s).trans (hall t).symm)

lemma Data.lower {r : ℝ} {γ v : ℝ → Phase n} {lam : ℝ → ℝ} (H : Data r γ v lam)
    (hnc : ∃ s t, γ s ≠ γ t) : Real.pi * r ^ 2 ≤ action γ := by
  rw [H.action_eq]
  set Θ1 := ∫ t in (0 : ℝ)..1, lam t
  have hnn : 0 ≤ Θ1 := intervalIntegral.integral_nonneg_of_ae zero_le_one H.lam0
  have hne := H.integral_ne_zero hnc
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff Θ1).1 H.cos_eq_one
  have hpos : 0 < Θ1 := lt_of_le_of_ne hnn (Ne.symm hne)
  have hk1 : (1 : ℝ) ≤ k := by
    have : (0 : ℝ) < k := by
      by_contra h; push_neg at h
      nlinarith [Real.pi_pos]
    have : (0 : ℤ) < k := by exact_mod_cast this
    exact_mod_cast this
  have : 2 * Real.pi ≤ Θ1 := by rw [← hk]; nlinarith [Real.pi_pos]
  have hr2 : 0 < r ^ 2 := pow_pos H.hr 2
  nlinarith

/-- Extraction of `λ` from a generalized closed characteristic on the ball. -/
lemma data_of_gcc {r : ℝ} (hr : 0 < r) {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic (capacityBall n (Real.pi * r ^ 2)) γ) :
    ∃ v lam, Data r γ v lam := by
  obtain ⟨hper, hfr, v, hvint, hftc, hae⟩ := hγ
  have hsph : ∀ t, phaseInner (γ t) (γ t) = r ^ 2 := fun t => (mem_frontier_iff hr _).1 (hfr t)
  set lam : ℝ → ℝ := fun t => phaseInner (v t) (J (γ t)) / r ^ 2 with hlam
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hpt : ∀ᵐ t, v t = lam t • J (γ t) ∧ 0 ≤ lam t := by
    filter_upwards [hae] with t ht
    obtain ⟨u, hu, hut⟩ := ht
    rw [← hut]
    obtain ⟨h1, h2⟩ := normalCone_ball hr (hsph t) hu
    have hl : lam t = phaseInner u (γ t) / r ^ 2 := by
      show phaseInner (v t) (J (γ t)) / r ^ 2 = _
      rw [← hut, pI_J_J]
    refine ⟨?_, ?_⟩
    · rw [hl]; conv_lhs => rw [h1]
      rw [J_smul]
    · rw [hl]; positivity
  have hcont : Continuous γ := by
    have hvI : ∀ a b : ℝ, IntervalIntegrable v volume a b := fun a b =>
      (hvint.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    have : γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
      funext x; rw [← hftc 0 x]; abel
    rw [this]
    exact continuous_const.add (intervalIntegral.continuous_primitive hvI 0)
  have hJγ : ∀ t, ‖J (γ t)‖ ≤ r := by
    intro t
    have h := hsph t
    rw [pI_self] at h
    rw [norm_prod_le_iff]
    simp only [J, norm_neg]
    constructor <;> nlinarith [norm_nonneg (γ t).1, norm_nonneg (γ t).2, sq_nonneg ‖(γ t).1‖,
      sq_nonneg ‖(γ t).2‖]
  have hlamI : IntervalIntegrable lam volume 0 1 := by
    have hvI : IntervalIntegrable v volume 0 1 :=
      (hvint.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    refine (hvI.norm.const_mul (2 * r / r ^ 2)).mono_fun' ?_ ?_
    · rw [uIoc_of_le zero_le_one]
      refine Continuous.comp_aestronglyMeasurable₂
        (g := fun a b : Phase n => phaseInner a (J b) / r ^ 2)
        ?_ hvI.aestronglyMeasurable hcont.aestronglyMeasurable
      unfold phaseInner J; fun_prop
    · refine Filter.Eventually.of_forall (fun t => ?_)
      simp only [hlam, Real.norm_eq_abs, abs_div, abs_of_pos hr2]
      rw [div_le_iff₀ hr2]
      have := abs_pI_le (v t) (J (γ t))
      have h2 : 2 * ‖v t‖ * ‖J (γ t)‖ ≤ 2 * ‖v t‖ * r := by
        gcongr; exact hJγ t
      have : 2 * r / r ^ 2 * ‖v t‖ * r ^ 2 = 2 * ‖v t‖ * r := by field_simp
      linarith
  exact ⟨v, lam, ⟨hr, hper, hsph, hvint, hftc, hpt.mono (fun _ h => h.1),
    hpt.mono (fun _ h => h.2), hlamI⟩⟩

theorem main (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    cEHZ (capacityBall n (Real.pi * r ^ 2)) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  apply le_antisymm
  · refine (iInf₂_le (circ hn r) ⟨circ_gcc hn r hr, 0, 1 / 4, circ_nonconst hn r hr⟩).trans ?_
    rw [circ_action, abs_of_nonneg (by positivity)]
  · refine le_iInf₂ (fun γ hγ => ?_)
    obtain ⟨v, lam, H⟩ := data_of_gcc hr hγ.1
    apply ENNReal.ofReal_le_ofReal
    exact (H.lower hγ.2).trans (le_abs_self _)

end Viterbo.EHZBall

theorem solution (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    Viterbo.cEHZ (OAI.SymmetricPolar.capacityBall n (Real.pi * r ^ 2)) =
      ENNReal.ofReal (Real.pi * r ^ 2) :=
  Viterbo.EHZBall.main n hn r hr
