-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_10_primal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T17:14:36.982127+00:00
-- url     : https://prove2.me/submissions/8b7ef0dc-5048-413e-9052-6ce99c3a0159

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

set_option autoImplicit false

namespace E312Aux

open ProxADMMLC.Conv

theorem deriv_nonneg_of_min {F : ℝ → ℝ} {D t0 : ℝ} (ht0 : 0 < t0) (hF : HasDerivAt F D 0)
    (hmin : ∀ t ∈ Set.Icc (0:ℝ) t0, F 0 ≤ F t) : 0 ≤ D := by
  have h1 : IsLocalMinOn F (Set.Icc 0 t0) 0 := IsMinOn.localize (isMinOn_iff.mpr hmin)
  have hy : t0 ∈ posTangentConeAt (Set.Icc (0:ℝ) t0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc ht0.le]
  have h2 := h1.hasFDerivWithinAt_nonneg hF.hasFDerivAt.hasFDerivWithinAt hy
  have h3 : 0 ≤ t0 * D := h2
  by_contra h
  push Not at h
  linarith [mul_neg_of_pos_of_neg ht0 h]

/-- Conic Carathéodory: a nonnegative combination can be rewritten with a linearly
independent support. -/

theorem hd_line {n : ℕ} (x d : E n) : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x

theorem hd_f {n : ℕ} {f : E n → ℝ} (hdiff : Differentiable ℝ f) (x d : E n) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) (inner ℝ (gradient f x) d) 0 := by
  have h0 : HasFDerivAt f (InnerProductSpace.toDual ℝ (E n) (gradient f x))
      ((fun t : ℝ => x + t • d) 0) := by
    simp only [zero_smul, add_zero]
    exact (hdiff x).hasGradientAt.hasFDerivAt
  exact h0.comp_hasDerivAt (0:ℝ) (hd_line x d)

theorem hd_norm {n : ℕ} (x d z : E n) :
    HasDerivAt (fun t : ℝ => ‖x + t • d - z‖ ^ 2) (2 * inner ℝ (x - z) d) 0 := by
  have := ((hd_line x d).sub_const z).norm_sq
  simpa using this

theorem hd_A {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (x d : E n) :
    HasDerivAt (fun t : ℝ => A (x + t • d) - b) (A d) 0 := by
  have := (A.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hd_line x d)).sub_const b
  exact this

theorem hd_K {n m : ℕ} {f : E n → ℝ} (hdiff : Differentiable ℝ f) (A : E n →L[ℝ] E m)
    (b : E m) (Γ p : ℝ) (x d z : E n) (y : E m) :
    HasDerivAt (fun t : ℝ => K f A b Γ p (x + t • d) z y)
      (inner ℝ (gradient f x) d + inner ℝ y (A d) + Γ * inner ℝ (A x - b) (A d)
        + p * inner ℝ (x - z) d) 0 := by
  have h1 := hd_f hdiff x d
  have h2 : HasDerivAt (fun t : ℝ => inner ℝ y (A (x + t • d) - b)) (inner ℝ y (A d)) 0 := by
    have := (innerSL ℝ y).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hd_A A b x d)
    exact this
  have h3 := (hd_A A b x d).norm_sq
  have h4 := hd_norm x d z
  have := ((h1.add h2).add (h3.const_mul (Γ / 2))).add (h4.const_mul (p / 2))
  unfold K
  convert this using 1
  all_goals first
    | rfl
    | (simp only [zero_smul, add_zero]; ring)

theorem box_seg {n : ℕ} {ℓ u : Fin n → ℝ} {x x' : E n} (hx : x ∈ box ℓ u)
    (hx' : x' ∈ box ℓ u) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : x + t • (x' - x) ∈ box ℓ u := by
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hx i
  obtain ⟨h3, h4⟩ := hx' i
  obtain ⟨ht0, ht1⟩ := ht
  have a1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h1)
  have a2 := mul_nonneg ht0 (sub_nonneg.mpr h3)
  have a3 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h2)
  have a4 := mul_nonneg ht0 (sub_nonneg.mpr h4)
  constructor <;> nlinarith

theorem vi_xs {n m : ℕ} {f : E n → ℝ} (hdiff : Differentiable ℝ f) {A : E n →L[ℝ] E m}
    {b : E m} {ℓ u : Fin n → ℝ} {Γ p : ℝ} {xs : E m → E n → E n}
    (hxs : IsXSel f A b ℓ u Γ p xs) (y : E m) (z x' : E n) (hx' : x' ∈ box ℓ u) :
    0 ≤ inner ℝ (gradient f (xs y z)) (x' - xs y z) + inner ℝ y (A (x' - xs y z))
      + Γ * inner ℝ (A (xs y z) - b) (A (x' - xs y z))
      + p * inner ℝ (xs y z - z) (x' - xs y z) := by
  obtain ⟨hbox, hmin⟩ := hxs y z
  refine deriv_nonneg_of_min one_pos (hd_K hdiff A b Γ p (xs y z) (x' - xs y z) z y) ?_
  intro t ht
  simp only [zero_smul, add_zero]
  exact hmin _ (box_seg hbox hx' ht)

end E312Aux

namespace C37Aux

open ProxADMMLC.Conv E312Aux Filter Topology

theorem proj_coord {n : ℕ} (ℓ u : Fin n → ℝ) (q : E n) (i : Fin n) :
    (boxProj ℓ u q) i = if q i < ℓ i then ℓ i else if q i ≤ u i then q i else u i := by
  simp only [boxProj, PiLp.toLp_apply]

theorem proj_mem {n : ℕ} {ℓ u : Fin n → ℝ} (hℓu : ∀ i, ℓ i < u i) (q : E n) :
    boxProj ℓ u q ∈ box ℓ u := by
  intro i
  rw [proj_coord]
  have := hℓu i
  split_ifs with h1 h2 <;> constructor <;> (try push Not at *) <;> linarith

theorem proj_ineq {n : ℕ} (ℓ u : Fin n → ℝ) (q v : E n) (hv : v ∈ box ℓ u) :
    inner ℝ (q - boxProj ℓ u q) (v - boxProj ℓ u q) ≤ 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_nonpos (fun i _ => ?_)
  simp only [PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
  rw [proj_coord]
  obtain ⟨hv1, hv2⟩ := hv i
  split_ifs with h1 h2
  · nlinarith
  · simp
  · push Not at h1 h2
    nlinarith

theorem proj_sign {n : ℕ} (ℓ u : Fin n → ℝ) (q : E n) (i : Fin n) :
    (q i < (boxProj ℓ u q) i → (boxProj ℓ u q) i = ℓ i) ∧
    ((boxProj ℓ u q) i < q i → (boxProj ℓ u q) i = u i) := by
  rw [proj_coord]
  split_ifs with h1 h2 <;> constructor <;> intro h <;> first | rfl | (exfalso; linarith)

theorem gradK_sub {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p : ℝ)
    (x x' z : E n) (y : E m) :
    gradK f A b Γ p x z y - gradK f A b Γ p x' z y
      = (gradient f x - gradient f x') + Γ • (ContinuousLinearMap.adjoint A) (A (x - x'))
        + p • (x - x') := by
  unfold gradK
  simp only [map_sub]
  module

theorem vi_gradK {n m : ℕ} {f : E n → ℝ} (hdiff : Differentiable ℝ f) {A : E n →L[ℝ] E m}
    {b : E m} {ℓ u : Fin n → ℝ} {Γ p : ℝ} {xs : E m → E n → E n}
    (hxs : IsXSel f A b ℓ u Γ p xs) (y : E m) (z x' : E n) (hx' : x' ∈ box ℓ u) :
    0 ≤ inner ℝ (gradK f A b Γ p (xs y z) z y) (x' - xs y z) := by
  have h := vi_xs hdiff hxs y z x' hx'
  unfold gradK
  simp only [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  linarith

theorem mono_gradK {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m}
    {ℓ u : Fin n → ℝ} {γ Γ p : ℝ} (hγ : MonoConst f ℓ u γ) (hΓ : 0 ≤ Γ) (z : E n) (y : E m)
    (x x' : E n) (hx : x ∈ box ℓ u) (hx' : x' ∈ box ℓ u) :
    (p + γ) * ‖x - x'‖ ^ 2
      ≤ inner ℝ (gradK f A b Γ p x z y - gradK f A b Γ p x' z y) (x - x') := by
  rw [gradK_sub]
  simp only [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]
  have h1 := hγ x hx x' hx'
  have h2 : 0 ≤ Γ * ‖A (x - x')‖ ^ 2 := by positivity
  linarith

theorem lip_gradK {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m}
    {ℓ u : Fin n → ℝ} {L Γ p : ℝ}
    (hlip : ∀ x ∈ box ℓ u, ∀ x' ∈ box ℓ u, ‖gradient f x - gradient f x'‖ ≤ L * ‖x - x'‖)
    (hΓ : 0 ≤ Γ) (hp : 0 ≤ p) (z : E n) (y : E m)
    (x x' : E n) (hx : x ∈ box ℓ u) (hx' : x' ∈ box ℓ u) :
    ‖gradK f A b Γ p x z y - gradK f A b Γ p x' z y‖
      ≤ (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) * ‖x - x'‖ := by
  rw [gradK_sub]
  have h1 := hlip x hx x' hx'
  have h2 : ‖Γ • (ContinuousLinearMap.adjoint A) (A (x - x'))‖
      ≤ Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) * ‖x - x'‖ := by
    rw [norm_smul, Real.norm_of_nonneg hΓ]
    have h3 := (ContinuousLinearMap.adjoint A).le_opNorm (A (x - x'))
    have h4 := A.le_opNorm (x - x')
    have h5 : ‖(ContinuousLinearMap.adjoint A) (A (x - x'))‖
        ≤ ‖ContinuousLinearMap.adjoint A‖ * (‖A‖ * ‖x - x'‖) :=
      h3.trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
    calc Γ * ‖(ContinuousLinearMap.adjoint A) (A (x - x'))‖
        ≤ Γ * (‖ContinuousLinearMap.adjoint A‖ * (‖A‖ * ‖x - x'‖)) :=
          mul_le_mul_of_nonneg_left h5 hΓ
      _ = Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) * ‖x - x'‖ := by ring
  have h3 : ‖p • (x - x')‖ = p * ‖x - x'‖ := by rw [norm_smul, Real.norm_of_nonneg hp]
  have h6 := norm_add_le ((gradient f x - gradient f x')
    + Γ • (ContinuousLinearMap.adjoint A) (A (x - x'))) (p • (x - x'))
  have h7 := norm_add_le (gradient f x - gradient f x')
    (Γ • (ContinuousLinearMap.adjoint A) (A (x - x')))
  linarith

end C37Aux

namespace L310Aux

open ProxADMMLC.Conv E312Aux C37Aux

theorem hdK_at {n m : ℕ} {f : E n → ℝ} (hdiff : Differentiable ℝ f) (A : E n →L[ℝ] E m)
    (b : E m) (Γ p : ℝ) (a d z : E n) (y : E m) (s : ℝ) :
    HasDerivAt (fun t : ℝ => K f A b Γ p (a + t • d) z y)
      (inner ℝ (gradK f A b Γ p (a + s • d) z y) d) s := by
  have h0 := hd_K hdiff A b Γ p (a + s • d) d z y
  have e : inner ℝ (gradK f A b Γ p (a + s • d) z y) d
      = inner ℝ (gradient f (a + s • d)) d + inner ℝ y (A d)
        + Γ * inner ℝ (A (a + s • d) - b) (A d) + p * inner ℝ (a + s • d - z) d := by
    unfold gradK
    simp only [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  rw [e]
  have h0' : HasDerivAt (fun t : ℝ => K f A b Γ p (a + s • d + t • d) z y)
      (inner ℝ (gradient f (a + s • d)) d + inner ℝ y (A d)
        + Γ * inner ℝ (A (a + s • d) - b) (A d) + p * inner ℝ (a + s • d - z) d) (s - s) := by
    rw [sub_self]; exact h0
  have h1 := h0'.comp_sub_const s s
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show K f A b Γ p (a + t • d) z y = K f A b Γ p (a + s • d + (t - s) • d) z y
  rw [show a + s • d + (t - s) • d = a + t • d by module]

/-- Descent inequality for `K(·, z; y)` on the box. -/
theorem K_ub {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    {L Γ p : ℝ} (hf : Assump22c f ℓ u L) (hΓ : 0 ≤ Γ) (hp : 0 ≤ p) (z : E n) (y : E m)
    {a w : E n} (ha : a ∈ box ℓ u) (hw : w ∈ box ℓ u) :
    K f A b Γ p w z y ≤ K f A b Γ p a z y + inner ℝ (gradK f A b Γ p a z y) (w - a)
      + (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) / 2 * ‖w - a‖ ^ 2 := by
  obtain ⟨hdiff, _, hlip⟩ := hf
  obtain ⟨LK, hLK⟩ : ∃ LK, LK = L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p :=
    ⟨_, rfl⟩
  rw [← hLK]
  let φ : ℝ → ℝ := fun s => K f A b Γ p (a + s • (w - a)) z y
    - s * inner ℝ (gradK f A b Γ p a z y) (w - a) - LK / 2 * (s * s) * ‖w - a‖ ^ 2
  have hφ : ∀ s : ℝ, HasDerivAt φ
      (inner ℝ (gradK f A b Γ p (a + s • (w - a)) z y) (w - a)
        - 1 * inner ℝ (gradK f A b Γ p a z y) (w - a)
        - LK / 2 * (1 * s + s * 1) * ‖w - a‖ ^ 2) s := by
    intro s
    have h1 := hdK_at hdiff A b Γ p a (w - a) z y s
    have h2 := (hasDerivAt_id' s).mul_const (inner ℝ (gradK f A b Γ p a z y) (w - a))
    have h3 := (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul (LK / 2)).mul_const
      (‖w - a‖ ^ 2)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun s _ => (hφ s).continuousAt.continuousWithinAt
    · intro s _
      exact (hφ s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsb : a + s • (w - a) ∈ box ℓ u := box_seg ha hw ⟨hs.1.le, hs.2.le⟩
      have hl := lip_gradK (A := A) (b := b) hlip hΓ hp z y _ _ hsb ha
      rw [← hLK] at hl
      have e : a + s • (w - a) - a = s • (w - a) := by abel
      rw [e, norm_smul, Real.norm_of_nonneg hs.1.le] at hl
      have hcs := real_inner_le_norm
        (gradK f A b Γ p (a + s • (w - a)) z y - gradK f A b Γ p a z y) (w - a)
      rw [inner_sub_left] at hcs
      have h4 := mul_le_mul_of_nonneg_right hl (norm_nonneg (w - a))
      have h5 : LK * (s * ‖w - a‖) * ‖w - a‖ = LK / 2 * (1 * s + s * 1) * ‖w - a‖ ^ 2 := by
        ring
      linarith
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : a + (1:ℝ) • (w - a) = w := by simp
  have e0 : a + (0:ℝ) • (w - a) = a := by simp
  simp only [φ] at h
  rw [e1, e0] at h
  linarith

/-- Strong convexity of `K(·, z; y)` on the box with modulus `p + γ`. -/
theorem K_lb {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    {γ Γ p : ℝ} (hdiff : Differentiable ℝ f) (hγ : MonoConst f ℓ u γ) (hΓ : 0 ≤ Γ)
    (z : E n) (y : E m) {a w : E n} (ha : a ∈ box ℓ u) (hw : w ∈ box ℓ u) :
    K f A b Γ p a z y + inner ℝ (gradK f A b Γ p a z y) (w - a) + (p + γ) / 2 * ‖w - a‖ ^ 2
      ≤ K f A b Γ p w z y := by
  let φ : ℝ → ℝ := fun s => K f A b Γ p (a + s • (w - a)) z y
    - s * inner ℝ (gradK f A b Γ p a z y) (w - a) - (p + γ) / 2 * (s * s) * ‖w - a‖ ^ 2
  have hφ : ∀ s : ℝ, HasDerivAt φ
      (inner ℝ (gradK f A b Γ p (a + s • (w - a)) z y) (w - a)
        - 1 * inner ℝ (gradK f A b Γ p a z y) (w - a)
        - (p + γ) / 2 * (1 * s + s * 1) * ‖w - a‖ ^ 2) s := by
    intro s
    have h1 := hdK_at hdiff A b Γ p a (w - a) z y s
    have h2 := (hasDerivAt_id' s).mul_const (inner ℝ (gradK f A b Γ p a z y) (w - a))
    have h3 := (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul ((p + γ) / 2)).mul_const
      (‖w - a‖ ^ 2)
    exact (h1.sub h2).sub h3
  have hmono : MonotoneOn φ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · exact fun s _ => (hφ s).continuousAt.continuousWithinAt
    · intro s _
      exact (hφ s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsb : a + s • (w - a) ∈ box ℓ u := box_seg ha hw ⟨hs.1.le, hs.2.le⟩
      have hm := mono_gradK (A := A) (b := b) (p := p) hγ hΓ z y _ _ hsb ha
      have e : a + s • (w - a) - a = s • (w - a) := by abel
      rw [e, norm_smul, Real.norm_of_nonneg hs.1.le, real_inner_smul_right,
        inner_sub_left] at hm
      obtain ⟨I1, hI1⟩ : ∃ I1, I1 = inner ℝ (gradK f A b Γ p (a + s • (w - a)) z y) (w - a) :=
        ⟨_, rfl⟩
      obtain ⟨I0, hI0⟩ : ∃ I0, I0 = inner ℝ (gradK f A b Γ p a z y) (w - a) := ⟨_, rfl⟩
      rw [← hI1, ← hI0] at hm ⊢
      have k : 0 ≤ s * (I1 - I0 - (p + γ) * s * ‖w - a‖ ^ 2) := by
        have e2 : s * (I1 - I0 - (p + γ) * s * ‖w - a‖ ^ 2)
            = s * (I1 - I0) - (p + γ) * (s * ‖w - a‖) ^ 2 := by ring
        rw [e2]; linarith
      have k2 := (mul_nonneg_iff_of_pos_left hs.1).mp k
      have e3 : (p + γ) / 2 * (1 * s + s * 1) * ‖w - a‖ ^ 2 = (p + γ) * s * ‖w - a‖ ^ 2 := by
        ring
      rw [e3]
      linarith
  have h := hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : a + (1:ℝ) • (w - a) = w := by simp
  have e0 : a + (0:ℝ) • (w - a) = a := by simp
  simp only [φ] at h
  rw [e1, e0] at h
  linarith

/-- Local co-coercivity (Nesterov, Thm 2.1.5 argument) on a set `S`. -/
theorem nest {n : ℕ} (h : E n → ℝ) (T : E n → E n) (S : Set (E n)) {M : ℝ} (hM : 0 < M)
    (hC : ∀ a ∈ S, ∀ w ∈ S, h a + inner ℝ (T a) (w - a) ≤ h w)
    (hU : ∀ a ∈ S, ∀ w ∈ S, h w ≤ h a + inner ℝ (T a) (w - a) + M / 2 * ‖w - a‖ ^ 2)
    {a b : E n} (ha : a ∈ S) (hb : b ∈ S) (h1 : b - M⁻¹ • (T b - T a) ∈ S)
    (h2 : a + M⁻¹ • (T b - T a) ∈ S) :
    ‖T b - T a‖ ≤ M * ‖b - a‖ := by
  obtain ⟨v, hv⟩ : ∃ v, v = T b - T a := ⟨_, rfl⟩
  rw [← hv] at h1 h2 ⊢
  have c1 := hC a ha _ h1
  have u1 := hU b hb _ h1
  have c2 := hC b hb _ h2
  have u2 := hU a ha _ h2
  have e1 : b - M⁻¹ • v - a = (b - a) - M⁻¹ • v := by abel
  have e2 : b - M⁻¹ • v - b = -(M⁻¹ • v) := by abel
  have e3 : a + M⁻¹ • v - b = -(b - a) + M⁻¹ • v := by abel
  have e4 : a + M⁻¹ • v - a = M⁻¹ • v := by abel
  rw [e1, inner_sub_right, real_inner_smul_right] at c1
  rw [e2, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul] at u1
  rw [e3, inner_add_right, inner_neg_right, real_inner_smul_right] at c2
  rw [e4, real_inner_smul_right, norm_smul] at u2
  have hn : ‖M⁻¹‖ = M⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr hM.le)
  rw [hn] at u1 u2
  have hMi := mul_inv_cancel₀ hM.ne'
  have hq : M / 2 * (M⁻¹ * ‖v‖) ^ 2 = M⁻¹ / 2 * ‖v‖ ^ 2 := by
    calc M / 2 * (M⁻¹ * ‖v‖) ^ 2 = (M * M⁻¹) * (M⁻¹ / 2 * ‖v‖ ^ 2) := by ring
      _ = M⁻¹ / 2 * ‖v‖ ^ 2 := by rw [hMi, one_mul]
  rw [hq] at u1 u2
  have hvv : inner ℝ (T b) v - inner ℝ (T a) v = ‖v‖ ^ 2 := by
    rw [← inner_sub_left, ← hv, real_inner_self_eq_norm_sq]
  have k : M⁻¹ * inner ℝ (T b) v - M⁻¹ * inner ℝ (T a) v = M⁻¹ * ‖v‖ ^ 2 := by
    rw [← mul_sub, hvv]
  have hvb : inner ℝ v (b - a) = inner ℝ (T b) (b - a) - inner ℝ (T a) (b - a) := by
    rw [hv, inner_sub_left]
  have key : M⁻¹ * ‖v‖ ^ 2 ≤ inner ℝ v (b - a) := by linarith
  have hcs := real_inner_le_norm v (b - a)
  have key2 : ‖v‖ ^ 2 ≤ M * (‖v‖ * ‖b - a‖) := by
    have := mul_le_mul_of_nonneg_left (key.trans hcs) hM.le
    calc ‖v‖ ^ 2 = (M * M⁻¹) * ‖v‖ ^ 2 := by rw [hMi, one_mul]
      _ = M * (M⁻¹ * ‖v‖ ^ 2) := by ring
      _ ≤ M * (‖v‖ * ‖b - a‖) := this
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hM.le (norm_nonneg _)
  · have k3 : ‖v‖ * ‖v‖ ≤ (M * ‖b - a‖) * ‖v‖ := by
      calc ‖v‖ * ‖v‖ = ‖v‖ ^ 2 := by ring
        _ ≤ M * (‖v‖ * ‖b - a‖) := key2
        _ = (M * ‖b - a‖) * ‖v‖ := by ring
    exact le_of_mul_le_mul_right k3 hpos

/-- Locally Lipschitz along `[0,1]` implies Lipschitz between the endpoints. -/
theorem chain {n : ℕ} (P : ℝ → E n) (C η : ℝ) (hη : 0 < η)
    (hloc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → t - s ≤ η → ‖P t - P s‖ ≤ C * (t - s)) :
    ‖P 1 - P 0‖ ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNpos : (0:ℝ) < N := lt_trans (by positivity) hN
  have hstep : 1 / (N:ℝ) ≤ η := by
    rw [div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hη] at hN
    linarith
  have hinv : (0:ℝ) < 1 / N := one_div_pos.mpr hNpos
  have key : ∀ k : ℕ, k ≤ N → ‖P (k / N) - P 0‖ ≤ C * (k / N) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (Nat.le_of_succ_le hk)
      have h0 : (0:ℝ) ≤ k / N := by positivity
      have e : ((k + 1 : ℕ) : ℝ) / N = k / N + 1 / N := by push_cast; ring
      have hle : ((k + 1 : ℕ) : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hk
      rw [e] at hle ⊢
      have hl := hloc (k / N) (k / N + 1 / N) h0 (by linarith) hle (by linarith)
      have tri := norm_sub_le_norm_sub_add_norm_sub (P (k / N + 1 / N)) (P (k / N)) (P 0)
      have e2 : (k:ℝ) / N + 1 / N - k / N = 1 / N := by ring
      rw [e2] at hl
      have e3 : C * ((k:ℝ) / N + 1 / N) = C * (k / N) + C * (1 / N) := by ring
      linarith
  have := key N le_rfl
  rwa [div_self hNpos.ne', mul_one] at this

/-- `w` is `δ`-inside the box. -/
def Inn {n : ℕ} (ℓ u : Fin n → ℝ) (δ : ℝ) (w : E n) : Prop :=
  ∀ i, ℓ i + δ ≤ w i ∧ w i + δ ≤ u i

theorem inn_ball {n : ℕ} {ℓ u : Fin n → ℝ} {δ : ℝ} {q w : E n} (hq : Inn ℓ u δ q)
    (hw : ‖w - q‖ ≤ δ) : w ∈ box ℓ u := by
  intro i
  have h1 : |w i - q i| ≤ δ := by
    have := PiLp.norm_apply_le (w - q) i
    rw [PiLp.sub_apply, Real.norm_eq_abs] at this
    linarith
  obtain ⟨a1, a2⟩ := hq i
  have := abs_le.mp h1
  constructor <;> linarith

theorem inn_box {n : ℕ} {ℓ u : Fin n → ℝ} {δ : ℝ} {q : E n} (hq : Inn ℓ u δ q)
    (hδ : 0 ≤ δ) : q ∈ box ℓ u := by
  intro i
  obtain ⟨a1, a2⟩ := hq i
  constructor <;> linarith

theorem inn_seg {n : ℕ} {ℓ u : Fin n → ℝ} {δ : ℝ} {x x' : E n} (hx : Inn ℓ u δ x)
    (hx' : Inn ℓ u δ x') {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Inn ℓ u δ (x + t • (x' - x)) := by
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hx i
  obtain ⟨h3, h4⟩ := hx' i
  have a1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h1)
  have a2 := mul_nonneg ht0 (sub_nonneg.mpr h3)
  have a3 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h2)
  have a4 := mul_nonneg ht0 (sub_nonneg.mpr h4)
  constructor <;> nlinarith

theorem exists_rho {n : ℕ} {ℓ u : Fin n → ℝ} (hℓu : ∀ i, ℓ i < u i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ (u i - ℓ i) / 2 := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image (fun i => (u i - ℓ i) / 2))
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  refine ⟨s.min' hs, ?_, fun i => Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
  rw [Finset.lt_min'_iff]
  intro r hr
  rcases Finset.mem_insert.mp hr with h | h
  · rw [h]; norm_num
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    have := hℓu i
    linarith

theorem shrink {n : ℕ} {ℓ u : Fin n → ℝ} {ρ : ℝ} (hρ : ∀ i, ρ ≤ (u i - ℓ i) / 2) {x : E n}
    (hx : x ∈ box ℓ u) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Inn ℓ u (ε * ρ) (x + ε • (WithLp.toLp 2 (fun i => (ℓ i + u i) / 2) - x)) := by
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hx i
  have hr := hρ i
  have a1 := mul_nonneg (sub_nonneg.mpr hε1) (sub_nonneg.mpr h1)
  have a2 := mul_nonneg (sub_nonneg.mpr hε1) (sub_nonneg.mpr h2)
  have a3 := mul_nonneg hε0 (sub_nonneg.mpr hr)
  constructor <;> nlinarith

/-- The gradient step `T w = w − c ∇ₓK(w)` is `2`-Lipschitz on the box. -/
theorem T_lip {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    {L Γ p c : ℝ} (hf : Assump22c f ℓ u L) (hΓ : 0 ≤ Γ) (hp : 0 ≤ p) (hc : 0 < c)
    (hcL : c * (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) < 1) (z : E n) (y : E m)
    {q w : E n} (hq : q ∈ box ℓ u) (hw : w ∈ box ℓ u) :
    ‖(w - c • gradK f A b Γ p w z y) - (q - c • gradK f A b Γ p q z y)‖ ≤ 2 * ‖w - q‖ := by
  have hl := lip_gradK (A := A) (b := b) hf.2.2 hΓ hp z y w q hw hq
  have e : (w - c • gradK f A b Γ p w z y) - (q - c • gradK f A b Γ p q z y)
      = (w - q) - c • (gradK f A b Γ p w z y - gradK f A b Γ p q z y) := by
    rw [smul_sub]; abel
  rw [e]
  have h1 := norm_sub_le (w - q) (c • (gradK f A b Γ p w z y - gradK f A b Γ p q z y))
  rw [norm_smul, Real.norm_of_nonneg hc.le] at h1
  have h2 := mul_le_mul_of_nonneg_left hl hc.le
  have h3 : c * ((L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) * ‖w - q‖)
      ≤ ‖w - q‖ := by
    have := mul_le_mul_of_nonneg_right hcL.le (norm_nonneg (w - q))
    calc _ = c * (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) * ‖w - q‖ := by ring
      _ ≤ 1 * ‖w - q‖ := this
      _ = ‖w - q‖ := one_mul _
  linarith

/-- Contraction of the gradient step between two `δ`-inner points. -/
theorem contr_loc {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    {L γ Γ p c : ℝ} (hf : Assump22c f ℓ u L) (hγ : MonoConst f ℓ u γ) (hΓ : 0 ≤ Γ)
    (hp : 0 ≤ p) (hc : 0 < c)
    (hcL : c * (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) < 1)
    (hM : 0 < 1 - c * (p + γ)) (z : E n) (y : E m) {δ : ℝ} (hδ : 0 < δ) {x1 x2 : E n}
    (h1 : Inn ℓ u δ x1) (h2 : Inn ℓ u δ x2) (h12 : 2 * ‖x2 - x1‖ ≤ δ * (1 - c * (p + γ))) :
    ‖(x2 - c • gradK f A b Γ p x2 z y) - (x1 - c • gradK f A b Γ p x1 z y)‖
      ≤ (1 - c * (p + γ)) * ‖x2 - x1‖ := by
  have hb1 := inn_box h1 hδ.le
  have hb2 := inn_box h2 hδ.le
  have hT := T_lip (A := A) (b := b) hf hΓ hp hc hcL z y hb1 hb2
  obtain ⟨M, hMdef⟩ : ∃ M, M = 1 - c * (p + γ) := ⟨_, rfl⟩
  rw [← hMdef] at hM h12 ⊢
  have hsmall : M⁻¹ * ‖(x2 - c • gradK f A b Γ p x2 z y) - (x1 - c • gradK f A b Γ p x1 z y)‖
      ≤ δ := by
    rw [inv_mul_le_iff₀ hM]
    linarith
  refine nest (fun w => ‖w‖ ^ 2 / 2 - c * K f A b Γ p w z y)
    (fun w => w - c • gradK f A b Γ p w z y) (box ℓ u) hM ?_ ?_ hb1 hb2 ?_ ?_
  · intro a ha w hw
    have hk := K_ub (A := A) (b := b) hf hΓ hp z y ha hw
    have hsq : ‖w‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a (w - a) + ‖w - a‖ ^ 2 := by
      have := norm_add_sq_real a (w - a)
      rwa [add_sub_cancel] at this
    rw [inner_sub_left, real_inner_smul_left]
    have hk2 := mul_le_mul_of_nonneg_left hk hc.le
    have hd : 0 ≤ ‖w - a‖ ^ 2 := by positivity
    have hk3 := mul_le_mul_of_nonneg_right hcL.le hd
    linarith
  · intro a ha w hw
    have hk := K_lb (A := A) (b := b) (p := p) hf.1 hγ hΓ z y ha hw
    have hsq : ‖w‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a (w - a) + ‖w - a‖ ^ 2 := by
      have := norm_add_sq_real a (w - a)
      rwa [add_sub_cancel] at this
    rw [inner_sub_left, real_inner_smul_left]
    have hk2 := mul_le_mul_of_nonneg_left hk hc.le
    rw [hMdef]
    linarith
  · apply inn_ball h2
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hM.le)]
    exact hsmall
  · apply inn_ball h1
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hM.le)]
    exact hsmall

/-- Contraction between two `δ`-inner points, any distance apart (chaining). -/
theorem contr_inn {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    {L γ Γ p c : ℝ} (hf : Assump22c f ℓ u L) (hγ : MonoConst f ℓ u γ) (hΓ : 0 ≤ Γ)
    (hp : 0 ≤ p) (hc : 0 < c)
    (hcL : c * (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) < 1)
    (hM : 0 < 1 - c * (p + γ)) (z : E n) (y : E m) {δ : ℝ} (hδ : 0 < δ) {x1 x2 : E n}
    (h1 : Inn ℓ u δ x1) (h2 : Inn ℓ u δ x2) :
    ‖(x2 - c • gradK f A b Γ p x2 z y) - (x1 - c • gradK f A b Γ p x1 z y)‖
      ≤ (1 - c * (p + γ)) * ‖x2 - x1‖ := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = 1 - c * (p + γ) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = x2 - x1 := ⟨_, rfl⟩
  have hD : 0 < ‖d‖ + 1 := by positivity
  let P : ℝ → E n := fun s =>
    (x1 + s • d) - c • gradK f A b Γ p (x1 + s • d) z y
  have hη : 0 < δ * M / (2 * (‖d‖ + 1)) := by rw [← hMdef] at hM; positivity
  have hch := chain P (M * ‖d‖) _ hη (by
    intro s t hs hst ht1 hts
    have hp1 := inn_seg h1 h2 hs (hst.trans ht1)
    have hp2 := inn_seg h1 h2 (hs.trans hst) ht1
    rw [← hd] at hp1 hp2
    have e : x1 + t • d - (x1 + s • d) = (t - s) • d := by module
    have hn : ‖x1 + t • d - (x1 + s • d)‖ = (t - s) * ‖d‖ := by
      rw [e, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hst)]
    have hsm : 2 * ‖x1 + t • d - (x1 + s • d)‖ ≤ δ * (1 - c * (p + γ)) := by
      rw [hn, ← hMdef]
      have k1 := mul_le_mul_of_nonneg_right hts (norm_nonneg d)
      have k2 : δ * M / (2 * (‖d‖ + 1)) * ‖d‖ ≤ δ * M / (2 * (‖d‖ + 1)) * (‖d‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hη.le
      have k3 : δ * M / (2 * (‖d‖ + 1)) * (‖d‖ + 1) = δ * M / 2 := by
        field_simp
      linarith
    have := contr_loc (A := A) (b := b) hf hγ hΓ hp hc hcL hM z y hδ hp1 hp2 hsm
    rw [hn, ← hMdef] at this
    calc ‖P t - P s‖ ≤ M * ((t - s) * ‖d‖) := this
      _ = M * ‖d‖ * (t - s) := by ring)
  have e1 : P 1 = x2 - c • gradK f A b Γ p x2 z y := by
    simp only [P, one_smul, hd, add_sub_cancel]
  have e0 : P 0 = x1 - c • gradK f A b Γ p x1 z y := by
    simp only [P, zero_smul, add_zero]
  rw [e1, e0] at hch
  rw [← hMdef, ← hd]
  exact hch

/-- Contraction of the gradient step on the whole box (limit from inner points). -/
theorem contr_box {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    (hℓu : ∀ i, ℓ i < u i) {L γ Γ p c : ℝ} (hf : Assump22c f ℓ u L) (hγ : MonoConst f ℓ u γ)
    (hΓ : 0 ≤ Γ) (hp : 0 ≤ p) (hc : 0 < c)
    (hcL : c * (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) < 1)
    (hM : 0 < 1 - c * (p + γ)) (z : E n) (y : E m) {x1 x2 : E n}
    (h1 : x1 ∈ box ℓ u) (h2 : x2 ∈ box ℓ u) :
    ‖(x2 - c • gradK f A b Γ p x2 z y) - (x1 - c • gradK f A b Γ p x1 z y)‖
      ≤ (1 - c * (p + γ)) * ‖x2 - x1‖ := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_rho hℓu
  obtain ⟨cen, hcen⟩ : ∃ cen : E n, cen = WithLp.toLp 2 (fun i => (ℓ i + u i) / 2) :=
    ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = 1 - c * (p + γ) := ⟨_, rfl⟩
  let T : E n → E n := fun w => w - c • gradK f A b Γ p w z y
  show ‖T x2 - T x1‖ ≤ (1 - c * (p + γ)) * ‖x2 - x1‖
  rw [← hMdef]
  obtain ⟨B, hB⟩ : ∃ B, B = 2 * ‖cen - x1‖ + 2 * ‖cen - x2‖ + 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min 1 (e / B) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min one_pos (div_pos he hB0)
  have hε1 : ε ≤ 1 := hε ▸ min_le_left _ _
  have hεB : ε * B ≤ e := by
    have : ε ≤ e / B := hε ▸ min_le_right _ _
    calc ε * B ≤ e / B * B := mul_le_mul_of_nonneg_right this hB0.le
      _ = e := div_mul_cancel₀ e hB0.ne'
  have i1 := shrink hρ h1 hε0.le hε1
  have i2 := shrink hρ h2 hε0.le hε1
  rw [← hcen] at i1 i2
  have hδ : 0 < ε * ρ := mul_pos hε0 hρ0
  have hc12 := contr_inn (A := A) (b := b) hf hγ hΓ hp hc hcL hM z y hδ i1 i2
  rw [← hMdef] at hc12 hM
  have j1 := T_lip (A := A) (b := b) hf hΓ hp hc hcL z y (inn_box i1 hδ.le) h1
  have j2 := T_lip (A := A) (b := b) hf hΓ hp hc hcL z y (inn_box i2 hδ.le) h2
  have n1 : ‖x1 - (x1 + ε • (cen - x1))‖ = ε * ‖cen - x1‖ := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hε0.le]
  have n2 : ‖x2 - (x2 + ε • (cen - x2))‖ = ε * ‖cen - x2‖ := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hε0.le]
  have n12 : ‖(x2 + ε • (cen - x2)) - (x1 + ε • (cen - x1))‖ = (1 - ε) * ‖x2 - x1‖ := by
    have : (x2 + ε • (cen - x2)) - (x1 + ε • (cen - x1)) = (1 - ε) • (x2 - x1) := by module
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
  rw [n1] at j1
  rw [n2] at j2
  rw [n12] at hc12
  have tri1 := norm_sub_le_norm_sub_add_norm_sub (T x2) (T (x2 + ε • (cen - x2))) (T x1)
  have tri2 := norm_sub_le_norm_sub_add_norm_sub (T (x2 + ε • (cen - x2)))
    (T (x1 + ε • (cen - x1))) (T x1)
  have hj1 : ‖T (x1 + ε • (cen - x1)) - T x1‖ ≤ 2 * (ε * ‖cen - x1‖) := by
    rw [norm_sub_rev]; exact j1
  have hj2 : ‖T x2 - T (x2 + ε • (cen - x2))‖ ≤ 2 * (ε * ‖cen - x2‖) := j2
  have hc12' : ‖T (x2 + ε • (cen - x2)) - T (x1 + ε • (cen - x1))‖ ≤ M * ((1 - ε) * ‖x2 - x1‖) :=
    hc12
  have k1 : M * ((1 - ε) * ‖x2 - x1‖) ≤ M * ‖x2 - x1‖ := by
    apply mul_le_mul_of_nonneg_left _ hM.le
    have := norm_nonneg (x2 - x1)
    nlinarith
  have k2 : 2 * (ε * ‖cen - x1‖) + 2 * (ε * ‖cen - x2‖) ≤ ε * B := by
    rw [hB]; nlinarith
  linarith

end L310Aux

open ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L)
    (γ : ℝ) (hγ : MonoConst f ℓ u γ) (Γ p c α β : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    ∀ t, c * (p + γ) * ‖x t - xs (y (t + 1)) (z t)‖ ≤ ‖x (t + 1) - x t‖ ∧
      c * (p + γ) / (1 + c * (p + γ)) * ‖x (t + 1) - xs (y (t + 1)) (z t)‖ ≤
        ‖x (t + 1) - x t‖ := by
  obtain ⟨hx0, _, hstep⟩ := hrun
  have hxt : ∀ t, x t ∈ box ℓ u := by
    intro t
    induction t with
    | zero => exact hx0
    | succ k _ =>
      rw [(hstep k).2.1]
      exact C37Aux.proj_mem hℓu _
  intro t
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : ∀ v : E 0, ‖v‖ = 0 := fun v => by rw [EuclideanSpace.norm_eq]; simp
    simp only [hz, mul_zero, le_refl, and_self]
  obtain ⟨hdiff, hL, hlip⟩ := hf
  have hadj : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint A
  have hcL' : c * (L + Γ * (‖ContinuousLinearMap.adjoint A‖ * ‖A‖) + p) < 1 := by
    rw [hadj]
    have e : L + Γ * (‖A‖ * ‖A‖) + p = L + p + Γ * ‖A‖ ^ 2 := by ring
    rw [e]; exact hcL
  have hγL : γ ≤ L := by
    obtain ⟨a1, ha1d⟩ : ∃ a1 : E n, a1 = WithLp.toLp 2 ℓ := ⟨_, rfl⟩
    obtain ⟨a2, ha2d⟩ : ∃ a2 : E n, a2 = WithLp.toLp 2 u := ⟨_, rfl⟩
    have ha1 : a1 ∈ box ℓ u := fun i => by
      rw [ha1d, PiLp.toLp_apply]; exact ⟨le_refl _, (hℓu i).le⟩
    have ha2 : a2 ∈ box ℓ u := fun i => by
      rw [ha2d, PiLp.toLp_apply]; exact ⟨(hℓu i).le, le_refl _⟩
    have hd : 0 < ‖a1 - a2‖ := by
      rw [norm_pos_iff]
      intro h
      have h0 := congrArg (fun v : E n => v ⟨0, hn⟩) h
      simp only [ha1d, ha2d, PiLp.sub_apply, PiLp.zero_apply] at h0
      have := hℓu ⟨0, hn⟩
      linarith
    have h1 := hγ a1 ha1 a2 ha2
    have h2 := real_inner_le_norm (gradient f a1 - gradient f a2) (a1 - a2)
    have h3 := mul_le_mul_of_nonneg_right (hlip a1 ha1 a2 ha2) (norm_nonneg (a1 - a2))
    have e : L * ‖a1 - a2‖ * ‖a1 - a2‖ = L * ‖a1 - a2‖ ^ 2 := by ring
    have h4 : γ * ‖a1 - a2‖ ^ 2 ≤ L * ‖a1 - a2‖ ^ 2 := by linarith
    exact le_of_mul_le_mul_right h4 (by positivity)
  have hM : 0 < 1 - c * (p + γ) := by
    have k1 : c * (p + γ) ≤ c * (p + L) := mul_le_mul_of_nonneg_left (by linarith) hc.le
    have k2 : 0 ≤ c * (Γ * ‖A‖ ^ 2) := by positivity
    have k3 : c * (L + p + Γ * ‖A‖ ^ 2) = c * (p + L) + c * (Γ * ‖A‖ ^ 2) := by ring
    linarith
  obtain ⟨_, hxx, _⟩ := hstep t
  obtain ⟨X, hX⟩ : ∃ X, X = x t := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1, X1 = x (t + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = y (t + 1) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = z t := ⟨_, rfl⟩
  have hXb : X ∈ box ℓ u := hX ▸ hxt t
  have hX1b : X1 ∈ box ℓ u := hX1 ▸ hxt (t + 1)
  rw [← hX, ← hX1, ← hY, ← hZ] at hxx
  rw [← hX, ← hX1, ← hY, ← hZ]
  obtain ⟨xb, hxbd⟩ : ∃ xb, xb = xs Y Z := ⟨_, rfl⟩
  rw [← hxbd]
  have hxb : xb ∈ box ℓ u := hxbd ▸ (hxs Y Z).1
  have hproj := C37Aux.proj_ineq ℓ u (X - c • gradK f A b Γ p X Z Y) xb hxb
  rw [← hxx] at hproj
  have hvi : 0 ≤ inner ℝ (gradK f A b Γ p xb Z Y) (X1 - xb) := by
    rw [hxbd]; exact C37Aux.vi_gradK hdiff hxs Y Z X1 hX1b
  have hcon := L310Aux.contr_box (A := A) (b := b) hℓu ⟨hdiff, hL, hlip⟩ hγ hΓ.le hp.le hc hcL'
    hM Z Y hxb hXb
  obtain ⟨D, hD⟩ : ∃ D, D = (X - c • gradK f A b Γ p X Z Y) - (xb - c • gradK f A b Γ p xb Z Y) :=
    ⟨_, rfl⟩
  rw [← hD] at hcon
  obtain ⟨e, he⟩ : ∃ e, e = X1 - xb := ⟨_, rfl⟩
  rw [← he] at hvi
  have r1 : xb - X1 = -e := by rw [he]; abel
  rw [r1, inner_neg_right] at hproj
  have r2 : D - e = ((X - c • gradK f A b Γ p X Z Y) - X1) + c • gradK f A b Γ p xb Z Y := by
    rw [hD, he]; abel
  have k : inner ℝ D e - ‖e‖ ^ 2
      = inner ℝ ((X - c • gradK f A b Γ p X Z Y) - X1) e
        + c * inner ℝ (gradK f A b Γ p xb Z Y) e := by
    rw [← real_inner_self_eq_norm_sq, ← inner_sub_left, r2, inner_add_left,
      real_inner_smul_left]
  have hcv := mul_nonneg hc.le hvi
  have hee : ‖e‖ ^ 2 ≤ inner ℝ D e := by linarith
  have hcs := real_inner_le_norm D e
  have heD : ‖e‖ ≤ ‖D‖ := by
    rcases (norm_nonneg e).eq_or_lt with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · have k3 : ‖e‖ * ‖e‖ ≤ ‖D‖ * ‖e‖ := by
        calc ‖e‖ * ‖e‖ = ‖e‖ ^ 2 := by ring
          _ ≤ ‖D‖ * ‖e‖ := hee.trans hcs
      exact le_of_mul_le_mul_right k3 hpos
  have tri1 := norm_sub_le_norm_sub_add_norm_sub X X1 xb
  have tri2 := norm_sub_le_norm_sub_add_norm_sub X1 X xb
  have hr : ‖X - X1‖ = ‖X1 - X‖ := norm_sub_rev _ _
  rw [← he] at tri1
  have first : c * (p + γ) * ‖X - xb‖ ≤ ‖X1 - X‖ := by
    have : ‖X - xb‖ ≤ ‖X1 - X‖ + (1 - c * (p + γ)) * ‖X - xb‖ := by linarith
    linarith
  refine ⟨first, ?_⟩
  have hμ : 0 < c * (p + γ) := mul_pos hc (by linarith)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), ← he]
  rw [← he] at tri2
  have k5 := mul_le_mul_of_nonneg_left tri2 hμ.le
  linarith
