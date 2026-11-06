-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T14:08:00.691606+00:00
-- url     : https://prove2.me/submissions/52ed49b0-a97f-4250-a249-2c487809007e

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

set_option autoImplicit false

namespace L31Aux

open ProxADMMLC.Conv

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

/-- Descent lemma for `f` on the box. -/
theorem descent {n : ℕ} {f : E n → ℝ} {ℓ u : Fin n → ℝ} {L : ℝ} (hf : Assump22c f ℓ u L)
    {x x' : E n} (hx : x ∈ box ℓ u) (hx' : x' ∈ box ℓ u) :
    f x' ≤ f x + inner ℝ (gradient f x) (x' - x) + L / 2 * ‖x' - x‖ ^ 2 := by
  obtain ⟨hdiff, _, hlip⟩ := hf
  let φ : ℝ → ℝ := fun s => f (x + s • (x' - x)) - s * inner ℝ (gradient f x) (x' - x)
    - L / 2 * (s * s) * ‖x' - x‖ ^ 2
  have hline : ∀ s : ℝ, HasDerivAt (fun t : ℝ => x + t • (x' - x)) (x' - x) s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const (x' - x)).const_add x
  have hφ : ∀ s : ℝ, HasDerivAt φ
      (inner ℝ (gradient f (x + s • (x' - x))) (x' - x) - 1 * inner ℝ (gradient f x) (x' - x)
        - L / 2 * (1 * s + s * 1) * ‖x' - x‖ ^ 2) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => f (x + t • (x' - x)))
        (inner ℝ (gradient f (x + s • (x' - x))) (x' - x)) s := by
      have h0 : HasFDerivAt f (InnerProductSpace.toDual ℝ (E n) (gradient f (x + s • (x' - x))))
          (x + s • (x' - x)) := (hdiff (x + s • (x' - x))).hasGradientAt.hasFDerivAt
      exact h0.comp_hasDerivAt s (hline s)
    have h2 := (hasDerivAt_id' s).mul_const (inner ℝ (gradient f x) (x' - x))
    have h3 := (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul (L / 2)).mul_const
      (‖x' - x‖ ^ 2)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun s _ => (hφ s).continuousAt.continuousWithinAt
    · intro s _
      exact (hφ s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsb : x + s • (x' - x) ∈ box ℓ u := box_seg hx hx' ⟨hs.1.le, hs.2.le⟩
      have hl := hlip _ hsb x hx
      have e : x + s • (x' - x) - x = s • (x' - x) := by abel
      rw [e, norm_smul, Real.norm_of_nonneg hs.1.le] at hl
      have hcs := real_inner_le_norm (gradient f (x + s • (x' - x)) - gradient f x) (x' - x)
      rw [inner_sub_left] at hcs
      have h4 : ‖gradient f (x + s • (x' - x)) - gradient f x‖ * ‖x' - x‖
          ≤ L * (s * ‖x' - x‖) * ‖x' - x‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      have h5 : L * (s * ‖x' - x‖) * ‖x' - x‖ = L / 2 * (1 * s + s * 1) * ‖x' - x‖ ^ 2 := by ring
      linarith
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1:ℝ) • (x' - x) = x' := by simp
  have e0 : x + (0:ℝ) • (x' - x) = x := by simp
  simp only [φ] at h
  rw [e1, e0] at h
  linarith

/-- The dual step raises `K` by `α‖Ax − b‖²`. -/
theorem dual_step {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p α : ℝ)
    (x z : E n) (y : E m) :
    K f A b Γ p x z (y + α • (A x - b)) = K f A b Γ p x z y + α * ‖A x - b‖ ^ 2 := by
  unfold K
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- The averaging step in `z` lowers `K` by at least `p/(2β)‖z − z⁺‖²`. -/
theorem z_step {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (Γ p β : ℝ)
    (hp : 0 ≤ p) (hβ : 0 < β) (hβ1 : β ≤ 1) (x z : E n) (y : E m) :
    K f A b Γ p x (z + β • (x - z)) y + p / (2 * β) * ‖z - (z + β • (x - z))‖ ^ 2
      ≤ K f A b Γ p x z y := by
  unfold K
  have e1 : x - (z + β • (x - z)) = (1 - β) • (x - z) := by module
  have e2 : z - (z + β • (x - z)) = (-β) • (x - z) := by module
  rw [e1, e2, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]
  have hS : 0 ≤ ‖x - z‖ ^ 2 := by positivity
  have h1 : p / (2 * β) * ((-β) ^ 2 * ‖x - z‖ ^ 2) = p * β * ‖x - z‖ ^ 2 / 2 := by
    field_simp
  have h3 : p / 2 * ((1 - β) ^ 2 * ‖x - z‖ ^ 2) + p * β * ‖x - z‖ ^ 2 / 2 - p / 2 * ‖x - z‖ ^ 2
      = p / 2 * ‖x - z‖ ^ 2 * (β ^ 2 - β) := by ring
  have h4 : p / 2 * ‖x - z‖ ^ 2 * (β ^ 2 - β) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
  rw [h1]
  linarith

/-- The projected-gradient step in `x` lowers `K` by at least `‖x − x⁺‖²/(2c)`. -/
theorem x_step {n m : ℕ} {f : E n → ℝ} {A : E n →L[ℝ] E m} {b : E m} {ℓ u : Fin n → ℝ}
    (hℓu : ∀ i, ℓ i < u i) {L Γ p c : ℝ} (hf : Assump22c f ℓ u L) (hΓ : 0 < Γ) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (x z : E n) (y : E m) (hx : x ∈ box ℓ u) :
    K f A b Γ p (boxProj ℓ u (x - c • gradK f A b Γ p x z y)) z y
      + 1 / (2 * c) * ‖x - boxProj ℓ u (x - c • gradK f A b Γ p x z y)‖ ^ 2
      ≤ K f A b Γ p x z y := by
  obtain ⟨X, hX⟩ : ∃ X, X = boxProj ℓ u (x - c • gradK f A b Γ p x z y) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = gradK f A b Γ p x z y := ⟨_, rfl⟩
  rw [← hg] at hX
  rw [← hg, ← hX]
  have hXbox : X ∈ box ℓ u := hX ▸ proj_mem hℓu _
  have hpi := proj_ineq ℓ u (x - c • g) x hx
  rw [← hX] at hpi
  have e : x - c • g - X = (x - X) - c • g := by abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hpi
  have hdes := descent hf hx hXbox
  have hgd : inner ℝ g (X - x) = inner ℝ (gradient f x) (X - x) + inner ℝ y (A (X - x))
      + Γ * inner ℝ (A x - b) (A (X - x)) + p * inner ℝ (x - z) (X - x) := by
    rw [hg]
    unfold gradK
    simp only [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  have hneg : inner ℝ g (x - X) = - inner ℝ g (X - x) := by
    rw [← inner_neg_right, neg_sub]
  have hAX : A X - b = (A x - b) + A (X - x) := by rw [map_sub]; abel
  have hA2 : ‖A X - b‖ ^ 2 = ‖A x - b‖ ^ 2 + 2 * inner ℝ (A x - b) (A (X - x))
      + ‖A (X - x)‖ ^ 2 := by rw [hAX]; exact norm_add_sq_real _ _
  have hXz : X - z = (x - z) + (X - x) := by abel
  have hz2 : ‖X - z‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * inner ℝ (x - z) (X - x) + ‖X - x‖ ^ 2 := by
    rw [hXz]; exact norm_add_sq_real _ _
  have hy2 : inner ℝ y (A X - b) = inner ℝ y (A x - b) + inner ℝ y (A (X - x)) := by
    rw [hAX, inner_add_right]
  have hAd : ‖A (X - x)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖X - x‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
  have hAd2 : Γ / 2 * ‖A (X - x)‖ ^ 2 ≤ Γ / 2 * (‖A‖ ^ 2 * ‖X - x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hAd (by positivity)
  have hnr : ‖x - X‖ = ‖X - x‖ := norm_sub_rev _ _
  rw [hnr] at hpi ⊢
  have hD : 0 ≤ ‖X - x‖ ^ 2 := by positivity
  have hgd2 : inner ℝ g (X - x) ≤ -‖X - x‖ ^ 2 / c := by
    rw [le_div_iff₀ hc]
    rw [hneg] at hpi
    linarith
  have hLK : (L + p + Γ * ‖A‖ ^ 2) * ‖X - x‖ ^ 2 ≤ ‖X - x‖ ^ 2 / c := by
    rw [le_div_iff₀ hc]
    have h := mul_le_mul_of_nonneg_right hcL.le hD
    linarith
  have hQ : 2 * (1 / (2 * c) * ‖X - x‖ ^ 2) = ‖X - x‖ ^ 2 / c := by
    field_simp
  have hdiv : -‖X - x‖ ^ 2 / c = -(‖X - x‖ ^ 2 / c) := neg_div _ _
  unfold K
  rw [hA2, hz2, hy2]
  linarith

end L31Aux

open ProxADMMLC.Conv in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L)
    (Γ p c α β : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    ∀ t, K f A b Γ p (x t) (z t) (y t) - K f A b Γ p (x (t + 1)) (z (t + 1)) (y (t + 1)) ≥
      1 / (2 * c) * ‖x t - x (t + 1)‖ ^ 2 + p / (2 * β) * ‖z t - z (t + 1)‖ ^ 2
        - α * ‖A (x t) - b‖ ^ 2 := by
  obtain ⟨hx0, _, hstep⟩ := hrun
  have hxt : ∀ t, x t ∈ box ℓ u := by
    intro t
    induction t with
    | zero => exact hx0
    | succ k _ =>
      rw [(hstep k).2.1]
      exact L31Aux.proj_mem hℓu _
  intro t
  obtain ⟨hy, hxx, hz⟩ := hstep t
  have h1 := L31Aux.dual_step f A b Γ p α (x t) (z t) (y t)
  have h2 := L31Aux.x_step (b := b) hℓu hf hΓ hc hcL (x t) (z t) (y (t + 1)) (hxt t)
  have h3 := L31Aux.z_step f A b Γ p β hp.le hβ hβ1 (x (t + 1)) (z t) (y (t + 1))
  rw [← hy] at h1
  rw [← hxx] at h2
  rw [← hz] at h3
  linarith
