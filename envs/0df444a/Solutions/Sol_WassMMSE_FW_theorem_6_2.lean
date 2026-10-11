-- Prove2me | solution 1 for WassMMSE.FW.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:32:17.959014+00:00
-- url     : https://prove2.me/submissions/74a3e59e-c3f2-45f5-80ed-3f04a42f68b9

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace RRAux_WassMMSE_FW_theorem_6_2

open scoped InnerProductSpace

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem line_deriv (f : F → ℝ) (x w : F) (t : ℝ) (hd : DifferentiableAt ℝ f (x + t • w)) :
    HasDerivAt (fun s : ℝ => f (x + s • w)) ⟪gradient f (x + t • w), w⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt t hl
  rw [grad_inner f] at hc
  exact hc

theorem first_order {X : Set F} (hXconv : Convex ℝ X) (f : F → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : F} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (y - x) ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hx hy ht
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) φ := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro a ha b hb α β hα hβ hαβ
    have := hf.2 (hmem a ha) (hmem b hb) hα hβ hαβ
    have e : α • (x + a • (y - x)) + β • (x + b • (y - x))
        = x + (α • a + β • b) • (y - x) := by
      have : α • (x + a • (y - x)) + β • (x + b • (y - x))
          = (α + β) • x + (α * a + β * b) • (y - x) := by module
      rw [this, hαβ, one_smul, smul_eq_mul, smul_eq_mul]
    rw [e] at this
    simpa [hφ] using this
  have hd : HasDerivAt φ ⟪gradient f x, y - x⟫_ℝ 0 := by
    have := line_deriv f x (y - x) 0 (by simpa using hdiff x hx)
    simpa using this
  have := hconv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hd
  have e1 : φ 1 = f y := by simp only [hφ, one_smul]; congr 1; abel
  have e0 : φ 0 = f x := by simp only [hφ, zero_smul, add_zero]
  rw [slope_def_field, e1, e0, sub_zero, div_one] at this
  linarith

theorem descentX {X : Set F} (hXconv : Convex ℝ X) (f : F → ℝ)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x) (L : ℝ)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : F} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x with hw
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • w ∈ X := fun t ht =>
    hXconv.add_smul_sub_mem hx hy ht
  set ψ : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
    with hψ
  have hder : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (⟪gradient f (x + t • w), w⟫_ℝ
      - ⟪gradient f x, w⟫_ℝ - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t ht
    have hc := line_deriv f x w t (hdiff _ (hmem t ht))
    have h2 : HasDerivAt (fun t : ℝ => t * ⟪gradient f x, w⟫_ℝ) ⟪gradient f x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫_ℝ
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (hc.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(hder t ht').deriv]
      have h1 := real_inner_le_norm (gradient f (x + t • w) - gradient f x) w
      have h2 := hL _ (hmem t ht') x hx
      have e : x + t • w - x = t • w := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at h2
      rw [inner_sub_left] at h1
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
      nlinarith
  have := hanti (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (1:ℝ) ∈ Set.Icc 0 1 by simp) zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at this
  have e : x + w = y := by rw [hw]; abel
  rw [e] at this
  norm_num at this
  rw [grad_inner f] at this
  linarith

end

theorem small_t (A K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → -(K * t) ≤ A) : 0 ≤ A := by
  by_contra hA
  push Not at hA
  set t := min 1 (-A / (2 * (K + 1))) with ht
  have hK1 : 0 < K + 1 := by linarith
  have htp : 0 < t := lt_min one_pos (div_pos (by linarith) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -A / (2 * (K + 1)) := min_le_right _ _
  have h1 := h t htp ht1
  have h2 : (K + 1) * t ≤ -A / 2 := by
    rw [le_div_iff₀ (by positivity)] at ht2; nlinarith
  nlinarith

theorem eta_bounds (g b D : ℝ) (hg : 0 ≤ g) (hb : 0 < b) (hD : 0 ≤ D) :
    0 ≤ min 1 (g / (b * D)) ∧ min 1 (g / (b * D)) ≤ 1 :=
  ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

theorem case_one (f0 f1 fs g b D δ ρ : ℝ) (hh : 0 ≤ f0 - fs) (hgδ : δ * (f0 - fs) ≤ g)
    (hacc : f1 ≤ f0 - g + b * D / 2) (hbD : b * D ≤ g) (hρ : 1 - δ / 2 ≤ ρ) :
    f1 - fs ≤ ρ * (f0 - fs) := by
  have := mul_le_mul_of_nonneg_right hρ hh
  nlinarith

theorem case_lt (f0 f1 fs g b D r α ε βb ρ : ℝ) (hh : 0 ≤ f0 - fs) (hD : 0 < D) (hb : 0 < b)
    (hbb : b ≤ βb) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hα : 0 < α) (hε : 0 < ε) (hg : 0 ≤ g)
    (hacc : f1 ≤ f0 - g ^ 2 / (2 * b * D))
    (hgap : (1 - r) * (α / 2 * ε * D) ≤ (1 + r) * g)
    (hgδ : (1 - r) * (1 + r) * (f0 - fs) ≤ g)
    (hρ : 1 - (1 - r) ^ 2 * α * ε / (4 * βb) ≤ ρ) :
    f1 - fs ≤ ρ * (f0 - fs) := by
  set h := f0 - fs with hhdef
  have hg2 : (1 - r) ^ 2 * (α / 2 * ε * D) * h ≤ g ^ 2 := by
    have h1 : (1 - r) * (α / 2 * ε * D) * g ≤ (1 + r) * g * g :=
      mul_le_mul_of_nonneg_right hgap hg
    have h2 : (1 - r) * (α / 2 * ε * D) * ((1 - r) * (1 + r) * h)
        ≤ (1 - r) * (α / 2 * ε * D) * g :=
      mul_le_mul_of_nonneg_left hgδ (by positivity)
    have h3 : (1 + r) * ((1 - r) ^ 2 * (α / 2 * ε * D) * h) ≤ (1 + r) * g ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left h3 (by linarith)
  have hbb' : 0 < βb := lt_of_lt_of_le hb hbb
  have h4 : (1 - r) ^ 2 * α * ε * h / (4 * βb) ≤ g ^ 2 / (2 * b * D) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : 0 ≤ (1 - r) ^ 2 * α * ε * h := by positivity
    have h6 : (1 - r) ^ 2 * α * ε * h * (2 * b * D) ≤ (1 - r) ^ 2 * α * ε * h * (2 * βb * D) :=
      mul_le_mul_of_nonneg_left (by nlinarith) h5
    nlinarith
  have h7 : (1 - (1 - r) ^ 2 * α * ε / (4 * βb)) * h ≤ ρ * h := mul_le_mul_of_nonneg_right hρ hh
  have e : (1 - (1 - r) ^ 2 * α * ε / (4 * βb)) * h = h - (1 - r) ^ 2 * α * ε * h / (4 * βb) := by
    field_simp
  linarith

theorem lt_algebra (f0 g b D : ℝ) (hb : 0 < b) (hD : 0 < D) :
    f0 - g / (b * D) * g + (g / (b * D)) ^ 2 * b / 2 * D = f0 - g ^ 2 / (2 * b * D) := by
  field_simp
  ring

theorem gap_pos (g δ r α ε D : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hδ : δ = 1 - r ^ 2)
    (hSC : δ * (r / (1 + r) * (1 - r / (1 + r)) * (α / 2)) * (ε * D)
      ≤ g * (1 - δ * (1 - r / (1 + r)))) :
    (1 - r) * (α / 2 * ε * D) ≤ (1 + r) * g := by
  have hq : 0 < 1 + r := by linarith
  have e1 : 1 - δ * (1 - r / (1 + r)) = r := by rw [hδ]; field_simp; ring
  have e2 : δ * (r / (1 + r) * (1 - r / (1 + r)) * (α / 2)) * (ε * D)
      = r * ((1 - r) * (α / 2 * ε * D)) / (1 + r) := by rw [hδ]; field_simp; ring
  rw [e1, e2, div_le_iff₀ hq] at hSC
  have : r * ((1 - r) * (α / 2 * ε * D)) ≤ r * ((1 + r) * g) := by linarith
  exact le_of_mul_le_mul_left this hr

theorem sc_scalar (P W δ c εD θ : ℝ) (h : P ≤ δ * ((1 - θ) * P - c * W)) (hW : εD ≤ W)
    (hδc : 0 ≤ δ * c) : δ * c * εD ≤ -P * (1 - δ * (1 - θ)) := by
  have := mul_le_mul_of_nonneg_left hW hδc
  nlinarith

open WassMMSE.FW in
theorem sc_ineq {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ α ε : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hF : IsInexactOracle S f F δ)
    (hα : IsStronglyConvexWrt S Sk f α) (hε : IsSteep S f ε)
    {s : BlockSpace K d} (hs : s ∈ S) {θ : ℝ} (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
    δ * (θ * (1 - θ) * (α / 2)) * (ε * ‖F s - s‖ ^ 2) ≤ fwGap f F s * (1 - δ * (1 - θ)) := by
  obtain ⟨hδ0, hδ1, hor⟩ := hF
  obtain ⟨hFs, hz⟩ := hor s hs
  set G := gradient f s with hG
  set s' := F s with hs'
  set c := θ * (1 - θ) * (α / 2) with hc
  set w : BlockSpace K d :=
    WithLp.toLp 2 (fun k => (‖s k - s' k‖ ^ 2) • (‖G k‖⁻¹ • G k)) with hw
  have hzS : θ • s + (1 - θ) • s' - c • w ∈ S := by
    rw [hS.1]
    intro k
    have := hα.2 s hs s' hFs θ hθ k
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, hw, smul_smul,
      hc] at this ⊢
    simp only [← mul_assoc]
    exact this
  have hor' := hz _ hzS
  have e : θ • s + (1 - θ) • s' - c • w - s = (1 - θ) • (s' - s) - c • w := by module
  rw [e, inner_sub_left ((1 - θ) • (s' - s)) (c • w), inner_smul_left, inner_smul_left] at hor'
  simp only [RCLike.conj_to_real] at hor'
  have hwG : ε * ‖s' - s‖ ^ 2 ≤ ⟪w, G⟫_ℝ := by
    rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hGk := hε.2 s hs k
    have hGp : 0 < ‖G k‖ := lt_of_lt_of_le hε.1 hGk
    simp only [hw, PiLp.toLp_apply, PiLp.sub_apply, inner_smul_left, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq]
    have e2 : ‖G k‖⁻¹ * ‖G k‖ ^ 2 = ‖G k‖ := by field_simp
    rw [e2, norm_sub_rev (s' k) (s k), mul_comm ε]
    exact mul_le_mul_of_nonneg_left hGk (sq_nonneg _)
  have hδc : 0 ≤ δ * c := mul_nonneg hδ0 (by rw [hc]; have := hα.1; have := hθ.1; have := hθ.2; positivity)
  have := sc_scalar _ _ δ c _ θ hor' hwG hδc
  unfold fwGap fwDirection
  exact this

end RRAux_WassMMSE_FW_theorem_6_2

open scoped InnerProductSpace
open RRAux_WassMMSE_FW_theorem_6_2

open WassMMSE.FW in
theorem solution
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {β α ε : ℝ} (hβ : IsSmoothOn S f β) (hα : IsStronglyConvexWrt S Sk f α) (hε : IsSteep S f ε)
    {fstar : ℝ} (hfstar : IsLeast (f '' S) fstar)
    {βm1 τ ζ : ℝ} {s : ℕ → BlockSpace K d} {βt ηt : ℕ → ℝ}
    (hrun : IsFAFWRun S f F βm1 τ ζ s βt ηt) :
    ∀ t : ℕ, f (s t) - fstar
      ≤ (max (1 - δ / 2) (1 - (1 - Real.sqrt (1 - δ)) ^ 2 * α * ε / (4 * max (τ * β) βm1))) ^ t
          * (f (s 0) - fstar) := by
  have hSconv : Convex ℝ S := by
    rw [hS.1]
    intro x hx y hy a b ha hb hab k
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply] at hx hy ⊢
    exact (hS.2 k).1 (hx k) (hy k) ha hb hab
  obtain ⟨hfc, hfd⟩ := hf
  have hδ0 := hF.1
  have hδ1 := hF.2.1
  have hor := hF.2.2
  obtain ⟨hβ0, hβL⟩ := hβ
  have hα0 := hα.1
  have hε0 := hε.1
  obtain ⟨⟨zs, hzsS, hzs⟩, hlowb⟩ := hfstar
  obtain ⟨hβm1, hτ, hζ, hs0, hstep⟩ := hrun
  have hh0 : ∀ x ∈ S, 0 ≤ f x - fstar := fun x hx => sub_nonneg.2 (hlowb ⟨x, hx, rfl⟩)
  have hgap0 : ∀ x ∈ S, 0 ≤ fwGap f F x := by
    intro x hx
    have := (hor x hx).2 x hx
    rw [sub_self, inner_zero_left, mul_zero] at this
    unfold fwGap fwDirection
    linarith
  have hgapδ : ∀ x ∈ S, δ * (f x - fstar) ≤ fwGap f F x := by
    intro x hx
    have h1 := (hor x hx).2 zs hzsS
    have h2 := first_order hSconv f hfc hfd hx hzsS
    rw [real_inner_comm, hzs] at h2
    have h3 := mul_le_mul_of_nonneg_left
      (show ⟪zs - x, gradient f x⟫_ℝ ≤ fstar - f x by linarith) hδ0
    unfold fwGap fwDirection
    linarith
  have hstepS : ∀ x ∈ S, ∀ b, 0 < b → x + fwStep f F x b • fwDirection F x ∈ S := by
    intro x hx b hb
    have hη := eta_bounds (fwGap f F x) b (‖fwDirection F x‖ ^ 2) (hgap0 x hx) hb (sq_nonneg _)
    exact hSconv.add_smul_sub_mem hx (hor x hx).1 ⟨hη.1, hη.2⟩
  have hacc : ∀ x ∈ S, ∀ b, β ≤ b → LineSearchAccepts f F x b := by
    intro x hx b hb
    have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb
    have hy := hstepS x hx b hb0
    have hd := descentX hSconv f hfd β hβL hx hy
    unfold LineSearchAccepts
    rw [add_sub_cancel_left, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm] at hd
    have hη := eta_bounds (fwGap f F x) b (‖fwDirection F x‖ ^ 2) (hgap0 x hx) hb0 (sq_nonneg _)
    have h2 : fwStep f F x b ^ 2 * β / 2 * ‖fwDirection F x‖ ^ 2
        ≤ fwStep f F x b ^ 2 * b / 2 * ‖fwDirection F x‖ ^ 2 := by
      have : 0 ≤ fwStep f F x b ^ 2 * ‖fwDirection F x‖ ^ 2 := by positivity
      nlinarith
    unfold fwGap
    nlinarith
  set βb := max (τ * β) βm1 with hβb
  have hinv : ∀ t, s t ∈ S ∧ 0 < prevBeta βm1 βt t ∧ prevBeta βm1 βt t ≤ βb := by
    intro t
    induction t with
    | zero => exact ⟨hs0, hβm1, le_max_right _ _⟩
    | succ t ih =>
      obtain ⟨hsS, hp0, hpb⟩ := ih
      obtain ⟨⟨j, hj, hacct, hmin⟩, hη, hsn⟩ := hstep t
      have hbt0 : 0 < βt t := by
        rw [hj]; have : 0 < ζ := by linarith
        have : 0 < τ := by linarith
        positivity
      refine ⟨?_, hbt0, ?_⟩
      · rw [hsn, hη]; exact hstepS _ hsS _ hbt0
      · show βt t ≤ βb
        cases j with
        | zero =>
          rw [hj, pow_zero, mul_one]
          exact (div_le_self hp0.le hζ.le).trans hpb
        | succ i =>
          have hlt : prevBeta βm1 βt t / ζ * τ ^ i < β := by
            by_contra hc
            push Not at hc
            exact hmin i (Nat.lt_succ_self i) (hacc _ hsS _ hc)
          rw [hj, pow_succ, ← mul_assoc]
          have : prevBeta βm1 βt t / ζ * τ ^ i * τ ≤ β * τ :=
            mul_le_mul_of_nonneg_right hlt.le (by linarith)
          calc _ ≤ β * τ := this
            _ = τ * β := mul_comm _ _
            _ ≤ βb := le_max_left _ _
  set r := Real.sqrt (1 - δ) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hδr : δ = 1 - r ^ 2 := by rw [hrdef, Real.sq_sqrt (by linarith)]; ring
  have hgapr : ∀ x ∈ S, (1 - r) * (α / 2 * ε * ‖F x - x‖ ^ 2) ≤ (1 + r) * fwGap f F x := by
    intro x hx
    rcases eq_or_lt_of_le hr0 with h0 | hpos
    · rw [← h0] at hδr ⊢
      have hδ1' : δ = 1 := by rw [hδr]; ring
      have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
          -(α / 2 * ε * ‖F x - x‖ ^ 2 * θ) ≤ fwGap f F x - α / 2 * ε * ‖F x - x‖ ^ 2 := by
        intro θ hθ0 hθ1
        have := sc_ineq hS hF hα hε hx ⟨hθ0.le, hθ1⟩
        rw [hδ1'] at this
        have e1 : 1 * (θ * (1 - θ) * (α / 2)) * (ε * ‖F x - x‖ ^ 2)
            = θ * ((1 - θ) * (α / 2 * ε * ‖F x - x‖ ^ 2)) := by ring
        have e2 : fwGap f F x * (1 - 1 * (1 - θ)) = θ * fwGap f F x := by ring
        rw [e1, e2] at this
        have := le_of_mul_le_mul_left this hθ0
        linarith
      have := small_t _ _ (by have := hα0; have := hε0; positivity) key
      linarith
    · have hθ : r / (1 + r) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one (by linarith)]; linarith
      have := sc_ineq hS hF hα hε hx hθ
      have e : δ * (r / (1 + r) * (1 - r / (1 + r)) * (α / 2)) * (ε * ‖F x - x‖ ^ 2)
          = δ * (r / (1 + r) * (1 - r / (1 + r)) * (α / 2)) * (ε * ‖F x - x‖ ^ 2) := rfl
      exact gap_pos _ δ r α ε _ hpos hr1 hδr this
  set ρ := max (1 - δ / 2) (1 - (1 - r) ^ 2 * α * ε / (4 * βb)) with hρdef
  have hρ1 : 1 - δ / 2 ≤ ρ := le_max_left _ _
  have hρ2 : 1 - (1 - r) ^ 2 * α * ε / (4 * βb) ≤ ρ := le_max_right _ _
  have hcon : ∀ t, f (s (t + 1)) - fstar ≤ ρ * (f (s t) - fstar) := by
    intro t
    obtain ⟨hsS, hp0, hpb⟩ := hinv t
    obtain ⟨hsS1, hbt0, hbtb⟩ := hinv (t + 1)
    have hbtb' : βt t ≤ βb := hbtb
    have hbt0 : 0 < βt t := hbt0
    obtain ⟨⟨j, hj, hacct, hmin⟩, hη, hsn⟩ := hstep t
    have hh := hh0 _ hsS
    have hgδ := hgapδ _ hsS
    have hg0 := hgap0 _ hsS
    unfold LineSearchAccepts at hacct
    rw [← hη, ← hsn] at hacct
    rcases eq_or_lt_of_le (sq_nonneg ‖fwDirection F (s t)‖) with hD | hD
    · -- zero direction
      have hd0 : fwDirection F (s t) = 0 := by
        have : ‖fwDirection F (s t)‖ = 0 := by
          have := hD.symm; exact pow_eq_zero_iff (two_ne_zero) |>.1 this
        exact norm_eq_zero.1 this
      have hg : fwGap f F (s t) = 0 := by
        unfold fwGap; rw [hd0, inner_zero_left, neg_zero]
      have hsn' : s (t + 1) = s t := by rw [hsn, hd0, smul_zero, add_zero]
      rw [hsn']
      rw [hg] at hgδ
      have := mul_le_mul_of_nonneg_right hρ1 hh
      nlinarith
    · have hb0 : 0 < βt t * ‖fwDirection F (s t)‖ ^ 2 := by positivity
      by_cases hge : 1 ≤ fwGap f F (s t) / (βt t * ‖fwDirection F (s t)‖ ^ 2)
      · have hη1 : ηt t = 1 := by rw [hη]; unfold fwStep; exact min_eq_left hge
        rw [hη1] at hacct
        have hbD : βt t * ‖fwDirection F (s t)‖ ^ 2 ≤ fwGap f F (s t) := by
          rwa [le_div_iff₀ hb0, one_mul] at hge
        refine case_one _ _ _ (fwGap f F (s t)) (βt t) (‖fwDirection F (s t)‖ ^ 2) δ ρ hh hgδ
          ?_ hbD hρ1
        linarith
      · push Not at hge
        have hηv : ηt t = fwGap f F (s t) / (βt t * ‖fwDirection F (s t)‖ ^ 2) := by
          rw [hη]; unfold fwStep; exact min_eq_right hge.le
        rw [hηv, lt_algebra (f (s t)) (fwGap f F (s t)) (βt t) _ hbt0 hD] at hacct
        have hgapx := hgapr _ hsS
        have hdir : ‖F (s t) - s t‖ = ‖fwDirection F (s t)‖ := rfl
        rw [hdir] at hgapx
        have hgδ' : (1 - r) * (1 + r) * (f (s t) - fstar) ≤ fwGap f F (s t) := by
          have e : (1 - r) * (1 + r) = δ := by rw [hδr]; ring
          rw [e]; exact hgδ
        exact case_lt _ _ _ _ (βt t) _ r α ε βb ρ hh hD hbt0 hbtb' hr0 hr1 hα0 hε0 hg0 hacct
          hgapx hgδ' hρ2
  have hρ0 : 0 ≤ ρ := le_trans (by linarith) hρ1
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc f (s (t + 1)) - fstar ≤ ρ * (f (s t) - fstar) := hcon t
      _ ≤ ρ * (ρ ^ t * (f (s 0) - fstar)) := mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ (t + 1) * (f (s 0) - fstar) := by ring

#print axioms solution
