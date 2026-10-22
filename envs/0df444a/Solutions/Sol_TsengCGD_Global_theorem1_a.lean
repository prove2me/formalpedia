-- Prove2me | solution 1 for TsengCGD.Global.theorem1_a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:21:46.261533+00:00
-- url     : https://prove2.me/submissions/a02cae21-d7f8-490d-bf66-cc31becca8cf

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Global

lemma g38_lim0 (A B : ℝ) (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + s * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  set s := min 1 (-A / (2 * (|B| + 1))) with hs
  have hB1 : 0 < |B| + 1 := by positivity
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ -A / (2 * (|B| + 1)) := min_le_right _ _
  have h3 : s * (2 * (|B| + 1)) ≤ -A := by
    rwa [le_div_iff₀ (by positivity)] at hs2
  have h4 : s * B ≤ s * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hs0.le
  have := h s hs0 hs1
  nlinarith

lemma g38_dot_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (v w : Fin n → ℝ) :
    v ⬝ᵥ (H *ᵥ w) = w ⬝ᵥ (H *ᵥ v) := by
  have hT : Hᵀ = H := by
    have := hH.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]

lemma g38_qf_add {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (d v : Vec n) (s : ℝ) :
    qf H (d + s • v) = qf H d + 2 * s * (WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp d)) + s ^ 2 * qf H v := by
  have := g38_dot_symm H hH (WithLp.ofLp d) (WithLp.ofLp v)
  simp only [qf, WithLp.ofLp_add, WithLp.ofLp_smul, mulVec_add, mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at *
  rw [this]; ring

lemma g38_qf_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (v : Vec n) :
    qf H (s • v) = s ^ 2 * qf H v := by
  simp only [qf, WithLp.ofLp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma g38_qf_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : qf H (0 : Vec n) = 0 := by
  simp [qf]

lemma g38_qf_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) {v : Vec n} (hv : v ≠ 0) :
    0 < qf H v := by
  have h : WithLp.ofLp v ≠ 0 := by
    intro h; apply hv
    have : v = WithLp.toLp 2 (WithLp.ofLp v) := rfl
    rw [this, h]; rfl
  have := hH.dotProduct_mulVec_pos h
  simpa [qf] using this

lemma g38_qf_nonneg {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (v : Vec n) :
    0 ≤ qf H v := by
  by_cases hv : v = 0
  · subst hv; simp [qf]
  · exact (g38_qf_pos hH hv).le

lemma g38_qf_cont {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Continuous (fun v : Vec n => qf H v) := by
  unfold qf
  simp only [dotProduct, mulVec]
  fun_prop

/-- first-order optimality condition for the CGD direction -/
lemma g38_fo {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Vec n} {J : Finset (Fin n)} {d : Vec n}
    (hD : Convex ℝ D) (hPc : ConvexOn ℝ D P) (hc : 0 ≤ c) (hH : H.IsHermitian)
    (hd : IsDir f D P c H x J d) (e : Vec n) (he : SupportedOn J e) (hxe : x + e ∈ D) :
    0 ≤ ⟪gradient f x, e - d⟫ + WithLp.ofLp (e - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)
      + c * (P (x + e) - P (x + d)) := by
  obtain ⟨hdS, hdD, hdmin⟩ := hd
  apply g38_lim0 _ (qf H (e - d) / 2)
  intro s hs0 hs1
  have hsup : SupportedOn J (d + s • (e - d)) := by
    intro j hj; simp [hdS j hj, he j hj]
  have hmemE : x + (d + s • (e - d)) = (1 - s) • (x + d) + s • (x + e) := by module
  have hmem : x + (d + s • (e - d)) ∈ D := by
    rw [hmemE]; exact hD hdD hxe (by linarith) hs0.le (by ring)
  have h1 := hdmin _ hsup hmem
  have hP := hPc.2 hdD hxe (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
  simp only [smul_eq_mul] at hP
  rw [← hmemE] at hP
  simp only [subObj] at h1
  rw [g38_qf_add H hH, inner_add_right, inner_smul_right] at h1
  have h2 : c * P (x + (d + s • (e - d))) ≤ c * ((1 - s) * P (x + d) + s * P (x + e)) :=
    mul_le_mul_of_nonneg_left hP hc
  have h3 : 0 ≤ s * (⟪gradient f x, e - d⟫ + WithLp.ofLp (e - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)
      + c * (P (x + e) - P (x + d)) + s * (qf H (e - d) / 2)) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs0).mp h3; linarith

lemma g38_qf_self {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (d : Vec n) :
    WithLp.ofLp (0 - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d) = - qf H d := by
  simp [qf]

lemma g38_delta_le {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Vec n} {J : Finset (Fin n)} {d : Vec n}
    (hD : Convex ℝ D) (hPc : ConvexOn ℝ D P) (hc : 0 ≤ c) (hH : H.IsHermitian)
    (hd : IsDir f D P c H x J d) (hx : x ∈ D) :
    ⟪gradient f x, d⟫ + qf H d + c * P (x + d) - c * P x ≤ 0 := by
  have := g38_fo hD hPc hc hH hd 0 (fun j _ => by simp) (by simpa using hx)
  rw [g38_qf_self] at this
  simp only [zero_sub, inner_neg_right, add_zero] at this
  linarith

lemma g38_diff {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {y : Vec n} (hy : y ∈ D) : DifferentiableAt ℝ f y := by
  obtain ⟨U, hU, hDU, hf⟩ := hs.smooth
  exact (hf.contDiffAt (hU.mem_nhds (hDU hy))).differentiableAt (by norm_num)

lemma g38_line_deriv {n : ℕ} (h : Vec n → ℝ) (x v : Vec n) (t : ℝ)
    (hd : DifferentiableAt ℝ h (x + t • v)) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := hd.hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

/-- the slope of `f` along `v` at `x` converges to the directional derivative -/
lemma g38_slope {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {x : Vec n} (hx : x ∈ D) (v : Vec n) :
    Tendsto (fun a => (f (x + a • v) - f x - a * ⟪gradient f x, v⟫) / a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hder := g38_line_deriv f x v 0 (by simpa using g38_diff hs hx)
  simp only [zero_smul, add_zero] at hder
  have hslope := hder.tendsto_slope_zero_right
  have h2 : Tendsto (fun a : ℝ => a⁻¹ • (f (x + (0 + a) • v) - f (x + (0:ℝ) • v)) - ⟪gradient f x, v⟫)
      (𝓝[>] 0) (𝓝 (⟪gradient f x, v⟫ - ⟪gradient f x, v⟫)) := hslope.sub_const _
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have : a ≠ 0 := ne_of_gt ha
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  field_simp

theorem lemma1_core {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (d : Vec n) (hd : IsDir f D P c H x J d) :
    (∃ r : ℝ → ℝ, Tendsto (fun a => r a / a) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤
          Fc f P c x + a * (⟪gradient f x, d⟫ + c * P (x + d) - c * P x) + r a) ∧
    ⟪gradient f x, d⟫ + c * P (x + d) - c * P x ≤ -qf H d := by
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  have hPc : ConvexOn ℝ D P := hs.properConvexLsc.2.2.1
  have hc := hs.c_pos
  refine ⟨⟨fun a => f (x + a • d) - f x - a * ⟪gradient f x, d⟫, g38_slope hs hx d, ?_⟩, ?_⟩
  · intro a ⟨ha0, ha1⟩
    have hmem : x + a • d = (1 - a) • x + a • (x + d) := by module
    have hxd := hd.2.1
    refine ⟨by rw [hmem]; exact hD hx hxd (by linarith) ha0.le (by ring), ?_⟩
    have hP := hPc.2 hx hxd (by linarith : (0:ℝ) ≤ 1 - a) ha0.le (by ring)
    simp only [smul_eq_mul] at hP
    rw [← hmem] at hP
    simp only [Fc]
    nlinarith [mul_le_mul_of_nonneg_left hP hc.le]
  · have := g38_delta_le hD hPc hc.le hH.isHermitian hd hx
    linarith

theorem armijo_exists_core {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (d : Vec n) (hd : IsDir f D P c H x J d)
    (β σ γ a₀ : ℝ) (hparams : ArmijoParams β σ γ) (ha₀ : 0 < a₀) :
    (∃ r : ℝ → ℝ, Tendsto (fun a => r a / a) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤ Fc f P c x + a * Delta f P c γ H x d + r a) ∧
    Delta f P c γ H x d ≤ (γ - 1) * qf H d ∧
    (d ≠ 0 → Delta f P c γ H x d < 0) ∧
    ∃ j : ℕ, ArmijoTest f D P c σ γ H x d (a₀ * β ^ j) := by
  obtain ⟨⟨r, hr, hineq⟩, hL⟩ := lemma1_core f D P c hs x hx J H hH d hd
  have hq := g38_qf_nonneg hH d
  have hγ := hparams.gamma_nonneg
  have hγ1 := hparams.gamma_lt_one
  have hDelta : Delta f P c γ H x d =
      (⟪gradient f x, d⟫ + c * P (x + d) - c * P x) + γ * qf H d := by
    simp only [Delta]; ring
  have hineq' : ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤ Fc f P c x + a * Delta f P c γ H x d + r a := by
    intro a ha
    refine ⟨(hineq a ha).1, ?_⟩
    have := (hineq a ha).2
    rw [hDelta]; nlinarith [ha.1, mul_nonneg ha.1.le (mul_nonneg hγ hq)]
  have hneg : d ≠ 0 → Delta f P c γ H x d < 0 := by
    intro hd0
    have := g38_qf_pos hH hd0
    rw [hDelta]; nlinarith
  refine ⟨⟨r, hr, hineq'⟩, ?_, hneg, ?_⟩
  · rw [hDelta]; nlinarith
  · by_cases hd0 : d = 0
    · refine ⟨0, ?_, ?_⟩
      · subst hd0; simpa using hx
      · subst hd0; simp [Delta, qf]
    · have hΔ := hneg hd0
      set Δ := Delta f P c γ H x d with hΔdef
      have hσ := hparams.sigma_lt_one
      have hpos : 0 < -(1 - σ) * Δ := by nlinarith
      have hev : ∀ᶠ a in 𝓝[>] (0:ℝ), r a / a < -(1 - σ) * Δ ∧ a ∈ Set.Ioc (0:ℝ) 1 :=
        (hr.eventually (gt_mem_nhds hpos)).and (Ioc_mem_nhdsGT one_pos)
      have ht : Tendsto (fun j : ℕ => a₀ * β ^ j) atTop (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hparams.beta_pos.le
            hparams.beta_lt_one).const_mul a₀
          simpa using this
        · exact Eventually.of_forall (fun j => mul_pos ha₀ (pow_pos hparams.beta_pos j))
      obtain ⟨j, hj⟩ := (ht.eventually hev).exists
      refine ⟨j, ?_⟩
      obtain ⟨hmem, hle⟩ := hineq' _ hj.2
      refine ⟨hmem, ?_⟩
      have ha0 := hj.2.1
      have h1 := hj.1
      rw [div_lt_iff₀ ha0] at h1
      nlinarith

theorem theorem1_a_core {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar) :
    Antitone (fun k => Fc f P c (x k)) ∧
    (∀ k, x k ∈ D) ∧
    (∀ k, (1 - γ) * qf (H k) (d k) ≤ -Delta f P c γ (H k) (x k) (d k) ∧
      (1 - γ) * lam * ‖d k‖ ^ 2 ≤ (1 - γ) * qf (H k) (d k)) ∧
    (∀ k, Fc f P c (x (k + 1)) - Fc f P c (x k) ≤ σ * α k * Delta f P c γ (H k) (x k) (d k) ∧
      σ * α k * Delta f P c γ (H k) (x k) (d k) ≤ 0) := by
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  have hPc : ConvexOn ℝ D P := hs.properConvexLsc.2.2.1
  have hc := hs.c_pos
  obtain ⟨hpar, _, hj⟩ := harm
  have hγ := hpar.gamma_nonneg
  have hγ1 := hpar.gamma_lt_one
  have hσ := hpar.sigma_pos
  have hDle : ∀ k, Delta f P c γ (H k) (x k) (d k) ≤ (γ - 1) * qf (H k) (d k) := by
    intro k
    have := g38_delta_le hD hPc hc.le (hrun.H_posDef k).isHermitian (hrun.dir k) (hrun.iterate_mem k)
    simp only [Delta]; linarith
  have hqn : ∀ k, 0 ≤ qf (H k) (d k) := fun k => g38_qf_nonneg (hrun.H_posDef k) _
  have hdesc : ∀ k, Fc f P c (x (k + 1)) - Fc f P c (x k) ≤
      σ * α k * Delta f P c γ (H k) (x k) (d k) := by
    intro k
    obtain ⟨j, hαj, htest, _⟩ := hj k
    have := htest.2
    rw [hrun.step k]
    linarith
  have hnp : ∀ k, σ * α k * Delta f P c γ (H k) (x k) (d k) ≤ 0 := by
    intro k
    have h1 := hDle k
    have h2 := hqn k
    have h3 : Delta f P c γ (H k) (x k) (d k) ≤ 0 := by nlinarith
    have h4 : 0 ≤ σ * α k := mul_nonneg hσ.le (hrun.step_pos k).le
    nlinarith
  refine ⟨?_, hrun.iterate_mem, ?_, fun k => ⟨hdesc k, hnp k⟩⟩
  · apply antitone_nat_of_succ_le
    intro k
    have := hdesc k
    have := hnp k
    linarith
  · intro k
    refine ⟨by have := hDle k; linarith, ?_⟩
    have := (hA1.2.2 k (d k)).1
    have h1 : 0 ≤ 1 - γ := by linarith
    have := mul_le_mul_of_nonneg_left this h1
    linarith

end TsengCGD.Global

open TsengCGD.Global


theorem solution {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k) :
    let Δ := fun k => Delta f P c γ (H k) (x k) (d k)
    Antitone (fun k => Fc f P c (x k)) ∧
    (∀ k, x k ∈ D) ∧
    (∀ k, (1 - γ) * qf (H k) (d k) ≤ -Δ k ∧
      (1 - γ) * lam * ‖d k‖ ^ 2 ≤ (1 - γ) * qf (H k) (d k)) ∧
    (∀ k, Fc f P c (x (k + 1)) - Fc f P c (x k) ≤ σ * α k * Δ k ∧
      σ * α k * Δ k ≤ 0) := by
  exact theorem1_a_core f D P c hs J H x d α αinit β σ γ lam lamBar hrun harm hA1
