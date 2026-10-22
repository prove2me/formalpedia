-- Prove2me | solution 1 for TsengCGD.Global.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:43:18.230832+00:00
-- url     : https://prove2.me/submissions/943f26e2-2ea5-4ed1-9696-c8a6bc9d41f6

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

open Classical in
lemma g38_affine_lb {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ}
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ y ∈ D, -A * ‖y‖ - B ≤ P y := by
  obtain ⟨⟨x0, hx0⟩, _, hPc, hlsc⟩ := hP
  set Ψ : Vec n → EReal := fun y => if y ∈ D then (P y : EReal) else ⊤ with hΨ
  set S : Set (Vec n × ℝ) := {p | p.1 ∈ D ∧ P p.1 ≤ p.2} with hS
  have hSconv : Convex ℝ S := hPc.convex_epigraph
  have hSclosed : IsClosed S := by
    have h1 := hlsc.isClosed_epigraph
    have e : S = (Prod.map id (fun t : ℝ => (t : EReal))) ⁻¹' {p : Vec n × EReal | Ψ p.1 ≤ p.2} := by
      ext ⟨y, t⟩
      simp only [hS, hΨ, Set.mem_setOf_eq, Set.mem_preimage, Prod.map_apply, id]
      by_cases hy : y ∈ D <;> simp [hy]
    rw [e]
    exact h1.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hnot : (x0, P x0 - 1) ∉ S := by simp [hS]
  obtain ⟨f, u, hfu, hS'⟩ := geometric_hahn_banach_point_closed hSconv hSclosed hnot
  have hsplit : ∀ y : Vec n, ∀ t : ℝ, f (y, t) = f (y, 0) + t * f (0, 1) := by
    intro y t
    have : ((y, t) : Vec n × ℝ) = (y, 0) + t • ((0 : Vec n), (1:ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set a := f (0, 1) with ha
  have h0 := hS' (x0, P x0) ⟨hx0, le_rfl⟩
  rw [hsplit] at h0 hfu
  have hapos : 0 < a := by nlinarith
  refine ⟨‖f‖ / a, -u / a, by positivity, ?_⟩
  intro y hy
  have h1 := hS' (y, P y) ⟨hy, le_rfl⟩
  rw [hsplit] at h1
  have h2 : f (y, 0) ≤ ‖f‖ * ‖y‖ := by
    have := f.le_opNorm (y, 0)
    have hn : ‖((y, 0) : Vec n × ℝ)‖ = ‖y‖ := by simp
    rw [hn] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  have h3 : -(‖f‖ / a) * ‖y‖ - -u / a = (u - ‖f‖ * ‖y‖) / a := by field_simp; ring
  rw [h3, div_le_iff₀ hapos]
  nlinarith

lemma g38_qf_lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    ∃ l > 0, ∀ v : Vec n, l * ‖v‖ ^ 2 ≤ qf H v := by
  have hunit : ∀ v : Vec n, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Vec n) 1 := by
    intro v hv
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    simp [norm_smul, hnv.ne']
  by_cases hS : (Metric.sphere (0 : Vec n) 1).Nonempty
  · obtain ⟨v0, hv0, hmin⟩ :=
      (isCompact_sphere (0 : Vec n) 1).exists_isMinOn hS (g38_qf_cont H).continuousOn
    have hv0ne : v0 ≠ 0 := by
      intro h; rw [h] at hv0; simp at hv0
    refine ⟨qf H v0, g38_qf_pos hH hv0ne, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst hv; simp [qf]
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have := isMinOn_iff.mp hmin _ (hunit v hv)
      rw [g38_qf_smul] at this
      calc qf H v0 * ‖v‖ ^ 2 ≤ (‖v‖⁻¹) ^ 2 * qf H v * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = qf H v := by field_simp
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp [qf]
    · exact absurd ⟨_, hunit v hv⟩ hS

lemma g38_supp_closed {n : ℕ} (J : Finset (Fin n)) : IsClosed {d : Vec n | SupportedOn J d} := by
  have : {d : Vec n | SupportedOn J d} = ⋂ j ∈ (Jᶜ : Finset (Fin n)), {d : Vec n | d j = 0} := by
    ext d; simp [SupportedOn]
  rw [this]
  exact isClosed_biInter (fun j _ => isClosed_eq (by fun_prop) continuous_const)

open Classical in
lemma g38_exists_dir {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c) {x : Vec n} (hx : x ∈ D)
    (g : Vec n) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (J : Finset (Fin n)) :
    ∃ d, SupportedOn J d ∧ x + d ∈ D ∧ ∀ d', SupportedOn J d' → x + d' ∈ D →
      ⟪g, d⟫ + qf H d / 2 + c * P (x + d) ≤ ⟪g, d'⟫ + qf H d' / 2 + c * P (x + d') := by
  obtain ⟨A, B, hA, hAB⟩ := g38_affine_lb hP
  obtain ⟨l, hl, hql⟩ := g38_qf_lower H hH
  have hlsc := hP.2.2.2
  set Ψ : Vec n → EReal := fun y => if y ∈ D then (P y : EReal) else ⊤ with hΨ
  set q : Vec n → ℝ := fun d => (⟪g, d⟫ + qf H d / 2) / c with hq
  have hqc : Continuous q := by
    have := g38_qf_cont H
    simp only [hq]; fun_prop
  set Φ : Vec n → EReal := fun d => Ψ (x + d) + (q d : EReal) with hΦ
  have hΦl : LowerSemicontinuous Φ := by
    apply LowerSemicontinuous.add'
    · exact hlsc.comp (continuous_const.add continuous_id)
    · exact (continuous_coe_real_ereal.comp hqc).lowerSemicontinuous
    · intro d
      apply EReal.continuousAt_add
      · right; simp
      · right; simp
  have hΦin : ∀ d, x + d ∈ D → Φ d = ((P (x + d) + q d : ℝ) : EReal) := by
    intro d hd; simp [hΦ, hΨ, hd]
  have hΦout : ∀ d, x + d ∉ D → Φ d = ⊤ := by
    intro d hd; simp [hΦ, hΨ, hd]
  set K := Φ ⁻¹' Set.Iic (Φ 0) ∩ {d : Vec n | SupportedOn J d} with hK
  have hKc : IsClosed K := (hΦl.isClosed_preimage _).inter (g38_supp_closed J)
  have h0D : x + 0 ∈ D := by simpa using hx
  have hΦ0 : Φ 0 = ((P x : ℝ) : EReal) := by rw [hΦin 0 h0D]; simp [hq, g38_qf_zero]
  have hKD : ∀ d ∈ K, x + d ∈ D ∧ P (x + d) + q d ≤ P x := by
    intro d hd
    have hd1 := hd.1
    simp only [Set.mem_preimage, Set.mem_Iic, hΦ0] at hd1
    by_cases hdD : x + d ∈ D
    · rw [hΦin d hdD] at hd1
      exact ⟨hdD, EReal.coe_le_coe_iff.mp hd1⟩
    · rw [hΦout d hdD] at hd1; simp at hd1
  set b := ‖g‖ + c * A with hb
  set M := c * (P x + A * ‖x‖ + B) with hM
  set R := 2 * (b + |M| + 1) / l + 1 with hR
  have hKb : K ⊆ Metric.closedBall 0 R := by
    intro d hd
    obtain ⟨hdD, hle⟩ := hKD d hd
    have h1 := hAB _ hdD
    have h2 : ‖x + d‖ ≤ ‖x‖ + ‖d‖ := norm_add_le _ _
    have h3 : -‖g‖ * ‖d‖ ≤ ⟪g, d⟫ := by
      have := abs_real_inner_le_norm g d
      have := neg_abs_le ⟪g, d⟫
      nlinarith
    have h4 : q d * c = ⟪g, d⟫ + qf H d / 2 := by simp only [hq]; field_simp
    have hqd := hql d
    have h5 : l * ‖d‖ ^ 2 / 2 - b * ‖d‖ ≤ M := by
      have hcle := mul_le_mul_of_nonneg_left hle hc.le
      have hAd := mul_le_mul_of_nonneg_left h2 hA
      have : c * (-A * ‖x + d‖ - B) ≤ c * P (x + d) := mul_le_mul_of_nonneg_left h1 hc.le
      simp only [hb, hM]
      nlinarith
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push_neg at hcon
    have hb0 : 0 ≤ b := by positivity
    have hM' : M ≤ |M| := le_abs_self M
    have ht : 0 ≤ ‖d‖ := norm_nonneg d
    have hR1 : 1 ≤ R := by
      have : 0 ≤ 2 * (b + |M| + 1) / l := by positivity
      simp only [hR]; linarith
    have hlR : l * R / 2 - b ≥ |M| + 1 := by
      simp only [hR]; field_simp; nlinarith [abs_nonneg M]
    have h6 : l * ‖d‖ / 2 - b ≥ |M| + 1 := by nlinarith
    have h7 : ‖d‖ * (l * ‖d‖ / 2 - b) ≥ 1 * (|M| + 1) :=
      mul_le_mul (by linarith) h6 (by positivity) (by linarith)
    nlinarith [abs_nonneg M]
  have hKcomp : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKc (Metric.isBounded_closedBall.subset hKb)
  have h0K : (0 : Vec n) ∈ K := ⟨by simp, fun j _ => by simp⟩
  obtain ⟨dstar, hdK, hmin⟩ := (hΦl.lowerSemicontinuousOn K).exists_isMinOn ⟨0, h0K⟩ hKcomp
  obtain ⟨hdD, _⟩ := hKD dstar hdK
  refine ⟨dstar, hdK.2, hdD, ?_⟩
  intro d' hd's hd'
  have hle : Φ dstar ≤ Φ d' := by
    by_cases hd'K : d' ∈ K
    · exact hmin hd'K
    · have h1 : Φ dstar ≤ Φ 0 := hdK.1
      have : ¬ Φ d' ≤ Φ 0 := fun h => hd'K ⟨h, hd's⟩
      exact le_trans h1 (not_le.mp this).le
  rw [hΦin _ hdD, hΦin _ hd', EReal.coe_le_coe_iff] at hle
  have e1 : q dstar * c = ⟪g, dstar⟫ + qf H dstar / 2 := by simp only [hq]; field_simp
  have e2 : q d' * c = ⟪g, d'⟫ + qf H d' / 2 := by simp only [hq]; field_simp
  have := mul_le_mul_of_nonneg_left hle hc.le
  nlinarith

lemma g38_dH_spec {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {x : Vec n} (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) :
    IsDir f D P c H x J (dH f D P c H x J) := by
  obtain ⟨d, hdS, hdD, hmin⟩ := g38_exists_dir hs.properConvexLsc hs.c_pos hx (gradient f x) H hH J
  exact Classical.epsilon_spec ⟨d, hdS, hdD, fun d' h1 h2 => by simpa [subObj] using hmin d' h1 h2⟩

theorem lemma2_core {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    IsStationary f D P c x ↔ dH f D P c H x Finset.univ = 0 := by
  have hdir := g38_dH_spec hs hx H hH Finset.univ
  set d := dH f D P c H x Finset.univ with hd
  have hc := hs.c_pos
  constructor
  · intro hst
    obtain ⟨⟨r, hr, hineq⟩, hL⟩ := lemma1_core f D P c hs x hx Finset.univ H hH d hdir
    set L := ⟪gradient f x, d⟫ + c * P (x + d) - c * P x with hLdef
    have hL0 : 0 ≤ L := by
      by_contra hneg
      push_neg at hneg
      have hε : 0 < -L / 4 := by linarith
      have h1 := hst.2 d (-L / 4) hε
      have h2 : ∀ᶠ a in 𝓝[>] (0:ℝ), r a / a < -L / 4 := hr.eventually (gt_mem_nhds hε)
      obtain ⟨a, ha1, ha2, ha3⟩ := (h1.and (h2.and (Ioc_mem_nhdsGT one_pos))).exists
      obtain ⟨hmem, hle⟩ := hineq a ha3
      have hpos := ha3.1
      have h4 := ha1 hmem
      rw [le_div_iff₀ hpos] at h4
      rw [div_lt_iff₀ hpos] at ha2
      nlinarith
    have hq : qf H d ≤ 0 := by linarith
    by_contra hne
    have := g38_qf_pos hH hne
    linarith
  · intro h0
    refine ⟨hx, fun v ε hε => ?_⟩
    have hmin := hdir.2.2
    rw [h0] at hmin
    have hsl := g38_slope hs hx v
    have hlin : Tendsto (fun a : ℝ => a * qf H v / 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have : Tendsto (fun a : ℝ => a * qf H v / 2) (𝓝 (0:ℝ)) (𝓝 (0 * qf H v / 2)) := by
        apply Continuous.tendsto; fun_prop
      simpa using this.mono_left nhdsWithin_le_nhds
    have hcomb := hsl.sub hlin
    rw [sub_zero] at hcomb
    filter_upwards [hcomb.eventually (lt_mem_nhds (show -ε < (0:ℝ) by linarith)),
      self_mem_nhdsWithin] with a ha hapos
    intro hmem
    have hapos' : 0 < a := hapos
    have h1 := hmin (a • v) (fun j hj => absurd (Finset.mem_univ j) hj) hmem
    simp only [subObj, g38_qf_zero, inner_zero_right, add_zero, zero_add, g38_qf_smul,
      inner_smul_right] at h1
    have e : (f (x + a • v) - f x - a * ⟪gradient f x, v⟫) / a - a * qf H v / 2 =
        (f (x + a • v) - f x - a * ⟪gradient f x, v⟫ - a ^ 2 * qf H v / 2) / a := by
      field_simp
    rw [e, lt_div_iff₀ hapos'] at ha
    rw [le_div_iff₀ hapos']
    simp only [Fc]
    nlinarith

end TsengCGD.Global

open TsengCGD.Global


theorem solution {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    IsStationary f D P c x ↔ dH f D P c H x Finset.univ = 0 := by
  exact lemma2_core f D P c hs x hx H hH
