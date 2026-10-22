-- Prove2me | solution 1 for TsengCGD.Linear.theorem2_a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:13:16.884376+00:00
-- url     : https://prove2.me/submissions/1a484efe-1942-4de2-a6f8-9c2d4a50d66e

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace


namespace TsengCGD.Linear

open TsengCGD.Global

lemma g37_lim0 (A B : ℝ) (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + s * B) : 0 ≤ A := by
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

lemma g37_dot_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (v w : Fin n → ℝ) :
    v ⬝ᵥ (H *ᵥ w) = w ⬝ᵥ (H *ᵥ v) := by
  have hT : Hᵀ = H := by
    have := hH.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]

lemma g37_qf_add {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (d v : Vec n) (s : ℝ) :
    qf H (d + s • v) = qf H d + 2 * s * (WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp d)) + s ^ 2 * qf H v := by
  have := g37_dot_symm H hH (WithLp.ofLp d) (WithLp.ofLp v)
  simp only [qf, WithLp.ofLp_add, WithLp.ofLp_smul, mulVec_add, mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at *
  rw [this]; ring

lemma g37_inner_supp {n : ℕ} (J : Finset (Fin n)) (g v : Vec n) (hv : SupportedOn J v) :
    ⟪g, v⟫ = ∑ j ∈ J, g j * v j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  rw [← Finset.sum_subset (Finset.subset_univ J)]
  · apply Finset.sum_congr rfl; intro j _; ring
  · intro j _ hj; rw [hv j hj]; ring

/-- first-order optimality condition for the CGD direction -/
lemma g37_fo {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Vec n} {J : Finset (Fin n)} {d : Vec n}
    (hD : Convex ℝ D) (hPc : ConvexOn ℝ D P) (hc : 0 ≤ c) (hH : H.IsHermitian)
    (hd : IsDir f D P c H x J d) (e : Vec n) (he : SupportedOn J e) (hxe : x + e ∈ D) :
    0 ≤ ⟪gradient f x, e - d⟫ + WithLp.ofLp (e - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)
      + c * (P (x + e) - P (x + d)) := by
  obtain ⟨hdS, hdD, hdmin⟩ := hd
  apply g37_lim0 _ (qf H (e - d) / 2)
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
  rw [g37_qf_add H hH, inner_add_right, inner_smul_right] at h1
  have h2 : c * P (x + (d + s • (e - d))) ≤ c * ((1 - s) * P (x + d) + s * P (x + e)) :=
    mul_le_mul_of_nonneg_left hP hc
  have h3 : 0 ≤ s * (⟪gradient f x, e - d⟫ + WithLp.ofLp (e - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)
      + c * (P (x + e) - P (x + d)) + s * (qf H (e - d) / 2)) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs0).mp h3; linarith

lemma g37_qf_self {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (d : Vec n) :
    WithLp.ofLp (0 - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d) = - qf H d := by
  simp [qf]

lemma g37_delta_le {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Vec n} {J : Finset (Fin n)} {d : Vec n}
    (hD : Convex ℝ D) (hPc : ConvexOn ℝ D P) (hc : 0 ≤ c) (hH : H.IsHermitian)
    (hd : IsDir f D P c H x J d) (hx : x ∈ D) :
    ⟪gradient f x, d⟫ + qf H d + c * P (x + d) - c * P x ≤ 0 := by
  have := g37_fo hD hPc hc hH hd 0 (fun j _ => by simp) (by simpa using hx)
  rw [g37_qf_self] at this
  simp only [zero_sub, inner_neg_right, add_zero] at this
  linarith


lemma g37_diff {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {y : Vec n} (hy : y ∈ D) : DifferentiableAt ℝ f y := by
  obtain ⟨U, hU, hDU, hf⟩ := hs.smooth
  exact (hf.contDiffAt (hU.mem_nhds (hDU hy))).differentiableAt (by norm_num)

lemma g37_line_deriv {n : ℕ} (h : Vec n → ℝ) (x v : Vec n) (t : ℝ)
    (hd : DifferentiableAt ℝ h (x + t • v)) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := hd.hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

lemma g37_descent {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {L : ℝ} (hL : GradLipOn f D L) {x y : Vec n} (hx : x ∈ D) (hy : y ∈ D) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  set v := y - x with hv
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • v ∈ D := by
    intro t ht
    have e : x + t • v = (1 - t) • x + t • y := by rw [hv]; module
    rw [e]; exact hD hx hy (by linarith [ht.2]) ht.1 (by ring)
  set ψ : ℝ → ℝ := fun t => f (x + t • v) - t * ⟪gradient f x, v⟫ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (⟪gradient f (x + t • v), v⟫ - ⟪gradient f x, v⟫
      - L * t * ‖v‖ ^ 2) t := by
    intro t ht
    have h1 := g37_line_deriv f x v t (g37_diff hs (hmem t ht))
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, v⟫) ⟪gradient f x, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, v⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := (hp.const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t ht => (hψd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hψd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t (Set.Ioo_subset_Icc_self ht)).deriv]
      have hcs : ⟪gradient f (x + t • v) - gradient f x, v⟫ ≤
          ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := real_inner_le_norm _ _
      have hlip := hL.2 (x + t • v) (hmem t (Set.Ioo_subset_Icc_self ht)) x hx
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

theorem lemma5_b_core {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (L : ℝ) (hL : GradLipOn f D L) (lam : ℝ) (hlam : 0 < lam)
    (hHlam : ∀ z : TsengCGD.Global.Vec n, lam * ‖z‖ ^ 2 ≤ TsengCGD.Global.qf H z)
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hαL : α * L ≤ 2 * lam * (1 - σ + σ * γ)) :
    x + α • d ∈ D ∧ TsengCGD.Global.Fc f P c (x + α • d) - TsengCGD.Global.Fc f P c x ≤ σ * α * TsengCGD.Global.Delta f P c γ H x d := by
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  have hPc : ConvexOn ℝ D P := hs.properConvexLsc.2.2.1
  have hc : 0 ≤ c := hs.c_pos.le
  have hxd : x + d ∈ D := hd.2.1
  have e : x + α • d = (1 - α) • x + α • (x + d) := by module
  have hmem : x + α • d ∈ D := by rw [e]; exact hD hx hxd (by linarith) hα0 (by ring)
  refine ⟨hmem, ?_⟩
  have hdes := g37_descent hs hL hx hmem
  rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0] at hdes
  have hP := hPc.2 hx hxd (by linarith : (0:ℝ) ≤ 1 - α) hα0 (by ring)
  simp only [smul_eq_mul] at hP
  rw [← e] at hP
  have hcP := mul_le_mul_of_nonneg_left hP hc
  have hdl := g37_delta_le hD hPc hc hH.1 hd hx
  have hQ := hHlam d
  set Q := qf H d
  set N := ‖d‖ ^ 2
  set a := ⟪gradient f x, d⟫ + c * P (x + d) - c * P x
  have hN : 0 ≤ N := by positivity
  have hκ : 0 ≤ 1 - σ + σ * γ := by nlinarith
  have key : α * a + L / 2 * (α ^ 2 * N) ≤ σ * α * (a + γ * Q) := by
    have h1 : (σ - 1) * a ≥ (1 - σ) * Q := by nlinarith
    have h2 : α * L * N ≤ 2 * lam * (1 - σ + σ * γ) * N := mul_le_mul_of_nonneg_right hαL hN
    have h3 : lam * N * (1 - σ + σ * γ) ≤ Q * (1 - σ + σ * γ) := mul_le_mul_of_nonneg_right hQ hκ
    have h4 : 0 ≤ α * ((σ - 1) * a + σ * γ * Q - α * L * N / 2) := by
      apply mul_nonneg hα0; nlinarith
    nlinarith
  simp only [Fc, Delta]
  nlinarith [mul_le_mul_of_nonneg_left hP hc]

lemma g37_dot_supp {n : ℕ} (J : Finset (Fin n)) (v : Vec n) (w : Fin n → ℝ) (hv : SupportedOn J v) :
    WithLp.ofLp v ⬝ᵥ w = ∑ j ∈ J, v j * w j := by
  simp only [dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ J)]
  intro j _ hj; rw [show (WithLp.ofLp v) j = v j from rfl, hv j hj]; ring

theorem lemma5_a_core {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ)
    (DJ : Set (TsengCGD.Global.Vec n)) (PJ : TsengCGD.Global.Vec n → ℝ) (DJC : Set (TsengCGD.Global.Vec n)) (PJC : TsengCGD.Global.Vec n → ℝ)
    (hw : TsengCGD.Global.IsBlockSepWitness D P J DJ PJ DJC PJC)
    (xbar : TsengCGD.Global.Vec n) (hxbar : xbar ∈ DJ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ J, (gradient f x j + (H *ᵥ WithLp.ofLp d) j) * ((x + α • d) j - xbar j))
        + c * PJ (x + α • d) - c * PJ xbar
      ≤ (α - 1) * ((1 - γ) * TsengCGD.Global.qf H d + TsengCGD.Global.Delta f P c γ H x d) := by
  obtain ⟨hPJ, _, hJeq, hJCeq, hDiff, hPsum⟩ := hw
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  have hPc : ConvexOn ℝ D P := hs.properConvexLsc.2.2.1
  have hc : 0 ≤ c := hs.c_pos.le
  have hdS : SupportedOn J d := hd.1
  have hxd : x + d ∈ D := hd.2.1
  set e : Vec n := WithLp.toLp 2 (fun j => if j ∈ J then xbar j - x j else 0) with he
  have heS : SupportedOn J e := by intro j hj; simp [he, hj]
  have hy1 : ∀ j ∈ J, (x + e) j = xbar j := by intro j hj; simp [he, hj]
  have hy2 : ∀ j, j ∉ J → (x + e) j = x j := by intro j hj; simp [he, hj]
  have hxDJ : x ∈ DJ := ((hDiff x).1 hx).1
  have hxDJC : x ∈ DJC := ((hDiff x).1 hx).2
  have hxdDJ : x + d ∈ DJ := ((hDiff _).1 hxd).1
  have hyDJ : x + e ∈ DJ := ((hJeq _ _ hy1).1).2 hxbar
  have hyDJC : x + e ∈ DJC := ((hJCeq _ _ hy2).1).2 hxDJC
  have hyD : x + e ∈ D := (hDiff _).2 ⟨hyDJ, hyDJC⟩
  have hfo := g37_fo hD hPc hc hH.1 hd e heS hyD
  have hedS : SupportedOn J (e - d) := by intro j hj; simp [heS j hj, hdS j hj]
  rw [g37_inner_supp J _ _ hedS, g37_dot_supp J _ _ hedS] at hfo
  -- P values
  have hPy : P (x + e) = PJ xbar + PJC x := by
    rw [hPsum _ hyD, (hJeq _ _ hy1).2, (hJCeq _ _ hy2).2]
  have hd2 : ∀ j, j ∉ J → (x + d) j = x j := by intro j hj; simp [hdS j hj]
  have hPxd : P (x + d) = PJ (x + d) + PJC x := by rw [hPsum _ hxd, (hJCeq _ _ hd2).2]
  have hPx : P x = PJ x + PJC x := hPsum _ hx
  have hconv := hPJ.2.2.1.2 hxDJ hxdDJ (by linarith : (0:ℝ) ≤ 1 - α) hα0.le (by ring)
  simp only [smul_eq_mul] at hconv
  have ee : (1 - α) • x + α • (x + d) = x + α • d := by module
  rw [ee] at hconv
  have hcc := mul_le_mul_of_nonneg_left hconv hc
  -- sums
  set G : Fin n → ℝ := fun j => gradient f x j + (H *ᵥ WithLp.ofLp d) j with hG
  have hS2 : ∑ j ∈ J, G j * d j = ⟪gradient f x, d⟫ + qf H d := by
    rw [g37_inner_supp J _ _ hdS, qf, g37_dot_supp J _ _ hdS, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp only [hG]; ring
  have hS1 : ∑ j ∈ J, (gradient f x j * (e - d) j + (e - d) j * (H *ᵥ WithLp.ofLp d) j)
      = ∑ j ∈ J, G j * (xbar j - x j) - ∑ j ∈ J, G j * d j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j hj; simp only [hG]; simp [he, hj]; ring
  rw [← Finset.sum_add_distrib, hS1] at hfo
  have hL : ∑ j ∈ J, G j * ((x + α • d) j - xbar j)
      = - ∑ j ∈ J, G j * (xbar j - x j) + α * ∑ j ∈ J, G j * d j := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp; ring
  rw [hL]
  simp only [Delta]
  rw [hPxd, hPx] at *
  rw [hPy] at hfo
  rw [hS2] at hfo ⊢
  nlinarith

theorem theorem1_f_core {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (hrun : TsengCGD.Global.IsCGDRun f D P c J H x d α)
    (lam lamBar : ℝ) (hA1 : TsengCGD.Global.Assumption1 H lam lamBar)
    (β σ γ : ℝ) (αinit : ℕ → ℝ) (harm : TsengCGD.Global.IsArmijo f D P c β σ γ αinit H x d α)
    (hinit : ∃ a > 0, ∀ k, a ≤ αinit k)
    (L : ℝ) (hL : GradLipOn f D L) :
    (∃ a > 0, ∀ k, a ≤ α k) ∧
      (BddBelow (Set.range fun k => TsengCGD.Global.Fc f P c (x k)) →
        Tendsto (fun k => TsengCGD.Global.Delta f P c γ (H k) (x k) (d k)) atTop (𝓝 0) ∧
          Tendsto d atTop (𝓝 0)) := by
  obtain ⟨hpar, hinitpos, harm'⟩ := harm
  obtain ⟨hlam, _, hHb⟩ := hA1
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  have hPc : ConvexOn ℝ D P := hs.properConvexLsc.2.2.1
  have hc : 0 ≤ c := hs.c_pos.le
  have hσ0 := hpar.sigma_pos
  have hσ1 := hpar.sigma_lt_one
  have hγ0 := hpar.gamma_nonneg
  have hγ1 := hpar.gamma_lt_one
  have hβ0 := hpar.beta_pos
  have hκ : 0 < 1 - σ + σ * γ := by nlinarith
  have hL0 : 0 ≤ L := hL.1
  set b := min 1 (2 * lam * (1 - σ + σ * γ) / (L + 1)) with hbdef
  have hb0 : 0 < b := lt_min one_pos (by positivity)
  have pass : ∀ k, ∀ a' : ℝ, 0 < a' → a' ≤ b → ArmijoTest f D P c σ γ (H k) (x k) (d k) a' := by
    intro k a' ha0 hab
    have haL : a' * L ≤ 2 * lam * (1 - σ + σ * γ) := by
      have h1 : a' ≤ 2 * lam * (1 - σ + σ * γ) / (L + 1) := le_trans hab (min_le_right _ _)
      rw [le_div_iff₀ (by linarith)] at h1
      nlinarith [mul_pos hlam hκ]
    have := lemma5_b_core f D P c hs (x k) (hrun.iterate_mem k) (H k) (hrun.H_posDef k) (J k) (d k)
      (hrun.dir k) γ hγ0 hγ1 L hL lam hlam (fun z => (hHb k z).1) σ hσ0 hσ1 a' ha0.le
      (le_trans hab (min_le_left _ _)) haL
    refine ⟨this.1, ?_⟩
    have := this.2
    nlinarith
  obtain ⟨a, ha0, hak⟩ := hinit
  set m := min a (β * b) with hm
  have hm0 : 0 < m := lt_min ha0 (mul_pos hβ0 hb0)
  have hlow : ∀ k, m ≤ α k := by
    intro k
    obtain ⟨j, hj, _, hfail⟩ := harm' k
    cases j with
    | zero => simp at hj; rw [hj]; exact le_trans (min_le_left _ _) (hak k)
    | succ j' =>
      have hf := hfail j' (Nat.lt_succ_self _)
      have hpos : 0 < αinit k * β ^ j' := mul_pos (hinitpos k) (pow_pos hβ0 _)
      have hlt : b < αinit k * β ^ j' := by
        by_contra hcon; push_neg at hcon; exact hf (pass k _ hpos hcon)
      rw [hj, pow_succ]
      calc m ≤ β * b := min_le_right _ _
        _ ≤ β * (αinit k * β ^ j') := mul_le_mul_of_nonneg_left hlt.le hβ0.le
        _ = αinit k * (β ^ j' * β) := by ring
  refine ⟨⟨m, hm0, hlow⟩, ?_⟩
  intro hbdd
  set Δ : ℕ → ℝ := fun k => Delta f P c γ (H k) (x k) (d k) with hΔdef
  have hΔ : ∀ k, Δ k ≤ -((1 - γ) * lam * ‖d k‖ ^ 2) := by
    intro k
    have h1 := g37_delta_le hD hPc hc (hrun.H_posDef k).1 (hrun.dir k) (hrun.iterate_mem k)
    have h2 := (hHb k (d k)).1
    simp only [hΔdef, Delta]
    nlinarith
  have hΔ0 : ∀ k, 0 ≤ -Δ k := fun k => by
    have := hΔ k
    have h1 : 0 < 1 - γ := by linarith
    have : 0 ≤ (1 - γ) * lam * ‖d k‖ ^ 2 := by positivity
    linarith
  set F : ℕ → ℝ := fun k => Fc f P c (x k) with hF
  have hdec : ∀ k, F (k + 1) ≤ F k + α k * σ * Δ k := by
    intro k
    obtain ⟨j, _, htest, _⟩ := harm' k
    simp only [hF, hΔdef]; rw [hrun.step k]; exact htest.2
  set u : ℕ → ℝ := fun k => F k - F (k + 1) with hu
  have hΔu : ∀ k, m * σ * (-Δ k) ≤ u k := by
    intro k
    have h1 := hdec k
    have h2 : 0 ≤ -Δ k := hΔ0 k
    have h3 : m * σ * (-Δ k) ≤ α k * σ * (-Δ k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hlow k) hσ0.le) h2
    simp only [hu]; linarith
  have hu0 : ∀ k, 0 ≤ u k := by
    intro k
    have h2 : 0 ≤ -Δ k := hΔ0 k
    have := hΔu k
    nlinarith [mul_pos hm0 hσ0]
  obtain ⟨B, hB⟩ := hbdd
  have hBk : ∀ k, B ≤ F k := fun k => hB ⟨k, rfl⟩
  have hsum : Summable u := by
    apply summable_of_sum_range_le hu0 (c := F 0 - B)
    intro N
    have : ∑ i ∈ Finset.range N, u i = F 0 - F N := by
      simp only [hu]; rw [Finset.sum_range_sub']
    rw [this]; linarith [hBk N]
  have hut := hsum.tendsto_atTop_zero
  have hmσ : 0 < m * σ := mul_pos hm0 hσ0
  have hnegΔ : Tendsto (fun k => -Δ k) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun k => u k / (m * σ)) hΔ0
      (fun k => (le_div_iff₀' hmσ).mpr (hΔu k))
    simpa using hut.div_const (m * σ)
  refine ⟨by simpa using hnegΔ.neg, ?_⟩
  have hk : 0 < (1 - γ) * lam := mul_pos (by linarith) hlam
  have hsq : Tendsto (fun k => ‖d k‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun k => -Δ k / ((1 - γ) * lam)) (fun k => by positivity)
      (fun k => (le_div_iff₀' hk).mpr (by have := hΔ k; linarith))
    simpa using hnegΔ.div_const ((1 - γ) * lam)
  have hn : Tendsto (fun k => ‖d k‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn


open Classical in
lemma g37_affine_lb {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ}
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

open Classical in
lemma g37_exists_min {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c) {x : Vec n} (hx : x ∈ D)
    (g : Vec n) :
    ∃ d, x + d ∈ D ∧ ∀ d', x + d' ∈ D →
      ⟪g, d⟫ + ‖d‖ ^ 2 / 2 + c * P (x + d) ≤ ⟪g, d'⟫ + ‖d'‖ ^ 2 / 2 + c * P (x + d') := by
  obtain ⟨A, B, hA, hAB⟩ := g37_affine_lb hP
  have hlsc := hP.2.2.2
  set Ψ : Vec n → EReal := fun y => if y ∈ D then (P y : EReal) else ⊤ with hΨ
  set q : Vec n → ℝ := fun d => (⟪g, d⟫ + ‖d‖ ^ 2 / 2) / c with hq
  have hqc : Continuous q := by simp only [hq]; fun_prop
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
  set K := Φ ⁻¹' Set.Iic (Φ 0) with hK
  have hKc : IsClosed K := hΦl.isClosed_preimage _
  have h0D : x + 0 ∈ D := by simpa using hx
  have hΦ0 : Φ 0 = ((P x : ℝ) : EReal) := by rw [hΦin 0 h0D]; simp [hq]
  have hKD : ∀ d ∈ K, x + d ∈ D ∧ P (x + d) + q d ≤ P x := by
    intro d hd
    simp only [hK, Set.mem_preimage, Set.mem_Iic, hΦ0] at hd
    by_cases hdD : x + d ∈ D
    · rw [hΦin d hdD] at hd
      exact ⟨hdD, EReal.coe_le_coe_iff.mp hd⟩
    · rw [hΦout d hdD] at hd; simp at hd
  set b := ‖g‖ + c * A with hb
  set M := c * (P x + A * ‖x‖ + B) with hM
  set R := 2 * b + 2 * |M| + 2 with hR
  have hKb : K ⊆ Metric.closedBall 0 R := by
    intro d hd
    obtain ⟨hdD, hle⟩ := hKD d hd
    have h1 := hAB _ hdD
    have h2 : ‖x + d‖ ≤ ‖x‖ + ‖d‖ := norm_add_le _ _
    have h3 : -‖g‖ * ‖d‖ ≤ ⟪g, d⟫ := by
      have := abs_real_inner_le_norm g d
      have := neg_abs_le ⟪g, d⟫
      nlinarith
    have h4 : q d * c = ⟪g, d⟫ + ‖d‖ ^ 2 / 2 := by simp only [hq]; field_simp
    have h5 : ‖d‖ ^ 2 / 2 - b * ‖d‖ ≤ M := by
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
    nlinarith [abs_nonneg M]
  have hKcomp : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKc (Metric.isBounded_closedBall.subset hKb)
  have h0K : (0 : Vec n) ∈ K := by simp [hK]
  obtain ⟨dstar, hdK, hmin⟩ := (hΦl.lowerSemicontinuousOn K).exists_isMinOn ⟨0, h0K⟩ hKcomp
  obtain ⟨hdD, _⟩ := hKD dstar hdK
  refine ⟨dstar, hdD, ?_⟩
  intro d' hd'
  have hle : Φ dstar ≤ Φ d' := by
    by_cases hd'K : d' ∈ K
    · exact hmin hd'K
    · have h1 : Φ dstar ≤ Φ 0 := hdK
      simp only [hK, Set.mem_preimage, Set.mem_Iic, not_le] at hd'K
      exact le_trans h1 hd'K.le
  rw [hΦin _ hdD, hΦin _ hd', EReal.coe_le_coe_iff] at hle
  have e1 : q dstar * c = ⟪g, dstar⟫ + ‖dstar‖ ^ 2 / 2 := by simp only [hq]; field_simp
  have e2 : q d' * c = ⟪g, d'⟫ + ‖d'‖ ^ 2 / 2 := by simp only [hq]; field_simp
  have := mul_le_mul_of_nonneg_left hle hc.le
  nlinarith


lemma g37_dI_spec {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {x : Vec n} (hx : x ∈ D) :
    IsDir f D P c 1 x Finset.univ (dI f D P c x) := by
  obtain ⟨d, hdD, hmin⟩ := g37_exists_min hs.properConvexLsc hs.c_pos hx (gradient f x)
  have hq1 : ∀ v : Vec n, qf (1 : Matrix (Fin n) (Fin n) ℝ) v = ‖v‖ ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [qf, dotProduct, sq]
  have : IsDir f D P c 1 x Finset.univ d := by
    refine ⟨fun j hj => absurd (Finset.mem_univ j) hj, hdD, ?_⟩
    intro d' _ hd'
    simp only [subObj, hq1]
    exact hmin d' hd'
  exact Classical.epsilon_spec ⟨d, this⟩

lemma g37_mix {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {J : Finset (Fin n)}
    {DJ : Set (Vec n)} {PJ : Vec n → ℝ} {DJC : Set (Vec n)} {PJC : Vec n → ℝ}
    (hw : IsBlockSepWitness D P J DJ PJ DJC PJC) {a b y : Vec n} (ha : a ∈ D) (hb : b ∈ D)
    (h1 : ∀ j ∈ J, y j = a j) (h2 : ∀ j, j ∉ J → y j = b j) : y ∈ D := by
  obtain ⟨_, _, hJeq, hJCeq, hDiff, _⟩ := hw
  exact (hDiff y).2 ⟨((hJeq y a h1).1).2 ((hDiff a).1 ha).1, ((hJCeq y b h2).1).2 ((hDiff b).1 hb).2⟩

lemma g37_Poff {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {J : Finset (Fin n)}
    {DJ : Set (Vec n)} {PJ : Vec n → ℝ} {DJC : Set (Vec n)} {PJC : Vec n → ℝ}
    (hw : IsBlockSepWitness D P J DJ PJ DJC PJC) {y z : Vec n} (hy : y ∈ D) (hz : z ∈ D)
    (h : ∀ j, j ∉ J → y j = z j) : P y - P z = PJ y - PJ z := by
  obtain ⟨_, _, _, hJCeq, _, hPsum⟩ := hw
  rw [hPsum y hy, hPsum z hz, (hJCeq y z h).2]; ring

lemma g37_PJon {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {J : Finset (Fin n)}
    {DJ : Set (Vec n)} {PJ : Vec n → ℝ} {DJC : Set (Vec n)} {PJC : Vec n → ℝ}
    (hw : IsBlockSepWitness D P J DJ PJ DJC PJC) {y z : Vec n}
    (h : ∀ j ∈ J, y j = z j) : PJ y = PJ z := (hw.2.2.1 y z h).2

lemma g37_psd_cs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (lamBar : ℝ)
    (hlb : 0 ≤ lamBar) (hq0 : ∀ z, 0 ≤ qf H z) (hqb : ∀ z, qf H z ≤ lamBar * ‖z‖ ^ 2)
    (z d : Vec n) : WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp d) ≤ lamBar * ‖d‖ * ‖z‖ := by
  set B := WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp d)
  have hdisc : discrim (qf H z) (2 * B) (qf H d) ≤ 0 := by
    apply discrim_le_zero
    intro t
    have := hq0 (d + t • z)
    rw [g37_qf_add H hH] at this
    nlinarith
  rw [discrim] at hdisc
  have h1 : B ^ 2 ≤ qf H d * qf H z := by nlinarith
  have h2 : qf H d * qf H z ≤ (lamBar * ‖d‖ ^ 2) * (lamBar * ‖z‖ ^ 2) :=
    mul_le_mul (hqb d) (hqb z) (hq0 z) (by have := hq0 d; nlinarith [hqb d])
  have h3 : B ^ 2 ≤ (lamBar * ‖d‖ * ‖z‖) ^ 2 := by nlinarith
  exact le_trans (le_abs_self B) (abs_le_of_sq_le_sq h3 (by positivity))

lemma g37_block {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {L : ℝ} (hL : GradLipOn f D L) {J : Finset (Fin n)}
    {DJ : Set (Vec n)} {PJ : Vec n → ℝ} {DJC : Set (Vec n)} {PJC : Vec n → ℝ}
    (hw : IsBlockSepWitness D P J DJ PJ DJC PJC) {xk xl : Vec n} (hxk : xk ∈ D) (hxl : xl ∈ D)
    (hagree : ∀ j ∈ J, xl j = xk j) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (lamBar : ℝ) (hlb : 0 ≤ lamBar) (hq0 : ∀ z, 0 ≤ qf H z) (hqb : ∀ z, qf H z ≤ lamBar * ‖z‖ ^ 2)
    {dl : Vec n} (hdl : IsDir f D P c H xl J dl) {dk : Vec n}
    (hdk : IsDir f D P c 1 xk Finset.univ dk) :
    ‖(WithLp.toLp 2 (fun j => if j ∈ J then dk j else 0) : Vec n)‖
      ≤ L * ‖xl - xk‖ + (lamBar + 2) * ‖dl‖ := by
  have hD : Convex ℝ D := hs.properConvexLsc.2.1
  have hPc : ConvexOn ℝ D P := hs.properConvexLsc.2.2.1
  have hc : 0 ≤ c := hs.c_pos.le
  set w : Vec n := WithLp.toLp 2 (fun j => if j ∈ J then dk j else 0) with hwdef
  have hwJ : ∀ j ∈ J, w j = dk j := by intro j hj; simp [hwdef, hj]
  have hwS : SupportedOn J w := by intro j hj; simp [hwdef, hj]
  have hdlS : SupportedOn J dl := hdl.1
  have hxld : xl + dl ∈ D := hdl.2.1
  have hxkd : xk + dk ∈ D := hdk.2.1
  set e : Vec n := dk - w + dl with he
  -- memberships
  have m1 : xk + dl ∈ D := g37_mix hw hxld hxk (fun j hj => by simp [hagree j hj])
    (fun j hj => by simp [hdlS j hj])
  have m2 : xk + e ∈ D := g37_mix hw m1 hxkd (fun j hj => by simp [he, hwJ j hj])
    (fun j hj => by simp [he, hwS j hj, hdlS j hj])
  have m3 : xk + w ∈ D := g37_mix hw hxkd hxk (fun j hj => by simp [hwJ j hj])
    (fun j hj => by simp [hwS j hj])
  have m4 : xl + w ∈ D := g37_mix hw m3 hxl (fun j hj => by simp [hagree j hj])
    (fun j hj => by simp [hwS j hj])
  have fo1 := g37_fo hD hPc hc isHermitian_one hdk e (fun j hj => absurd (Finset.mem_univ j) hj) m2
  have fo2 := g37_fo hD hPc hc hH hdl w hwS m4
  -- P relations
  have p1 : P (xk + e) - P (xk + dk) = PJ (xk + dl) - PJ (xk + w) := by
    rw [g37_Poff hw m2 hxkd (fun j hj => by simp [he, hwS j hj, hdlS j hj]),
      g37_PJon hw (y := xk + e) (z := xk + dl) (fun j hj => by simp [he, hwJ j hj]),
      g37_PJon hw (y := xk + dk) (z := xk + w) (fun j hj => by simp [hwJ j hj])]
  have p2 : P (xl + w) - P (xl + dl) = PJ (xk + w) - PJ (xk + dl) := by
    rw [g37_Poff hw m4 hxld (fun j hj => by simp [hwS j hj, hdlS j hj]),
      g37_PJon hw (y := xl + w) (z := xk + w) (fun j hj => by simp [hagree j hj]),
      g37_PJon hw (y := xl + dl) (z := xk + dl) (fun j hj => by simp [hagree j hj])]
  rw [p1] at fo1
  rw [p2] at fo2
  set u := w - dl with hu
  have hed : e - dk = -u := by rw [he, hu]; abel
  rw [hed, one_mulVec] at fo1
  have hdot : ∀ a b : Vec n, WithLp.ofLp a ⬝ᵥ WithLp.ofLp b = ⟪a, b⟫ := by
    intro a b
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; simp
  rw [hdot] at fo1
  have huS : SupportedOn J u := by intro j hj; simp [hu, hwS j hj, hdlS j hj]
  have hzero : ⟪-u, dk - w⟫ = 0 := by
    rw [real_inner_comm, g37_inner_supp J _ _ (by intro j hj; simp [huS j hj])]
    apply Finset.sum_eq_zero; intro j hj; simp [hwJ j hj]
  have hdkw : ⟪-u, dk⟫ = ⟪-u, w⟫ := by
    have : ⟪-u, dk⟫ = ⟪-u, w⟫ + ⟪-u, dk - w⟫ := by
      rw [← inner_add_right]; congr 1; abel
    rw [this, hzero, add_zero]
  have hwu : w = u + dl := by rw [hu]; abel
  have hinner : ⟪-u, w⟫ = -(‖u‖ ^ 2) - ⟪u, dl⟫ := by
    rw [hwu, inner_neg_left, inner_add_right, real_inner_self_eq_norm_sq]; ring
  rw [hdkw, hinner, inner_neg_right] at fo1
  have hHt := g37_psd_cs H hH lamBar hlb hq0 hqb u dl
  have hg : ⟪gradient f xl, u⟫ - ⟪gradient f xk, u⟫ ≤ L * ‖xl - xk‖ * ‖u‖ := by
    rw [← inner_sub_left]
    have := real_inner_le_norm (gradient f xl - gradient f xk) u
    have h2 := hL.2 xl hxl xk hxk
    nlinarith [norm_nonneg u]
  have hud : -⟪u, dl⟫ ≤ ‖u‖ * ‖dl‖ := by
    have := abs_real_inner_le_norm u dl
    have := neg_abs_le ⟪u, dl⟫
    linarith
  have hkey : ‖u‖ ^ 2 ≤ (L * ‖xl - xk‖ + (lamBar + 1) * ‖dl‖) * ‖u‖ := by nlinarith
  have hK0 : 0 ≤ L * ‖xl - xk‖ + (lamBar + 1) * ‖dl‖ := by
    have := hL.1; positivity
  have hu_le : ‖u‖ ≤ L * ‖xl - xk‖ + (lamBar + 1) * ‖dl‖ := by
    by_contra hcon; push_neg at hcon
    nlinarith [norm_nonneg u]
  have : ‖w‖ ≤ ‖u‖ + ‖dl‖ := by rw [hwu]; exact norm_add_le _ _
  linarith


theorem theorem2_a_core {n : ℕ} (L lam lamBar : ℝ) :
    ∃ C > 0, ∀ (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
      (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (t : ℕ → ℕ),
      TsengCGD.Global.Standing f D P c → GradLipOn f D L → TsengCGD.Global.IsCGDRun f D P c J H x d α →
      (∀ k, x k ∈ D) → TsengCGD.Global.Assumption1 H lam lamBar → RestrictedGaussSeidel J t →
      (∀ k, TsengCGD.Global.BlockSeparable D P (J k)) →
      ∀ abar : ℝ, (∀ j, α j ≤ abar) →
      ∀ i, ‖TsengCGD.Global.dI f D P c (x (t i))‖ ≤ max 1 abar * C * r t d i := by
  refine ⟨n * |L| + |lamBar| + 2, by positivity, ?_⟩
  intro f D P c J H x d α t hs hL hrun hxD hA1 hRGS hsep abar habar i
  obtain ⟨hlam, hll, hHb⟩ := hA1
  have hlb : 0 ≤ lamBar := by linarith
  have hL0 := hL.1
  obtain ⟨htmono, _, hcyc⟩ := hRGS
  obtain ⟨hpd, hcov⟩ := hcyc i
  have habar0 : 0 ≤ abar := le_trans (hrun.step_pos 0).le (habar 0)
  set k := t i with hk
  set τ := t (i + 1) with hτ
  set I := Finset.Ico k τ with hI
  set v := dI f D P c (x k) with hvdef
  have hv := g37_dI_spec hs (hxD k)
  set W : ℕ → Vec n := fun ℓ => WithLp.toLp 2 (fun j => if j ∈ J ℓ then v j else 0) with hW
  have hagree : ∀ ℓ ∈ I, ∀ j ∈ J ℓ, x ℓ j = x k j := by
    intro ℓ hℓ j hj
    have hℓ' := Finset.mem_Ico.mp hℓ
    have : ∀ m, k ≤ m → m ≤ ℓ → x m j = x k j := by
      intro m hkm
      induction m, hkm using Nat.le_induction with
      | base => intro _; rfl
      | succ m hkm ih =>
        intro hmℓ
        have hmI : m ∈ I := Finset.mem_Ico.mpr ⟨hkm, by omega⟩
        have hne : m ≠ ℓ := by omega
        have hdisj : Disjoint (J m) (J ℓ) := hpd (Finset.mem_coe.mpr hmI) (Finset.mem_coe.mpr hℓ) hne
        have hjm : j ∉ J m := Finset.disjoint_right.mp hdisj hj
        rw [hrun.step m]
        simp [(hrun.dir m).1 j hjm]
        exact ih (by omega)
    exact this ℓ hℓ'.1 le_rfl
  have hdist : ∀ ℓ ∈ I, ‖x ℓ - x k‖ ≤ abar * r t d i := by
    have : ∀ m, k ≤ m → ‖x m - x k‖ ≤ abar * ∑ m' ∈ Finset.Ico k m, ‖d m'‖ := by
      intro m hkm
      induction m, hkm using Nat.le_induction with
      | base => simp
      | succ m hkm ih =>
        rw [hrun.step m, Finset.sum_Ico_succ_top hkm, mul_add]
        have e : x m + α m • d m - x k = (x m - x k) + α m • d m := by abel
        rw [e]
        calc ‖(x m - x k) + α m • d m‖ ≤ ‖x m - x k‖ + ‖α m • d m‖ := norm_add_le _ _
          _ ≤ _ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hrun.step_pos m)]
            have := mul_le_mul_of_nonneg_right (habar m) (norm_nonneg (d m))
            linarith
    intro ℓ hℓ
    have hm := Finset.mem_Ico.mp hℓ
    refine le_trans (this ℓ hm.1) (mul_le_mul_of_nonneg_left ?_ habar0)
    simp only [r]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hm.2.le)
      (fun _ _ _ => norm_nonneg _)
  have hblock : ∀ ℓ ∈ I, ‖W ℓ‖ ≤ L * (abar * r t d i) + (lamBar + 2) * ‖d ℓ‖ := by
    intro ℓ hℓ
    obtain ⟨DJ, PJ, DJC, PJC, hw⟩ := hsep ℓ
    have := g37_block hs hL hw (hxD k) (hxD ℓ) (hagree ℓ hℓ) (hrun.H_posDef ℓ).1 lamBar hlb
      (fun z => le_trans (by positivity) (hHb ℓ z).1) (fun z => (hHb ℓ z).2) (hrun.dir ℓ) hv
    have h2 := mul_le_mul_of_nonneg_left (hdist ℓ hℓ) hL0
    simp only [hW]
    linarith
  have hnorm : ‖v‖ ≤ ∑ ℓ ∈ I, ‖W ℓ‖ := by
    have h1 : ‖v‖ ^ 2 = ∑ ℓ ∈ I, ‖W ℓ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have : ∀ ℓ, ‖W ℓ‖ ^ 2 = ∑ j ∈ J ℓ, ‖v j‖ ^ 2 := by
        intro ℓ
        have hh : ∑ j ∈ J ℓ, ‖v j‖ ^ 2 = ∑ j, if j ∈ J ℓ then ‖v j‖ ^ 2 else 0 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
        rw [EuclideanSpace.norm_sq_eq, hh]
        apply Finset.sum_congr rfl; intro j _
        by_cases hj : j ∈ J ℓ <;> simp [hW, hj]
      simp_rw [this]
      rw [← Finset.sum_biUnion hpd, hcov]
    have h2 : ∑ ℓ ∈ I, ‖W ℓ‖ ^ 2 ≤ (∑ ℓ ∈ I, ‖W ℓ‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
    have h3 : 0 ≤ ∑ ℓ ∈ I, ‖W ℓ‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have := abs_le_of_sq_le_sq (h1 ▸ h2) h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hcard : (I.card : ℝ) ≤ n := by
    have h1 : (I.biUnion J).card = ∑ ℓ ∈ I, (J ℓ).card := Finset.card_biUnion hpd
    rw [hcov, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : I.card ≤ ∑ ℓ ∈ I, (J ℓ).card := by
      rw [Finset.card_eq_sum_ones]; apply Finset.sum_le_sum; intro ℓ _
      exact (hrun.J_nonempty ℓ).card_pos
    rw [← h1] at h2
    exact_mod_cast h2
  have hsum : ∑ ℓ ∈ I, ‖W ℓ‖ ≤ I.card * (L * (abar * r t d i)) + (lamBar + 2) * r t d i := by
    calc ∑ ℓ ∈ I, ‖W ℓ‖ ≤ ∑ ℓ ∈ I, (L * (abar * r t d i) + (lamBar + 2) * ‖d ℓ‖) :=
          Finset.sum_le_sum hblock
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; rfl
  have hr0 : 0 ≤ r t d i := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [abs_of_nonneg hL0, abs_of_nonneg hlb]
  set M := max 1 abar
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMa : abar ≤ M := le_max_right _ _
  have e1 : (I.card : ℝ) * (L * (abar * r t d i)) ≤ n * L * M * r t d i := by
    have := mul_le_mul_of_nonneg_right hcard (mul_nonneg hL0 (mul_nonneg habar0 hr0))
    have h2 : (n : ℝ) * (L * (abar * r t d i)) ≤ n * (L * (M * r t d i)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hL0
      exact mul_le_mul_of_nonneg_right hMa hr0
    nlinarith
  have e2 : (lamBar + 2) * r t d i ≤ M * (lamBar + 2) * r t d i := by
    have : 0 ≤ (lamBar + 2) * r t d i := by positivity
    nlinarith
  nlinarith

end TsengCGD.Linear

open TsengCGD.Linear


theorem solution {n : ℕ} (L lam lamBar : ℝ) :
    ∃ C > 0, ∀ (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
      (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (t : ℕ → ℕ),
      TsengCGD.Global.Standing f D P c → GradLipOn f D L → TsengCGD.Global.IsCGDRun f D P c J H x d α →
      (∀ k, x k ∈ D) → TsengCGD.Global.Assumption1 H lam lamBar → RestrictedGaussSeidel J t →
      (∀ k, TsengCGD.Global.BlockSeparable D P (J k)) →
      ∀ abar : ℝ, (∀ j, α j ≤ abar) →
      ∀ i, ‖TsengCGD.Global.dI f D P c (x (t i))‖ ≤ max 1 abar * C * r t d i := by
  exact theorem2_a_core L lam lamBar
