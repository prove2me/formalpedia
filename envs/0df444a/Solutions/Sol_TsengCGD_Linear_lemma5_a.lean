-- Prove2me | solution 1 for TsengCGD.Linear.lemma5_a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:58:53.530984+00:00
-- url     : https://prove2.me/submissions/b696fa92-006d-412c-9f24-b1f4ad141879

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

end TsengCGD.Linear

open TsengCGD.Linear


theorem solution {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (hJ : J.Nonempty) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (DJ : Set (TsengCGD.Global.Vec n)) (PJ : TsengCGD.Global.Vec n → ℝ) (DJC : Set (TsengCGD.Global.Vec n)) (PJC : TsengCGD.Global.Vec n → ℝ)
    (hw : TsengCGD.Global.IsBlockSepWitness D P J DJ PJ DJC PJC)
    (xbar : TsengCGD.Global.Vec n) (hxbar : xbar ∈ DJ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ J, (gradient f x j + (H *ᵥ WithLp.ofLp d) j) * ((x + α • d) j - xbar j))
        + c * PJ (x + α • d) - c * PJ xbar
      ≤ (α - 1) * ((1 - γ) * TsengCGD.Global.qf H d + TsengCGD.Global.Delta f P c γ H x d) := by
  exact lemma5_a_core f D P c hs x hx H hH J d hd γ DJ PJ DJC PJC hw xbar hxbar α hα0 hα1
