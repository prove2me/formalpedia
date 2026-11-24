-- Prove2me | solution 1 for Weil2.exists_zeta_ordinate_ne_zero_of_expType
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:17:31.596261+00:00
-- url     : https://prove2.me/submissions/1c88281a-b9d2-45bb-916b-7963b75e3615

import Mathlib
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_XiHadamardPortPublished_concrete_xi_no_real_zeros
import Theorems.Thm_Titchmarsh_inv_riemannZeta_le_rpow_of_riemannHypothesis
import Theorems.Thm_BranchActualCount_concrete_zero_count_bounds

open Filter Topology Complex

noncomputable section

namespace Weil2Mult

def xiM (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

def FP (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

lemma FP_eq (z : ℂ) : FP z = xiM (z + 1/2) := by unfold FP xiM; ring

lemma xiM_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiM s = s * (s-1) * completedRiemannZeta s / 2 := by
  have h1' : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [completedRiemannZeta_eq]; unfold xiM
  field_simp
  ring

lemma zeta_eq_xiM_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannZeta s = xiM s * (2 / (s * (s-1)) * (Gammaℝ s)⁻¹) := by
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [riemannZeta_def_of_ne_zero h0, xiM_eq h0 h1, div_eq_mul_inv]
  field_simp

lemma xiM_eq_zeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hre : 0 < s.re) :
    xiM s = s * (s-1) * Gammaℝ s * riemannZeta s / 2 := by
  rw [xiM_eq h0 h1, riemannZeta_def_of_ne_zero h0]
  have := Gammaℝ_ne_zero_of_re_pos hre
  field_simp

lemma FP_differentiable : Differentiable ℂ FP := by
  unfold FP
  have := differentiable_completedZeta₀
  fun_prop

lemma xiM_differentiable : Differentiable ℂ xiM := by
  unfold xiM
  have := differentiable_completedZeta₀
  fun_prop

lemma FP_zero_ne : FP 0 ≠ 0 := by
  have := XiHadamardPortPublished.concrete_xi_no_real_zeros (1/2 : ℝ)
  rw [FP_eq, xiM]
  simpa using this

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

lemma xiM_zero_re (hRH : RiemannHypothesis) {s : ℂ} (hx' : xiM s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiM at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (completed_ne_zero_of_one_le_re h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (completed_ne_zero_of_one_le_re this ?_)
    · rw [completedRiemannZeta_one_sub]; exact hΛ
    · intro h2; apply hs0; linear_combination -h2
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  apply hRH s hζ
  · rintro ⟨n, hn⟩
    rw [hn] at h'
    simp at h'
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hs1

lemma zero_re_of_order (hRH : RiemannHypothesis) {a : ℂ} (h : analyticOrderNatAt FP a ≠ 0) :
    a.re = 0 := by
  have h1 : analyticOrderAt FP a ≠ 0 := by
    intro h0; apply h; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FP_eq] at h2
  have := xiM_zero_re hRH h2
  simpa using this

lemma factor_lt {a wa wb : ℂ} (hre : a.re = 0) (hpos : 0 < a.im)
    (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖1 + wa ^ 2 / (-a ^ 2)‖ < ‖1 + wb ^ 2 / (-a ^ 2)‖ := by
  have ha : -a ^ 2 = ((a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, hre]
  have hc : (0:ℝ) < a.im ^ 2 := by positivity
  have hc' : ((a.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrw : ∀ w : ℂ, 1 + w ^ 2 / (-a ^ 2) =
      (((a.im ^ 2 : ℝ) : ℂ) + w ^ 2) / ((a.im ^ 2 : ℝ) : ℂ) := by
    intro w; rw [ha]; field_simp
  rw [hrw, hrw, norm_div, norm_div]
  apply div_lt_div_of_pos_right _ (by simpa using hc)
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im, zero_add]
  rw [him] at *
  have hX' : wa.re * wa.re < wb.re * wb.re := by nlinarith
  have hpos2 : 0 < 2 * (a.im * a.im) + 2 * (wb.im * wb.im) + wa.re * wa.re + wb.re * wb.re := by
    nlinarith [mul_self_nonneg wb.im, mul_self_nonneg wa.re, mul_self_nonneg wb.re]
  nlinarith [mul_pos (sub_pos.mpr hX') hpos2]

/-- The factor attached to the zero `iγ` itself. -/
lemma factor0 {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    ‖1 + ((δ:ℂ) + γ * I) ^ 2 / (-((γ:ℂ) * I) ^ 2)‖ ≤
      (δ / (2 + δ)) * ‖1 + (((2 + δ : ℝ) : ℂ) + γ * I) ^ 2 / (-((γ:ℂ) * I) ^ 2)‖ := by
  have hγc : (γ:ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have key : ∀ x : ℝ, 1 + ((x:ℂ) + γ * I) ^ 2 / (-((γ:ℂ) * I) ^ 2) =
      (x:ℂ) * ((x:ℂ) + (2 * γ : ℝ) * I) / ((γ ^ 2 : ℝ) : ℂ) := by
    intro x
    have : -((γ:ℂ) * I) ^ 2 = ((γ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this]
    have hγ2 : ((γ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (γ^2:ℝ) ≠ 0)
    field_simp
    push_cast
    ring_nf
    rw [I_sq]; ring
  rw [key, key, norm_div, norm_div, norm_mul, norm_mul, norm_add_mul_I, norm_add_mul_I]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hδ, abs_of_pos (by linarith : (0:ℝ) < 2 + δ)]
  have hg : (0:ℝ) < |γ ^ 2| := by positivity
  have hs : √(δ ^ 2 + (2 * γ) ^ 2) ≤ √((2 + δ) ^ 2 + (2 * γ) ^ 2) := by
    apply Real.sqrt_le_sqrt; nlinarith
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hg]
  have h2 : δ / (2 + δ) * ((2 + δ) * √((2 + δ) ^ 2 + (2 * γ) ^ 2)) =
      δ * √((2 + δ) ^ 2 + (2 * γ) ^ 2) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left hs hδ.le

/-- Product inequality: removing the `m` factors attached to the zero `iγ`. -/
lemma prod_ineq (hRH : RiemannHypothesis) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    ‖FP ((δ:ℂ) + γ * I)‖ ≤
      (δ / (2 + δ)) ^ (analyticOrderNatAt FP ((γ:ℂ) * I)) * ‖FP (((2 + δ : ℝ) : ℂ) + γ * I)‖ := by
  classical
  let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FP z.val)
  have key : ∀ w : ℂ, Multipliable (fun p : U => 1+w^2/(-p.1.val^2)) ∧
      FP w / FP 0 = ∏' p : U, (1+w^2/(-p.1.val^2)) :=
    XiPairingPublished.concrete_upper_paired_product
  have h0 := FP_zero_ne
  have hP : ∀ w, FP w = FP 0 * ∏' p : U, (1+w^2/(-p.1.val^2)) := by
    intro w; rw [← (key w).2]; field_simp
  set a0 : ℂ := (γ:ℂ) * I with ha0def
  have ha0 : 0 < a0.im := by simp [a0, hγ]
  set wa : ℂ := (δ:ℂ) + γ * I with hwa
  set wb : ℂ := ((2 + δ : ℝ) : ℂ) + γ * I with hwb
  set q : ℝ := δ / (2 + δ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by linarith)]; linarith
  set m := analyticOrderNatAt FP a0 with hm
  set g : U → ℂ → ℂ := fun p w => 1+w^2/(-p.1.val^2) with hg
  let c : U → ℝ := fun p => if p.1.val = a0 then q else 1
  have hpt : ∀ p : U, ‖g p wa‖ ≤ c p * ‖g p wb‖ := by
    intro p
    by_cases hp : p.1.val = a0
    · simp only [c, hp, if_true, g]
      exact factor0 hγ hδ
    · simp only [c, hp, if_false, one_mul]
      have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
        intro h; have := p.2.isLt; omega
      refine (factor_lt (zero_re_of_order hRH hord) p.1.2 ?_ ?_).le
      · simp [wa, wb]
      · simp [wa, wb]; nlinarith
  -- the finset of the `m` copies of `a0`
  let emb : Fin m ↪ U := ⟨fun k => (⟨⟨a0, ha0⟩, k⟩ : U), by
    intro k1 k2 h
    exact eq_of_heq (Sigma.mk.inj h).2⟩
  let K : Finset U := Finset.univ.map emb
  have hK : K.card = m := by simp [K]
  have hKmem : ∀ p ∈ K, p.1.val = a0 := by
    intro p hp
    simp only [K, Finset.mem_map, Finset.mem_univ, true_and] at hp
    obtain ⟨k, rfl⟩ := hp
    rfl
  have hc : ∀ S : Finset U, K ⊆ S → ∏ p ∈ S, c p ≤ q ^ m := by
    intro S hS
    have : ∏ p ∈ S, c p = q ^ (S.filter (fun p : U => p.1.val = a0)).card := by
      simp only [c]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rw [this]
    apply pow_le_pow_of_le_one hq0 hq1
    rw [← hK]
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter]
    exact ⟨hS hp, hKmem p hp⟩
  set Pa := ‖∏' p : U, g p wa‖
  set Pb := ‖∏' p : U, g p wb‖
  have hTa := (key wa).1.hasProd.norm
  have hTb := (key wb).1.hasProd.norm
  have hlim : Pa ≤ q ^ m * Pb := by
    apply le_of_tendsto_of_tendsto hTa (hTb.const_mul _)
    filter_upwards [Filter.eventually_ge_atTop K] with S hS
    calc ∏ p ∈ S, ‖g p wa‖ ≤ ∏ p ∈ S, (c p * ‖g p wb‖) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hpt i)
      _ = (∏ p ∈ S, c p) * ∏ p ∈ S, ‖g p wb‖ := Finset.prod_mul_distrib
      _ ≤ q ^ m * ∏ p ∈ S, ‖g p wb‖ :=
          mul_le_mul_of_nonneg_right (hc S hS) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  have hna : ‖FP wa‖ = ‖FP 0‖ * Pa := by rw [hP wa, norm_mul]
  have hnb : ‖FP wb‖ = ‖FP 0‖ * Pb := by rw [hP wb, norm_mul]
  rw [hna, hnb]
  calc ‖FP 0‖ * Pa ≤ ‖FP 0‖ * (q ^ m * Pb) := mul_le_mul_of_nonneg_left hlim (norm_nonneg _)
    _ = q ^ m * (‖FP 0‖ * Pb) := by ring

end Weil2Mult

namespace Weil2Mult

lemma zeta_norm_le_two {s : ℂ} (hs : 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 2 := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith)]
  have h2 : HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hb : ∀ n : ℕ, ‖1 / ((n:ℂ) + 1) ^ s‖ ≤ 1 / ((n:ℝ) + 1) ^ 2 := by
    intro n
    have hn : ((n:ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hn, norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    have h1 : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have : ((n + 1 : ℕ) : ℝ) ^ (2:ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le h1 hs
    rw [Real.rpow_two] at this
    push_cast at this ⊢
    apply one_div_le_one_div_of_le (by positivity) this
  have := tsum_of_norm_bounded h2 hb
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  linarith

lemma zeta_order_eq {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hre : 0 < ρ.re) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt FP (ρ - 1/2) ∧
      analyticOrderAt FP (ρ - 1/2) ≠ ⊤ ∧ AnalyticAt ℂ riemannZeta ρ := by
  have hFP : analyticOrderAt FP (ρ - 1/2) = analyticOrderAt xiM ρ := by
    have : FP = xiM ∘ (fun z => z + 1/2) := funext FP_eq
    rw [this, analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop)]
    · simp
    · simp
  have hnhds : {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∈ 𝓝 ρ :=
    IsOpen.mem_nhds (isOpen_ne.inter isOpen_ne) ⟨h0, h1⟩
  set k : ℂ → ℂ := fun s => 2 / (s * (s-1)) * (Gammaℝ s)⁻¹ with hkdef
  have hk : AnalyticAt ℂ k ρ := by
    apply DifferentiableOn.analyticAt _ hnhds
    intro s hs
    have hs' : s * (s - 1) ≠ 0 := mul_ne_zero hs.1 (sub_ne_zero.mpr hs.2)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact DifferentiableAt.div (c := fun _ => (2:ℂ)) (d := fun s : ℂ => s * (s - 1))
        (differentiableAt_const _) (by fun_prop) hs'
    · exact differentiable_Gammaℝ_inv.differentiableAt
  have hkne : k ρ ≠ 0 := by
    have hs' : ρ * (ρ - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
    simp only [k]
    exact mul_ne_zero (div_ne_zero two_ne_zero hs') (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre))
  have hz : AnalyticAt ℂ riemannZeta ρ := by
    apply DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 1}) _ (isOpen_ne.mem_nhds h1)
    intro s hs
    exact (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hx : AnalyticAt ℂ xiM ρ := xiM_differentiable.analyticAt ρ
  have heq : riemannZeta =ᶠ[𝓝 ρ] xiM * k := by
    filter_upwards [hnhds] with s hs
    exact zeta_eq_xiM_mul hs.1 hs.2
  have hord : analyticOrderAt riemannZeta ρ = analyticOrderAt xiM ρ := by
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul hx hk,
      hk.analyticOrderAt_eq_zero.mpr hkne, add_zero]
  have hfin : analyticOrderAt FP (ρ - 1/2) ≠ ⊤ := by
    have hA : AnalyticOnNhd ℂ FP Set.univ :=
      analyticOnNhd_univ_iff_differentiable.mpr FP_differentiable
    apply hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
      (Set.mem_univ _)
    rw [(FP_differentiable.analyticAt 0).analyticOrderAt_eq_zero.mpr FP_zero_ne]
    simp
  exact ⟨hord.trans hFP.symm, hfin, hz⟩

lemma zeta_natOrder_pos {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hre : 0 < ρ.re)
    (hz : riemannZeta ρ = 0) : 0 < analyticOrderNatAt riemannZeta ρ := by
  obtain ⟨he, hfin, ha⟩ := zeta_order_eq h0 h1 hre
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨ha, hz⟩
  simp only [analyticOrderNatAt]
  rw [he] at hne ⊢
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hne ⊢
  simp only [ENat.toNat_natCast]
  rcases Nat.eq_zero_or_pos n with h | h
  · exact absurd (by rw [h]; rfl) hne
  · exact h

lemma order_bridge {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hre : 0 < ρ.re) :
    (((meromorphicOrderAt riemannZeta ρ).untopD 0 : ℤ) : ℝ) ≤
      (analyticOrderNatAt FP (ρ - 1/2) : ℝ) := by
  have hFP : analyticOrderAt FP (ρ - 1/2) = analyticOrderAt xiM ρ := by
    have : FP = xiM ∘ (fun z => z + 1/2) := funext FP_eq
    rw [this, analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop)]
    · simp
    · simp
  have hnhds : {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∈ 𝓝 ρ :=
    IsOpen.mem_nhds (isOpen_ne.inter isOpen_ne) ⟨h0, h1⟩
  set k : ℂ → ℂ := fun s => 2 / (s * (s-1)) * (Gammaℝ s)⁻¹ with hkdef
  have hk : AnalyticAt ℂ k ρ := by
    apply DifferentiableOn.analyticAt _ hnhds
    intro s hs
    have hs' : s * (s - 1) ≠ 0 := mul_ne_zero hs.1 (sub_ne_zero.mpr hs.2)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact DifferentiableAt.div (c := fun _ => (2:ℂ)) (d := fun s : ℂ => s * (s - 1))
        (differentiableAt_const _) (by fun_prop) hs'
    · exact differentiable_Gammaℝ_inv.differentiableAt
  have hkne : k ρ ≠ 0 := by
    have hs' : ρ * (ρ - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
    simp only [k]
    exact mul_ne_zero (div_ne_zero two_ne_zero hs') (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre))
  have hz : AnalyticAt ℂ riemannZeta ρ := by
    apply DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 1}) _ (isOpen_ne.mem_nhds h1)
    intro s hs
    exact (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hx : AnalyticAt ℂ xiM ρ := xiM_differentiable.analyticAt ρ
  have heq : riemannZeta =ᶠ[𝓝 ρ] xiM * k := by
    filter_upwards [hnhds] with s hs
    exact zeta_eq_xiM_mul hs.1 hs.2
  have hord : analyticOrderAt riemannZeta ρ = analyticOrderAt xiM ρ := by
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul hx hk,
      hk.analyticOrderAt_eq_zero.mpr hkne, add_zero]
  have hfin : analyticOrderAt FP (ρ - 1/2) ≠ ⊤ := by
    have hA : AnalyticOnNhd ℂ FP Set.univ :=
      analyticOnNhd_univ_iff_differentiable.mpr FP_differentiable
    apply hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
      (Set.mem_univ _)
    rw [(FP_differentiable.analyticAt 0).analyticOrderAt_eq_zero.mpr FP_zero_ne]
    simp
  rw [hz.meromorphicOrderAt_eq, hord, ← hFP]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only [analyticOrderNatAt]
  rw [← hn]
  simp
  have : ((n : WithTop ℤ)) = (((n:ℤ)) : WithTop ℤ) := rfl
  rw [this, WithTop.untopD_coe]
  simp

/-- **Multiplicity bound under RH.** For every `η > 0`, zeros of `ζ` high enough have
multiplicity at most `η log γ`. -/
theorem mult_le (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0 < η → ∃ T0 : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → T0 ≤ ρ.im →
      (((meromorphicOrderAt riemannZeta ρ).untopD 0 : ℤ) : ℝ) ≤ η * Real.log ρ.im := by
  intro η hη
  set δ : ℝ := Real.exp (-(4/η)) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by have := div_pos (by norm_num : (0:ℝ) < 4) hη; linarith)
  set L : ℝ := Real.log ((2 + δ) / δ) with hLdef
  have hL : 4 / η ≤ L := by
    have h1 : Real.exp (4/η) ≤ (2 + δ) / δ := by
      rw [le_div_iff₀ hδ, hδdef, ← Real.exp_add]
      simp
      linarith
    calc 4 / η = Real.log (Real.exp (4/η)) := (Real.log_exp _).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos _) h1
  have hLpos : 0 < L := lt_of_lt_of_le (div_pos (by norm_num) hη) hL
  obtain ⟨C, hC⟩ := Titchmarsh.inv_riemannZeta_le_rpow_of_riemannHypothesis hRH δ hδ 1 one_pos
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  set K : ℝ := Real.log (16 * C' / Real.pi) with hK
  refine ⟨max 2 (Real.exp (2 * |K| / (L * η))), ?_⟩
  intro ρ hρ hT
  set γ := ρ.im with hγdef
  have hγ2 : 2 ≤ γ := le_trans (le_max_left _ _) hT
  have hγpos : 0 < γ := by linarith
  have hlogγ : 2 * |K| / (L * η) ≤ Real.log γ := by
    have := le_trans (le_max_right _ _) hT
    calc 2 * |K| / (L * η) = Real.log (Real.exp (2 * |K| / (L * η))) := (Real.log_exp _).symm
      _ ≤ Real.log γ := Real.log_le_log (Real.exp_pos _) this
  -- RH puts ρ on the line
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hγdef; simp at hγdef; linarith
  have hρre : ρ.re = 1/2 := by
    apply hRH ρ hρ _ hρ1
    rintro ⟨n, hn⟩
    have : ρ.im = 0 := by rw [hn]; simp
    linarith
  have hρeq : ρ - 1/2 = (γ:ℂ) * I := by
    apply Complex.ext <;> simp [hρre, hγdef]
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hρre; simp at hρre
  have hbr := order_bridge hρ0 hρ1 (by rw [hρre]; norm_num)
  rw [hρeq] at hbr
  set m := analyticOrderNatAt FP ((γ:ℂ) * I) with hm
  -- the product inequality
  have hpr := prod_ineq hRH hγpos hδ
  rw [← hm] at hpr
  set s : ℂ := ((1/2 + δ : ℝ) : ℂ) + γ * I with hsdef
  have hsa : (δ:ℂ) + γ * I + 1/2 = s := by rw [hsdef]; push_cast; ring
  have hsb : ((2 + δ : ℝ) : ℂ) + γ * I + 1/2 = s + 2 := by rw [hsdef]; push_cast; ring
  rw [FP_eq, FP_eq, hsa, hsb] at hpr
  have hsre : s.re = 1/2 + δ := by simp [hsdef]
  have hsim : s.im = γ := by simp [hsdef]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsim; simp at hsim; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsim; simp at hsim; linarith
  have hs2 : s + 2 ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; linarith
  have hs3 : s + 2 ≠ 1 := by intro h; have := congrArg Complex.im h; simp at this; linarith
  have hsre0 : 0 < s.re := by rw [hsre]; linarith
  have hs2re : 0 < (s+2).re := by simp; linarith
  rw [xiM_eq_zeta hs0 hs1 hsre0, xiM_eq_zeta hs2 hs3 hs2re, Gammaℝ_add_two hs0] at hpr
  -- zeta(s) ≠ 0 and lower bound
  have hζs : riemannZeta s ≠ 0 := by
    intro h
    have := hRH s h (by rintro ⟨n, hn⟩; have := congrArg Complex.im hn; simp at this; linarith) hs1
    rw [hsre] at this; linarith
  have hCs := hC s (by rw [hsre]) (by rw [hsre]; linarith) (by rw [hsim, abs_of_pos hγpos]; linarith)
  rw [hsim, abs_of_pos hγpos, Real.rpow_one, norm_inv] at hCs
  have hlow : 1 ≤ C' * γ * ‖riemannZeta s‖ := by
    have hn : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζs
    have : ‖riemannZeta s‖⁻¹ ≤ C' * γ :=
      le_trans hCs (mul_le_mul_of_nonneg_right (le_max_left _ _) hγpos.le)
    rw [inv_le_iff_one_le_mul₀ hn] at this
    linarith [mul_comm (C' * γ) ‖riemannZeta s‖]
  have hz2 := zeta_norm_le_two (s := s + 2) (by simp; linarith)
  have hG : 0 < ‖Gammaℝ s‖ := norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos hsre0)
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hq0 : 0 ≤ (δ / (2 + δ)) ^ m := by positivity
  -- norm bounds
  have hn1 : γ ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    simp [hsim] at this; rw [abs_of_pos hγpos] at this; exact this
  have hn2 : ‖s + 2‖ ≤ 4 * γ := by
    have := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hr : |(s + 2).re| = 5/2 + δ := by simp [hsre]; rw [abs_of_pos (by linarith)]; ring
    have hi : |(s + 2).im| = γ := by simp [hsim, abs_of_pos hγpos]
    linarith
  have hn3 : ‖s + 1‖ ≤ 4 * γ := by
    have := Complex.norm_le_abs_re_add_abs_im (s + 1)
    have hr : |(s + 1).re| = 3/2 + δ := by simp [hsre]; rw [abs_of_pos (by linarith)]; ring
    have hi : |(s + 1).im| = γ := by simp [hsim, abs_of_pos hγpos]
    linarith
  -- main inequality: ‖s-1‖ ‖ζ s‖ ≤ q^m ‖s+2‖ ‖s+1‖ ‖ζ(s+2)‖ / (2π)
  have hmain : ‖s - 1‖ * ‖riemannZeta s‖ ≤
      (δ / (2 + δ)) ^ m * (‖s + 2‖ * ‖s + 1‖ * ‖riemannZeta (s + 2)‖ / (2 * Real.pi)) := by
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    simp only [norm_div, norm_mul] at hpr
    have e1 : (s + 2 - 1) = s + 1 := by ring
    rw [e1] at hpr
    have hn2' : ‖(2:ℂ)‖ = 2 := by simp
    have hnpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos hpi]
    rw [hn2', hnpi] at hpr
    have hpos : 0 < ‖s‖ * ‖Gammaℝ s‖ / 2 := by positivity
    have := hpr
    have lhs : ‖s‖ * ‖s - 1‖ * ‖Gammaℝ s‖ * ‖riemannZeta s‖ / 2 =
        (‖s‖ * ‖Gammaℝ s‖ / 2) * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
    have rhs : (δ / (2 + δ)) ^ m * (‖s + 2‖ * ‖s + 1‖ * (‖Gammaℝ s‖ * ‖s‖ / 2 / Real.pi) *
        ‖riemannZeta (s + 2)‖ / 2) = (‖s‖ * ‖Gammaℝ s‖ / 2) *
        ((δ / (2 + δ)) ^ m * (‖s + 2‖ * ‖s + 1‖ * ‖riemannZeta (s + 2)‖ / (2 * Real.pi))) := by
      field_simp
    rw [lhs, rhs] at this
    exact le_of_mul_le_mul_left this hpos
  -- combine
  have hfinal : 1 ≤ (δ / (2 + δ)) ^ m * (16 * C' / Real.pi) * γ ^ 2 := by
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hA : ‖s + 2‖ * ‖s + 1‖ * ‖riemannZeta (s + 2)‖ / (2 * Real.pi) ≤
        (4 * γ) * (4 * γ) * 2 / (2 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul (mul_le_mul hn2 hn3 (norm_nonneg _) (by positivity)) hz2 (norm_nonneg _)
        (by positivity)
    have hB : γ * ‖riemannZeta s‖ ≤ (δ / (2 + δ)) ^ m * ((4 * γ) * (4 * γ) * 2 / (2 * Real.pi)) :=
      le_trans (mul_le_mul_of_nonneg_right hn1 (norm_nonneg _))
        (le_trans hmain (mul_le_mul_of_nonneg_left hA hq0))
    have hC'pos : 0 < C' := by linarith
    have : γ ≤ C' * γ * (γ * ‖riemannZeta s‖) := by nlinarith
    have h3 : γ ≤ C' * γ * ((δ / (2 + δ)) ^ m * ((4 * γ) * (4 * γ) * 2 / (2 * Real.pi))) :=
      le_trans this (mul_le_mul_of_nonneg_left hB (by positivity))
    have e : C' * γ * ((δ / (2 + δ)) ^ m * ((4 * γ) * (4 * γ) * 2 / (2 * Real.pi))) =
        γ * ((δ / (2 + δ)) ^ m * (16 * C' / Real.pi) * γ ^ 2) := by
      field_simp; ring
    rw [e] at h3
    have h4 : γ * 1 ≤ γ * ((δ / (2 + δ)) ^ m * (16 * C' / Real.pi) * γ ^ 2) := by linarith
    exact le_of_mul_le_mul_left h4 hγpos
  -- logs
  have hqpos : 0 < δ / (2 + δ) := by positivity
  have hApos : 0 < 16 * C' / Real.pi := by have := Real.pi_pos; positivity
  have hlog := Real.log_le_log one_pos hfinal
  rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hlq : Real.log (δ / (2 + δ)) = -L := by
    rw [hLdef, ← Real.log_inv, inv_div]
  rw [hlq] at hlog
  -- hlog : 0 ≤ m * (-L) + K + 2 * log γ
  have hmL : (m:ℝ) * L ≤ K + 2 * Real.log γ := by rw [← hK] at hlog; push_cast at hlog; linarith
  have hlogpos : 0 ≤ Real.log γ := Real.log_nonneg (by linarith)
  have hmle : (m:ℝ) ≤ η * Real.log γ := by
    have h1 : (m:ℝ) * L ≤ |K| + 2 * Real.log γ := by linarith [le_abs_self K]
    have h2 : |K| ≤ L * η / 2 * Real.log γ := by
      have := hlogγ
      rw [div_le_iff₀ (by positivity)] at this
      have e : L * η / 2 * Real.log γ = (Real.log γ * (L * η)) / 2 := by ring
      rw [e]; linarith
    have h3 : 2 * Real.log γ ≤ L * η / 2 * Real.log γ := by
      have h4 : 4 ≤ L * η := by rw [div_le_iff₀ hη] at hL; linarith
      have h5 := mul_le_mul_of_nonneg_right h4 hlogpos
      have e : L * η / 2 * Real.log γ = (L * η * Real.log γ) / 2 := by ring
      rw [e]; linarith
    have e : L * (η * Real.log γ) = L * η / 2 * Real.log γ + L * η / 2 * Real.log γ := by ring
    have h4 : L * (m:ℝ) ≤ L * (η * Real.log γ) := by rw [e, mul_comm]; linarith
    exact le_of_mul_le_mul_left h4 hLpos
  exact le_trans hbr hmle

end Weil2Mult

namespace Weil2Mult

lemma untopD_nonneg {x : WithTop ℤ} (hx : 0 ≤ x) : 0 ≤ x.untopD 0 := by
  cases x with
  | top => simp
  | coe n =>
    simp only [WithTop.untopD_coe]
    exact_mod_cast hx

/-- **Superlinearly many distinct zeros under RH.** -/
theorem many_distinct (hRH : RiemannHypothesis) (B : ℝ) (hB : 0 < B) (T1 : ℝ) :
    ∃ T ≥ T1, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T) ∧
      B * T ≤ Z.card := by
  classical
  obtain ⟨-, hev⟩ := BranchActualCount.concrete_zero_count_bounds
  set η : ℝ := 1 / (64 * Real.pi * (B + 1)) with hη
  have hηpos : 0 < η := by have := Real.pi_pos; positivity
  obtain ⟨T0', hT0'⟩ := mult_le hRH η hηpos
  set T0 : ℝ := max T0' 2 with hT0
  let f : ℂ → ℝ := fun ρ => (((meromorphicOrderAt riemannZeta ρ).untopD 0 : ℤ) : ℝ)
  let f' : ℂ → ℝ := fun ρ => max 0 (f ρ)
  let S : ℝ → Set ℂ := fun T =>
    {s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z = 0}}
  have hff' : ∀ T, ∀ ρ ∈ S T, f ρ = f' ρ := by
    intro T ρ hρ
    have h1 : ρ ≠ 1 := by
      intro h; have := hρ.2.1.1; rw [h] at this; simp at this
    have hz : AnalyticAt ℂ riemannZeta ρ := by
      apply DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 1}) _ (isOpen_ne.mem_nhds h1)
      intro s hs
      exact (differentiableAt_riemannZeta hs).differentiableWithinAt
    have : 0 ≤ f ρ := by
      have := untopD_nonneg hz.meromorphicOrderAt_nonneg
      simp only [f]; exact_mod_cast this
    simp [f', this]
  have hf'0 : ∀ ρ, 0 ≤ f' ρ := fun ρ => le_max_left _ _
  have hNeq : ∀ T, (∑' ρ : S T, f ρ) = ∑' ρ, (S T).indicator f' ρ := by
    intro T
    rw [← tsum_subtype]
    exact tsum_congr (fun ρ => hff' T ρ.1 ρ.2)
  set N0 : ℝ := ∑' ρ : S T0, f ρ with hN0
  have hlarge : ∀ᶠ T : ℝ in atTop, 64 * Real.pi * (|N0| + 1) ≤ T * Real.log T :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).eventually_ge_atTop _
  obtain ⟨T, hNT, hTl, hTge⟩ :=
    (hev.and (hlarge.and (eventually_ge_atTop (max T1 T0)))).exists
  have hNT' : T * Real.log T / (32 * Real.pi) ≤ ∑' ρ : S T, f ρ := hNT
  have hTT1 : T1 ≤ T := le_trans (le_max_left _ _) hTge
  have hTT0 : T0 ≤ T := le_trans (le_max_right _ _) hTge
  have hT2 : 2 ≤ T := le_trans (le_max_right _ _) hTT0
  refine ⟨T, hTT1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hTlogpos : 0 < T * Real.log T := by positivity
  -- summability
  have hsum : Summable (fun ρ => (S T).indicator f' ρ) := by
    by_contra hns
    have := tsum_eq_zero_of_not_summable hns
    rw [← hNeq] at this
    rw [this] at hNT'
    have : 0 < T * Real.log T / (32 * Real.pi) := by have := Real.pi_pos; positivity
    linarith
  -- split
  set S' : Set ℂ := {s ∈ S T | T0 ≤ s.im} with hS'
  have hsplit : S T = S T0 ∪ S' := by
    ext s
    simp only [S, S', Set.mem_union, Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : s.im < T0
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact Or.inr ⟨⟨⟨h1, h2⟩, h3⟩, le_of_not_gt h⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, _⟩)
      · exact ⟨⟨h1, by linarith⟩, h3⟩
      · exact ⟨⟨h1, h2⟩, h3⟩
  have hdisj : Disjoint (S T0) S' := by
    rw [Set.disjoint_left]
    intro s h1 h2
    have := h1.2.1.2
    have := h2.2
    linarith
  have hle1 : ∀ ρ, (S T0).indicator f' ρ ≤ (S T).indicator f' ρ := by
    intro ρ; rw [hsplit, Set.indicator_union_of_disjoint hdisj]
    have := Set.indicator_nonneg (fun x _ => hf'0 x) (s := S') ρ
    linarith
  have hle2 : ∀ ρ, S'.indicator f' ρ ≤ (S T).indicator f' ρ := by
    intro ρ; rw [hsplit, Set.indicator_union_of_disjoint hdisj]
    have := Set.indicator_nonneg (fun x _ => hf'0 x) (s := S T0) ρ
    linarith
  have hs1 : Summable (fun ρ => (S T0).indicator f' ρ) :=
    Summable.of_nonneg_of_le (fun ρ => Set.indicator_nonneg (fun x _ => hf'0 x) ρ) hle1 hsum
  have hs2 : Summable (fun ρ => S'.indicator f' ρ) :=
    Summable.of_nonneg_of_le (fun ρ => Set.indicator_nonneg (fun x _ => hf'0 x) ρ) hle2 hsum
  have hdecomp : (∑' ρ : S T, f ρ) = N0 + ∑' ρ, S'.indicator f' ρ := by
    rw [hNeq, hN0, hNeq, hsplit, Set.indicator_union_of_disjoint hdisj]
    exact hs1.tsum_add hs2
  -- S' is finite
  have hfin : S'.Finite := by
    by_contra hinf
    obtain ⟨Z, hZ, hZc⟩ := Set.Infinite.exists_subset_card_eq hinf ⌈B * T⌉₊
    have := hcon Z (by
      intro ρ hρ
      have h := hZ hρ
      exact ⟨h.1.2.2, h.1.2.1.1, h.1.2.1.2⟩)
    rw [hZc] at this
    have := Nat.le_ceil (B * T)
    linarith
  have hcard : (hfin.toFinset.card : ℝ) < B * T := by
    apply hcon
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1.2.2, hρ.1.2.1.1, hρ.1.2.1.2⟩
  have hS'sum : ∑' ρ, S'.indicator f' ρ = ∑ ρ ∈ hfin.toFinset, f' ρ := by
    rw [tsum_eq_sum (s := hfin.toFinset)]
    · apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      exact Set.indicator_of_mem hρ _
    · intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      exact Set.indicator_of_notMem hρ _
  have hbound : ∀ ρ ∈ hfin.toFinset, f' ρ ≤ η * Real.log T := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hT0ρ : T0' ≤ ρ.im := le_trans (le_max_left _ _) hρ.2
    have h1 := hT0' ρ hρ.1.2.2 hT0ρ
    have hρpos : 0 < ρ.im := hρ.1.2.1.1
    have h2 : Real.log ρ.im ≤ Real.log T := Real.log_le_log hρpos hρ.1.2.1.2.le
    have h3 : 0 ≤ η * Real.log T := by positivity
    simp only [f']
    apply max_le h3
    calc f ρ ≤ η * Real.log ρ.im := h1
      _ ≤ η * Real.log T := mul_le_mul_of_nonneg_left h2 hηpos.le
  have hsumle : ∑ ρ ∈ hfin.toFinset, f' ρ ≤ hfin.toFinset.card * (η * Real.log T) := by
    have := Finset.sum_le_sum hbound
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hηB : B * η ≤ 1 / (64 * Real.pi) := by
    rw [hη]
    have hpi := Real.pi_pos
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hc2 : (hfin.toFinset.card : ℝ) * (η * Real.log T) ≤ B * T * (η * Real.log T) :=
    mul_le_mul_of_nonneg_right hcard.le (by positivity)
  have hc3 : B * T * (η * Real.log T) ≤ T * Real.log T / (64 * Real.pi) := by
    have : B * T * (η * Real.log T) = (B * η) * (T * Real.log T) := by ring
    rw [this]
    have h := mul_le_mul_of_nonneg_right hηB hTlogpos.le
    calc B * η * (T * Real.log T) ≤ 1 / (64 * Real.pi) * (T * Real.log T) := h
      _ = T * Real.log T / (64 * Real.pi) := by ring
  have hfinal : T * Real.log T / (32 * Real.pi) ≤ N0 + T * Real.log T / (64 * Real.pi) := by
    rw [hdecomp, hS'sum] at hNT'
    linarith
  have hpi := Real.pi_pos
  have h64 : T * Real.log T / (64 * Real.pi) ≤ N0 := by
    have : T * Real.log T / (32 * Real.pi) = 2 * (T * Real.log T / (64 * Real.pi)) := by
      field_simp; ring
    linarith
  have : 64 * Real.pi * (|N0| + 1) ≤ 64 * Real.pi * N0 := by
    rw [div_le_iff₀ (by positivity)] at h64
    linarith
  have := le_abs_self N0
  nlinarith

end Weil2Mult

namespace Weil2Mult

open Metric in
/-- Jensen counting: distinct zeros of an entire function in a disc. -/
lemma jensen_card (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (hc : F c ≠ 0) (r : ℝ)
    (hr : 0 < r) (M : ℝ) (hM : 1 ≤ M) (hb : ∀ z ∈ sphere c (2 * r), ‖F z‖ ≤ M)
    (Z : Finset ℂ) (hZ : ∀ z ∈ Z, F z = 0 ∧ z ∈ closedBall c r) :
    (Z.card : ℝ) ≤ Real.log (M / ‖F c‖) / Real.log 2 := by
  classical
  have hA : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hF
  have h2r : 0 < 2 * r := by linarith
  have hJ := (hA.mono (Set.subset_univ (closedBall c |2 * r|))).sum_divisor_le (c := c) (r := r)
    (R := 2 * r) (M := M) (by rwa [abs_of_pos hr]) (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith)
    hM hc (by rwa [abs_of_pos h2r])
  rw [abs_of_pos hr, show 2 * r / r = 2 by field_simp] at hJ
  set D := MeromorphicOn.divisor F (closedBall c r) with hD
  have hAr : AnalyticOnNhd ℂ F (closedBall c r) := hA.mono (Set.subset_univ _)
  have hDnn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAr u
  have hfin : ∀ z, analyticOrderAt F z ≠ ⊤ := by
    intro z
    apply hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ c)
      (Set.mem_univ z)
    rw [(hA c trivial).analyticOrderAt_eq_zero.mpr hc]
    simp
  have hD1 : ∀ z ∈ Z, 1 ≤ D z := by
    intro z hz
    rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hAr (hZ z hz).2]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfin z)
    have hne : analyticOrderAt F z ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hA z trivial, (hZ z hz).1⟩
    rw [← hn] at hne ⊢
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (by rw [h]; rfl) hne
      · exact h
    simp
    exact_mod_cast hn1
  have hsupp : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hle : (Z.card : ℤ) ≤ ∑ᶠ u, D u := by
    rw [finsum_eq_sum_of_support_subset (s := Z ∪ hsupp.toFinset) _
      (by intro u hu; simp [hu])]
    calc (Z.card : ℤ) = ∑ u ∈ Z, (1 : ℤ) := by simp
      _ ≤ ∑ u ∈ Z, D u := Finset.sum_le_sum hD1
      _ ≤ ∑ u ∈ Z ∪ hsupp.toFinset, D u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun u _ _ => hDnn u)
  have hle' : (Z.card : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by exact_mod_cast hle
  exact le_trans hle' hJ

/-- **Key lemma.** Under RH, an entire function of exponential type which is not identically
zero on the real line cannot vanish at every ordinate of a zeta zero. -/
theorem exists_ordinate_ne_zero (hRH : RiemannHypothesis) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (C A : ℝ) (hb : ∀ z, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) (t0 : ℝ) (h0 : F t0 ≠ 0) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ 0 < analyticOrderNatAt riemannZeta ρ ∧
      F (ρ.im : ℂ) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set A' := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hF0 : 0 < ‖F t0‖ := norm_pos_iff.mpr h0
  have hCpos : 0 < C := by
    have := hb t0
    by_contra h
    push Not at h
    have : C * Real.exp (A * ‖(t0:ℂ)‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le
    linarith
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hb' : ∀ z, ‖F z‖ ≤ C' * Real.exp (A' * ‖z‖) := by
    intro z
    calc ‖F z‖ ≤ C * Real.exp (A * ‖z‖) := hb z
      _ ≤ C' * Real.exp (A' * ‖z‖) := by
        apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le (by linarith)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  set a := |t0| with ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K0 := (Real.log C' + 3 * A' * a - Real.log ‖F t0‖) / Real.log 2 with hK0
  set B := 2 * A' / Real.log 2 + 1 with hB
  have hBpos : 0 < B := by positivity
  obtain ⟨T, hT, Z, hZ, hcard⟩ := many_distinct hRH B hBpos (max 1 (K0 + 1))
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTK : K0 + 1 ≤ T := le_trans (le_max_right _ _) hT
  let im' : ℂ → ℂ := fun ρ => ((ρ.im : ℝ) : ℂ)
  have hre : ∀ ρ ∈ Z, ρ.re = 1/2 := by
    intro ρ hρ
    obtain ⟨hz, hpos, -⟩ := hZ ρ hρ
    apply hRH ρ hz
    · rintro ⟨n, hn⟩
      have : ρ.im = 0 := by rw [hn]; simp
      linarith
    · intro h; rw [h] at hpos; simp at hpos
  have hinj : Set.InjOn im' Z := by
    intro x hx y hy hxy
    have h1 : x.im = y.im := by simpa [im'] using hxy
    apply Complex.ext
    · rw [hre x hx, hre y hy]
    · exact h1
  set Y := Z.image im' with hY
  have hYc : Y.card = Z.card := Finset.card_image_of_injOn hinj
  set r := T + a with hr
  have hrpos : 0 < r := by have := abs_nonneg t0; linarith
  have hYZ : ∀ y ∈ Y, F y = 0 ∧ y ∈ Metric.closedBall (t0 : ℂ) r := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨ρ, hρ, rfl⟩ := hy
    obtain ⟨hz, hpos, hlt⟩ := hZ ρ hρ
    have hρre := hre ρ hρ
    have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
    have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hpos; simp at hpos
    refine ⟨hcon ρ hz hpos (zeta_natOrder_pos hρ0 hρ1 (by rw [hρre]; norm_num) hz), ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [im']
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := abs_sub (ρ.im) t0
    rw [abs_of_pos hpos] at this
    linarith
  set M := C' * Real.exp (A' * (a + 2 * r)) with hM
  have hM1 : 1 ≤ M := by
    have : 1 ≤ Real.exp (A' * (a + 2 * r)) := Real.one_le_exp (by positivity)
    nlinarith
  have hsph : ∀ z ∈ Metric.sphere (t0 : ℂ) (2 * r), ‖F z‖ ≤ M := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hzn : ‖z‖ ≤ a + 2 * r := by
      have := norm_le_norm_add_norm_sub' z (t0 : ℂ)
      have h2 : ‖(t0:ℂ)‖ = a := by simp [ha]
      linarith
    calc ‖F z‖ ≤ C' * Real.exp (A' * ‖z‖) := hb' z
      _ ≤ M := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzn hA'0)
  have hJ := jensen_card F hF (t0 : ℂ) h0 r hrpos M hM1 hsph Y hYZ
  rw [hYc] at hJ
  have hlogM : Real.log (M / ‖F t0‖) = Real.log C' + A' * (a + 2 * r) - Real.log ‖F t0‖ := by
    rw [Real.log_div (by positivity) hF0.ne', hM, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_exp]
  rw [hlogM] at hJ
  have e : (Real.log C' + A' * (a + 2 * r) - Real.log ‖F t0‖) / Real.log 2 =
      K0 + 2 * A' / Real.log 2 * T := by
    rw [hK0, hr]; field_simp; ring
  rw [e] at hJ
  have : B * T = 2 * A' / Real.log 2 * T + T := by rw [hB]; ring
  linarith

end Weil2Mult

end

theorem solution (hRH : RiemannHypothesis) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (C A : ℝ) (hb : ∀ z, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) (t0 : ℝ)
    (h0 : F t0 ≠ 0) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ 0 < analyticOrderNatAt riemannZeta ρ ∧
      F (ρ.im : ℂ) ≠ 0 :=
  Weil2Mult.exists_ordinate_ne_zero hRH F hF C A hb t0 h0
