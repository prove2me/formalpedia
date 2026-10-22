-- Prove2me | solution 1 for Subamenable.EpiDiff.eq_4_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:06:25.912003+00:00
-- url     : https://prove2.me/submissions/b4bbf421-742a-4efd-8d75-fe3799b10f9b

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology Subamenable.EpiDiff
open scoped InnerProductSpace

lemma SA410_taylor {n m : ℕ} (f : E n → E m) (x : E n) (hf : TwiceDiffAt f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : E n), ‖f (x + h) - f x - fderiv ℝ f x h -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) x h h‖ ≤ ε * ‖h‖ ^ 2 := by
  set Q := fderiv ℝ (fderiv ℝ f) x with hQ
  have hf2 : HasFDerivAt (fderiv ℝ f) Q x := hf.2.hasFDerivAt
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf2).def hε
  have hd : ∀ᶠ h in 𝓝 (0 : E n), DifferentiableAt ℝ f (x + h) := by
    have hc : Tendsto (fun h : E n => x + h) (𝓝 0) (𝓝 x) := by
      simpa using (tendsto_const_nhds (x := x)).add (tendsto_id (x := 𝓝 (0 : E n)))
    exact hc.eventually hf.1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlo.and hd)
  filter_upwards [Metric.ball_mem_nhds (0 : E n) hδ] with h hh
  have hsh : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • h ∈ Metric.ball (0 : E n) δ := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    rw [Metric.mem_ball, dist_zero_right] at hh
    calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact hs.2
      _ < δ := by simpa using hh
  set ψ : ℝ → E m := fun s => f (x + s • h) - s • fderiv ℝ f x h -
    (s ^ 2 / 2) • Q h h with hψ
  set ψ' : ℝ → E m := fun s => fderiv ℝ f (x + s • h) h - fderiv ℝ f x h -
    s • Q h h with hψ'
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt ψ (ψ' s) (Set.Icc 0 1) s := by
    intro s hs
    apply HasDerivAt.hasDerivWithinAt
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    have hdiff := (hball (s • h) (hsh s hs)).2
    have h2 : HasDerivAt (fun s : ℝ => f (x + s • h)) (fderiv ℝ f (x + s • h) h) s :=
      hdiff.hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => s • fderiv ℝ f x h) (fderiv ℝ f x h) s := by
      simpa using (hasDerivAt_id s).smul_const (fderiv ℝ f x h)
    have h4 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • Q h h) (s • Q h h) s := by
      have := ((hasDerivAt_pow 2 s).div_const 2).smul_const (Q h h)
      refine this.congr_deriv ?_
      congr 1; norm_num
    exact (h2.sub h3).sub h4
  have hbd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖ψ' s‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    have hb := (hball (s • h) (hsh s hs')).1
    have heq : ψ' s = (fderiv ℝ f (x + s • h) - fderiv ℝ f x - Q (s • h)) h := by
      simp [hψ', map_smul]
    rw [heq]
    calc ‖(fderiv ℝ f (x + s • h) - fderiv ℝ f x - Q (s • h)) h‖
        ≤ ‖fderiv ℝ f (x + s • h) - fderiv ℝ f x - Q (s • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖s • h‖) * ‖h‖ := by gcongr
      _ ≤ (ε * ‖h‖) * ‖h‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
          calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact hs.2.le
            _ = ‖h‖ := one_mul _
      _ = ε * ‖h‖ ^ 2 := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbd
  have e : ψ 1 - ψ 0 = f (x + h) - f x - fderiv ℝ f x h - (1 / 2 : ℝ) • Q h h := by
    simp only [hψ]; simp; norm_num; abel
  rw [e] at this
  exact this

lemma SA410_second_tendsto {n m : ℕ} (f : E n → E m) (x : E n) (hf : TwiceDiffAt f x)
    (w : E n) :
    Tendsto (fun p : ℝ × E n => (2 / p.1 ^ 2) •
        (f (x + p.1 • p.2) - f x - p.1 • fderiv ℝ f x p.2))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (fderiv ℝ (fderiv ℝ f) x w w)) := by
  set Q := fderiv ℝ (fderiv ℝ f) x with hQ
  set F : Filter (ℝ × E n) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w with hF
  set R : E n → E m := fun h => f (x + h) - f x - fderiv ℝ f x h - (1 / 2 : ℝ) • Q h h
    with hR
  have hpos : ∀ᶠ p : ℝ × E n in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hQc : Tendsto (fun p : ℝ × E n => Q p.2 p.2) F (𝓝 (Q w w)) := by
    have hc : Continuous (fun y : E n => Q y y) := by fun_prop
    exact (hc.tendsto w).comp tendsto_snd
  -- remainder term tends to zero
  have hrem : Tendsto (fun p : ℝ × E n => (2 / p.1 ^ 2) • R (p.1 • p.2)) F (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set M : ℝ := ‖w‖ + 1 with hM
    have hM1 : 1 ≤ M := by simp [hM]
    have hM0 : 0 < M := by linarith
    have hε' : 0 < ε / (4 * M ^ 2) := by positivity
    have hh : Tendsto (fun p : ℝ × E n => p.1 • p.2) F (𝓝 0) := by
      have h1 : Tendsto (fun p : ℝ × E n => p.1) F (𝓝 0) :=
        (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun p : ℝ × E n => p.2) F (𝓝 w) := tendsto_snd
      simpa using h1.smul h2
    have hT := hh.eventually (SA410_taylor f x hf _ hε')
    have hb : ∀ᶠ p : ℝ × E n in F, ‖p.2‖ ≤ M := by
      have h1 : ∀ᶠ y in 𝓝 w, ‖y‖ < ‖w‖ + 1 :=
        (continuous_norm.tendsto w).eventually (gt_mem_nhds (by linarith))
      filter_upwards [tendsto_snd.eventually h1] with p hp using hp.le
    filter_upwards [hT, hb, hpos] with p hp1 hp2 hp3
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / p.1 ^ 2)]
    have hn : ‖p.1 • p.2‖ ^ 2 = p.1 ^ 2 * ‖p.2‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp3]; ring
    rw [hn] at hp1
    have hp1' : ‖R (p.1 • p.2)‖ ≤ ε / (4 * M ^ 2) * (p.1 ^ 2 * ‖p.2‖ ^ 2) := hp1
    have hsq : ‖p.2‖ ^ 2 ≤ M ^ 2 := by
      have := norm_nonneg p.2
      nlinarith
    have ht2 : 0 < p.1 ^ 2 := by positivity
    calc 2 / p.1 ^ 2 * ‖R (p.1 • p.2)‖
        ≤ 2 / p.1 ^ 2 * (ε / (4 * M ^ 2) * (p.1 ^ 2 * ‖p.2‖ ^ 2)) := by gcongr
      _ = ε / 2 * (‖p.2‖ ^ 2 / M ^ 2) := by field_simp; ring
      _ ≤ ε / 2 * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact hsq
      _ < ε := by linarith
  have hsum := hQc.add hrem
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hpos] with p hp
  have hne : p.1 ≠ 0 := hp.ne'
  simp only [hR, map_smul, ContinuousLinearMap.smul_apply, smul_sub, smul_smul]
  have : (2 / p.1 ^ 2) * ((1 / 2 : ℝ) * (p.1 * p.1)) = 1 := by field_simp
  rw [this, one_smul]
  abel_nf

lemma SA410_ereal_split (A : EReal) (hA : A ≠ ⊥) (a b k : ℝ) (hk : 0 < k) :
    (A - (a : EReal)) * (k : EReal) =
      (A - (b : EReal)) * (k : EReal) + (((b - a) * k : ℝ) : EReal) := by
  induction A using EReal.rec with
  | bot => exact absurd rfl hA
  | top =>
    rw [EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_mul_coe_of_pos hk,
      EReal.top_add_coe]
  | coe A =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul,
      ← EReal.coe_add]
    congr 1; ring

lemma SA410_g_tendsto {n m : ℕ} (f : E n → E m) (xbar : E n)
    (hdf : DifferentiableAt ℝ f xbar) (w : E n) :
    Tendsto (fun p : ℝ × E n => (p.1, p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (fderiv ℝ f xbar w)) := by
  refine Filter.Tendsto.prodMk tendsto_fst ?_
  set F : Filter (ℝ × E n) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w with hF
  have hh : Tendsto (fun p : ℝ × E n => p.1 • p.2) F (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × E n => p.1) F (𝓝 0) :=
      (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds
    have h2 : Tendsto (fun p : ℝ × E n => p.2) F (𝓝 w) := tendsto_snd
    simpa using h1.smul h2
  have hr := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdf.hasFDerivAt).comp_tendsto hh
  have hbig : (fun p : ℝ × E n => p.1 • p.2) =O[F] (fun p : ℝ × E n => p.1) := by
    refine Asymptotics.IsBigO.of_bound (‖w‖ + 1) ?_
    have h1 : ∀ᶠ y in 𝓝 w, ‖y‖ < ‖w‖ + 1 :=
      (continuous_norm.tendsto w).eventually (gt_mem_nhds (by linarith))
    filter_upwards [tendsto_snd.eventually h1] with p hp
    rw [norm_smul]
    nlinarith [norm_nonneg p.1, norm_nonneg p.2]
  have hr' := hr.trans_isBigO hbig
  have ht := hr'.tendsto_inv_smul_nhds_zero
  have h3 : Tendsto (fun p : ℝ × E n => fderiv ℝ f xbar p.2) F (𝓝 (fderiv ℝ f xbar w)) :=
    ((fderiv ℝ f xbar).continuous.tendsto w).comp tendsto_snd
  have h4 := h3.add ht
  rw [add_zero] at h4
  refine h4.congr' ?_
  have hpos : ∀ᶠ p : ℝ × E n in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  filter_upwards [hpos] with p hp
  simp only [Function.comp]
  have hne : p.1 ≠ 0 := hp.ne'
  have key : p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar) =
      fderiv ℝ f xbar p.2 +
        p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar - fderiv ℝ f xbar (p.1 • p.2)) := by
    rw [map_smul, smul_sub, smul_sub, smul_sub, inv_smul_smul₀ hne]; abel
  exact key.symm

theorem solution {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar vbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar)
    (hv : vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff phi xbar) :
    ∀ w : E n, ∀ lam ∈ Subamenable.EpiDiff.Lam theta f xbar vbar,
      Subamenable.EpiDiff.multiplierValue theta f xbar w lam ≤
        secondSubderiv phi xbar vbar w := by
  intro w lam hlam
  obtain ⟨_, hbot, ⟨U, hU, hUeq⟩, htd, _, _⟩ := h
  have hphix : phi xbar = theta (f xbar) := hUeq xbar (mem_of_mem_nhds hU)
  set L := fderiv ℝ f xbar with hL
  set Q := fderiv ℝ (fderiv ℝ f) xbar with hQ
  set F : Filter (ℝ × E n) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w with hF
  have hdf : DifferentiableAt ℝ f xbar := htd.1.self_of_nhds
  set mm : ℝ × E n → ℝ × E m :=
    fun p => (p.1, p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar)) with hmm
  set r : ℝ × E n → ℝ := fun p => ⟪lam, (2 / p.1 ^ 2) •
      (f (xbar + p.1 • p.2) - f xbar - p.1 • L p.2)⟫_ℝ with hr
  set g : ℝ × E m → EReal := fun q => delta2 theta (f xbar) lam q.2 q.1 with hg
  have hm : Tendsto mm F (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (L w)) := SA410_g_tendsto f xbar hdf w
  have hrt : Tendsto r F (𝓝 ⟪lam, Q w w⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp
      (SA410_second_tendsto f xbar htd w)
  have hpos : ∀ᶠ p : ℝ × E n in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  have hU' : ∀ᶠ p : ℝ × E n in F, xbar + p.1 • p.2 ∈ U := by
    have h1 : Tendsto (fun p : ℝ × E n => p.1) F (𝓝 0) :=
      (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds
    have h2 : Tendsto (fun p : ℝ × E n => p.2) F (𝓝 w) := tendsto_snd
    have h3 : Tendsto (fun p : ℝ × E n => xbar + p.1 • p.2) F (𝓝 xbar) := by
      simpa using (tendsto_const_nhds (x := xbar)).add (h1.smul h2)
    exact h3.eventually hU
  have heq : ∀ᶠ p : ℝ × E n in F,
      delta2 phi xbar vbar p.2 p.1 = (g ∘ mm) p + ((r p : ℝ) : EReal) := by
    filter_upwards [hpos, hU'] with p hp hpU
    have hne : p.1 ≠ 0 := hp.ne'
    have hfx : f xbar + p.1 • (p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar)) =
        f (xbar + p.1 • p.2) := by
      rw [smul_inv_smul₀ hne]; abel
    simp only [Function.comp, hg, hmm, delta2, hfx, ← hUeq _ hpU, hphix]
    rw [SA410_ereal_split (phi (xbar + p.1 • p.2)) (hbot _) _
      ((theta (f xbar)).toReal + p.1 * ⟪lam, p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar)⟫_ℝ)
      _ (by positivity)]
    congr 2
    rw [hr]
    simp only
    have hadj : ⟪vbar, p.2⟫_ℝ = ⟪lam, L p.2⟫_ℝ := by
      rw [← hlam.1, ContinuousLinearMap.adjoint_inner_left]
    rw [hadj, inner_smul_right, inner_smul_right, inner_sub_right, inner_sub_right,
      inner_smul_right]
    field_simp
    rw [inner_sub_right]
    ring
  -- assemble
  have hcoe : Tendsto (fun p => ((r p : ℝ) : EReal)) F (𝓝 ((⟪lam, Q w w⟫_ℝ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hrt
  have hlr : liminf (fun p => ((r p : ℝ) : EReal)) F = ((⟪lam, Q w w⟫_ℝ : ℝ) : EReal) :=
    hcoe.liminf_eq
  have hlg : secondSubderiv theta (f xbar) lam (L w) ≤ liminf (g ∘ mm) F := by
    rw [Filter.liminf_comp]
    exact Filter.liminf_le_liminf_of_le hm
  unfold Subamenable.EpiDiff.multiplierValue
  calc secondSubderiv theta (f xbar) lam (L w) + ((⟪lam, Q w w⟫_ℝ : ℝ) : EReal)
      ≤ liminf (g ∘ mm) F + liminf (fun p => ((r p : ℝ) : EReal)) F := by
        rw [hlr]; gcongr
    _ ≤ liminf ((g ∘ mm) + (fun p => ((r p : ℝ) : EReal))) F := EReal.le_liminf_add
    _ = secondSubderiv phi xbar vbar w := by
        unfold secondSubderiv
        refine Filter.liminf_congr ?_
        filter_upwards [heq] with p hp
        rw [hp]; rfl
