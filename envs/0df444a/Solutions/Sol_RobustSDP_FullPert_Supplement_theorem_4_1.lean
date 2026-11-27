-- Prove2me | solution 1 for RobustSDP.FullPert.Supplement.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:37.2828+00:00
-- url     : https://prove2.me/submissions/1d642bbc-fb09-43e5-88ca-057dd746d581

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses
import Definitions.Def_RobustSDP_FullPert_Supplement_NonlinearProgram

open Matrix

open RobustSDP
open RobustSDP.FullPert
open RobustSDP.FullPert.Supplement

open RobustSDP.Uniqueness

/-- **Theorem 4.1, corrected** (El Ghaoui–Oustry–Lebret 1998, p. 39). Full perturbations, `D = 0`, `ρ = 1`
(§4, p. 38). Let `y_opt = (x_opt, τ_opt)` be optimal for the SDP (15), with `τ_opt > 0` (the
notation of §4.2). If H1 (Slater) and H2 (inf-compactness) hold, and some
`Y ∈ 𝒴(y_opt)` satisfying complementary slackness makes the Hessian `∇²_yy ℒ(y_opt, Y)` positive definite (17), then problem (16)
satisfies the quadratic growth condition at `y_opt`. Standing assumptions: `c ≠ 0` and
`F₀, …, F_m` symmetric (p. 33). -/
theorem solution {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c)
    (yopt : (Fin m → ℝ) × ℝ) (hopt : D.IsOptimal c yopt) (hτ : 0 < yopt.2)
    (h17 : ∃ Y ∈ dualSet D c yopt.2 yopt, ∀ h : (Fin m → ℝ) × ℝ, h ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (lagrangian D c yopt.2 Y) yopt ![h, h]) :
    QGC16 D c yopt.2 yopt := by
      obtain ⟨Y, ⟨_, hYpsd, hstat, hτstat, hcs⟩, hH⟩ := h17
      set τopt := yopt.2 with hτopt
      set U : Set ((Fin m → ℝ) × ℝ) := {y | 0 < y.2} with hUdef
      have hU : IsOpen U := isOpen_lt continuous_const continuous_snd
      set T : (Fin m → ℝ) × ℝ → ℝ := fun y => (Y * Gcal D τopt y).trace with hTdef
      set f := lagrangian D c τopt Y with hfdef
      -- smoothness
      have hT : ContDiffOn ℝ 2 T U := by
        have hent : ∀ a b, ContDiffOn ℝ 2 (fun y : (Fin m → ℝ) × ℝ => Gcal D τopt y a b) U := by
          intro a b
          rcases a with a | a <;> rcases b with b | b
          · simp only [Gcal, fromBlocks_apply₁₁, SDPData.G, SDPData.F, SDPData.R, Matrix.sub_apply,
              Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
              Matrix.transpose_apply, smul_eq_mul]
            intro y hy
            have hy' : y.2 ≠ 0 := ne_of_gt hy
            apply ContDiffAt.contDiffWithinAt
            fun_prop (disch := exact hy')
          · simp only [Gcal, fromBlocks_apply₁₂, Matrix.zero_apply]; fun_prop
          · simp only [Gcal, fromBlocks_apply₂₁, Matrix.zero_apply]; fun_prop
          · simp only [Gcal, fromBlocks_apply₂₂, Matrix.of_apply]; fun_prop
        simp only [hTdef, Matrix.trace, Matrix.diag, Matrix.mul_apply]
        fun_prop
      -- the linear part
      set ℓ : (Fin m → ℝ) × ℝ →L[ℝ] ℝ :=
        ∑ i, c i • (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ)
        with hℓdef
      have hℓ : ∀ y : (Fin m → ℝ) × ℝ, ℓ y = c ⬝ᵥ y.1 := by
        intro y
        simp [hℓdef, dotProduct]
      have hfeq : f = fun y => ℓ y - T y := by
        funext y
        simp [hfdef, lagrangian, hℓ, hTdef]
      have hf : ContDiffOn ℝ 2 f U := by
        rw [hfeq]
        exact ℓ.contDiff.contDiffOn.sub hT
      have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
      have hcont2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U :=
        hf1.continuousOn_fderiv_of_isOpen hU le_rfl
      have hdiff1 : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ f) z := fun z hz =>
        (hf1.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
      have hdiff0 : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
        (hf.differentiableOn (by norm_num) z hz).differentiableAt (hU.mem_nhds hz)
      have hdiffT : DifferentiableAt ℝ T yopt :=
        (hT.differentiableOn (by norm_num) yopt hτ).differentiableAt (hU.mem_nhds hτ)
      -- gradient vanishes
      have hgrad : ∀ h, fderiv ℝ f yopt h = 0 := by
        intro h
        have e1 : fderiv ℝ f yopt = ℓ - fderiv ℝ T yopt := by
          rw [hfeq]
          exact (ℓ.hasFDerivAt.sub hdiffT.hasFDerivAt).fderiv
        have hdec : h = ∑ i, h.1 i • ((Pi.single i 1 : Fin m → ℝ), (0:ℝ)) + h.2 • ((0 : Fin m → ℝ), (1:ℝ)) := by
          ext j
          · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
          · simp [Prod.snd_sum]
        have hL : fderiv ℝ T yopt h = ∑ i, h.1 i * c i := by
          conv_lhs => rw [hdec]
          rw [map_add, map_sum, map_smul, hτstat]
          simp only [map_smul, smul_eq_mul, hstat]
          simp
        rw [e1, _root_.sub_apply, hℓ, hL]
        simp [dotProduct, mul_comm]
      -- Hessian
      set B := fderiv ℝ (fderiv ℝ f) yopt with hBdef
      have hpos : ∀ h, h ≠ 0 → 0 < B h h := by
        intro h hh
        have := hH h hh
        rw [iteratedFDeriv_two_apply] at this
        simpa using this
      have hlam : ∃ lam : ℝ, 0 < lam ∧ ∀ h, lam * ‖h‖ ^ 2 ≤ B h h := by
        have hcpt : IsCompact (Metric.sphere (0 : (Fin m → ℝ) × ℝ) 1) := isCompact_sphere 0 1
        have hne : (Metric.sphere (0 : (Fin m → ℝ) × ℝ) 1).Nonempty :=
          ⟨((0 : Fin m → ℝ), (1 : ℝ)), by simp⟩
        have hcB : ContinuousOn (fun h => B h h) (Metric.sphere (0 : (Fin m → ℝ) × ℝ) 1) := by
          apply Continuous.continuousOn
          fun_prop
        obtain ⟨h0, hh0, hmin⟩ := hcpt.exists_isMinOn hne hcB
        refine ⟨B h0 h0, hpos h0 ?_, ?_⟩
        · intro h0z; rw [h0z] at hh0; simp at hh0
        · intro h
          by_cases hz : h = 0
          · subst hz; simp
          · have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
            set u := ‖h‖⁻¹ • h with hu
            have hus : u ∈ Metric.sphere (0 : (Fin m → ℝ) × ℝ) 1 := by
              simp [hu, norm_smul, hn.ne']
            have h1 := hmin hus
            simp only at h1
            have hhu : h = ‖h‖ • u := by
              rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
            have : B h h = ‖h‖ ^ 2 * B u u := by
              conv_lhs => rw [hhu]
              simp [map_smul, smul_eq_mul]; ring
            rw [this]
            have : B h0 h0 ≤ B u u := h1
            nlinarith [sq_nonneg ‖h‖]
      obtain ⟨lam, hlam0, hlamB⟩ := hlam
      -- continuity of Hessian at yopt
      have hcontAt : ContinuousAt (fderiv ℝ (fderiv ℝ f)) yopt :=
        (hcont2 yopt hτ).continuousAt (hU.mem_nhds hτ)
      have hcm : ∀ ε > 0, ∃ δ > 0, ∀ {x : (Fin m → ℝ) × ℝ}, dist x yopt < δ →
          dist (fderiv ℝ (fderiv ℝ f) x) B < ε :=
        Metric.continuousAt_iff.mp (by exact hcontAt)
      obtain ⟨δ, hδ0, hδ⟩ := hcm (lam / 2) (by linarith)
      -- trace nonneg
      have htr : ∀ G : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ, G.PosSemidef → 0 ≤ (Y * G).trace := by
        intro G hG
        obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hYpsd
        rw [hv, Finset.sum_mul, trace_sum]
        apply Finset.sum_nonneg
        intro i _
        rw [vecMulVec_mul, trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec]
        exact hG.dotProduct_mulVec_nonneg (v i)
      -- norm comparisons
      have hnorm_le : ∀ h : (Fin m → ℝ) × ℝ, ‖h‖ ^ 2 ≤ ∑ i, (h.1 i) ^ 2 + h.2 ^ 2 := by
        intro h
        have hS0 : 0 ≤ ∑ i, (h.1 i) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (h.1 j))
        have : ‖h‖ ≤ Real.sqrt (∑ i, (h.1 i) ^ 2 + h.2 ^ 2) := by
          rw [Prod.norm_def]
          apply max_le
          · rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
            intro i
            rw [Real.norm_eq_abs]
            apply Real.abs_le_sqrt
            have := Finset.single_le_sum (f := fun j => (h.1 j) ^ 2) (fun j _ => sq_nonneg _)
              (Finset.mem_univ i)
            nlinarith [sq_nonneg h.2]
          · rw [Real.norm_eq_abs]
            apply Real.abs_le_sqrt
            linarith
        have h2 := pow_le_pow_left₀ (norm_nonneg h) this 2
        rwa [Real.sq_sqrt (by positivity)] at h2
      have hnorm_ge : ∀ h : (Fin m → ℝ) × ℝ, ∑ i, (h.1 i) ^ 2 + h.2 ^ 2 ≤ (m + 1) * ‖h‖ ^ 2 := by
        intro h
        have hi : ∀ i, (h.1 i) ^ 2 ≤ ‖h‖ ^ 2 := by
          intro i
          have : |h.1 i| ≤ ‖h‖ := by
            rw [← Real.norm_eq_abs]
            exact (norm_le_pi_norm h.1 i).trans (norm_fst_le h)
          have := pow_le_pow_left₀ (abs_nonneg _) this 2
          rwa [sq_abs] at this
        have h2 : h.2 ^ 2 ≤ ‖h‖ ^ 2 := by
          have : |h.2| ≤ ‖h‖ := by
            rw [← Real.norm_eq_abs]
            exact norm_snd_le h
          have := pow_le_pow_left₀ (abs_nonneg _) this 2
          rwa [sq_abs] at this
        have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        nlinarith
      -- main
      refine ⟨lam / (4 * (m + 1)), by positivity, δ, hδ0, ?_⟩
      intro y hy hS
      obtain ⟨hy2, hGpsd⟩ := hy
      set h := y - yopt with hhdef
      have hSeq : SDPData.sqDist y yopt = ∑ i, (h.1 i) ^ 2 + h.2 ^ 2 := by
        simp [SDPData.sqDist, hhdef]
      have hhδ : ‖h‖ < δ := by
        have := hnorm_le h
        rw [← hSeq] at this
        exact lt_of_pow_lt_pow_left₀ 2 hδ0.le (by linarith)
      set z : ℝ → (Fin m → ℝ) × ℝ := fun t => yopt + t • h with hzdef
      have hzU : ∀ t ∈ Set.Icc (0:ℝ) 1, z t ∈ U := by
        intro t ht
        simp only [hUdef, Set.mem_setOf_eq, hzdef, Prod.snd_add, Prod.smul_snd, smul_eq_mul, hhdef,
          Prod.snd_sub]
        rcases eq_or_lt_of_le ht.2 with heq | hlt
        · rw [heq]; linarith
        · nlinarith [mul_pos (sub_pos.2 hlt) hτ, mul_nonneg ht.1 hy2.le]
      have hzd : ∀ t ∈ Set.Icc (0:ℝ) 1, dist (z t) yopt < δ := by
        intro t ht
        rw [dist_eq_norm]
        simp only [hzdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        nlinarith [norm_nonneg h, ht.2]
      have hzder : ∀ t, HasDerivAt z h t := by
        intro t
        have := ((hasDerivAt_id t).smul_const h).const_add yopt
        simpa [hzdef] using this
      have hBt : ∀ t ∈ Set.Icc (0:ℝ) 1, lam / 2 * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (z t) h h := by
        intro t ht
        have hd0 := hδ (hzd t ht)
        have hd : ‖fderiv ℝ (fderiv ℝ f) (z t) - B‖ < lam / 2 := by
          have := dist_eq_norm (fderiv ℝ (fderiv ℝ f) (z t)) B
          exact lt_of_eq_of_lt this.symm hd0
        have hle : ‖(fderiv ℝ (fderiv ℝ f) (z t) - B) h h‖ ≤
            ‖fderiv ℝ (fderiv ℝ f) (z t) - B‖ * ‖h‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
        rw [Real.norm_eq_abs] at hle
        have heq : (fderiv ℝ (fderiv ℝ f) (z t) - B) h h =
            fderiv ℝ (fderiv ℝ f) (z t) h h - B h h := by simp
        rw [heq] at hle
        have := hlamB h
        have hh2 : ‖fderiv ℝ (fderiv ℝ f) (z t) - B‖ * ‖h‖ * ‖h‖ ≤ lam / 2 * ‖h‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_right hd.le (sq_nonneg ‖h‖)
          nlinarith
        linarith [neg_abs_le (fderiv ℝ (fderiv ℝ f) (z t) h h - B h h)]
      have hg1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => fderiv ℝ f (z t) h)
          (fderiv ℝ (fderiv ℝ f) (z t) h h) t := by
        intro t ht
        have hc := (hdiff1 (z t) (hzU t ht)).hasFDerivAt.comp_hasDerivAt t (hzder t)
        have := hc.clm_apply (hasDerivAt_const t h)
        simpa using this
      have hlin : ∀ (a t : ℝ), HasDerivAt (fun t => a * t) a t := by
        intro a t
        simpa using (hasDerivAt_id t).const_mul a
      have hk : MonotoneOn (fun t => fderiv ℝ f (z t) h - lam / 2 * ‖h‖ ^ 2 * t) (Set.Icc 0 1) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
          (f' := fun t => fderiv ℝ (fderiv ℝ f) (z t) h h - lam / 2 * ‖h‖ ^ 2)
        · intro t ht
          exact ((hg1 t ht).sub (hlin _ t)).continuousAt.continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht ⊢
          exact ((hg1 t (Set.Ioo_subset_Icc_self ht)).sub (hlin _ t)).hasDerivWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have := hBt t (Set.Ioo_subset_Icc_self ht)
          linarith
      have hz0 : z 0 = yopt := by simp [hzdef]
      have hz1 : z 1 = y := by simp [hzdef, hhdef]
      have hk0 : ∀ t ∈ Set.Icc (0:ℝ) 1, lam / 2 * ‖h‖ ^ 2 * t ≤ fderiv ℝ f (z t) h := by
        intro t ht
        have := hk ⟨le_refl 0, zero_le_one⟩ ht ht.1
        simp only [hz0, hgrad] at this
        linarith
      have hquad : ∀ t : ℝ, HasDerivAt (fun t => lam / 4 * ‖h‖ ^ 2 * t ^ 2) (lam / 2 * ‖h‖ ^ 2 * t) t := by
        intro t
        have := (hasDerivAt_pow 2 t).const_mul (lam / 4 * ‖h‖ ^ 2)
        exact this.congr_deriv (by norm_num; ring)
      have hg0 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => f (z t)) (fderiv ℝ f (z t) h) t := by
        intro t ht
        exact (hdiff0 (z t) (hzU t ht)).hasFDerivAt.comp_hasDerivAt t (hzder t)
      have hψ : MonotoneOn (fun t => f (z t) - lam / 4 * ‖h‖ ^ 2 * t ^ 2) (Set.Icc 0 1) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
          (f' := fun t => fderiv ℝ f (z t) h - lam / 2 * ‖h‖ ^ 2 * t)
        · intro t ht
          exact ((hg0 t ht).sub (hquad t)).continuousAt.continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht ⊢
          exact ((hg0 t (Set.Ioo_subset_Icc_self ht)).sub (hquad t)).hasDerivWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have := hk0 t (Set.Ioo_subset_Icc_self ht)
          linarith
      have hmono := hψ ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
      simp only [hz0, hz1] at hmono
      have hfopt : f yopt = c ⬝ᵥ yopt.1 := by simp [hfdef, lagrangian, hcs]
      have hfy : f y ≤ c ⬝ᵥ y.1 := by
        have := htr _ hGpsd
        simp only [hfdef, lagrangian]
        linarith
      have hS' := hnorm_ge h
      rw [← hSeq] at hS'
      have hfin : lam / (4 * (m + 1)) * SDPData.sqDist y yopt ≤ lam / 4 * ‖h‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
