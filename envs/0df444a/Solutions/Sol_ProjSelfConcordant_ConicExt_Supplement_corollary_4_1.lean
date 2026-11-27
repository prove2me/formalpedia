-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.Supplement.corollary_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:43.067523+00:00
-- url     : https://prove2.me/submissions/481968af-768d-42f6-8b46-aafd1e04cc2b

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier

open ProjSelfConcordant
open ProjSelfConcordant.ConicExt
open ProjSelfConcordant.ConicExt.Supplement

/-- Corollary 4.1, p. 10: for a projectively self-concordant barrier `f` on a regular convex set
`X ⊂ ℝⁿ` with parameter `γ = (ν − 2)/√(ν − 1)`, for all `x ∈ Xᵒ` and `h ∈ ℝⁿ`,
`max(0, f′(x)[h] + √G(x)[h,h]/√(ν−1)) ≤ σₓ(h) ≤ max(0, f′(x)[h] + √(ν−1)√G(x)[h,h])` and
`|f′(x)[h]| + √G(x)[h,h]/√(ν−1) ≤ πₓ(h) ≤ |f′(x)[h]| + √(ν−1)√G(x)[h,h]`. -/
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (f : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 2 ≤ ν)
    (hf : ProjBarrier ((ν - 2) / Real.sqrt (ν - 1)) X f) :
    ∀ x ∈ interior X, ∀ h : EuclideanSpace ℝ (Fin n),
      (max 0 (fderiv ℝ f x h + Real.sqrt (affMetric f x h h) / Real.sqrt (ν - 1))
          ≤ sigmaGauge X x h ∧
        sigmaGauge X x h
          ≤ max 0 (fderiv ℝ f x h + Real.sqrt (ν - 1) * Real.sqrt (affMetric f x h h))) ∧
      (|fderiv ℝ f x h| + Real.sqrt (affMetric f x h h) / Real.sqrt (ν - 1)
          ≤ piGauge X x h ∧
        piGauge X x h
          ≤ |fderiv ℝ f x h| + Real.sqrt (ν - 1) * Real.sqrt (affMetric f x h h)) := by
            obtain ⟨hXc, hXconv, hXne, hXline⟩ := hX
            obtain ⟨⟨hγ0, hfC, hf1, hf3⟩, hbar⟩ := hf
            set k := Real.sqrt (ν - 1) with hk_def
            set γ := (ν - 2) / Real.sqrt (ν - 1) with hγ_def
            have hk1 : 1 ≤ k := by
              have h1 : (1:ℝ) ≤ ν - 1 := by linarith
              calc (1:ℝ) = Real.sqrt 1 := by simp
                _ ≤ Real.sqrt (ν - 1) := Real.sqrt_le_sqrt h1
            have hkpos : 0 < k := by linarith
            have hkk : k ^ 2 = ν - 1 := Real.sq_sqrt (by linarith)
            have hγk : γ * k = k ^ 2 - 1 := by
              rw [hγ_def, ← hk_def, div_mul_cancel₀ _ hkpos.ne']; linarith
            have hopen : IsOpen (interior X) := isOpen_interior
            have hCA : ∀ y ∈ interior X, ContDiffAt ℝ 3 f y := fun y hy => hfC.contDiffAt (hopen.mem_nhds hy)
            have hline : ∀ (x h : EuclideanSpace ℝ (Fin n)) (τ : ℝ),
                HasDerivAt (fun τ : ℝ => x + τ • h) h τ := by
              intro x h τ
              simpa using ((hasDerivAt_id τ).smul_const h).const_add x
            have hD0 : ∀ (x h : EuclideanSpace ℝ (Fin n)) (τ : ℝ), x + τ • h ∈ interior X →
                HasDerivAt (fun τ : ℝ => f (x + τ • h)) (fderiv ℝ f (x + τ • h) h) τ := by
              intro x h τ hτ
              have hd : DifferentiableAt ℝ f (x + τ • h) := (hCA _ hτ).differentiableAt (by norm_num)
              exact hd.hasFDerivAt.comp_hasDerivAt τ (hline x h τ)
            have hD1 : ∀ (x h : EuclideanSpace ℝ (Fin n)) (τ : ℝ), x + τ • h ∈ interior X →
                HasDerivAt (fun τ : ℝ => fderiv ℝ f (x + τ • h) h)
                  (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h)) τ := by
              intro x h τ hτ
              have hd : DifferentiableAt ℝ (fderiv ℝ f) (x + τ • h) :=
                ((hCA _ hτ).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
              have h0 : HasDerivAt (fun τ : ℝ => fderiv ℝ f (x + τ • h))
                  (fderiv ℝ (fderiv ℝ f) (x + τ • h) h) τ := hd.hasFDerivAt.comp_hasDerivAt τ (hline x h τ)
              have h1 : HasDerivAt (fun τ : ℝ => fderiv ℝ f (x + τ • h) h)
                  (fderiv ℝ (fderiv ℝ f) (x + τ • h) h h) τ :=
                (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt τ h0
              rw [iteratedFDeriv_two_apply]
              exact h1
            have hD2 : ∀ (x h : EuclideanSpace ℝ (Fin n)) (τ : ℝ), x + τ • h ∈ interior X →
                HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h))
                  (iteratedFDeriv ℝ 3 f (x + τ • h) (fun _ => h)) τ := by
              intro x h τ hτ
              have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) (x + τ • h) :=
                (hCA _ hτ).differentiableAt_iteratedFDeriv (by norm_num)
              have h0 : HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ 2 f (x + τ • h))
                  (fderiv ℝ (iteratedFDeriv ℝ 2 f) (x + τ • h) h) τ :=
                hd.hasFDerivAt.comp_hasDerivAt τ (hline x h τ)
              have h1 : HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h))
                  (fderiv ℝ (iteratedFDeriv ℝ 2 f) (x + τ • h) h (fun _ => h)) τ :=
                (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ
                  (fun _ => h)).hasFDerivAt.comp_hasDerivAt τ h0
              have h3 : iteratedFDeriv ℝ 3 f (x + τ • h) (fun _ => h)
                  = fderiv ℝ (iteratedFDeriv ℝ 2 f) (x + τ • h) h (fun _ => h) :=
                iteratedFDeriv_succ_apply_left (n := 2) _
              rw [h3]
              exact h1
            have hdk1 : ∀ y h : EuclideanSpace ℝ (Fin n), dk 1 f y h = fderiv ℝ f y h := by
              intro y h; simp only [dk]; rw [iteratedFDeriv_one_apply]
            have hd2 : ∀ y h : EuclideanSpace ℝ (Fin n), d2 f y h h = iteratedFDeriv ℝ 2 f y (fun _ => h) := by
              intro y h; simp only [d2]; congr 1; ext i; fin_cases i <;> rfl
            -- derivative of p + c * s along the line
            have hderiv : ∀ (x h : EuclideanSpace ℝ (Fin n)) (τ : ℝ), x + τ • h ∈ interior X → h ≠ 0 →
                ∀ c : ℝ,
                HasDerivAt (fun τ : ℝ => fderiv ℝ f (x + τ • h) h + c * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2))
                  (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) + c *
                    ((iteratedFDeriv ℝ 3 f (x + τ • h) (fun _ => h) - 2 * fderiv ℝ f (x + τ • h) h *
                      iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h)) / (2 * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2)))) τ ∧
                (c = k → iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) + c *
                    ((iteratedFDeriv ℝ 3 f (x + τ • h) (fun _ => h) - 2 * fderiv ℝ f (x + τ • h) h *
                      iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h)) / (2 * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2)))
                    ≤ (fderiv ℝ f (x + τ • h) h + c * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2)) ^ 2) ∧
                (c = k⁻¹ → (fderiv ℝ f (x + τ • h) h + c * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2)) ^ 2
                    ≤ iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) + c *
                    ((iteratedFDeriv ℝ 3 f (x + τ • h) (fun _ => h) - 2 * fderiv ℝ f (x + τ • h) h *
                      iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h)) / (2 * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2)))) := by
              intro x h τ hτ hh c
              set y := x + τ • h with hy
              set P := fderiv ℝ f y h with hP
              set A := iteratedFDeriv ℝ 2 f y (fun _ => h) with hA
              set D := iteratedFDeriv ℝ 3 f y (fun _ => h) with hD
              have hG : 0 < A - P ^ 2 := by
                have := hf1 y hτ h hh
                rw [hdk1] at this; exact this
              have h3 := hf3 y hτ h
              rw [hdk1] at h3
              change |D - 6 * A * P + 4 * P ^ 3| ≤ 2 * γ * (A - P ^ 2) ^ (3 / 2 : ℝ) at h3
              set s := Real.sqrt (A - P ^ 2) with hs
              have hspos : 0 < s := Real.sqrt_pos.2 hG
              have hss : s ^ 2 = A - P ^ 2 := Real.sq_sqrt hG.le
              have hpow : (A - P ^ 2) ^ (3 / 2 : ℝ) = s ^ 3 := by
                rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hG.le]; norm_num
              rw [hpow] at h3
              set C := D - 6 * A * P + 4 * P ^ 3 with hC
              have hexp : A + c * ((D - 2 * P * A) / (2 * s)) = s ^ 2 + P ^ 2 + c * C / (2 * s)
                  + 2 * c * P * s := by
                have hA' : A = s ^ 2 + P ^ 2 := by linarith
                rw [hC, hA']; field_simp; ring
              refine ⟨?_, ?_, ?_⟩
              · have eP2 : HasDerivAt (fun τ : ℝ => fderiv ℝ f (x + τ • h) h ^ 2) (2 * P * A) τ := by
                  have := (hD1 x h τ hτ).fun_pow 2
                  refine this.congr_deriv ?_
                  simp only [← hy, ← hP, ← hA]; norm_num
                have e1 : HasDerivAt (fun τ : ℝ => iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h)
                    - fderiv ℝ f (x + τ • h) h ^ 2) (D - 2 * P * A) τ := (hD2 x h τ hτ).fun_sub eP2
                have e2 := (hD1 x h τ hτ).fun_add ((e1.sqrt hG.ne').const_mul c)
                exact e2.congr_deriv (by simp only [← hy, ← hP, ← hA, ← hs])
              · intro hc
                rw [hexp, hc]
                have hCb : C ≤ 2 * γ * s ^ 3 := le_trans (le_abs_self C) h3
                have : k * C / (2 * s) ≤ (k ^ 2 - 1) * s ^ 2 := by
                  rw [div_le_iff₀ (by positivity), ← hγk]
                  have := mul_le_mul_of_nonneg_left hCb hkpos.le
                  linarith only [this]
                have e : (P + k * s) ^ 2 = P ^ 2 + 2 * k * P * s + k ^ 2 * s ^ 2 := by ring
                rw [e]; linarith only [this]
              · intro hc
                rw [hexp, hc]
                have hCb : -(2 * γ * s ^ 3) ≤ C := by
                  have := neg_abs_le C; linarith
                have hγ' : γ = (k ^ 2 - 1) / k := by field_simp; linarith
                have : -((k ^ 2 - 1) / k ^ 2) * s ^ 2 ≤ k⁻¹ * C / (2 * s) := by
                  rw [le_div_iff₀ (by positivity)]
                  have : k⁻¹ * C ≥ k⁻¹ * (-(2 * γ * s ^ 3)) := mul_le_mul_of_nonneg_left hCb (by positivity)
                  rw [hγ'] at this
                  have e : k⁻¹ * (-(2 * ((k ^ 2 - 1) / k) * s ^ 3)) = -((k ^ 2 - 1) / k ^ 2) * s ^ 2 * (2 * s) := by
                    field_simp
                  linarith
                have e2 : (P + k⁻¹ * s) ^ 2 = P ^ 2 + 2 * k⁻¹ * P * s + s ^ 2 / k ^ 2 := by
                  field_simp; ring
                have e3 : s ^ 2 / k ^ 2 = s ^ 2 - (k ^ 2 - 1) / k ^ 2 * s ^ 2 := by
                  field_simp; ring
                rw [e2]; linarith only [this, e3]
            have hseg : ∀ x ∈ interior X, ∀ h : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, 0 < t → x + t • h ∈ X →
                ∀ τ : ℝ, 0 ≤ τ → τ < t → x + τ • h ∈ interior X := by
              intro x hx h t ht htX τ hτ0 hτt
              have hmem := hXconv.add_smul_sub_mem_interior' (subset_closure htX) hx
                (t := 1 - τ / t) ⟨by rw [sub_pos, div_lt_one ht]; exact hτt,
                  by linarith [div_nonneg hτ0 ht.le]⟩
              have e : x + t • h + (1 - τ / t) • (x - (x + t • h)) = x + τ • h := by
                have e1 : t + (1 - τ / t) * (-t) = τ := by field_simp; ring
                calc x + t • h + (1 - τ / t) • (x - (x + t • h))
                    = x + (t + (1 - τ / t) * (-t)) • h := by module
                  _ = x + τ • h := by rw [e1]
              rwa [e] at hmem
            have hbnd : ∀ (x h : EuclideanSpace ℝ (Fin n)) (b M : ℝ),
                (∀ τ : ℝ, 0 ≤ τ → τ < b → x + τ • h ∈ interior X) →
                (∀ τ : ℝ, 0 ≤ τ → τ < b → fderiv ℝ f (x + τ • h) h ≤ M) → 0 ≤ M →
                ∀ τ : ℝ, 0 ≤ τ → τ < b → f (x + τ • h) ≤ f x + M * b := by
              intro x h b M hin hPM hM0 τ0 h0 h1
              have hd : ∀ τ ∈ Set.Icc 0 τ0, HasDerivAt (fun τ : ℝ => f (x + τ • h) - M * τ)
                  (fderiv ℝ f (x + τ • h) h - M) τ := by
                intro τ hτ
                have hτb : τ < b := lt_of_le_of_lt hτ.2 h1
                have e0 := hD0 x h τ (hin τ hτ.1 hτb)
                have e1 : HasDerivAt (fun τ : ℝ => M * τ) M τ := by
                  simpa using (hasDerivAt_id' τ).const_mul M
                exact e0.fun_sub e1
              have hanti : AntitoneOn (fun τ : ℝ => f (x + τ • h) - M * τ) (Set.Icc 0 τ0) := by
                apply antitoneOn_of_deriv_nonpos (convex_Icc 0 τ0)
                · exact fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt
                · intro τ hτ; rw [interior_Icc] at hτ
                  exact (hd τ (Set.Ioo_subset_Icc_self hτ)).differentiableAt.differentiableWithinAt
                · intro τ hτ; rw [interior_Icc] at hτ
                  rw [(hd τ (Set.Ioo_subset_Icc_self hτ)).deriv]
                  linarith only [hPM τ hτ.1.le (hτ.2.trans h1)]
              have := hanti ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
              simp only [zero_smul, add_zero, mul_zero, sub_zero] at this
              have hMb : M * τ0 ≤ M * b := mul_le_mul_of_nonneg_left h1.le hM0
              linarith only [this, hMb]
            have key : ∀ x ∈ interior X, ∀ h : EuclideanSpace ℝ (Fin n),
                max 0 (fderiv ℝ f x h + k⁻¹ * Real.sqrt
                  (iteratedFDeriv ℝ 2 f x (fun _ => h) - (fderiv ℝ f x h) ^ 2)) ≤ sigmaGauge X x h ∧
                sigmaGauge X x h ≤ max 0 (fderiv ℝ f x h + k * Real.sqrt
                  (iteratedFDeriv ℝ 2 f x (fun _ => h) - (fderiv ℝ f x h) ^ 2)) := by
              intro x hx h
              have hσ : sigmaGauge X x h = sInf {s : ℝ | ∃ t : ℝ, 0 < t ∧ x + t • h ∈ X ∧ s = t⁻¹} := rfl
              have hSbdd : BddBelow {s : ℝ | ∃ t : ℝ, 0 < t ∧ x + t • h ∈ X ∧ s = t⁻¹} :=
                ⟨0, by rintro s ⟨t, ht, -, rfl⟩; exact (inv_pos.2 ht).le⟩
              have hU : IsOpen {τ : ℝ | x + τ • h ∈ interior X} :=
                isOpen_interior.preimage (by fun_prop)
              obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hU 0 (by simpa using hx)
              have hSne : {s : ℝ | ∃ t : ℝ, 0 < t ∧ x + t • h ∈ X ∧ s = t⁻¹}.Nonempty :=
                ⟨(ε/2)⁻¹, ε/2, by positivity, interior_subset (hε (by
                  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)), rfl⟩
              set q : ℝ → ℝ := fun τ => fderiv ℝ f (x + τ • h) h + k⁻¹ * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2) with hq
              set r : ℝ → ℝ := fun τ => fderiv ℝ f (x + τ • h) h + k * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2) with hr
              have hq0 : q 0 = fderiv ℝ f x h + k⁻¹ * Real.sqrt
                  (iteratedFDeriv ℝ 2 f x (fun _ => h) - (fderiv ℝ f x h) ^ 2) := by simp [hq]
              have hr0 : r 0 = fderiv ℝ f x h + k * Real.sqrt
                  (iteratedFDeriv ℝ 2 f x (fun _ => h) - (fderiv ℝ f x h) ^ 2) := by simp [hr]
              constructor
              · rw [hσ]
                apply le_csInf hSne
                rintro s ⟨t, ht, htX, rfl⟩
                refine max_le (inv_pos.2 ht).le ?_
                rw [← hq0]
                by_contra hlt
                push Not at hlt
                have hqpos : 0 < q 0 := lt_trans (inv_pos.2 ht) hlt
                have hh : h ≠ 0 := by
                  rintro rfl
                  have hz : (iteratedFDeriv ℝ 2 f (x + (0:ℝ) • (0:EuclideanSpace ℝ (Fin n))))
                      (fun _ => 0) = 0 := (iteratedFDeriv ℝ 2 f _).map_zero
                  have hz2 : q 0 = 0 := by
                    simp only [hq]; rw [hz]; simp
                  linarith
                set τs := (q 0)⁻¹ with hτs
                have hτst : τs < t := by
                  rw [hτs]; rw [inv_lt_comm₀ hqpos ht]; exact hlt
                have hin : ∀ τ ∈ Set.Icc 0 τs, x + τ • h ∈ interior X := fun τ hτ =>
                  hseg x hx h t ht htX τ hτ.1 (lt_of_le_of_lt hτ.2 hτst)
                have hqd : ∀ τ ∈ Set.Icc 0 τs, ∃ d, HasDerivAt q d τ ∧ q τ ^ 2 ≤ d := fun τ hτ =>
                  ⟨_, (hderiv x h τ (hin τ hτ) hh k⁻¹).1, (hderiv x h τ (hin τ hτ) hh k⁻¹).2.2 rfl⟩
                choose! dq hdq hdq2 using hqd
                have hτs0 : 0 ≤ τs := (inv_pos.2 hqpos).le
                have hmono : MonotoneOn q (Set.Icc 0 τs) := by
                  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 τs)
                  · exact fun τ hτ => (hdq τ hτ).continuousAt.continuousWithinAt
                  · intro τ hτ; rw [interior_Icc] at hτ
                    exact (hdq τ (Set.Ioo_subset_Icc_self hτ)).differentiableAt.differentiableWithinAt
                  · intro τ hτ; rw [interior_Icc] at hτ
                    rw [(hdq τ (Set.Ioo_subset_Icc_self hτ)).deriv]
                    exact le_trans (sq_nonneg _) (hdq2 τ (Set.Ioo_subset_Icc_self hτ))
                have hqge : ∀ τ ∈ Set.Icc 0 τs, q 0 ≤ q τ := fun τ hτ => hmono ⟨le_rfl, hτs0⟩ hτ hτ.1
                have hwd : ∀ τ ∈ Set.Icc 0 τs, HasDerivAt (q⁻¹ + id) (-(dq τ) / (q τ) ^ 2 + 1) τ :=
                  fun τ hτ => ((hdq τ hτ).inv (by linarith [hqge τ hτ])).add (hasDerivAt_id τ)
                have hw : AntitoneOn (q⁻¹ + id) (Set.Icc 0 τs) := by
                  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 τs)
                  · exact fun τ hτ => (hwd τ hτ).continuousAt.continuousWithinAt
                  · intro τ hτ; rw [interior_Icc] at hτ
                    exact (hwd τ (Set.Ioo_subset_Icc_self hτ)).differentiableAt.differentiableWithinAt
                  · intro τ hτ; rw [interior_Icc] at hτ
                    have hτ' := Set.Ioo_subset_Icc_self hτ
                    rw [(hwd τ hτ').deriv]
                    have hqp : 0 < q τ := by linarith [hqge τ hτ']
                    have : 1 ≤ dq τ / q τ ^ 2 := by
                      rw [le_div_iff₀ (by positivity)]; linarith [hdq2 τ hτ']
                    rw [neg_div]; linarith
                have hfin := hw ⟨le_rfl, hτs0⟩ ⟨hτs0, le_rfl⟩ hτs0
                simp only [Pi.add_apply, Pi.inv_apply, id] at hfin
                have hqp : 0 < q τs := by linarith [hqge τs ⟨hτs0, le_rfl⟩]
                rw [← hτs] at hfin
                linarith [inv_pos.2 hqp]
              · rw [hσ]
                apply le_of_forall_gt_imp_ge_of_dense
                intro c hc
                have hc0 : 0 < c := lt_of_le_of_lt (le_max_left _ _) hc
                have hrc : r 0 < c := by rw [hr0]; exact lt_of_le_of_lt (le_max_right _ _) hc
                set T := c⁻¹ with hT
                have hT0 : 0 < T := inv_pos.2 hc0
                suffices hmem : x + T • h ∈ X from csInf_le hSbdd ⟨T, hT0, hmem, by rw [hT, inv_inv]⟩
                by_cases hh : h = 0
                · subst hh; simpa using interior_subset hx
                by_contra hTX
                set J := {τ : ℝ | τ ∈ Set.Icc 0 T ∧ x + τ • h ∈ X} with hJ
                have hJc : IsClosed J := isClosed_Icc.inter (hXc.preimage (by fun_prop))
                have hJne : J.Nonempty := ⟨0, ⟨le_rfl, hT0.le⟩, by simpa using interior_subset hx⟩
                have hJbdd : BddAbove J := ⟨T, fun τ hτ => hτ.1.2⟩
                set b := sSup J with hb
                have hbJ : b ∈ J := hJc.csSup_mem hJne hJbdd
                have hbT : b < T := lt_of_le_of_ne hbJ.1.2 (by intro e; apply hTX; rw [← e]; exact hbJ.2)
                have hbint : x + b • h ∉ interior X := by
                  intro hbi
                  obtain ⟨δ, δpos, hδ⟩ := Metric.isOpen_iff.1 hU b hbi
                  have h1 : b < min (b + δ/2) T := lt_min (by linarith) hbT
                  have h2 : min (b + δ/2) T ∈ J := by
                    refine ⟨⟨by linarith [hbJ.1.1], min_le_right _ _⟩, interior_subset (hδ ?_)⟩
                    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
                    linarith [min_le_left (b + δ/2) T]
                  linarith [le_csSup hJbdd h2]
                have hb0 : 0 < b := by
                  rcases eq_or_lt_of_le hbJ.1.1 with e | e
                  · exfalso; apply hbint; rw [← e]; simpa using hx
                  · exact e
                have hfront : x + b • h ∈ frontier X := by
                  rw [frontier, hXc.closure_eq]; exact ⟨hbJ.2, hbint⟩
                have hin : ∀ τ : ℝ, 0 ≤ τ → τ < b → x + τ • h ∈ interior X :=
                  fun τ h0 h1 => hseg x hx h b hb0 hbJ.2 τ h0 h1
                set L := (b + T) / 2 with hL
                set lam := T / L with hlam
                have hLpos : 0 < L := by linarith
                have hbL : b < L := by linarith
                have hlam1 : 1 < lam := by rw [hlam, one_lt_div hLpos]; linarith
                set B : ℝ → ℝ := fun τ => (lam * (L - τ))⁻¹ with hB
                have hBd : ∀ τ, τ < L → HasDerivAt B (lam * B τ ^ 2) τ := by
                  intro τ hτ
                  have h1 : HasDerivAt (fun τ : ℝ => lam * (L - τ)) (lam * (-1)) τ :=
                    ((hasDerivAt_id' τ).const_sub L).const_mul lam
                  have hne : lam * (L - τ) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
                  have h2 := h1.inv hne
                  refine h2.congr_deriv ?_
                  simp only [hB]; field_simp
                have hB0 : B 0 = c := by
                  simp only [hB]; rw [sub_zero, hlam, div_mul_cancel₀ _ hLpos.ne', hT, inv_inv]
                have hrd : ∀ τ : ℝ, 0 ≤ τ → τ < b → ∃ d, HasDerivAt r d τ ∧ d ≤ r τ ^ 2 := fun τ h0 h1 =>
                  ⟨_, (hderiv x h τ (hin τ h0 h1) hh k).1, (hderiv x h τ (hin τ h0 h1) hh k).2.1 rfl⟩
                choose! dr hdr hdr2 using hrd
                have hrB : ∀ τ : ℝ, 0 ≤ τ → τ < b → r τ ≤ B τ := by
                  intro τ0 h0 h1
                  refine image_le_of_deriv_right_lt_deriv_boundary' (f := r) (f' := dr) (a := 0) (b := τ0)
                    (B' := fun τ => lam * B τ ^ 2) ?_ ?_ ?_ ?_ ?_ ?_ ⟨h0, le_rfl⟩
                  · intro τ hτ; exact (hdr τ hτ.1 (lt_of_le_of_lt hτ.2 h1)).continuousAt.continuousWithinAt
                  · intro τ hτ; exact (hdr τ hτ.1 (hτ.2.trans h1)).hasDerivWithinAt
                  · rw [hB0]; exact hrc.le
                  · intro τ hτ; exact (hBd τ (lt_of_le_of_lt hτ.2 (h1.trans hbL))).continuousAt.continuousWithinAt
                  · intro τ hτ; exact (hBd τ (hτ.2.trans (h1.trans hbL))).hasDerivWithinAt
                  · intro τ hτ
                    have hτb : τ < b := hτ.2.trans h1
                    have hBp : 0 < B τ := by
                      simp only [hB]
                      exact inv_pos.2 (mul_pos (lt_trans one_pos hlam1) (sub_pos.2 (hτb.trans hbL)))
                    have := hdr2 τ hτ.1 hτb
                    intro he
                    rw [he] at this
                    exact lt_of_le_of_lt this (lt_mul_of_one_lt_left (pow_pos hBp 2) hlam1)
                have hlam0 : 0 < lam := lt_trans one_pos hlam1
                obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (lam * (L - b))⁻¹ := ⟨_, rfl⟩
                have hMpos : 0 < M := by rw [hM]; exact inv_pos.2 (mul_pos hlam0 (sub_pos.2 hbL))
                have hPM : ∀ τ : ℝ, 0 ≤ τ → τ < b → fderiv ℝ f (x + τ • h) h ≤ M := by
                  intro τ h0 h1
                  have e1 : fderiv ℝ f (x + τ • h) h + k * Real.sqrt
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2)
                      ≤ B τ := hrB τ h0 h1
                  have e2 : B τ ≤ M := by
                    simp only [hB, hM]
                    apply inv_anti₀ (mul_pos hlam0 (sub_pos.2 hbL))
                    exact mul_le_mul_of_nonneg_left (sub_le_sub_left h1.le L) hlam0.le
                  have e3 := mul_nonneg hkpos.le (Real.sqrt_nonneg
                    (iteratedFDeriv ℝ 2 f (x + τ • h) (fun _ => h) - (fderiv ℝ f (x + τ • h) h) ^ 2))
                  linarith only [e1, e2, e3]
                have hφ : ∀ τ : ℝ, 0 ≤ τ → τ < b → f (x + τ • h) ≤ f x + M * b :=
                  hbnd x h b M hin hPM hMpos.le
                have hT1 : Filter.Tendsto (fun τ : ℝ => x + τ • h) (nhdsWithin b (Set.Iio b))
                    (nhdsWithin (x + b • h) (interior X)) := by
                  apply tendsto_nhdsWithin_iff.2
                  have hcont : Continuous (fun τ : ℝ => x + τ • h) := by fun_prop
                  refine ⟨(hcont.tendsto b).mono_left nhdsWithin_le_nhds, ?_⟩
                  filter_upwards [Ioo_mem_nhdsLT hb0] with τ hτ
                  exact hin τ hτ.1.le hτ.2
                have hT2 := (hbar _ hfront).comp hT1
                have hev := hT2.eventually (Filter.eventually_gt_atTop (f x + M * b))
                have hev2 : ∀ᶠ τ in nhdsWithin b (Set.Iio b), τ ∈ Set.Ioo 0 b := Ioo_mem_nhdsLT hb0
                obtain ⟨τ, h1, h2⟩ := (hev.and hev2).exists
                have := hφ τ h2.1.le h2.2
                simp only [Function.comp] at h1
                linarith only [this, h1]
            intro x hx h
            have hAm : ∀ h, affMetric f x h h
                = iteratedFDeriv ℝ 2 f x (fun _ => h) - (fderiv ℝ f x h) ^ 2 := by
              intro h; rw [affMetric, hd2]; ring
            have hneg1 : fderiv ℝ f x (-h) = - fderiv ℝ f x h := map_neg _ _
            have hneg2 : affMetric f x (-h) (-h) = affMetric f x h h := by
              have e : iteratedFDeriv ℝ 2 f x (fun _ => -h) = iteratedFDeriv ℝ 2 f x (fun _ => h) := by
                rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
                simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
              rw [hAm, hAm, hneg1, e, neg_sq]
            obtain ⟨k1, k2⟩ := key x hx h
            obtain ⟨k3, k4⟩ := key x hx (-h)
            rw [← hAm h] at k1 k2
            rw [← hAm (-h), hneg2, hneg1] at k3 k4
            have hg : 0 ≤ Real.sqrt (affMetric f x h h) := Real.sqrt_nonneg _
            have e : Real.sqrt (affMetric f x h h) / k = k⁻¹ * Real.sqrt (affMetric f x h h) := by ring
            unfold piGauge
            rw [e]
            refine ⟨⟨k1, k2⟩, ?_, ?_⟩
            · rcases le_total 0 (fderiv ℝ f x h) with ha | ha
              · rw [abs_of_nonneg ha]; exact le_trans (le_max_right _ _) (le_trans k1 (le_max_left _ _))
              · rw [abs_of_nonpos ha]; exact le_trans (le_max_right _ _) (le_trans k3 (le_max_right _ _))
            · have hkg := mul_nonneg hkpos.le hg
              apply max_le
              · refine le_trans k2 (max_le ?_ ?_)
                · linarith [abs_nonneg (fderiv ℝ f x h)]
                · linarith [le_abs_self (fderiv ℝ f x h)]
              · refine le_trans k4 (max_le ?_ ?_)
                · linarith [abs_nonneg (fderiv ℝ f x h)]
                · linarith [neg_abs_le (fderiv ℝ f x h)]
