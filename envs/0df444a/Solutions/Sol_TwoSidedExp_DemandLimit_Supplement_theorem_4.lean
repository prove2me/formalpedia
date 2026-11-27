-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:50.188195+00:00
-- url     : https://prove2.me/submissions/845a1e75-126b-4708-8766-34e7bcbc085a

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Supply

open Filter Topology MeasureTheory

open TwoSidedExp
open TwoSidedExp.DemandLimit
open TwoSidedExp.DemandLimit.Supplement

/-- Theorem 4, p. 22, including all three clauses and the generic limit's quantifier order. -/
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) :
    (∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
      Tendsto (fun n => lam n / tau n) atTop atTop →
      ∀ (sGT sGC : ℕ → Θ × Fin 2 → ℝ),
        (∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
        (∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
      Tendsto (fun n => M.gte (lam n) (sGT n) (sGC n) / tau n) atTop (𝓝 0)) ∧
    (∀ aL : ℝ, 0 < aL → aL < 1 →
      ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
        Tendsto (fun n => lam n / tau n) atTop atTop →
      ∀ sLR : ℕ → Θ × Fin 2 → ℝ,
        (∀ n, (M.expt 1 aL).IsSteady (lam n) (tau n) (sLR n)) →
      Tendsto (fun n => M.lrEst (lam n) aL (sLR n) / tau n) atTop (𝓝 0)) ∧
    (∀ aC : ℝ, 0 < aC → aC < 1 →
      ∀ᵐ w ∂(volume : Measure (Γ → Θ → ℝ)), (∀ γ θ, 0 < w γ θ) →
        ∃ L : ℝ, L ≠ 0 ∧
          ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
            Tendsto (fun n => lam n / tau n) atTop atTop →
          ∀ (sCR sGT sGC : ℕ → Θ × Fin 2 → ℝ),
            (∀ n, ((M.withVt w).expt aC 1).IsSteady (lam n) (tau n) (sCR n)) →
            (∀ n, ((M.withVt w).expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
            (∀ n, ((M.withVt w).expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
          Tendsto (fun n => (M.withVt w).crEst (lam n) aC (sCR n) / tau n
            - (M.withVt w).gte (lam n) (sGT n) (sGC n) / tau n) atTop (𝓝 L)) := by
              classical
              obtain ⟨γ0⟩ : Nonempty Γ := by
                by_contra h
                rw [not_nonempty_iff] at h
                have := hM.phi_sum
                simp at this
              obtain ⟨T, hT⟩ : ∃ T : Model Γ Θ → ℝ → Fin 2 → Θ × Fin 2 → ℝ, ∀ M' aC i p,
                  T M' aC i p = ∑ γ, (M'.expt aC 1).φ (γ, i) * (M'.expt aC 1).α (γ, i) p *
                    (M'.expt aC 1).v (γ, i) p / (M'.expt aC 1).eps (γ, i) := ⟨_, fun _ _ _ _ => rfl⟩
              have G : ∀ (M' : Model Γ Θ), M'.Standing → ∀ aC aL : ℝ, 0 ≤ aC → aC ≤ 1 → 0 ≤ aL → aL ≤ 1 →
                  ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
                  Tendsto (fun n => lam n / tau n) atTop atTop →
                  ∀ s : ℕ → Θ × Fin 2 → ℝ, (∀ n, (M'.expt aC aL).IsSteady (lam n) (tau n) (s n)) →
                  ∀ i j : Fin 2, Tendsto (fun n => M'.Q (lam n) aC aL (s n) i j / tau n) atTop
                    (𝓝 (∑ θ, T M' aC i (θ, j) * ((M'.expt aC aL).ρ (θ, j) * M'.sys.ν θ /
                      (T M' aC 0 (θ, j) + T M' aC 1 (θ, j))))) := by
                intro M' hM' aC aL haC haC1 haL haL1 lam tau hlam htau hr s hs i j
                obtain ⟨E, hE⟩ : ∃ E, E = M'.expt aC aL := ⟨_, rfl⟩
                rw [← hE] at hs ⊢
                have hφ : ∀ q, 0 ≤ E.φ q := by
                  rintro ⟨γ, i⟩; simp only [hE, Model.expt]; split_ifs
                  · exact mul_nonneg haC (hM'.phi_pos γ).le
                  · exact mul_nonneg (by linarith) (hM'.phi_pos γ).le
                obtain ⟨q0, hφ0⟩ : ∃ q0, 0 < E.φ q0 := by
                  rcases haC.lt_or_eq with h | h
                  · refine ⟨(γ0, 1), ?_⟩
                    simp only [hE, Model.expt]; simp only [if_true]; exact mul_pos h (hM'.phi_pos γ0)
                  · refine ⟨(γ0, 0), ?_⟩
                    simp only [hE, Model.expt, ← h]; simp
                    exact hM'.phi_pos γ0
                have hα : ∀ q p, 0 < E.α q p := by
                  intro q p; simp only [hE, Model.expt]; split_ifs
                  · exact hM'.alphat_pos _ _
                  · exact hM'.alpha_pos _ _
                have hv : ∀ q p, 0 < E.v q p := by
                  intro q p; simp only [hE, Model.expt]; split_ifs
                  · exact hM'.vt_pos _ _
                  · exact hM'.v_pos _ _
                have heps : ∀ q, 0 < E.eps q := fun q => by rw [hE]; exact hM'.eps_pos q.1
                have hν : ∀ p, E.ν p = M'.sys.ν p.1 := fun p => by rw [hE]; rfl
                have hνpos : ∀ θ, 0 < M'.sys.ν θ := hM'.nu_pos
                have hρ : ∀ p, 0 ≤ E.ρ p := by
                  rintro ⟨θ, j⟩; simp only [hE, Model.expt, Model.rhoL]; split_ifs
                  · exact mul_nonneg haL (hM'.rho_pos θ).le
                  · exact mul_nonneg (by linarith) (hM'.rho_pos θ).le
                obtain ⟨D, hD⟩ : ∃ D : Γ × Fin 2 → (Θ × Fin 2 → ℝ) → ℝ, ∀ q x,
                    D q x = E.eps q + ∑ p', E.α q p' * E.v q p' * x p' := ⟨_, fun _ _ => rfl⟩
                have hS : ∀ n p, 0 ≤ s n p ∧ s n p ≤ E.ρ p := fun n p => (hs n).1 p
                have hDge : ∀ n q, E.eps q ≤ D q (s n) := by
                  intro n q; rw [hD]
                  have : 0 ≤ ∑ p', E.α q p' * E.v q p' * s n p' :=
                    Finset.sum_nonneg (fun p' _ => mul_nonneg (mul_pos (hα q p') (hv q p')).le (hS n p').1)
                  linarith
                have hDpos : ∀ n q, 0 < D q (s n) := fun n q => lt_of_lt_of_le (heps q) (hDge n q)
                have hDle : ∀ n q, D q (s n) ≤ D q E.ρ := by
                  intro n q; rw [hD, hD]
                  gcongr with p' _
                  · exact (mul_pos (hα q p') (hv q p')).le
                  · exact (hS n p').2
                obtain ⟨r, hr_def⟩ : ∃ r : ℕ → ℝ, r = fun n => lam n / tau n := ⟨_, rfl⟩
                rw [← hr_def] at hr
                have hrpos : ∀ n, 0 < r n := fun n => by rw [hr_def]; exact div_pos (hlam n) (htau n)
                obtain ⟨k, hk⟩ : ∃ k : ℕ → Θ × Fin 2 → ℝ, ∀ n p,
                    k n p = ∑ q, E.φ q * E.α q p * E.v q p / D q (s n) := ⟨_, fun _ _ => rfl⟩
                have hsteady : ∀ n p, (E.ρ p - s n p) * M'.sys.ν p.1 = r n * s n p * k n p := by
                  intro n p
                  have h := (hs n).2 p
                  simp only [MFSystem.choice, ← hD, hν] at h
                  have h2 : lam n * ∑ q, E.φ q * (E.α q p * E.v q p * s n p / D q (s n))
                      = tau n * (r n * s n p * k n p) := by
                    rw [hk, hr_def, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun q _ => ?_)
                    have := (hDpos n q).ne'
                    have := (htau n).ne'
                    field_simp
                  have h3 := h.trans h2
                  have h4 : tau n * ((E.ρ p - s n p) * M'.sys.ν p.1) = tau n * (r n * s n p * k n p) := by
                    rw [← h3]; ring
                  exact mul_left_cancel₀ (htau n).ne' h4
                -- lower bound on k
                have hc : ∀ p, 0 < E.φ q0 * E.α q0 p * E.v q0 p / D q0 E.ρ := by
                  intro p
                  have : 0 < D q0 E.ρ := lt_of_lt_of_le (hDpos 0 _) (hDle 0 _)
                  exact div_pos (mul_pos (mul_pos hφ0 (hα _ _)) (hv _ _)) this
                have hkc : ∀ n p, E.φ q0 * E.α q0 p * E.v q0 p / D q0 E.ρ ≤ k n p := by
                  intro n p
                  rw [hk]
                  refine le_trans ?_ (Finset.single_le_sum (f := fun q => E.φ q * E.α q p * E.v q p / D q (s n))
                    (fun q _ => div_nonneg (mul_nonneg (mul_nonneg (hφ q) (hα q p).le) (hv q p).le) (hDpos n q).le)
                    (Finset.mem_univ q0))
                  exact div_le_div_of_nonneg_left (mul_pos (mul_pos hφ0 (hα _ _)) (hv _ _)).le (hDpos n _) (hDle n _)
                have hs0 : ∀ p, Tendsto (fun n => s n p) atTop (𝓝 0) := by
                  intro p
                  set c := E.φ q0 * E.α q0 p * E.v q0 p / D q0 E.ρ with hcdef
                  have hup : Tendsto (fun n => E.ρ p * M'.sys.ν p.1 / (c * r n)) atTop (𝓝 0) :=
                    tendsto_const_nhds.div_atTop (hr.const_mul_atTop (hc p))
                  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
                    (fun n => (hS n p).1) (fun n => ?_)
                  rw [le_div_iff₀ (mul_pos (hc p) (hrpos n))]
                  have h1 := hsteady n p
                  have h2 : s n p * (c * r n) ≤ s n p * (k n p * r n) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hkc n p) (hrpos n).le) (hS n p).1
                  have h3 : 0 ≤ s n p * M'.sys.ν p.1 := mul_nonneg (hS n p).1 (hνpos _).le
                  nlinarith
                have hDlim : ∀ q, Tendsto (fun n => D q (s n)) atTop (𝓝 (E.eps q)) := by
                  intro q
                  have : Tendsto (fun n => E.eps q + ∑ p', E.α q p' * E.v q p' * s n p') atTop
                      (𝓝 (E.eps q + ∑ p', E.α q p' * E.v q p' * 0)) :=
                    tendsto_const_nhds.add (tendsto_finsetSum _ fun p' _ => (hs0 p').const_mul _)
                  simp only [mul_zero, Finset.sum_const_zero, add_zero] at this
                  simpa only [hD] using this
                have hK : ∀ p, ∑ q, E.φ q * E.α q p * E.v q p / E.eps q = T M' aC 0 p + T M' aC 1 p := by
                  intro p
                  rw [hT, hT, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl (fun γ _ => ?_)
                  rw [Fin.sum_univ_two, hE]
                  rfl
                have hKpos : ∀ p, 0 < T M' aC 0 p + T M' aC 1 p := by
                  intro p
                  rw [← hK]
                  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun q => E.φ q * E.α q p * E.v q p / E.eps q)
                    (fun q _ => div_nonneg (mul_nonneg (mul_nonneg (hφ q) (hα q p).le) (hv q p).le) (heps q).le)
                    (Finset.mem_univ q0))
                  exact div_pos (mul_pos (mul_pos hφ0 (hα _ _)) (hv _ _)) (heps _)
                have hklim : ∀ p, Tendsto (fun n => k n p) atTop (𝓝 (T M' aC 0 p + T M' aC 1 p)) := by
                  intro p
                  rw [← hK]
                  simp only [hk]
                  exact tendsto_finsetSum _ fun q _ => tendsto_const_nhds.div (hDlim q) (heps q).ne'
                have hx : ∀ p, Tendsto (fun n => r n * s n p) atTop
                    (𝓝 (E.ρ p * M'.sys.ν p.1 / (T M' aC 0 p + T M' aC 1 p))) := by
                  intro p
                  have : Tendsto (fun n => (E.ρ p - s n p) * M'.sys.ν p.1 / k n p) atTop
                      (𝓝 ((E.ρ p - 0) * M'.sys.ν p.1 / (T M' aC 0 p + T M' aC 1 p))) :=
                    ((tendsto_const_nhds.sub (hs0 p)).mul tendsto_const_nhds).div (hklim p) (hKpos p).ne'
                  rw [sub_zero] at this
                  refine this.congr (fun n => ?_)
                  have hkpos : 0 < k n p := lt_of_lt_of_le (hc p) (hkc n p)
                  rw [div_eq_iff hkpos.ne', hsteady]
                have hQ : ∀ n, M'.Q (lam n) aC aL (s n) i j / tau n
                    = ∑ θ, ∑ γ, E.φ (γ, i) * E.α (γ, i) (θ, j) * E.v (γ, i) (θ, j) * (r n * s n (θ, j))
                        / D (γ, i) (s n) := by
                  intro n
                  simp only [Model.Q, ← hE, MFSystem.choice, ← hD, hr_def]
                  rw [Finset.mul_sum, Finset.sum_div]
                  refine Finset.sum_congr rfl (fun θ _ => ?_)
                  rw [Finset.mul_sum, Finset.sum_div]
                  refine Finset.sum_congr rfl (fun γ _ => ?_)
                  have := (hDpos n (γ, i)).ne'
                  have := (htau n).ne'
                  field_simp
                simp only [hQ]
                have hlim := tendsto_finsetSum (Finset.univ : Finset Θ) fun θ _ =>
                  tendsto_finsetSum (Finset.univ : Finset Γ) fun γ _ =>
                    ((tendsto_const_nhds (x := E.φ (γ, i) * E.α (γ, i) (θ, j) * E.v (γ, i) (θ, j))).mul
                      (hx (θ, j))).div (hDlim (γ, i)) (heps _).ne'
                convert hlim using 1
                · funext n; rfl
                congr 1
                refine Finset.sum_congr rfl (fun θ _ => ?_)
                rw [hT, Finset.sum_mul]
                refine Finset.sum_congr rfl (fun γ _ => ?_)
                simp only [hE, Model.expt]
                ring
              have hT0 : ∀ M' : Model Γ Θ, ∀ p, T M' 1 0 p = 0 := by
                intro M' p; rw [hT]; simp [Model.expt]
              have hT1 : ∀ M' : Model Γ Θ, ∀ p, T M' 0 1 p = 0 := by
                intro M' p; rw [hT]; simp [Model.expt]
              have hTpos : ∀ M' : Model Γ Θ, M'.Standing → ∀ aC, 0 < aC → ∀ p, 0 < T M' aC 1 p := by
                intro M' hM' aC haC p
                rw [hT]
                refine Finset.sum_pos (fun γ _ => ?_) ⟨γ0, Finset.mem_univ _⟩
                simp only [Model.expt, if_true, true_and]
                split_ifs
                · exact div_pos (mul_pos (mul_pos (mul_pos haC (hM'.phi_pos γ)) (hM'.alphat_pos _ _)) (hM'.vt_pos _ _)) (hM'.eps_pos γ)
                · exact div_pos (mul_pos (mul_pos (mul_pos haC (hM'.phi_pos γ)) (hM'.alpha_pos _ _)) (hM'.v_pos _ _)) (hM'.eps_pos γ)
              have hT0pos : ∀ M' : Model Γ Θ, M'.Standing → ∀ aC, aC < 1 → ∀ p, 0 < T M' aC 0 p := by
                intro M' hM' aC haC p
                rw [hT]
                refine Finset.sum_pos (fun γ _ => ?_) ⟨γ0, Finset.mem_univ _⟩
                simp only [Model.expt]
                simp
                exact div_pos (mul_pos (mul_pos (mul_pos (by linarith) (hM'.phi_pos γ)) (hM'.alpha_pos _ _)) (hM'.v_pos _ _)) (hM'.eps_pos γ)
              have C1 : ∀ M' : Model Γ Θ, M'.Standing →
                  ∀ (lam tau : ℕ → ℝ), (∀ n, 0 < lam n) → (∀ n, 0 < tau n) →
                  Tendsto (fun n => lam n / tau n) atTop atTop →
                  ∀ (sGT sGC : ℕ → Θ × Fin 2 → ℝ),
                    (∀ n, (M'.expt 1 1).IsSteady (lam n) (tau n) (sGT n)) →
                    (∀ n, (M'.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) →
                  Tendsto (fun n => M'.gte (lam n) (sGT n) (sGC n) / tau n) atTop (𝓝 0) := by
                intro M' hM' lam tau hlam htau hr sGT sGC hGT hGC
                have h1 := G M' hM' 1 1 zero_le_one le_rfl zero_le_one le_rfl lam tau hlam htau hr sGT hGT 1 1
                have h0 := G M' hM' 0 0 le_rfl zero_le_one le_rfl zero_le_one lam tau hlam htau hr sGC hGC 0 0
                have e1 : ∑ θ, T M' 1 1 (θ, 1) * ((M'.expt 1 1).ρ (θ, 1) * M'.sys.ν θ /
                    (T M' 1 0 (θ, 1) + T M' 1 1 (θ, 1))) = ∑ θ, M'.sys.ρ θ * M'.sys.ν θ := by
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  rw [hT0, zero_add]
                  have := (hTpos M' hM' 1 one_pos (θ, 1)).ne'
                  simp only [Model.expt, Model.rhoL, if_true, one_mul]
                  field_simp
                have e0 : ∑ θ, T M' 0 0 (θ, 0) * ((M'.expt 0 0).ρ (θ, 0) * M'.sys.ν θ /
                    (T M' 0 0 (θ, 0) + T M' 0 1 (θ, 0))) = ∑ θ, M'.sys.ρ θ * M'.sys.ν θ := by
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  rw [hT1, add_zero]
                  have := (hT0pos M' hM' 0 zero_lt_one (θ, 0)).ne'
                  simp only [Model.expt, Model.rhoL]
                  simp
                  field_simp
                rw [e1] at h1
                rw [e0] at h0
                have := h1.sub h0
                rw [sub_self] at this
                refine this.congr fun n => ?_
                simp only [Model.gte, sub_div]
              refine ⟨C1 M hM, ?_, ?_⟩
              · intro aL haL haL1 lam tau hlam htau hr s hs
                have h1 := G M hM 1 aL zero_le_one le_rfl haL.le haL1.le lam tau hlam htau hr s hs 1 1
                have h0 := G M hM 1 aL zero_le_one le_rfl haL.le haL1.le lam tau hlam htau hr s hs 1 0
                have e1 : ∑ θ, T M 1 1 (θ, 1) * ((M.expt 1 aL).ρ (θ, 1) * M.sys.ν θ /
                    (T M 1 0 (θ, 1) + T M 1 1 (θ, 1))) = aL * ∑ θ, M.sys.ρ θ * M.sys.ν θ := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  rw [hT0, zero_add]
                  have := (hTpos M hM 1 one_pos (θ, 1)).ne'
                  simp only [Model.expt, Model.rhoL, if_true]
                  field_simp
                have e0 : ∑ θ, T M 1 1 (θ, 0) * ((M.expt 1 aL).ρ (θ, 0) * M.sys.ν θ /
                    (T M 1 0 (θ, 0) + T M 1 1 (θ, 0))) = (1 - aL) * ∑ θ, M.sys.ρ θ * M.sys.ν θ := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  rw [hT0, zero_add]
                  have := (hTpos M hM 1 one_pos (θ, 0)).ne'
                  simp only [Model.expt, Model.rhoL]
                  simp
                  field_simp
                rw [e1] at h1
                rw [e0] at h0
                have := (h1.div_const aL).sub (h0.div_const (1 - aL))
                have hne : (1 - aL) ≠ 0 := by linarith
                have hval : (aL * ∑ θ, M.sys.ρ θ * M.sys.ν θ) / aL
                    - ((1 - aL) * ∑ θ, M.sys.ρ θ * M.sys.ν θ) / (1 - aL) = 0 := by
                  field_simp; ring
                rw [hval] at this
                refine this.congr fun n => ?_
                simp only [Model.lrEst]
                ring
              · intro aC haC haC1
                have hw_st : ∀ w : Γ → Θ → ℝ, (∀ γ θ, 0 < w γ θ) → (M.withVt w).Standing := fun w hw =>
                  ⟨hM.rho_pos, hM.rho_sum, hM.phi_pos, hM.phi_sum, hM.alpha_pos, hM.alpha_le_one,
                    hM.alphat_pos, hM.alphat_le_one, hM.v_pos, hw, hM.eps_pos, hM.nu_pos⟩
                obtain ⟨a, ha⟩ : ∃ a : Θ → ℝ, a = fun θ => T M aC 0 (θ, 1) := ⟨_, rfl⟩
                have hapos : ∀ θ, 0 < a θ := fun θ => by rw [ha]; exact hT0pos M hM aC haC1 _
                obtain ⟨b, hb⟩ : ∃ b : (Γ → Θ → ℝ) → Θ → ℝ,
                    b = fun w θ => ∑ γ, aC * M.sys.φ γ * M.αt γ θ * w γ θ / M.sys.eps γ := ⟨_, rfl⟩
                have hTa : ∀ w θ, T (M.withVt w) aC 0 (θ, 1) = a θ := by
                  intro w θ; rw [ha, hT]; dsimp only; rw [hT]; rfl
                have hTb : ∀ w θ, T (M.withVt w) aC 1 (θ, 1) = b w θ := by
                  intro w θ; rw [hb, hT]
                  refine Finset.sum_congr rfl fun γ _ => ?_
                  simp only [Model.expt, Model.withVt, if_true, and_self]
                have hbpos : ∀ w, (∀ γ θ, 0 < w γ θ) → ∀ θ, 0 < b w θ := by
                  intro w hw θ
                  rw [← hTb]; exact hTpos _ (hw_st w hw) aC haC _
                obtain ⟨Ln, hLn⟩ : ∃ Ln : (Γ → Θ → ℝ) → ℝ, Ln = fun w => ∑ θ, M.sys.ρ θ * M.sys.ν θ *
                    (1 / aC - a θ / (aC * (1 - aC) * (a θ + b w θ))) := ⟨_, rfl⟩
                have hnull : ∀ᵐ w ∂(volume : Measure (Γ → Θ → ℝ)), (∀ γ θ, 0 < w γ θ) → Ln w ≠ 0 := by
                  obtain ⟨θ0⟩ : Nonempty Θ := by
                    by_contra h
                    rw [not_nonempty_iff] at h
                    have := hM.rho_sum
                    simp at this
                  have hK : 0 < aC * (1 - aC) := mul_pos haC (by linarith)
                  have mono : ∀ w : Γ → Θ → ℝ, (∀ γ θ, 0 < w γ θ) → ∀ t : ℝ, 0 < t →
                      Ln w < Ln (w + fun _ _ => t) := by
                    intro w hw t ht
                    simp only [hLn]
                    refine Finset.sum_lt_sum_of_nonempty ⟨θ0, Finset.mem_univ _⟩ fun θ _ => ?_
                    have hb' : b w θ < b (w + fun _ _ => t) θ := by
                      simp only [hb, Pi.add_apply]
                      refine Finset.sum_lt_sum_of_nonempty ⟨γ0, Finset.mem_univ _⟩ fun γ _ => ?_
                      have h1 := hM.phi_pos γ
                      have h2 := hM.alphat_pos γ θ
                      have h3 := hM.eps_pos γ
                      gcongr
                      linarith
                    have hbw := hbpos w hw θ
                    apply mul_lt_mul_of_pos_left _ (mul_pos (hM.rho_pos θ) (hM.nu_pos θ))
                    apply sub_lt_sub_left
                    apply div_lt_div_of_pos_left (hapos θ) (mul_pos hK (by linarith [hapos θ]))
                    exact mul_lt_mul_of_pos_left (by linarith) hK
                  have hLnm : Measurable Ln := by
                    rw [hLn, hb]; fun_prop
                  obtain ⟨P, hP⟩ : ∃ P : Set (Γ → Θ → ℝ), P = {w | ∀ γ θ, 0 < w γ θ} := ⟨_, rfl⟩
                  have hPm : MeasurableSet P := by
                    rw [hP]; simp only [Set.setOf_forall]
                    exact MeasurableSet.iInter fun γ => MeasurableSet.iInter fun θ =>
                      measurableSet_lt measurable_const (by fun_prop)
                  have hBm : ∀ N : ℕ, MeasurableSet {w : Γ → Θ → ℝ | ∀ γ θ, w γ θ ≤ N} := by
                    intro N; simp only [Set.setOf_forall]
                    exact MeasurableSet.iInter fun γ => MeasurableSet.iInter fun θ =>
                      measurableSet_le (by fun_prop) measurable_const
                  have hZN : ∀ N : ℕ, volume (P ∩ {w | Ln w = 0} ∩ {w : Γ → Θ → ℝ | ∀ γ θ, w γ θ ≤ N}) = 0 := by
                    intro N
                    set ZN := P ∩ {w | Ln w = 0} ∩ {w : Γ → Θ → ℝ | ∀ γ θ, w γ θ ≤ N} with hZNdef
                    have hZNm : MeasurableSet ZN :=
                      (hPm.inter (measurableSet_eq_fun hLnm measurable_const)).inter (hBm N)
                    set S : ℕ → Set (Γ → Θ → ℝ) := fun k => (fun w => w + fun _ _ => -(1 / ((k : ℝ) + 1))) ⁻¹' ZN
                      with hSdef
                    have hSm : ∀ k, MeasurableSet (S k) := fun k => hZNm.preimage (measurable_add_const _)
                    have hSv : ∀ k, volume (S k) = volume ZN := fun k => measure_preimage_add_right _ _ _
                    have hdisj0 : ∀ k m : ℕ, k < m → Disjoint (S k) (S m) := by
                      intro k m hkm
                      rw [Set.disjoint_left]
                      intro w hk hm
                      simp only [hSdef, hZNdef, hP, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq] at hk hm
                      have hlt : 1 / ((m : ℝ) + 1) < 1 / ((k : ℝ) + 1) := by
                        apply one_div_lt_one_div_of_lt (by positivity)
                        exact_mod_cast Nat.add_lt_add_right hkm 1
                      have := mono _ hk.1.1 (1 / ((k : ℝ) + 1) - 1 / ((m : ℝ) + 1)) (by linarith)
                      have heq : ((w + fun _ _ => -(1 / ((k : ℝ) + 1))) + fun _ _ => 1 / ((k : ℝ) + 1) - 1 / ((m : ℝ) + 1))
                          = w + fun _ _ => -(1 / ((m : ℝ) + 1)) := by
                        funext γ θ; simp only [Pi.add_apply]; ring
                      rw [heq, hk.1.2, hm.1.2] at this
                      exact lt_irrefl _ this
                    have hdisj : Pairwise (Function.onFun Disjoint S) := by
                      intro k m hkm
                      rcases lt_or_gt_of_ne hkm with h | h
                      · exact hdisj0 k m h
                      · exact (hdisj0 m k h).symm
                    have hsub : (⋃ k, S k) ⊆ Set.Icc (fun _ _ => (0 : ℝ)) (fun _ _ => (N : ℝ) + 1) := by
                      intro w hw
                      rw [Set.mem_iUnion] at hw
                      obtain ⟨k, hk⟩ := hw
                      simp only [hSdef, hZNdef, hP, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
                        Pi.add_apply] at hk
                      have h1 : 0 < 1 / ((k : ℝ) + 1) := by positivity
                      have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
                        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
                      constructor
                      · intro γ θ; have := hk.1.1 γ θ; simp only; linarith
                      · intro γ θ; have := hk.2 γ θ; simp only; linarith
                    have hfin : volume (Set.Icc (fun _ _ => (0 : ℝ)) (fun (_ : Γ) (_ : Θ) => (N : ℝ) + 1)) < ⊤ :=
                      isCompact_Icc.measure_lt_top
                    by_contra hne
                    have h1 : volume (⋃ k, S k) = ⊤ := by
                      rw [measure_iUnion hdisj hSm]
                      simp only [hSv]
                      exact ENNReal.tsum_const_eq_top_of_ne_zero hne
                    have h2 := measure_mono (μ := volume) hsub
                    rw [h1] at h2
                    exact absurd (lt_of_le_of_lt h2 hfin) (lt_irrefl _)
                  rw [ae_iff]
                  refine measure_mono_null ?_ (measure_iUnion_null hZN)
                  intro w hw
                  simp only [Set.mem_setOf_eq, _root_.not_imp, not_not] at hw
                  rw [Set.mem_iUnion]
                  obtain ⟨N, hN⟩ := exists_nat_ge ‖w‖
                  refine ⟨N, ⟨?_, hw.2⟩, ?_⟩
                  · rw [hP]; exact hw.1
                  · intro γ θ
                    have := (norm_le_pi_norm (w γ) θ).trans (norm_le_pi_norm w γ)
                    rw [Real.norm_eq_abs] at this
                    linarith [le_abs_self (w γ θ)]
                filter_upwards [hnull] with w hw hwpos
                refine ⟨Ln w, hw hwpos, ?_⟩
                intro lam tau hlam htau hr sCR sGT sGC hCR hGT hGC
                have hst := hw_st w hwpos
                have hg := C1 _ hst lam tau hlam htau hr sGT sGC hGT hGC
                have h11 := G _ hst aC 1 haC.le haC1.le zero_le_one le_rfl lam tau hlam htau hr sCR hCR 1 1
                have h01 := G _ hst aC 1 haC.le haC1.le zero_le_one le_rfl lam tau hlam htau hr sCR hCR 0 1
                have hcr := ((h11.div_const aC).sub (h01.div_const (1 - aC))).sub hg
                rw [sub_zero] at hcr
                convert hcr using 1
                · funext n; simp only [Model.crEst]; ring
                · congr 1
                  rw [hLn, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun θ _ => ?_
                  rw [hTa, hTb]
                  have h1 := hapos θ
                  have h2 := hbpos w hwpos θ
                  have h3 : 1 - aC ≠ 0 := by linarith
                  have h4 : a θ + b w θ ≠ 0 := by linarith
                  have h5 := haC.ne'
                  simp only [Model.expt, Model.rhoL, Model.withVt, if_true, one_mul]
                  field_simp
                  ring
