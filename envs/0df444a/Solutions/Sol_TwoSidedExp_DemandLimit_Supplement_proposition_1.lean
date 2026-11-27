-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.Supplement.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:11.489852+00:00
-- url     : https://prove2.me/submissions/0f1f0cc8-b21e-498b-a11a-7f1be666d2d7

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics

open Filter Topology MeasureTheory

open TwoSidedExp
open TwoSidedExp.DemandLimit
open TwoSidedExp.DemandLimit.Supplement

/-- Proposition 1, p. 11: existence and uniqueness on nonnegative times. -/
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) (s₀ : Θ → ℝ) (hs₀ : M.sys.InS s₀) :
    ∃ s : ℝ → Θ → ℝ, Trajectory M.sys lam tau s ∧ s 0 = s₀ ∧
      ∀ z : ℝ → Θ → ℝ, Trajectory M.sys lam tau z → z 0 = s₀ →
        ∀ t, 0 ≤ t → z t = s t := by
          classical
          let B : Set (Θ → ℝ) := Set.Icc 0 M.sys.ρ
          have hB (x : Θ → ℝ) : x ∈ B ↔ M.sys.InS x := by
            simp only [B, Set.mem_Icc, Pi.le_def, Pi.zero_apply, MFSystem.InS]
            exact ⟨fun h θ => ⟨h.1 θ, h.2 θ⟩, fun h => ⟨fun θ => (h θ).1, fun θ => (h θ).2⟩⟩
          have hden (x : Θ → ℝ) (hx : x ∈ B) (γ : Γ) :
              0 < M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * x θ := by
            exact add_pos_of_pos_of_nonneg (hM.eps_pos γ) (Finset.sum_nonneg fun θ _ =>
              mul_nonneg (mul_nonneg (hM.alpha_pos γ θ).le (hM.v_pos γ θ).le) ((hB x).mp hx θ).1)
          have hdiff : ContDiffOn ℝ 1 (drift M.sys lam tau) B := by
            apply contDiffOn_pi.mpr
            intro θ
            apply ContDiffOn.sub
            · exact ((contDiffOn_const.sub (contDiff_apply ℝ ℝ θ).contDiffOn).mul contDiffOn_const)
            · apply ContDiffOn.mul contDiffOn_const
              apply ContDiffOn.sum
              intro γ _
              apply ContDiffOn.mul contDiffOn_const
              apply ContDiffOn.div
              · exact contDiffOn_const.mul (contDiff_apply ℝ ℝ θ).contDiffOn
              · apply ContDiffOn.add contDiffOn_const
                apply ContDiffOn.sum
                intro i _
                exact contDiffOn_const.mul (contDiff_apply ℝ ℝ i).contDiffOn
              · intro x hx
                exact ne_of_gt (hden x hx γ)
          obtain ⟨K, hK⟩ := hdiff.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
          let P : (Θ → ℝ) → Θ → ℝ := fun x θ => max 0 (min (M.sys.ρ θ) (x θ))
          have hP (x : Θ → ℝ) : P x ∈ B := by
            apply (hB _).mpr
            intro θ
            exact ⟨le_max_left _ _, max_le (hM.rho_pos θ).le (min_le_left _ _)⟩
          have hPeq (x : Θ → ℝ) (hx : x ∈ B) : P x = x := by
            ext θ
            simp only [P, min_eq_right ((hB x).mp hx θ).2, max_eq_right ((hB x).mp hx θ).1]
          have hPlip : LipschitzWith 1 P := by
            apply LipschitzWith.of_dist_le_mul
            intro x y
            apply (dist_pi_le_iff (by positivity : 0 ≤ (1 : ℝ) * dist x y)).mpr
            intro θ
            exact (((LipschitzWith.eval θ).const_min (M.sys.ρ θ)).const_max 0).dist_le_mul x y
          let F := fun x => drift M.sys lam tau (P x)
          have hFlip : LipschitzWith K F := by
            apply LipschitzWith.of_dist_le_mul
            intro x y
            exact (hK.dist_le_mul (P x) (hP x) (P y) (hP y)).trans
              (mul_le_mul_of_nonneg_left (by simpa using hPlip.dist_le_mul x y) K.coe_nonneg)
          obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hdiff.continuousOn
          let L : NNReal := ⟨max C 0, le_max_right _ _⟩
          have hFbound (x : Θ → ℝ) : ‖F x‖ ≤ L := (hC _ (hP x)).trans (le_max_left _ _)
          have hFeq (x : Θ → ℝ) (hx : x ∈ B) : F x = drift M.sys lam tau x := by
            dsimp [F]
            rw [hPeq x hx]
          have hlower (x : Θ → ℝ) (θ : Θ) (hx : x θ ≤ 0) : 0 ≤ F x θ := by
            have hp : P x θ = 0 := max_eq_left ((min_le_right _ _).trans hx)
            simp only [F, drift, MFSystem.choice, hp, mul_zero, zero_div,
              Finset.sum_const_zero, sub_zero]
            exact mul_nonneg (hM.rho_pos θ).le (mul_nonneg htau.le (hM.nu_pos θ).le)
          have hupper (x : Θ → ℝ) (θ : Θ) (hx : M.sys.ρ θ ≤ x θ) : F x θ ≤ 0 := by
            have hp : P x θ = M.sys.ρ θ := by
              simp only [P, min_eq_left hx, max_eq_right (hM.rho_pos θ).le]
            have hc (γ : Γ) : 0 ≤ M.sys.φ γ * M.sys.choice γ θ (P x) := by
              apply mul_nonneg (hM.phi_pos γ).le
              exact div_nonneg (mul_nonneg (mul_nonneg (hM.alpha_pos γ θ).le
                (hM.v_pos γ θ).le) ((hB _).mp (hP x) θ).1) (hden _ (hP x) γ).le
            dsimp [F, drift]
            rw [hp, sub_self, zero_mul, zero_sub]
            exact neg_nonpos.mpr (mul_nonneg hlam.le (Finset.sum_nonneg fun γ _ => hc γ))
          have hex (T : ℝ) : ∃ a : ℝ → Θ → ℝ, a 0 = s₀ ∧
              ∀ t ∈ Set.Icc 0 (max T 1), HasDerivWithinAt a (F (a t)) (Set.Icc 0 (max T 1)) t := by
            let R : NNReal := ⟨max T 1, le_trans zero_le_one (le_max_right _ _)⟩
            have hpl : IsPicardLindelof (fun (_ : ℝ) => F)
                (⟨0, by constructor <;> simp [le_trans zero_le_one (le_max_right T 1)]⟩ :
                  Set.Icc 0 (max T 1)) s₀ (L * R) 0 L K := by
              constructor
              · intro t ht
                exact hFlip.lipschitzOnWith
              · intro x hx
                exact continuousOn_const
              · intro t ht x hx
                exact hFbound x
              · change (L : ℝ) * max (max T 1 - 0) (0 - 0) ≤ (L : ℝ) * max T 1 - 0
                rw [sub_zero, sub_self, max_eq_left (le_trans zero_le_one (le_max_right T 1)), sub_zero]
            exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
          choose a ha0 ha using hex
          have had (T t : ℝ) (ht : 0 ≤ t) (htT : t < max T 1) :
              HasDerivWithinAt (a T) (F (a T t)) (Set.Ici 0) t := by
            exact (ha T t ⟨ht, htT.le⟩).mono_of_mem_nhdsWithin
              (by
                filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds htT)] with u hu hu'
                exact ⟨hu, hu'.le⟩)
          have hac (T : ℝ) : ContinuousOn (a T) (Set.Icc 0 (max T 1)) := by
            exact fun t ht => (ha T t ht).continuousWithinAt
          have haunique (T U t : ℝ) (ht : 0 ≤ t) (hT : t ≤ max T 1) (hU : t ≤ max U 1) :
              a T t = a U t := by
            apply ODE_solution_unique (fun _ => hFlip)
              ((hac T).mono (Set.Icc_subset_Icc le_rfl hT))
              (fun u hu => (had T u hu.1 (hu.2.trans_le hT)).mono
                (Set.Ici_subset_Ici.mpr hu.1))
              ((hac U).mono (Set.Icc_subset_Icc le_rfl hU))
              (fun u hu => (had U u hu.1 (hu.2.trans_le hU)).mono
                (Set.Ici_subset_Ici.mpr hu.1))
              (by rw [ha0, ha0]) ⟨ht, le_rfl⟩
          let s : ℝ → Θ → ℝ := fun t => a (t + 1) t
          have hs0 : s 0 = s₀ := by simp only [s, ha0]
          have hsd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt s (F (s t)) (Set.Ici 0) t := by
            have hR : max (t + 1) 1 = t + 1 := max_eq_left (by linarith)
            apply (had (t + 1) t ht (by rw [hR]; linarith)).congr_of_eventuallyEq
            · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds (show t < t + 1 by linarith))] with u hu hu'
              exact haunique (u + 1) (t + 1) u hu
                (le_trans (by linarith) (le_max_left _ _)) (by rw [hR]; exact hu'.le)
            · rfl
          have fence (f f' : ℝ → ℝ) (c : ℝ)
              (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Set.Ici 0) t)
              (hf0 : f 0 ≤ c) (hb : ∀ t, 0 ≤ t → c < f t → f' t ≤ 0)
              (t : ℝ) (ht : 0 ≤ t) : f t ≤ c := by
            apply le_of_forall_pos_le_add
            intro ε hε
            let e := ε / (t + 1)
            have htp : 0 < t + 1 := by linarith
            have he : 0 < e := div_pos hε htp
            have hbar : ∀ u, HasDerivAt (fun u : ℝ => c + e * (u + 1)) e u := by
              intro u
              convert! (((hasDerivAt_id u).add_const 1).const_mul e).const_add c using 1; ring
            have hbound := image_le_of_deriv_right_lt_deriv_boundary
              (f := f) (f' := f') (a := 0) (b := t)
              (fun u hu => (hf u hu.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
              (fun u hu => (hf u hu.1).mono (Set.Ici_subset_Ici.mpr hu.1))
              (B := fun u => c + e * (u + 1)) (B' := fun _ => e)
              (by simp only [zero_add, mul_one]; linarith) hbar
              (fun u hu heq => lt_of_le_of_lt (hb u hu.1 (by
                have := mul_pos he (show 0 < u + 1 by linarith [hu.1])
                linarith)) he) (x := t) ⟨ht, le_rfl⟩
            simpa only [e, div_mul_cancel₀ ε (ne_of_gt htp)] using hbound
          have hsB (t : ℝ) (ht : 0 ≤ t) : s t ∈ B := by
            apply (hB _).mpr
            intro θ
            have hcoord (u : ℝ) (hu : 0 ≤ u) := (hasDerivWithinAt_pi.mp (hsd u hu)) θ
            constructor
            · have hn := fence (fun u => -s u θ) (fun u => -F (s u) θ) 0
                (fun u hu => (hcoord u hu).neg)
                (by rw [hs0]; exact neg_nonpos.mpr (hs₀ θ).1)
                (fun u hu hneg => neg_nonpos.mpr (hlower (s u) θ (by linarith))) t ht
              linarith
            · exact fence (fun u => s u θ) (fun u => F (s u) θ) (M.sys.ρ θ)
                hcoord (by rw [hs0]; exact (hs₀ θ).2)
                (fun u hu hgt => hupper (s u) θ hgt.le) t ht
          have hstraj : Trajectory M.sys lam tau s := by
            refine ⟨fun t ht => (hB _).mp (hsB t ht), fun θ t ht => ?_⟩
            rw [← hFeq _ (hsB t ht)]
            exact hasDerivWithinAt_pi.mp (hsd t ht) θ
          refine ⟨s, hstraj, hs0, ?_⟩
          intro z hz hz0 t ht
          have hzd (u : ℝ) (hu : 0 ≤ u) : HasDerivWithinAt z (F (z u)) (Set.Ici 0) u := by
            rw [hFeq _ ((hB _).mpr (hz.1 u hu))]
            exact hasDerivWithinAt_pi.mpr (fun θ => hz.2 θ u hu)
          exact ODE_solution_unique (fun _ => hFlip)
            (fun u hu => (hzd u hu.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
            (fun u hu => (hzd u hu.1).mono (Set.Ici_subset_Ici.mpr hu.1))
            (fun u hu => (hsd u hu.1).continuousWithinAt.mono Set.Icc_subset_Ici_self)
            (fun u hu => (hsd u hu.1).mono (Set.Ici_subset_Ici.mpr hu.1))
            (hz0.trans hs0.symm) ⟨ht, le_rfl⟩
