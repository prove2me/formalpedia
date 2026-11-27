-- Prove2me | solution 1 for StochApproxDyn.WeakAPT.Supplement.tubeDist_expansion
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:18.84714+00:00
-- url     : https://prove2.me/submissions/9b52dd94-5f98-4c91-873e-3f1a7f554bc7

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_Supplement_NormallyRepelling

open Filter
open scoped NNReal Topology

open StochApproxDyn
open StochApproxDyn.WeakAPT
open StochApproxDyn.WeakAPT.Supplement

/-- Lemma 9.3 (Benaïm 1999, p. 51). In the setting of §9, with `F` and `S` of class `C^r`
(`r ≥ 1`), let `T, N, E^u, Ẽ^u, ε, N₀, Π` be chosen as in the construction of §9.1, step 1
(pp. 50–51), `f = Φ_T` and `V(x) = ‖x − Π(x)‖`. There exist a neighbourhood `N₁ ⊆ N₀` of `Γ` and
`ρ > 1` such that for all `x ∈ N₁`, `V(f(x)) ≥ ρ V(x)` (in particular `f(x) ∈ N₀`, where `V` is
defined). Here `Pr` is the projection `Π`. -/
theorem solution {m d : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hF : ContDiff ℝ (r : WithTop ℕ∞) F)
    (Φ : Flow ℝ (EuclideanSpace ℝ (Fin m))) (S Γ U : Set (EuclideanSpace ℝ (Fin m))) (t₀ : ℝ)
    (hS : IsSubmanifoldOfClass r d S)
    (Eu : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (hNR : IsNormallyRepellingSet d F Φ S Γ U t₀ Eu) (T : ℝ) (N : Set (EuclideanSpace ℝ (Fin m)))
    (Eext Et : EuclideanSpace ℝ (Fin m) → Submodule ℝ (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (N₀ : Set (EuclideanSpace ℝ (Fin m)))
    (Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hC : IsTubularConstruction d Φ S Γ U Eu T N Eext Et ε N₀ Pr) :
    ∃ N₁ ∈ 𝓝ˢ Γ, N₁ ⊆ N₀ ∧ ∃ ρ : ℝ, 1 < ρ ∧ ∀ x ∈ N₁,
      Φ T x ∈ N₀ ∧ ρ * tubeDist Pr x ≤ tubeDist Pr (Φ T x) := by
        classical
        obtain ⟨hflow, hd1, hdm, hΓne, hΓc, hΓS, hΓinv, hUn, ht₀, hloc, hsplit, hEuc, hEuinv, -⟩ := hNR
        obtain ⟨⟨hT, h5⟩, ⟨hNc, hNn, hNU, hfNU⟩, ⟨-, -, hExt, -⟩, ⟨hEtd, hEts⟩, ⟨hε, hε1, -⟩, h6,
          hN₀o, hSN₀, hN₀N, hPrc, hPrx, hPrS, -⟩ := hC
        have hr1 : (1 : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
        have hF1 : ContDiff ℝ 1 F := hF.of_le hr1
        have hFc : Continuous (fderiv ℝ F) := hF1.continuous_fderiv (by norm_num)
        have hcontΦ : Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin m) => Φ z.1 z.2) := Φ.cont'
        have hΓm : ∀ t : ℝ, ∀ p ∈ Γ, Φ t p ∈ Γ := fun t p hp => by
          rw [← hΓinv t]; exact Set.mem_image_of_mem _ hp
        -- strict differentiability of the time-T map
        have hstrict : ∀ p : EuclideanSpace ℝ (Fin m), DifferentiableAt ℝ (Φ T) p →
            HasStrictFDerivAt (Φ T) (fderiv ℝ (Φ T) p) p := by
          intro p hp
          have horb : Continuous (fun s : ℝ => Φ s p) := hcontΦ.comp (by fun_prop : Continuous (fun s : ℝ => (s, p)))
          have hAc : Continuous (fun s : ℝ => fderiv ℝ F (Φ s p)) := hFc.comp horb
          obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hAc.continuousOn
          obtain ⟨K, hK1, hK⟩ : ∃ K : ℝ≥0, (1:ℝ) ≤ K ∧ ∀ s ∈ Set.Icc 0 T, ‖fderiv ℝ F (Φ s p)‖ ≤ K := by
            refine ⟨(max 1 K0).toNNReal, ?_, ?_⟩
            · rw [Real.coe_toNNReal _ (by positivity)]; exact le_max_left _ _
            · intro s hs
              rw [Real.coe_toNNReal _ (by positivity)]; exact (hK0 s hs).trans (le_max_right _ _)
          have hunif : ∀ η : ℝ, 0 < η → ∀ᶠ z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 (p, p),
              ∀ s ∈ Set.Icc 0 T, ‖F (Φ s z.1) - F (Φ s z.2) - fderiv ℝ F (Φ s p) (Φ s z.1 - Φ s z.2)‖
                ≤ η * ‖Φ s z.1 - Φ s z.2‖ := by
            intro η hη
            refine (isCompact_Icc (a := (0:ℝ)) (b := T)).eventually_forall_of_forall_eventually ?_
            intro s₀ _
            have h1 : ∀ᶠ w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 (Φ s₀ p, Φ s₀ p),
                ‖F w.1 - F w.2 - fderiv ℝ F (Φ s₀ p) (w.1 - w.2)‖ ≤ η / 2 * ‖w.1 - w.2‖ := by
              have := (hF1.contDiffAt (x := Φ s₀ p)).hasStrictFDerivAt (by norm_num)
              exact (Asymptotics.isLittleO_iff.1 (hasStrictFDerivAt_iff_isLittleO.1 this)) (by positivity)
            have h2 : Tendsto (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
                (Φ q.2 q.1.1, Φ q.2 q.1.2)) (𝓝 ((p, p), s₀)) (𝓝 (Φ s₀ p, Φ s₀ p)) := by
              have : Continuous (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
                (Φ q.2 q.1.1, Φ q.2 q.1.2)) :=
                (hcontΦ.comp (by fun_prop : Continuous (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ => (q.2, q.1.1)))).prodMk
                (hcontΦ.comp (by fun_prop : Continuous (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ => (q.2, q.1.2))))
              exact this.tendsto ((p, p), s₀)
            have h3 : ∀ᶠ q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ in 𝓝 ((p, p), s₀),
                ‖fderiv ℝ F (Φ q.2 p) - fderiv ℝ F (Φ s₀ p)‖ < η / 2 := by
              have : Continuous (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
                ‖fderiv ℝ F (Φ q.2 p) - fderiv ℝ F (Φ s₀ p)‖) :=
                ((hAc.comp continuous_snd).sub continuous_const).norm
              have h := this.tendsto ((p, p), s₀)
              simp only [sub_self, norm_zero] at h
              exact h.eventually_lt_const (by positivity)
            filter_upwards [h2.eventually h1, h3] with q hq1 hq3
            have e : F (Φ q.2 q.1.1) - F (Φ q.2 q.1.2) - fderiv ℝ F (Φ q.2 p) (Φ q.2 q.1.1 - Φ q.2 q.1.2)
              = (F (Φ q.2 q.1.1) - F (Φ q.2 q.1.2) - fderiv ℝ F (Φ s₀ p) (Φ q.2 q.1.1 - Φ q.2 q.1.2))
                - (fderiv ℝ F (Φ q.2 p) - fderiv ℝ F (Φ s₀ p)) (Φ q.2 q.1.1 - Φ q.2 q.1.2) := by
              simp only [sub_apply]; abel
            rw [e]
            refine (norm_sub_le _ _).trans ?_
            have := (fderiv ℝ F (Φ q.2 p) - fderiv ℝ F (Φ s₀ p)).le_of_opNorm_le hq3.le (Φ q.2 q.1.1 - Φ q.2 q.1.2)
            linarith
          rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
          intro c hc
          set G : ℝ := Real.exp ((K + 1) * T) with hG
          have hGpos : 0 < G := Real.exp_pos _
          set H : ℝ := Real.exp (K * T) with hH
          have hHpos : 0 < H := Real.exp_pos _
          set η : ℝ := min 1 (c / (4 * G * H)) with hη
          have hηpos : 0 < η := lt_min one_pos (by positivity)
          have hη1 : η ≤ 1 := min_le_left _ _
          have hη2 : 2 * η * G * H ≤ c / 2 := by
            have : η ≤ c / (4 * G * H) := min_le_right _ _
            rw [le_div_iff₀ (by positivity)] at this
            linarith
          have hder : ∀ x y : EuclideanSpace ℝ (Fin m), ∀ s : ℝ,
              HasDerivAt (fun s => Φ s x - Φ s y) (F (Φ s x) - F (Φ s y)) s := fun x y s =>
            (hflow x s).sub (hflow y s)
          have hcts : ∀ x y : EuclideanSpace ℝ (Fin m), Continuous (fun s => Φ s x - Φ s y) := fun x y =>
            continuous_iff_continuousAt.2 fun s => (hder x y s).continuousAt
          have hgrow : ∀ x y : EuclideanSpace ℝ (Fin m),
              (∀ s ∈ Set.Icc 0 T, ‖F (Φ s x) - F (Φ s y) - fderiv ℝ F (Φ s p) (Φ s x - Φ s y)‖
                ≤ η * ‖Φ s x - Φ s y‖) → ∀ s ∈ Set.Icc 0 T, ‖Φ s x - Φ s y‖ ≤ G * ‖x - y‖ := by
            intro x y hxy s hs
            have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => Φ s x - Φ s y)
              (f' := fun s => F (Φ s x) - F (Φ s y)) (δ := ‖x - y‖) (K := K + 1) (ε := 0) (a := 0) (b := T)
              (hcts x y).continuousOn (fun s _ => (hder x y s).hasDerivWithinAt)
              (by simp [Φ.map_zero']) (by
                intro s hs
                have hs' := Set.Ico_subset_Icc_self hs
                have h1 := hxy s hs'
                have h2 := (fderiv ℝ F (Φ s p)).le_of_opNorm_le (hK s hs') (Φ s x - Φ s y)
                have h3 := norm_le_insert' (F (Φ s x) - F (Φ s y)) (fderiv ℝ F (Φ s p) (Φ s x - Φ s y))
                have h4 : η * ‖Φ s x - Φ s y‖ ≤ 1 * ‖Φ s x - Φ s y‖ := by gcongr
                linarith) s hs
            rw [gronwallBound_ε0] at this
            refine this.trans ?_
            rw [mul_comm]
            rw [hG, sub_zero]
            gcongr
            exact hs.2
          have hshift : Tendsto (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
              (p + (z.1 - z.2), p)) (𝓝 (p, p)) (𝓝 (p, p)) := by
            have : Continuous (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
              (p + (z.1 - z.2), p)) := by fun_prop
            have h := this.tendsto (p, p)
            simpa using h
          have hshift' : Tendsto (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
              (p + (z.1 - z.2))) (𝓝 (p, p)) (𝓝 p) := by
            have : Continuous (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
              (p + (z.1 - z.2))) := by fun_prop
            have h := this.tendsto (p, p)
            simpa using h
          have hdiff := (Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO.1 hp.hasFDerivAt)) (half_pos hc)
          filter_upwards [hunif η hηpos, hshift.eventually (hunif η hηpos), hshift'.eventually hdiff] with z hz1 hz2 hz3
          have g1 := hgrow _ _ hz1
          have g2 := hgrow _ _ hz2
          simp only [add_sub_cancel_left] at g2 hz3
          have key := dist_le_of_approx_trajectories_ODE (v := fun s w => if s ∈ Set.Icc 0 T then fderiv ℝ F (Φ s p) w else 0)
            (K := K) (f := fun s => Φ s z.1 - Φ s z.2) (f' := fun s => F (Φ s z.1) - F (Φ s z.2))
            (g := fun s => Φ s (p + (z.1 - z.2)) - Φ s p) (g' := fun s => F (Φ s (p + (z.1 - z.2))) - F (Φ s p))
            (a := 0) (b := T) (εf := η * (G * ‖z.1 - z.2‖)) (εg := η * (G * ‖z.1 - z.2‖)) (δ := 0)
            (by
              intro s
              by_cases hs : s ∈ Set.Icc 0 T
              · simp only [hs, if_true]
                exact (fderiv ℝ F (Φ s p)).lipschitz.weaken (by exact_mod_cast hK s hs)
              · simp only [hs, if_false]
                exact LipschitzWith.const' 0)
            (hcts _ _).continuousOn (fun s _ => (hder _ _ s).hasDerivWithinAt)
            (by
              intro s hs
              have hs' := Set.Ico_subset_Icc_self hs
              simp only [hs', if_true, dist_eq_norm]
              exact (hz1 s hs').trans (by gcongr; exact g1 s hs'))
            (hcts _ _).continuousOn (fun s _ => (hder _ _ s).hasDerivWithinAt)
            (by
              intro s hs
              have hs' := Set.Ico_subset_Icc_self hs
              simp only [hs', if_true, dist_eq_norm]
              exact (hz2 s hs').trans (by gcongr; exact g2 s hs'))
            (by simp [Φ.map_zero']) T ⟨hT.le, le_rfl⟩
          rw [gronwallBound_of_K_ne_0 (by positivity), dist_eq_norm] at key
          simp only [sub_zero, zero_mul, zero_add] at key
          have hb : (η * (G * ‖z.1 - z.2‖) + η * (G * ‖z.1 - z.2‖)) / K * (Real.exp (K * T) - 1) ≤ c / 2 * ‖z.1 - z.2‖ := by
            have h1 : (η * (G * ‖z.1 - z.2‖) + η * (G * ‖z.1 - z.2‖)) / K ≤ (η * (G * ‖z.1 - z.2‖) + η * (G * ‖z.1 - z.2‖)) :=
              div_le_self (by positivity) hK1
            calc _ ≤ (η * (G * ‖z.1 - z.2‖) + η * (G * ‖z.1 - z.2‖)) * H := by
                    apply mul_le_mul h1 (by linarith) _ (by positivity)
                    have : 1 ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
                    linarith
              _ = (2 * η * G * H) * ‖z.1 - z.2‖ := by ring
              _ ≤ _ := by gcongr
          have e : Φ T z.1 - Φ T z.2 - fderiv ℝ (Φ T) p (z.1 - z.2) =
            (Φ T z.1 - Φ T z.2 - (Φ T (p + (z.1 - z.2)) - Φ T p)) +
             (Φ T (p + (z.1 - z.2)) - Φ T p - fderiv ℝ (Φ T) p (z.1 - z.2)) := by abel
          rw [e]
          refine (norm_add_le _ _).trans ?_
          linarith
        -- local invariance of S near Γ
        have hSinv : ∀ p ∈ Γ, ∀ᶠ q in 𝓝 p, q ∈ S → Φ T q ∈ S := by
          intro p hp
          have hU : ∀ᶠ q in 𝓝 p, ∀ s ∈ Set.Icc 0 T, Φ s q ∈ U := by
            refine (isCompact_Icc (a := (0:ℝ)) (b := T)).eventually_forall_of_forall_eventually ?_
            intro s _
            have : Tendsto (fun q : EuclideanSpace ℝ (Fin m) × ℝ => Φ q.2 q.1) (𝓝 (p, s)) (𝓝 (Φ s p)) :=
              (hcontΦ.comp continuous_swap).tendsto (p, s)
            exact this.eventually (mem_nhdsSet_iff_forall.1 hUn _ (hΓm s p hp))
          obtain ⟨n, hn⟩ := exists_nat_gt (T / t₀)
          have hn0 : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn
          filter_upwards [hU] with q hq hqS
          have hstep : ∀ k : ℕ, k ≤ n → Φ (k * (T / n)) q ∈ S := by
            intro k
            induction k with
            | zero => intro _; simpa [Φ.map_zero'] using hqS
            | succ k ih =>
              intro hk
              have h1 := ih (by omega)
              have h2 : Φ (k * (T / n)) q ∈ U := by
                refine hq _ ⟨by positivity, ?_⟩
                have : (k:ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
                calc (k:ℝ) * (T / n) ≤ n * (T / n) := by gcongr
                  _ = T := by field_simp
              have h3 : ((k + 1 : ℕ) : ℝ) * (T / n) = T / n + k * (T / n) := by push_cast; ring
              rw [h3, Φ.map_add']
              refine hloc (T / n) ?_ ⟨_, ⟨h2, h1⟩, rfl⟩
              rw [abs_of_pos (by positivity), div_le_iff₀ hn0]
              rw [div_lt_iff₀ ht₀] at hn
              linarith
          have := hstep n le_rfl
          rwa [show (n:ℝ) * (T / n) = T by field_simp] at this
        -- secants of S are asymptotically tangent
        have hTan : ∀ p ∈ S, ∀ R : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
            (∀ t ∈ tangentSubspace S p, R t = 0) →
            (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => R (z.1 - z.2))
              =o[𝓝 (p, p) ⊓ 𝓟 (S ×ˢ S)] (fun z => z.1 - z.2) := by
          intro p hp R hR
          obtain ⟨φ, hpφ, hslice, hφ, hψ⟩ := hS.2 p hp
          have hφs : HasStrictFDerivAt φ (fderiv ℝ φ p) p :=
            ((hφ.contDiffAt (φ.open_source.mem_nhds hpφ)).of_le hr1).hasStrictFDerivAt (by norm_num)
          have hψs : HasStrictFDerivAt φ.symm (fderiv ℝ φ.symm (φ p)) (φ p) :=
            ((hψ.contDiffAt (φ.open_target.mem_nhds (φ.map_source hpφ))).of_le hr1).hasStrictFDerivAt (by norm_num)
          have hzero : ∀ a ∈ S ∩ φ.source, ∀ i : Fin m, m - d ≤ i.val → φ a i = 0 := by
            intro a ha
            rw [hslice] at ha
            exact ha.2
          have hBt : ∀ u : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, m - d ≤ i.val → u i = 0) →
              fderiv ℝ φ.symm (φ p) u ∈ tangentSubspace S p := by
            intro u hu
            refine Submodule.subset_span ⟨fun s => φ.symm (φ p + s • u), by simp [φ.left_inv hpφ], ?_, ?_⟩
            · have ht : Tendsto (fun s : ℝ => φ p + s • u) (𝓝 0) (𝓝 (φ p)) := by
                have : Continuous (fun s : ℝ => φ p + s • u) := by fun_prop
                simpa using this.tendsto 0
              filter_upwards [ht.eventually (φ.open_target.mem_nhds (φ.map_source hpφ))] with s hs
              have : φ.symm (φ p + s • u) ∈ {x ∈ φ.source | ∀ i : Fin m, m - d ≤ i.val → φ x i = 0} := by
                refine ⟨φ.map_target hs, fun i hi => ?_⟩
                rw [φ.right_inv hs]
                simp [hu i hi, hzero p ⟨hp, hpφ⟩ i hi]
              rw [← hslice] at this
              exact this.1
            · have h1 : HasDerivAt (fun s : ℝ => φ p + s • u) u 0 := by
                simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add (φ p)
              have h2 : HasFDerivAt φ.symm (fderiv ℝ φ.symm (φ p)) (φ p + (0:ℝ) • u) := by
                simpa using hψs.hasFDerivAt
              exact h2.comp_hasDerivAt (0:ℝ) h1
          have hcφ : Tendsto (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => (φ z.1, φ z.2))
              (𝓝 (p, p)) (𝓝 (φ p, φ p)) := by
            have hc : ContinuousAt φ p := φ.continuousAt hpφ
            exact (hc.tendsto.comp (continuous_fst.tendsto (p, p))).prodMk_nhds (hc.tendsto.comp (continuous_snd.tendsto (p, p)))
          have h1 : (fun z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
              φ.symm (φ z.1) - φ.symm (φ z.2) - fderiv ℝ φ.symm (φ p) (φ z.1 - φ z.2)) =o[𝓝 (p, p)]
              (fun z => z.1 - z.2) :=
            ((hasStrictFDerivAt_iff_isLittleO.1 hψs).comp_tendsto hcφ).trans_isBigO hφs.isBigO_sub
          have h2 := ((R.isBigO_comp _ _).trans_isLittleO h1).mono (inf_le_left (b := 𝓟 (S ×ˢ S)))
          refine h2.congr' ?_ EventuallyEq.rfl
          have hsrc : ∀ᶠ z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 (p, p) ⊓ 𝓟 (S ×ˢ S),
              z ∈ φ.source ×ˢ φ.source :=
            mem_inf_of_left ((φ.open_source.prod φ.open_source).mem_nhds ⟨hpφ, hpφ⟩)
          have hSS : ∀ᶠ z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 (p, p) ⊓ 𝓟 (S ×ˢ S),
              z ∈ S ×ˢ S := mem_inf_of_right (mem_principal_self _)
          filter_upwards [hsrc, hSS] with z hz1 hz2
          rw [φ.left_inv hz1.1, φ.left_inv hz1.2, map_sub R (z.1 - z.2), hR _ (hBt _ _), sub_zero]
          intro i hi
          simp [hzero _ ⟨hz2.1, hz1.1⟩ i hi, hzero _ ⟨hz2.2, hz1.2⟩ i hi]
        have hΓN : Γ ⊆ interior N := fun p hp => mem_interior_iff_mem_nhds.2 (mem_nhdsSet_iff_forall.1 hNn p hp)
        have hΓN₀ : Γ ⊆ N₀ := fun p hp => hSN₀ ⟨hΓS hp, hΓN hp⟩
        -- projAlong facts
        have hpL : ∀ V W : Submodule ℝ (EuclideanSpace ℝ (Fin m)), IsCompl V W → ∀ v ∈ V, projAlong V W v = v := by
          intro V W h v hv
          simp only [projAlong, dif_pos h]
          simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left h ⟨v, hv⟩)
        have hpR : ∀ V W : Submodule ℝ (EuclideanSpace ℝ (Fin m)), IsCompl V W → ∀ v ∈ W, projAlong V W v = 0 := by
          intro V W h v hv
          simp only [projAlong, dif_pos h]
          simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_right h ⟨v, hv⟩)
        have hpm : ∀ V W : Submodule ℝ (EuclideanSpace ℝ (Fin m)), IsCompl V W → ∀ v, projAlong V W v ∈ V := by
          intro V W h v
          simp only [projAlong, dif_pos h]
          simp
        have hps : ∀ V W : Submodule ℝ (EuclideanSpace ℝ (Fin m)), IsCompl V W → ∀ v, v - projAlong V W v ∈ W := by
          intro V W h v
          rw [← Submodule.projectionOnto_apply_eq_zero_iff h]
          have h1 := Submodule.projectionOnto_apply_left h ⟨_, hpm V W h v⟩
          simp only at h1
          rw [map_sub, h1, sub_eq_zero]
          ext1
          simp [projAlong, dif_pos h]
        -- main local claim
        have hmain : ∀ p ∈ Γ, ∀ᶠ x in 𝓝 p, x ∈ N₀ ∧ Φ T x ∈ N₀ ∧ 2 * tubeDist Pr x ≤ tubeDist Pr (Φ T x) := by
          intro p hp
          have hp' : Φ T p ∈ Γ := hΓm T p hp
          have hpS := hΓS hp
          have hp'S := hΓS hp'
          have hpN := interior_subset (hΓN hp)
          have hp'N := interior_subset (hΓN hp')
          obtain ⟨hc1, hc2, hc3⟩ := h6 p ⟨hpN, hpS⟩
          obtain ⟨hc1', hc2', hc3'⟩ := h6 _ ⟨hp'N, hp'S⟩
          rw [hExt _ hp] at hc1 hc3
          rw [hExt _ hp'] at hc1' hc3'
          have hdf : DifferentiableAt ℝ (Φ T) p := by
            by_contra hnd
            have h0 := fderiv_zero_of_not_differentiableAt hnd
            have hfr := (hsplit p hp).2
            have : Eu p ≠ ⊥ := by
              intro hb
              rw [hb, finrank_bot] at hfr
              omega
            obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
            have := h5 p hp w hw
            rw [h0] at this
            simp only [zero_apply, norm_zero] at this
            exact hw0 (norm_le_zero_iff.1 (by linarith))
          have hfs := hstrict p hdf
          set L := fderiv ℝ (Φ T) p with hL
          have hLnorm : 5 ≤ ‖L‖ := by
            have hfr := (hsplit p hp).2
            have : Eu p ≠ ⊥ := by
              intro hb
              rw [hb, finrank_bot] at hfr
              omega
            obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
            have h1 := (h5 p hp w hw).trans (L.le_opNorm w)
            exact le_of_mul_le_mul_right h1 (norm_pos_iff.2 hw0)
          have hε9 : ε < 1 / 9 := by
            have := hε1 p hpN
            nlinarith
          -- tangent invariance
          have hLT : ∀ t ∈ tangentSubspace S p, L t ∈ tangentSubspace S (Φ T p) := by
            intro t ht
            have : tangentSubspace S p ≤ (tangentSubspace S (Φ T p)).comap (L : _ →ₗ[ℝ] _) := by
              refine Submodule.span_le.2 ?_
              rintro v ⟨c, hc0, hcS, hcd⟩
              refine Submodule.subset_span ⟨fun s => Φ T (c s), by simp [hc0], ?_, ?_⟩
              · have ht : Tendsto c (𝓝 0) (𝓝 p) := by simpa [hc0] using hcd.continuousAt.tendsto
                filter_upwards [hcS, ht.eventually (hSinv p hp)] with s h1 h2 using h2 h1
              · have : HasFDerivAt (Φ T) L (c 0) := by rw [hc0]; exact hfs.hasFDerivAt
                exact this.comp_hasDerivAt (0:ℝ) hcd
            exact this ht
          set R : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
            ContinuousLinearMap.id ℝ _ - projAlong (tangentSubspace S (Φ T p)) (Et (Φ T p)) with hR
          have hRT : ∀ t ∈ tangentSubspace S (Φ T p), R t = 0 := by
            intro t ht
            simp [hR, hpL _ _ hc2' t ht]
          have hRE : ∀ t ∈ Et (Φ T p), R t = t := by
            intro t ht
            simp [hR, hpR _ _ hc2' t ht]
          -- linear expansion
          have hlin : ∀ w ∈ Et p, 3 * ‖w‖ ≤ ‖R (L w)‖ := by
            intro w hw
            set a := projAlong (tangentSubspace S p) (Eu p) w with ha
            have ha1 : ‖a‖ ≤ ε * ‖w‖ := by
              have := (projAlong (tangentSubspace S p) (Eu p) - projAlong (tangentSubspace S p) (Et p)).le_of_opNorm_le hc3 w
              simpa [hpR _ _ hc2 w hw] using this
            set b := w - a with hb
            have hbE : b ∈ Eu p := hps _ _ hc1 w
            have hb1 : ‖w‖ - ‖a‖ ≤ ‖b‖ := norm_sub_norm_le _ _
            have hLb := h5 p hp b hbE
            have hLbE : L b ∈ Eu (Φ T p) := by
              rw [← hEuinv T p hp]
              exact ⟨b, hbE, rfl⟩
            have hRw : R (L w) = R (L b) := by
              have : w = a + b := by simp [hb]
              rw [this, map_add, map_add, hRT _ (hLT _ (hpm _ _ hc1 w)), zero_add]
            have hRb : R (L b) = L b + (projAlong (tangentSubspace S (Φ T p)) (Eu (Φ T p)) -
                projAlong (tangentSubspace S (Φ T p)) (Et (Φ T p))) (L b) := by
              simp [hR, hpR _ _ hc1' _ hLbE, sub_eq_add_neg]
            have h7 := (projAlong (tangentSubspace S (Φ T p)) (Eu (Φ T p)) -
                projAlong (tangentSubspace S (Φ T p)) (Et (Φ T p))).le_of_opNorm_le hc3' (L b)
            have h8 : ‖L b‖ - ε * ‖L b‖ ≤ ‖R (L b)‖ := by
              rw [hRb]
              have := norm_sub_le_norm_add (L b) ((projAlong (tangentSubspace S (Φ T p)) (Eu (Φ T p)) -
                projAlong (tangentSubspace S (Φ T p)) (Et (Φ T p))) (L b))
              linarith
            rw [hRw]
            have h9 : ε * ‖L b‖ ≤ 1 / 9 * ‖L b‖ := by gcongr
            have h10 : ε * ‖w‖ ≤ 1 / 9 * ‖w‖ := by gcongr
            have := norm_nonneg w
            linarith
          -- limits
          have hPp : Pr p = p := hPrS p ⟨hpS, hΓN₀ hp⟩
          have hPp' : Pr (Φ T p) = Φ T p := hPrS _ ⟨hp'S, hΓN₀ hp'⟩
          have hfc : Tendsto (Φ T) (𝓝 p) (𝓝 (Φ T p)) := hdf.continuousAt.tendsto
          have hq : Tendsto Pr (𝓝 p) (𝓝 p) := by
            have := (hPrc.continuousAt (hN₀o.mem_nhds (hΓN₀ hp))).tendsto
            rwa [hPp] at this
          have hq' : Tendsto (fun x => Pr (Φ T x)) (𝓝 p) (𝓝 (Φ T p)) := by
            have := (hPrc.continuousAt (hN₀o.mem_nhds (hΓN₀ hp'))).tendsto
            rw [hPp'] at this
            exact this.comp hfc
          have hN0x : ∀ᶠ x in 𝓝 p, x ∈ N₀ := hN₀o.mem_nhds (hΓN₀ hp)
          have hN0y : ∀ᶠ x in 𝓝 p, Φ T x ∈ N₀ := hfc.eventually (hN₀o.mem_nhds (hΓN₀ hp'))
          have hQ : ∀ p ∈ Γ, ∀ c : ℝ, 0 < c → ∀ᶠ q in 𝓝 p, ‖(Et q).starProjection - (Et p).starProjection‖ < c := by
            intro p hp c hc
            have h1 : ContinuousAt (fun q => (Et q).starProjection) p :=
              hEts.continuousOn.continuousAt (mem_nhdsSet_iff_forall.1 hNn p hp)
            have h2 := (h1.sub (continuousAt_const (y := (Et p).starProjection))).norm.tendsto
            have h3 : Tendsto (fun q => ‖(Et q).starProjection - (Et p).starProjection‖) (𝓝 p) (𝓝 0) := by
              simpa using h2
            exact h3.eventually_lt_const hc
          have o2 : (fun x => (x - Pr x) - (Et p).starProjection (x - Pr x)) =o[𝓝 p] (fun x => x - Pr x) := by
            rw [Asymptotics.isLittleO_iff]
            intro c hc
            filter_upwards [hN0x, hq.eventually (hQ p hp c hc)] with x h1 h2
            have h3 := (hPrx x h1).2.1
            have h4 := ((Et (Pr x)).starProjection - (Et p).starProjection).le_of_opNorm_le h2.le (x - Pr x)
            rw [sub_apply, Submodule.starProjection_eq_self_iff.2 h3] at h4
            exact h4
          have o3 : (fun x => (Φ T x - Pr (Φ T x)) - (Et (Φ T p)).starProjection (Φ T x - Pr (Φ T x)))
              =o[𝓝 p] (fun x => Φ T x - Pr (Φ T x)) := by
            rw [Asymptotics.isLittleO_iff]
            intro c hc
            filter_upwards [hN0y, hq'.eventually (hQ _ hp' c hc)] with x h1 h2
            have h3 := (hPrx _ h1).2.1
            have h4 := ((Et (Pr (Φ T x))).starProjection - (Et (Φ T p)).starProjection).le_of_opNorm_le h2.le (Φ T x - Pr (Φ T x))
            rw [sub_apply, Submodule.starProjection_eq_self_iff.2 h3] at h4
            exact h4
          have hxq : Tendsto (fun x => (x, Pr x)) (𝓝 p) (𝓝 (p, p)) := tendsto_id.prodMk_nhds hq
          have o1 : (fun x => Φ T x - Φ T (Pr x) - L (x - Pr x)) =o[𝓝 p] (fun x => x - Pr x) :=
            (hasStrictFDerivAt_iff_isLittleO.1 hfs).comp_tendsto hxq
          have b1 : (fun x => Φ T x - Φ T (Pr x)) =O[𝓝 p] (fun x => x - Pr x) :=
            hfs.isBigO_sub.comp_tendsto hxq
          have hqS : ∀ᶠ x in 𝓝 p, Φ T (Pr x) ∈ S := by
            filter_upwards [hN0x, hq.eventually (hSinv p hp)] with x h1 h2 using h2 (hPrx x h1).1.1
          have hpair : Tendsto (fun x => (Φ T (Pr x), Pr (Φ T x))) (𝓝 p)
              (𝓝 (Φ T p, Φ T p) ⊓ 𝓟 (S ×ˢ S)) := by
            refine tendsto_inf.2 ⟨(hfc.comp hq).prodMk_nhds hq', tendsto_principal.2 ?_⟩
            filter_upwards [hqS, hN0y] with x h1 h2 using ⟨h1, (hPrx _ h2).1.1⟩
          have o4 : (fun x => R (Φ T (Pr x) - Pr (Φ T x))) =o[𝓝 p] (fun x => Φ T (Pr x) - Pr (Φ T x)) :=
            (hTan _ hp'S R hRT).comp_tendsto hpair
          set gg : EuclideanSpace ℝ (Fin m) → ℝ := fun x => ‖Φ T x - Pr (Φ T x)‖ + ‖x - Pr x‖ with hgg
          have bu : (fun x => Φ T x - Pr (Φ T x)) =O[𝓝 p] gg :=
            Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => by
              rw [hgg, one_mul, Real.norm_of_nonneg (by positivity)]
              have := norm_nonneg (x - Pr x); linarith)
          have bv : (fun x => x - Pr x) =O[𝓝 p] gg :=
            Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => by
              rw [hgg, one_mul, Real.norm_of_nonneg (by positivity)]
              have := norm_nonneg (Φ T x - Pr (Φ T x)); linarith)
          have bw : (fun x => Φ T (Pr x) - Pr (Φ T x)) =O[𝓝 p] gg :=
            (bu.sub (b1.trans bv)).congr_left (fun x => by abel)
          have o5 : (fun x => ((Φ T x - Pr (Φ T x)) - (Et (Φ T p)).starProjection (Φ T x - Pr (Φ T x)))
              - R ((Φ T x - Pr (Φ T x)) - (Et (Φ T p)).starProjection (Φ T x - Pr (Φ T x)))
              + R (Φ T x - Φ T (Pr x) - L (x - Pr x))
              + R (L ((x - Pr x) - (Et p).starProjection (x - Pr x)))
              + R (Φ T (Pr x) - Pr (Φ T x))) =o[𝓝 p] gg := by
            refine (((?_ : Asymptotics.IsLittleO _ _ _).sub ?_).add ?_).add ?_ |>.add ?_
            · exact o3.trans_isBigO bu
            · exact (R.isBigO_comp _ _).trans_isLittleO (o3.trans_isBigO bu)
            · exact (R.isBigO_comp _ _).trans_isLittleO (o1.trans_isBigO bv)
            · exact ((R.comp L).isBigO_comp _ _).trans_isLittleO (o2.trans_isBigO bv)
            · exact o4.trans_isBigO bw
          have o6 : (fun x => (Φ T x - Pr (Φ T x)) - R (L ((Et p).starProjection (x - Pr x)))) =o[𝓝 p] gg := by
            refine o5.congr_left (fun x => ?_)
            have h1 := hRE _ ((Et (Φ T p)).starProjection_apply_mem (Φ T x - Pr (Φ T x)))
            have h2 : Φ T (Pr x) - Pr (Φ T x) = (Φ T x - Pr (Φ T x)) - (Φ T x - Φ T (Pr x)) := by abel
            rw [h2]
            simp only [map_sub] at h1 ⊢
            rw [h1]
            abel
          filter_upwards [hN0x, hN0y, o6.bound (by norm_num : (0:ℝ) < 1 / 10), o2.bound (by norm_num : (0:ℝ) < 1 / 10)]
            with x h1 h2 h3 h4
          refine ⟨h1, h2, ?_⟩
          simp only [tubeDist]
          rw [hgg, Real.norm_of_nonneg (by positivity)] at h3
          beta_reduce at h3
          have h5 := hlin _ ((Et p).starProjection_apply_mem (x - Pr x))
          have h6 := norm_le_insert' (R (L ((Et p).starProjection (x - Pr x)))) (Φ T x - Pr (Φ T x))
          rw [norm_sub_rev (R (L ((Et p).starProjection (x - Pr x))))] at h6
          have h7 := norm_le_insert' (x - Pr x) ((Et p).starProjection (x - Pr x))
          have := norm_nonneg (x - Pr x)
          linarith
        refine ⟨{x | x ∈ N₀ ∧ Φ T x ∈ N₀ ∧ 2 * tubeDist Pr x ≤ tubeDist Pr (Φ T x)}, ?_, fun x hx => hx.1, 2, by norm_num, fun x hx => hx.2⟩
        exact mem_nhdsSet_iff_forall.2 hmain
