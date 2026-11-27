-- Prove2me | solution 1 for StrictCQ.Scaled.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:02.494719+00:00
-- url     : https://prove2.me/submissions/5b3ef5d7-ec5e-4cb3-bd6d-3083a333eaf5

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Supplement_CCP
import Definitions.Def_StrictCQ_AGP_LAGP
import Definitions.Def_StrictCQ_SAKKT_Conditions
import Definitions.Def_StrictCQ_CAKKT_Conditions

open StrictCQ
open StrictCQ.Scaled
open StrictCQ.Scaled.Supplement

/-- Theorem 5.1, p. 13, corrected: clauses 1–3, together with a counterexample to clause 4.
The counterexample has n = 1, m = 0, p = 1 and g(x) = -x² at the feasible point 0. -/
theorem solution {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hC : C.IsC1) (hxs : xs ∈ C.feasible) :
    (CCP C xs → C.AGPRegular xs) ∧
    (C.AGPRegular xs →
      (⟨C.h, C.g⟩ : StrictCQ.SAKKT.Constraints n m p).SAKKTRegular xs) ∧
    (C.AGPRegular xs → C.LAGPRegular xs) ∧
    (∃ D : StrictCQ.AGP.Constraints 1 0 1,
      (∀ (j : Fin 1) (x : EuclideanSpace ℝ (Fin 1)), D.g j x = -(x 0)^2) ∧
      D.IsC1 ∧ (0 : EuclideanSpace ℝ (Fin 1)) ∈ D.feasible ∧
      (⟨D.h, D.g⟩ : StrictCQ.SAKKT.Constraints 1 0 1).SAKKTRegular 0 ∧
      ¬ (⟨D.h, D.g⟩ : StrictCQ.CAKKT.Constraints 1 0 1).CAKKTRegular 0) := by
        have hlinxs : xs ∈ C.linSet xs ⊥ :=
          ⟨fun i => by simp, fun j _ => by simp, fun j _ hj => by simpa using hj.le⟩
        have hNeq : ∀ w, w ∈ StrictCQ.AGP.normalCone (C.linSet xs ⊥) xs →
            w ∈ StrictCQ.AGP.normalCone
              ((⟨C.h, C.g⟩ : StrictCQ.SAKKT.Constraints n m p).linSet xs 0) xs := by
          rintro w ⟨_, hw⟩
          refine ⟨⟨fun i => by simp, fun j _ => by simp,
            fun j h1 h2 => (lt_asymm (EReal.coe_pos.1 h1) h2).elim⟩, ?_⟩
          rintro z ⟨hz1, hz2, -⟩
          have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ j, C.g j xs < 0 →
              C.g j xs + t * inner ℝ (gradient (C.g j) xs) (z - xs) < 0 := by
            rw [Filter.eventually_all]
            intro j
            by_cases hj : C.g j xs < 0
            · have : Filter.Tendsto (fun t : ℝ => C.g j xs + t * inner ℝ (gradient (C.g j) xs) (z - xs))
                  (nhds 0) (nhds (C.g j xs + 0 * inner ℝ (gradient (C.g j) xs) (z - xs))) :=
                tendsto_const_nhds.add (Filter.tendsto_id.mul tendsto_const_nhds)
              rw [zero_mul, add_zero] at this
              exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds (this.eventually_lt_const hj)).mono fun t ht _ => ht
            · exact Filter.Eventually.of_forall fun t ht => absurd ht hj
          obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
          have htpos' : (0:ℝ) < t := htpos
          have hmem : xs + t • (z - xs) ∈ C.linSet xs ⊥ := by
            refine ⟨fun i => ?_, fun j hj => ?_, fun j _ hj => ?_⟩
            · rw [add_sub_cancel_left, inner_smul_right]
              have := hz1 i
              simp only at this
              rw [this, mul_zero]
            · rw [add_sub_cancel_left, inner_smul_right]
              have := hz2 j hj
              simp only at this
              nlinarith
            · rw [add_sub_cancel_left, inner_smul_right]; exact (ht j hj).le
          have := hw _ hmem
          rw [add_sub_cancel_left, inner_smul_right] at this
          by_contra hc
          push Not at hc
          have := mul_pos htpos' hc
          linarith
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hccp w hw
          obtain ⟨q, wk, -, hq, hwk, hmem⟩ := hw
          have hmc : ∀ w ∈ movingCone C xs xs, w ∈ StrictCQ.AGP.normalCone (C.linSet xs ⊥) xs := by
            rintro w ⟨lam, mu, hmu, hmu', rfl⟩
            refine ⟨hlinxs, fun z hz => ?_⟩
            obtain ⟨hz1, hz2, -⟩ := hz
            rw [inner_add_left, sum_inner, sum_inner]
            have e1 : ∑ i, inner ℝ (lam i • gradient (C.h i) xs) (z - xs) = 0 :=
              Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_left, hz1 i, mul_zero]
            have e2 : ∑ j, inner ℝ (mu j • gradient (C.g j) xs) (z - xs) ≤ 0 :=
              Finset.sum_nonpos fun j _ => by
                rw [real_inner_smul_left]
                by_cases hj : C.g j xs = 0
                · have := hz2 j hj.ge; have := hmu j; nlinarith
                · rw [hmu' j hj, zero_mul]
            linarith
          have hx : Filter.Tendsto (fun k => (q k).1) Filter.atTop (nhds xs) := by
            exact (continuous_fst.tendsto _).comp hq
          have he : Filter.Tendsto (fun k => (q k).2) Filter.atTop (nhds 0) := by
            exact (continuous_snd.tendsto _).comp hq
          have hgc : ∀ j, Continuous (gradient (C.g j)) := fun j =>
            (InnerProductSpace.toDual ℝ _).symm.continuous.comp ((hC.2 j).continuous_fderiv one_ne_zero)
          have hev : ∀ᶠ k in Filter.atTop, ∀ j, C.g j xs < 0 →
              C.g j (q k).1 < 0 ∧ C.g j (q k).1 + inner ℝ (gradient (C.g j) (q k).1) (q k).2 < 0 := by
            rw [Filter.eventually_all]
            intro j
            by_cases hj : C.g j xs < 0
            · have t1 : Filter.Tendsto (fun k => C.g j (q k).1) Filter.atTop (nhds (C.g j xs)) :=
                ((hC.2 j).continuous.tendsto xs).comp hx
              have t2 : Filter.Tendsto
                  (fun k => C.g j (q k).1 + inner ℝ (gradient (C.g j) (q k).1) (q k).2) Filter.atTop
                  (nhds (C.g j xs + inner ℝ (gradient (C.g j) xs) 0)) :=
                t1.add ((((hgc j).tendsto xs).comp hx).inner he)
              rw [inner_zero_right, add_zero] at t2
              filter_upwards [t1.eventually_lt_const hj, t2.eventually_lt_const hj] with k h1 h2 _
              exact ⟨h1, h2⟩
            · exact Filter.Eventually.of_forall fun k hk => absurd hk hj
          have key : ∀ (x ε v : EuclideanSpace ℝ (Fin n)),
              v ∈ StrictCQ.AGP.normalCone (C.linSet x ⊥) (x + ε) →
              (∀ j, C.g j xs < 0 → C.g j x < 0 ∧ C.g j x + inner ℝ (gradient (C.g j) x) ε < 0) →
              v ∈ closure (movingCone C xs x) := by
            intro x ε v hvn hj
            obtain ⟨hy, hv⟩ := hvn
            by_contra hcl
            have hconv : Convex ℝ (movingCone C xs x) := by
              rintro a ⟨la, ma, hma, hma', rfl⟩ b ⟨lb, mb, hmb, hmb', rfl⟩ s t hs ht hst
              refine ⟨fun i => s * la i + t * lb i, fun j => s * ma j + t * mb j,
                fun j => by have := hma j; have := hmb j; positivity,
                fun j hj => by simp [hma' j hj, hmb' j hj], ?_⟩
              simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib, smul_add]
              abel
            obtain ⟨f, u, hfu, hfv⟩ := geometric_hahn_banach_closed_point hconv.closure isClosed_closure hcl
            have hin : ∀ a ∈ movingCone C xs x, f a < u := fun a ha => hfu a (subset_closure ha)
            have hu : 0 < u := by
              have := hin 0 ⟨0, 0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
              simpa using this
            have hh : ∀ i, f (gradient (C.h i) x) = 0 := by
              intro i
              by_contra hne
              have := hin ((u / f (gradient (C.h i) x)) • gradient (C.h i) x)
                ⟨Pi.single i (u / f (gradient (C.h i) x)), 0, fun _ => le_rfl, fun _ _ => rfl,
                  by simp [Pi.single_apply]⟩
              rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
              exact lt_irrefl _ this
            have hg : ∀ j, C.g j xs = 0 → f (gradient (C.g j) x) ≤ 0 := by
              intro j hj0
              by_contra hpos
              push Not at hpos
              have hc0 : 0 ≤ u / f (gradient (C.g j) x) := by positivity
              have := hin ((u / f (gradient (C.g j) x)) • gradient (C.g j) x)
                ⟨0, Pi.single j (u / f (gradient (C.g j) x)), fun j' => by
                    rcases eq_or_ne j' j with rfl | h
                    · simpa using hc0
                    · simp [h], fun j' hj' => by
                    rcases eq_or_ne j' j with rfl | h
                    · exact absurd hj0 hj'
                    · simp [h], by simp [Pi.single_apply]⟩
              rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
              exact lt_irrefl _ this
            set d := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f with hdd
            have hd : ∀ a, inner ℝ d a = f a := fun a => InnerProductSpace.toDual_symm_apply
            have hev2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ j, C.g j xs < 0 →
                C.g j x + inner ℝ (gradient (C.g j) x) ε + t * inner ℝ (gradient (C.g j) x) d < 0 := by
              rw [Filter.eventually_all]
              intro j
              by_cases hj' : C.g j xs < 0
              · have : Filter.Tendsto (fun t : ℝ => C.g j x + inner ℝ (gradient (C.g j) x) ε +
                    t * inner ℝ (gradient (C.g j) x) d) (nhds 0)
                    (nhds (C.g j x + inner ℝ (gradient (C.g j) x) ε +
                      0 * inner ℝ (gradient (C.g j) x) d)) :=
                  tendsto_const_nhds.add (Filter.tendsto_id.mul tendsto_const_nhds)
                rw [zero_mul, add_zero] at this
                exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds (this.eventually_lt_const (hj j hj').2)).mono fun t ht _ => ht
              · exact Filter.Eventually.of_forall fun t ht => absurd ht hj'
            obtain ⟨t, ht, htpos⟩ := (hev2.and self_mem_nhdsWithin).exists
            have htpos' : (0:ℝ) < t := htpos
            have hz : x + ε + t • d ∈ C.linSet x ⊥ := by
              obtain ⟨hy1, hy2, hy3⟩ := hy
              simp only [add_sub_cancel_left] at hy1 hy2 hy3
              have hsub : x + ε + t • d - x = ε + t • d := by abel
              refine ⟨fun i => ?_, fun j hj0 => ?_, fun j hb hjn => ?_⟩
              · rw [hsub, inner_add_right, inner_smul_right, hy1 i, real_inner_comm, hd, hh i]; ring
              · rw [hsub, inner_add_right, inner_smul_right, real_inner_comm d, hd]
                rcases (hxs.2 j).lt_or_eq with hlt | heq
                · exact absurd hj0 (not_le.2 (hj j hlt).1)
                · have := hy2 j hj0; have := hg j heq; nlinarith
              · rcases (hxs.2 j).lt_or_eq with hlt | heq
                · have := ht j hlt; rw [hsub, inner_add_right, inner_smul_right]; linarith
                · rw [hsub, inner_add_right, inner_smul_right, real_inner_comm d, hd]
                  have := hy3 j hb hjn; have := hg j heq; nlinarith
            have := hv _ hz
            rw [show x + ε + t • d - (x + ε) = t • d by abel, inner_smul_right, real_inner_comm, hd] at this
            nlinarith
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
          have hcl : ∀ k, N ≤ k → wk k ∈ closure (movingCone C xs (q k).1) := fun k hk =>
            key _ _ _ (hmem k) (hN k hk)
          have hch : ∀ k, ∃ v ∈ movingCone C xs (q k).1, N ≤ k → dist v (wk k) < 1 / ((k:ℝ) + 1) := by
            intro k
            by_cases hk : N ≤ k
            · obtain ⟨v, hv, hd⟩ := Metric.mem_closure_iff.1 (hcl k hk) (1 / ((k:ℝ)+1)) (by positivity)
              exact ⟨v, hv, fun _ => by rw [dist_comm]; exact hd⟩
            · exact ⟨0, ⟨0, 0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩, fun h => absurd h hk⟩
          choose v hv hvd using hch
          apply hmc
          apply hccp.1
          refine ⟨fun k => (q k).1, v, fun _ => trivial, hx, ?_, hv⟩
          rw [Metric.tendsto_atTop] at hwk ⊢
          intro ε hε
          obtain ⟨N1, hN1⟩ := hwk (ε/2) (by positivity)
          obtain ⟨N2, hN2⟩ := exists_nat_one_div_lt (half_pos hε)
          refine ⟨max N (max N1 N2), fun k hk => ?_⟩
          have h1 := hN1 k (le_of_max_le_left (le_of_max_le_right hk))
          have h2 := hvd k (le_of_max_le_left hk)
          have hk2 : (N2:ℝ) ≤ k := by exact_mod_cast le_of_max_le_right (le_of_max_le_right hk)
          have h3 : 1 / ((k:ℝ) + 1) ≤ 1 / ((N2:ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity); linarith
          calc dist (v k) w ≤ dist (v k) (wk k) + dist (wk k) w := dist_triangle _ _ _
            _ < ε := by linarith
        · intro hreg w hw
          obtain ⟨z, v, -, hz, hv, hmem⟩ := hw
          apply hNeq
          apply hreg
          refine ⟨fun k => (z k, 0), v, fun _ => trivial, hz.prodMk_nhds tendsto_const_nhds, hv,
            fun k => ?_⟩
          obtain ⟨_, hk⟩ := hmem k
          refine ⟨?_, fun y hy => ?_⟩
          · simp only [add_zero]
            exact ⟨fun i => by simp, fun j _ => by simp, fun j _ hj => by simpa using hj.le⟩
          · simp only [add_zero]
            exact hk y ⟨hy.1, hy.2.1, fun j h1 h2 => (lt_asymm (EReal.coe_pos.1 h1) h2).elim⟩
        · intro hreg
          have haff : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, StrictCQ.AGP.IsAffine φ →
              ∀ x z, inner ℝ (gradient φ x) (z - x) = φ z - φ x := by
            rintro φ ⟨a, b, hab⟩ x z
            have hφ : φ = fun y => inner ℝ a y + b := funext hab
            have hg : gradient φ x = a := by
              apply HasGradientAt.gradient
              rw [hasGradientAt_iff_hasFDerivAt, hφ]
              have := ((innerSL ℝ a).hasFDerivAt (x := x)).add_const b
              refine this.congr_fderiv ?_
              ext y; simp
            rw [hg, hab, hab, inner_sub_right]; ring
          have hset : ∀ x ∈ C.linPart, C.nonlinSet x ∩ C.linPart = C.linSet x ⊥ := by
            intro x hx
            ext z
            constructor
            · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
              refine ⟨fun i => ?_, fun j hj => ?_, fun j _ hj => ?_⟩
              · by_cases ha : StrictCQ.AGP.IsAffine (C.h i)
                · rw [haff _ ha, h4 i ha, hx.1 i ha, sub_zero]
                · exact h1 i ha
              · by_cases ha : StrictCQ.AGP.IsAffine (C.g j)
                · rw [haff _ ha]; linarith [h5 j ha]
                · exact h2 j ha hj
              · by_cases ha : StrictCQ.AGP.IsAffine (C.g j)
                · rw [haff _ ha]; linarith [h5 j ha]
                · exact h3 j ha hj
            · rintro ⟨h1, h2, h3⟩
              refine ⟨⟨fun i _ => h1 i, fun j _ hj => h2 j hj,
                fun j _ hj => h3 j (EReal.bot_lt_coe _) hj⟩, fun i ha => ?_, fun j ha => ?_⟩
              · have := h1 i; rw [haff _ ha, hx.1 i ha, sub_zero] at this; exact this
              · rcases (hx.2 j ha).lt_or_eq with hlt | heq
                · have := h3 j (EReal.bot_lt_coe _) hlt; rw [haff _ ha] at this; linarith
                · have := h2 j heq.ge; rw [haff _ ha] at this; linarith
          have hxsL : xs ∈ C.linPart := ⟨fun i _ => hxs.1 i, fun j _ => hxs.2 j⟩
          intro w hw
          obtain ⟨q, v, hqD, hq, hv, hmem⟩ := hw
          rw [hset xs hxsL]
          apply hreg
          refine ⟨q, v, fun _ => trivial, hq, hv, fun k => ?_⟩
          have := hmem k
          simp only at this ⊢
          rwa [hset (q k).1 (hqD k)] at this
        · set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with he
          have hgr : ∀ x : EuclideanSpace ℝ (Fin 1),
              gradient (fun x : EuclideanSpace ℝ (Fin 1) => -(x 0)^2) x = (-2 * x 0) • e := by
            intro x
            apply HasGradientAt.gradient
            rw [hasGradientAt_iff_hasFDerivAt]
            have h1 := (((EuclideanSpace.proj (0 : Fin 1)) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2
            have h2 := h1.neg
            have h3 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 1) => -(x 0)^2)
                (-((2 • (EuclideanSpace.proj (0 : Fin 1) x) ^ (2 - 1)) •
                  ((EuclideanSpace.proj (0 : Fin 1)) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ))) x := h2
            refine h3.congr_fderiv ?_
            ext y
            simp [he, EuclideanSpace.inner_single_left]
          refine ⟨⟨fun i => i.elim0, fun _ x => -(x 0)^2⟩, fun _ _ => rfl, ⟨fun i => i.elim0, fun _ => ?_⟩, ⟨fun i => i.elim0, fun _ => by simp⟩, ?_, ?_⟩
          · exact (((EuclideanSpace.proj (0 : Fin 1)) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff.pow 2).neg
          · intro w hw
            obtain ⟨z, v, -, hz, hv, hmem⟩ := hw
            have hv0 : ∀ k, v k = 0 := by
              intro k
              obtain ⟨-, hk⟩ := hmem k
              have hy := hk (z k + v k) ⟨fun i => i.elim0, fun j hj => ?_, fun j h1 h2 => ?_⟩
              · rw [add_sub_cancel_left] at hy
                exact real_inner_self_nonpos.1 hy
              · have : z k 0 = 0 := by
                  have : (z k 0)^2 ≤ 0 := by simpa using hj
                  nlinarith [sq_nonneg (z k 0)]
                show inner ℝ (gradient (fun x : EuclideanSpace ℝ (Fin 1) => -(x 0)^2) (z k)) _ ≤ 0
                rw [hgr, this]; simp
              · exact (lt_asymm (EReal.coe_pos.1 h1) h2).elim
            have : w = 0 := by
              have hv' : Filter.Tendsto v Filter.atTop (nhds 0) := by
                simp only [funext hv0]; exact tendsto_const_nhds
              exact tendsto_nhds_unique hv hv'
            subst this
            refine ⟨⟨fun i => i.elim0, fun j _ => by simp, fun j h1 h2 => (lt_asymm (EReal.coe_pos.1 h1) h2).elim⟩, fun z _ => by simp⟩
          · intro hreg
            set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with ht
            have htpos : ∀ k, 0 < t k := fun k => by simp only [ht]; positivity
            have htt : Filter.Tendsto t Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
            have hmemlim : e ∈ StrictCQ.AGP.outerLimitWithin
                (fun q : EuclideanSpace ℝ (Fin 1) × ℝ =>
                  (⟨fun i => i.elim0, fun _ x => -(x 0)^2⟩ : StrictCQ.CAKKT.Constraints 1 0 1).KC 0 q.1 q.2)
                {q | 0 ≤ q.2} (0, 0) := by
              refine ⟨fun k => ((-t k) • e, t k), fun _ => e, fun k => (htpos k).le, ?_, tendsto_const_nhds, ?_⟩
              · apply Filter.Tendsto.prodMk_nhds
                · have := (htt.neg).smul_const e
                  simpa using this
                · exact htt
              · intro k
                refine ⟨fun i => i.elim0, fun _ => 1 / (2 * t k), fun _ => by have := htpos k; positivity,
                  fun j h => by simp at h, ?_, ?_⟩
                · have := htpos k
                  simp [he, abs_mul, abs_of_pos this]
                  rw [show (t k)⁻¹ * 2⁻¹ * t k ^ 2 = t k / 2 by field_simp]
                  linarith
                · show e = _
                  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
                  rw [hgr]
                  have h0 : (-t k • e).ofLp 0 = -t k := by simp [he]
                  have hp := htpos k
                  rw [h0, smul_smul, show 1 / (2 * t k) * (-2 * -t k) = 1 by field_simp, one_smul]
            have := hreg hmemlim
            obtain ⟨lam, mu, -, -, -, hw⟩ := this
            simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hw
            rw [hgr] at hw
            have : e 0 = 0 := by rw [hw]; simp
            simp [he] at this
