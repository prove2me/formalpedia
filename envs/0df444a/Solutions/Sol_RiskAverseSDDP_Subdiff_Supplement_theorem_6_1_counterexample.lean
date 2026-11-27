-- Prove2me | solution 1 for RiskAverseSDDP.Subdiff.Supplement.theorem_6_1_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:36.793051+00:00
-- url     : https://prove2.me/submissions/222a5576-4f00-4c38-bc76-a67def9ba679

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm3Counterexample
open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

open RiskAverseSDDP
open RiskAverseSDDP.Subdiff
open RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence

/-- Refutation of the explicit independence test printed in Theorem 6.1, p. 20.
The selected-leaf indicators are independent constants, although the sampled scenarios
are repeated forever. Both the unvisited-node convergence and first-stage value
convergence fail, for every outcome. -/
theorem solution :
    zeroData.H2 1 ∧
    zeroTreeModel.H2 1 ∧ zeroTreeModel.Standing ∧
    IsProbabilityMeasure zeroLaw ∧
    (∀ k, Measurable (repeatedSample k)) ∧
    (∀ k (b : Bool), zeroLaw {ω | repeatedSample (k + 1) ω = b} = (1 / 2 : ℝ≥0∞)) ∧
    (∀ k ω, zeroProcess (repeatedSample k ω) = zeroProcess ω) ∧
    (∀ k ω, zeroSelected k ω (.leaf (repeatedSample k ω)) = 1) ∧
    iIndepFun (fun k : ℕ => fun ω : Bool => zeroSelected (k + 1) ω (.leaf (repeatedSample (k + 1) ω))) zeroLaw ∧
    (¬ iIndepFun (fun k : ℕ => repeatedSample (k + 1)) zeroLaw) ∧
    (∀ ω, IsZeroAlgorithm3Run (fun k => repeatedSample k ω) (zeroApprox ω)) ∧
    (∀ ω, zeroTreeModel.IsRun3 zeroTreeRules (fun _ => zeroPath ω) (zeroTreeRun ω)) ∧
    (∀ s, s < 3 → ∀ ν : ZeroLevel s, ∀ z, zeroTreeModel.Q s ν z = 0) ∧
    (zeroTreeModel.Q1 = 0) ∧
    (∀ ω,
      ¬ Tendsto (fun k => (zeroTreeRun ω).Qm k 1 (!ω) ((zeroTreeRun ω).hist zeroTreeModel k 1 (!ω)) -
          zeroTreeModel.Q 1 (!ω) ((zeroTreeRun ω).hist zeroTreeModel k 1 (!ω))) atTop (𝓝 0) ∧
      ¬ Tendsto (fun k => zeroTreeModel.stageVal 0 zeroTreeModel.first
          ((zeroTreeRun ω).Qm k 0 zeroTreeModel.first) (Hist.empty 1)) atTop (𝓝 zeroTreeModel.Q1)) ∧
    (∀ ω, (∀ k, zeroApprox ω k (.middle (!ω)) = ⊥) ∧
      ¬ Tendsto (fun k => zeroApprox ω k (.middle (!ω)) - zeroTrueValue (.middle (!ω))) atTop (𝓝 0) ∧
      ¬ Tendsto (fun k => zeroApprox ω k .first) atTop (𝓝 (zeroTrueValue .first))) := by
        set_option backward.isDefEq.respectTransparency false in
          classical
          have hf : ∀ s (ν : ZeroLevel s) (x : Hist 1 s), zeroTreeModel.feas s ν x = {0} := by
            intro s ν x
            ext y
            simp [TreeModel.feas, zeroTreeModel]
          have hfd : ∀ s (j : Fin 2) (x : Hist 1 s), zeroData.feas s j x = {0} := by
            intro s j x
            ext y
            simp [Model.feas, zeroData]
          have hsv : ∀ s (ν : ZeroLevel s) (c : EReal) (x : Hist 1 s),
              zeroTreeModel.stageVal s ν (fun _ => c) x = c := by
            intro s ν c x
            unfold TreeModel.stageVal
            rw [hf]
            simp only [Set.mem_singleton_iff, iInf_singleton]
            simp [zeroTreeModel]
          have hrho : ∀ s (ν : ZeroLevel s) (Z : zeroTreeModel.Child s ν → EReal),
              zeroTreeModel.rho s ν Z = zeroTreeModel.wsum s ν (fun _ => 1) Z := by
            intro s ν Z
            unfold TreeModel.rho
            change (⨆ a ∈ ({fun _ => 1} : Set (zeroTreeModel.Child s ν → ℝ)), zeroTreeModel.wsum s ν a Z) = _
            exact iSup_singleton
          have hproper : ∀ s, EProper (fun _ : Hist 1 s => (0 : EReal)) := by
            intro s
            exact ⟨fun _ => by simp, 0, by simp⟩
          have hconvex : ∀ s, EConvex (fun _ : Hist 1 s => (0 : EReal)) := by
            intro s
            intro x hx y hy a b ha hb hab
            simp only [Set.mem_setOf_eq] at hx hy ⊢
            change (0 : EReal) ≤ ((a • x + b • y).2 : ℝ)
            have hx' : 0 ≤ x.2 := by exact_mod_cast hx
            have hy' : 0 ≤ y.2 := by exact_mod_cast hy
            exact_mod_cast (add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy'))
          have hqual : ∀ s, ∃ xb : Hist 1 s, ∃ yb : EuclideanSpace ℝ (Fin 1),
              (∀ i : Fin s, xb i ∈ ({0} : Set (EuclideanSpace ℝ (Fin 1)))) ∧
              yb ∈ intrinsicInterior ℝ ({0} : Set (EuclideanSpace ℝ (Fin 1))) ∧
              xb.snoc yb ∈ intrinsicInterior ℝ (Set.univ : Set (Hist 1 (s+1))) ∧ yb = 0 := by
            intro s
            refine ⟨0, 0, ?_⟩
            refine ⟨by simp, by simp [intrinsicInterior_singleton], ?_, rfl⟩
            apply interior_subset_intrinsicInterior
            simp
          have hH2 : zeroData.H2 1 := by
            refine ⟨by norm_num, ?_⟩
            intro s hs
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [zeroData] using And.intro (Set.singleton_nonempty (0 : EuclideanSpace ℝ (Fin 1)))
                ⟨convex_singleton 0, isCompact_singleton⟩
            · intro j hj
              exact ⟨hproper _, hconvex _, lowerSemicontinuous_const⟩
            · intro j hj i
              exact Fin.elim0 i
            · intro j hj x hx y hy
              simp [zeroData]
            · intro j hj x hx
              rw [hfd]
              exact Set.singleton_nonempty _
            · intro h j
              obtain ⟨xb, yb, hx, hy, hz, he⟩ := hqual s
              refine ⟨xb, yb, hx, hy, ?_, ?_⟩
              · simpa [zeroData] using hz
              · simpa [hfd] using he
          have hH2t : zeroTreeModel.H2 1 := by
            refine ⟨by norm_num, ?_⟩
            intro s hs
            refine ⟨?_, ?_⟩
            · simpa [zeroTreeModel] using And.intro (Set.singleton_nonempty (0 : EuclideanSpace ℝ (Fin 1)))
                ⟨convex_singleton 0, isCompact_singleton⟩
            intro ν
            refine ⟨⟨hproper _, hconvex _, lowerSemicontinuous_const⟩, ?_, ?_, ?_, ?_⟩
            · intro i; exact Fin.elim0 i
            · intro x hx y hy; simp [zeroTreeModel]
            · intro x hx; rw [hf]; exact Set.singleton_nonempty _
            · intro h
              obtain ⟨xb, yb, hx, hy, hz, he⟩ := hqual s
              refine ⟨xb, yb, hx, hy, ?_, ?_⟩
              · simpa [zeroTreeModel] using hz
              · simpa [hf] using he
          have hprob : IsProbabilityMeasure zeroLaw := by
            constructor
            norm_num [zeroLaw, Measure.add_apply, Measure.smul_apply]
            exact ENNReal.inv_two_add_inv_two
          have hmass : ∀ k (b : Bool), zeroLaw {ω | repeatedSample (k+1) ω = b} = (1/2 : ℝ≥0∞) := by
            intro k b
            cases b <;> norm_num [zeroLaw, repeatedSample, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
          have hbot : ∀ ω k, zeroApprox ω k (.middle (!ω)) = ⊥ := by
            intro ω k
            cases ω <;> simp [zeroApprox]
          have hrec : ∀ ω, IsZeroAlgorithm3Run (fun k => repeatedSample k ω) (zeroApprox ω) := by
            intro ω
            refine ⟨rfl, ?_, ?_, ?_, ?_⟩
            · intro b; simp [zeroApprox]
            · intro k b; rfl
            · intro k b
              cases k <;> cases ω <;> cases b <;> simp [zeroApprox, repeatedSample]
            · intro k
              cases k <;> cases ω <;> norm_num [zeroApprox, EReal.coe_mul_bot_of_pos]
          have hnon : ¬ Tendsto (fun _ : ℕ => (⊥ : EReal)) atTop (𝓝 0) := by
            simp [tendsto_const_nhds_iff]
          letI : IsProbabilityMeasure zeroLaw := hprob
          have hind : iIndepFun (fun k : ℕ => fun ω : Bool => zeroSelected (k+1) ω (.leaf (repeatedSample (k+1) ω))) zeroLaw := by
            have he : (fun k : ℕ => fun ω : Bool => zeroSelected (k+1) ω (.leaf (repeatedSample (k+1) ω))) =
                (fun _ : ℕ => fun _ : Bool => (1 : ℝ)) := by
              funext k ω
              simp [zeroSelected]
            rw [he, iIndepFun_iff_measure_inter_preimage_eq_mul]
            intro S sets hm
            by_cases hall : ∀ i ∈ S, (1 : ℝ) ∈ sets i
            · have hi : (⋂ i ∈ S, (fun _ : Bool => (1 : ℝ)) ⁻¹' sets i) = Set.univ := by
                ext w
                simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
                exact hall
              rw [hi, measure_univ]
              symm
              apply Finset.prod_eq_one
              intro i hi
              rw [Set.preimage_const_of_mem (hall i hi), measure_univ]
            · push_neg at hall
              obtain ⟨i, hi, hn⟩ := hall
              have he : (⋂ i ∈ S, (fun _ : Bool => (1 : ℝ)) ⁻¹' sets i) = ∅ := by
                apply Set.eq_empty_iff_forall_notMem.mpr
                intro w hw
                exact hn (Set.mem_iInter.mp (Set.mem_iInter.mp hw i) hi)
              rw [he, measure_empty]
              symm
              apply Finset.prod_eq_zero hi
              rw [Set.preimage_const_of_notMem hn, measure_empty]
          have hnotind : ¬ iIndepFun (fun k : ℕ => repeatedSample (k+1)) zeroLaw := by
            intro h
            have hh := (h.indepFun (show (0 : ℕ) ≠ 1 by decide)).measure_inter_preimage_eq_mul
              {false} {false} (by trivial) (by trivial)
            have he : zeroLaw {ω | ω = false} = (1/2 : ℝ≥0∞) := hmass 0 false
            change zeroLaw ({false} ∩ {false}) = zeroLaw {false} * zeroLaw {false} at hh
            rw [Set.inter_self] at hh
            have he' : zeroLaw {false} = (1/2 : ℝ≥0∞) := he
            rw [he'] at hh
            have hc := congrArg ENNReal.toReal hh
            norm_num at hc
          have hQaux : ∀ r s (ν : ZeroLevel s) z, zeroTreeModel.Qaux r s ν z = 0 := by
            intro r
            induction r with
            | zero => intros; rfl
            | succ r ih =>
              intro s ν z
              have ih' : ∀ s ν, zeroTreeModel.Qaux r s ν = fun _ => 0 := fun s ν => funext (ih s ν)
              simp only [TreeModel.Qaux, ih', hsv, hrho]
              simp [TreeModel.wsum]
          have hQ : ∀ s, s < 3 → ∀ ν : ZeroLevel s, ∀ z, zeroTreeModel.Q s ν z = 0 := by
            intros; apply hQaux
          have hQ1 : zeroTreeModel.Q1 = 0 := by
            unfold TreeModel.Q1
            have he : zeroTreeModel.Q 0 zeroTreeModel.first = fun _ => 0 := funext (hQ 0 (by decide) _)
            rw [he, hsv]
          let e0 : Bool ≃ zeroTreeModel.Child 0 () :=
            { toFun := fun b => ⟨b, rfl⟩
              invFun := fun m => m.val
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          have hsum0 : ∀ {M : Type} [AddCommMonoid M] (f : zeroTreeModel.Child 0 () → M),
              ∑ m, f m = f ⟨true, rfl⟩ + f ⟨false, rfl⟩ := by
            intro M _ f
            simpa [e0] using (Fintype.sum_equiv e0 (fun b => f (e0 b)) f (fun _ => rfl)).symm
          have hu1 : ∀ b : Bool, Unique (zeroTreeModel.Child 1 b) := by
            intro b
            refine ⟨⟨⟨b, rfl⟩⟩, ?_⟩
            intro m
            apply Subtype.ext
            exact m.property
          have hp0 : ∀ ω, zeroPath ω ⟨0, by decide⟩ = () := by intro ω; rfl
          have hp1 : ∀ ω, zeroPath ω ⟨1, by decide⟩ = ω := by intro ω; rfl
          have hc0 : Fintype.card (zeroTreeModel.Child 0 ()) = 2 := by
            simpa using Fintype.card_congr e0.symm
          have hst : ∀ ω k s (ν : ZeroLevel s) x,
              zeroTreeModel.stageVal s ν ((zeroTreeRun ω).Qm k s ν) x =
                zeroApprox ω k (zeroNodeAt s ν) := by
            intro ω k s ν x
            exact hsv s ν _ x
          have hphi : ∀ s (ν : ZeroLevel s) m, zeroTreeModel.Φ s ν m = if s = 0 then 1 / 2 else 1 := by
            intros; rfl
          have hpr : ∀ s (ν : ZeroLevel s), zeroTreeModel.Prisk s ν = {fun _ => 1} := by
            intros; rfl
          have hstanding : zeroTreeModel.Standing := by
            unfold TreeModel.Standing
            intro s hs ν
            have hs' : s ≤ 1 := by omega
            interval_cases s
            · cases ν
              refine ⟨⟨⟨false, rfl⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
              · intro m; change (0 : ℝ) < 1 / 2; norm_num
              · rw [hsum0]; norm_num only [hphi, one_mul, if_pos rfl]; norm_num
              · exact Set.singleton_nonempty _
              · exact convex_singleton _
              · intro a ha
                have ha' : a = fun _ => 1 := ha
                subst a
                constructor
                · intro m; norm_num
                · rw [hsum0]; norm_num only [hphi, one_mul, if_pos rfl]; norm_num
            · letI := hu1 ν
              refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
              · intro m; change (0 : ℝ) < 1; norm_num
              · rw [Fintype.sum_unique]; norm_num [hphi]
              · exact Set.singleton_nonempty _
              · exact convex_singleton _
              · intro a ha
                have ha' : a = fun _ => 1 := ha
                subst a
                constructor
                · intro m; norm_num
                · rw [Fintype.sum_unique]; norm_num [hphi]
          refine ⟨hH2, hH2t, hstanding, hprob, fun _ => measurable_id, hmass,
            fun _ _ => rfl, by simp [zeroSelected], hind, hnotind, hrec,
            ?_, hQ, hQ1, ?_, ?_⟩
          · intro ω
            unfold TreeModel.IsRun3
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro s hs ν
              have hs' : s ≤ 1 := by omega
              interval_cases s <;> rfl
            · intro k s hs ν
              have : s = 2 := by omega
              subst s
              exact ⟨rfl, rfl, rfl⟩
            · intro k s hs ν
              dsimp only
              refine ⟨rfl, ?_, ?_⟩
              · rw [hf]; exact Set.mem_singleton 0
              · intro z hz
                rw [hf] at hz
                have : z = 0 := hz
                subst z
                exact le_rfl
            · intro k s hs ν
              have hs' : s ≤ 1 := by omega
              interval_cases s
              · cases ν
                simp only [hp0, if_pos rfl, hst, hrho]
                simp only [zeroTreeRun, zeroTreeRules]
                simp only [TreeModel.wsum, hsum0]
                cases k <;> cases ω <;>
                  norm_num [hphi, hpr, zeroNodeAt, zeroApprox, ESubdiff, hsv,
                    EReal.coe_mul_bot_of_pos]
              · simp only [hp1]
                cases ν <;> cases ω <;> cases k <;>
                  simp [zeroTreeRun, zeroTreeRules, zeroPath, TreeModel.stageVal, TreeModel.feas,
                    zeroTreeModel, zeroNodeAt, zeroApprox, ESubdiff, TreeModel.rho, TreeModel.wsum,
                    iSup_singleton, Set.mem_singleton_iff, Fin.cases, Fin.induction]
          · intro ω
            constructor
            · have he : (fun k => (zeroTreeRun ω).Qm k 1 (!ω) ((zeroTreeRun ω).hist zeroTreeModel k 1 (!ω)) -
                  zeroTreeModel.Q 1 (!ω) ((zeroTreeRun ω).hist zeroTreeModel k 1 (!ω))) = (fun _ => (⊥ : EReal)) := by
                funext k
                rw [hQ 1 (by decide)]
                change zeroApprox ω k (.middle (!ω)) - 0 = ⊥
                rw [hbot, sub_zero]
              rw [he]
              exact hnon
            · simpa only [zeroTreeRun, zeroNodeAt, zeroApprox, hsv, hQ1] using hnon
          · intro ω
            exact ⟨hbot ω, by simpa only [hbot, zeroTrueValue, sub_zero] using hnon,
              by simpa only [zeroApprox, zeroTrueValue] using hnon⟩
