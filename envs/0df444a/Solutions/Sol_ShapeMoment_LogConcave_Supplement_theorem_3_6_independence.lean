-- Prove2me | solution 1 for ShapeMoment.LogConcave.Supplement.theorem_3_6_independence
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:06.741245+00:00
-- url     : https://prove2.me/submissions/fac51048-d9ba-4810-a847-3b19f32eb767

import Definitions.Def_ShapeMoment_LogConcave_ReverseConvex
import Definitions.Def_ShapeMoment_LogConcave_Supplement_ActiveGradients

open ShapeMoment
open ShapeMoment.LogConcave
open ShapeMoment.LogConcave.Supplement

theorem solution (n m P : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : (Fin n → ℝ) → ℝ)
    (f : Fin P → (Fin n → ℝ) → ℝ)
    (hc : Continuous c) (hqc : QuasiconcaveOn ℝ Set.univ c)
    (hrank : A.rank = m) (hfdiff : ∀ p, Differentiable ℝ (f p))
    (hrc : ∀ p, Convex ℝ {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧ 0 < f p x})
    (hne : (revCvxFeasible A b f).Nonempty)
    (hcompact : IsCompact (revCvxFeasible A b f)) :
    ∀ x ∈ (revCvxFeasible A b f).extremePoints ℝ,
      IsMinOn c (revCvxFeasible A b f) x →
      (∀ p, f p x = 0 →
        restrictTo (supportSet x) (grad (f p) x) ∉ rowSpanOn A (supportSet x)) →
      ∃ s : Finset (Fin n → ℝ), (↑s : Set (Fin n → ℝ)) ⊆ activeVectors f x ∧
        s.card = n - m ∧
        LinearIndependent ℝ (fun v : (↑s : Set (Fin n → ℝ)) => (v : Fin n → ℝ)) := by
          classical
          intro x hx hmin hreg
          have hx0 : ∀ j, 0 ≤ x j := hx.1.1
          have hxA : A.mulVec x = b := hx.1.2.1
          have hxf : ∀ p, f p x ≤ 0 := hx.1.2.2
          let S := supportSet x
          let E := S → ℝ
          let e : E →ₗ[ℝ] (Fin n → ℝ) :=
            { toFun := fun u j => if h : j ∈ S then u ⟨j, h⟩ else 0
              map_add' := by intros; ext j; dsimp; split <;> first | rfl | simp
              map_smul' := by intros; ext j; dsimp; split <;> first | rfl | simp }
          let ec : E →L[ℝ] (Fin n → ℝ) := e.toContinuousLinearMap
          let a : E := restrictTo S x
          have hea : e a = x := by
            ext j
            dsimp [e, a, restrictTo]
            split
            · rfl
            · rename_i hj
              have : ¬ 0 < x j := hj
              linarith [hx0 j]
          have he_single (j : S) : e (Pi.single j 1) = Pi.single (j : Fin n) 1 := by
            ext k
            dsimp [e]
            split
            · rename_i hk
              by_cases h : k = j
              · subst k; simp
              · have : (⟨k, hk⟩ : S) ≠ j := fun h' => h (congrArg Subtype.val h')
                simp [h, this]
            · rename_i hk
              have : k ≠ j := by rintro rfl; exact hk j.property
              simp [this]
          let Q : Set E := {u | ∀ j, 0 < u j}
          have hQopen : IsOpen Q := by
            change IsOpen {u : E | ∀ j, u j ∈ Set.Ioi (0 : ℝ)}
            rw [Set.ofPred_forall]
            exact isOpen_iInter_of_finite (fun j : S => isOpen_Ioi.preimage (continuous_apply j))
          have haQ : a ∈ Q := fun j => j.property
          have hQconv : Convex ℝ Q := by
            intro u hu v hv r t hr ht hrt j
            change 0 < r * u j + t * v j
            by_cases h : r = 0
            · have : t = 1 := by linarith
              simp [h, this, hv j]
            · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hr (Ne.symm h)) (hu j))
                (mul_nonneg ht (le_of_lt (hv j)))
          have boundary : ∀ (g : E → ℝ) (D : E →L[ℝ] ℝ),
              Continuous g → HasFDerivAt g D a → g a = 0 → D ≠ 0 →
              Convex ℝ (Q ∩ {u | 0 < g u}) →
              ∀ y ∈ Q, D (y - a) = 0 → g y ≤ 0 := by
            intro g D hg hd hga hD hC y hy hDy
            let C : Set E := Q ∩ {u | 0 < g u}
            have hCo : IsOpen C := hQopen.inter (isOpen_lt continuous_const hg)
            have hac : a ∈ closure C := by
              by_contra ha
              have hmax : IsLocalMax g a := by
                filter_upwards [hQopen.mem_nhds haQ, isOpen_compl_iff.mpr isClosed_closure |>.mem_nhds ha] with z hzQ hz
                rw [hga]
                by_contra h
                exact hz (subset_closure ⟨hzQ, lt_of_not_ge h⟩)
              exact hD (hmax.hasFDerivAt_eq_zero hd)
            have hnonneg : ∀ z ∈ closure C, 0 ≤ g z := by
              intro z hz
              have hs : closure C ⊆ {z | 0 ≤ g z} :=
                closure_minimal (fun z hz => show 0 ≤ g z from le_of_lt hz.2) (isClosed_le continuous_const hg)
              exact hs hz
            have hsupp : ∀ z ∈ closure C, 0 ≤ D (z - a) := by
              intro z hz
              have hm : IsLocalMinOn g (closure C) a := by
                apply IsMinOn.localize
                intro w hw
                rw [hga]
                exact hnonneg w hw
              exact hm.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
                (sub_mem_posTangentConeAt_of_segment_subset (hC.closure.segment_subset hac hz))
            by_contra hgy
            have hyC : y ∈ C := ⟨hy, lt_of_not_ge hgy⟩
            have hm : IsLocalMin (fun z => D (z - a)) y := by
              filter_upwards [hCo.mem_nhds hyC] with z hz
              rw [hDy]
              exact hsupp z (subset_closure hz)
            have hd' : HasFDerivAt (fun z => D (z - a)) D y := by
              exact D.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const a) |>.congr_fderiv (by ext z; rfl)
            exact hD (hm.hasFDerivAt_eq_zero hd')
          have hactive : ∀ p, f p x = 0 → ∀ y : E, y ∈ Q →
              fderiv ℝ (f p) x (e y - x) = 0 → f p (e y) ≤ 0 := by
            intro p hp y hy hdy
            let g : E → ℝ := fun u => f p (e u)
            let D : E →L[ℝ] ℝ := (fderiv ℝ (f p) x).comp ec
            have hd : HasFDerivAt g D a := by
              have hh : HasFDerivAt (f p) (fderiv ℝ (f p) x) (ec a) := by
                change HasFDerivAt (f p) (fderiv ℝ (f p) x) (e a)
                rw [hea]
                exact (hfdiff p x).hasFDerivAt
              exact hh.comp a ec.hasFDerivAt
            have hD : D ≠ 0 := by
              intro hzero
              apply hreg p hp
              have hgzero : restrictTo S (grad (f p) x) = 0 := by
                ext j
                have hh := congrArg (fun L : E →L[ℝ] ℝ => L (Pi.single j 1)) hzero
                simpa [D, ec, grad, restrictTo, he_single] using hh
              rw [hgzero]
              exact Submodule.zero_mem _
            apply boundary g D ((hfdiff p).continuous.comp ec.continuous) hd (by simpa [g, hea] using hp) hD ?_ y hy ?_
            · intro u hu v hv r t hr ht hrt
              refine ⟨hQconv hu.1 hv.1 hr ht hrt, ?_⟩
              have hu0 : ∀ j, 0 ≤ e u j := by
                intro j; dsimp [e]; split <;> simp [le_of_lt (hu.1 _)]
              have hv0 : ∀ j, 0 ≤ e v j := by
                intro j; dsimp [e]; split <;> simp [le_of_lt (hv.1 _)]
              have hh := hrc p ⟨hu0, hu.2⟩ ⟨hv0, hv.2⟩ hr ht hrt
              simpa [g, map_add, map_smul] using hh.2
            · simpa [D, ec, map_sub, hea] using hdy
          have hpair : ∀ (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) (v : Fin n → ℝ),
              L v = ∑ j, v j * L (Pi.single j 1) := by
            intro L v
            have hv : (∑ j, v j • Pi.single j (1 : ℝ)) = v := by
              ext j
              simp [Finset.sum_apply, Pi.single_apply]
            rw [← hv, map_sum]
            simp only [map_smul, smul_eq_mul]
            congr 1
            funext j
            rw [hv]
          let V := Submodule.span ℝ (activeVectors f x)
          let R := Submodule.span ℝ (Set.range fun i : Fin m => A i)
          have hspan : V ⊔ R = ⊤ := by
            by_contra htop
            obtain ⟨L, hL, hLV⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
              (lt_top_iff_ne_top.mpr htop) (inferInstance : Module.Projective ℝ ((Fin n → ℝ) ⧸ (V ⊔ R)))
            let d : Fin n → ℝ := fun j => L (Pi.single j 1)
            have hLd : ∀ v, L v = ∑ j, v j * d j := hpair L
            have hdne : d ≠ 0 := by
              intro hd
              apply hL
              ext v
              simp [hLd, hd]
            have hkill : ∀ v ∈ V ⊔ R, L v = 0 := by
              intro v hv
              have : L v ∈ (V ⊔ R).map L := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
              rwa [hLV, Submodule.mem_bot] at this
            have hkillactive : ∀ v ∈ activeVectors f x, L v = 0 := by
              intro v hv
              exact hkill v (Submodule.mem_sup_left (Submodule.subset_span hv))
            have hdzero : ∀ j, x j = 0 → d j = 0 := by
              intro j hj
              exact hkillactive _ (Or.inr ⟨j, hj, rfl⟩)
            have hdA : A.mulVec d = 0 := by
              ext i
              change (∑ j, A i j * d j) = 0
              rw [← hLd]
              exact hkill _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
            have hdf : ∀ p, f p x = 0 → fderiv ℝ (f p) x d = 0 := by
              intro p hp
              have hh := hkillactive _ (Or.inl ⟨p, hp, rfl⟩)
              rw [hLd] at hh
              change (fderiv ℝ (f p) x).toLinearMap d = 0
              rw [hpair (fderiv ℝ (f p) x).toLinearMap d]
              calc
                (∑ j, d j * (fderiv ℝ (f p) x).toLinearMap (Pi.single j 1)) =
                    ∑ j, grad (f p) x j * d j := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
                _ = 0 := hh
            let ds : E := restrictTo S d
            have heds : e ds = d := by
              ext j
              dsimp [e, ds, restrictTo]
              split
              · rfl
              · rename_i hj
                have hj0 : x j = 0 := by
                  have : ¬ 0 < x j := hj
                  linarith [hx0 j]
                exact (hdzero j hj0).symm
            let line : ℝ → E := fun t => a + t • ds
            have hline : Continuous line := by unfold line; fun_prop
            have hnearQ : ∀ᶠ t : ℝ in nhds 0, line t ∈ Q := by
              apply hline.continuousAt.preimage_mem_nhds
              simpa [line] using hQopen.mem_nhds haQ
            have hnearF : ∀ᶠ t : ℝ in nhds 0, ∀ p, f p x ≠ 0 → f p (e (line t)) < 0 := by
              rw [Filter.eventually_all]
              intro p
              by_cases hp : f p x = 0
              · exact Filter.Eventually.of_forall (fun t h => (h hp).elim)
              · have hc' : Continuous (fun t => f p (e (line t))) :=
                  (hfdiff p).continuous.comp (ec.continuous.comp hline)
                have hneg : f p (e (line 0)) < 0 := by
                  simpa [line, hea] using lt_of_le_of_ne (hxf p) hp
                filter_upwards [hc'.continuousAt.eventually (gt_mem_nhds hneg)] with t ht
                exact fun _ => ht
            have hnear : ∀ᶠ t : ℝ in nhds 0, e (line t) ∈ revCvxFeasible A b f := by
              filter_upwards [hnearQ, hnearF] with t htQ htF
              have heline : e (line t) = x + t • d := by simp [line, map_add, map_smul, hea, heds]
              refine ⟨?_, ?_, ?_⟩
              · intro j
                dsimp [e]
                split
                · exact le_of_lt (htQ _)
                · rfl
              · rw [heline, Matrix.mulVec_add, Matrix.mulVec_smul, hxA, hdA, smul_zero, add_zero]
              · intro p
                by_cases hp : f p x = 0
                · apply hactive p hp (line t) htQ
                  rw [heline, add_sub_cancel_left, map_smul, hdf p hp, smul_zero]
                · exact le_of_lt (htF p hp)
            have hboth : ∀ᶠ t : ℝ in nhds 0,
                e (line t) ∈ revCvxFeasible A b f ∧ e (line (-t)) ∈ revCvxFeasible A b f :=
              hnear.and ((show Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) from
                by simpa using continuous_neg.tendsto (0 : ℝ)).eventually hnear)
            obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hboth
            let t : ℝ := ε / 2
            have htpos : 0 < t := by dsimp [t]; positivity
            have ht : e (line t) ∈ revCvxFeasible A b f ∧ e (line (-t)) ∈ revCvxFeasible A b f := by
              apply hball
              change dist t 0 < ε
              rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
              dsimp [t]; linarith
            have hseg : x ∈ openSegment ℝ (e (line t)) (e (line (-t))) := by
              refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
              simp only [line, map_add, map_smul, hea, heds]
              ext j
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
            have heq := hx.2 ht.1 ht.2 hseg
            have htd : t • d = 0 := by
              have hh : x + t • d = x := by simpa [line, map_add, map_smul, hea, heds] using heq
              exact add_left_cancel (hh.trans (add_zero x).symm)
            exact hdne ((smul_eq_zero.mp htd).resolve_left (ne_of_gt htpos))
          have hdim : n - m ≤ Module.finrank ℝ V := by
            have hh := Submodule.finrank_add_le_finrank_add_finrank V R
            have hr : Module.finrank ℝ R = m := by
              rw [← hrank, Matrix.rank_eq_finrank_span_row]
              rfl
            rw [hspan, finrank_top, Module.finrank_pi, Fintype.card_fin, hr] at hh
            omega
          obtain ⟨s, hs, hcard, hsspan, hli⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ (activeVectors f x)
          obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (hcard ▸ hdim)
          exact ⟨t, fun v hv => hs (hts hv), htcard, hli.mono (by exact_mod_cast hts)⟩
