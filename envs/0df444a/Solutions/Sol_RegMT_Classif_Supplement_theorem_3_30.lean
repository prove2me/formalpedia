-- Prove2me | solution 1 for RegMT.Classif.Supplement.theorem_3_30
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:24.49705+00:00
-- url     : https://prove2.me/submissions/61603cec-472b-4962-a786-4aeac3f5dc17

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Neural

open scoped ENNReal

open RegMT
open RegMT.Classif
open RegMT.Classif.Supplement

/-- Corrected for arbitrary final-layer scalar norm; see DISPROOF.md. -/
theorem solution {M : ℕ} (hM : 0 < M) (A : Layers M)
    [MeasurableSpace (A.Space 0)] [BorelSpace (A.Space 0)] {N : ℕ} (hN : 0 < N)
    (X : Set (A.Space 0)) (hX : MeasurableSet X) (x : Fin N → A.Space 0) (hx : ∀ i, x i ∈ X)
    (L : ℝ → ℝ) (hconvex : ConvexOn ℝ Set.univ L) (hnonneg : ∀ t, 0 ≤ L t)
    (hlip : ∃ K, LipschitzWith K L) (κ : ℝ≥0∞) (hκ : 0 < κ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ (Y : Set ℝ), MeasurableSet Y → ∀ y : Fin N → ℝ, (∀ i, y i ∈ Y) →
      (⨅ W : Weights A, neuralRegRisk A X Y x y L κ ρ W) ≤
        ⨅ W : Weights A, neuralRegBound A x y L κ ρ W) ∧
    (∀ y : Fin N → Bool,
      (⨅ W : Weights A, neuralClassRisk A X x y L κ ρ W) ≤
        ⨅ W : Weights A, neuralClassBound A X x y L κ ρ W) := by
          open MeasureTheory DRLogReg.Reformulation WassersteinDRO.Duality in (
          have core : ∀ {Z : Type} [MeasurableSpace Z] (π : Measure (Z × Z)) (ℓ : Z → ℝ≥0∞)
              (c : Z → Z → ℝ≥0∞) (S : Set Z) (K : ℝ≥0∞), Measurable ℓ →
              Measurable (fun p : Z × Z => c p.1 p.2) → MeasurableSet S →
              (π.map Prod.snd) Sᶜ = 0 →
              (∀ z1 z2, z2 ∈ S → c z1 z2 ≠ ⊤ → ℓ z1 ≤ ℓ z2 + K * c z1 z2) →
              ∫⁻ p, c p.1 p.2 ∂π ≠ ⊤ →
              ∫⁻ z, ℓ z ∂(π.map Prod.fst) ≤ ∫⁻ z, ℓ z ∂(π.map Prod.snd) + K * ∫⁻ p, c p.1 p.2 ∂π := by
            intro Z _ π ℓ c S K hℓ hc hS hP h hfin
            have hS' : ∀ᵐ p ∂π, p.2 ∈ S := by
              rw [Measure.map_apply measurable_snd hS.compl] at hP
              rw [ae_iff]; exact hP
            have hlt := ae_lt_top hc hfin
            calc _ ≤ ∫⁻ p, ℓ p.1 ∂π := lintegral_map_le _ _
              _ ≤ ∫⁻ p, (ℓ p.2 + K * c p.1 p.2) ∂π := by
                  apply lintegral_mono_ae
                  filter_upwards [hS', hlt] with p h1 h2
                  exact h _ _ h1 h2.ne
              _ = _ := by
                  rw [lintegral_add_left (f := fun p : Z × Z => ℓ p.2) (hℓ.comp measurable_snd), lintegral_const_mul _ hc,
                    lintegral_map hℓ measurable_snd]
          have gen : ∀ {Z : Type} [MeasurableSpace Z] [TopologicalSpace Z] [OpensMeasurableSpace Z]
              [MeasurableSingletonClass Z]
              (Q P : Measure Z) (c : Z → Z → ℝ≥0∞) (S : Set Z) (ℓ : Z → ℝ) (K : ℝ≥0∞) (ρ : ℝ),
              0 ≤ ρ → Continuous ℓ → (∀ z, 0 ≤ ℓ z) → Measurable (fun p : Z × Z => c p.1 p.2) →
              S.Finite → P Sᶜ = 0 →
              (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ π : Measure (Z × Z), π.map Prod.fst = Q ∧
                π.map Prod.snd = P ∧ ∫⁻ p, c p.1 p.2 ∂π < ENNReal.ofReal ρ + ε) →
              (∀ z1 z2, z2 ∈ S → c z1 z2 ≠ ⊤ →
                ENNReal.ofReal (ℓ z1) ≤ ENNReal.ofReal (ℓ z2) + K * c z1 z2) →
              (∀ F : Set Z, IsClosed F → ∀ s ∈ S, s ∉ F →
                ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ ≠ ⊤ ∧ ∀ z ∈ F, δ ≤ c z s) →
              ∫⁻ z, ENNReal.ofReal (ℓ z) ∂Q ≤
                ∫⁻ z, ENNReal.ofReal (ℓ z) ∂P + ENNReal.ofReal ρ * K := by
            intro Z _ _ _ _ Q P c S ℓ K ρ hρ hℓc hℓnn hc hSfin hP hcoup hh hδ
            have hSm : MeasurableSet S := hSfin.measurableSet
            have hℓm : Measurable ℓ := hℓc.measurable
            have hℓm' : Measurable (fun z => ENNReal.ofReal (ℓ z)) := hℓm.ennreal_ofReal
            have step : ∀ (g : Z → ℝ≥0∞) (K' : ℝ≥0∞), Measurable g →
                (∀ z1 z2, z2 ∈ S → c z1 z2 ≠ ⊤ → g z1 ≤ g z2 + K' * c z1 z2) →
                ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ⊤ →
                ∫⁻ z, g z ∂Q ≤ ∫⁻ z, g z ∂P + K' * (ENNReal.ofReal ρ + ε) := by
              intro g K' hg hgK ε hε hε'
              obtain ⟨π, h1, h2, h3⟩ := hcoup ε hε
              have hfin : ∫⁻ p, c p.1 p.2 ∂π ≠ ⊤ :=
                (h3.trans (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hε'.lt_top⟩)).ne
              have := core π g c S K' hg hc hSm (by rw [h2]; exact hP) hgK hfin
              rw [h1, h2] at this
              exact this.trans (by gcongr)
            rcases eq_or_lt_of_le hρ with hρ0 | hρpos
            · subst hρ0
              simp only [ENNReal.ofReal_zero, zero_mul, add_zero]
              have hclosed : ∀ F : Set Z, IsClosed F → Q F ≤ P F := by
                intro F hF
                have hδs : ∀ s, ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ ≠ ⊤ ∧ (s ∈ S → s ∉ F → ∀ z ∈ F, δ ≤ c z s) := by
                  intro s
                  by_cases h : s ∈ S ∧ s ∉ F
                  · obtain ⟨δ, a, b, d⟩ := hδ F hF s h.1 h.2
                    exact ⟨δ, a, b, fun _ _ => d⟩
                  · exact ⟨1, one_ne_zero, ENNReal.one_ne_top, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
                choose d hd0 hdt hd using hδs
                set δ : ℝ≥0∞ := min 1 (hSfin.toFinset.inf d) with hδdef
                have hδ0 : δ ≠ 0 := by
                  apply ne_of_gt
                  apply lt_min zero_lt_one
                  rw [Finset.lt_inf_iff (by simp)]
                  intro s _; exact pos_iff_ne_zero.2 (hd0 s)
                have hδt : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
                have hδle : ∀ s ∈ S, s ∉ F → ∀ z ∈ F, δ ≤ c z s := by
                  intro s hs hsF z hz
                  exact (min_le_of_right_le (Finset.inf_le (hSfin.mem_toFinset.2 hs))).trans
                    (hd s hs hsF z hz)
                have hind : Measurable (F.indicator (1 : Z → ℝ≥0∞)) :=
                  measurable_const.indicator hF.measurableSet
                have hstep := step (F.indicator 1) δ⁻¹ hind (by
                  intro z1 z2 hz2 _
                  by_cases h1 : z1 ∈ F
                  · by_cases h2 : z2 ∈ F
                    · simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
                    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, zero_add]
                      calc (1 : Z → ℝ≥0∞) z1 = δ⁻¹ * δ := by
                            simp [ENNReal.inv_mul_cancel hδ0 hδt]
                        _ ≤ δ⁻¹ * c z1 z2 := by gcongr; exact hδle z2 hz2 h2 z1 h1
                  · simp [Set.indicator_of_notMem h1])
                rw [← lintegral_indicator_one hF.measurableSet, ← lintegral_indicator_one hF.measurableSet]
                apply ENNReal.le_of_forall_pos_le_add
                intro η hη _
                have := hstep (δ * η) (mul_ne_zero hδ0 (by exact_mod_cast hη.ne'))
                  (ENNReal.mul_ne_top hδt ENNReal.coe_ne_top)
                rw [ENNReal.ofReal_zero, zero_add, ← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδt,
                  one_mul] at this
                exact this
              rw [lintegral_eq_lintegral_meas_le Q (ae_of_all _ hℓnn) hℓm.aemeasurable,
                lintegral_eq_lintegral_meas_le P (ae_of_all _ hℓnn) hℓm.aemeasurable]
              apply lintegral_mono; intro t
              exact hclosed _ (isClosed_le continuous_const hℓc)
            · by_cases hK : K = ⊤
              · rw [hK, ENNReal.mul_top (ENNReal.ofReal_pos.2 hρpos).ne']; simp
              · apply ENNReal.le_of_forall_pos_le_add
                intro η hη _
                by_cases hK0 : K = 0
                · have := step _ K hℓm' hh 1 one_ne_zero ENNReal.one_ne_top
                  rw [hK0] at this ⊢; simp only [zero_mul, mul_zero, add_zero] at this ⊢
                  exact this.trans le_self_add
                · have hηK : (η : ℝ≥0∞) / K ≠ 0 := by
                    simp [ENNReal.div_eq_zero_iff, hK, hη.ne']
                  have hηK' : (η : ℝ≥0∞) / K ≠ ⊤ := (ENNReal.div_lt_top ENNReal.coe_ne_top hK0).ne
                  have := step _ K hℓm' hh _ hηK hηK'
                  rw [mul_add, ENNReal.mul_div_cancel hK0 hK] at this
                  calc _ ≤ _ := this
                    _ = _ := by ring
          have hdivle : ∀ (a b : ℝ) (Mod : ℝ≥0∞), 0 ≤ a → 0 < b → ENNReal.ofReal (a / b) ≤ Mod →
              ENNReal.ofReal a ≤ Mod * ENNReal.ofReal b := by
            intro a b Mod ha hb h
            have : ENNReal.ofReal a = ENNReal.ofReal (a / b) * ENNReal.ofReal b := by
              rw [← ENNReal.ofReal_mul (div_nonneg ha hb.le), div_mul_cancel₀ _ hb.ne']
            rw [this]; gcongr
          have hact : ∀ (m : Fin M) (u u' : A.Space (m.val + 1)),
              ENNReal.ofReal ‖A.activation m u - A.activation m u'‖ ≤
                activationModulus A m * ENNReal.ofReal ‖u - u'‖ := by
            intro m u u'
            by_cases h : u = u'
            · subst h; simp
            · apply hdivle _ _ _ (norm_nonneg _) (norm_pos_iff.2 (sub_ne_zero.2 h))
              unfold activationModulus
              exact le_iSup_of_le u (le_iSup_of_le u' (le_iSup_of_le h le_rfl))
          have hLip : ∀ (L : ℝ → ℝ) (a b : ℝ),
              ENNReal.ofReal |L a - L b| ≤ lipschitzModulus L * ENNReal.ofReal |a - b| := by
            intro L a b
            by_cases h : a = b
            · subst h; simp
            · have := hdivle |L a - L b| ‖a - b‖ (lipschitzModulus L) (abs_nonneg _)
                (norm_pos_iff.2 (sub_ne_zero.2 h))
                (by unfold lipschitzModulus
                    exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le h le_rfl)))
              simpa [Real.norm_eq_abs] using this
          have hcontState : ∀ (W : Weights A) (m : ℕ), Continuous (netState A W m) := by
            intro W m
            induction m with
            | zero => exact continuous_id
            | succ m ih =>
              by_cases hm : m < M
              · have : netState A W (m + 1) = fun x =>
                    A.activation ⟨m, hm⟩ (W ⟨m, hm⟩ (netState A W m x)) := by
                  funext x; simp [netState, hm]
                rw [this]
                exact (A.continuous_activation _).comp ((W _).continuous.comp ih)
              · have : netState A W (m + 1) = fun x => 0 := by
                  funext x; simp [netState, hm]
                rw [this]; exact continuous_const
          have hcontNet : ∀ W : Weights A, Continuous (network A W) := fun W =>
            A.output.continuous.comp (hcontState W M)
          have hlipState : ∀ (W : Weights A) (m : ℕ), m ≤ M → ∀ x x' : A.Space 0,
              ENNReal.ofReal ‖netState A W m x - netState A W m x'‖ ≤
                (∏ k ∈ Finset.univ.filter (fun k : Fin M => k.val < m),
                  activationModulus A k * ENNReal.ofReal ‖W k‖) * ENNReal.ofReal ‖x - x'‖ := by
            intro W m
            induction m with
            | zero => intro _ x x'; simp [netState]
            | succ m ih =>
              intro hmM x x'
              have hm : m < M := hmM
              have hfil : Finset.univ.filter (fun k : Fin M => k.val < m + 1) =
                  insert ⟨m, hm⟩ (Finset.univ.filter (fun k : Fin M => k.val < m)) := by
                ext k; simp [Fin.ext_iff]; omega
              have hnot : (⟨m, hm⟩ : Fin M) ∉ Finset.univ.filter (fun k : Fin M => k.val < m) := by
                simp
              rw [hfil, Finset.prod_insert hnot]
              have hst : ∀ y, netState A W (m + 1) y =
                    A.activation ⟨m, hm⟩ (W ⟨m, hm⟩ (netState A W m y)) := by
                intro y; simp [netState, hm]
              rw [hst, hst]
              calc _ ≤ activationModulus A ⟨m, hm⟩ *
                    ENNReal.ofReal ‖W ⟨m, hm⟩ (netState A W m x) - W ⟨m, hm⟩ (netState A W m x')‖ :=
                    hact _ _ _
                _ ≤ activationModulus A ⟨m, hm⟩ * (ENNReal.ofReal ‖W ⟨m, hm⟩‖ *
                    ENNReal.ofReal ‖netState A W m x - netState A W m x'‖) := by
                  gcongr
                  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← map_sub]
                  exact ENNReal.ofReal_le_ofReal ((W _).le_opNorm _)
                _ ≤ activationModulus A ⟨m, hm⟩ * (ENNReal.ofReal ‖W ⟨m, hm⟩‖ *
                    ((∏ k ∈ Finset.univ.filter (fun k : Fin M => k.val < m),
                    activationModulus A k * ENNReal.ofReal ‖W k‖) * ENNReal.ofReal ‖x - x'‖)) := by
                  gcongr; exact ih (by omega) x x'
                _ = _ := by ring
          have hlipNet : ∀ (W : Weights A) (x x' : A.Space 0),
              ENNReal.ofReal |network A W x - network A W x'| ≤
                outputProduct A W * ENNReal.ofReal ‖x - x'‖ := by
            intro W x x'
            have h1 := hlipState W M le_rfl x x'
            have hf : Finset.univ.filter (fun k : Fin M => k.val < M) = Finset.univ := by
              ext k; simp
            rw [hf] at h1
            unfold network outputProduct layerProduct
            calc ENNReal.ofReal |A.output (netState A W M x) - A.output (netState A W M x')|
                ≤ ENNReal.ofReal (‖(A.output : A.Space M →L[ℝ] ℝ)‖ *
                    ‖netState A W M x - netState A W M x'‖) := by
                  apply ENNReal.ofReal_le_ofReal
                  rw [← map_sub, ← Real.norm_eq_abs]
                  exact (A.output : A.Space M →L[ℝ] ℝ).le_opNorm _
              _ = ENNReal.ofReal ‖(A.output : A.Space M →L[ℝ] ℝ)‖ *
                    ENNReal.ofReal ‖netState A W M x - netState A W M x'‖ :=
                  ENNReal.ofReal_mul (norm_nonneg _)
              _ ≤ _ := by rw [mul_assoc]; gcongr
          have hempNull : ∀ {Z : Type} [MeasurableSpace Z] [MeasurableSingletonClass Z]
              (z : Fin N → Z), ((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (z i)) (Set.range z)ᶜ = 0 := by
            intro Z _ _ z
            rw [Measure.smul_apply, Measure.finsetSum_apply]
            simp [Measure.dirac_apply' _ (Set.finite_range z).measurableSet.compl]
          have hempInt : ∀ {Z : Type} [MeasurableSpace Z] [MeasurableSingletonClass Z]
              (z : Fin N → Z) (g : Z → ℝ), (∀ w, 0 ≤ g w) →
              ∫⁻ w, ENNReal.ofReal (g w) ∂((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (z i)) =
                ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, g (z i)) := by
            intro Z _ _ z g hg
            rw [lintegral_smul_measure, lintegral_finsetSum_measure]
            simp only [lintegral_dirac]
            rw [smul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by
              exact_mod_cast hN), ENNReal.ofReal_natCast,
              ENNReal.ofReal_sum_of_nonneg (fun i _ => hg _)]
          have hcoupCost : ∀ {Z : Type} [MeasurableSpace Z] (c : Z → Z → ℝ≥0∞) (Q P : Measure Z),
              costTransport c Q P ≤ ENNReal.ofReal ρ → ∀ ε : ℝ≥0∞, ε ≠ 0 →
              ∃ π : Measure (Z × Z), π.map Prod.fst = Q ∧ π.map Prod.snd = P ∧
                ∫⁻ p, c p.1 p.2 ∂π < ENNReal.ofReal ρ + ε := by
            intro Z _ c Q P h ε hε
            have : costTransport c Q P < ENNReal.ofReal ρ + ε :=
              h.trans_lt (ENNReal.lt_add_right ENNReal.ofReal_ne_top hε)
            unfold costTransport at this
            obtain ⟨π, hπ⟩ := iInf_lt_iff.1 this
            obtain ⟨⟨h1, h2⟩, h3⟩ := iInf_lt_iff.1 hπ
            exact ⟨π, h1, h2, h3⟩
          have hCge : ∀ (W : Weights A) (v : A.Space 0), v ∈ X →
              ENNReal.ofReal (2 * |network A W v|) ≤ classC A X := by
            intro W v hv
            unfold classC
            refine le_max_of_le_right ?_
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
            gcongr
            exact le_iSup_of_le W (le_iSup_of_le v (le_iSup_of_le hv le_rfl))
          have hLstep : ∀ (a b : ℝ), ENNReal.ofReal (L a) ≤
              ENNReal.ofReal (L b) + lipschitzModulus L * ENNReal.ofReal |a - b| := by
            intro a b
            calc ENNReal.ofReal (L a) ≤ ENNReal.ofReal (L b + |L a - L b|) :=
                  ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (L a - L b)])
              _ = ENNReal.ofReal (L b) + ENNReal.ofReal |L a - L b| :=
                  ENNReal.ofReal_add (hnonneg _) (abs_nonneg _)
              _ ≤ _ := by gcongr; exact hLip L a b
          have hLc : Continuous L := by
            obtain ⟨K0, hK0⟩ := hlip; exact hK0.continuous
          refine ⟨fun Y hY y hy => iInf_mono fun W => ?_, fun y => iInf_mono fun W => ?_⟩
          · -- regression
            unfold neuralRegRisk costRisk neuralRegBound
            apply iSup₂_le
            intro Q hQ
            obtain ⟨_, _, hQc⟩ := hQ
            have hmeas : Measurable (fun p : (A.Space 0 × ℝ) × (A.Space 0 × ℝ) =>
                extendedWeightedCost A κ p.1 p.2) := by
              unfold extendedWeightedCost
              refine Measurable.add ?_ (Measurable.const_mul ?_ κ)
              · exact (Continuous.measurable (by fun_prop)).ennreal_ofReal
              · exact (Continuous.measurable (by fun_prop)).ennreal_ofReal
            have key := gen Q (empiricalDistribution fun i => (x i, y i)) (extendedWeightedCost A κ)
              (Set.range fun i => (x i, y i)) (fun p => L (network A W p.1 - p.2))
              (lipschitzModulus L * max (outputProduct A W) (1 / κ)) ρ hρ
              (hLc.comp (((hcontNet W).comp continuous_fst).sub continuous_snd)) (fun _ => hnonneg _) hmeas (Set.finite_range _)
              (hempNull _) (hcoupCost _ _ _ hQc) ?_ ?_
            · unfold expected
              rw [mul_assoc]
              refine key.trans (le_of_eq ?_)
              unfold empiricalDistribution
              rw [hempInt _ _ (fun _ => hnonneg _)]
            · rintro ⟨v1, y1⟩ ⟨v2, y2⟩ _ hc
              simp only [extendedWeightedCost] at hc ⊢
              refine (hLstep _ (network A W v2 - y2)).trans ?_
              gcongr ENNReal.ofReal _ + ?_
              rw [mul_assoc]
              gcongr
              calc ENNReal.ofReal |network A W v1 - y1 - (network A W v2 - y2)|
                  ≤ ENNReal.ofReal (|network A W v1 - network A W v2| + |y1 - y2|) := by
                    apply ENNReal.ofReal_le_ofReal
                    rw [show network A W v1 - y1 - (network A W v2 - y2) =
                      (network A W v1 - network A W v2) - (y1 - y2) by ring]
                    exact abs_sub _ _
                _ = ENNReal.ofReal |network A W v1 - network A W v2| + ENNReal.ofReal |y1 - y2| :=
                    ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
                _ ≤ outputProduct A W * ENNReal.ofReal ‖v1 - v2‖ + ENNReal.ofReal |y1 - y2| := by
                    gcongr; exact hlipNet W v1 v2
                _ ≤ max (outputProduct A W) (1 / κ) * ENNReal.ofReal ‖v1 - v2‖ +
                      max (outputProduct A W) (1 / κ) * (κ * ENNReal.ofReal |y1 - y2|) := by
                    gcongr
                    · exact le_max_left _ _
                    · by_cases hκt : κ = ⊤
                      · have h2 : κ * ENNReal.ofReal |y1 - y2| ≠ ⊤ := (ENNReal.add_ne_top.1 hc).2
                        have : ENNReal.ofReal |y1 - y2| = 0 := by
                          by_contra hne
                          exact h2 (by rw [hκt, ENNReal.top_mul hne])
                        rw [this]; exact bot_le
                      · calc ENNReal.ofReal |y1 - y2| = (1 / κ) * (κ * ENNReal.ofReal |y1 - y2|) := by
                              rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel hκ.ne' hκt, one_mul]
                          _ ≤ _ := by gcongr; exact le_max_right _ _
                _ = _ := by rw [mul_add]
            · rintro F hF ⟨vs, ys⟩ _ hsF
              obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hF.isOpen_compl _ hsF
              refine ⟨min 1 κ * ENNReal.ofReal r, ?_, ?_, ?_⟩
              · exact mul_ne_zero (by simp [hκ.ne']) (by simp [hr])
              · exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
                  ENNReal.ofReal_ne_top
              · rintro ⟨v, w⟩ hz
                have hnot : ¬ dist (v, w) (vs, ys) < r := fun h => hball h hz
                rw [not_lt, Prod.dist_eq, le_max_iff] at hnot
                simp only [extendedWeightedCost]
                rcases hnot with h | h
                · rw [dist_eq_norm] at h
                  calc min 1 κ * ENNReal.ofReal r ≤ 1 * ENNReal.ofReal ‖v - vs‖ := by
                        gcongr; exact min_le_left _ _
                    _ ≤ _ := by rw [one_mul]; exact le_self_add
                · rw [Real.dist_eq] at h
                  calc min 1 κ * ENNReal.ofReal r ≤ κ * ENNReal.ofReal |w - ys| := by
                        gcongr; exact min_le_right _ _
                    _ ≤ _ := le_add_self
          · -- classification
            have hsc : Continuous sgn := continuous_of_discreteTopology
            have hcontℓ : Continuous (fun p : A.Space 0 × Bool => L (sgn p.2 * network A W p.1)) :=
              hLc.comp ((hsc.comp continuous_snd).mul ((hcontNet W).comp continuous_fst))
            have hsgn1 : ∀ b : Bool, |sgn b| = 1 := by intro b; cases b <;> simp [sgn]
            have hsame : ∀ (b : Bool) (v1 v2 : A.Space 0),
                ENNReal.ofReal |sgn b * network A W v1 - sgn b * network A W v2| ≤
                  outputProduct A W * ENNReal.ofReal ‖v1 - v2‖ := by
              intro b v1 v2
              rw [← mul_sub, abs_mul, hsgn1, one_mul]; exact hlipNet W v1 v2
            unfold neuralClassRisk neuralClassBound
            split_ifs with hκt
            · -- κ = ⊤
              unfold costRisk
              apply iSup₂_le; intro Q hQ
              obtain ⟨_, _, hQc⟩ := hQ
              have hmeas : Measurable (fun p : (A.Space 0 × Bool) × (A.Space 0 × Bool) =>
                  labelPreservingCost p.1 p.2) := by
                unfold labelPreservingCost
                refine Measurable.ite ?_ ((Continuous.measurable (by fun_prop)).ennreal_ofReal)
                  measurable_const
                exact measurableSet_eq_fun (measurable_snd.comp measurable_fst)
                  (measurable_snd.comp measurable_snd)
              have key := gen Q (empiricalDistribution fun i => (x i, y i)) labelPreservingCost
                (Set.range fun i => (x i, y i)) (fun p => L (sgn p.2 * network A W p.1))
                (lipschitzModulus L * max (outputProduct A W) (classC A X / κ)) ρ hρ hcontℓ
                (fun _ => hnonneg _) hmeas (Set.finite_range _) (hempNull _) (hcoupCost _ _ _ hQc) ?_ ?_
              · unfold expected; rw [mul_assoc]; refine key.trans (le_of_eq ?_)
                unfold empiricalDistribution; rw [hempInt _ _ (fun _ => hnonneg _)]
              · rintro ⟨v1, b1⟩ ⟨v2, b2⟩ _ hc
                by_cases hb : b1 = b2
                · subst hb
                  simp only [labelPreservingCost, if_true] at hc ⊢
                  refine (hLstep _ (sgn b1 * network A W v2)).trans ?_
                  gcongr ENNReal.ofReal _ + ?_
                  rw [mul_assoc]; gcongr
                  exact (hsame b1 v1 v2).trans (by gcongr; exact le_max_left _ _)
                · exfalso; apply hc; simp [labelPreservingCost, hb]
              · rintro F hF ⟨vs, bs⟩ _ hsF
                have hopen : IsOpen {v : A.Space 0 | (v, bs) ∈ Fᶜ} :=
                  hF.isOpen_compl.preimage (by fun_prop)
                obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen vs hsF
                refine ⟨ENNReal.ofReal r, by simp [hr], ENNReal.ofReal_ne_top, ?_⟩
                rintro ⟨v, b⟩ hz
                unfold labelPreservingCost
                split_ifs with hb
                · simp only at hb; subst hb
                  have : ¬ dist v vs < r := fun h => hball (Metric.mem_ball.2 h) hz
                  rw [not_lt, dist_eq_norm] at this; exact ENNReal.ofReal_le_ofReal this
                · exact le_top
            · -- κ < ⊤
              unfold classRisk
              apply iSup₂_le; intro Q hQ; apply iSup_le; intro _
              obtain ⟨_, hQc⟩ := hQ
              have hκr : 0 < κ.toReal := ENNReal.toReal_pos hκ.ne' hκt
              have hκeq : κ = ENNReal.ofReal κ.toReal := (ENNReal.ofReal_toReal hκt).symm
              have hcoup : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ π : Measure ((A.Space 0 × Bool) × (A.Space 0 × Bool)),
                  π.map Prod.fst = Q ∧ π.map Prod.snd = empirical x y ∧
                  ∫⁻ p, ENNReal.ofReal (featureLabelDist κ.toReal p.1 p.2) ∂π < ENNReal.ofReal ρ + ε := by
                intro ε hε
                have : wasserstein κ.toReal Q (empirical x y) < ENNReal.ofReal ρ + ε :=
                  hQc.trans_lt (ENNReal.lt_add_right ENNReal.ofReal_ne_top hε)
                unfold wasserstein at this
                obtain ⟨π, hπ⟩ := iInf_lt_iff.1 this
                obtain ⟨_, hπ⟩ := iInf_lt_iff.1 hπ
                obtain ⟨h1, hπ⟩ := iInf_lt_iff.1 hπ
                obtain ⟨h2, h3⟩ := iInf_lt_iff.1 hπ
                exact ⟨π, h1, h2, h3⟩
              have hmeas : Measurable (fun p : (A.Space 0 × Bool) × (A.Space 0 × Bool) =>
                  ENNReal.ofReal (featureLabelDist κ.toReal p.1 p.2)) := by
                unfold featureLabelDist
                exact (Continuous.measurable (by fun_prop)).ennreal_ofReal
              have hfld_ge : ∀ z z' : A.Space 0 × Bool, ‖z.1 - z'.1‖ ≤ featureLabelDist κ.toReal z z' := by
                intro z z'; unfold featureLabelDist
                have : 0 ≤ κ.toReal * |sgn z.2 - sgn z'.2| / 2 := by positivity
                linarith
              have hfld_ne : ∀ (v v' : A.Space 0) (b b' : Bool), b ≠ b' →
                  featureLabelDist κ.toReal (v, b) (v', b') = ‖v - v'‖ + κ.toReal := by
                intro v v' b b' hb
                cases b <;> cases b' <;> first | exact absurd rfl hb |
                  (simp only [featureLabelDist, sgn, ↓reduceIte, Bool.false_eq_true]; norm_num)
              have key := gen Q (empirical x y) (fun z z' => ENNReal.ofReal (featureLabelDist κ.toReal z z'))
                (Set.range fun i => (x i, y i)) (fun p => L (sgn p.2 * network A W p.1))
                (lipschitzModulus L * max (outputProduct A W) (classC A X / κ)) ρ hρ hcontℓ
                (fun _ => hnonneg _) hmeas (Set.finite_range _)
                (by unfold empirical; exact hempNull (fun i => (x i, y i))) hcoup ?_ ?_
              · unfold expected; rw [mul_assoc]; refine key.trans (le_of_eq ?_)
                unfold empirical; rw [hempInt (fun i => (x i, y i)) _ (fun _ => hnonneg _)]
              · rintro ⟨v1, b1⟩ z2 hz2 _
                obtain ⟨i, rfl⟩ := hz2
                refine (hLstep _ (sgn (y i) * network A W (x i))).trans ?_
                gcongr ENNReal.ofReal _ + ?_
                rw [mul_assoc]; gcongr
                by_cases hb : b1 = y i
                · rw [hb]
                  refine (hsame (y i) v1 (x i)).trans ?_
                  gcongr
                  · exact le_max_left _ _
                  · exact hfld_ge (v1, y i) (x i, y i)
                · rw [hfld_ne _ _ _ _ hb]
                  have habs : |sgn b1 * network A W v1 - sgn (y i) * network A W (x i)| ≤
                      |network A W v1 - network A W (x i)| + 2 * |network A W (x i)| := by
                    generalize y i = b2 at hb ⊢
                    generalize network A W v1 = u
                    generalize network A W (x i) = w
                    rw [abs_le]
                    cases b1 <;> cases b2 <;> first | exact absurd rfl hb |
                      (simp only [sgn, ↓reduceIte, Bool.false_eq_true]; constructor <;>
                        linarith [neg_abs_le (u - w), le_abs_self (u - w), neg_abs_le w, le_abs_self w])
                  calc _ ≤ ENNReal.ofReal (|network A W v1 - network A W (x i)| +
                        2 * |network A W (x i)|) := ENNReal.ofReal_le_ofReal habs
                    _ = ENNReal.ofReal |network A W v1 - network A W (x i)| +
                        ENNReal.ofReal (2 * |network A W (x i)|) :=
                        ENNReal.ofReal_add (abs_nonneg _) (by positivity)
                    _ ≤ outputProduct A W * ENNReal.ofReal ‖v1 - x i‖ + classC A X := by
                        gcongr
                        · exact hlipNet W v1 (x i)
                        · exact hCge W (x i) (hx i)
                    _ ≤ max (outputProduct A W) (classC A X / κ) * ENNReal.ofReal ‖v1 - x i‖ +
                        max (outputProduct A W) (classC A X / κ) * κ := by
                        gcongr
                        · exact le_max_left _ _
                        · calc classC A X = classC A X / κ * κ :=
                                (ENNReal.div_mul_cancel hκ.ne' hκt).symm
                            _ ≤ _ := by gcongr; exact le_max_right _ _
                    _ = _ := by
                        rw [← mul_add, ENNReal.ofReal_add (norm_nonneg _) hκr.le, ← hκeq]
              · rintro F hF ⟨vs, bs⟩ _ hsF
                have hopen : IsOpen {v : A.Space 0 | (v, bs) ∈ Fᶜ} :=
                  hF.isOpen_compl.preimage (by fun_prop)
                obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen vs hsF
                refine ⟨ENNReal.ofReal (min r κ.toReal), by simp [hr, hκr], ENNReal.ofReal_ne_top, ?_⟩
                rintro ⟨v, b⟩ hz
                apply ENNReal.ofReal_le_ofReal
                by_cases hb : b = bs
                · subst hb
                  have : ¬ dist v vs < r := fun h => hball (Metric.mem_ball.2 h) hz
                  rw [not_lt, dist_eq_norm] at this
                  exact (min_le_left _ _).trans (this.trans (hfld_ge (v, b) (vs, b)))
                · rw [hfld_ne _ _ _ _ hb]
                  have := norm_nonneg (v - vs)
                  have := min_le_right r κ.toReal
                  linarith
          )
