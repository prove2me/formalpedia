-- Prove2me | solution 1 for RobustSAA.Discrete.Supplement.theorem_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:08.862144+00:00
-- url     : https://prove2.me/submissions/09f9cb07-2bf7-4111-b1cc-8b6602abf771

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Univariate_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivDual

open RobustSAA
open RobustSAA.Discrete
open RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Univariate

theorem solution {dx N : ℕ} (hN : 0 < N) (Ξ : Set ℝ) (hΞ : IsClosed Ξ) (s : Fin N → ℝ)
    (hs : ∀ i, s i ∈ Ξ) (X : Set (RobustSAA.Convergence.Pt dx)) (hX : IsClosed X)
    (c : RobustSAA.Convergence.Pt dx → ℝ → ℝ) (hmeas : ∀ x, Measurable (c x))
    (hequi : Equicontinuous (fun ξ : ↥Ξ => fun x => c x (ξ : ℝ)))
    (hcomp : IsCompact X ∨ ∀ ξ ∈ Ξ,
      Tendsto (fun x => c x ξ) (Bornology.cobounded (RobustSAA.Convergence.Pt dx)) atTop)
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφ : ∀ ξ ∈ Ξ, 0 ≤ φ ξ)
    (hφc : ∃ x₀ ∈ X, ∃ ν η : ℝ, ∀ ξ ∈ Ξ, |c x₀ ξ| ≤ ν + η * φ ξ)
    (x : RobustSAA.Convergence.Pt dx) (hx : x ∈ X) :
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (ksRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ ksStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (ksRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_KS N) (b_KS N Q) (K_KS N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (kuiperRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ kuiperStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (kuiperRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_KS N) (b_Kuiper N Q) (K_Kuiper N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (cvmRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ cvmStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (cvmRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_CvM N) (b_CvM N Q) (K_CvM N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (watsonRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ watsonStat F₀ s < Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (watsonRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_Watson N) (b_Watson N Q) (K_Watson N) Ξ (c x) φ QM s)) ∧
    (∀ Q QM : ℝ, (∃ x₀ ∈ X, worstCaseR (adRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x₀) < ⊤) →
      (∃ F₀ : ProbabilityMeasure ℝ, SupportedOn Ξ F₀ ∧ adStat F₀ s < ENNReal.ofReal Q ∧
        ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
        |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| < QM) →
      IsMinValue (worstCaseR (adRegionOn Ξ Q s ∩ momentRegion φ QM s) (c x))
        (momentDualValues (A_AD N) (b_AD N Q) (K_AD N) Ξ (c x) φ QM s)) := by
          set_option maxHeartbeats 0 in
            set_option maxRecDepth 4096 in
              classical
              letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
              have hdiff : ∀ a b : RobustSAA.Convergence.Pt dx,
                  ∃ M : ℝ, ∀ ξ ∈ Ξ, |c a ξ - c b ξ| ≤ M := by
                intro a
                let S : Set (RobustSAA.Convergence.Pt dx) :=
                  {b | ∃ M : ℝ, ∀ ξ ∈ Ξ, |c a ξ - c b ξ| ≤ M}
                have hloc : ∀ b, ∃ U ∈ 𝓝 b, ∀ z ∈ U, ∀ ξ ∈ Ξ, |c b ξ - c z ξ| < 1 := by
                  intro b
                  have h := (Metric.equicontinuousAt_iff_right.mp (hequi b)) 1 zero_lt_one
                  obtain ⟨U, hU, h⟩ := Filter.eventually_iff_exists_mem.mp h
                  refine ⟨U, hU, ?_⟩
                  intro z hz ξ hξ
                  simpa only [Real.dist_eq] using h z hz ⟨ξ, hξ⟩
                have hS : IsOpen S := by
                  rw [isOpen_iff_mem_nhds]
                  intro b hb
                  obtain ⟨M, hM⟩ := hb
                  obtain ⟨U, hU, h⟩ := hloc b
                  apply Filter.mem_of_superset hU
                  intro z hz
                  refine ⟨M + 1, fun ξ hξ => ?_⟩
                  calc
                    |c a ξ - c z ξ| ≤ |c a ξ - c b ξ| + |c b ξ - c z ξ| := abs_sub_le _ _ _
                    _ ≤ M + 1 := add_le_add (hM ξ hξ) (h z hz ξ hξ).le
                have hSc : IsOpen Sᶜ := by
                  rw [isOpen_iff_mem_nhds]
                  intro b hb
                  obtain ⟨U, hU, h⟩ := hloc b
                  apply Filter.mem_of_superset hU
                  intro z hz hzS
                  apply hb
                  obtain ⟨M, hM⟩ := hzS
                  refine ⟨M + 1, fun ξ hξ => ?_⟩
                  calc
                    |c a ξ - c b ξ| ≤ |c a ξ - c z ξ| + |c z ξ - c b ξ| := abs_sub_le _ _ _
                    _ ≤ M + 1 := add_le_add (hM ξ hξ) (by rw [abs_sub_comm]; exact (h z hz ξ hξ).le)
                have hnon : S.Nonempty := ⟨a, 0, by simp⟩
                have hSuniv : S = Set.univ := (isClopen_iff.mp ⟨by simpa using hSc.isClosed_compl, hS⟩).resolve_left (Set.nonempty_iff_ne_empty.mp hnon)
                intro b
                have : b ∈ S := by rw [hSuniv]; trivial
                exact this
              have hsep : ∀ (J : Type) [Fintype J] (K : Set (J → ℝ)),
                  Convex ℝ K → (0 : J → ℝ) ∈ K →
                  (∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K) →
                  ∀ (P : Set ((J → ℝ) × ℝ)), Convex ℝ P → ∀ V : ℝ,
                  (∀ y v, (y, v) ∈ P → y ∈ K → v ≤ V) →
                  (∃ y v, (y, v) ∈ P ∧ y ∈ interior K) →
                  ∃ r : J → ℝ, (∀ y ∈ K, ∑ j, r j * y j ≤ 0) ∧
                    ∀ y v, (y, v) ∈ P → v ≤ V + ∑ j, r j * y j := by
                intro J _ K hK hzero hscale P hP V hV hstrict
                obtain ⟨y₀, v₀, h₀, hy₀⟩ := hstrict
                let B : Set ((J → ℝ) × ℝ) := K ×ˢ Set.Ici V
                have hB : Convex ℝ B := hK.prod (convex_Ici V)
                have hBi : (interior B).Nonempty := by
                  refine ⟨(y₀, V + 1), ?_⟩
                  rw [interior_prod_eq]
                  exact ⟨hy₀, by simp⟩
                have hdisj : Disjoint (interior B) P := by
                  rw [Set.disjoint_left]
                  intro z hz hzP
                  rw [interior_prod_eq] at hz
                  have hlt : V < z.2 := by simpa using hz.2
                  exact hlt.not_ge (hV z.1 z.2 hzP (interior_subset hz.1))
                obtain ⟨l, u, hlB, hlP⟩ := geometric_hahn_banach_open hB.interior isOpen_interior hP hdisj
                have hlB' : ∀ z ∈ B, l z ≤ u := by
                  have hclosure : closure (interior B) ⊆ {z | l z ≤ u} :=
                    closure_minimal (fun z hz => (hlB z hz).le) (isClosed_le l.continuous continuous_const)
                  intro z hz
                  apply hclosure
                  rw [hB.closure_interior_eq_closure_of_nonempty_interior hBi]
                  exact subset_closure hz
                let a : ℝ := l (0, 1)
                let q : J → ℝ := fun j => l (Pi.single j 1, 0)
                have hl : ∀ y v, l (y, v) = (∑ j, q j * y j) + a * v := by
                  intro y v
                  have hz : (y, v) = (∑ j, y j • (Pi.single j 1, (0 : ℝ))) + v • (0, 1) := by
                    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
                  rw [hz, map_add, map_sum, map_smul]
                  simp only [map_smul, smul_eq_mul, q, a]
                  congr 1
                  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
                  · ring
                have ha : a < 0 := by
                  by_contra ha
                  have ha' : 0 ≤ a := le_of_not_gt ha
                  have hz : (y₀, max V v₀ + 1) ∈ interior B := by
                    rw [interior_prod_eq]
                    exact ⟨hy₀, by simpa using (lt_add_one (max V v₀)).trans_le' (le_max_left V v₀)⟩
                  have hu := hlB _ hz
                  have hw := hlP _ h₀
                  rw [hl] at hu hw
                  have hv : v₀ ≤ max V v₀ + 1 := by linarith [le_max_right V v₀]
                  have := mul_le_mul_of_nonneg_left hv ha'
                  linarith
                have hu : a * V ≤ u := by
                  have hh := hlB' (0, V) ⟨hzero, Set.mem_Ici.mpr le_rfl⟩
                  simpa [hl] using hh
                have hq : ∀ y ∈ K, ∑ j, q j * y j ≤ 0 := by
                  intro y hy
                  by_contra hq
                  have hq' : 0 < ∑ j, q j * y j := lt_of_not_ge hq
                  let t : ℝ := (u - a * V + 1) / (∑ j, q j * y j)
                  have ht : 0 ≤ t := div_nonneg (by linarith) hq'.le
                  have hh := hlB' (t • y, V) ⟨hscale t ht y hy, Set.mem_Ici.mpr le_rfl⟩
                  rw [hl] at hh
                  have heq : (∑ j, q j * (t • y) j) = t * ∑ j, q j * y j := by
                    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
                  rw [heq] at hh
                  have htq : t * (∑ j, q j * y j) = u - a * V + 1 := div_mul_cancel₀ _ (ne_of_gt hq')
                  linarith
                refine ⟨fun j => q j / (-a), ?_, ?_⟩
                · intro y hy
                  have heq : (∑ j, q j / (-a) * y j) = (∑ j, q j * y j) / (-a) := by
                    rw [Finset.sum_div]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
                  rw [heq]
                  exact div_nonpos_of_nonpos_of_nonneg (hq y hy) (by linarith)
                · intro y v hyv
                  have hh := (hu.trans (hlP _ hyv))
                  rw [hl] at hh
                  have heq : (∑ j, q j / (-a) * y j) = (∑ j, q j * y j) / (-a) := by
                    rw [Finset.sum_div]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
                  rw [heq]
                  have hh' : v - V ≤ (∑ j, q j * y j) / (-a) :=
                    (le_div_iff₀ (by linarith : 0 < -a)).mpr (by nlinarith only [hh])
                  linarith only [hh']
              obtain ⟨x₀, hx₀, ν, η, hν⟩ := hφc
              obtain ⟨M, hM⟩ := hdiff x x₀
              let B : ℝ := |ν| + |M|
              let D : ℝ := |η|
              have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (abs_nonneg _)
              have hD : 0 ≤ D := abs_nonneg _
              have hbound : ∀ ξ ∈ Ξ, |c x ξ| ≤ B + D * φ ξ := by
                intro ξ hξ
                calc
                  |c x ξ| ≤ |c x₀ ξ| + |c x ξ - c x₀ ξ| := by
                    calc
                      |c x ξ| = |(c x ξ - c x₀ ξ) + c x₀ ξ| := by congr 1; ring
                      _ ≤ |c x ξ - c x₀ ξ| + |c x₀ ξ| := abs_add_le _ _
                      _ = _ := add_comm _ _
                  _ ≤ (ν + η * φ ξ) + M := add_le_add (hν ξ hξ) (hM ξ hξ)
                  _ ≤ B + D * φ ξ := by
                    have := mul_le_mul_of_nonneg_right (le_abs_self η) (hφ ξ hξ)
                    dsimp [B, D]
                    linarith [le_abs_self ν, le_abs_self M]
              have hae : ∀ G : ProbabilityMeasure ℝ, SupportedOn Ξ G → ∀ᵐ ξ ∂(G : Measure ℝ), ξ ∈ Ξ := by
                intro G hG
                exact ae_iff.mpr hG
              have hmoment : ∀ G : ProbabilityMeasure ℝ, SupportedOn Ξ G →
                  ((∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(G : Measure ℝ)) < ⊤ ↔ Integrable φ (G : Measure ℝ)) := by
                intro G hG
                have hpos : 0 ≤ᵐ[(G : Measure ℝ)] φ := (hae G hG).mono (fun ξ hξ => hφ ξ hξ)
                exact (hasFiniteIntegral_iff_ofReal hpos).symm.trans
                  (by simp only [Integrable, hφm.aestronglyMeasurable, true_and])
              have hfint : ∀ G : ProbabilityMeasure ℝ, SupportedOn Ξ G → Integrable φ (G : Measure ℝ) →
                  Integrable (c x) (G : Measure ℝ) := by
                intro G hG hφG
                apply ((integrable_const B).add (hφG.const_mul D)).mono' (hmeas x).aestronglyMeasurable
                exact (hae G hG).mono (fun ξ hξ => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hbound ξ hξ)
              have hmix : ∀ (G H : ProbabilityMeasure ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
                  ∃ I : ProbabilityMeasure ℝ,
                    (I : Measure ℝ) = ENNReal.ofReal a • (G : Measure ℝ) + ENNReal.ofReal b • (H : Measure ℝ) ∧
                    (SupportedOn Ξ G → SupportedOn Ξ H → SupportedOn Ξ I) ∧
                    ∀ f : ℝ → ℝ, Integrable f (G : Measure ℝ) → Integrable f (H : Measure ℝ) →
                      Integrable f (I : Measure ℝ) ∧
                        ∫ ξ, f ξ ∂(I : Measure ℝ) = a * (∫ ξ, f ξ ∂(G : Measure ℝ)) + b * (∫ ξ, f ξ ∂(H : Measure ℝ)) := by
                intro G H a b ha hb hab
                let μ : Measure ℝ := ENNReal.ofReal a • (G : Measure ℝ) + ENNReal.ofReal b • (H : Measure ℝ)
                have hμ : IsProbabilityMeasure μ := by
                  apply isProbabilityMeasure_iff.mpr
                  simp only [μ, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
                  rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
                refine ⟨⟨μ, hμ⟩, rfl, ?_, ?_⟩
                · intro hG hH
                  change μ Ξᶜ = 0
                  change (G : Measure ℝ) Ξᶜ = 0 at hG
                  change (H : Measure ℝ) Ξᶜ = 0 at hH
                  simp only [μ, Measure.add_apply, Measure.smul_apply, hG, hH, smul_eq_mul, mul_zero, add_zero]
                · intro f hfG hfH
                  change Integrable f μ ∧ _
                  have haG := hfG.smul_measure (ENNReal.ofReal_ne_top : ENNReal.ofReal a ≠ ⊤)
                  have hbH := hfH.smul_measure (ENNReal.ofReal_ne_top : ENNReal.ofReal b ≠ ⊤)
                  refine ⟨haG.add_measure hbH, ?_⟩
                  change (∫ ξ, f ξ ∂μ) = _
                  rw [integral_add_measure haG hbH]
                  simp [integral_smul_measure, ENNReal.toReal_ofReal, ha, hb]
              have hgen : ∀ (J : Type) [Fintype J] (K : Set (J → ℝ)),
                  Convex ℝ K → (0 : J → ℝ) ∈ K →
                  (∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K) →
                  ∀ (g : ℝ → J → ℝ) (d : J → ℝ),
                  (∀ (G : ProbabilityMeasure ℝ), SupportedOn Ξ G → Integrable φ (G : Measure ℝ) →
                    ∀ j, Integrable (fun ξ => g ξ j) (G : Measure ℝ)) →
                  ∀ R : Set (ProbabilityMeasure ℝ),
                  (∀ G, G ∈ R ↔ SupportedOn Ξ G ∧ Integrable φ (G : Measure ℝ) ∧
                    (fun j => (∫ ξ, g ξ j ∂(G : Measure ℝ)) - d j) ∈ K) →
                  worstCaseR R (c x) < ⊤ →
                  (∃ G : ProbabilityMeasure ℝ, SupportedOn Ξ G ∧ Integrable φ (G : Measure ℝ) ∧
                    (fun j => (∫ ξ, g ξ j ∂(G : Measure ℝ)) - d j) ∈ interior K) →
                  ∃ (V : ℝ) (r : J → ℝ), worstCaseR R (c x) = (V : EReal) ∧
                    (fun j => -r j) ∈ dualCone K ∧
                    ∀ ξ ∈ Ξ, c x ξ ≤ V + ∑ j, r j * (g ξ j - d j) := by
                intro J _ K hK hzero hscale g d hg R hR hfin hstrict
                clear * - hmix hfint hsep hR hfin hstrict hg hK hzero hscale
                let m : ProbabilityMeasure ℝ → J → ℝ := fun G j => ∫ ξ, g ξ j ∂(G : Measure ℝ)
                let p : ProbabilityMeasure ℝ → ((J → ℝ) × ℝ) :=
                  fun G => (m G - d, ∫ ξ, c x ξ ∂(G : Measure ℝ))
                let P : Set ((J → ℝ) × ℝ) :=
                  {z | ∃ G : ProbabilityMeasure ℝ, SupportedOn Ξ G ∧ Integrable φ (G : Measure ℝ) ∧ z = p G}
                have hP : Convex ℝ P := by
                  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
                  obtain ⟨G, hG, hφG, rfl⟩ := hz₁
                  obtain ⟨H, hH, hφH, rfl⟩ := hz₂
                  obtain ⟨I, hI, hIs, hIi⟩ := hmix G H a b ha hb hab
                  refine ⟨I, hIs hG hH, (hIi φ hφG hφH).1, ?_⟩
                  have hcg := hfint G hG hφG
                  have hch := hfint H hH hφH
                  apply Prod.ext
                  · ext j
                    change a * (m G j - d j) + b * (m H j - d j) = m I j - d j
                    have hi := (hIi (fun ξ => g ξ j) (hg G hG hφG j) (hg H hH hφH j)).2
                    change m I j = a * m G j + b * m H j at hi
                    rw [hi]
                    nlinarith only [congrArg (fun t : ℝ => t * d j) hab]
                  · change a * (∫ ξ, c x ξ ∂(G : Measure ℝ)) + b * (∫ ξ, c x ξ ∂(H : Measure ℝ)) =
                      ∫ ξ, c x ξ ∂(I : Measure ℝ)
                    exact (hIi (c x) hcg hch).2.symm
                obtain ⟨G₀, hG₀, hφG₀, hint⟩ := hstrict
                have hG₀R : G₀ ∈ R := (hR G₀).mpr ⟨hG₀, hφG₀, interior_subset hint⟩
                have hcG₀ := hfint G₀ hG₀ hφG₀
                have hbot : worstCaseR R (c x) ≠ ⊥ := by
                  have hh : ((∫ ξ, c x ξ ∂(G₀ : Measure ℝ) : ℝ) : EReal) ≤ worstCaseR R (c x) := by
                    exact le_iSup_of_le G₀ (le_iSup_of_le hG₀R (by simp [expectR, hcG₀]))
                  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hh)
                let V : ℝ := (worstCaseR R (c x)).toReal
                have hWV : worstCaseR R (c x) = (V : EReal) := (EReal.coe_toReal hfin.ne hbot).symm
                have hPV : ∀ y v, (y, v) ∈ P → y ∈ K → v ≤ V := by
                  intro y v ⟨G, hG, hφG, heq⟩ hy
                  have hy' : (m G - d) ∈ K := by
                    have hey : y = m G - d := congrArg Prod.fst heq
                    rw [← hey]
                    exact hy
                  have hGR : G ∈ R := (hR G).mpr ⟨hG, hφG, hy'⟩
                  have hcg := hfint G hG hφG
                  have hh : ((∫ ξ, c x ξ ∂(G : Measure ℝ) : ℝ) : EReal) ≤ worstCaseR R (c x) :=
                    le_iSup_of_le G (le_iSup_of_le hGR (by simp [expectR, hcg]))
                  rw [hWV] at hh
                  have hv : v = ∫ ξ, c x ξ ∂(G : Measure ℝ) := congrArg Prod.snd heq
                  rw [hv]
                  exact EReal.coe_le_coe_iff.mp hh
                obtain ⟨r, hrK, hrP⟩ := hsep J K hK hzero hscale P hP V hPV
                  ⟨m G₀ - d, ∫ ξ, c x ξ ∂(G₀ : Measure ℝ), ⟨G₀, hG₀, hφG₀, rfl⟩, hint⟩
                refine ⟨V, r, hWV, ?_, ?_⟩
                · intro y hy
                  simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonneg] using hrK y hy
                · intro ξ hξ
                  let G : ProbabilityMeasure ℝ := ⟨Measure.dirac ξ, Measure.dirac.isProbabilityMeasure⟩
                  have hG : SupportedOn Ξ G := by
                    change (Measure.dirac ξ) Ξᶜ = 0
                    simp [Measure.dirac_apply', hΞ.measurableSet.compl, hξ]
                  have hφG : Integrable φ (G : Measure ℝ) := by
                    change Integrable φ (Measure.dirac ξ)
                    exact integrable_dirac (by simp)
                  have hh := hrP (m G - d) (∫ z, c x z ∂(G : Measure ℝ)) ⟨G, hG, hφG, rfl⟩
                  simpa [m, G] using hh
              have hfinite : ∀ (R : Set (ProbabilityMeasure ℝ)) (QM : ℝ),
                  (∀ G ∈ R, SupportedOn Ξ G ∧ G ∈ momentRegion φ QM s) →
                  worstCaseR R (c x) < ⊤ := by
                intro R QM hR
                apply lt_of_le_of_lt (b := ((B + D * (phiHat φ s + QM) : ℝ) : EReal)) _ (EReal.coe_lt_top _)
                apply iSup_le
                intro G
                apply iSup_le
                intro hGR
                obtain ⟨hGs, hGm⟩ := hR G hGR
                have hφG := (hmoment G hGs).mp hGm.1
                have hcG := hfint G hGs hφG
                rw [expectR, if_pos hcG]
                apply EReal.coe_le_coe_iff.mpr
                have hle : (∫ ξ, c x ξ ∂(G : Measure ℝ)) ≤ B + D * (∫ ξ, φ ξ ∂(G : Measure ℝ)) := by
                  have hi := integral_mono_ae hcG ((integrable_const B).add (hφG.const_mul D))
                    ((hae G hGs).mono (fun ξ hξ => (le_abs_self (c x ξ)).trans (hbound ξ hξ)))
                  change (∫ ξ, c x ξ ∂(G : Measure ℝ)) ≤ ∫ ξ, (B + D * φ ξ) ∂(G : Measure ℝ) at hi
                  simpa [integral_add (integrable_const B) (hφG.const_mul D), integral_const_mul] using hi
                have hm : (∫ ξ, φ ξ ∂(G : Measure ℝ)) ≤ phiHat φ s + QM := by
                  have := (abs_le.mp hGm.2).2
                  linarith
                nlinarith only [hle, mul_le_mul_of_nonneg_left hm hD]
              let z : ℝ → Fin N → ℝ := fun ξ i => (Set.Iic (ord s i)).indicator (fun _ => 1) ξ
              have hzi : ∀ (G : ProbabilityMeasure ℝ) (i : Fin N), Integrable (fun ξ => z ξ i) (G : Measure ℝ) := by
                intro G i
                exact (integrable_const 1).indicator measurableSet_Iic
              have hzv : ∀ (G : ProbabilityMeasure ℝ) (i : Fin N),
                  (∫ ξ, z ξ i ∂(G : Measure ℝ)) = u G s i := by
                intro G i
                simp [z, u, cdfOf, ProbabilityTheory.cdf_eq_real, integral_indicator measurableSet_Iic]
              have hord : Monotone (ord s) := Tuple.monotone_sort s
              have hcell : ∀ ξ ∈ Ξ, ∃ k : Fin (N + 1), ξ ∈ cell Ξ s k := by
                intro ξ hξ
                let n := (Finset.univ.filter (fun i : Fin N => ord s i < ξ)).card
                have hn : n ≤ N := by
                  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
                refine ⟨⟨n, by omega⟩, hξ, ?_, ?_⟩
                · intro hn0
                  change 0 < n at hn0
                  exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone hord).mp (by change n - 1 < n; omega)
                · intro hnN
                  apply le_of_not_gt
                  intro hlt
                  have hh := (Tuple.lt_card_lt_iff_apply_lt_of_monotone (j := (⟨n, hnN⟩ : Fin N)) hord).mpr hlt
                  change n < n at hh
                  omega
              have hzc : ∀ (k : Fin (N + 1)) ξ, ξ ∈ cell Ξ s k →
                  ∀ i : Fin N, z ξ i = if (k : ℕ) ≤ (i : ℕ) then 1 else 0 := by
                intro k ξ hξ i
                rcases hξ with ⟨hξ, hlo, hhi⟩
                dsimp [z]
                by_cases hki : (k : ℕ) ≤ (i : ℕ)
                · rw [if_pos hki, Set.indicator_of_mem]
                  exact (hhi (by omega)).trans (hord (by change (k : ℕ) ≤ (i : ℕ); exact hki))
                · rw [if_neg hki, Set.indicator_of_notMem]
                  change ¬ ξ ≤ ord s i
                  have hk0 : 0 < (k : ℕ) := by omega
                  have hh := hlo hk0
                  exact not_le.mpr ((hord (by simp only [Fin.le_iff_val_le_val]; omega)).trans_lt hh)
              have htail : ∀ n : ℕ, ∀ (w : Fin (n + 1) → ℝ) (k : Fin (n + 1)),
                  (∑ i : Fin n, if (k : ℕ) ≤ (i : ℕ) then w i.castSucc - w i.succ else 0) =
                    w k - w (Fin.last n) := by
                intro n
                induction n with
                | zero =>
                  intro w k
                  have hk : k = 0 := by apply Fin.ext; omega
                  subst k
                  simp
                | succ n ih =>
                  intro w k
                  refine Fin.cases ?_ (fun k => ?_) k
                  · rw [Fin.sum_univ_succ]
                    have hh := ih (fun j => w j.succ) 0
                    simp only [Fin.val_zero, Nat.zero_le, ite_true] at hh ⊢
                    simpa [Fin.succ_last, Fin.castSucc_succ] using (show
                      (w 0 - w (0 : Fin (n + 1)).succ) +
                        (∑ i : Fin n, (w (Fin.succ i.castSucc) - w (Fin.succ (Fin.succ i)))) = w 0 - w (Fin.last n).succ by
                          rw [hh]; ring)
                  · rw [Fin.sum_univ_succ]
                    simpa [Fin.val_succ, Fin.castSucc_succ, Fin.succ_last] using
                      ih (fun j => w j.succ) k
              have htel : ∀ (w : Fin (N + 1) → ℝ) (k : Fin (N + 1)) ξ, ξ ∈ cell Ξ s k →
                  w (Fin.last N) + ∑ i : Fin N, (w i.castSucc - w i.succ) * z ξ i = w k := by
                intro w k ξ hξ
                simp_rw [hzc k ξ hξ, mul_ite, mul_one, mul_zero]
                rw [htail]
                ring
              have htaildiff : ∀ (q : Fin N → ℝ) (i : Fin N),
                  (∑ j : Fin N, if (i : ℕ) ≤ (j : ℕ) then q j else 0) -
                    (∑ j : Fin N, if (i : ℕ) + 1 ≤ (j : ℕ) then q j else 0) = q i := by
                intro q i
                rw [← Finset.sum_sub_distrib]
                rw [Finset.sum_eq_single i]
                · simp
                · intro j _ hji
                  have hne : (j : ℕ) ≠ (i : ℕ) := by intro hh; exact hji (Fin.ext hh)
                  by_cases hij : (i : ℕ) ≤ (j : ℕ)
                  · simp [hij, show (i : ℕ) + 1 ≤ (j : ℕ) by omega]
                  · simp [hij, show ¬ (i : ℕ) + 1 ≤ (j : ℕ) by omega]
                · simp
              have hdot : ∀ (J : Type) [Fintype J] (A : Matrix J (Fin N) ℝ) (r : J → ℝ) (v : Fin N → ℝ),
                  (∑ i, (A.transpose.mulVec r) i * v i) = ∑ j, r j * (A.mulVec v) j := by
                intro J _ A r v
                simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j _
                apply Finset.sum_congr rfl
                intro i _
                ring
              have hweak : ∀ (J : Type) [Fintype J] (A : Matrix J (Fin N) ℝ) (b : J → ℝ)
                  (K : Set (J → ℝ)) (QM : ℝ) (R : Set (ProbabilityMeasure ℝ)),
                  (∀ G ∈ R, SupportedOn Ξ G ∧ G ∈ momentRegion φ QM s ∧ (A.mulVec (u G s) - b) ∈ K) →
                  ∀ v ∈ momentDualValues A b K Ξ (c x) φ QM s, worstCaseR R (c x) ≤ (v : EReal) := by
                intro J _ A b K QM R hR v hv
                clear * - hR hv hmoment hfint hcell htel hzi hzv hdot hae
                obtain ⟨r, t, t', w, hr, ht, ht', hw, hwc, rfl⟩ := hv
                apply iSup_le
                intro G
                apply iSup_le
                intro hGR
                obtain ⟨hGs, hGm, hGK⟩ := hR G hGR
                have hφG := (hmoment G hGs).mp hGm.1
                have hcG := hfint G hGs hφG
                rw [expectR, if_pos hcG]
                apply EReal.coe_le_coe_iff.mpr
                let q : Fin N → ℝ := A.transpose.mulVec r
                have hqi : ∀ i, Integrable (fun ξ => q i * z ξ i) (G : Measure ℝ) :=
                  fun i => (hzi G i).const_mul _
                have hp : ∀ ξ ∈ Ξ, c x ξ ≤ w (Fin.last N) + (∑ i, q i * z ξ i) + (t - t') * φ ξ := by
                  intro ξ hξ
                  obtain ⟨k, hk⟩ := hcell ξ hξ
                  have hh := hwc k ξ hk
                  have heq := htel w k ξ hk
                  simp_rw [← hw] at heq
                  change w (Fin.last N) + (∑ i, q i * z ξ i) = w k at heq
                  linarith
                have hi := integral_mono_ae hcG
                  (((integrable_const (w (Fin.last N))).add (integrable_finset_sum _ (fun i _ => hqi i))).add
                    (hφG.const_mul (t - t')))
                  ((hae G hGs).mono (fun ξ hξ => hp ξ hξ))
                change (∫ ξ, c x ξ ∂(G : Measure ℝ)) ≤
                  ∫ ξ, (w (Fin.last N) + (∑ i, q i * z ξ i) + (t - t') * φ ξ) ∂(G : Measure ℝ) at hi
                have heval : (∫ ξ, (w (Fin.last N) + (∑ i, q i * z ξ i) + (t - t') * φ ξ) ∂(G : Measure ℝ)) =
                    w (Fin.last N) + (∑ i, q i * u G s i) + (t - t') * (∫ ξ, φ ξ ∂(G : Measure ℝ)) := by
                  rw [integral_add (f := fun ξ => w (Fin.last N) + ∑ i, q i * z ξ i)
                    (g := fun ξ => (t - t') * φ ξ)
                    ((integrable_const _).add (integrable_finset_sum _ (fun i _ => hqi i))) (hφG.const_mul _)]
                  rw [integral_add (f := fun _ => w (Fin.last N)) (g := fun ξ => ∑ i, q i * z ξ i)
                    (integrable_const _) (integrable_finset_sum _ (fun i _ => hqi i))]
                  rw [integral_finset_sum _ (fun i _ => hqi i)]
                  simp [integral_const_mul, hzv]
                rw [heval, hdot J A r (u G s)] at hi
                have hrineq := hr (A.mulVec (u G s) - b) hGK
                have hrineq' : (∑ j, r j * (A.mulVec (u G s)) j) ≤ ∑ j, b j * r j := by
                  simp only [Pi.sub_apply, neg_mul, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hrineq
                  have hh : (∑ j, r j * b j) = ∑ j, b j * r j := by
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
                  linarith
                obtain ⟨hmlo, hmhi⟩ := abs_le.mp hGm.2
                have hmt := mul_le_mul_of_nonneg_left hmhi ht
                have hmt' := mul_le_mul_of_nonneg_left hmlo ht'
                nlinarith only [hi, hrineq', hmt, hmt']
              have hconic : ∀ (J : Type) [Fintype J] (A : Matrix J (Fin N) ℝ) (b : J → ℝ)
                  (K : Set (J → ℝ)), Convex ℝ K → (0 : J → ℝ) ∈ K →
                  (∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K) →
                  ∀ (QM : ℝ) (R : Set (ProbabilityMeasure ℝ)),
                  (∀ G, G ∈ R ↔ SupportedOn Ξ G ∧ G ∈ momentRegion φ QM s ∧ (A.mulVec (u G s) - b) ∈ K) →
                  (∃ G : ProbabilityMeasure ℝ, SupportedOn Ξ G ∧
                    (∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(G : Measure ℝ)) < ⊤ ∧
                    |(∫ ξ, φ ξ ∂(G : Measure ℝ)) - phiHat φ s| < QM ∧
                    (A.mulVec (u G s) - b) ∈ interior K) →
                  IsMinValue (worstCaseR R (c x)) (momentDualValues A b K Ξ (c x) φ QM s) := by
                intro J _ A b K hK hzero hscale QM R hR hstrict
                clear * - hfinite hgen hmoment hzi hzv htaildiff hzc hdot hweak hK hzero hscale hR hstrict
                let U := phiHat φ s + QM
                let L := phiHat φ s - QM
                let C : Set (Option (Option J) → ℝ) :=
                  {y | (fun j => y (some (some j))) ∈ K ∧ 0 ≤ y none ∧ 0 ≤ y (some none)}
                have hC : Convex ℝ C := by
                  intro y hy y' hy' a b ha hb hab
                  refine ⟨hK hy.1 hy'.1 ha hb hab, ?_, ?_⟩
                  · exact add_nonneg (mul_nonneg ha hy.2.1) (mul_nonneg hb hy'.2.1)
                  · exact add_nonneg (mul_nonneg ha hy.2.2) (mul_nonneg hb hy'.2.2)
                have hCzero : (0 : Option (Option J) → ℝ) ∈ C := ⟨hzero, le_rfl, le_rfl⟩
                have hCscale : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ C, t • y ∈ C := by
                  intro t ht y hy
                  exact ⟨hscale t ht _ hy.1, mul_nonneg ht hy.2.1, mul_nonneg ht hy.2.2⟩
                let g : ℝ → Option (Option J) → ℝ := fun ξ o => match o with
                  | none => -φ ξ
                  | some none => φ ξ
                  | some (some j) => (A.mulVec (z ξ)) j
                let d : Option (Option J) → ℝ
                  | none => -U
                  | some none => L
                  | some (some j) => b j
                have hAi : ∀ (G : ProbabilityMeasure ℝ) j,
                    Integrable (fun ξ => (A.mulVec (z ξ)) j) (G : Measure ℝ) := by
                  intro G j
                  change Integrable (fun ξ => ∑ i, A j i * z ξ i) (G : Measure ℝ)
                  exact integrable_finset_sum _ (fun i _ => (hzi G i).const_mul (A j i))
                have hAv : ∀ (G : ProbabilityMeasure ℝ) j,
                    (∫ ξ, (A.mulVec (z ξ)) j ∂(G : Measure ℝ)) = (A.mulVec (u G s)) j := by
                  intro G j
                  change (∫ ξ, ∑ i, A j i * z ξ i ∂(G : Measure ℝ)) = _
                  rw [integral_finset_sum _ (fun i _ => (hzi G i).const_mul (A j i))]
                  simp only [integral_const_mul, hzv, Matrix.mulVec, dotProduct]
                have hgi : ∀ (G : ProbabilityMeasure ℝ), SupportedOn Ξ G → Integrable φ (G : Measure ℝ) →
                    ∀ j, Integrable (fun ξ => g ξ j) (G : Measure ℝ) := by
                  intro G hGs hφG j
                  rcases j with _ | (_ | j)
                  · exact hφG.neg
                  · exact hφG
                  · exact hAi G j
                let slack : ProbabilityMeasure ℝ → Option (Option J) → ℝ := fun G o => match o with
                  | none => U - ∫ ξ, φ ξ ∂(G : Measure ℝ)
                  | some none => (∫ ξ, φ ξ ∂(G : Measure ℝ)) - L
                  | some (some j) => (A.mulVec (u G s) - b) j
                have hslack : ∀ G : ProbabilityMeasure ℝ,
                    (fun j => (∫ ξ, g ξ j ∂(G : Measure ℝ)) - d j) = slack G := by
                  intro G
                  ext o
                  rcases o with _ | (_ | j)
                  · simp [g, d, slack, integral_neg]; ring
                  · rfl
                  · exact congrArg (fun t : ℝ => t - b j) (hAv G j)
                have hRC : ∀ G, G ∈ R ↔ SupportedOn Ξ G ∧ Integrable φ (G : Measure ℝ) ∧
                    (fun j => (∫ ξ, g ξ j ∂(G : Measure ℝ)) - d j) ∈ C := by
                  intro G
                  rw [hR, hslack]
                  constructor
                  · rintro ⟨hGs, hGm, hGK⟩
                    refine ⟨hGs, (hmoment G hGs).mp hGm.1, hGK, ?_, ?_⟩
                    · have := (abs_le.mp hGm.2).2
                      change 0 ≤ U - _
                      dsimp [U]; linarith
                    · have := (abs_le.mp hGm.2).1
                      change 0 ≤ _ - L
                      dsimp [L]; linarith
                  · rintro ⟨hGs, hφG, hGK, hU, hL⟩
                    refine ⟨hGs, ⟨(hmoment G hGs).mpr hφG, ?_⟩, hGK⟩
                    change 0 ≤ U - _ at hU
                    change 0 ≤ _ - L at hL
                    rw [abs_le]
                    dsimp [U, L] at *
                    constructor <;> linarith
                obtain ⟨G₀, hGs₀, hGm₀, hdev₀, hGK₀⟩ := hstrict
                have hGstrict : (slack G₀) ∈ interior C := by
                  let O : Set (Option (Option J) → ℝ) :=
                    {y | (fun j => y (some (some j))) ∈ interior K ∧ 0 < y none ∧ 0 < y (some none)}
                  have hO : IsOpen O :=
                    (isOpen_interior.preimage (continuous_pi (fun j => continuous_apply (some (some j))))).inter
                      ((isOpen_lt continuous_const (continuous_apply none)).inter
                        (isOpen_lt continuous_const (continuous_apply (some none))))
                  have hmem : slack G₀ ∈ O := by
                    refine ⟨hGK₀, ?_, ?_⟩
                    · have := (abs_lt.mp hdev₀).2
                      change 0 < U - _
                      dsimp [U]; linarith
                    · have := (abs_lt.mp hdev₀).1
                      change 0 < _ - L
                      dsimp [L]; linarith
                  exact mem_interior_iff_mem_nhds.mpr
                    (Filter.mem_of_superset (hO.mem_nhds hmem) (fun y hy => ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩))
                have hfin := hfinite R QM (fun G hG => ⟨((hR G).mp hG).1, ((hR G).mp hG).2.1⟩)
                obtain ⟨V, ρ, hWV, hρ, hp⟩ := hgen (Option (Option J)) C hC hCzero hCscale g d hgi R hRC hfin
                  ⟨G₀, hGs₀, (hmoment G₀ hGs₀).mp hGm₀, by rw [hslack]; exact hGstrict⟩
                let r : J → ℝ := fun j => ρ (some (some j))
                let t : ℝ := -ρ none
                let t' : ℝ := -ρ (some none)
                have ht : 0 ≤ t := by
                  have hh := hρ (fun o => if o = none then 1 else 0) (by
                    refine ⟨?_, by simp, by simp⟩
                    convert hzero using 1 <;> ext j <;> simp)
                  simpa [t, Fintype.sum_option] using hh
                have ht' : 0 ≤ t' := by
                  have hh := hρ (fun o => if o = some none then 1 else 0) (by
                    refine ⟨?_, by simp, by simp⟩
                    convert hzero using 1 <;> ext j <;> simp)
                  simpa [t', Fintype.sum_option] using hh
                have hr : (fun j => -r j) ∈ dualCone K := by
                  intro y hy
                  let yy : Option (Option J) → ℝ
                    | none => 0
                    | some none => 0
                    | some (some j) => y j
                  have hh := hρ yy ⟨hy, le_rfl, le_rfl⟩
                  simpa [yy, r, Fintype.sum_option] using hh
                let q := A.transpose.mulVec r
                let β : ℝ := V - (∑ j, b j * r j) - U * t + L * t'
                let w : Fin (N + 1) → ℝ := fun k => β + ∑ i : Fin N, if (k : ℕ) ≤ (i : ℕ) then q i else 0
                have hwlast : w (Fin.last N) = β := by
                  apply add_eq_left.mpr
                  apply Finset.sum_eq_zero
                  intro i _
                  exact if_neg (by have := i.isLt; simp only [Fin.val_last]; omega)
                have hw : ∀ i : Fin N, (A.transpose.mulVec r) i = w i.castSucc - w i.succ := by
                  intro i
                  dsimp only [w, Fin.val_castSucc, Fin.val_succ]
                  have hh := htaildiff q i
                  change q i = _
                  linarith
                have hp' : ∀ ξ ∈ Ξ, c x ξ - (t - t') * φ ξ ≤ β + ∑ i, q i * z ξ i := by
                  intro ξ hξ
                  have hh := hp ξ hξ
                  simp only [Fintype.sum_option, g, d] at hh
                  have hsum : (∑ j, r j * ((A.mulVec (z ξ)) j - b j)) =
                      (∑ i, q i * z ξ i) - ∑ j, b j * r j := by
                    simp only [mul_sub, Finset.sum_sub_distrib]
                    rw [← hdot J A r (z ξ)]
                    congr 1
                    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
                  change c x ξ ≤ V + (ρ none * (-φ ξ - -U) +
                    (ρ (some none) * (φ ξ - L) + ∑ j, r j * ((A.mulVec (z ξ)) j - b j))) at hh
                  rw [hsum] at hh
                  dsimp [β, t, t']
                  nlinarith only [hh]
                have hVmem : V ∈ momentDualValues A b K Ξ (c x) φ QM s := by
                  refine ⟨r, t, t', w, hr, ht, ht', hw, ?_, ?_⟩
                  · intro k ξ hξ
                    have hh := hp' ξ hξ.1
                    simp_rw [hzc k ξ hξ, mul_ite, mul_one, mul_zero] at hh
                    exact hh
                  · rw [hwlast]
                    dsimp [β, U, L]
                    ring
                refine ⟨?_, fun _ => ⟨V, hVmem, hWV⟩⟩
                apply le_antisymm
                · apply le_sInf
                  rintro y ⟨v, hv, rfl⟩
                  exact hweak J A b K QM R (fun G hG => (hR G).mp hG) v hv
                · rw [hWV]
                  exact sInf_le (Set.mem_image_of_mem _ hVmem)
              clear * - hconic hN
              letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
              have hmax : ∀ f : Fin N → ℝ, ∃ i, (⨆ j, f j) = f i := by
                intro f
                obtain ⟨i, hi⟩ := Finite.exists_max f
                refine ⟨i, le_antisymm (ciSup_le hi) (le_ciSup (Set.finite_range f).bddAbove i)⟩
              have hmin : ∀ f : Fin N → ℝ, ∃ i, (⨅ j, f j) = f i := by
                intro f
                obtain ⟨i, hi⟩ := Finite.exists_min f
                exact ⟨i, le_antisymm (ciInf_le (Set.finite_range f).bddBelow i) (le_ciInf hi)⟩
              have hinfsup : ∀ (f : Fin N → ℝ) a, (⨅ i, a - f i) = a - ⨆ i, f i := by
                intro f a
                obtain ⟨i, hi⟩ := hmax f
                rw [hi]
                apply le_antisymm (ciInf_le (Set.finite_range (fun j => a - f j)).bddBelow i)
                apply le_ciInf
                intro j
                have hh := le_ciSup (Set.finite_range f).bddAbove j
                rw [hi] at hh
                linarith
              have hAmul : ∀ ζ : Fin N → ℝ, ∀ i : Fin N ⊕ Fin N,
                  (A_KS N).mulVec ζ i = Sum.elim ζ (fun j => -ζ j) i := by
                intro ζ i
                rcases i with i | i
                · change ((1 : Matrix (Fin N) (Fin N) ℝ).mulVec ζ) i = ζ i
                  simp
                · change ((-1 : Matrix (Fin N) (Fin N) ℝ).mulVec ζ) i = -ζ i
                  rw [Matrix.neg_mulVec, Matrix.one_mulVec]
                  rfl
              have hnonnegint : ∀ (J : Type) [Fintype J] (y : J → ℝ), (∀ j, 0 < y j) →
                  y ∈ interior {v : J → ℝ | ∀ j, 0 ≤ v j} := by
                intro J _ y hy
                have hO : IsOpen {v : J → ℝ | ∀ j, 0 < v j} := by
                  simp only [Set.setOf_forall]
                  exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (continuous_apply j))
                exact mem_interior_iff_mem_nhds.mpr
                  (Filter.mem_of_superset (hO.mem_nhds hy) (fun v hv j => (hv j).le))
              have hKSconv : Convex ℝ (K_KS N) := by
                intro v hv w hw a b ha hb hab j
                exact add_nonneg (mul_nonneg ha (hv j)) (mul_nonneg hb (hw j))
              have hKSzero : (0 : Fin N ⊕ Fin N → ℝ) ∈ K_KS N := by intro j; simp
              have hKSscale : ∀ t : ℝ, 0 ≤ t → ∀ v ∈ K_KS N, t • v ∈ K_KS N := by
                intro t ht v hv j
                exact mul_nonneg ht (hv j)
              have hKSenc : ∀ Q (ζ : Fin N → ℝ), ksZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_KS N Q ∈ K_KS N := by
                intro Q ζ
                constructor
                · intro h i
                  rcases i with i | i
                  · have hh := (le_ciSup (Set.finite_range (fun i : Fin N =>
                      max (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N))).bddAbove i).trans h
                    have := (max_le_iff.mp hh).1
                    simp only [Pi.sub_apply, hAmul, Sum.elim_inl, b_KS]
                    linarith
                  · have hh := (le_ciSup (Set.finite_range (fun i : Fin N =>
                      max (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N))).bddAbove i).trans h
                    have := (max_le_iff.mp hh).2
                    simp only [Pi.sub_apply, hAmul, Sum.elim_inr, b_KS]
                    linarith
                · intro h
                  apply ciSup_le
                  intro i
                  have hl := h (Sum.inl i)
                  have hr := h (Sum.inr i)
                  simp only [Pi.sub_apply, hAmul, Sum.elim_inl, Sum.elim_inr, b_KS] at hl hr
                  exact max_le (by linarith) (by linarith)
              have hKSstrict : ∀ Q (ζ : Fin N → ℝ), ksZ ζ < Q →
                  (A_KS N).mulVec ζ - b_KS N Q ∈ interior (K_KS N) := by
                intro Q ζ h
                apply hnonnegint
                intro i
                rcases i with i | i
                · have hh := (le_ciSup (Set.finite_range (fun i : Fin N =>
                    max (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N))).bddAbove i).trans_lt h
                  have hx := (le_max_left (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N)).trans_lt hh
                  simp only [Pi.sub_apply, hAmul, Sum.elim_inl, b_KS]
                  linarith
                · have hh := (le_ciSup (Set.finite_range (fun i : Fin N =>
                    max (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N))).bddAbove i).trans_lt h
                  have hx := (le_max_right (((i : ℕ) + 1 : ℝ) / N - ζ i) (ζ i - ((i : ℕ) : ℝ) / N)).trans_lt hh
                  simp only [Pi.sub_apply, hAmul, Sum.elim_inr, b_KS]
                  linarith
              have hKpair : ∀ v : Fin N ⊕ Fin N → ℝ,
                  v ∈ K_Kuiper N ↔ ∀ i j : Fin N, 0 ≤ v (Sum.inl i) + v (Sum.inr j) := by
                intro v
                constructor
                · intro hv i j
                  have hl := ciInf_le (Set.finite_range (fun i => v (Sum.inl i))).bddBelow i
                  have hr := ciInf_le (Set.finite_range (fun j => v (Sum.inr j))).bddBelow j
                  change 0 ≤ (⨅ i, v (Sum.inl i)) + (⨅ j, v (Sum.inr j)) at hv
                  linarith
                · intro hv
                  obtain ⟨i, hi⟩ := hmin (fun i => v (Sum.inl i))
                  obtain ⟨j, hj⟩ := hmin (fun j => v (Sum.inr j))
                  change 0 ≤ (⨅ i, v (Sum.inl i)) + (⨅ j, v (Sum.inr j))
                  rw [hi, hj]
                  exact hv i j
              have hKuiperconv : Convex ℝ (K_Kuiper N) := by
                intro v hv w hw a b ha hb hab
                rw [hKpair] at hv hw ⊢
                intro i j
                have h₁ := mul_nonneg ha (hv i j)
                have h₂ := mul_nonneg hb (hw i j)
                change 0 ≤ a * v (Sum.inl i) + b * w (Sum.inl i) + (a * v (Sum.inr j) + b * w (Sum.inr j))
                nlinarith only [h₁, h₂]
              have hKuiperzero : (0 : Fin N ⊕ Fin N → ℝ) ∈ K_Kuiper N := by
                rw [hKpair]; intro i j; simp
              have hKuiperscale : ∀ t : ℝ, 0 ≤ t → ∀ v ∈ K_Kuiper N, t • v ∈ K_Kuiper N := by
                intro t ht v hv
                rw [hKpair] at hv ⊢
                intro i j
                simpa only [Pi.smul_apply, smul_eq_mul, mul_add] using mul_nonneg ht (hv i j)
              have hKuiperid : ∀ Q (ζ : Fin N → ℝ),
                  (⨅ i, ((A_KS N).mulVec ζ - b_Kuiper N Q) (Sum.inl i)) +
                    (⨅ i, ((A_KS N).mulVec ζ - b_Kuiper N Q) (Sum.inr i)) = Q - kuiperZ ζ := by
                intro Q ζ
                have hl : (fun i : Fin N => ((A_KS N).mulVec ζ - b_Kuiper N Q) (Sum.inl i)) =
                    (fun i : Fin N => Q / 2 - (((i : ℕ) + 1 : ℝ) / N - ζ i)) := by
                  ext i; simp only [Pi.sub_apply, hAmul, Sum.elim_inl, b_Kuiper]; ring
                have hr : (fun i : Fin N => ((A_KS N).mulVec ζ - b_Kuiper N Q) (Sum.inr i)) =
                    (fun i : Fin N => Q / 2 - (ζ i - ((i : ℕ) : ℝ) / N)) := by
                  ext i; simp only [Pi.sub_apply, hAmul, Sum.elim_inr, b_Kuiper]; ring
                rw [hl, hr, hinfsup, hinfsup]
                dsimp [kuiperZ]
                ring
              have hKuiperenc : ∀ Q (ζ : Fin N → ℝ), kuiperZ ζ ≤ Q ↔
                  (A_KS N).mulVec ζ - b_Kuiper N Q ∈ K_Kuiper N := by
                intro Q ζ
                simp only [K_Kuiper, Set.mem_setOf_eq]
                rw [hKuiperid]
                exact sub_nonneg.symm
              have hKuiperstrict : ∀ Q (ζ : Fin N → ℝ), kuiperZ ζ < Q →
                  (A_KS N).mulVec ζ - b_Kuiper N Q ∈ interior (K_Kuiper N) := by
                intro Q ζ hζ
                have hO : IsOpen {v : Fin N ⊕ Fin N → ℝ | ∀ i j, 0 < v (Sum.inl i) + v (Sum.inr j)} := by
                  simp only [Set.setOf_forall]
                  apply isOpen_iInter_of_finite
                  intro i
                  apply isOpen_iInter_of_finite
                  intro j
                  exact isOpen_lt continuous_const ((continuous_apply _).add (continuous_apply _))
                apply mem_interior_iff_mem_nhds.mpr
                apply Filter.mem_of_superset (hO.mem_nhds ?_)
                · intro v hv
                  rw [hKpair]
                  exact fun i j => (hv i j).le
                · intro i j
                  have hl := ciInf_le (Set.finite_range (fun i : Fin N => ((A_KS N).mulVec ζ - b_Kuiper N Q) (Sum.inl i))).bddBelow i
                  have hr := ciInf_le (Set.finite_range (fun j => ((A_KS N).mulVec ζ - b_Kuiper N Q) (Sum.inr j))).bddBelow j
                  have hh := hKuiperid Q ζ
                  linarith
              have hSOCnorm : ∀ (J : Type) [Fintype J] (v : Option J → ℝ),
                  Real.sqrt (∑ i, v (some i) ^ 2) = ‖(WithLp.toLp 2 (fun i => v (some i)) : EuclideanSpace ℝ J)‖ := by
                intro J _ v
                simp [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
              have hSOCconv : ∀ (J : Type) [Fintype J], Convex ℝ (soc J) := by
                intro J _ v hv w hw a b ha hb hab
                change Real.sqrt (∑ i, (a * v (some i) + b * w (some i)) ^ 2) ≤ a * v none + b * w none
                have hnorm := hSOCnorm J (a • v + b • w)
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hnorm
                rw [hnorm]
                have heq : (WithLp.toLp 2 (fun i => a * v (some i) + b * w (some i)) : EuclideanSpace ℝ J) =
                    a • WithLp.toLp 2 (fun i => v (some i)) + b • WithLp.toLp 2 (fun i => w (some i)) := by
                  rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
                  rfl
                rw [heq]
                calc
                  _ ≤ ‖a • (WithLp.toLp 2 (fun i => v (some i)) : EuclideanSpace ℝ J)‖ +
                    ‖b • (WithLp.toLp 2 (fun i => w (some i)) : EuclideanSpace ℝ J)‖ := norm_add_le _ _
                  _ = a * Real.sqrt (∑ i, v (some i) ^ 2) + b * Real.sqrt (∑ i, w (some i) ^ 2) := by
                    rw [norm_smul, norm_smul, ← hSOCnorm J v, ← hSOCnorm J w]
                    simp [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
                  _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
              have hSOCzero : ∀ (J : Type) [Fintype J], (0 : Option J → ℝ) ∈ soc J := by
                intro J _; simp [soc]
              have hSOCscale : ∀ (J : Type) [Fintype J] (t : ℝ), 0 ≤ t → ∀ v ∈ soc J, t • v ∈ soc J := by
                intro J _ t ht v hv
                change Real.sqrt (∑ i, (t * v (some i)) ^ 2) ≤ t * v none
                have hnorm := hSOCnorm J (t • v)
                simp only [Pi.smul_apply, smul_eq_mul] at hnorm
                rw [hnorm]
                have heq : (WithLp.toLp 2 (fun i => t * v (some i)) : EuclideanSpace ℝ J) =
                    t • WithLp.toLp 2 (fun i => v (some i)) := by rw [← WithLp.toLp_smul]; rfl
                rw [heq, norm_smul, ← hSOCnorm J v]
                simp only [Real.norm_eq_abs, abs_of_nonneg ht]
                exact mul_le_mul_of_nonneg_left hv ht
              have hSOCstrict : ∀ (J : Type) [Fintype J] (v : Option J → ℝ),
                  Real.sqrt (∑ i, v (some i) ^ 2) < v none → v ∈ interior (soc J) := by
                intro J _ v hv
                have hO : IsOpen {y : Option J → ℝ | Real.sqrt (∑ i, y (some i) ^ 2) < y none} := by
                  apply isOpen_lt _ (continuous_apply none)
                  exact Real.continuous_sqrt.comp (continuous_finset_sum _ (fun i _ => (continuous_apply _).pow 2))
                exact mem_interior_iff_mem_nhds.mpr
                  (Filter.mem_of_superset (hO.mem_nhds hv) (fun y hy => (show Real.sqrt (∑ i, y (some i) ^ 2) ≤ y none from hy.le)))
              have hnreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
              have hnne : (N : ℝ) ≠ 0 := ne_of_gt hnreal
              let mid : Fin N → ℝ := fun i => (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N)
              have hCvMrad : ∀ ζ : Fin N → ℝ,
                  0 ≤ 1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) * ∑ i, (mid i - ζ i) ^ 2 := by
                intro ζ
                positivity
              have hCvMsq : ∀ ζ : Fin N → ℝ, cvmZ ζ ^ 2 =
                  1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) * ∑ i, (mid i - ζ i) ^ 2 := by
                intro ζ
                exact Real.sq_sqrt (hCvMrad ζ)
              have hCvmul : ∀ (ζ : Fin N → ℝ) (o : Option (Fin N)),
                  (A_CvM N).mulVec ζ o = Option.elim o 0 ζ := by
                intro ζ o
                cases o with
                | none => simp [A_CvM, Matrix.mulVec, dotProduct]
                | some i => simp [A_CvM, Matrix.mulVec, dotProduct]
              have hCVMenc : ∀ Q : ℝ, 0 ≤ Q → 1 / (12 * (N : ℝ) ^ 2) ≤ Q ^ 2 →
                  ∀ ζ : Fin N → ℝ, cvmZ ζ ≤ Q ↔ (A_CvM N).mulVec ζ - b_CvM N Q ∈ K_CvM N := by
                intro Q hQ hQmin ζ
                have hr : 0 ≤ (N : ℝ) * Q ^ 2 - 1 / (12 * (N : ℝ)) := by
                  have heq : (N : ℝ) * (1 / (12 * (N : ℝ) ^ 2)) = 1 / (12 * (N : ℝ)) := by field_simp <;> ring
                  nlinarith [mul_le_mul_of_nonneg_left hQmin hnreal.le]
                have hs : (∑ i : Fin N, (ζ i - mid i) ^ 2) = ∑ i, (mid i - ζ i) ^ 2 := by
                  apply Finset.sum_congr rfl; intro i _; ring
                change cvmZ ζ ≤ Q ↔ Real.sqrt (∑ i, ((A_CvM N).mulVec ζ (some i) - b_CvM N Q (some i)) ^ 2) ≤
                  (A_CvM N).mulVec ζ none - b_CvM N Q none
                simp only [hCvmul, Option.elim, b_CvM, zero_sub, neg_neg]
                change cvmZ ζ ≤ Q ↔ Real.sqrt (∑ i, (ζ i - mid i) ^ 2) ≤ Real.sqrt ((N : ℝ) * Q ^ 2 - 1 / (12 * (N : ℝ)))
                rw [hs, Real.sqrt_le_left (Real.sqrt_nonneg _), Real.sq_sqrt hr]
                change Real.sqrt _ ≤ Q ↔ _
                rw [Real.sqrt_le_left hQ]
                have hmul : (N : ℝ) * (1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) * ∑ i, (mid i - ζ i) ^ 2) =
                    1 / (12 * (N : ℝ)) + ∑ i, (mid i - ζ i) ^ 2 := by field_simp <;> ring
                constructor <;> intro hh <;> nlinarith only [hh, hmul, hnreal]
              have hCVMstrict : ∀ Q (ζ : Fin N → ℝ), cvmZ ζ < Q →
                  (A_CvM N).mulVec ζ - b_CvM N Q ∈ interior (K_CvM N) := by
                intro Q ζ hζ
                have hQ : 0 < Q := (Real.sqrt_nonneg _).trans_lt hζ
                have hsq : 1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) * ∑ i, (mid i - ζ i) ^ 2 < Q ^ 2 :=
                  (Real.sqrt_lt' hQ).mp hζ
                apply hSOCstrict
                change Real.sqrt (∑ i, ((A_CvM N).mulVec ζ (some i) - b_CvM N Q (some i)) ^ 2) <
                  (A_CvM N).mulVec ζ none - b_CvM N Q none
                simp only [hCvmul, Option.elim, b_CvM, zero_sub, neg_neg]
                apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
                have heq : (∑ i : Fin N, (ζ i - mid i) ^ 2) = ∑ i, (mid i - ζ i) ^ 2 := by
                  apply Finset.sum_congr rfl; intro i _; ring
                change (∑ i, (ζ i - mid i) ^ 2) < _
                rw [heq]
                have hmul : (N : ℝ) * (1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) * ∑ i, (mid i - ζ i) ^ 2) =
                    1 / (12 * (N : ℝ)) + ∑ i, (mid i - ζ i) ^ 2 := by field_simp <;> ring
                nlinarith only [hmul, mul_lt_mul_of_pos_left hsq hnreal]
              have hGM : ∀ (J : Type) [Fintype J] (w : J → ℝ),
                  (∀ j, 0 < w j) → (∑ j, w j) = 1 →
                  let G : (J → ℝ) → ℝ := fun v => ∏ j, (v j) ^ (w j)
                  (∀ v, (∀ j, 0 ≤ v j) → 0 ≤ G v) ∧
                  (∀ t : ℝ, 0 ≤ t → ∀ v, (∀ j, 0 ≤ v j) → G (t • v) = t * G v) ∧
                  (∀ v v', (∀ j, 0 ≤ v j) → (∀ j, 0 ≤ v' j) → G v + G v' ≤ G (v + v')) := by
                intro J _ w hw hws G
                have hGpos : ∀ v, (∀ j, 0 ≤ v j) → 0 ≤ G v := by
                  intro v hv
                  exact Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hv j) _)
                refine ⟨hGpos, ?_, ?_⟩
                · intro t ht v hv
                  change (∏ j, (t * v j) ^ w j) = _
                  simp_rw [Real.mul_rpow ht (hv _)]
                  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_nonneg ht (fun j _ => (hw j).le), hws, Real.rpow_one]
                · intro v v' hv hv'
                  by_cases hz : ∃ j, v j + v' j = 0
                  · obtain ⟨j, hj⟩ := hz
                    have hjv : v j = 0 := by linarith [hv j, hv' j]
                    have hjv' : v' j = 0 := by linarith [hv j, hv' j]
                    have hGv : G v = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ j)
                      rw [hjv, Real.zero_rpow (ne_of_gt (hw j))]
                    have hGv' : G v' = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ j)
                      rw [hjv', Real.zero_rpow (ne_of_gt (hw j))]
                    rw [hGv, hGv', add_zero]
                    exact hGpos _ (fun i => add_nonneg (hv i) (hv' i))
                  · have hp : ∀ j, 0 < v j + v' j := by
                      intro j
                      exact lt_of_le_of_ne (add_nonneg (hv j) (hv' j)) (Ne.symm (fun h => hz ⟨j, h⟩))
                    let a : J → ℝ := fun j => v j / (v j + v' j)
                    let b : J → ℝ := fun j => v' j / (v j + v' j)
                    have ha : ∀ j, 0 ≤ a j := fun j => div_nonneg (hv j) (hp j).le
                    have hb : ∀ j, 0 ≤ b j := fun j => div_nonneg (hv' j) (hp j).le
                    have hab : ∀ j, a j + b j = 1 := by
                      intro j
                      dsimp [a, b]
                      rw [← add_div, div_self (ne_of_gt (hp j))]
                    have hGa := Real.geom_mean_le_arith_mean_weighted Finset.univ w a
                      (fun j _ => (hw j).le) hws (fun j _ => ha j)
                    have hGb := Real.geom_mean_le_arith_mean_weighted Finset.univ w b
                      (fun j _ => (hw j).le) hws (fun j _ => hb j)
                    have hs : (∑ j, w j * a j) + (∑ j, w j * b j) = 1 := by
                      rw [← Finset.sum_add_distrib]
                      simp_rw [← mul_add, hab, mul_one]
                      exact hws
                    have hGab : G a + G b ≤ 1 := by change G a ≤ _ at hGa; change G b ≤ _ at hGb; linarith only [hGa, hGb, hs]
                    have hGv : G v = G a * G (v + v') := by
                      change (∏ j, (v j) ^ w j) = _
                      have heq : v = a * (v + v') := by
                        ext j
                        exact (div_mul_cancel₀ _ (ne_of_gt (hp j))).symm
                      conv_lhs => rw [heq]
                      simp only [Pi.mul_apply, Pi.add_apply]
                      simp_rw [Real.mul_rpow (ha _) (add_nonneg (hv _) (hv' _))]
                      exact Finset.prod_mul_distrib
                    have hGv' : G v' = G b * G (v + v') := by
                      change (∏ j, (v' j) ^ w j) = _
                      have heq : v' = b * (v + v') := by
                        ext j
                        exact (div_mul_cancel₀ _ (ne_of_gt (hp j))).symm
                      conv_lhs => rw [heq]
                      simp only [Pi.mul_apply, Pi.add_apply]
                      simp_rw [Real.mul_rpow (hb _) (add_nonneg (hv _) (hv' _))]
                      exact Finset.prod_mul_distrib
                    rw [hGv, hGv']
                    have hh := mul_le_mul_of_nonneg_right hGab (hGpos (v + v') (fun i => add_nonneg (hv i) (hv' i)))
                    nlinarith only [hh]
              have hsumn : ∀ n : ℕ, (∑ i : Fin n, ((i : ℕ) : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
                intro n
                induction n with
                | zero => simp
                | succ n ih =>
                  rw [Fin.sum_univ_castSucc]
                  simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
                  ring
              have hsumn2 : ∀ n : ℕ, (∑ i : Fin n, ((i : ℕ) : ℝ) ^ 2) =
                  (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
                intro n
                induction n with
                | zero => simp
                | succ n ih =>
                  rw [Fin.sum_univ_castSucc]
                  simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
                  ring
              have hmid : ∀ i : Fin N, mid i = (((i : ℕ) : ℝ) + 1 / 2) / (N : ℝ) := by
                intro i
                dsimp [mid]
                ring
              have hmidsq : (∑ i : Fin N, mid i ^ 2) = (N : ℝ) / 3 - 1 / (12 * (N : ℝ)) := by
                have heq : ∀ i : Fin N, mid i ^ 2 = (((i : ℕ) : ℝ) ^ 2 + ((i : ℕ) : ℝ) + 1 / 4) / (N : ℝ) ^ 2 := by
                  intro i
                  rw [hmid]
                  ring
                simp_rw [heq]
                rw [← Finset.sum_div]
                simp only [Finset.sum_add_distrib, hsumn, hsumn2, Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul]
                field_simp
                <;> ring
              have hWa : ∀ ζ : Fin N → ℝ,
                  (∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1 - N) / (2 * N)) * ζ i) =
                    (∑ i, mid i * ζ i) - (∑ i, ζ i) / 2 := by
                intro ζ
                calc
                  _ = ∑ i : Fin N, (mid i * ζ i - (1 / 2) * ζ i) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    dsimp [mid]
                    field_simp
                    <;> ring
                  _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
              have hWnone : ∀ ζ : Fin N → ℝ,
                  (A_Watson N).mulVec ζ none = (∑ i, mid i * ζ i) - (∑ i, ζ i) / 2 := by
                intro ζ
                exact hWa ζ
              have hWsecond : ∀ ζ : Fin N → ℝ,
                  (A_Watson N).mulVec ζ (some none) = -((∑ i, mid i * ζ i) - (∑ i, ζ i) / 2) := by
                intro ζ
                rw [← hWa]
                change (∑ i : Fin N, ((N - (2 * ((i : ℕ) + 1 : ℝ) - 1)) / (2 * N)) * ζ i) = _
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro i _
                ring
              have hWrest : ∀ (ζ : Fin N → ℝ) (i : Fin N),
                  (A_Watson N).mulVec ζ (some (some i)) = ζ i - (1 / (N : ℝ)) * ∑ j, ζ j := by
                intro ζ i
                simp only [A_Watson, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
                rw [← Finset.mul_sum]
                simp
              have hWident : ∀ Q (ζ : Fin N → ℝ),
                  let y := (A_Watson N).mulVec ζ - b_Watson N Q
                  (y none + y (some none) = 1) ∧
                  (y none ^ 2 - ∑ o : Option (Fin N), y (some o) ^ 2 =
                    (N : ℝ) * (Q ^ 2 - (cvmZ ζ ^ 2 - ((1 / (N : ℝ)) * ∑ i, ζ i - 1 / 2) ^ 2))) := by
                intro Q ζ y
                let S : ℝ := ∑ i, ζ i
                let T : ℝ := ∑ i, ζ i ^ 2
                let H : ℝ := ∑ i, mid i * ζ i
                have hres : (∑ i : Fin N, (ζ i - (1 / (N : ℝ)) * S) ^ 2) = T - S ^ 2 / (N : ℝ) := by
                  calc
                    _ = ∑ i : Fin N, (ζ i ^ 2 - 2 * ((1 / (N : ℝ)) * S) * ζ i + ((1 / (N : ℝ)) * S) ^ 2) := by
                      apply Finset.sum_congr rfl; intro i _; ring
                    _ = T - 2 * ((1 / (N : ℝ)) * S) * S + (N : ℝ) * ((1 / (N : ℝ)) * S) ^ 2 := by
                      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
                        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, S, T]
                    _ = _ := by field_simp <;> ring
                have hcost : (∑ i : Fin N, (mid i - ζ i) ^ 2) = (∑ i : Fin N, mid i ^ 2) - 2 * H + T := by
                  calc
                    _ = ∑ i : Fin N, (mid i ^ 2 - 2 * (mid i * ζ i) + ζ i ^ 2) := by
                      apply Finset.sum_congr rfl; intro i _; ring
                    _ = _ := by
                      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, H, T]
                have hy0 : y none = H - S / 2 + 1 / 2 - (N : ℝ) / 24 + (N : ℝ) * Q ^ 2 / 2 := by
                  dsimp only [y, Pi.sub_apply]
                  rw [hWnone]
                  dsimp only [b_Watson]
                  dsimp [H, S]
                  ring
                have hy1 : y (some none) = -(H - S / 2) + 1 / 2 + (N : ℝ) / 24 - (N : ℝ) * Q ^ 2 / 2 := by
                  dsimp only [y, Pi.sub_apply]
                  rw [hWsecond]
                  dsimp only [b_Watson]
                  dsimp [H, S]
                  ring
                have hyi : ∀ i : Fin N, y (some (some i)) = ζ i - (1 / (N : ℝ)) * S := by
                  intro i
                  dsimp only [y, Pi.sub_apply]
                  rw [hWrest]
                  simp only [b_Watson, sub_zero, S]
                have hysum : (∑ o : Option (Fin N), y (some o) ^ 2) = y (some none) ^ 2 + T - S ^ 2 / (N : ℝ) := by
                  rw [Fintype.sum_option]
                  simp_rw [hyi]
                  rw [hres]
                  ring
                refine ⟨by rw [hy0, hy1]; ring, ?_⟩
                rw [hysum, hy0, hy1, hCvMsq, hcost, hmidsq]
                change _ = (N : ℝ) * (Q ^ 2 - (1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) *
                  ((N : ℝ) / 3 - 1 / (12 * (N : ℝ)) - 2 * H + T) - ((1 / (N : ℝ)) * S - 1 / 2) ^ 2))
                field_simp
                <;> ring
              have hWenc : ∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
                  watsonZ ζ ≤ Q ↔ (A_Watson N).mulVec ζ - b_Watson N Q ∈ K_Watson N := by
                intro Q hQ ζ
                let y := (A_Watson N).mulVec ζ - b_Watson N Q
                obtain ⟨hsum, hid⟩ := hWident Q ζ
                change y none + y (some none) = 1 at hsum
                change y none ^ 2 - (∑ o : Option (Fin N), y (some o) ^ 2) = _ at hid
                have htailpos : 0 ≤ ∑ i : Fin N, y (some (some i)) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
                change Real.sqrt (cvmZ ζ ^ 2 - ((1 / (N : ℝ)) * ∑ i, ζ i - 1 / 2) ^ 2) ≤ Q ↔
                  Real.sqrt (∑ o : Option (Fin N), y (some o) ^ 2) ≤ y none
                rw [Real.sqrt_le_left hQ, Real.sqrt_le_iff]
                constructor
                · intro hh
                  have hgap : 0 ≤ y none ^ 2 - ∑ o : Option (Fin N), y (some o) ^ 2 := by
                    rw [hid]; exact mul_nonneg hnreal.le (sub_nonneg.mpr hh)
                  refine ⟨?_, by linarith⟩
                  rw [Fintype.sum_option] at hgap
                  nlinarith only [hsum, hgap, htailpos]
                · rintro ⟨hyn, hh⟩
                  nlinarith only [hid, hnreal, hh]
              have hWstrict : ∀ Q (ζ : Fin N → ℝ), watsonZ ζ < Q →
                  (A_Watson N).mulVec ζ - b_Watson N Q ∈ interior (K_Watson N) := by
                intro Q ζ hζ
                have hQ : 0 < Q := (Real.sqrt_nonneg _).trans_lt hζ
                have hsq : cvmZ ζ ^ 2 - ((1 / (N : ℝ)) * ∑ i, ζ i - 1 / 2) ^ 2 < Q ^ 2 := (Real.sqrt_lt' hQ).mp hζ
                let y := (A_Watson N).mulVec ζ - b_Watson N Q
                obtain ⟨hsum, hid⟩ := hWident Q ζ
                change y none + y (some none) = 1 at hsum
                change y none ^ 2 - (∑ o : Option (Fin N), y (some o) ^ 2) = _ at hid
                have hgap : 0 < y none ^ 2 - ∑ o : Option (Fin N), y (some o) ^ 2 := by
                  rw [hid]; exact mul_pos hnreal (sub_pos.mpr hsq)
                have htailpos : 0 ≤ ∑ i : Fin N, y (some (some i)) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
                have hyn : 0 < y none := by
                  rw [Fintype.sum_option] at hgap
                  nlinarith only [hsum, hgap, htailpos]
                apply hSOCstrict
                exact (Real.sqrt_lt' hyn).mpr (by linarith)
              clear hmax hmin hinfsup hAmul hnonnegint hKpair hKuiperid hSOCnorm hCvMrad hCvMsq hCvmul
                hWnone hWsecond hWrest hWident hWa hmidsq hmid hsumn2
              let α : Fin N → ℝ := fun i => (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * (N : ℝ) ^ 2)
              have hα : ∀ i, 0 < α i := by
                intro i
                dsimp [α]
                apply div_pos
                · have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
                  linarith
                · positivity
              have hαsum : (∑ i, α i) = 1 / 2 := by
                have heq : ∀ i : Fin N, α i = (((i : ℕ) : ℝ) + 1 / 2) / (N : ℝ) ^ 2 := by
                  intro i
                  dsimp [α]
                  ring
                simp_rw [heq]
                rw [← Finset.sum_div, Finset.sum_add_distrib, hsumn]
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                field_simp
                <;> ring
              let weights : Fin N ⊕ Fin N → ℝ := Sum.elim α α
              have hweights : ∀ j, 0 < weights j := by intro j; cases j <;> apply hα
              have hweightsum : (∑ j, weights j) = 1 := by
                norm_num [weights, Fintype.sum_sum_type, hαsum]
              let GM : (Fin N ⊕ Fin N → ℝ) → ℝ := fun v => ∏ j, (v j) ^ (weights j)
              obtain ⟨hGMpos, hGMscale, hGMadd⟩ := hGM (Fin N ⊕ Fin N) weights hweights hweightsum
              change ∀ v, (∀ j, 0 ≤ v j) → 0 ≤ GM v at hGMpos
              change ∀ t : ℝ, 0 ≤ t → ∀ v, (∀ j, 0 ≤ v j) → GM (t • v) = t * GM v at hGMscale
              change ∀ v v', (∀ j, 0 ≤ v j) → (∀ j, 0 ≤ v' j) → GM v + GM v' ≤ GM (v + v') at hGMadd
              have hGMprod : ∀ v : Fin N ⊕ Fin N → ℝ, (∀ j, 0 ≤ v j) →
                  GM v = ∏ i : Fin N, (v (Sum.inl i) * v (Sum.inr i)) ^ α i := by
                intro v hv
                dsimp only [GM]
                rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
                apply Finset.prod_congr rfl
                intro i _
                exact (Real.mul_rpow (hv (Sum.inl i)) (hv (Sum.inr i))).symm
              have hADchar : ∀ y : Option (Fin N ⊕ Fin N) → ℝ,
                  y ∈ K_AD N ↔ (∀ j, 0 ≤ y (some j)) ∧ |y none| ≤ GM (fun j => y (some j)) := by
                intro y
                constructor
                · rintro ⟨hx, hy, hp⟩
                  have hxy : ∀ j, 0 ≤ y (some j) := by intro j; cases j with
                    | inl i => exact hx i
                    | inr i => exact hy i
                  refine ⟨hxy, ?_⟩
                  rw [hGMprod _ hxy]
                  exact hp
                · rintro ⟨hxy, hp⟩
                  refine ⟨fun i => hxy (Sum.inl i), fun i => hxy (Sum.inr i), ?_⟩
                  rw [hGMprod _ hxy] at hp
                  exact hp
              have hADconv : Convex ℝ (K_AD N) := by
                intro v hv w hw a b ha hb hab
                rw [hADchar] at hv hw ⊢
                refine ⟨fun j => add_nonneg (mul_nonneg ha (hv.1 j)) (mul_nonneg hb (hw.1 j)), ?_⟩
                change |a * v none + b * w none| ≤ GM (fun j => a * v (some j) + b * w (some j))
                calc
                  _ ≤ |a * v none| + |b * w none| := abs_add_le _ _
                  _ = a * |v none| + b * |w none| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
                  _ ≤ a * GM (fun j => v (some j)) + b * GM (fun j => w (some j)) :=
                    add_le_add (mul_le_mul_of_nonneg_left hv.2 ha) (mul_le_mul_of_nonneg_left hw.2 hb)
                  _ = GM (a • (fun j => v (some j))) + GM (b • (fun j => w (some j))) := by
                    rw [hGMscale a ha _ hv.1, hGMscale b hb _ hw.1]
                  _ ≤ _ := hGMadd _ _ (fun j => mul_nonneg ha (hv.1 j)) (fun j => mul_nonneg hb (hw.1 j))
              have hADzero : (0 : Option (Fin N ⊕ Fin N) → ℝ) ∈ K_AD N := by
                rw [hADchar]
                refine ⟨fun j => le_rfl, ?_⟩
                simpa using hGMpos (fun _ => 0) (fun _ => le_rfl)
              have hADscale : ∀ t : ℝ, 0 ≤ t → ∀ v ∈ K_AD N, t • v ∈ K_AD N := by
                intro t ht v hv
                rw [hADchar] at hv ⊢
                refine ⟨fun j => mul_nonneg ht (hv.1 j), ?_⟩
                change |t * v none| ≤ GM (t • fun j => v (some j))
                rw [abs_mul, abs_of_nonneg ht, hGMscale t ht _ hv.1]
                exact mul_le_mul_of_nonneg_left hv.2 ht
              have hADint : ∀ y : Option (Fin N ⊕ Fin N) → ℝ,
                  (∀ j, 0 < y (some j)) → |y none| < GM (fun j => y (some j)) → y ∈ interior (K_AD N) := by
                intro y hy hprod
                let O : Set (Option (Fin N ⊕ Fin N) → ℝ) :=
                  {v | (∀ j, 0 < v (some j)) ∧ |v none| < GM (fun j => v (some j))}
                have hcont : Continuous (fun v : Option (Fin N ⊕ Fin N) → ℝ => GM (fun j => v (some j))) := by
                  exact continuous_finset_prod _ (fun j _ => (continuous_apply (some j)).rpow_const (fun _ => Or.inr (hweights j).le))
                have hO : IsOpen O := by
                  change IsOpen ({v : Option (Fin N ⊕ Fin N) → ℝ | ∀ j, 0 < v (some j)} ∩
                    {v | |v none| < GM (fun j => v (some j))})
                  apply IsOpen.inter
                  · simp only [Set.setOf_forall]
                    exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (continuous_apply (some j)))
                  · exact isOpen_lt (continuous_abs.comp (continuous_apply none)) hcont
                exact mem_interior_iff_mem_nhds.mpr
                  (Filter.mem_of_superset (hO.mem_nhds ⟨hy, hprod⟩) (fun v hv =>
                    (hADchar v).mpr ⟨fun j => (hv.1 j).le, hv.2.le⟩))
              let adprod : (Fin N → ℝ) → ℝ := fun ζ => ∏ i, (ζ i * (1 - ζ (Fin.rev i))) ^ α i
              have hADmul : ∀ (ζ : Fin N → ℝ) (o : Option (Fin N ⊕ Fin N)),
                  (A_AD N).mulVec ζ o = match o with
                  | none => 0
                  | some (Sum.inl i) => ζ i
                  | some (Sum.inr i) => -ζ (Fin.rev i) := by
                intro ζ o
                rcases o with _ | (i | i) <;> simp [A_AD, Matrix.mulVec, dotProduct, ite_mul]
              have hADlog : ∀ ζ : Fin N → ℝ, (∀ i, 0 < ζ i ∧ ζ i < 1) →
                  0 < adprod ζ ∧ adSqZ ζ = -1 - 2 * Real.log (adprod ζ) := by
                intro ζ hζ
                have hp : ∀ i, 0 < ζ i * (1 - ζ (Fin.rev i)) :=
                  fun i => mul_pos (hζ i).1 (sub_pos.mpr (hζ (Fin.rev i)).2)
                have hprod : 0 < adprod ζ := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hp i) _)
                refine ⟨hprod, ?_⟩
                have hlog : Real.log (adprod ζ) = ∑ i : Fin N, α i *
                    (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i))) := by
                  rw [Real.log_prod (fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hp i) (α i)))]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Real.log_rpow (hp i), Real.log_mul (ne_of_gt (hζ i).1) (ne_of_gt (sub_pos.mpr (hζ (Fin.rev i)).2))]
                rw [hlog]
                dsimp only [adSqZ]
                have hsum : (∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (N : ℝ) ^ 2) *
                    (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i)))) =
                    2 * ∑ i : Fin N, α i * (Real.log (ζ i) + Real.log (1 - ζ (Fin.rev i))) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _
                  dsimp [α]
                  ring
                rw [hsum]
              have hADconeIff : ∀ Q (ζ : Fin N → ℝ),
                  (A_AD N).mulVec ζ - b_AD N Q ∈ K_AD N ↔
                    (∀ i, 0 < ζ i ∧ ζ i < 1) ∧ Real.exp (-(Q ^ 2 + 1) / 2) ≤ adprod ζ := by
                intro Q ζ
                constructor
                · intro hy
                  have hx : ∀ i, 0 ≤ ζ i := by
                    intro i
                    simpa only [Pi.sub_apply, hADmul, b_AD, sub_zero] using hy.1 i
                  have hx' : ∀ i, 0 ≤ 1 - ζ (Fin.rev i) := by
                    intro i
                    have hh := hy.2.1 i
                    simp only [Pi.sub_apply, hADmul, b_AD] at hh
                    linarith
                  have hp : Real.exp (-(Q ^ 2 + 1) / 2) ≤ adprod ζ := by
                    have hh := hy.2.2
                    simpa [Pi.sub_apply, hADmul, b_AD, adprod, α, abs_of_pos (Real.exp_pos _), sub_neg_eq_add, sub_eq_add_neg, add_comm] using hh
                  have hp' : ∀ i, 0 < ζ i * (1 - ζ (Fin.rev i)) := by
                    intro i
                    by_contra hn
                    have heq : ζ i * (1 - ζ (Fin.rev i)) = 0 :=
                      le_antisymm (le_of_not_gt hn) (mul_nonneg (hx i) (hx' i))
                    have hz : adprod ζ = 0 := by
                      apply Finset.prod_eq_zero (Finset.mem_univ i)
                      rw [heq, Real.zero_rpow (ne_of_gt (hα i))]
                    rw [hz] at hp
                    exact (Real.exp_pos _).not_ge hp
                  refine ⟨?_, hp⟩
                  intro i
                  constructor
                  · exact pos_of_mul_pos_left (hp' i) (hx' i)
                  · have hh := hp' (Fin.rev i)
                    rw [Fin.rev_involutive i] at hh
                    exact sub_pos.mp (pos_of_mul_pos_right hh (hx (Fin.rev i)))
                · rintro ⟨hζ, hp⟩
                  refine ⟨?_, ?_, ?_⟩
                  · intro i
                    simpa only [Pi.sub_apply, hADmul, b_AD, sub_zero] using (hζ i).1.le
                  · intro i
                    have hh := (hζ (Fin.rev i)).2.le
                    simp only [Pi.sub_apply, hADmul, b_AD]
                    linarith
                  · simpa [Pi.sub_apply, hADmul, b_AD, adprod, α, abs_of_pos (Real.exp_pos _), sub_neg_eq_add, sub_eq_add_neg, add_comm] using hp
              have hADenc : ∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
                  adZ ζ ≤ ENNReal.ofReal Q ↔ (A_AD N).mulVec ζ - b_AD N Q ∈ K_AD N := by
                intro Q hQ ζ
                by_cases hζ : ∀ i, 0 < ζ i ∧ ζ i < 1
                · rw [adZ, if_pos hζ, ENNReal.ofReal_le_ofReal_iff hQ, Real.sqrt_le_left hQ, hADconeIff]
                  simp only [hζ, forall_const, true_and]
                  obtain ⟨hp, hid⟩ := hADlog ζ hζ
                  have heq : (Real.exp (-(Q ^ 2 + 1) / 2) ≤ adprod ζ) ↔
                      (-(Q ^ 2 + 1) / 2 ≤ Real.log (adprod ζ)) := by
                    conv_lhs => rhs; rw [← Real.exp_log hp]
                    exact Real.exp_le_exp
                  rw [heq, hid]
                  constructor <;> intro hh <;> linarith only [hh]
                · rw [hADconeIff]
                  simp [adZ, hζ]
              have hADstrict : ∀ Q (ζ : Fin N → ℝ), adZ ζ < ENNReal.ofReal Q →
                  (A_AD N).mulVec ζ - b_AD N Q ∈ interior (K_AD N) := by
                set_option maxHeartbeats 1000000 in
                  intro Q ζ hstat
                  have hζ : ∀ i, 0 < ζ i ∧ ζ i < 1 := by
                    by_contra hn
                    simp [adZ, hn] at hstat
                  rw [adZ, if_pos hζ] at hstat
                  have hroot : Real.sqrt (adSqZ ζ) < Q :=
                    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).mp hstat
                  have hQ : 0 < Q := (Real.sqrt_nonneg _).trans_lt hroot
                  have hsq := (Real.sqrt_lt' hQ).mp hroot
                  obtain ⟨hp, hid⟩ := hADlog ζ hζ
                  have hprod : Real.exp (-(Q ^ 2 + 1) / 2) < adprod ζ := by
                    calc
                      _ < Real.exp (Real.log (adprod ζ)) := Real.exp_lt_exp.mpr (by rw [hid] at hsq; linarith only [hsq])
                      _ = _ := Real.exp_log hp
                  let y := (A_AD N).mulVec ζ - b_AD N Q
                  have hcoords : ∀ j : Fin N ⊕ Fin N, 0 < y (some j) := by
                    intro j
                    rcases j with i | i
                    · simpa only [y, Pi.sub_apply, hADmul, b_AD, sub_zero] using (hζ i).1
                    · have hh := (hζ (Fin.rev i)).2
                      change 0 < (A_AD N).mulVec ζ (some (Sum.inr i)) - b_AD N Q (some (Sum.inr i))
                      rw [hADmul, b_AD]
                      linarith
                  apply hADint _ hcoords
                  rw [hGMprod _ (fun j => (hcoords j).le)]
                  simpa [y, Pi.sub_apply, hADmul, b_AD, adprod, α, abs_of_pos (Real.exp_pos _), sub_neg_eq_add, sub_eq_add_neg, add_comm] using hprod
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · intro Q QM hfin hstrict
                obtain ⟨G, hGs, hGstat, hGm, hdev⟩ := hstrict
                apply hconic (Fin N ⊕ Fin N) (A_KS N) (b_KS N Q) (K_KS N) hKSconv hKSzero hKSscale QM
                · intro H
                  change ((SupportedOn Ξ H ∧ ksZ (u H s) ≤ Q) ∧ H ∈ momentRegion φ QM s) ↔
                    SupportedOn Ξ H ∧ H ∈ momentRegion φ QM s ∧ (A_KS N).mulVec (u H s) - b_KS N Q ∈ K_KS N
                  rw [← hKSenc]
                  tauto
                · exact ⟨G, hGs, hGm, hdev, hKSstrict Q (u G s) hGstat⟩
              · intro Q QM hfin hstrict
                obtain ⟨G, hGs, hGstat, hGm, hdev⟩ := hstrict
                apply hconic (Fin N ⊕ Fin N) (A_KS N) (b_Kuiper N Q) (K_Kuiper N)
                  hKuiperconv hKuiperzero hKuiperscale QM
                · intro H
                  change ((SupportedOn Ξ H ∧ kuiperZ (u H s) ≤ Q) ∧ H ∈ momentRegion φ QM s) ↔
                    SupportedOn Ξ H ∧ H ∈ momentRegion φ QM s ∧ (A_KS N).mulVec (u H s) - b_Kuiper N Q ∈ K_Kuiper N
                  rw [← hKuiperenc]
                  tauto
                · exact ⟨G, hGs, hGm, hdev, hKuiperstrict Q (u G s) hGstat⟩
              · intro Q QM hfin hstrict
                obtain ⟨G, hGs, hGstat, hGm, hdev⟩ := hstrict
                have hQ : 0 < Q := (Real.sqrt_nonneg _).trans_lt hGstat
                have hminQ : 1 / (12 * (N : ℝ) ^ 2) ≤ Q ^ 2 := by
                  have hh := (Real.sqrt_lt' hQ).mp hGstat
                  have hn : 0 ≤ (1 / (N : ℝ)) * ∑ i, (mid i - u G s i) ^ 2 := by positivity
                  change 1 / (12 * (N : ℝ) ^ 2) + (1 / (N : ℝ)) * ∑ i, (mid i - u G s i) ^ 2 < Q ^ 2 at hh
                  linarith
                apply hconic (Option (Fin N)) (A_CvM N) (b_CvM N Q) (K_CvM N)
                  (hSOCconv (Fin N)) (hSOCzero (Fin N)) (hSOCscale (Fin N)) QM
                · intro H
                  change ((SupportedOn Ξ H ∧ cvmZ (u H s) ≤ Q) ∧ H ∈ momentRegion φ QM s) ↔
                    SupportedOn Ξ H ∧ H ∈ momentRegion φ QM s ∧ (A_CvM N).mulVec (u H s) - b_CvM N Q ∈ K_CvM N
                  rw [← hCVMenc Q hQ.le hminQ]
                  tauto
                · exact ⟨G, hGs, hGm, hdev, hCVMstrict Q (u G s) hGstat⟩
              · intro Q QM hfin hstrict
                obtain ⟨G, hGs, hGstat, hGm, hdev⟩ := hstrict
                have hQ : 0 < Q := (Real.sqrt_nonneg _).trans_lt hGstat
                apply hconic (Option (Option (Fin N))) (A_Watson N) (b_Watson N Q) (K_Watson N)
                  (hSOCconv (Option (Fin N))) (hSOCzero (Option (Fin N))) (hSOCscale (Option (Fin N))) QM
                · intro H
                  change ((SupportedOn Ξ H ∧ watsonZ (u H s) ≤ Q) ∧ H ∈ momentRegion φ QM s) ↔
                    SupportedOn Ξ H ∧ H ∈ momentRegion φ QM s ∧ (A_Watson N).mulVec (u H s) - b_Watson N Q ∈ K_Watson N
                  rw [← hWenc Q hQ.le]
                  tauto
                · exact ⟨G, hGs, hGm, hdev, hWstrict Q (u G s) hGstat⟩
              · intro Q QM hfin hstrict
                obtain ⟨G, hGs, hGstat, hGm, hdev⟩ := hstrict
                have hQ : 0 < Q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (show (0 : ENNReal) ≤ adStat G s from bot_le) hGstat)
                apply hconic (Option (Fin N ⊕ Fin N)) (A_AD N) (b_AD N Q) (K_AD N)
                  hADconv hADzero hADscale QM
                · intro H
                  change ((SupportedOn Ξ H ∧ adZ (u H s) ≤ ENNReal.ofReal Q) ∧ H ∈ momentRegion φ QM s) ↔
                    SupportedOn Ξ H ∧ H ∈ momentRegion φ QM s ∧ (A_AD N).mulVec (u H s) - b_AD N Q ∈ K_AD N
                  rw [← hADenc Q hQ.le]
                  tauto
                · exact ⟨G, hGs, hGm, hdev, hADstrict Q (u G s) hGstat⟩
