-- Prove2me | solution 1 for ScenarioReduction.Redistribution.Supplement.quantitative_stability
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:10.932718+00:00
-- url     : https://prove2.me/submissions/620c4676-67cd-41d1-83d2-480c7f92ecba

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_standing
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_epsilonSolutions
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_admissible
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_informationDistance
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_conditioningModulus
set_option autoImplicit false
open scoped ENNReal

open ScenarioReduction
open ScenarioReduction.Redistribution
open ScenarioReduction.Redistribution.Supplement

/-- Theorem 1, p. 496: both regimes, with the SAME constants. No additional
closeness condition is imposed in the epsilon-solution regime. -/
theorem solution {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (hM : standing M) (P : MeasureTheory.Measure M.Ξ) (hP : admissible M P)
    (hS : (M.S P).Nonempty) (hSb : Bornology.IsBounded (M.S P)) :
    ∃ ρ εbar : ℝ, 0 < ρ ∧ 0 < εbar ∧
      (∀ Q : MeasureTheory.Measure M.Ξ, admissible M Q →
        informationDistance M ρ P Q < ENNReal.ofReal εbar →
        (M.v P ≠ ⊤ ∧ M.v P ≠ ⊥ ∧ M.v Q ≠ ⊤ ∧ M.v Q ≠ ⊥ ∧
          EReal.abs (M.v P - M.v Q) ≤ informationDistance M ρ P Q) ∧
        (M.S Q).Nonempty ∧
        ∀ x ∈ M.S Q, ∃ y ∈ M.S P,
          edist x y ≤ conditioningModulus M P (informationDistance M ρ P Q)) ∧
      (∀ ε : ℝ, 0 < ε → ε < εbar →
        ∀ Q : MeasureTheory.Measure M.Ξ, admissible M Q →
          informationDistance M (ρ + ε) P Q < ENNReal.ofReal ε →
          (epsilonSolutions M P ε).Nonempty ∧ (epsilonSolutions M Q ε).Nonempty ∧
          Metric.hausdorffEDist (epsilonSolutions M P ε) (epsilonSolutions M Q ε) ≤
            ENNReal.ofReal (2 * ρ / ε) * informationDistance M (ρ + ε) P Q) := by
              classical
              set φ : MeasureTheory.Measure M.Ξ → EuclideanSpace ℝ (Fin n) → ℝ :=
                fun ν x => (M.integral ν 0 x).toReal with hφdef
              have hMM : ∀ ν, M.M ν = M.X := by
                intro ν; ext x; simp [ProbMetricStab.General.Model.M]
              have hdecomp : ∀ a : EReal, a.toReal = a.toENNReal.toReal - (-a).toENNReal.toReal := by
                intro a
                induction a using EReal.rec
                · simp
                · rename_i a
                  rw [← EReal.coe_neg]
                  simp only [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe,
                    ENNReal.toReal_ofReal']
                  rcases le_total a 0 with h | h
                  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
                  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
                · simp
              have hmeas : ∀ x, Measurable (fun ω : M.Ξ => M.f 0 ω x) := hM.2.2.2.2.1
              have hmp : ∀ x, Measurable (fun ω : M.Ξ => (M.f 0 ω x).toENNReal) := fun x =>
                EReal.continuous_toENNReal.measurable.comp (hmeas x)
              have hmn : ∀ x, Measurable (fun ω : M.Ξ => (-M.f 0 ω x).toENNReal) := fun x =>
                EReal.continuous_toENNReal.measurable.comp (continuous_neg.measurable.comp (hmeas x))
              have hmr : ∀ x, Measurable (fun ω : M.Ξ => (M.f 0 ω x).toReal) := by
                intro x
                have : (fun ω : M.Ξ => (M.f 0 ω x).toReal) =
                    fun ω => (M.f 0 ω x).toENNReal.toReal - (-M.f 0 ω x).toENNReal.toReal :=
                  funext fun ω => hdecomp _
                rw [this]; exact (hmp x).ennreal_toReal.sub (hmn x).ennreal_toReal
              have hfin : ∀ ν, admissible M ν → ∀ x ∈ M.X,
                  (∫⁻ ω, (M.f 0 ω x).toENNReal ∂ν) ≠ ∞ ∧ (∫⁻ ω, (-M.f 0 ω x).toENNReal ∂ν) ≠ ∞ := by
                intro ν hν x hx
                obtain ⟨hlow, hup⟩ := hν.2 (‖x‖ + 1) (by positivity)
                have hxS : x ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ ‖x‖ + 1} := ⟨hx, by linarith⟩
                have h1 : M.integral ν 0 x < ⊤ := lt_of_le_of_lt (le_iSup₂ (f := fun y (_ : y ∈
                  {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ ‖x‖ + 1}) => M.integral ν 0 y) x hxS) hup
                have hpos : (∫⁻ ω, (M.f 0 ω x).toENNReal ∂ν) ≠ ∞ := by
                  intro h
                  unfold ProbMetricStab.General.Model.integral DupacovaWets.Consistency.expect at h1
                  rw [if_pos h] at h1; exact lt_irrefl _ h1
                have hle : ∀ ω, (⨅ y ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ ‖x‖ + 1}, M.f 0 ω y)
                    ≤ M.f 0 ω x := fun ω => iInf₂_le x hxS
                have hhpos : (∫⁻ ω, (⨅ y ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ ‖x‖ + 1},
                    M.f 0 ω y).toENNReal ∂ν) ≠ ∞ :=
                  ne_top_of_le_ne_top hpos (MeasureTheory.lintegral_mono fun ω =>
                    EReal.toENNReal_le_toENNReal (hle ω))
                have hhneg : (∫⁻ ω, (-⨅ y ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ ‖x‖ + 1},
                    M.f 0 ω y).toENNReal ∂ν) ≠ ∞ := by
                  intro hinf
                  unfold DupacovaWets.Consistency.expect at hlow
                  rw [if_neg hhpos, hinf] at hlow
                  simp at hlow
                refine ⟨hpos, ne_top_of_le_ne_top hhneg (MeasureTheory.lintegral_mono fun ω =>
                  EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hle ω)))⟩
              have hrep : ∀ ν, admissible M ν → ∀ x ∈ M.X, M.integral ν 0 x =
                  (((∫⁻ ω, (M.f 0 ω x).toENNReal ∂ν).toReal - (∫⁻ ω, (-M.f 0 ω x).toENNReal ∂ν).toReal : ℝ)
                    : EReal) := by
                intro ν hν x hx
                obtain ⟨h1, h2⟩ := hfin ν hν x hx
                unfold ProbMetricStab.General.Model.integral DupacovaWets.Consistency.expect
                rw [if_neg h1, EReal.coe_sub, EReal.coe_ennreal_toReal h1, EReal.coe_ennreal_toReal h2]
              have M1 : ∀ ν, admissible M ν → ∀ x ∈ M.X, M.integral ν 0 x = ((φ ν x : ℝ) : EReal) := by
                intro ν hν x hx
                simp only [hφdef]
                rw [hrep ν hν x hx, EReal.toReal_coe]
              have hint : ∀ ν, admissible M ν → ∀ x ∈ M.X,
                  MeasureTheory.Integrable (fun ω => (M.f 0 ω x).toReal) ν ∧
                  φ ν x = ∫ ω, (M.f 0 ω x).toReal ∂ν ∧
                  ∀ᵐ ω ∂ν, M.f 0 ω x ≠ ⊤ ∧ M.f 0 ω x ≠ ⊥ := by
                intro ν hν x hx
                obtain ⟨h1, h2⟩ := hfin ν hν x hx
                have i1 := MeasureTheory.integrable_toReal_of_lintegral_ne_top (hmp x).aemeasurable h1
                have i2 := MeasureTheory.integrable_toReal_of_lintegral_ne_top (hmn x).aemeasurable h2
                have a1 := MeasureTheory.ae_lt_top (hmp x) h1
                have a2 := MeasureTheory.ae_lt_top (hmn x) h2
                have heq : (fun ω => (M.f 0 ω x).toReal) =
                    fun ω => (M.f 0 ω x).toENNReal.toReal - (-M.f 0 ω x).toENNReal.toReal :=
                  funext fun ω => hdecomp _
                refine ⟨by rw [heq]; exact i1.sub i2, ?_, ?_⟩
                · simp only [hφdef]
                  rw [hrep ν hν x hx, EReal.toReal_coe, heq, MeasureTheory.integral_sub i1 i2,
                    MeasureTheory.integral_toReal (hmp x).aemeasurable a1,
                    MeasureTheory.integral_toReal (hmn x).aemeasurable a2]
                · filter_upwards [a1, a2] with ω e1 e2
                  refine ⟨fun h => by simp [h] at e1, fun h => by simp [h] at e2⟩
              have M2 : ∀ ν, admissible M ν → ∀ x ∈ M.X, ∀ y ∈ M.X, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
                  φ ν (a • x + b • y) ≤ a * φ ν x + b * φ ν y := by
                intro ν hν x hx y hy a b ha hb hab
                have hz : a • x + b • y ∈ M.X := hM.2.2.1 hx hy ha hb hab
                obtain ⟨ix, ex, ax⟩ := hint ν hν x hx
                obtain ⟨iy, ey, ay⟩ := hint ν hν y hy
                obtain ⟨iz, ez, az⟩ := hint ν hν _ hz
                rw [ex, ey, ez, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
                  ← MeasureTheory.integral_add (ix.const_mul a) (iy.const_mul b)]
                refine MeasureTheory.integral_mono_ae iz ((ix.const_mul a).add (iy.const_mul b)) ?_
                filter_upwards [ax, ay, az] with ω hx1 hy1 hz1
                have hcv := hM.2.2.2.2.2.2 ω
                have mx : (x, (M.f 0 ω x).toReal) ∈
                    {p : EuclideanSpace ℝ (Fin n) × ℝ | M.f 0 ω p.1 ≤ (p.2 : EReal)} := by
                  simp only [Set.mem_setOf_eq]; rw [EReal.coe_toReal hx1.1 hx1.2]
                have my : (y, (M.f 0 ω y).toReal) ∈
                    {p : EuclideanSpace ℝ (Fin n) × ℝ | M.f 0 ω p.1 ≤ (p.2 : EReal)} := by
                  simp only [Set.mem_setOf_eq]; rw [EReal.coe_toReal hy1.1 hy1.2]
                have mz := hcv mx my ha hb hab
                simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
                  smul_eq_mul] at mz
                have mz' : M.f 0 ω (a • x + b • y) ≤
                    ((a * (M.f 0 ω x).toReal + b * (M.f 0 ω y).toReal : ℝ) : EReal) := by exact_mod_cast mz
                exact (EReal.toReal_le_toReal mz' hz1.2 (EReal.coe_ne_top _)).trans_eq (EReal.toReal_coe _)
              have M3 : ∀ ν, admissible M ν → ∀ (u : ℕ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
                  (A : ℝ), (∀ k, u k ∈ M.X) → Filter.Tendsto u Filter.atTop (nhds x) →
                  (∀ k, φ ν (u k) ≤ A) → φ ν x ≤ A := by
                intro ν hν u x A hu hux hA
                have hxX : x ∈ M.X := hM.2.1.mem_of_tendsto hux (Filter.Eventually.of_forall hu)
                obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto u hux)
                set R' := max R ‖x‖ + 1 with hR'
                have hR'0 : 0 < R' := by have := le_max_right R ‖x‖; have := norm_nonneg x; linarith
                have huR : ∀ k, u k ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ R'} := fun k =>
                  ⟨hu k, (hR _ ⟨k, rfl⟩).trans (by have := le_max_left R ‖x‖; linarith)⟩
                obtain ⟨hlow, hup⟩ := hν.2 R' hR'0
                have h1 : M.integral ν 0 (u 0) < ⊤ := lt_of_le_of_lt (le_iSup₂ (f := fun y (_ : y ∈
                  {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ R'}) => M.integral ν 0 y) (u 0) (huR 0)) hup
                have hpos0 := (hfin ν hν (u 0) (hu 0)).1
                have hhpos : (∫⁻ ω, (⨅ y ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ R'},
                    M.f 0 ω y).toENNReal ∂ν) ≠ ∞ :=
                  ne_top_of_le_ne_top hpos0 (MeasureTheory.lintegral_mono fun ω =>
                    EReal.toENNReal_le_toENNReal (iInf₂_le (u 0) (huR 0)))
                have hhneg : (∫⁻ ω, (-⨅ y ∈ {y : EuclideanSpace ℝ (Fin n) | y ∈ M.X ∧ ‖y‖ ≤ R'},
                    M.f 0 ω y).toENNReal ∂ν) ≠ ∞ := by
                  intro hinf
                  unfold DupacovaWets.Consistency.expect at hlow
                  rw [if_neg hhpos, hinf] at hlow
                  simp at hlow
                set G : M.Ξ → ℝ≥0∞ := fun ω => ⨆ k, (-M.f 0 ω (u k)).toENNReal with hG
                have hGm : Measurable G := Measurable.iSup fun k => hmn (u k)
                have hGfin : (∫⁻ ω, G ω ∂ν) ≠ ∞ :=
                  ne_top_of_le_ne_top hhneg (MeasureTheory.lintegral_mono fun ω => iSup_le fun k =>
                    EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (iInf₂_le (u k) (huR k))))
                have hGae := MeasureTheory.ae_lt_top hGm hGfin
                have iG := MeasureTheory.integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfin
                set C := ∫ ω, (G ω).toReal ∂ν with hC
                have hkb : ∀ k ω, G ω < ⊤ → 0 ≤ (M.f 0 ω (u k)).toReal + (G ω).toReal := by
                  intro k ω hω
                  rw [hdecomp (M.f 0 ω (u k))]
                  have : (-M.f 0 ω (u k)).toENNReal ≤ G ω := le_iSup (fun k => (-M.f 0 ω (u k)).toENNReal) k
                  have := ENNReal.toReal_mono hω.ne this
                  have := ENNReal.toReal_nonneg (a := (M.f 0 ω (u k)).toENNReal)
                  linarith
                have hFk : ∀ k, (∫⁻ ω, ENNReal.ofReal ((M.f 0 ω (u k)).toReal + (G ω).toReal) ∂ν) =
                    ENNReal.ofReal (φ ν (u k) + C) := by
                  intro k
                  obtain ⟨ik, ek, _⟩ := hint ν hν (u k) (hu k)
                  rw [ek, ← MeasureTheory.integral_add ik iG]
                  refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (ik.add iG) ?_).symm
                  filter_upwards [hGae] with ω hω using hkb k ω hω
                obtain ⟨ix, ex, ax⟩ := hint ν hν x hxX
                have aall : ∀ᵐ ω ∂ν, ∀ k, M.f 0 ω (u k) ≠ ⊤ :=
                  MeasureTheory.ae_all_iff.mpr fun k => (hint ν hν (u k) (hu k)).2.2.mono fun ω h => h.1
                have hpt : ∀ᵐ ω ∂ν, ENNReal.ofReal ((M.f 0 ω x).toReal + (G ω).toReal) ≤
                    Filter.liminf (fun k => ENNReal.ofReal ((M.f 0 ω (u k)).toReal + (G ω).toReal))
                      Filter.atTop := by
                  filter_upwards [ax, aall, hGae] with ω hx1 hk1 hG1
                  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
                  have hbt : b ≠ ⊤ := ne_top_of_lt hb
                  have hb' : b.toReal < (M.f 0 ω x).toReal + (G ω).toReal := by
                    have := (ENNReal.toReal_lt_toReal hbt ENNReal.ofReal_ne_top).mpr hb
                    rw [ENNReal.toReal_ofReal'] at this
                    rcases le_total 0 ((M.f 0 ω x).toReal + (G ω).toReal) with h0 | h0
                    · rwa [max_eq_left h0] at this
                    · rw [max_eq_right h0] at this; linarith [ENNReal.toReal_nonneg (a := b)]
                  have hy : ((b.toReal - (G ω).toReal : ℝ) : EReal) < M.f 0 ω x := by
                    rw [← EReal.coe_toReal hx1.1 hx1.2]; exact_mod_cast (by linarith)
                  have hev : ∀ᶠ k in Filter.atTop, ((b.toReal - (G ω).toReal : ℝ) : EReal) < M.f 0 ω (u k) :=
                    hux.eventually ((hM.2.2.2.2.2.1 ω) x _ hy)
                  refine Filter.le_liminf_of_le (f := Filter.atTop)
                    (u := fun k => ENNReal.ofReal ((M.f 0 ω (u k)).toReal + (G ω).toReal)) (by isBoundedDefault) ?_
                  filter_upwards [hev] with k hk
                  have hkt := hk1 k
                  have hne : M.f 0 ω (u k) ≠ ⊥ := ne_bot_of_gt hk
                  have : b.toReal - (G ω).toReal < (M.f 0 ω (u k)).toReal := by
                    rw [← EReal.coe_toReal hkt hne] at hk; exact_mod_cast hk
                  rw [← ENNReal.ofReal_toReal hbt]
                  exact ENNReal.ofReal_le_ofReal (by linarith)
                have hfatou := MeasureTheory.lintegral_liminf_le (μ := ν) (u := Filter.atTop)
                  (f := fun k ω => ENNReal.ofReal ((M.f 0 ω (u k)).toReal + (G ω).toReal))
                  (fun k => ENNReal.measurable_ofReal.comp
                    ((hmr (u k)).add hGm.ennreal_toReal))
                have hlhs : ENNReal.ofReal (φ ν x + C) ≤
                    (∫⁻ ω, ENNReal.ofReal ((M.f 0 ω x).toReal + (G ω).toReal) ∂ν) := by
                  rw [ex, hC, ← MeasureTheory.integral_add ix iG]
                  have ih := ix.add iG
                  calc ENNReal.ofReal (∫ ω, ((M.f 0 ω x).toReal + (G ω).toReal) ∂ν)
                      ≤ ENNReal.ofReal (∫ ω, max ((M.f 0 ω x).toReal + (G ω).toReal) 0 ∂ν) :=
                        ENNReal.ofReal_le_ofReal (MeasureTheory.integral_mono ih ih.pos_part
                          (fun ω => le_max_left _ _))
                    _ = ∫⁻ ω, ENNReal.ofReal (max ((M.f 0 ω x).toReal + (G ω).toReal) 0) ∂ν :=
                        MeasureTheory.ofReal_integral_eq_lintegral_ofReal ih.pos_part
                          (Filter.Eventually.of_forall fun ω => le_max_right _ _)
                    _ = _ := by
                      congr 1; funext ω
                      rcases le_total 0 ((M.f 0 ω x).toReal + (G ω).toReal) with h | h
                      · simp [max_eq_left h]
                      · simp [max_eq_right h, ENNReal.ofReal_of_nonpos h]
                have hchain : ENNReal.ofReal (φ ν x + C) ≤ ENNReal.ofReal (A + C) := by
                  refine hlhs.trans ((MeasureTheory.lintegral_mono_ae hpt).trans (hfatou.trans ?_))
                  simp only [hFk]
                  refine (Filter.liminf_le_liminf (Filter.Eventually.of_forall fun k =>
                    ENNReal.ofReal_le_ofReal (by linarith [hA k] : φ ν (u k) + C ≤ A + C))).trans ?_
                  rw [Filter.liminf_const]
                have hAC : 0 ≤ A + C := by
                  have h0 : 0 ≤ φ ν (u 0) + C := by
                    obtain ⟨ik, ek, _⟩ := hint ν hν (u 0) (hu 0)
                    rw [ek, hC, ← MeasureTheory.integral_add ik iG]
                    exact MeasureTheory.integral_nonneg_of_ae (by
                      filter_upwards [hGae] with ω hω using hkb 0 ω hω)
                  linarith [hA 0]
                have := (ENNReal.ofReal_le_ofReal_iff hAC).mp hchain
                linarith
              have hXc : IsClosed M.X := hM.2.1
              have hXcv : Convex ℝ M.X := hM.2.2.1
              have M3' : ∀ ν, admissible M ν → ∀ (u : ℕ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
                  (A : ℝ), (∀ k, u k ∈ M.X) → Filter.Tendsto u Filter.atTop (nhds x) →
                  (∀ δ > 0, ∃ N, ∀ k ≥ N, φ ν (u k) ≤ A + δ) → φ ν x ≤ A := by
                intro ν hν u x A hu hux hA
                refine le_of_forall_pos_le_add fun δ hδ => ?_
                obtain ⟨N, hN⟩ := hA δ hδ
                exact M3 ν hν (fun k => u (k + N)) x (A + δ) (fun k => hu _)
                  ((Filter.tendsto_add_atTop_iff_nat N).mpr hux) (fun k => hN _ (by omega))
              have D1 : ∀ ν, admissible M ν → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ M.X →
                  K.Nonempty → BddBelow (φ ν '' K) → ∃ xb ∈ K, ∀ z ∈ K, φ ν xb ≤ φ ν z := by
                intro ν hν K hK hKX hKn hbdd
                set m := sInf (φ ν '' K) with hm
                have hne : (φ ν '' K).Nonempty := hKn.image _
                have hseq : ∀ k : ℕ, ∃ z ∈ K, φ ν z < m + 1 / ((k:ℝ) + 1) := by
                  intro k
                  have : m < m + 1 / ((k:ℝ)+1) := by
                    have : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
                    linarith
                  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne this
                  exact ⟨z, hz, hlt⟩
                choose u huK hu using hseq
                obtain ⟨xb, hxb, ψ, hψ, hlim⟩ := hK.tendsto_subseq huK
                refine ⟨xb, hxb, fun z hz => ?_⟩
                have hle : φ ν xb ≤ m := by
                  refine M3' ν hν (u ∘ ψ) xb m (fun k => hKX (huK _)) hlim ?_
                  intro δ hδ
                  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
                  refine ⟨N, fun k hk => ?_⟩
                  have h1 := hu (ψ k)
                  have hk' : (N:ℝ) ≤ (ψ k : ℝ) := by exact_mod_cast (hk.trans (hψ.id_le k))
                  have : 1 / ((ψ k : ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := by
                    apply one_div_le_one_div_of_le (by positivity); linarith
                  simp only [Function.comp]; linarith
                exact hle.trans (csInf_le hbdd ⟨z, hz, rfl⟩)
              obtain ⟨x0, hx0⟩ := hS
              have hx0X : x0 ∈ M.X := by have := hx0.1; rwa [hMM] at this
              set vP := φ P x0 with hvP
              have hvPe : M.v P = (vP : EReal) := by rw [← hx0.2, M1 P hP x0 hx0X]
              have hvle : ∀ ν, ∀ z ∈ M.X, M.v ν ≤ M.integral ν 0 z := by
                intro ν z hz
                unfold ProbMetricStab.General.Model.v
                exact iInf₂_le z (by rw [hMM]; exact hz)
              have hPmin : ∀ z ∈ M.X, vP ≤ φ P z := by
                intro z hz
                have := hvle P z hz
                rw [hvPe, M1 P hP z hz] at this
                exact_mod_cast this
              have hSmem : ∀ ν, ∀ z ∈ M.X, M.integral ν 0 z ≤ M.v ν → z ∈ M.S ν := by
                intro ν z hz h
                exact ⟨by rw [hMM]; exact hz, le_antisymm h (hvle ν z hz)⟩
              obtain ⟨R0, hR0⟩ := hSb.subset_closedBall x0
              set r := max R0 0 + 1 with hr
              have hr0 : 0 < r := by have := le_max_right R0 0; linarith
              have hSin : ∀ z ∈ M.S P, dist z x0 < r := by
                intro z hz
                have := hR0 hz
                rw [Metric.mem_closedBall] at this
                have := le_max_left R0 0
                linarith
              have G : ∀ ν, admissible M ν → ∀ g : ℝ, 0 < g →
                  (∀ w ∈ M.X, dist w x0 = r → φ ν x0 + g ≤ φ ν w) →
                  ∀ z ∈ M.X, r ≤ dist z x0 → φ ν x0 + g ≤ φ ν z := by
                intro ν hν g hg hw z hz hrz
                have hd : 0 < dist z x0 := lt_of_lt_of_le hr0 hrz
                set t := r / dist z x0 with ht
                have ht0 : 0 < t := div_pos hr0 hd
                have ht1 : t ≤ 1 := (div_le_one hd).mpr hrz
                set w := (1 - t) • x0 + t • z with hw_def
                have hwX : w ∈ M.X := hXcv hx0X hz (by linarith) ht0.le (by ring)
                have hwd : dist w x0 = r := by
                  have : w - x0 = t • (z - x0) := by rw [hw_def]; module
                  rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm, ht,
                    div_mul_cancel₀ _ hd.ne']
                have h1 := hw w hwX hwd
                have h2 := M2 ν hν x0 hx0X z hz (1 - t) t (by linarith) ht0.le (by ring)
                have h3 : g ≤ t * (φ ν z - φ ν x0) := by nlinarith
                have hpos : 0 < φ ν z - φ ν x0 := by
                  by_contra h; push_neg at h; nlinarith
                nlinarith [mul_le_mul_of_nonneg_right ht1 hpos.le]
              have hgap : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ M.X, dist w x0 = r → vP + c ≤ φ P w := by
                by_cases hK : (M.X ∩ Metric.sphere x0 r).Nonempty
                · have hKc : IsCompact (M.X ∩ Metric.sphere x0 r) := (isCompact_sphere x0 r).inter_left hXc
                  obtain ⟨xb, hxb, hmin⟩ := D1 P hP _ hKc Set.inter_subset_left hK
                    ⟨vP, by rintro _ ⟨z, hz, rfl⟩; exact hPmin z hz.1⟩
                  have hxbgt : vP < φ P xb := by
                    by_contra h; push_neg at h
                    have hxS : xb ∈ M.S P :=
                      hSmem P xb hxb.1 (by rw [M1 P hP xb hxb.1, hvPe]; exact_mod_cast h)
                    have := hSin xb hxS
                    have h2 := hxb.2; rw [Metric.mem_sphere] at h2; linarith
                  refine ⟨φ P xb - vP, by linarith, fun w hw hwd => ?_⟩
                  have := hmin w ⟨hw, by rw [Metric.mem_sphere]; exact hwd⟩
                  linarith
                · refine ⟨1, one_pos, fun w hw hwd => ?_⟩
                  exact absurd ⟨w, hw, by rw [Metric.mem_sphere]; exact hwd⟩ hK
              obtain ⟨c, hc0, hc⟩ := hgap
              have hPgrow : ∀ z ∈ M.X, r ≤ dist z x0 → vP + c ≤ φ P z := G P hP c hc0 hc
              set ρ := ‖x0‖ + 2 * r with hρ
              have hρr : 2 * r ≤ ρ := by have := norm_nonneg x0; linarith
              have hball : ∀ z, dist z x0 ≤ r → ‖z‖ ≤ ρ := by
                intro z hz
                have := norm_sub_norm_le z x0
                rw [dist_eq_norm] at hz
                linarith
              have hID : ∀ ν, admissible M ν → ∀ ρ' : ℝ, ∀ x ∈ M.X, ‖x‖ ≤ ρ' →
                  ENNReal.ofReal |φ P x - φ ν x| ≤ informationDistance M ρ' P ν := by
                intro ν hν ρ' x hx hxρ
                unfold informationDistance
                refine le_trans ?_ (le_iSup₂ (f := fun x (_ : x ∈ {x : EuclideanSpace ℝ (Fin n) | x ∈ M.X ∧ ‖x‖ ≤ ρ'}) =>
                  EReal.abs (M.integral P 0 x - M.integral ν 0 x)) x ⟨hx, hxρ⟩)
                rw [M1 P hP x hx, M1 ν hν x hx, ← EReal.coe_sub, EReal.abs_def]
              have hIDmono : ∀ ν ρ1 ρ2, ρ1 ≤ ρ2 → informationDistance M ρ1 P ν ≤ informationDistance M ρ2 P ν := by
                intro ν ρ1 ρ2 h
                unfold informationDistance
                exact iSup₂_mono' fun x hx => ⟨x, ⟨hx.1, hx.2.trans h⟩, le_rfl⟩
              have hdbound : ∀ ν, admissible M ν → ∀ ρ' e : ℝ, informationDistance M ρ' P ν < ENNReal.ofReal e →
                  ∀ x ∈ M.X, ‖x‖ ≤ ρ' → |φ P x - φ ν x| ≤ (informationDistance M ρ' P ν).toReal := by
                intro ν hν ρ' e hlt x hx hxρ
                have hne : informationDistance M ρ' P ν ≠ ⊤ := ne_top_of_lt hlt
                have := hID ν hν ρ' x hx hxρ
                rw [← ENNReal.ofReal_toReal hne] at this
                exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp this
              have hx0r : x0 ∈ Metric.closedBall x0 r := Metric.mem_closedBall_self hr0.le
              have core : ∀ Q, admissible M Q → informationDistance M ρ P Q < ENNReal.ofReal (c/3) →
                  ∃ xb ∈ M.X, dist xb x0 ≤ r ∧ (∀ z ∈ M.X, φ Q xb ≤ φ Q z) ∧
                    (∀ z ∈ M.X, r ≤ dist z x0 →
                      φ Q x0 + (c - 2 * (informationDistance M ρ P Q).toReal) ≤ φ Q z) ∧
                    |vP - φ Q xb| ≤ (informationDistance M ρ P Q).toReal ∧
                    (informationDistance M ρ P Q).toReal < c/3 := by
                intro Q hQ hlt
                set d := (informationDistance M ρ P Q).toReal with hd
                have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
                have hdc : d < c/3 := ENNReal.toReal_lt_of_lt_ofReal hlt
                have hb := hdbound Q hQ ρ (c/3) hlt
                have hx0b := hb x0 hx0X (hball x0 hx0r)
                have hQgrow := G Q hQ (c - 2*d) (by linarith) (by
                  intro w hw hwd
                  have h1 := hb w hw (hball w hwd.le)
                  have h2 := hc w hw hwd
                  rw [abs_le] at h1 hx0b
                  linarith)
                have hK1c : IsCompact (M.X ∩ Metric.closedBall x0 r) :=
                  (isCompact_closedBall x0 r).inter_left hXc
                obtain ⟨xb, hxb, hmin⟩ := D1 Q hQ _ hK1c Set.inter_subset_left ⟨x0, hx0X, hx0r⟩
                  ⟨vP - d, by
                    rintro _ ⟨z, hz, rfl⟩
                    have h1 := hb z hz.1 (hball z hz.2)
                    have := hPmin z hz.1
                    rw [abs_le] at h1; linarith⟩
                have hxbd : dist xb x0 ≤ r := hxb.2
                have hglob : ∀ z ∈ M.X, φ Q xb ≤ φ Q z := by
                  intro z hz
                  by_cases hzr : dist z x0 ≤ r
                  · exact hmin z ⟨hz, hzr⟩
                  · have := hQgrow z hz (not_le.mp hzr).le
                    have := hmin x0 ⟨hx0X, hx0r⟩
                    linarith
                refine ⟨xb, hxb.1, hxbd, hglob, hQgrow, ?_, hdc⟩
                have h1 := hb xb hxb.1 (hball xb hxbd)
                have h2 := hPmin xb hxb.1
                have h3 := hmin x0 ⟨hx0X, hx0r⟩
                rw [abs_le] at h1 hx0b ⊢
                constructor <;> linarith
              have hvQe : ∀ Q, admissible M Q → ∀ xb ∈ M.X, (∀ z ∈ M.X, φ Q xb ≤ φ Q z) →
                  M.v Q = ((φ Q xb : ℝ) : EReal) := by
                intro Q hQ xb hxbX hglob
                apply le_antisymm
                · rw [← M1 Q hQ xb hxbX]; exact hvle Q xb hxbX
                · unfold ProbMetricStab.General.Model.v
                  refine le_iInf₂ fun z hz => ?_
                  rw [hMM] at hz
                  rw [M1 Q hQ z hz]; exact_mod_cast hglob z hz
              refine ⟨ρ, c / 3, by linarith, by linarith, ?_, ?_⟩
              · intro Q hQ hlt
                obtain ⟨xb, hxbX, hxbd, hglob, hQgrow, hv, hdc⟩ := core Q hQ hlt
                set D := informationDistance M ρ P Q with hD
                set d := D.toReal with hd
                have hDne : D ≠ ⊤ := ne_top_of_lt hlt
                have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
                have hvQ := hvQe Q hQ xb hxbX hglob
                have hSQ : ∀ x ∈ M.S Q, x ∈ M.X ∧ φ Q x = φ Q xb := by
                  intro x hx
                  have hxX : x ∈ M.X := by have := hx.1; rwa [hMM] at this
                  refine ⟨hxX, ?_⟩
                  have := hx.2; rw [M1 Q hQ x hxX, hvQ] at this; exact_mod_cast this
                refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨xb, hSmem Q xb hxbX (by rw [hvQ, M1 Q hQ xb hxbX])⟩, ?_⟩
                · rw [hvPe]; exact EReal.coe_ne_top _
                · rw [hvPe]; exact EReal.coe_ne_bot _
                · rw [hvQ]; exact EReal.coe_ne_top _
                · rw [hvQ]; exact EReal.coe_ne_bot _
                · rw [hvPe, hvQ, ← EReal.coe_sub, EReal.abs_def, ← ENNReal.ofReal_toReal hDne]
                  exact ENNReal.ofReal_le_ofReal hv
                · intro x hx
                  obtain ⟨hxX, hxv⟩ := hSQ x hx
                  have hxr : dist x x0 < r := by
                    by_contra h; push_neg at h
                    have := hQgrow x hxX h
                    have h3 := hglob x0 hx0X
                    linarith
                  have hb := hdbound Q hQ ρ (c/3) hlt x hxX (hball x hxr.le)
                  have hPx : φ P x ≤ vP + 2 * d := by rw [abs_le] at hb hv; linarith
                  rcases eq_or_lt_of_le hd0 with hd00 | hdpos
                  · refine ⟨x, hSmem P x hxX (by
                      rw [M1 P hP x hxX, hvPe]; exact_mod_cast (by linarith : φ P x ≤ vP)), by simp⟩
                  · have hDpos : 0 < D := (ENNReal.toReal_pos_iff.mp hdpos).1
                    have hinf_ne : Metric.infEDist x (M.S P) ≠ ⊤ := Metric.infEDist_ne_top ⟨x0, hx0⟩
                    set τ := (Metric.infEDist x (M.S P)).toReal with hτ
                    have hcond : conditioning M P τ ≤ ((2 * D : ℝ≥0∞) : EReal) := by
                      unfold conditioning
                      refine (iInf₂_le x ⟨hxX, by rw [hτ, ENNReal.ofReal_toReal hinf_ne]⟩).trans ?_
                      have e2 : (2 * D : ℝ≥0∞) = ENNReal.ofReal (2 * d) := by
                        rw [ENNReal.ofReal_mul (by norm_num), hd, ENNReal.ofReal_toReal hDne]; simp
                      rw [M1 P hP x hxX, hvPe, ← EReal.coe_sub, e2, EReal.coe_ennreal_ofReal]
                      exact_mod_cast (show φ P x - vP ≤ max (2 * d) 0 from by
                        have := le_max_left (2*d) 0; linarith)
                    have hτle : ENNReal.ofReal τ ≤ conditioningInverse M P ((2 * D : ℝ≥0∞) : EReal) := by
                      unfold conditioningInverse
                      exact le_iSup₂ (f := fun τ (_ : τ ∈ {τ : ℝ | 0 ≤ τ ∧
                        conditioning M P τ ≤ ((2 * D : ℝ≥0∞) : EReal)}) => ENNReal.ofReal τ) τ
                        ⟨ENNReal.toReal_nonneg, hcond⟩
                    have hlt2 : Metric.infEDist x (M.S P) < Metric.infEDist x (M.S P) + D :=
                      ENNReal.lt_add_right hinf_ne hDpos.ne'
                    obtain ⟨y, hy, hxy⟩ := Metric.infEDist_lt_iff.mp hlt2
                    refine ⟨y, hy, hxy.le.trans ?_⟩
                    unfold conditioningModulus
                    rw [add_comm D]
                    refine add_le_add ?_ le_rfl
                    rw [← ENNReal.ofReal_toReal hinf_ne]; exact hτle
              · intro ε hε hεb Q hQ hlt'
                set D' := informationDistance M (ρ + ε) P Q with hD'
                have hD'ne : D' ≠ ⊤ := ne_top_of_lt hlt'
                set d' := D'.toReal with hd'
                have hd'0 : 0 ≤ d' := ENNReal.toReal_nonneg
                have hd'ε : d' < ε := ENNReal.toReal_lt_of_lt_ofReal hlt'
                have hDD : informationDistance M ρ P Q ≤ D' := hIDmono Q ρ (ρ+ε) (by linarith)
                have hlt : informationDistance M ρ P Q < ENNReal.ofReal (c/3) :=
                  lt_of_le_of_lt hDD (lt_of_lt_of_le hlt' (ENNReal.ofReal_le_ofReal hεb.le))
                obtain ⟨xb, hxbX, hxbd, hglob, hQgrow, hv, hdc⟩ := core Q hQ hlt
                have hdd' : (informationDistance M ρ P Q).toReal ≤ d' := ENNReal.toReal_mono hD'ne hDD
                have hvQ := hvQe Q hQ xb hxbX hglob
                have hb' := hdbound Q hQ (ρ+ε) ε hlt'
                have hball2 : ∀ z, dist z x0 ≤ r → ‖z‖ ≤ ρ + ε := fun z hz => (hball z hz).trans (by linarith)
                have hEP : ∀ x, x ∈ epsilonSolutions M P ε ↔ x ∈ M.X ∧ φ P x ≤ vP + ε := by
                  intro x; constructor
                  · rintro ⟨hx, h⟩; refine ⟨hx, ?_⟩; rw [M1 P hP x hx, hvPe] at h; exact_mod_cast h
                  · rintro ⟨hx, h⟩; refine ⟨hx, ?_⟩; rw [M1 P hP x hx, hvPe]; exact_mod_cast h
                have hEQ : ∀ x, x ∈ epsilonSolutions M Q ε ↔ x ∈ M.X ∧ φ Q x ≤ φ Q xb + ε := by
                  intro x; constructor
                  · rintro ⟨hx, h⟩; refine ⟨hx, ?_⟩; rw [M1 Q hQ x hx, hvQ] at h; exact_mod_cast h
                  · rintro ⟨hx, h⟩; refine ⟨hx, ?_⟩; rw [M1 Q hQ x hx, hvQ]; exact_mod_cast h
                have hmove : ∀ ν, admissible M ν → ∀ x ∈ M.X, ∀ y ∈ M.X, ∀ m : ℝ,
                    φ ν x ≤ m + ε + 2 * d' → φ ν y ≤ m → dist x y ≤ 2 * r →
                    ∃ z ∈ M.X, φ ν z ≤ m + ε ∧ edist x z ≤ ENNReal.ofReal (2 * ρ / ε) * D' := by
                  intro ν hν x hx y hy m h1 h2 h3
                  set l := 2 * d' / (ε + 2 * d') with hl
                  have hden : 0 < ε + 2 * d' := by linarith
                  have hl0 : 0 ≤ l := div_nonneg (by linarith) hden.le
                  have hl1 : l ≤ 1 := (div_le_one hden).mpr (by linarith)
                  have hkey : (1 - l) * (ε + 2 * d') = ε := by rw [hl]; field_simp; ring
                  refine ⟨(1 - l) • x + l • y, hXcv hx hy (by linarith) hl0 (by ring), ?_, ?_⟩
                  · have h4 := M2 ν hν x hx y hy (1 - l) l (by linarith) hl0 (by ring)
                    have e1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - l by linarith)
                    have e2 := mul_le_mul_of_nonneg_left h2 hl0
                    nlinarith
                  · have hxz : x - ((1 - l) • x + l • y) = l • (x - y) := by module
                    rw [edist_dist, dist_eq_norm, hxz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0,
                      ← dist_eq_norm, ← ENNReal.ofReal_toReal hD'ne, ← ENNReal.ofReal_mul (by positivity)]
                    apply ENNReal.ofReal_le_ofReal
                    have hl' : l ≤ 2 * d' / ε := div_le_div_of_nonneg_left (by linarith) hε (by linarith)
                    calc l * dist x y ≤ (2 * d' / ε) * (2 * r) :=
                          mul_le_mul hl' h3 dist_nonneg (by positivity)
                      _ ≤ (2 * d' / ε) * ρ := mul_le_mul_of_nonneg_left hρr (by positivity)
                      _ = 2 * ρ / ε * d' := by ring
                have hEPball : ∀ x ∈ epsilonSolutions M P ε, dist x x0 ≤ r := by
                  intro x hx; rw [hEP] at hx
                  by_contra h; push_neg at h
                  have := hPgrow x hx.1 h.le; linarith
                have hEQball : ∀ x ∈ epsilonSolutions M Q ε, dist x x0 ≤ r := by
                  intro x hx; rw [hEQ] at hx
                  by_contra h; push_neg at h
                  have := hQgrow x hx.1 h.le
                  have := hglob x0 hx0X
                  linarith
                refine ⟨⟨x0, (hEP x0).mpr ⟨hx0X, by linarith⟩⟩, ⟨xb, (hEQ xb).mpr ⟨hxbX, by linarith⟩⟩, ?_⟩
                apply Metric.hausdorffEDist_le_of_mem_edist
                · intro x hx
                  have hxr := hEPball x hx
                  rw [hEP] at hx
                  have h1 := hb' x hx.1 (hball2 x hxr)
                  rw [abs_le] at h1 hv
                  obtain ⟨z, hzX, hz, hxz⟩ := hmove Q hQ x hx.1 xb hxbX (φ Q xb) (by linarith) le_rfl
                    (by have := dist_triangle x x0 xb; rw [dist_comm x0 xb] at this; linarith)
                  exact ⟨z, (hEQ z).mpr ⟨hzX, hz⟩, hxz⟩
                · intro x hx
                  have hxr := hEQball x hx
                  rw [hEQ] at hx
                  have h1 := hb' x hx.1 (hball2 x hxr)
                  rw [abs_le] at h1 hv
                  obtain ⟨z, hzX, hz, hxz⟩ := hmove P hP x hx.1 x0 hx0X vP (by linarith) le_rfl
                    (by linarith)
                  exact ⟨z, (hEP z).mpr ⟨hzX, hz⟩, hxz⟩
