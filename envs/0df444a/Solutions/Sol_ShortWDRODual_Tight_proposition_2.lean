-- Prove2me | solution 1 for ShortWDRODual.Tight.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:49:40.838285+00:00
-- url     : https://prove2.me/submissions/faffcb7d-d184-4969-a499-7027dc110134

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Tight_Setting
import Theorems.Thm_ShortWDRODual_Tight_supFn_lsc
import Theorems.Thm_ShortWDRODual_Tight_integral_le_supFn
import Theorems.Thm_ShortWDRODual_Tight_exists_eps_optimal_coupling

namespace ShortWDRODual.Tight.RedAux

open MeasureTheory ModelRiskOT.Duality

lemma extIntegral_mono' {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) {ψ φ : Y → EReal}
    (h : ∀ y, ψ y ≤ φ y) : extIntegral ν ψ ≤ extIntegral ν φ := by
  unfold extIntegral
  exact EReal.sub_le_sub
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun y => EReal.toENNReal_le_toENNReal (h y)))
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun y => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h y))))

lemma ereal_le_of_forall {a s : EReal}
    (h : ∀ ε : ℝ, 0 < ε → ((-6 * ε : ℝ) : EReal) + a ≤ s) : a ≤ s := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top =>
    have := h 1 one_pos
    rwa [EReal.coe_add_top] at this
  | coe a =>
    induction s using EReal.rec with
    | bot =>
      have := h 1 one_pos
      rw [← EReal.coe_add] at this
      exact absurd this (by simp)
    | top => exact le_top
    | coe s =>
      rw [EReal.coe_le_coe_iff]
      by_contra hlt
      push_neg at hlt
      have := h ((a - s) / 12) (by linarith)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      linarith

lemma coupling_mem {X : Type*} [MeasurableSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (T : X → X) (hT : Measurable T) :
    Phat.map (fun x => (x, T x)) ∈ ShortWDRODual.Legendre.couplingsFst Phat := by
  have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  refine ⟨Measure.isProbabilityMeasure_map hg.aemeasurable, ?_⟩
  rw [Measure.map_map measurable_fst hg]
  exact Measure.map_id

lemma bot_lt_sub {a b : ENNReal} (hb : b ≠ ⊤) : (⊥ : EReal) < (a : EReal) - (b : EReal) := by
  have h1 : (0 : EReal) - (b : EReal) ≤ (a : EReal) - (b : EReal) :=
    EReal.sub_le_sub (by exact_mod_cast (bot_le : (0:ENNReal) ≤ a)) le_rfl
  refine lt_of_lt_of_le ?_ h1
  rw [← EReal.coe_ennreal_toReal hb, ← EReal.coe_zero, ← EReal.coe_sub]
  exact EReal.bot_lt_coe _

lemma sub_le_self' (a b : ENNReal) : (a : EReal) - (b : EReal) ≤ (a : EReal) := by
  have := EReal.sub_le_sub (le_refl (a : EReal)) (show (0 : EReal) ≤ (b : EReal) by exact_mod_cast (bot_le : (0:ENNReal) ≤ b))
  simpa using this

end ShortWDRODual.Tight.RedAux

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Tight ShortWDRODual.Tight.RedAux

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (htight : IsTightMeasureSet ({Phat} : Set (Measure X)))
    (f : X → ℝ) (hf : NullMeasurable f Phat)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam) :
    (TopologicalSpace.SeparableSpace X →
        @Measurable (X × NullMeasurableSpace X Phat) EReal _ _
          (fun q => pWassIntegrand f lam p (q.1, q.2))) ∧
      ShortWDRODual.Legendre.IPEq Phat (pWassIntegrand f lam p) := by
  refine ⟨?_, ?_⟩
  · intro hsep
    have : SecondCountableTopology X := inferInstance
    have hid : @Measurable (NullMeasurableSpace X Phat) X _ _ (fun x => x) :=
      fun s hs => hs.nullMeasurableSet
    have hd : Measurable (fun q : X × NullMeasurableSpace X Phat => dist (q.1 : X) (q.2 : X)) :=
      measurable_dist.comp (measurable_fst.prodMk (hid.comp measurable_snd))
    have hfm : Measurable (fun q : X × NullMeasurableSpace X Phat => f q.2) :=
      (show @Measurable (NullMeasurableSpace X Phat) ℝ _ _ f from hf).comp measurable_snd
    unfold pWassIntegrand
    exact measurable_coe_real_ereal.comp (hfm.sub (measurable_const.mul (hd.pow_const p)))
  · set Φ := ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p) with hΦdef
    have hΦm : Measurable Φ := (supFn_lsc f p hp lam hlam).2
    refine ⟨hΦm.nullMeasurable, le_antisymm ?_
      (iSup₂_le (integral_le_supFn Phat htight f hf hfint p hp lam hlam))⟩
    set S := ⨆ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat,
      extIntegral γ (pWassIntegrand f lam p) with hSdef
    have hS : ∀ T : X → X, Measurable T →
        extIntegral (Phat.map (fun x => (x, T x))) (pWassIntegrand f lam p) ≤ S :=
      fun T hT => le_iSup₂ (f := fun γ (_ : γ ∈ ShortWDRODual.Legendre.couplingsFst Phat) =>
        extIntegral γ (pWassIntegrand f lam p)) _ (coupling_mem Phat T hT)
    rcases lt_or_eq_of_le (le_top : extIntegral Phat Φ ≤ ⊤) with hfin | hinf
    · apply ereal_le_of_forall
      intro ε hε
      obtain ⟨T, hT, hlt⟩ :=
        exists_eps_optimal_coupling Phat htight f hf hfint p hp lam hlam hfin ε hε
      exact hlt.le.trans (hS T hT)
    · -- the case `𝔼[Φ] = +∞`: truncate `f` at level `M`
      set Bf : ENNReal := ∫⁻ x, (-((f x : ℝ) : EReal)).toENNReal ∂Phat with hBfdef
      have hBf : Bf ≠ ⊤ := by
        intro h
        unfold extIntegral at hfint
        rw [← hBfdef, h] at hfint
        simp at hfint
      let fM : ℕ → X → ℝ := fun M x => min (f x) (M : ℝ)
      let ΦM : ℕ → X → EReal := fun M => ShortWDRODual.Legendre.supFn (pWassIntegrand (fM M) lam p)
      have hΦMm : ∀ M, Measurable (ΦM M) := fun M => (supFn_lsc (fM M) p hp lam hlam).2
      have hfMm : ∀ M, NullMeasurable (fM M) Phat := fun M =>
        (show @Measurable (NullMeasurableSpace X Phat) ℝ _ _ f from hf).min measurable_const
      have hneg : ∀ M x, (-((fM M x : ℝ) : EReal)).toENNReal ≤ (-((f x : ℝ) : EReal)).toENNReal := by
        intro M x
        by_cases h : f x ≤ M
        · simp only [fM, min_eq_left h, le_refl]
        · push_neg at h
          have : fM M x = M := min_eq_right h.le
          rw [this, EReal.toENNReal_of_nonpos]
          · exact bot_le
          · rw [← EReal.coe_neg]; exact_mod_cast (by linarith [(M.cast_nonneg : (0:ℝ) ≤ M)])
      have hfintM : ∀ M, ⊥ < extIntegral Phat (fun x => ((fM M x : ℝ) : EReal)) := by
        intro M
        unfold extIntegral
        exact bot_lt_sub (ne_top_of_le_ne_top hBf (lintegral_mono (hneg M)))
      have hΦMle : ∀ M x, ΦM M x ≤ ((M : ℝ) : EReal) := by
        intro M x
        refine iSup_le fun y => ?_
        show (((fM M y - lam * dist x y ^ p : ℝ)) : EReal) ≤ ((M : ℝ) : EReal)
        rw [EReal.coe_le_coe_iff]
        have h1 : fM M y ≤ M := min_le_right _ _
        have h2 : 0 ≤ lam * dist x y ^ p := mul_nonneg hlam (Real.rpow_nonneg dist_nonneg _)
        linarith
      have hAM : ∀ M, ∫⁻ x, (ΦM M x).toENNReal ∂Phat ≤ ENNReal.ofReal M := by
        intro M
        calc ∫⁻ x, (ΦM M x).toENNReal ∂Phat ≤ ∫⁻ _x, ENNReal.ofReal M ∂Phat :=
              lintegral_mono fun x => by
                have := EReal.toENNReal_le_toENNReal (hΦMle M x)
                rw [EReal.real_coe_toENNReal] at this
                exact this
          _ = ENNReal.ofReal M := by simp
      have hfinM : ∀ M, extIntegral Phat (ΦM M) < ⊤ := by
        intro M
        unfold extIntegral
        refine lt_of_le_of_lt (sub_le_self' _ _) ?_
        rw [← EReal.coe_ennreal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hAM M))]
        exact EReal.coe_lt_top _
      -- the negative part of `Φ_M` is dominated by `f⁻`
      have hΦMself : ∀ M x, ((fM M x : ℝ) : EReal) ≤ ΦM M x := by
        intro M x
        refine le_trans ?_ (le_iSup (fun y => pWassIntegrand (fM M) lam p (x, y)) x)
        show ((fM M x : ℝ) : EReal) ≤ ((fM M x - lam * dist x x ^ p : ℝ) : EReal)
        rw [dist_self, Real.zero_rpow (by linarith)]
        simp
      have hBM : ∀ M, ∫⁻ x, (-ΦM M x).toENNReal ∂Phat ≤ Bf := by
        intro M
        refine lintegral_mono fun x => le_trans ?_ (hneg M x)
        exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hΦMself M x))
      -- `φ_M ≤ φ`
      have hφM : ∀ M q, pWassIntegrand (fM M) lam p q ≤ pWassIntegrand f lam p q := by
        intro M q
        show ((fM M q.2 - lam * dist q.1 q.2 ^ p : ℝ) : EReal) ≤ ((f q.2 - lam * dist q.1 q.2 ^ p : ℝ) : EReal)
        rw [EReal.coe_le_coe_iff]
        have : fM M q.2 ≤ f q.2 := min_le_left _ _
        linarith
      have hkey : ∀ M, ((-6 * 1 : ℝ) : EReal) + extIntegral Phat (ΦM M) ≤ S := by
        intro M
        obtain ⟨T, hT, hlt⟩ := exists_eps_optimal_coupling Phat htight (fM M) (hfMm M) (hfintM M)
          p hp lam hlam (hfinM M) 1 one_pos
        exact hlt.le.trans ((extIntegral_mono' _ (hφM M)).trans (hS T hT))
      -- conclude
      have hreal : ∀ M, extIntegral Phat (ΦM M) =
          (((∫⁻ x, (ΦM M x).toENNReal ∂Phat).toReal - (∫⁻ x, (-ΦM M x).toENNReal ∂Phat).toReal : ℝ)
            : EReal) := by
        intro M
        unfold extIntegral
        rw [EReal.coe_sub,
          EReal.coe_ennreal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hAM M)),
          EReal.coe_ennreal_toReal (ne_top_of_le_ne_top hBf (hBM M))]
      have hkey' : ∀ M, ((-6 * 1 + ((∫⁻ x, (ΦM M x).toENNReal ∂Phat).toReal -
          (∫⁻ x, (-ΦM M x).toENNReal ∂Phat).toReal) : ℝ) : EReal) ≤ S := by
        intro M
        rw [EReal.coe_add, ← hreal]
        exact hkey M
      rw [hinf]
      by_contra hStop
      have hSne : S ≠ ⊤ := fun h => hStop (h ▸ le_rfl)
      have hSbot : S ≠ ⊥ := by
        intro h
        have := hkey' 0
        rw [h, le_bot_iff] at this
        exact EReal.coe_ne_bot _ this
      obtain ⟨s, hs⟩ : ∃ s : ℝ, S = (s : EReal) := ⟨S.toReal, (EReal.coe_toReal hSne hSbot).symm⟩
      -- every truncated positive part is bounded by `s + 6 + ‖f⁻‖`
      have hbound : ∀ M, ∫⁻ x, (ΦM M x).toENNReal ∂Phat ≤ ENNReal.ofReal (s + 6 + Bf.toReal) := by
        intro M
        have h1 := hkey' M
        rw [hs, EReal.coe_le_coe_iff] at h1
        have h2 : (∫⁻ x, (-ΦM M x).toENNReal ∂Phat).toReal ≤ Bf.toReal :=
          ENNReal.toReal_mono hBf (hBM M)
        rw [ENNReal.le_ofReal_iff_toReal_le
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hAM M))
          (by linarith [ENNReal.toReal_nonneg (a := ∫⁻ x, (ΦM M x).toENNReal ∂Phat)])]
        linarith
      -- monotone convergence: `∫ Φ⁺ ≤ sup_M ∫ Φ_M⁺`
      have hmono : Monotone (fun M x => (ΦM M x).toENNReal) := by
        intro M M' hMM' x
        refine EReal.toENNReal_le_toENNReal (iSup_mono fun y => ?_)
        show ((fM M y - lam * dist x y ^ p : ℝ) : EReal) ≤ ((fM M' y - lam * dist x y ^ p : ℝ) : EReal)
        rw [EReal.coe_le_coe_iff]
        have : fM M y ≤ fM M' y := min_le_min_left _ (by exact_mod_cast hMM')
        linarith
      have hpt : ∀ x, (Φ x).toENNReal ≤ ⨆ M, (ΦM M x).toENNReal := by
        intro x
        have hc : (Φ x).toENNReal = ⨆ y, (pWassIntegrand f lam p (x, y)).toENNReal :=
          Monotone.map_iSup_of_continuousAt EReal.continuous_toENNReal.continuousAt
            (fun _ _ h => EReal.toENNReal_le_toENNReal h) EReal.toENNReal_bot
        rw [hc]
        refine iSup_le fun y => ?_
        obtain ⟨M, hM⟩ := exists_nat_ge (f y)
        refine le_trans ?_ (le_iSup _ M)
        refine EReal.toENNReal_le_toENNReal ?_
        refine le_trans (le_of_eq ?_) (le_iSup (fun y => pWassIntegrand (fM M) lam p (x, y)) y)
        show ((f y - lam * dist x y ^ p : ℝ) : EReal) = ((fM M y - lam * dist x y ^ p : ℝ) : EReal)
        simp only [fM, min_eq_left hM]
      have hA : ∫⁻ x, (Φ x).toENNReal ∂Phat ≤ ENNReal.ofReal (s + 6 + Bf.toReal) := by
        calc ∫⁻ x, (Φ x).toENNReal ∂Phat ≤ ∫⁻ x, ⨆ M, (ΦM M x).toENNReal ∂Phat := lintegral_mono hpt
          _ = ⨆ M, ∫⁻ x, (ΦM M x).toENNReal ∂Phat :=
              lintegral_iSup (fun M => (hΦMm M).ereal_toENNReal) hmono
          _ ≤ _ := iSup_le hbound
      have hle : extIntegral Phat Φ ≤ ((∫⁻ x, (Φ x).toENNReal ∂Phat : ENNReal) : EReal) := by
        unfold extIntegral; exact sub_le_self' _ _
      rw [hinf, ← EReal.coe_ennreal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA)] at hle
      exact EReal.coe_ne_top _ (top_le_iff.mp hle)
