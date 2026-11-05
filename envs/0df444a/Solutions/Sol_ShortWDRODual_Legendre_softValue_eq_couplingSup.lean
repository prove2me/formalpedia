-- Prove2me | solution 1 for ShortWDRODual.Legendre.softValue_eq_couplingSup
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:14:40.746766+00:00
-- url     : https://prove2.me/submissions/3aba225c-0024-48b5-85fc-7e13d36716f4

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre RWPI.SqrtLasso Filter Topology

namespace WDRO1SC

variable {X : Type*} [MeasurableSpace X]

lemma lamMul_eq (lam : ℝ) {t : ENNReal} (ht : t ≠ ⊤) :
    lamMul lam t = ((lam * t.toReal : ℝ) : EReal) := by
  unfold lamMul
  rw [if_neg ht, EReal.coe_mul, EReal.coe_ennreal_toReal ht]

lemma lamMul_measurable (lam : ℝ) : Measurable (lamMul lam) := by
  unfold lamMul
  refine Measurable.ite (measurableSet_singleton ⊤) measurable_const ?_
  exact (measurable_coe_ennreal_ereal).const_mul _

lemma phiLam_measurable (c : X → X → ENNReal) (f : X → ℝ) (hf : Measurable f)
    (hc : Measurable (fun p : X × X => c p.1 p.2)) (lam : ℝ) :
    Measurable (phiLam c f lam) := by
  unfold phiLam
  have h1 : Measurable (fun p : X × X => (f p.2 : EReal)) :=
    (hf.comp measurable_snd).coe_real_ereal
  have h2 : Measurable (fun p : X × X => lamMul lam (c p.1 p.2)) :=
    (lamMul_measurable lam).comp hc
  simp_rw [sub_eq_add_neg]
  exact h1.add h2.neg

lemma phi_top (c : X → X → ENNReal) (f : X → ℝ) (lam : ℝ) (p : X × X) (h : c p.1 p.2 = ⊤) :
    phiLam c f lam p = ⊥ := by
  unfold phiLam lamMul; rw [if_pos h, EReal.sub_top]

lemma phi_fin (c : X → X → ENNReal) (f : X → ℝ) (lam : ℝ) (p : X × X) (h : c p.1 p.2 ≠ ⊤) :
    phiLam c f lam p = ((f p.2 - lam * (c p.1 p.2).toReal : ℝ) : EReal) := by
  unfold phiLam; rw [lamMul_eq lam h, ← EReal.coe_sub]

lemma phi_le_f (c : X → X → ENNReal) (f : X → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (p : X × X) :
    phiLam c f lam p ≤ (f p.2 : EReal) := by
  by_cases h : c p.1 p.2 = ⊤
  · rw [phi_top c f lam p h]; exact bot_le
  · rw [phi_fin c f lam p h]
    exact_mod_cast (by nlinarith [ENNReal.toReal_nonneg (a := c p.1 p.2)] :
      f p.2 - lam * (c p.1 p.2).toReal ≤ f p.2)

lemma ennreal_coe_sub_fin {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ((a : EReal) - (b : EReal)) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal ha, EReal.coe_ennreal_toReal hb]

lemma key_max (w : ℝ) : max w 0 = max (-w) 0 + w := by
  rcases le_total w 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- The expectation of `φ_λ` under a coupling of finite cost. -/
lemma ext_phi_eq (c : X → X → ENNReal) (f : X → ℝ) (hf : Measurable f)
    (hc : Measurable (fun p : X × X => c p.1 p.2)) {lam : ℝ} (hlam : 0 ≤ lam)
    (π : Measure (X × X)) (hC : ∫⁻ p, c p.1 p.2 ∂π ≠ ⊤) :
    extIntegral π (phiLam c f lam) =
      extIntegral (π.map Prod.snd) (fun x => (f x : EReal)) -
        ((lam * (∫⁻ p, c p.1 p.2 ∂π).toReal : ℝ) : EReal) := by
  have hφ := phiLam_measurable c f hf hc lam
  have hneg : Measurable (fun e : EReal => -e) := (continuous_neg : Continuous fun e : EReal => -e).measurable
  have hfp : Measurable (fun x : X => ((f x : EReal)).toENNReal) := hf.coe_real_ereal.ereal_toENNReal
  have hfm : Measurable (fun x : X => (-(f x : EReal)).toENNReal) :=
    (hneg.comp hf.coe_real_ereal).ereal_toENNReal
  have hφp : Measurable (fun p => (phiLam c f lam p).toENNReal) := hφ.ereal_toENNReal
  have hφm : Measurable (fun p => (-phiLam c f lam p).toENNReal) := (hneg.comp hφ).ereal_toENNReal
  have hae : ∀ᵐ p ∂π, c p.1 p.2 < ⊤ := ae_lt_top hc hC
  set C := ∫⁻ p, c p.1 p.2 ∂π
  -- the a.e. identity
  have hid : ∀ᵐ p ∂π, (phiLam c f lam p).toENNReal +
      ((-(f p.2 : EReal)).toENNReal + ENNReal.ofReal lam * c p.1 p.2) =
      (-phiLam c f lam p).toENNReal + ((f p.2 : EReal)).toENNReal := by
    filter_upwards [hae] with p hp
    rw [phi_fin c f lam p hp.ne, ← EReal.coe_neg, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    rw [← ENNReal.ofReal_toReal hp.ne, ← ENNReal.ofReal_mul hlam]
    set r := (c p.1 p.2).toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_ofReal']
    rw [max_eq_left hr, key_max (f p.2 - lam * r), key_max (f p.2),
      max_eq_left (by positivity : 0 ≤ lam * r)]
    ring
  have hint := lintegral_congr_ae hid
  have hfm2 : AEMeasurable (fun p : X × X => (-(f p.2 : EReal)).toENNReal) π :=
    (hfm.comp measurable_snd).aemeasurable
  have hWmle0 : ∫⁻ p, (-phiLam c f lam p).toENNReal ∂π ≤
      ∫⁻ p, (-(f p.2 : EReal)).toENNReal ∂π + ENNReal.ofReal lam * ∫⁻ p, c p.1 p.2 ∂π := by
    rw [← lintegral_const_mul _ hc, ← lintegral_add_left' hfm2]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with p hp
    rw [phi_fin c f lam p hp.ne, ← EReal.coe_neg, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    have hcr : ENNReal.ofReal lam * c p.1 p.2 = ENNReal.ofReal (lam * (c p.1 p.2).toReal) := by
      rw [ENNReal.ofReal_mul hlam, ENNReal.ofReal_toReal hp.ne]
    rw [hcr]
    calc ENNReal.ofReal (-(f p.2 - lam * (c p.1 p.2).toReal))
        = ENNReal.ofReal (-f p.2 + lam * (c p.1 p.2).toReal) := by ring_nf
      _ ≤ _ := ENNReal.ofReal_add_le
  rw [lintegral_add_left' hφp.aemeasurable, lintegral_add_left' hfm2,
    lintegral_const_mul _ hc, lintegral_add_left' hφm.aemeasurable] at hint
  -- integrals of `f` parts
  have hPp : ∫⁻ x, ((f x : EReal)).toENNReal ∂(π.map Prod.snd) = ∫⁻ p, ((f p.2 : EReal)).toENNReal ∂π :=
    lintegral_map hfp measurable_snd
  have hPm : ∫⁻ x, (-(f x : EReal)).toENNReal ∂(π.map Prod.snd) = ∫⁻ p, (-(f p.2 : EReal)).toENNReal ∂π :=
    lintegral_map hfm measurable_snd
  unfold extIntegral
  rw [hPp, hPm]
  set Wp := ∫⁻ p, (phiLam c f lam p).toENNReal ∂π
  set Wm := ∫⁻ p, (-phiLam c f lam p).toENNReal ∂π
  set Fp := ∫⁻ p, ((f p.2 : EReal)).toENNReal ∂π
  set Fm := ∫⁻ p, (-(f p.2 : EReal)).toENNReal ∂π
  have hCfin : C ≠ ⊤ := hC
  have hlC : ENNReal.ofReal lam * C ≠ ⊤ := by finiteness
  have hlCr : (ENNReal.ofReal lam * C).toReal = lam * C.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam]
  by_cases hFm : Fm = ⊤
  · -- `𝔼[f⁻] = ∞`
    have hWm : Wm = ⊤ := by
      refine top_le_iff.mp (hFm ▸ lintegral_mono fun p => EReal.toENNReal_le_toENNReal ?_)
      exact EReal.neg_le_neg_iff.mpr (phi_le_f c f hlam p)
    rw [hWm, hFm, EReal.coe_ennreal_top, EReal.sub_top, EReal.sub_top, EReal.bot_sub]
  have hWmfin : Wm ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hFm, hlC⟩) hWmle0
  by_cases hFp : Fp = ⊤
  · have hWp : Wp = ⊤ := by
      rw [hFp, add_top] at hint
      by_contra hne
      exact (ENNReal.add_ne_top.mpr ⟨hne, ENNReal.add_ne_top.mpr ⟨hFm, hlC⟩⟩) hint
    rw [hWp, hFp, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hWmfin,
      ← EReal.coe_ennreal_toReal hFm, EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_sub_coe]
  have hWp : Wp ≠ ⊤ := by
    intro h
    rw [h, top_add] at hint
    exact (ENNReal.add_ne_top.mpr ⟨hWmfin, hFp⟩) hint.symm
  have hr := congrArg ENNReal.toReal hint
  rw [ENNReal.toReal_add hWp (ENNReal.add_ne_top.mpr ⟨hFm, hlC⟩), ENNReal.toReal_add hFm hlC,
    ENNReal.toReal_add hWmfin hFp, hlCr] at hr
  rw [ennreal_coe_sub_fin hWp hWmfin, ennreal_coe_sub_fin hFp hFm, ← EReal.coe_sub]
  congr 1
  linarith

lemma ereal_le_of_forall_pos {a b : EReal} (h : ∀ δ : ℝ, 0 < δ → a ≤ (δ : EReal) + b) : a ≤ b := by
  induction b using EReal.rec with
  | bot =>
    have := h 1 one_pos
    simpa using this
  | top => exact le_top
  | coe b =>
    induction a using EReal.rec with
    | bot => exact bot_le
    | top =>
      have := h 1 one_pos
      rw [← EReal.coe_add] at this
      exact absurd this (not_le.mpr (EReal.coe_lt_top _))
    | coe a =>
      have : ∀ δ : ℝ, 0 < δ → a ≤ δ + b := fun δ hδ => by
        have := h δ hδ
        rw [← EReal.coe_add] at this
        exact_mod_cast this
      exact_mod_cast le_of_forall_pos_le_add fun δ hδ => by linarith [this δ hδ]

end WDRO1SC

open WDRO1SC

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    softValue c f Phat lam = ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam) := by
  set S := ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam) with hS
  have hneg : Measurable (fun e : EReal => -e) := (continuous_neg : Continuous fun e : EReal => -e).measurable
  have hφ := phiLam_measurable c f hf hc lam
  apply le_antisymm
  · -- (P-soft) ≤ coupling supremum
    unfold softValue
    refine iSup₂_le fun P hP => ?_
    obtain ⟨hPp, hKlt⟩ := hP
    have hKtop : transportCost c Phat P ≠ ⊤ := hKlt.ne
    refine ereal_le_of_forall_pos fun δ hδ => ?_
    set ε : ENNReal := ENNReal.ofReal (δ / (lam + 1)) with hε
    have hε0 : ε ≠ 0 := by
      rw [hε]; exact (ENNReal.ofReal_pos.mpr (div_pos hδ (by linarith))).ne'
    obtain ⟨π, ⟨hπ, hπ1, hπ2⟩, hπc⟩ : ∃ π : Measure (X × X),
        (IsProbabilityMeasure π ∧ π.map Prod.fst = Phat ∧ π.map Prod.snd = P) ∧
        ∫⁻ w, c w.1 w.2 ∂π < transportCost c Phat P + ε := by
      have := ENNReal.lt_add_right hKtop hε0
      unfold transportCost at this
      rw [iInf_lt_iff] at this
      obtain ⟨π, hπ⟩ := this
      rw [iInf_lt_iff] at hπ
      obtain ⟨h1, h2⟩ := hπ
      exact ⟨π, h1, by unfold transportCost; exact h2⟩
    have hCfin : ∫⁻ w, c w.1 w.2 ∂π ≠ ⊤ :=
      (lt_trans hπc (ENNReal.add_lt_top.mpr ⟨hKlt, by rw [hε]; exact ENNReal.ofReal_lt_top⟩)).ne
    have hmem : π ∈ couplingsFst Phat := ⟨hπ, hπ1⟩
    have heq := ext_phi_eq c f hf hc hlam π hCfin
    rw [hπ2] at heq
    set C := ∫⁻ w, c w.1 w.2 ∂π
    set K := transportCost c Phat P
    have hCr : C.toReal ≤ K.toReal + δ / (lam + 1) := by
      have h1 : C ≤ K + ε := hπc.le
      have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hKtop, by rw [hε]; exact ENNReal.ofReal_ne_top⟩) h1
      rw [ENNReal.toReal_add hKtop (by rw [hε]; exact ENNReal.ofReal_ne_top), hε,
        ENNReal.toReal_ofReal (div_pos hδ (by linarith)).le] at h2
      exact h2
    have hlamC : lam * C.toReal ≤ lam * K.toReal + δ := by
      have h1 : lam * (δ / (lam + 1)) ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
      nlinarith
    have hle : extIntegral P (fun x => (f x : EReal)) - ((lam * K.toReal : ℝ) : EReal) ≤
        extIntegral P (fun x => (f x : EReal)) - ((lam * C.toReal : ℝ) : EReal) + (δ : EReal) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
      exact add_le_add le_rfl (by exact_mod_cast (by linarith : -(lam * K.toReal) ≤ -(lam * C.toReal) + δ))
    rw [← heq] at hle
    refine hle.trans ?_
    rw [add_comm]
    exact add_le_add le_rfl (le_iSup₂ (f := fun γ (_ : γ ∈ couplingsFst Phat) =>
      extIntegral γ (phiLam c f lam)) π hmem)
  · -- coupling supremum ≤ (P-soft)
    have FIN : ∀ π : Measure (X × X), π ∈ couplingsFst Phat → ∫⁻ p, c p.1 p.2 ∂π ≠ ⊤ →
        extIntegral π (phiLam c f lam) ≤ softValue c f Phat lam := by
      intro π hπ hC
      obtain ⟨hπp, hπ1⟩ := hπ
      set P := π.map Prod.snd
      have hPp : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
      have hK : transportCost c Phat P ≤ ∫⁻ p, c p.1 p.2 ∂π := by
        unfold transportCost
        exact iInf₂_le π ⟨hπp, hπ1, rfl⟩
      have hKtop : transportCost c Phat P ≠ ⊤ := ne_top_of_le_ne_top hC hK
      rw [ext_phi_eq c f hf hc hlam π hC]
      refine le_trans ?_ (le_iSup₂ (f := fun (P : Measure X)
        (_ : IsProbabilityMeasure P ∧ transportCost c Phat P < ⊤) =>
        extIntegral P (fun x => (f x : EReal)) -
          ((lam * (transportCost c Phat P).toReal : ℝ) : EReal)) P ⟨hPp, lt_top_iff_ne_top.mpr hKtop⟩)
      refine EReal.sub_le_sub le_rfl ?_
      exact_mod_cast mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hC hK) hlam
    refine iSup₂_le fun γ hγ => ?_
    by_cases hC : ∫⁻ p, c p.1 p.2 ∂γ ≠ ⊤
    · exact FIN γ hγ hC
    set T := {p : X × X | c p.1 p.2 = ⊤} with hT
    have hTm : MeasurableSet T := hc (measurableSet_singleton ⊤)
    set B := ∫⁻ p, (-phiLam c f lam p).toENNReal ∂γ with hB
    by_cases hBtop : B = ⊤
    · unfold extIntegral
      rw [← hB, hBtop, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
    have hnull : γ T = 0 := by
      by_contra hne
      apply hBtop
      refine top_le_iff.mp (le_trans ?_ (setLIntegral_le_lintegral T _))
      rw [setLIntegral_congr_fun hTm (g := fun _ => (⊤ : ENNReal)) (fun p hp => by
        simp only
        rw [phi_top c f lam p hp, EReal.neg_bot, EReal.toENNReal_top])]
      rw [setLIntegral_const, ENNReal.top_mul hne]
    -- truncation
    set A : ℕ → Set (X × X) := fun n => {p | c p.1 p.2 ≤ (n : ENNReal)} with hA
    have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le hc measurable_const
    have hAmono : Monotone A := by
      intro n m hnm p hp
      exact le_trans (show c p.1 p.2 ≤ (n : ENNReal) from hp) (by exact_mod_cast hnm)
    set dg : X × X → X × X := fun p => (p.1, p.1) with hdg
    have hdgm : Measurable dg := measurable_fst.prodMk measurable_fst
    set γn : ℕ → Measure (X × X) := fun n => γ.restrict (A n) + (γ.restrict (A n)ᶜ).map dg
    obtain ⟨hγp, hγ1⟩ := hγ
    have hγn_mem : ∀ n, γn n ∈ couplingsFst Phat := by
      intro n
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [γn]
        rw [Measure.add_apply, Measure.map_apply hdgm MeasurableSet.univ, Set.preimage_univ,
          Measure.restrict_apply_univ, Measure.restrict_apply_univ,
          measure_add_measure_compl (hAm n), measure_univ]
      · simp only [γn]
        rw [Measure.map_add _ _ measurable_fst, Measure.map_map measurable_fst hdgm]
        have : (Prod.fst ∘ dg) = Prod.fst := rfl
        rw [this, ← Measure.map_add _ _ measurable_fst, Measure.restrict_add_restrict_compl (hAm n), hγ1]
    have hγn_cost : ∀ n, ∫⁻ p, c p.1 p.2 ∂(γn n) ≠ ⊤ := by
      intro n
      simp only [γn]
      rw [lintegral_add_measure, lintegral_map hc hdgm]
      simp only [hdg, hc0, lintegral_zero, add_zero]
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (n : ENNReal) ∂(γ.restrict (A n))) ?_ ?_
      · rw [lintegral_const]; finiteness
      · exact lintegral_mono_ae ((ae_restrict_mem (hAm n)).mono fun p hp => hp)
    have hFINn : ∀ n, extIntegral (γn n) (phiLam c f lam) ≤ softValue c f Phat lam :=
      fun n => FIN _ (hγn_mem n) (hγn_cost n)
    -- the lower bound for the truncated couplings
    have hφp : Measurable (fun p => (phiLam c f lam p).toENNReal) := hφ.ereal_toENNReal
    have hφm : Measurable (fun p => (-phiLam c f lam p).toENNReal) := (hneg.comp hφ).ereal_toENNReal
    have hdiag : ∀ p : X × X, phiLam c f lam (dg p) = (f p.1 : EReal) := by
      intro p
      rw [phi_fin c f lam (dg p) (by simp [hdg, hc0])]
      simp [hdg, hc0]
    set g : X × X → ENNReal := fun p => (-(f p.1 : EReal)).toENNReal with hg
    have hgm : Measurable g := (hneg.comp (hf.comp measurable_fst).coe_real_ereal).ereal_toENNReal
    set a : ℕ → ENNReal := fun n => ∫⁻ p in A n, (phiLam c f lam p).toENNReal ∂γ
    set e : ℕ → ENNReal := fun n => ∫⁻ p in (A n)ᶜ, g p ∂γ
    have hlow : ∀ n, ((a n : ENNReal) : EReal) - ((B + e n : ENNReal) : EReal) ≤
        extIntegral (γn n) (phiLam c f lam) := by
      intro n
      unfold extIntegral
      simp only [γn]
      rw [lintegral_add_measure, lintegral_add_measure, lintegral_map hφp hdgm, lintegral_map hφm hdgm]
      simp only [Function.comp_def, hdiag]
      refine EReal.sub_le_sub ?_ ?_
      · exact_mod_cast le_self_add
      · refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr (add_le_add ?_ le_rfl)
        exact lintegral_mono' Measure.restrict_le_self le_rfl
    -- limits
    set Wp := ∫⁻ p, (phiLam c f lam p).toENNReal ∂γ
    have hta : Tendsto a atTop (𝓝 Wp) := by
      have h1 : ∀ n, a n = (γ.withDensity fun p => (phiLam c f lam p).toENNReal) (A n) :=
        fun n => (withDensity_apply _ (hAm n)).symm
      have h2 := tendsto_measure_iUnion_atTop (μ := γ.withDensity fun p => (phiLam c f lam p).toENNReal) hAmono
      rw [withDensity_apply _ (MeasurableSet.iUnion hAm)] at h2
      rw [setLIntegral_eq_of_support_subset] at h2
      · simpa only [Function.comp_def, ← h1] using h2
      · intro p hp
        rw [Function.mem_support] at hp
        have hct : c p.1 p.2 ≠ ⊤ := by
          intro h; apply hp; rw [phi_top c f lam p h]; exact EReal.toENNReal_bot
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hct
        exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
    have hte : Tendsto e atTop (𝓝 0) := by
      have h1 : ∀ n, e n = (γ.withDensity g) (A n)ᶜ :=
        fun n => (withDensity_apply _ (hAm n).compl).symm
      have hfin : ∫⁻ p, g p ∂γ ≠ ⊤ := by
        have : ∫⁻ p, g p ∂γ = ∫⁻ x, (-(f x : EReal)).toENNReal ∂Phat := by
          have hfm' : Measurable (fun x : X => (-(f x : EReal)).toENNReal) :=
            (hneg.comp hf.coe_real_ereal).ereal_toENNReal
          rw [← hγ1, lintegral_map hfm' measurable_fst]
        rw [this]
        intro h
        unfold extIntegral at hfint
        rw [h, EReal.coe_ennreal_top, EReal.sub_top] at hfint
        exact lt_irrefl _ hfint
      have h2 := tendsto_measure_iInter_atTop (μ := γ.withDensity g)
        (fun n => (hAm n).compl.nullMeasurableSet) (fun n m h => Set.compl_subset_compl.mpr (hAmono h))
        ⟨0, by rw [withDensity_apply _ (hAm 0).compl]; exact ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)⟩
      have h3 : (⋂ n, (A n)ᶜ) = T := by
        ext p
        simp only [Set.mem_iInter, Set.mem_compl_iff, hA, Set.mem_setOf_eq, not_le, hT]
        constructor
        · intro h
          by_contra hne
          obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
          exact absurd (h n) (not_lt.mpr hn.le)
        · intro h n; rw [h]; exact lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top n)
      rw [h3, withDensity_apply _ hTm, setLIntegral_measure_zero _ _ hnull] at h2
      simpa only [Function.comp_def, ← h1] using h2
    have hlim : Tendsto (fun n => ((a n : ENNReal) : EReal) - ((B + e n : ENNReal) : EReal)) atTop
        (𝓝 ((Wp : EReal) - (B : EReal))) := by
      have htb : Tendsto (fun n => B + e n) atTop (𝓝 B) := by
        simpa using (tendsto_const_nhds (x := B)).add hte
      simp_rw [sub_eq_add_neg]
      have h1 := (continuous_coe_ennreal_ereal.tendsto _).comp hta
      have h2 := ((continuous_neg : Continuous fun e : EReal => -e).tendsto _).comp
        ((continuous_coe_ennreal_ereal.tendsto _).comp htb)
      refine (EReal.continuousAt_add ?_ ?_).tendsto.comp (h1.prodMk_nhds h2)
      · right
        simp only [ne_eq, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
        exact hBtop
      · left; exact EReal.coe_ennreal_ne_bot _
    refine le_of_forall_lt fun y hy => ?_
    have hy' : y < (Wp : EReal) - (B : EReal) := hy
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hy')).exists
    exact lt_of_lt_of_le hn ((hlow n).trans (hFINn n))
