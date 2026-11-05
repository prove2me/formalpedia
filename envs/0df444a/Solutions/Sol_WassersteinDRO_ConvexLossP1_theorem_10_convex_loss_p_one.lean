-- Prove2me | solution 1 for WassersteinDRO.ConvexLossP1.theorem_10_convex_loss_p_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:43:33.250055+00:00
-- url     : https://prove2.me/submissions/07d3f6f9-3814-4512-9f72-179bddde7163

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_WassersteinDRO_ConvexLossP1_empirical
import Definitions.Def_WassersteinDRO_ConvexLossP1_worstCaseRisk
import Definitions.Def_WassersteinDRO_ConvexLossP1_lipModulus

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory

namespace WDRO7

open WassersteinDRO.ConvexLossP1

/-- The Moreau-Yosida (sup-convolution) envelope `ℓ_γ(ξ) = sup_{z ∈ Ξ} ℓ(z) - γ‖z - ξ‖^p`
of the paper (Theorem 7, p. 9), used here as an auxiliary function. -/
noncomputable def moreauYosida {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E)
    (γ p : ℝ) (ξ : E) : EReal :=
  ⨆ z ∈ Ξ, ℓ z - ((γ * ‖z - ξ‖ ^ p : ℝ) : EReal)

/-! ## Part A: EReal / ENNReal bookkeeping -/

lemma toENNReal_real (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x), EReal.toReal_coe]

lemma ofReal_eq_ofReal_max (a : ℝ) : ENNReal.ofReal a = ENNReal.ofReal (max a 0) := by
  rcases le_total a 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

lemma max_split (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- Positive parts: `a ≤ b + r` gives `a⁺ ≤ b⁺ + r`. -/
lemma pos_le_of_le {a b : EReal} {r : ℝ} (hr : 0 ≤ r) (h : a ≤ b + (r : EReal)) :
    a.toENNReal ≤ b.toENNReal + ENNReal.ofReal r := by
  induction a using EReal.rec with
  | bot => simp
  | top =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => simp
    | coe y =>
      exfalso
      rw [← EReal.coe_add] at h
      exact (not_le.mpr (EReal.coe_lt_top _)) h
  | coe x =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => simp
    | coe y =>
      have h' : x ≤ y + r := by exact_mod_cast h
      rw [toENNReal_real, toENNReal_real, ofReal_eq_ofReal_max x,
        ofReal_eq_ofReal_max y, ← ENNReal.ofReal_add (le_max_right _ _) hr]
      apply ENNReal.ofReal_le_ofReal
      rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy <;>
        simp only [max_eq_left, max_eq_right, hx, hy] <;> linarith

/-- Both parts: `a ≤ b + r` gives `a⁺ + b⁻ ≤ b⁺ + a⁻ + r`. -/
lemma pos_neg_le {a b : EReal} {r : ℝ} (hr : 0 ≤ r) (h : a ≤ b + (r : EReal)) :
    a.toENNReal + (-b).toENNReal ≤ b.toENNReal + (-a).toENNReal + ENNReal.ofReal r := by
  induction a using EReal.rec with
  | bot => simp
  | top =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => simp
    | coe y =>
      exfalso
      rw [← EReal.coe_add] at h
      exact (not_le.mpr (EReal.coe_lt_top _)) h
  | coe x =>
    induction b using EReal.rec with
    | bot => simp at h
    | top => simp
    | coe y =>
      have h' : x ≤ y + r := by exact_mod_cast h
      rw [← EReal.coe_neg, ← EReal.coe_neg]
      simp only [toENNReal_real]
      rw [ofReal_eq_ofReal_max x, ofReal_eq_ofReal_max y, ofReal_eq_ofReal_max (-x),
        ofReal_eq_ofReal_max (-y), ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
        ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
        ← ENNReal.ofReal_add (by positivity) hr]
      apply ENNReal.ofReal_le_ofReal
      have e1 := max_split x
      have e2 := max_split y
      linarith

/-- Turning an ENNReal inequality into the EReal difference inequality. -/
lemma ereal_sub_le {a b c d e : ENNReal} (ha : a ≠ ⊤) (hc : c ≠ ⊤) (he : e ≠ ⊤)
    (h : a + d ≤ c + b + e) : (a : EReal) - b ≤ ((c : EReal) - d) + e := by
  by_cases hb : b = ⊤
  · subst hb; simp
  by_cases hd : d = ⊤
  · exfalso; subst hd
    rw [add_top, top_le_iff] at h
    simp [ENNReal.add_eq_top, hb, hc, he] at h
  rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb, ← EReal.coe_ennreal_toReal hc,
    ← EReal.coe_ennreal_toReal hd, ← EReal.coe_ennreal_toReal he, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  have h2 := (ENNReal.toReal_le_toReal (by simp [ha, hd]) (by simp [hb, hc, he])).mpr h
  rw [ENNReal.toReal_add ha hd, ENNReal.toReal_add (by simp [hb, hc]) he,
    ENNReal.toReal_add hc hb] at h2
  linarith

lemma ereal_le_of_forall_pos {x y : EReal} (h : ∀ η : ℝ, 0 < η → x ≤ y + (η : EReal)) : x ≤ y := by
  induction y using EReal.rec with
  | bot =>
    have := h 1 one_pos
    simpa using this
  | top => exact le_top
  | coe y =>
    induction x using EReal.rec with
    | bot => exact bot_le
    | top =>
      exfalso
      have := h 1 one_pos
      rw [← EReal.coe_add] at this
      exact (not_le.mpr (EReal.coe_lt_top _)) this
    | coe x =>
      rw [EReal.coe_le_coe_iff]
      refine le_of_forall_pos_le_add fun η hη => ?_
      have := h η hη
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this

/-! ## Part B: measurability -/

lemma measurable_pos {E : Type*} [MeasurableSpace E] {f : E → EReal} (hf : Measurable f) :
    Measurable fun x => (f x).toENNReal := hf.ereal_toENNReal

lemma measurable_neg' {E : Type*} [MeasurableSpace E] {f : E → EReal} (hf : Measurable f) :
    Measurable fun x => (-f x).toENNReal := hf.neg.ereal_toENNReal

lemma continuous_sub_coe (a : EReal) {E : Type*} [TopologicalSpace E] {g : E → ℝ}
    (hg : Continuous g) : Continuous fun x => a - ((g x : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => simpa using continuous_const
  | top => simpa using continuous_const
  | coe a =>
    have : (fun x => (a : EReal) - ((g x : ℝ) : EReal)) = fun x => (((a - g x : ℝ)) : EReal) := by
      funext x; rw [EReal.coe_sub]
    rw [this]
    exact continuous_coe_real_ereal.comp (continuous_const.sub hg)

lemma moreauYosida_lsc {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E)
    (γ p : ℝ) (hp : 0 ≤ p) : LowerSemicontinuous (moreauYosida ℓ Ξ γ p) := by
  unfold moreauYosida
  refine lowerSemicontinuous_iSup fun z => lowerSemicontinuous_iSup fun _ => ?_
  exact (continuous_sub_coe (ℓ z) (continuous_const.mul
    ((continuous_const.sub continuous_id).norm.rpow_const fun _ => Or.inr hp))).lowerSemicontinuous

/-! ## Part C: weak duality -/

lemma coe_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ((ENNReal.ofReal x : ENNReal) : EReal) = (x : EReal) := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left hx]

lemma le_sub_add (a : EReal) (r : ℝ) : a ≤ a - (r : EReal) + (r : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => simp
  | coe a => rw [← EReal.coe_sub, ← EReal.coe_add]; simp

lemma lintegral_fst {E : Type*} [MeasurableSpace E] {π : Measure (E × E)} {Q : Measure E}
    (h : π.map Prod.fst = Q) {f : E → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f x.1 ∂π = ∫⁻ x, f x ∂Q := by
  rw [← h, lintegral_map hf measurable_fst]

lemma lintegral_snd {E : Type*} [MeasurableSpace E] {π : Measure (E × E)} {P : Measure E}
    (h : π.map Prod.snd = P) {f : E → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f x.2 ∂π = ∫⁻ x, f x ∂P := by
  rw [← h, lintegral_map hf measurable_snd]

/-- Weak duality against one coupling `π` of `Q` and `P`. -/
lemma weak_core {E : Type*} [MeasurableSpace E] (Q P : Measure E) (π : Measure (E × E))
    (h1 : π.map Prod.fst = Q) (h2 : π.map Prod.snd = P) {Ξ : Set E} (hΞ : MeasurableSet Ξ)
    (hQ : Q Ξᶜ = 0) {ℓ g : E → EReal} (hℓ : Measurable ℓ) (hg : Measurable g) {γ : ℝ}
    (hγ : 0 ≤ γ) {c : E × E → ℝ} (hc : Measurable c) (hc0 : ∀ x, 0 ≤ c x)
    (hpt : ∀ x y, x ∈ Ξ → ℓ x ≤ g y + ((γ * c (x, y) : ℝ) : EReal)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∫⁻ x, ENNReal.ofReal (c x) ∂π ≤ ENNReal.ofReal C) :
    risk Q ℓ ≤ risk P g + ((γ * C : ℝ) : EReal) := by
  have hae : ∀ᵐ x ∂π, x.1 ∈ Ξ := by
    have : π (Prod.fst ⁻¹' Ξᶜ) = 0 := by
      rw [← Measure.map_apply measurable_fst hΞ.compl, h1, hQ]
    rw [ae_iff]; exact this
  have hγC : ∫⁻ x, ENNReal.ofReal (γ * c x) ∂π ≤ ENNReal.ofReal (γ * C) := by
    simp_rw [ENNReal.ofReal_mul hγ]
    rw [lintegral_const_mul _ hc.ennreal_ofReal]
    gcongr
  have mA : Measurable fun x : E × E => (ℓ x.1).toENNReal := (measurable_pos hℓ).comp measurable_fst
  have mA' : Measurable fun x : E × E => (-ℓ x.1).toENNReal :=
    (measurable_neg' hℓ).comp measurable_fst
  have mB : Measurable fun x : E × E => (g x.2).toENNReal := (measurable_pos hg).comp measurable_snd
  have mB' : Measurable fun x : E × E => (-g x.2).toENNReal :=
    (measurable_neg' hg).comp measurable_snd
  have eA : ∫⁻ x, (ℓ x.1).toENNReal ∂π = ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q := lintegral_fst h1 (measurable_pos hℓ)
  have eA' : ∫⁻ x, (-ℓ x.1).toENNReal ∂π = ∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q :=
    lintegral_fst h1 (measurable_neg' hℓ)
  have eB : ∫⁻ x, (g x.2).toENNReal ∂π = ∫⁻ ξ, (g ξ).toENNReal ∂P := lintegral_snd h2 (measurable_pos hg)
  have eB' : ∫⁻ x, (-g x.2).toENNReal ∂π = ∫⁻ ξ, (-g ξ).toENNReal ∂P :=
    lintegral_snd h2 (measurable_neg' hg)
  have hpos : ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q ≤ ∫⁻ ξ, (g ξ).toENNReal ∂P + ENNReal.ofReal (γ * C) := by
    rw [← eA, ← eB]
    calc ∫⁻ x, (ℓ x.1).toENNReal ∂π
        ≤ ∫⁻ x, ((g x.2).toENNReal + ENNReal.ofReal (γ * c x)) ∂π := by
          refine lintegral_mono_ae (hae.mono fun x hx => ?_)
          exact pos_le_of_le (mul_nonneg hγ (hc0 x)) (hpt x.1 x.2 hx)
      _ = ∫⁻ x, (g x.2).toENNReal ∂π + ∫⁻ x, ENNReal.ofReal (γ * c x) ∂π := lintegral_add_left mB _
      _ ≤ _ := by gcongr
  have hboth : ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q + ∫⁻ ξ, (-g ξ).toENNReal ∂P ≤
      ∫⁻ ξ, (g ξ).toENNReal ∂P + ∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q + ENNReal.ofReal (γ * C) := by
    rw [← eA, ← eB, ← eA', ← eB', ← lintegral_add_left mA, ← lintegral_add_left mB]
    calc ∫⁻ x, ((ℓ x.1).toENNReal + (-g x.2).toENNReal) ∂π
        ≤ ∫⁻ x, ((g x.2).toENNReal + (-ℓ x.1).toENNReal + ENNReal.ofReal (γ * c x)) ∂π := by
          refine lintegral_mono_ae (hae.mono fun x hx => ?_)
          exact pos_neg_le (mul_nonneg hγ (hc0 x)) (hpt x.1 x.2 hx)
      _ = ∫⁻ x, ((g x.2).toENNReal + (-ℓ x.1).toENNReal) ∂π
            + ∫⁻ x, ENNReal.ofReal (γ * c x) ∂π := lintegral_add_left (mB.add mA') _
      _ ≤ _ := by gcongr
  unfold risk
  by_cases hB : ∫⁻ ξ, (g ξ).toENNReal ∂P = ⊤
  · rw [if_pos hB, EReal.top_add_coe]; exact le_top
  rw [if_neg hB]
  have hA : ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q ≠ ⊤ := by
    intro hA; rw [hA, top_le_iff] at hpos; simp [ENNReal.add_eq_top, hB] at hpos
  rw [if_neg hA]
  have := ereal_sub_le hA hB ENNReal.ofReal_ne_top hboth
  rwa [coe_ofReal_of_nonneg (mul_nonneg hγ hC0)] at this

lemma exists_coupling {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {p ε : ℝ}
    (hp : 0 < p) (hε : 0 ≤ ε) {Q P : Measure E} (hW : wasserstein p Q P ≤ ENNReal.ofReal ε)
    {η : ℝ} (hη : 0 < η) : ∃ π ∈ couplings Q P,
      ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π ≤ ENNReal.ofReal (ε ^ p + η) := by
  unfold wasserstein at hW
  rw [one_div, ENNReal.rpow_inv_le_iff hp, ENNReal.ofReal_rpow_of_nonneg hε hp.le] at hW
  have hlt := lt_of_le_of_lt hW
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith : ε ^ p < ε ^ p + η))
  simp only [iInf_lt_iff] at hlt
  obtain ⟨π, hπ, h⟩ := hlt
  exact ⟨π, hπ, h.le⟩

/-- Weak duality for one `Q` in the ball and one `γ ≥ 0`. -/
lemma weak_duality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {p : ℝ} (hp : 1 ≤ p) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) {ℓ : E → EReal} (hℓ : Measurable ℓ) {ε : ℝ} (hε : 0 ≤ ε)
    {Q : Measure E} (hQ : Q ∈ ambiguityBall ε p P Ξ) {γ : ℝ} (hγ : 0 ≤ γ) :
    risk Q ℓ ≤ risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal) := by
  obtain ⟨_, hQΞ, hW⟩ := hQ
  have hg : Measurable (moreauYosida ℓ Ξ γ p) :=
    (moreauYosida_lsc ℓ Ξ γ p (by linarith)).measurable
  have hc : Measurable fun x : E × E => ‖x.1 - x.2‖ ^ p :=
    ((measurable_fst.sub measurable_snd).norm).pow_const p
  refine ereal_le_of_forall_pos fun η hη => ?_
  have hη' : 0 < η / (γ + 1) := div_pos hη (by linarith)
  obtain ⟨π, ⟨_, h1, h2⟩, hπ⟩ := exists_coupling (by linarith) hε hW hη'
  have key := weak_core Q P π h1 h2 hΞ.measurableSet hQΞ hℓ hg hγ hc
    (fun x => by positivity)
    (fun x y hx => by
      have : ℓ x - ((γ * ‖x - y‖ ^ p : ℝ) : EReal) ≤ moreauYosida ℓ Ξ γ p y := by
        unfold moreauYosida
        exact le_iSup₂ (f := fun z _ => ℓ z - ((γ * ‖z - y‖ ^ p : ℝ) : EReal)) x hx
      exact (le_sub_add (ℓ x) _).trans (by gcongr))
    (by positivity) hπ
  refine key.trans ?_
  rw [add_assoc, ← EReal.coe_add]
  gcongr
  have : γ * (η / (γ + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  nlinarith

lemma le_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {p : ℝ} (hp : 1 ≤ p) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) {ℓ : E → EReal} (hℓ : Measurable ℓ) {ε : ℝ} (hε : 0 ≤ ε) :
    worstCaseRisk ε p P Ξ ℓ
      ≤ ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal) :=
  iSup₂_le fun _ hQ => le_iInf₂ fun _ hγ => weak_duality hp hΞ P hℓ hε hQ hγ

/-! ## Part D: the case ε = 0 -/

lemma pos_le_abs (a : EReal) : a.toENNReal ≤ EReal.abs a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [toENNReal_real, EReal.abs_def]; exact ENNReal.ofReal_le_ofReal (le_abs_self x)

lemma negpart_le_abs (a : EReal) : (-a).toENNReal ≤ EReal.abs a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_neg, toENNReal_real, EReal.abs_def]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs x)

lemma self_mem_ball {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {p ε : ℝ} (hp : 0 < p)
    (hε : 0 ≤ ε) (P : Measure E) [IsProbabilityMeasure P] {Ξ : Set E} (hPΞ : P Ξᶜ = 0) :
    P ∈ ambiguityBall ε p P Ξ := by
  refine ⟨inferInstance, hPΞ, ?_⟩
  have hd : Measurable fun x : E => (x, x) := measurable_id.prodMk measurable_id
  have hπ : P.map (fun x : E => (x, x)) ∈ couplings P P := by
    refine ⟨Measure.isProbabilityMeasure_map hd.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hd]; exact Measure.map_id
    · rw [Measure.map_map measurable_snd hd]; exact Measure.map_id
  have h0 : (⨅ π ∈ couplings P P, ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) = 0 := by
    refine le_antisymm ((iInf₂_le _ hπ).trans ?_) zero_le
    refine (lintegral_map_le _ _).trans ?_
    simp [Real.zero_rpow hp.ne']
  unfold wasserstein
  rw [h0, ENNReal.zero_rpow_of_pos (by positivity)]
  exact zero_le

lemma ereal_sub_coe_le {a : EReal} {r s u : ℝ} (h : a - (r : EReal) ≤ (s : EReal)) :
    a - ((r + u : ℝ) : EReal) ≤ ((s - u : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp at h
  | coe a =>
    rw [← EReal.coe_sub] at h ⊢
    rw [EReal.coe_le_coe_iff] at h ⊢
    linarith

lemma ereal_sub_le_self {a : EReal} {r : ℝ} (hr : 0 ≤ r) : a - (r : EReal) ≤ a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_sub, EReal.coe_le_coe_iff]; linarith

lemma my_mono {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) {p γ γ' : ℝ}
    (h : γ ≤ γ') (ξ : E) : moreauYosida ℓ Ξ γ' p ξ ≤ moreauYosida ℓ Ξ γ p ξ := by
  unfold moreauYosida
  refine iSup₂_mono fun z _ => EReal.sub_le_sub le_rfl ?_
  rw [EReal.coe_le_coe_iff]
  exact mul_le_mul_of_nonneg_right h (by positivity)

lemma my_ge {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) {Ξ : Set E} {p γ : ℝ}
    (hp : 0 < p) {ξ : E} (hξ : ξ ∈ Ξ) : ℓ ξ ≤ moreauYosida ℓ Ξ γ p ξ := by
  unfold moreauYosida
  refine le_iSup₂_of_le ξ hξ ?_
  simp [Real.zero_rpow hp.ne']

lemma my_eventually_le {E : Type*} [NormedAddCommGroup E] {ℓ : E → EReal}
    (husc : UpperSemicontinuous ℓ) (Ξ : Set E) {p : ℝ} (hp : 0 < p) {γ0 : ℝ} (hγ0 : 0 ≤ γ0) {ξ : E}
    (hfin : moreauYosida ℓ Ξ γ0 p ξ < ⊤) {t : ℝ} (ht : ℓ ξ < t) :
    ∃ N : ℕ, moreauYosida ℓ Ξ (γ0 + N) p ξ ≤ t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (husc ξ (t : EReal) ht)
  set m : ℝ := (moreauYosida ℓ Ξ γ0 p ξ).toReal
  have hm : moreauYosida ℓ Ξ γ0 p ξ ≤ (m : EReal) := EReal.le_coe_toReal hfin.ne
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ p
  obtain ⟨N, hN⟩ := exists_nat_ge ((m - t) / δ ^ p)
  refine ⟨N, ?_⟩
  unfold moreauYosida
  refine iSup₂_le fun z hz => ?_
  by_cases hzd : dist z ξ < δ
  · exact (ereal_sub_le_self (by positivity)).trans (hball hzd).le
  · have hd : δ ^ p ≤ ‖z - ξ‖ ^ p := by
      rw [← dist_eq_norm]; exact Real.rpow_le_rpow hδ.le (not_lt.mp hzd) hp.le
    have h1 : ℓ z - ((γ0 * ‖z - ξ‖ ^ p : ℝ) : EReal) ≤ (m : EReal) := by
      refine le_trans ?_ hm
      unfold moreauYosida
      exact le_iSup₂ (f := fun z _ => ℓ z - ((γ0 * ‖z - ξ‖ ^ p : ℝ) : EReal)) z hz
    have h2 := ereal_sub_coe_le (u := (N : ℝ) * ‖z - ξ‖ ^ p) h1
    have e : (γ0 + (N : ℝ)) * ‖z - ξ‖ ^ p = γ0 * ‖z - ξ‖ ^ p + N * ‖z - ξ‖ ^ p := by ring
    rw [e]
    refine h2.trans ?_
    rw [EReal.coe_le_coe_iff]
    have h3 : m - t ≤ N * δ ^ p := by rwa [div_le_iff₀ hδp] at hN
    have h4 : (N : ℝ) * δ ^ p ≤ N * ‖z - ξ‖ ^ p := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N)
    linarith

lemma risk_eq_coe {E : Type*} [MeasurableSpace E] (P : Measure E) (f : E → EReal)
    (hA : ∫⁻ ξ, (f ξ).toENNReal ∂P ≠ ⊤) (hB : ∫⁻ ξ, (-f ξ).toENNReal ∂P ≠ ⊤) :
    risk P f = (((∫⁻ ξ, (f ξ).toENNReal ∂P).toReal - (∫⁻ ξ, (-f ξ).toENNReal ∂P).toReal : ℝ) : EReal) := by
  unfold risk
  rw [if_neg hA, ← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB, EReal.coe_sub]

lemma dual_le_risk_zero {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {p : ℝ} (hp : 0 < p) {Ξ : Set E} (P : Measure E)
    (hPΞ : P Ξᶜ = 0) {ℓ : E → EReal} (husc : UpperSemicontinuous ℓ)
    (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂P < ⊤) {γ0 : ℝ} (hγ0 : 0 ≤ γ0)
    (hfin0 : risk P (moreauYosida ℓ Ξ γ0 p) < ⊤) :
    ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk P (moreauYosida ℓ Ξ γ p) ≤ risk P ℓ := by
  set f : ℕ → E → EReal := fun n => moreauYosida ℓ Ξ (γ0 + n) p with hf
  have hfm : ∀ n, Measurable (f n) := fun n => (moreauYosida_lsc ℓ Ξ _ p hp.le).measurable
  have hℓm : Measurable ℓ := husc.measurable
  have hf0 : f 0 = moreauYosida ℓ Ξ γ0 p := by simp [hf]
  have hA : ∫⁻ ξ, (ℓ ξ).toENNReal ∂P < ⊤ := (lintegral_mono fun ξ => pos_le_abs _).trans_lt hint
  have hB : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂P < ⊤ :=
    (lintegral_mono fun ξ => negpart_le_abs _).trans_lt hint
  have hA0 : ∫⁻ ξ, (f 0 ξ).toENNReal ∂P ≠ ⊤ := by
    intro h; rw [hf0] at h; unfold risk at hfin0; rw [if_pos h] at hfin0; exact lt_irrefl _ hfin0
  -- the good set
  have gΞ : ∀ᵐ ξ ∂P, ξ ∈ Ξ := ae_iff.2 (show P {a | ¬ a ∈ Ξ} = 0 from hPΞ)
  have g0 : ∀ᵐ ξ ∂P, f 0 ξ < ⊤ := by
    filter_upwards [ae_lt_top (measurable_pos (hfm 0)) hA0] with ξ hξ
    rw [lt_top_iff_ne_top] at hξ ⊢
    intro h; rw [h] at hξ; simp at hξ
  have gT : ∀ᵐ ξ ∂P, ℓ ξ ≠ ⊤ := by
    filter_upwards [ae_lt_top (measurable_pos hℓm) hA.ne] with ξ hξ
    intro h; rw [h] at hξ; simp at hξ
  have gB : ∀ᵐ ξ ∂P, ℓ ξ ≠ ⊥ := by
    filter_upwards [ae_lt_top (measurable_neg' hℓm) hB.ne] with ξ hξ
    intro h; rw [h] at hξ; simp at hξ
  have hanti : ∀ n m, n ≤ m → ∀ ξ, f m ξ ≤ f n ξ := fun n m h ξ =>
    my_mono ℓ Ξ (by simp only [add_le_add_iff_left, Nat.cast_le]; exact h) ξ
  -- pointwise limits
  have hinf : ∀ᵐ ξ ∂P, (⨅ n, (f n ξ).toENNReal) ≤ (ℓ ξ).toENNReal := by
    filter_upwards [g0, gT, gB] with ξ h0 hT hB'
    obtain ⟨a, ha⟩ : ∃ a : ℝ, ℓ ξ = a := ⟨(ℓ ξ).toReal, (EReal.coe_toReal hT hB').symm⟩
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    obtain ⟨N, hN⟩ := my_eventually_le husc Ξ hp hγ0 (hf0 ▸ h0)
      (t := a + η) (by rw [ha, EReal.coe_lt_coe_iff]; linarith [(NNReal.coe_pos.mpr hη)])
    refine (iInf_le _ N).trans ?_
    refine (EReal.toENNReal_le_toENNReal hN).trans ?_
    rw [ha, toENNReal_real, toENNReal_real, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_add_le
  have hsup : ∀ᵐ ξ ∂P, (-ℓ ξ).toENNReal ≤ ⨆ n, (-f n ξ).toENNReal := by
    filter_upwards [g0, gT, gB] with ξ h0 hT hB'
    obtain ⟨a, ha⟩ : ∃ a : ℝ, ℓ ξ = a := ⟨(ℓ ξ).toReal, (EReal.coe_toReal hT hB').symm⟩
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    obtain ⟨N, hN⟩ := my_eventually_le husc Ξ hp hγ0 (hf0 ▸ h0)
      (t := a + η) (by rw [ha, EReal.coe_lt_coe_iff]; linarith [(NNReal.coe_pos.mpr hη)])
    have h1 : ((-(a + η) : ℝ) : EReal) ≤ -f N ξ := by
      rw [EReal.coe_neg]; exact EReal.neg_le_neg_iff.mpr hN
    have h2 := (EReal.toENNReal_le_toENNReal h1).trans (le_iSup (fun n => (-f n ξ).toENNReal) N)
    rw [toENNReal_real] at h2
    rw [ha, ← EReal.coe_neg, toENNReal_real, ← ENNReal.ofReal_coe_nnreal]
    calc ENNReal.ofReal (-a) = ENNReal.ofReal (-(a + η) + η) := by ring_nf
      _ ≤ ENNReal.ofReal (-(a + η)) + ENNReal.ofReal η := ENNReal.ofReal_add_le
      _ ≤ _ := by gcongr
  have hge : ∀ n, ∀ᵐ ξ ∂P, ℓ ξ ≤ f n ξ := fun n => gΞ.mono fun ξ hξ => my_ge ℓ hp hξ
  -- integrals
  set A : ℕ → ENNReal := fun n => ∫⁻ ξ, (f n ξ).toENNReal ∂P with hAdef
  set B : ℕ → ENNReal := fun n => ∫⁻ ξ, (-f n ξ).toENNReal ∂P with hBdef
  have hAanti : Antitone A := fun n m h => lintegral_mono fun ξ =>
    EReal.toENNReal_le_toENNReal (hanti n m h ξ)
  have hBmono : Monotone B := fun n m h => lintegral_mono fun ξ =>
    EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hanti n m h ξ))
  have hAlim : ⨅ n, A n = ∫⁻ ξ, (ℓ ξ).toENNReal ∂P := by
    refine le_antisymm ?_ (le_iInf fun n => lintegral_mono_ae ((hge n).mono fun ξ h =>
      EReal.toENNReal_le_toENNReal h))
    rw [hAdef, ← lintegral_iInf (fun n => measurable_pos (hfm n))
      (fun n m h ξ => EReal.toENNReal_le_toENNReal (hanti n m h ξ)) hA0]
    exact lintegral_mono_ae hinf
  have hBlim : ⨆ n, B n = ∫⁻ ξ, (-ℓ ξ).toENNReal ∂P := by
    refine le_antisymm (iSup_le fun n => lintegral_mono_ae ((hge n).mono fun ξ h =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr h))) ?_
    rw [hBdef, ← lintegral_iSup (fun n => measurable_neg' (hfm n))
      (fun n m h ξ => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hanti n m h ξ)))]
    exact lintegral_mono_ae hsup
  have hAfin : ∀ n, A n ≠ ⊤ := fun n => ne_top_of_le_ne_top hA0 (hAanti (Nat.zero_le n))
  have hBfin : ∀ n, B n ≠ ⊤ := fun n => ne_top_of_le_ne_top hB.ne (hBlim ▸ le_iSup B n)
  have hAt := (ENNReal.tendsto_toReal hA.ne).comp (hAlim ▸ tendsto_atTop_iInf hAanti)
  have hBt := (ENNReal.tendsto_toReal hB.ne).comp (hBlim ▸ tendsto_atTop_iSup hBmono)
  have hlim := (continuous_coe_real_ereal.tendsto _).comp (hAt.sub hBt)
  rw [risk_eq_coe P ℓ hA.ne hB.ne]
  refine ge_of_tendsto' hlim fun n => ?_
  refine (iInf₂_le (γ0 + n) (by positivity)).trans (le_of_eq ?_)
  exact risk_eq_coe P (f n) (hAfin n) (hBfin n)

/-! ## Part E: measurable selection of near-maximisers -/

/-- The single term `ℓ z − γ ‖z − ξ‖^p`. -/
noncomputable def fz {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ p : ℝ) (z ξ : E) :
    EReal :=
  ℓ z - ((γ * ‖z - ξ‖ ^ p : ℝ) : EReal)

/-- The term restricted to the open ball `‖z − ξ‖ < r` (value `⊥` outside). -/
noncomputable def Fz {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ p r : ℝ) (z ξ : E) :
    EReal :=
  ⨆ (_ : ‖z - ξ‖ < r), fz ℓ γ p z ξ

/-- The radius-`r` Moreau–Yosida regularisation. -/
noncomputable def Lr {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E)
    (γ p r : ℝ) (ξ : E) : EReal :=
  ⨆ z ∈ Ξ, Fz ℓ γ p r z ξ

lemma fz_cont {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (z : E) : Continuous (fz ℓ γ p z) :=
  continuous_sub_coe (ℓ z) (continuous_const.mul
    ((continuous_const.sub continuous_id).norm.rpow_const fun _ => Or.inr hp))

lemma Fz_lt_iff {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ p r : ℝ) (z ξ : E)
    (y : EReal) : y < Fz ℓ γ p r z ξ ↔ ‖z - ξ‖ < r ∧ y < fz ℓ γ p z ξ := by
  unfold Fz
  by_cases h : ‖z - ξ‖ < r
  · rw [iSup_pos h]; exact ⟨fun hy => ⟨h, hy⟩, fun hy => hy.2⟩
  · rw [iSup_neg h]; exact ⟨fun hy => absurd hy not_lt_bot, fun hy => absurd hy.1 h⟩

lemma Fz_lsc {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (r : ℝ) (z : E) : LowerSemicontinuous (Fz ℓ γ p r z) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  have : Fz ℓ γ p r z ⁻¹' Set.Ioi y = {ξ | ‖z - ξ‖ < r} ∩ {ξ | y < fz ℓ γ p z ξ} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact Fz_lt_iff ℓ γ p r z ξ y
  rw [this]
  exact (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const).inter
    (isOpen_lt continuous_const (fz_cont ℓ γ hp z))

lemma Lr_lsc {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) (γ : ℝ) {p : ℝ}
    (hp : 0 ≤ p) (r : ℝ) : LowerSemicontinuous (Lr ℓ Ξ γ p r) := by
  unfold Lr
  exact lowerSemicontinuous_iSup fun z => lowerSemicontinuous_iSup fun _ => Fz_lsc ℓ γ hp r z

lemma exists_countable_dense {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    (ℓ : E → EReal) (Ξ : Set E) (γ : ℝ) {p : ℝ} (hp : 0 ≤ p) (r : ℝ) :
    ∃ D : Set E, D.Countable ∧ D ⊆ Ξ ∧ ∀ ξ, ∀ z ∈ Ξ, ∀ q : ℚ,
      ((q : ℝ) : EReal) < Fz ℓ γ p r z ξ → ∃ d ∈ D, ((q : ℝ) : EReal) < Fz ℓ γ p r d ξ := by
  have key : ∀ q : ℚ, ∃ T : Set Ξ, T.Countable ∧
      ⋃ i ∈ T, Fz ℓ γ p r i ⁻¹' Set.Ioi ((q : ℝ) : EReal)
        = ⋃ i : Ξ, Fz ℓ γ p r i ⁻¹' Set.Ioi ((q : ℝ) : EReal) := fun q =>
    TopologicalSpace.isOpen_iUnion_countable _ fun i => (Fz_lsc ℓ γ hp r i).isOpen_preimage _
  choose T hT hTU using key
  refine ⟨⋃ q, Subtype.val '' T q, Set.countable_iUnion fun q => (hT q).image _, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨q, i, _, rfl⟩ := hx
    exact i.2
  · intro ξ z hz q hq
    have hmem : ξ ∈ ⋃ i : Ξ, Fz ℓ γ p r i ⁻¹' Set.Ioi ((q : ℝ) : EReal) :=
      Set.mem_iUnion.2 ⟨⟨z, hz⟩, hq⟩
    rw [← hTU q] at hmem
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_Ioi] at hmem
    obtain ⟨i, hi, hlt⟩ := hmem
    exact ⟨i, Set.mem_iUnion.2 ⟨q, i, hi, rfl⟩, hlt⟩

open Classical in
/-- Measurable selection: a measurable `T` into `Ξ`, moving each point of `Ξ` by less than `r`,
whose value beats the target `g` wherever `g` is below the radius-`r` regularisation. -/
lemma select {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    (ℓ : E → EReal) {Ξ : Set E} (hΞm : MeasurableSet Ξ) {z0 : E} (hz0 : z0 ∈ Ξ) (γ : ℝ) {p : ℝ}
    (hp : 0 < p) {r : ℝ} (hr : 0 < r) {g : E → EReal} (hg : Measurable g)
    (hgl : ∀ ξ, g ξ = ⊥ ∨ g ξ < Lr ℓ Ξ γ p r ξ) :
    ∃ T : E → E, Measurable T ∧ (∀ ξ, T ξ ∈ Ξ) ∧
      ∀ ξ ∈ Ξ, ‖T ξ - ξ‖ < r ∧ g ξ ≤ fz ℓ γ p (T ξ) ξ := by
  obtain ⟨D, hDc, hDΞ, hD⟩ := exists_countable_dense ℓ Ξ γ hp.le r
  obtain ⟨e, he⟩ := (hDc.insert z0).exists_eq_range (Set.insert_nonempty _ _)
  have heΞ : ∀ k, e k ∈ Ξ := fun k => by
    have : e k ∈ insert z0 D := he ▸ Set.mem_range_self k
    rcases this with h | h
    · exact h ▸ hz0
    · exact hDΞ h
  let cond : ℕ → E → Prop := fun k ξ => ‖e k - ξ‖ < r ∧ g ξ < fz ℓ γ p (e k) ξ
  have hcm : ∀ k, MeasurableSet {ξ | cond k ξ} := fun k =>
    (measurableSet_lt (continuous_const.sub continuous_id).norm.measurable measurable_const).inter
      (measurableSet_lt hg (fz_cont ℓ γ hp.le (e k)).measurable)
  let F0 : E → E := fun ξ => if ξ ∈ Ξ then ξ else z0
  let pr : ℕ → E → Prop := fun k ξ => cond k ξ ∨ ¬ ∃ j, cond j ξ
  have hex : ∀ ξ, ∃ k, pr k ξ := fun ξ => by
    by_cases h : ∃ j, cond j ξ
    · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr h⟩
  let f : ℕ → E → E := fun k ξ => if cond k ξ then e k else F0 ξ
  have hfm : ∀ k, Measurable (f k) := fun k =>
    Measurable.ite (hcm k) measurable_const (Measurable.ite hΞm measurable_id measurable_const)
  have hpm : ∀ k, MeasurableSet {ξ | pr k ξ} := fun k => by
    have := (hcm k).union (MeasurableSet.iUnion fun j => hcm j).compl
    convert this using 1
    ext ξ
    simp [pr]
  refine ⟨fun ξ => f (Nat.find (hex ξ)) ξ, Measurable.find hfm hpm hex, ?_, ?_⟩
  · intro ξ
    show (if cond (Nat.find (hex ξ)) ξ then e (Nat.find (hex ξ)) else F0 ξ) ∈ Ξ
    split_ifs
    · exact heΞ _
    · show (if ξ ∈ Ξ then ξ else z0) ∈ Ξ
      split_ifs with h
      · exact h
      · exact hz0
  · intro ξ hξ
    show ‖(if cond (Nat.find (hex ξ)) ξ then e (Nat.find (hex ξ)) else F0 ξ) - ξ‖ < r ∧
      g ξ ≤ fz ℓ γ p (if cond (Nat.find (hex ξ)) ξ then e (Nat.find (hex ξ)) else F0 ξ) ξ
    by_cases hc : cond (Nat.find (hex ξ)) ξ
    · rw [if_pos hc]; exact ⟨hc.1, hc.2.le⟩
    · rw [if_neg hc]
      have hF : F0 ξ = ξ := if_pos hξ
      rw [hF, sub_self, norm_zero]
      refine ⟨hr, ?_⟩
      have hnone : ¬ ∃ j, cond j ξ := by
        rcases Nat.find_spec (hex ξ) with h | h
        · exact absurd h hc
        · exact h
      rcases hgl ξ with h | h
      · rw [h]; exact bot_le
      · exfalso
        unfold Lr at h
        obtain ⟨z, hz, hzlt⟩ := lt_biSup_iff.mp h
        obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.mp hzlt
        obtain ⟨d, hd, hdlt⟩ := hD ξ z hz q hq2
        rw [Fz_lt_iff] at hdlt
        have hdr : d ∈ Set.range e := he ▸ Set.mem_insert_of_mem z0 hd
        obtain ⟨j, rfl⟩ := hdr
        exact hnone ⟨j, hdlt.1, hq1.trans hdlt.2⟩

/-! ## Part F: the primal set `S` of (cost, risk) pairs -/

lemma pos_add_le {a b : EReal} {u : ℝ} (hu : 0 ≤ u) (h : a + (u : EReal) ≤ b) :
    a.toENNReal + ENNReal.ofReal u + (-b).toENNReal ≤ b.toENNReal + (-a).toENNReal := by
  induction a using EReal.rec with
  | bot => simp
  | top =>
    rw [EReal.top_add_coe, top_le_iff] at h
    subst h; simp
  | coe x =>
    induction b using EReal.rec with
    | bot => rw [← EReal.coe_add] at h; exact absurd h (not_le.mpr (EReal.bot_lt_coe _))
    | top => simp
    | coe y =>
      have h' : x + u ≤ y := by exact_mod_cast h
      rw [← EReal.coe_neg, ← EReal.coe_neg]
      simp only [toENNReal_real]
      rw [ofReal_eq_ofReal_max x, ofReal_eq_ofReal_max y, ofReal_eq_ofReal_max (-x),
        ofReal_eq_ofReal_max (-y), ← ENNReal.ofReal_add (le_max_right _ _) hu,
        ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
        ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
      apply ENNReal.ofReal_le_ofReal
      have e1 := max_split x
      have e2 := max_split y
      linarith

lemma ereal_add_le' {a b c d e : ENNReal} (ha : a ≠ ⊤) (hc : c ≠ ⊤) (he : e ≠ ⊤)
    (h : a + e + d ≤ c + b) : ((a : EReal) - b) + e ≤ (c : EReal) - d := by
  by_cases hb : b = ⊤
  · subst hb; simp
  by_cases hd : d = ⊤
  · exfalso; subst hd
    rw [add_top, top_le_iff] at h
    simp [ENNReal.add_eq_top, hb, hc] at h
  rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb, ← EReal.coe_ennreal_toReal hc,
    ← EReal.coe_ennreal_toReal hd, ← EReal.coe_ennreal_toReal he, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  have h2 := (ENNReal.toReal_le_toReal (by simp [ha, hd, he]) (by simp [hb, hc])).mpr h
  rw [ENNReal.toReal_add (by simp [ha, he]) hd, ENNReal.toReal_add ha he,
    ENNReal.toReal_add hc hb] at h2
  linarith

/-- `f₁ + u ≤ f₂` a.e. with `u ≥ 0` gives `risk f₁ + ∫ u ≤ risk f₂`. -/
lemma risk_add_le {E : Type*} [MeasurableSpace E] (P : Measure E) {f1 f2 : E → EReal}
    (hf1 : Measurable f1) (hf2 : Measurable f2) {u : E → ℝ} (hu0 : ∀ ξ, 0 ≤ u ξ)
    (hum : Measurable u) {U : ℝ} (hU0 : 0 ≤ U) (hU : ∫⁻ ξ, ENNReal.ofReal (u ξ) ∂P = ENNReal.ofReal U)
    (hpt : ∀ᵐ ξ ∂P, f1 ξ + ((u ξ : ℝ) : EReal) ≤ f2 ξ) :
    risk P f1 + ((U : ℝ) : EReal) ≤ risk P f2 := by
  have h1 : ∫⁻ ξ, (f1 ξ).toENNReal ∂P ≤ ∫⁻ ξ, (f2 ξ).toENNReal ∂P := by
    refine lintegral_mono_ae (hpt.mono fun ξ h => EReal.toENNReal_le_toENNReal ?_)
    refine le_trans ?_ h
    have : (0 : EReal) ≤ ((u ξ : ℝ) : EReal) := EReal.coe_nonneg.mpr (hu0 ξ)
    exact le_add_of_nonneg_right this
  have h2 : ∫⁻ ξ, (f1 ξ).toENNReal ∂P + ENNReal.ofReal U + ∫⁻ ξ, (-f2 ξ).toENNReal ∂P ≤
      ∫⁻ ξ, (f2 ξ).toENNReal ∂P + ∫⁻ ξ, (-f1 ξ).toENNReal ∂P := by
    have m1 : Measurable fun ξ => (f1 ξ).toENNReal + ENNReal.ofReal (u ξ) :=
      (measurable_pos hf1).add hum.ennreal_ofReal
    have m0 : Measurable fun ξ => (f1 ξ).toENNReal := measurable_pos hf1
    have m2 : Measurable fun ξ => (f2 ξ).toENNReal := measurable_pos hf2
    rw [← hU, ← lintegral_add_left m0, ← lintegral_add_left m1, ← lintegral_add_left m2]
    exact lintegral_mono_ae (hpt.mono fun ξ h => pos_add_le (hu0 ξ) h)
  unfold risk
  by_cases hB : ∫⁻ ξ, (f2 ξ).toENNReal ∂P = ⊤
  · rw [if_pos hB]; exact le_top
  rw [if_neg hB, if_neg (ne_top_of_le_ne_top hB h1)]
  have := ereal_add_le' (ne_top_of_le_ne_top hB h1) hB ENNReal.ofReal_ne_top h2
  rwa [coe_ofReal_of_nonneg hU0] at this

/-- The primal set: `(C, R)` with `C ≥ 0`, realised by some `Q` supported on `Ξ` and a coupling
of `Q` and `P` of cost at most `C`, with `R ≤ risk Q ℓ`. -/
def Sset {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (P : Measure E) (Ξ : Set E)
    (ℓ : E → EReal) (p : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ ∃ Q : Measure E, ∃ π ∈ couplings Q P, Q Ξᶜ = 0 ∧
    ∫⁻ y, ENNReal.ofReal (‖y.1 - y.2‖ ^ p) ∂π ≤ ENNReal.ofReal x.1 ∧ (x.2 : EReal) ≤ risk Q ℓ}

lemma add_coe_le_of_le_sub {a b : EReal} {r : ℝ} (h : a ≤ b - (r : EReal)) : a + (r : EReal) ≤ b := by
  induction b using EReal.rec with
  | bot =>
    have : a = ⊥ := by simpa using h
    subst this; simp
  | top => exact le_top
  | coe y =>
    induction a using EReal.rec with
    | bot => simp
    | top => rw [← EReal.coe_sub] at h; exact absurd h (not_le.mpr (EReal.coe_lt_top _))
    | coe x =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith

/-- A selected transport map gives an element of `S` with `R − γ C = M`. -/
lemma map_mem_S {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P] {Ξ : Set E}
    (hΞm : MeasurableSet Ξ) (hPΞ : P Ξᶜ = 0) {ℓ : E → EReal} (hℓ : Measurable ℓ) {γ p r : ℝ}
    (hγ : 0 ≤ γ) (hp : 0 < p) {T : E → E} (hT : Measurable T) (hTΞ : ∀ ξ, T ξ ∈ Ξ)
    {g : E → EReal} (hg : Measurable g)
    (hTg : ∀ ξ ∈ Ξ, ‖T ξ - ξ‖ < r ∧ g ξ ≤ fz ℓ γ p (T ξ) ξ) {M : ℝ} (hM : (M : EReal) ≤ risk P g) :
    ∃ C : ℝ, (C, M + γ * C) ∈ Sset P Ξ ℓ p := by
  have hTi : Measurable fun ξ => (T ξ, ξ) := hT.prodMk measurable_id
  have hcm : Measurable fun x : E × E => ENNReal.ofReal (‖x.1 - x.2‖ ^ p) :=
    ((continuous_fst.sub continuous_snd).norm.rpow_const fun _ => Or.inr hp.le).measurable.ennreal_ofReal
  have hcT : Measurable fun ξ => ‖T ξ - ξ‖ ^ p :=
    ((hT.sub measurable_id).norm).pow_const p
  have gΞ : ∀ᵐ ξ ∂P, ξ ∈ Ξ := ae_iff.2 (show P {a | ¬ a ∈ Ξ} = 0 from hPΞ)
  set Cost := ∫⁻ ξ, ENNReal.ofReal (‖T ξ - ξ‖ ^ p) ∂P with hCost
  have hCfin : Cost ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := r ^ p)) ?_
    calc Cost ≤ ∫⁻ _, ENNReal.ofReal (r ^ p) ∂P := lintegral_mono_ae (gΞ.mono fun ξ hξ =>
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hTg ξ hξ).1.le hp.le))
      _ = ENNReal.ofReal (r ^ p) := by simp
  refine ⟨Cost.toReal, ENNReal.toReal_nonneg, P.map T, P.map fun ξ => (T ξ, ξ), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map hTi.aemeasurable
  · rw [Measure.map_map measurable_fst hTi]; rfl
  · rw [Measure.map_map measurable_snd hTi]; exact Measure.map_id
  · rw [Measure.map_apply hT hΞm.compl]
    have : T ⁻¹' Ξᶜ = ∅ := by ext ξ; simp [hTΞ ξ]
    rw [this, measure_empty]
  · rw [lintegral_map hcm hTi, ENNReal.ofReal_toReal hCfin]
  · -- risk
    have hrisk : risk (P.map T) ℓ = risk P (fun ξ => ℓ (T ξ)) := by
      unfold risk
      rw [lintegral_map (measurable_pos hℓ) hT, lintegral_map (measurable_neg' hℓ) hT]
    rw [hrisk]
    have hU : ∫⁻ ξ, ENNReal.ofReal (γ * ‖T ξ - ξ‖ ^ p) ∂P = ENNReal.ofReal (γ * Cost.toReal) := by
      simp_rw [ENNReal.ofReal_mul hγ]
      rw [lintegral_const_mul _ hcT.ennreal_ofReal, ENNReal.ofReal_toReal hCfin]
    have key := risk_add_le P hg (hℓ.comp hT) (u := fun ξ => γ * ‖T ξ - ξ‖ ^ p)
      (fun ξ => by positivity) (measurable_const.mul hcT) (by positivity) hU
      (gΞ.mono fun ξ hξ => add_coe_le_of_le_sub (hTg ξ hξ).2)
    refine le_trans ?_ key
    rw [EReal.coe_add]
    gcongr

lemma risk_mix {E : Type*} [MeasurableSpace E] (Q1 Q2 : Measure E) (ℓ : E → EReal) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {R1 R2 : ℝ} (h1 : (R1 : EReal) ≤ risk Q1 ℓ)
    (h2 : (R2 : EReal) ≤ risk Q2 ℓ) :
    ((a * R1 + b * R2 : ℝ) : EReal) ≤ risk (ENNReal.ofReal a • Q1 + ENNReal.ofReal b • Q2) ℓ := by
  have eA : ∫⁻ ξ, (ℓ ξ).toENNReal ∂(ENNReal.ofReal a • Q1 + ENNReal.ofReal b • Q2)
      = ENNReal.ofReal a * ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q1 + ENNReal.ofReal b * ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q2 := by
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
      smul_eq_mul]
  have eB : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂(ENNReal.ofReal a • Q1 + ENNReal.ofReal b • Q2)
      = ENNReal.ofReal a * ∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q1 + ENNReal.ofReal b * ∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q2 := by
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
      smul_eq_mul]
  by_cases hA : ∫⁻ ξ, (ℓ ξ).toENNReal ∂(ENNReal.ofReal a • Q1 + ENNReal.ofReal b • Q2) = ⊤
  · unfold risk; rw [if_pos hA]; exact le_top
  have ha' : ENNReal.ofReal a ≠ 0 := by simpa using ha
  have hb' : ENNReal.ofReal b ≠ 0 := by simpa using hb
  rw [eA] at hA
  have hA1 : ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q1 ≠ ⊤ := fun h => hA (by simp [h, ha'])
  have hA2 : ∫⁻ ξ, (ℓ ξ).toENNReal ∂Q2 ≠ ⊤ := fun h => hA (by simp [h, hb'])
  have hB1 : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q1 ≠ ⊤ := by
    intro h; unfold risk at h1; rw [if_neg hA1, h] at h1; simp at h1
  have hB2 : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂Q2 ≠ ⊤ := by
    intro h; unfold risk at h2; rw [if_neg hA2, h] at h2; simp at h2
  rw [risk_eq_coe Q1 ℓ hA1 hB1, EReal.coe_le_coe_iff] at h1
  rw [risk_eq_coe Q2 ℓ hA2 hB2, EReal.coe_le_coe_iff] at h2
  have hBm : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂(ENNReal.ofReal a • Q1 + ENNReal.ofReal b • Q2) ≠ ⊤ := by
    rw [eB]; exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB1,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB2⟩
  have hAm : ∫⁻ ξ, (ℓ ξ).toENNReal ∂(ENNReal.ofReal a • Q1 + ENNReal.ofReal b • Q2) ≠ ⊤ := by
    rw [eA]; exact hA
  rw [risk_eq_coe _ ℓ hAm hBm, EReal.coe_le_coe_iff, eA, eB,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA1)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA2),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB1)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB2),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hb.le]
  nlinarith

lemma mix_mem_S {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (P : Measure E)
    (Ξ : Set E) (ℓ : E → EReal) (p : ℝ) {x y : ℝ × ℝ} (hx : x ∈ Sset P Ξ ℓ p)
    (hy : y ∈ Sset P Ξ ℓ p) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (a * x.1 + (1 - a) * y.1, a * x.2 + (1 - a) * y.2) ∈ Sset P Ξ ℓ p := by
  obtain ⟨hx0, Q1, π1, ⟨hπ1, h11, h12⟩, hQ1, hc1, hr1⟩ := hx
  obtain ⟨hy0, Q2, π2, ⟨hπ2, h21, h22⟩, hQ2, hc2, hr2⟩ := hy
  have hb : 0 < 1 - a := by linarith
  have hsum : ENNReal.ofReal a + ENNReal.ofReal (1 - a) = 1 := by
    rw [← ENNReal.ofReal_add ha.le hb.le]; simp
  refine ⟨by positivity, ENNReal.ofReal a • Q1 + ENNReal.ofReal (1 - a) • Q2,
    ENNReal.ofReal a • π1 + ENNReal.ofReal (1 - a) • π2, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · constructor
    simp [Measure.add_apply, Measure.smul_apply, measure_univ, hsum]
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, h11, h21]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, h12, h22,
      ← add_smul, hsum, one_smul]
  · simp [Measure.add_apply, Measure.smul_apply, hQ1, hQ2]
  · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
    calc ENNReal.ofReal a * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π1
          + ENNReal.ofReal (1 - a) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π2
        ≤ ENNReal.ofReal a * ENNReal.ofReal x.1 + ENNReal.ofReal (1 - a) * ENNReal.ofReal y.1 := by
          gcongr
      _ = ENNReal.ofReal (a * x.1 + (1 - a) * y.1) := by
          rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul hb.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  · exact risk_mix Q1 Q2 ℓ ha hb hr1 hr2

lemma S_le_wc {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {P : Measure E}
    {Ξ : Set E} {ℓ : E → EReal} {p ε : ℝ} (hp : 0 < p) (hε : 0 ≤ ε) {x : ℝ × ℝ}
    (hx : x ∈ Sset P Ξ ℓ p) (hC : x.1 ≤ ε ^ p) : (x.2 : EReal) ≤ worstCaseRisk ε p P Ξ ℓ := by
  obtain ⟨hx0, Q, π, ⟨hπ, h1, h2⟩, hQ, hc, hr⟩ := hx
  have hQball : Q ∈ ambiguityBall ε p P Ξ := by
    refine ⟨?_, hQ, ?_⟩
    · rw [← h1]; exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    · unfold wasserstein
      have hle : (⨅ π ∈ couplings Q P, ∫⁻ y, ENNReal.ofReal (‖y.1 - y.2‖ ^ p) ∂π)
          ≤ ENNReal.ofReal (ε ^ p) :=
        (iInf₂_le π ⟨hπ, h1, h2⟩).trans (hc.trans (ENNReal.ofReal_le_ofReal hC))
      calc (⨅ π ∈ couplings Q P, ∫⁻ y, ENNReal.ofReal (‖y.1 - y.2‖ ^ p) ∂π) ^ (1 / p)
          ≤ ENNReal.ofReal (ε ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hle (by positivity)
        _ = ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
            Real.rpow_rpow_inv hε hp.ne']
  exact hr.trans (le_iSup₂ (f := fun Q _ => risk Q ℓ) Q hQball)

lemma zero_mem_S {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] {Ξ : Set E} (hPΞ : P Ξᶜ = 0) (ℓ : E → EReal) {p : ℝ} (hp : 0 < p)
    {R : ℝ} (hR : (R : EReal) ≤ risk P ℓ) : ((0 : ℝ), R) ∈ Sset P Ξ ℓ p := by
  have hd : Measurable fun x : E => (x, x) := measurable_id.prodMk measurable_id
  refine ⟨le_rfl, P, P.map fun x : E => (x, x), ⟨?_, ?_, ?_⟩, hPΞ, ?_, hR⟩
  · exact Measure.isProbabilityMeasure_map hd.aemeasurable
  · rw [Measure.map_map measurable_fst hd]; exact Measure.map_id
  · rw [Measure.map_map measurable_snd hd]; exact Measure.map_id
  · refine (lintegral_map_le _ _).trans ?_
    simp [Real.zero_rpow hp.ne']

/-! ## Part G: one-constraint Lagrange duality on a convex set of (cost, value) pairs -/

lemma lagrange {S : Set (ℝ × ℝ)}
    (hmix : ∀ x ∈ S, ∀ y ∈ S, ∀ a : ℝ, 0 < a → a < 1 →
      (a * x.1 + (1 - a) * y.1, a * x.2 + (1 - a) * y.2) ∈ S)
    {ρ L R0 : ℝ} (hρ : 0 < ρ) (h0 : ((0 : ℝ), R0) ∈ S) (hL : ∀ x ∈ S, x.1 ≤ ρ → x.2 ≤ L) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ x ∈ S, x.2 - γ * x.1 ≤ L - γ * ρ := by
  set A : Set ℝ := {s | ∃ x ∈ S, ρ < x.1 ∧ s = (x.2 - L) / (x.1 - ρ)} with hA
  have hbdd : BddAbove A := by
    refine ⟨(L - R0) / ρ, ?_⟩
    rintro s ⟨x, hx, hxρ, rfl⟩
    have hC : 0 < x.1 := hρ.trans hxρ
    have hCne := hC.ne'
    have hm := hL _ (hmix x hx _ h0 (ρ / x.1) (div_pos hρ hC) ((div_lt_one hC).2 hxρ))
      (le_of_eq (by dsimp only; field_simp; ring))
    dsimp only at hm
    have haC : ρ / x.1 * x.1 = ρ := by field_simp
    rw [div_le_div_iff₀ (by linarith) hρ]
    have h3 := mul_le_mul_of_nonneg_left hm hC.le
    have e : x.1 * (ρ / x.1 * x.2 + (1 - ρ / x.1) * R0) = ρ * x.2 + (x.1 - ρ) * R0 := by
      rw [show x.1 * (ρ / x.1 * x.2 + (1 - ρ / x.1) * R0)
        = ρ / x.1 * x.1 * x.2 + (x.1 - ρ / x.1 * x.1) * R0 by ring, haC]
    nlinarith [h3, e]
  refine ⟨max 0 (sSup A), le_max_left _ _, fun x hx => ?_⟩
  rcases lt_or_ge ρ x.1 with hxρ | hxρ
  · have hs : (x.2 - L) / (x.1 - ρ) ≤ max 0 (sSup A) :=
      (le_csSup hbdd ⟨x, hx, hxρ, rfl⟩).trans (le_max_right _ _)
    rw [div_le_iff₀ (by linarith)] at hs
    nlinarith [hs]
  · have hR : x.2 ≤ L := hL x hx hxρ
    rcases eq_or_lt_of_le hxρ with heq | hlt
    · rw [heq]; linarith
    · have hγ : max 0 (sSup A) ≤ (L - x.2) / (ρ - x.1) := by
        refine max_le (div_nonneg (by linarith) (by linarith)) ?_
        rcases A.eq_empty_or_nonempty with hAe | hAne
        · rw [hAe, Real.sSup_empty]; exact div_nonneg (by linarith) (by linarith)
        · refine csSup_le hAne ?_
          rintro s ⟨y, hy, hyρ, rfl⟩
          have hyx : 0 < y.1 - x.1 := by linarith
          have hyxne := hyx.ne'
          set a := (y.1 - ρ) / (y.1 - x.1) with ha
          have ha0 : 0 < a := div_pos (by linarith) hyx
          have ha1 : a < 1 := (div_lt_one hyx).2 (by linarith)
          have ha' : a * (y.1 - x.1) = y.1 - ρ := by rw [ha]; field_simp
          have hm := hL _ (hmix x hx y hy a ha0 ha1) (le_of_eq (by
            dsimp only
            have : a * x.1 + (1 - a) * y.1 = y.1 - a * (y.1 - x.1) := by ring
            rw [this, ha']; ring))
          dsimp only at hm
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          have h3 := mul_le_mul_of_nonneg_left hm hyx.le
          have e : (y.1 - x.1) * (a * x.2 + (1 - a) * y.2) = (y.1 - ρ) * x.2 + (ρ - x.1) * y.2 := by
            rw [show (y.1 - x.1) * (a * x.2 + (1 - a) * y.2)
              = a * (y.1 - x.1) * x.2 + ((y.1 - x.1) - a * (y.1 - x.1)) * y.2 by ring, ha']
            ring
          nlinarith [h3, e]
      rw [le_div_iff₀ (by linarith)] at hγ
      nlinarith [hγ]

/-! ## Part H: the approximating targets `g n ↑ ℓ_γ` -/

/-- Truncated, radius-limited targets strictly below `Lr` (or `⊥`). -/
noncomputable def gseq {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E)
    (γ p : ℝ) (n : ℕ) (ξ : E) : EReal :=
  min (Lr ℓ Ξ γ p ((n : ℝ) + 1) ξ) ((((n : ℝ) + 1 : ℝ)) : EReal) - ((1 / ((n : ℝ) + 2) : ℝ) : EReal)

lemma Lr_mono {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) (γ p : ℝ)
    {r r' : ℝ} (h : r ≤ r') (ξ : E) : Lr ℓ Ξ γ p r ξ ≤ Lr ℓ Ξ γ p r' ξ := by
  unfold Lr
  refine iSup₂_mono fun z _ => ?_
  unfold Fz
  exact iSup_le fun hz => le_iSup_of_le (hz.trans_le h) le_rfl

lemma Lr_ge {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) (γ : ℝ) {p : ℝ}
    (hp : 0 < p) {r : ℝ} (hr : 0 < r) {ξ : E} (hξ : ξ ∈ Ξ) : ℓ ξ ≤ Lr ℓ Ξ γ p r ξ := by
  unfold Lr
  refine le_iSup₂_of_le ξ hξ ?_
  unfold Fz
  rw [iSup_pos (by simpa using hr)]
  unfold fz
  simp [Real.zero_rpow hp.ne']

lemma gseq_mono {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) (γ p : ℝ)
    (ξ : E) : Monotone fun n => gseq ℓ Ξ γ p n ξ := by
  intro n m h
  have hnm : (n : ℝ) ≤ m := Nat.cast_le.mpr h
  unfold gseq
  refine EReal.sub_le_sub (min_le_min (Lr_mono ℓ Ξ γ p (by linarith) ξ)
    (EReal.coe_le_coe_iff.mpr (by linarith))) ?_
  rw [EReal.coe_le_coe_iff]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma gseq_meas {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (ℓ : E → EReal) (Ξ : Set E) (γ : ℝ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    Measurable (gseq ℓ Ξ γ p n) := by
  have hmon : Monotone fun y : EReal =>
      min y ((((n : ℝ) + 1 : ℝ)) : EReal) - ((1 / ((n : ℝ) + 2) : ℝ) : EReal) :=
    fun a b h => EReal.sub_le_sub (min_le_min h le_rfl) le_rfl
  have e : gseq ℓ Ξ γ p n = (fun y : EReal =>
      min y ((((n : ℝ) + 1 : ℝ)) : EReal) - ((1 / ((n : ℝ) + 2) : ℝ) : EReal))
        ∘ Lr ℓ Ξ γ p ((n : ℝ) + 1) := rfl
  rw [e]
  exact hmon.measurable.comp (Lr_lsc ℓ Ξ γ hp _).measurable

lemma gseq_hgl {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) (γ p : ℝ)
    (n : ℕ) (ξ : E) :
    gseq ℓ Ξ γ p n ξ = ⊥ ∨ gseq ℓ Ξ γ p n ξ < Lr ℓ Ξ γ p ((n : ℝ) + 1) ξ := by
  unfold gseq
  generalize Lr ℓ Ξ γ p ((n : ℝ) + 1) ξ = L
  have hc : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  induction L using EReal.rec with
  | bot => left; simp
  | top =>
    right
    rw [min_eq_right le_top, ← EReal.coe_sub]
    exact EReal.coe_lt_top _
  | coe a =>
    right
    refine lt_of_le_of_lt (EReal.sub_le_sub (min_le_left _ _) le_rfl) ?_
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
    linarith

lemma my_le_gsup {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (Ξ : Set E) (γ p : ℝ)
    (ξ : E) : moreauYosida ℓ Ξ γ p ξ ≤ ⨆ n : ℕ, gseq ℓ Ξ γ p n ξ := by
  unfold moreauYosida
  refine iSup₂_le fun z hz => ?_
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨t, hct, htf⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  obtain ⟨s, hcs, hst⟩ := EReal.lt_iff_exists_real_btwn.mp hct
  have hst' : s < t := by exact_mod_cast hst
  have htf' : (t : EReal) < fz ℓ γ p z ξ := htf
  obtain ⟨n, hn⟩ := exists_nat_gt (max (‖z - ξ‖) (max t (1 / (t - s))))
  have hn1 : ‖z - ξ‖ < (n : ℝ) + 1 := by
    have := le_max_left (‖z - ξ‖) (max t (1 / (t - s))); linarith
  have hn2 : t < (n : ℝ) + 1 := by
    have := le_max_left t (1 / (t - s))
    have := le_max_right (‖z - ξ‖) (max t (1 / (t - s))); linarith
  have hn3 : 1 / (t - s) < (n : ℝ) + 2 := by
    have := le_max_right t (1 / (t - s))
    have := le_max_right (‖z - ξ‖) (max t (1 / (t - s))); linarith
  have hn4 : 1 / ((n : ℝ) + 2) < t - s := (one_div_lt (sub_pos.2 hst') (by positivity)).mp hn3
  refine lt_of_lt_of_le hcs (le_iSup_of_le n ?_)
  have hFz : Fz ℓ γ p ((n : ℝ) + 1) z ξ = fz ℓ γ p z ξ := by unfold Fz; exact iSup_pos hn1
  have h1 : (t : EReal) ≤ Lr ℓ Ξ γ p ((n : ℝ) + 1) ξ := by
    refine htf'.le.trans ?_
    rw [← hFz]
    unfold Lr
    exact le_iSup₂ (f := fun z _ => Fz ℓ γ p ((n : ℝ) + 1) z ξ) z hz
  have h2 : (t : EReal) ≤ min (Lr ℓ Ξ γ p ((n : ℝ) + 1) ξ) ((((n : ℝ) + 1 : ℝ)) : EReal) :=
    le_min h1 (EReal.coe_le_coe_iff.mpr hn2.le)
  unfold gseq
  calc (s : EReal) ≤ ((t - 1 / ((n : ℝ) + 2) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
    _ = (t : EReal) - ((1 / ((n : ℝ) + 2) : ℝ) : EReal) := EReal.coe_sub _ _
    _ ≤ _ := EReal.sub_le_sub h2 le_rfl

lemma negpart_le_add {a b : EReal} {r : ℝ} (hr : 0 ≤ r) (h : a ≤ b + (r : EReal)) :
    (-b).toENNReal ≤ (-a).toENNReal + ENNReal.ofReal r := by
  induction b using EReal.rec with
  | bot =>
    have : a = ⊥ := le_bot_iff.mp (by simpa using h)
    subst this; simp
  | top => simp
  | coe y =>
    induction a using EReal.rec with
    | bot => simp
    | top =>
      exfalso
      rw [← EReal.coe_add] at h
      exact absurd h (not_le.mpr (EReal.coe_lt_top _))
    | coe x =>
      have h' : x ≤ y + r := by exact_mod_cast h
      rw [← EReal.coe_neg, ← EReal.coe_neg, toENNReal_real, toENNReal_real]
      calc ENNReal.ofReal (-y) ≤ ENNReal.ofReal (-x + r) := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ _ := ENNReal.ofReal_add_le

lemma negpart_min_one (a : EReal) : (-min a 1).toENNReal ≤ (-a).toENNReal := by
  rcases le_total a 1 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, EReal.toENNReal_of_nonpos (by rw [← EReal.coe_one, ← EReal.coe_neg]; exact EReal.coe_nonpos.mpr (by norm_num))]
    exact zero_le

lemma risk_eq_sub {E : Type*} [MeasurableSpace E] (P : Measure E) (f : E → EReal)
    (hB : ∫⁻ ξ, (-f ξ).toENNReal ∂P ≠ ⊤) :
    risk P f = ((∫⁻ ξ, (f ξ).toENNReal ∂P : ENNReal) : EReal)
      - ((∫⁻ ξ, (-f ξ).toENNReal ∂P : ENNReal) : EReal) := by
  unfold risk
  split_ifs with h
  · rw [h, ← EReal.coe_ennreal_toReal hB]; simp
  · rfl

open Filter in
lemma target_seq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] {Ξ : Set E} (hPΞ : P Ξᶜ = 0) {ℓ : E → EReal}
    (hℓ : Measurable ℓ) (hB : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂P < ⊤) {γ p : ℝ} (hp : 0 < p) {M : ℝ}
    (hM : (M : EReal) < risk P (moreauYosida ℓ Ξ γ p)) :
    ∃ n : ℕ, (M : EReal) ≤ risk P (gseq ℓ Ξ γ p n) := by
  set g : ℕ → E → EReal := fun n => gseq ℓ Ξ γ p n with hgdef
  set f : E → EReal := moreauYosida ℓ Ξ γ p with hfdef
  have hgm : ∀ n, Measurable (g n) := fun n => gseq_meas ℓ Ξ γ hp.le n
  have gΞ : ∀ᵐ ξ ∂P, ξ ∈ Ξ := ae_iff.2 (show P {a | ¬ a ∈ Ξ} = 0 from hPΞ)
  set s : E → EReal := fun ξ => ⨆ n, g n ξ with hsdef
  have hfs : ∀ ξ, f ξ ≤ s ξ := fun ξ => my_le_gsup ℓ Ξ γ p ξ
  have hmono : ∀ ξ, Monotone fun n => g n ξ := fun ξ => gseq_mono ℓ Ξ γ p ξ
  have htl : ∀ ξ, Tendsto (fun n => g n ξ) atTop (nhds (s ξ)) :=
    fun ξ => tendsto_atTop_iSup (hmono ξ)
  have hApt : ∀ ξ, ⨆ n, (g n ξ).toENNReal = (s ξ).toENNReal := fun ξ =>
    tendsto_nhds_unique (tendsto_atTop_iSup fun n m h => EReal.toENNReal_le_toENNReal (hmono ξ h))
      ((EReal.continuous_toENNReal.tendsto _).comp (htl ξ))
  have hBpt : ∀ ξ, ⨅ n, (-g n ξ).toENNReal = (-s ξ).toENNReal := fun ξ =>
    tendsto_nhds_unique (tendsto_atTop_iInf fun n m h =>
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hmono ξ h)))
      (((EReal.continuous_toENNReal.comp continuous_neg).tendsto _).comp (htl ξ))
  -- the negative part of `g 0` is integrable
  have hpt : ∀ ξ ∈ Ξ, (-g 0 ξ).toENNReal ≤ (-ℓ ξ).toENNReal + 1 := by
    intro ξ hξ
    have hc0 : (0 : ℝ) ≤ 1 / (((0 : ℕ) : ℝ) + 2) := by positivity
    have hc1 : 1 / (((0 : ℕ) : ℝ) + 2) ≤ 1 := by norm_num
    have hmin : min (ℓ ξ) 1 ≤ g 0 ξ + ((1 / (((0 : ℕ) : ℝ) + 2) : ℝ) : EReal) := by
      calc min (ℓ ξ) 1 ≤ min (Lr ℓ Ξ γ p (((0 : ℕ) : ℝ) + 1) ξ) ((((0 : ℕ) : ℝ) + 1 : ℝ) : EReal) :=
            min_le_min (Lr_ge ℓ Ξ γ hp (by norm_num) hξ) (by norm_num)
        _ ≤ _ := le_sub_add _ _
    calc (-g 0 ξ).toENNReal ≤ (-min (ℓ ξ) 1).toENNReal + ENNReal.ofReal (1 / (((0 : ℕ) : ℝ) + 2)) :=
          negpart_le_add hc0 hmin
      _ ≤ (-ℓ ξ).toENNReal + 1 := add_le_add (negpart_min_one _) (ENNReal.ofReal_le_one.mpr hc1)
  have hB0 : ∫⁻ ξ, (-g 0 ξ).toENNReal ∂P ≠ ⊤ := by
    have : ∫⁻ ξ, (-g 0 ξ).toENNReal ∂P ≤ ∫⁻ ξ, (-ℓ ξ).toENNReal ∂P + 1 := by
      calc ∫⁻ ξ, (-g 0 ξ).toENNReal ∂P ≤ ∫⁻ ξ, ((-ℓ ξ).toENNReal + 1) ∂P :=
            lintegral_mono_ae (gΞ.mono fun ξ hξ => hpt ξ hξ)
        _ = ∫⁻ ξ, (-ℓ ξ).toENNReal ∂P + 1 := by
            rw [lintegral_add_right _ measurable_const]; simp
    exact (lt_of_le_of_lt this (ENNReal.add_lt_top.mpr ⟨hB, ENNReal.one_lt_top⟩)).ne
  have hBf : ∫⁻ ξ, (-f ξ).toENNReal ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top hB.ne (lintegral_mono_ae (gΞ.mono fun ξ hξ => ?_))
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (my_ge ℓ hp hξ))
  set A : ℕ → ENNReal := fun n => ∫⁻ ξ, (g n ξ).toENNReal ∂P with hAdef
  set B : ℕ → ENNReal := fun n => ∫⁻ ξ, (-g n ξ).toENNReal ∂P with hBdef
  have hAmono : Monotone A := fun n m h => lintegral_mono fun ξ =>
    EReal.toENNReal_le_toENNReal (hmono ξ h)
  have hBanti : Antitone B := fun n m h => lintegral_mono fun ξ =>
    EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hmono ξ h))
  have hAsup : ⨆ n, A n = ∫⁻ ξ, (s ξ).toENNReal ∂P := by
    rw [hAdef, ← lintegral_iSup (fun n => measurable_pos (hgm n))
      (fun n m h ξ => EReal.toENNReal_le_toENNReal (hmono ξ h))]
    exact lintegral_congr fun ξ => hApt ξ
  have hBinf : ⨅ n, B n = ∫⁻ ξ, (-s ξ).toENNReal ∂P := by
    rw [hBdef, ← lintegral_iInf (fun n => measurable_neg' (hgm n))
      (fun n m h ξ => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hmono ξ h))) hB0]
    exact lintegral_congr fun ξ => hBpt ξ
  have hAge : ∫⁻ ξ, (f ξ).toENNReal ∂P ≤ ⨆ n, A n := by
    rw [hAsup]; exact lintegral_mono fun ξ => EReal.toENNReal_le_toENNReal (hfs ξ)
  have hBle : ⨅ n, B n ≤ ∫⁻ ξ, (-f ξ).toENNReal ∂P := by
    rw [hBinf]
    exact lintegral_mono fun ξ => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hfs ξ))
  have hBifin : (⨅ n, B n) ≠ ⊤ := ne_top_of_le_ne_top hB0 (iInf_le B 0)
  have hBn : ∀ n, B n ≠ ⊤ := fun n => ne_top_of_le_ne_top hB0 (hBanti (Nat.zero_le n))
  have hAt : Tendsto (fun n => ((A n : ENNReal) : EReal)) atTop
      (nhds ((⨆ n, A n : ENNReal) : EReal)) :=
    (continuous_coe_ennreal_ereal.tendsto _).comp (tendsto_atTop_iSup hAmono)
  have hBt : Tendsto (fun n => -((B n : ENNReal) : EReal)) atTop
      (nhds (-((⨅ n, B n : ENNReal) : EReal))) :=
    ((continuous_neg.comp continuous_coe_ennreal_ereal).tendsto _).comp (tendsto_atTop_iInf hBanti)
  have hc1 : ((⨆ n, A n : ENNReal) : EReal) ≠ ⊥ := EReal.coe_ennreal_ne_bot _
  have hc2 : -((⨅ n, B n : ENNReal) : EReal) ≠ ⊥ := by
    rw [ne_eq, EReal.neg_eq_bot_iff]
    exact fun h => hBifin (EReal.coe_ennreal_eq_top_iff.mp h)
  have hlim : Tendsto (fun n => ((A n : ENNReal) : EReal) + -((B n : ENNReal) : EReal)) atTop
      (nhds (((⨆ n, A n : ENNReal) : EReal) + -((⨅ n, B n : ENNReal) : EReal))) :=
    (EReal.continuousAt_add (p := (((⨆ n, A n : ENNReal) : EReal), -((⨅ n, B n : ENNReal) : EReal)))
      (Or.inr hc2) (Or.inl hc1)).tendsto.comp (hAt.prodMk_nhds hBt)
  have hrisk : risk P f ≤ ((⨆ n, A n : ENNReal) : EReal) + -((⨅ n, B n : ENNReal) : EReal) := by
    rw [risk_eq_sub P f hBf, sub_eq_add_neg]
    exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hAge)
      (EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hBle))
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (hM.trans_le hrisk))).exists
  refine ⟨n, ?_⟩
  have e : risk P (gseq ℓ Ξ γ p n) = ((A n : ENNReal) : EReal) + -((B n : ENNReal) : EReal) := by
    rw [risk_eq_sub P (g n) (hBn n), sub_eq_add_neg]
  rw [e]; exact hn.le

/-! ## Part I: assembly for `ε > 0` -/

lemma dual_le_wc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {p : ℝ} (hp : 1 ≤ p) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0)
    (ℓ : E → EReal) (husc : UpperSemicontinuous ℓ) (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂P < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal)
      ≤ worstCaseRisk ε p P Ξ ℓ := by
  have hp0 : 0 < p := by linarith
  have hℓm : Measurable ℓ := husc.measurable
  set W := worstCaseRisk ε p P Ξ ℓ with hWdef
  by_cases hW : W = ⊤
  · rw [hW]; exact le_top
  have hA : ∫⁻ ξ, (ℓ ξ).toENNReal ∂P < ⊤ := (lintegral_mono fun ξ => pos_le_abs _).trans_lt hint
  have hB : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂P < ⊤ :=
    (lintegral_mono fun ξ => negpart_le_abs _).trans_lt hint
  set R0 : ℝ := (∫⁻ ξ, (ℓ ξ).toENNReal ∂P).toReal - (∫⁻ ξ, (-ℓ ξ).toENNReal ∂P).toReal
  have hR0 : (R0 : EReal) = risk P ℓ := (risk_eq_coe P ℓ hA.ne hB.ne).symm
  have hRW : risk P ℓ ≤ W := le_iSup₂ (f := fun Q _ => risk Q ℓ) P (self_mem_ball hp0 hε.le P hPΞ)
  have hWbot : W ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot R0) (hR0 ▸ hRW)
  set L : ℝ := W.toReal
  have hLW : (L : EReal) = W := EReal.coe_toReal hW hWbot
  set ρ : ℝ := ε ^ p with hρdef
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hε p
  have hL : ∀ x ∈ Sset P Ξ ℓ p, x.1 ≤ ρ → x.2 ≤ L := fun x hx hC => by
    have h := S_le_wc hp0 hε.le hx hC
    rw [← hWdef, ← hLW] at h
    exact_mod_cast h
  obtain ⟨γ, hγ, hlag⟩ := lagrange (fun x hx y hy a ha ha1 => mix_mem_S P Ξ ℓ p hx hy ha ha1) hρ
    (zero_mem_S P hPΞ ℓ hp0 hR0.le) hL
  have hne : Ξ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.compl_empty, measure_univ] at hPΞ
    exact one_ne_zero hPΞ
  obtain ⟨z0, hz0⟩ := hne
  have hclaim : risk P (moreauYosida ℓ Ξ γ p) ≤ ((L - γ * ρ : ℝ) : EReal) := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨M, hM1, hM2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    obtain ⟨n, hn⟩ := target_seq P hPΞ hℓm hB hp0 hM2
    obtain ⟨T, hTm, hTΞ, hTg⟩ := select ℓ hΞ.measurableSet hz0 γ hp0
      (r := (n : ℝ) + 1) (by positivity) (gseq_meas ℓ Ξ γ hp0.le n) (gseq_hgl ℓ Ξ γ p n)
    obtain ⟨C, hC⟩ := map_mem_S P hΞ.measurableSet hPΞ hℓm hγ hp0 hTm hTΞ
      (gseq_meas ℓ Ξ γ hp0.le n) hTg hn
    have h := hlag _ hC
    dsimp only at h
    have hM1' : L - γ * ρ < M := by exact_mod_cast hM1
    linarith
  calc ⨅ (γ' : ℝ) (_ : 0 ≤ γ'), risk P (moreauYosida ℓ Ξ γ' p) + ((γ' * ε ^ p : ℝ) : EReal)
      ≤ risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal) := iInf₂_le γ hγ
    _ ≤ ((L - γ * ρ : ℝ) : EReal) + ((γ * ρ : ℝ) : EReal) := by gcongr
    _ = (L : EReal) := by rw [← EReal.coe_add]; ring_nf
    _ = W := hLW


/-! ## Part J: theorem 7 (strong duality) as a lemma -/

theorem thm7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0)
    (ℓ : E → EReal) (husc : UpperSemicontinuous ℓ) (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂P < ⊤)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hcorr : 0 < ε ∨ ∃ γ : ℝ, 0 ≤ γ ∧ risk P (moreauYosida ℓ Ξ γ p) < ⊤) :
    worstCaseRisk ε p P Ξ ℓ
      = ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal) := by
  have hp0 : 0 < p := by linarith
  refine le_antisymm (WDRO7.le_dual hp hΞ P husc.measurable hε) ?_
  rcases hε.lt_or_eq with hεpos | hε0
  · exact WDRO7.dual_le_wc hp hΞ P hPΞ ℓ husc hint hεpos
  · subst hε0
    obtain ⟨γ0, hγ0, hfin⟩ := hcorr.resolve_left (lt_irrefl 0)
    have e : ∀ γ : ℝ, risk P (moreauYosida ℓ Ξ γ p) + ((γ * (0 : ℝ) ^ p : ℝ) : EReal)
        = risk P (moreauYosida ℓ Ξ γ p) := by
      intro γ; rw [Real.zero_rpow hp0.ne', mul_zero, EReal.coe_zero, add_zero]
    simp_rw [e]
    calc ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk P (moreauYosida ℓ Ξ γ p)
        ≤ risk P ℓ := WDRO7.dual_le_risk_zero hp0 P hPΞ husc hint hγ0 hfin
      _ ≤ worstCaseRisk 0 p P Ξ ℓ :=
        le_iSup₂ (f := fun Q _ => risk Q ℓ) P (WDRO7.self_mem_ball hp0 le_rfl P hPΞ)


/-! ## Part K: theorem 10 (convex loss, p = 1, empirical centre) -/

lemma risk_mono {E : Type*} [MeasurableSpace E] (P : Measure E) {f g : E → EReal}
    (h : ∀ x, f x ≤ g x) : risk P f ≤ risk P g := by
  unfold risk
  by_cases hg : ∫⁻ ξ, (g ξ).toENNReal ∂P = ⊤
  · rw [if_pos hg]; exact le_top
  · have hfg : ∫⁻ ξ, (f ξ).toENNReal ∂P ≤ ∫⁻ ξ, (g ξ).toENNReal ∂P :=
      lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h x)
    have hf : ∫⁻ ξ, (f ξ).toENNReal ∂P ≠ ⊤ := ne_top_of_le_ne_top hg hfg
    rw [if_neg hg, if_neg hf]
    refine EReal.sub_le_sub ?_ ?_
    · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hfg
    · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h x)))

lemma risk_lt_top_of_le {E : Type*} [MeasurableSpace E] (P : Measure E) [IsFiniteMeasure P]
    {f : E → EReal} {C : ℝ} (h : ∀ x, f x ≤ (C : EReal)) : risk P f < ⊤ := by
  have hA : ∫⁻ ξ, (f ξ).toENNReal ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal C ∂P) ?_ ?_
    · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _)
    · refine lintegral_mono fun x => ?_
      rw [← toENNReal_real]; exact EReal.toENNReal_le_toENNReal (h x)
  unfold risk
  rw [if_neg hA]
  refine lt_of_le_of_lt (EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)) ?_
  rw [sub_zero]
  exact lt_top_iff_ne_top.mpr fun h => hA (EReal.coe_ennreal_eq_top_iff.mp h)

lemma risk_top {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    {f : E → EReal} (h : ∀ x, f x = ⊤) : risk P f = ⊤ := by
  unfold risk
  have : ∫⁻ ξ, (f ξ).toENNReal ∂P = ⊤ := by
    simp only [h, EReal.toENNReal_top, lintegral_const, measure_univ, mul_one]
  rw [if_pos this]

lemma empirical_prob {E : Type*} [MeasurableSpace E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) :
    IsProbabilityMeasure (empirical ξhat) := by
  constructor
  unfold empirical
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

lemma empirical_compl {E : Type*} [MeasurableSpace E] {N : ℕ} (ξhat : Fin N → E)
    (hS : MeasurableSet (Set.range ξhat)) : empirical ξhat (Set.range ξhat)ᶜ = 0 := by
  unfold empirical
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have : ∀ i, Measure.dirac (ξhat i) (Set.range ξhat)ᶜ = 0 := fun i => by
    rw [Measure.dirac_apply' _ hS.compl]
    simp
  simp [this]

lemma empirical_lintegral {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ}
    (ξhat : Fin N → E) (f : E → ENNReal) :
    ∫⁻ ξ, f ξ ∂(empirical ξhat) = (N : ENNReal)⁻¹ * ∑ i, f (ξhat i) := by
  unfold empirical
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp [lintegral_dirac]

/-- `W_1(Q, P) = 0` and `P` carried by a closed nonempty `S` force `Q` to be carried by `S`. -/
lemma compl_zero_of_w1 {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {Q P : Measure E} {S : Set E} (hS : IsClosed S) (hne : S.Nonempty)
    (hP : P Sᶜ = 0) (hW : wasserstein 1 Q P ≤ ENNReal.ofReal 0) : Q Sᶜ = 0 := by
  set f : E → ENNReal := fun x => ENNReal.ofReal (Metric.infDist x S) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (Metric.continuous_infDist_pt S).measurable
  have hbound : ∫⁻ x, f x ∂Q = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) bot_le
    obtain ⟨π, ⟨_, h1, h2⟩, hπ⟩ := exists_coupling one_pos le_rfl hW (η := (η : ℝ)) hη
    have hae : ∀ᵐ x ∂π, x.2 ∈ S := by
      have : π (Prod.snd ⁻¹' Sᶜ) = 0 := by
        rw [← Measure.map_apply measurable_snd hS.measurableSet.compl, h2, hP]
      exact ae_iff.mpr this
    rw [← lintegral_fst h1 hfm, zero_add]
    calc ∫⁻ x, f x.1 ∂π ≤ ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π := by
          refine lintegral_mono_ae (hae.mono fun x hx => ?_)
          rw [Real.rpow_one, hf]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← dist_eq_norm]
          exact Metric.infDist_le_dist_of_mem hx
      _ ≤ ENNReal.ofReal ((0 : ℝ) ^ (1 : ℝ) + η) := hπ
      _ = (η : ENNReal) := by rw [Real.rpow_one, zero_add, ENNReal.ofReal_coe_nnreal]
  have hz : ∀ᵐ x ∂Q, f x = 0 := (lintegral_eq_zero_iff hfm).mp hbound
  have hmem : ∀ᵐ x ∂Q, x ∈ S := hz.mono fun x hx => by
    rw [hf, ENNReal.ofReal_eq_zero] at hx
    have h0 : Metric.infDist x S = 0 := le_antisymm hx Metric.infDist_nonneg
    rw [← hS.closure_eq, Metric.mem_closure_iff_infDist_zero hne]
    exact h0
  exact ae_iff.mp hmem

lemma my_ge_point {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ : ℝ) (z ξ : E) :
    ℓ z - ((γ * ‖z - ξ‖ : ℝ) : EReal) ≤ moreauYosida ℓ Set.univ γ 1 ξ := by
  unfold moreauYosida
  refine le_iSup₂_of_le z (Set.mem_univ z) ?_
  rw [Real.rpow_one]

lemma my_top_of_top {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) (γ : ℝ) {z : E}
    (hz : ℓ z = ⊤) (ξ : E) : moreauYosida ℓ Set.univ γ 1 ξ = ⊤ := by
  have := my_ge_point ℓ γ z ξ
  rw [hz, EReal.top_sub_coe] at this
  exact eq_top_iff.mpr this

lemma epi_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ : E → EReal}
    (hconv : IsConvexExt ℓ) {x y : E} {s t : ℝ} (hx : ℓ x ≤ (s : EReal)) (hy : ℓ y ≤ (t : EReal))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ℓ (a • x + b • y) ≤ ((a * s + b * t : ℝ) : EReal) := by
  have := hconv (x := (x, s)) (y := (y, t)) hx hy ha hb hab
  simpa [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using this

lemma exists_top_of_bot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ : E → EReal}
    (hconv : IsConvexExt ℓ) {x c : E} (hx : ℓ x = ⊥) (hc : ℓ c ≠ ⊥) :
    ℓ ((2 : ℝ) • c - x) = ⊤ := by
  by_contra hw
  set s : ℝ := (ℓ ((2 : ℝ) • c - x)).toReal
  have hws : ℓ ((2 : ℝ) • c - x) ≤ (s : EReal) := EReal.le_coe_toReal hw
  apply hc
  refine (EReal.eq_bot_iff_forall_lt _).mpr fun y => ?_
  have hxr : ℓ x ≤ ((2 * (y - 1) - s : ℝ) : EReal) := by rw [hx]; exact bot_le
  have hcomb := epi_comb hconv hxr hws (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  have heq : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • ((2 : ℝ) • c - x) = c := by
    rw [smul_sub, smul_smul]; norm_num
  rw [heq] at hcomb
  refine lt_of_le_of_lt hcomb ?_
  rw [EReal.coe_lt_coe_iff]
  linarith

lemma my_top_of_slope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ : E → EReal}
    (hconv : IsConvexExt ℓ) {x y : E} {A B γ : ℝ} (hγ : 0 ≤ γ) (hA : ℓ x = A) (hB : ℓ y = B)
    (hslope : γ * ‖x - y‖ < A - B) (ξ : E) : moreauYosida ℓ Set.univ γ 1 ξ = ⊤ := by
  have key : ∀ t : ℝ, 1 ≤ t → ((B + t * (A - B) : ℝ) : EReal) ≤ ℓ (y + t • (x - y)) := by
    intro t ht
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have ht0 : 0 < t := by linarith
    have hcomb := epi_comb hconv hs1.le hB.le (a := 1 / t) (b := 1 - 1 / t) (by positivity)
      (by rw [sub_nonneg, div_le_one ht0]; exact ht) (by ring)
    have heq : (1 / t) • (y + t • (x - y)) + (1 - 1 / t) • y = x := by
      rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ ht0.ne', one_smul, sub_smul, one_smul]
      abel
    rw [heq, hA, EReal.coe_le_coe_iff] at hcomb
    have hs2' : s < B + t * (A - B) := EReal.coe_lt_coe_iff.mp hs2
    have e : t * (1 / t * s + (1 - 1 / t) * B) = s + (t - 1) * B := by
      field_simp
    have := mul_le_mul_of_nonneg_left hcomb ht0.le
    rw [e] at this
    nlinarith
  refine (EReal.eq_top_iff_forall_lt _).mpr fun M => ?_
  set δ : ℝ := A - B - γ * ‖x - y‖ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set t : ℝ := max 1 ((M - B + γ * ‖y - ξ‖ + 1) / δ) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht2 : (M - B + γ * ‖y - ξ‖ + 1) / δ ≤ t := le_max_right _ _
  have ht3 : M - B + γ * ‖y - ξ‖ + 1 ≤ t * δ := by
    rwa [div_le_iff₀ hδ0] at ht2
  set z : E := y + t • (x - y)
  have hnorm : ‖z - ξ‖ ≤ ‖y - ξ‖ + t * ‖x - y‖ := by
    have : z - ξ = (y - ξ) + t • (x - y) := by simp only [z]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  have h1 := my_ge_point ℓ γ z ξ
  have h2 : ((B + t * (A - B) : ℝ) : EReal) - ((γ * ‖z - ξ‖ : ℝ) : EReal)
      ≤ ℓ z - ((γ * ‖z - ξ‖ : ℝ) : EReal) := EReal.sub_le_sub (key t ht1) le_rfl
  rw [← EReal.coe_sub] at h2
  refine lt_of_lt_of_le ?_ (h2.trans h1)
  rw [EReal.coe_lt_coe_iff]
  have hγn : γ * ‖z - ξ‖ ≤ γ * ‖y - ξ‖ + γ * (t * ‖x - y‖) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hnorm hγ
  have : t * δ = t * (A - B) - γ * (t * ‖x - y‖) := by rw [hδ]; ring
  linarith

lemma lip_term_le {E : Type*} [NormedAddCommGroup E] (ℓ : E → EReal) {z ξ : E} (hne : z ≠ ξ) :
    EReal.abs (ℓ z - ℓ ξ) / ENNReal.ofReal ‖z - ξ‖ ≤ lipModulus ℓ := by
  unfold lipModulus
  exact le_iSup₂_of_le z ξ (le_iSup_of_le hne le_rfl)

lemma real_of_ne {x : EReal} (h1 : x ≠ ⊤) (h2 : x ≠ ⊥) : ∃ r : ℝ, x = r :=
  ⟨x.toReal, (EReal.coe_toReal h1 h2).symm⟩

lemma ratio_iff {a b γ : ℝ} (hb : 0 < b) (hγ : 0 ≤ γ) :
    ENNReal.ofReal γ < EReal.abs ((a : EReal)) / ENNReal.ofReal b ↔ γ * b < |a| := by
  rw [EReal.abs_def, ← ENNReal.ofReal_div_of_pos hb, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hγ,
    lt_div_iff₀ hb]

lemma my_top_of_lt_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ : E → EReal}
    (hconv : IsConvexExt ℓ) {c : E} (hc : ℓ c ≠ ⊥) {γ : ℝ} (hγ : 0 ≤ γ)
    (hlt : ENNReal.ofReal γ < lipModulus ℓ) (ξ : E) : moreauYosida ℓ Set.univ γ 1 ξ = ⊤ := by
  have htop : ∀ w, ℓ w = ⊥ → moreauYosida ℓ Set.univ γ 1 ξ = ⊤ := fun w hw =>
    my_top_of_top ℓ γ (exists_top_of_bot hconv hw hc) ξ
  unfold lipModulus at hlt
  simp only [lt_iSup_iff] at hlt
  obtain ⟨x, y, hne, h⟩ := hlt
  by_cases hxt : ℓ x = ⊤
  · exact my_top_of_top ℓ γ hxt ξ
  by_cases hyt : ℓ y = ⊤
  · exact my_top_of_top ℓ γ hyt ξ
  by_cases hxb : ℓ x = ⊥
  · exact htop x hxb
  by_cases hyb : ℓ y = ⊥
  · exact htop y hyb
  obtain ⟨A, hA⟩ := real_of_ne hxt hxb
  obtain ⟨B, hB⟩ := real_of_ne hyt hyb
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [hA, hB, ← EReal.coe_sub, ratio_iff hpos hγ] at h
  rcases le_or_gt 0 (A - B) with hab | hab
  · rw [abs_of_nonneg hab] at h
    exact my_top_of_slope hconv hγ hA hB h ξ
  · rw [abs_of_neg hab] at h
    refine my_top_of_slope hconv hγ hB hA ?_ ξ
    rw [← norm_neg, neg_sub]; linarith

lemma fin_of_lip {E : Type*} [NormedAddCommGroup E] {ℓ : E → EReal} (hL : lipModulus ℓ ≠ ⊤)
    {c : E} (hc1 : ℓ c ≠ ⊤) (hc2 : ℓ c ≠ ⊥) (z : E) : ℓ z ≠ ⊤ ∧ ℓ z ≠ ⊥ := by
  by_cases hzc : z = c
  · rw [hzc]; exact ⟨hc1, hc2⟩
  obtain ⟨C, hC⟩ := real_of_ne hc1 hc2
  have hle := lip_term_le ℓ hzc
  have hpos : ENNReal.ofReal ‖z - c‖ ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro hz
    rw [hz, hC, EReal.top_sub_coe, EReal.abs_top, ENNReal.top_div_of_ne_top hpos] at hle
    exact hL (top_le_iff.mp hle)
  · intro hz
    rw [hz, hC, EReal.bot_sub, EReal.abs_bot, ENNReal.top_div_of_ne_top hpos] at hle
    exact hL (top_le_iff.mp hle)

lemma my_eq_of_lip {E : Type*} [NormedAddCommGroup E] {ℓ : E → EReal} (hL : lipModulus ℓ ≠ ⊤)
    {c : E} (hc1 : ℓ c ≠ ⊤) (hc2 : ℓ c ≠ ⊥) :
    moreauYosida ℓ Set.univ (lipModulus ℓ).toReal 1 = ℓ := by
  set L := (lipModulus ℓ).toReal with hLdef
  have hLeq : lipModulus ℓ = ENNReal.ofReal L := (ENNReal.ofReal_toReal hL).symm
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  funext ξ
  refine le_antisymm ?_ (my_ge ℓ one_pos (Set.mem_univ ξ))
  unfold moreauYosida
  refine iSup₂_le fun z _ => ?_
  rw [Real.rpow_one]
  by_cases hzξ : z = ξ
  · rw [hzξ, sub_self, norm_zero, mul_zero, EReal.coe_zero, sub_zero]
  obtain ⟨a, ha⟩ := real_of_ne (fin_of_lip hL hc1 hc2 z).1 (fin_of_lip hL hc1 hc2 z).2
  obtain ⟨b, hb⟩ := real_of_ne (fin_of_lip hL hc1 hc2 ξ).1 (fin_of_lip hL hc1 hc2 ξ).2
  have hle := lip_term_le ℓ hzξ
  have hpos : 0 < ‖z - ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzξ)
  rw [ha, hb, ← EReal.coe_sub, EReal.abs_def, ← ENNReal.ofReal_div_of_pos hpos, hLeq,
    ENNReal.ofReal_le_ofReal_iff hL0, div_le_iff₀ hpos] at hle
  rw [ha, hb, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have := le_abs_self (a - b)
  linarith

theorem main10 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → EReal) (hconv : IsConvexExt ℓ)
    (hmeas : Measurable ℓ) (husc : UpperSemicontinuous ℓ)
    (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂(empirical ξhat) < ⊤) (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseRisk ε 1 (empirical ξhat) Set.univ ℓ
      = risk (empirical ξhat) ℓ + (ε : EReal) * ((lipModulus ℓ : ENNReal) : EReal) := by
  have := empirical_prob hN ξhat
  -- every sample value is finite
  have hfin : ∀ i, ℓ (ξhat i) ≠ ⊤ ∧ ℓ (ξhat i) ≠ ⊥ := by
    intro i
    have habs : EReal.abs (ℓ (ξhat i)) ≠ ⊤ := by
      intro h
      have h1 : (N : ENNReal)⁻¹ * EReal.abs (ℓ (ξhat i))
          ≤ ∫⁻ ξ, EReal.abs (ℓ ξ) ∂(empirical ξhat) := by
        rw [empirical_lintegral]
        gcongr (N : ENNReal)⁻¹ * ?_
        exact Finset.single_le_sum (f := fun j => EReal.abs (ℓ (ξhat j)))
          (fun _ _ => bot_le) (Finset.mem_univ i)
      rw [h, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top N))] at h1
      exact (lt_of_le_of_lt h1 hint).ne rfl
    exact ⟨fun h => habs (by rw [h, EReal.abs_top]), fun h => habs (by rw [h, EReal.abs_bot])⟩
  set c : E := ξhat ⟨0, hN⟩
  have hc1 : ℓ c ≠ ⊤ := (hfin _).1
  have hc2 : ℓ c ≠ ⊥ := (hfin _).2
  -- the nominal risk is a real number
  have hA : ∫⁻ ξ, (ℓ ξ).toENNReal ∂(empirical ξhat) ≠ ⊤ :=
    ne_top_of_le_ne_top hint.ne (lintegral_mono fun x => pos_le_abs _)
  have hB : ∫⁻ ξ, (-ℓ ξ).toENNReal ∂(empirical ξhat) ≠ ⊤ :=
    ne_top_of_le_ne_top hint.ne (lintegral_mono fun x => negpart_le_abs _)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, risk (empirical ξhat) ℓ = R := ⟨_, risk_eq_coe _ ℓ hA hB⟩
  rcases hε.lt_or_eq with hεpos | hε0
  · rw [thm7 (le_refl 1) isClosed_univ (empirical ξhat) (by simp) ℓ husc hint ε hε
      (Or.inl hεpos)]
    by_cases hL : lipModulus ℓ = ⊤
    · rw [hL, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos hεpos, hR,
        EReal.coe_add_top]
      refine le_antisymm le_top (le_iInf₂ fun γ hγ => ?_)
      have hlt : ENNReal.ofReal γ < lipModulus ℓ := by rw [hL]; exact ENNReal.ofReal_lt_top
      rw [risk_top _ (my_top_of_lt_lip hconv hc2 hγ hlt), EReal.top_add_coe]
    · set L := (lipModulus ℓ).toReal with hLdef
      have hLeq : lipModulus ℓ = ENNReal.ofReal L := (ENNReal.ofReal_toReal hL).symm
      have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
      rw [hLeq, coe_ofReal_of_nonneg hL0, hR, ← EReal.coe_mul, ← EReal.coe_add]
      refine le_antisymm ?_ (le_iInf₂ fun γ hγ => ?_)
      · refine (iInf₂_le L hL0).trans (le_of_eq ?_)
        rw [hLdef, my_eq_of_lip hL hc1 hc2, ← hLdef, hR, Real.rpow_one, ← EReal.coe_add]
        congr 1; ring
      · by_cases hlt : ENNReal.ofReal γ < lipModulus ℓ
        · rw [risk_top _ (my_top_of_lt_lip hconv hc2 hγ hlt), EReal.top_add_coe]
          exact le_top
        · rw [not_lt, hLeq, ENNReal.ofReal_le_ofReal_iff hγ] at hlt
          have h1 : risk (empirical ξhat) ℓ ≤ risk (empirical ξhat) (moreauYosida ℓ Set.univ γ 1) :=
            risk_mono _ fun x => my_ge ℓ one_pos (Set.mem_univ x)
          rw [hR] at h1
          refine le_trans ?_ (add_le_add h1 le_rfl)
          rw [← EReal.coe_add, EReal.coe_le_coe_iff, Real.rpow_one]
          nlinarith
  · subst hε0
    rw [EReal.coe_zero, zero_mul, add_zero]
    set S : Set E := Set.range ξhat with hSdef
    have hSc : IsClosed S := (Set.finite_range ξhat).isClosed
    have hSne : S.Nonempty := ⟨c, Set.mem_range_self _⟩
    have hPS : empirical ξhat Sᶜ = 0 := empirical_compl ξhat hSc.measurableSet
    -- the Moreau-Yosida envelope over S at γ = 0 is bounded above
    set K : ℝ := ∑ i, |(ℓ (ξhat i)).toReal| with hK
    have hzK : ∀ z ∈ S, ℓ z ≤ (K : EReal) := by
      rintro z ⟨i, rfl⟩
      refine (EReal.le_coe_toReal (hfin i).1).trans (EReal.coe_le_coe_iff.mpr ?_)
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |(ℓ (ξhat j)).toReal|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    have hfinS : risk (empirical ξhat) (moreauYosida ℓ S 0 1) < ⊤ := by
      refine risk_lt_top_of_le _ (C := K) fun ξ => ?_
      unfold moreauYosida
      refine iSup₂_le fun z hz => ?_
      rw [zero_mul, EReal.coe_zero, sub_zero]
      exact hzK z hz
    have e : ∀ γ : ℝ, risk (empirical ξhat) (moreauYosida ℓ S γ 1) + ((γ * (0 : ℝ) ^ (1 : ℝ) : ℝ) : EReal)
        = risk (empirical ξhat) (moreauYosida ℓ S γ 1) := by
      intro γ; rw [Real.rpow_one, mul_zero, EReal.coe_zero, add_zero]
    refine le_antisymm (iSup₂_le fun Q hQ => ?_)
      (le_iSup₂ (f := fun Q _ => risk Q ℓ) (empirical ξhat)
        (self_mem_ball one_pos le_rfl (empirical ξhat) (by simp)))
    obtain ⟨hQp, _, hW⟩ := hQ
    have hQS : Q Sᶜ = 0 := compl_zero_of_w1 hSc hSne hPS hW
    have hQ' : Q ∈ ambiguityBall 0 1 (empirical ξhat) S := ⟨hQp, hQS, hW⟩
    calc risk Q ℓ ≤ worstCaseRisk 0 1 (empirical ξhat) S ℓ :=
          le_iSup₂ (f := fun Q _ => risk Q ℓ) Q hQ'
      _ ≤ ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk (empirical ξhat) (moreauYosida ℓ S γ 1)
            + ((γ * (0 : ℝ) ^ (1 : ℝ) : ℝ) : EReal) :=
          le_dual (le_refl 1) hSc (empirical ξhat) hmeas le_rfl
      _ = ⨅ (γ : ℝ) (_ : 0 ≤ γ), risk (empirical ξhat) (moreauYosida ℓ S γ 1) := by simp_rw [e]
      _ ≤ risk (empirical ξhat) ℓ :=
          dual_le_risk_zero one_pos (empirical ξhat) hPS husc hint le_rfl hfinS


end WDRO7

open WassersteinDRO.ConvexLossP1 MeasureTheory in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → EReal) (hconv : IsConvexExt ℓ)
    (hmeas : Measurable ℓ) (husc : UpperSemicontinuous ℓ)
    (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂(empirical ξhat) < ⊤) (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseRisk ε 1 (empirical ξhat) Set.univ ℓ
      = risk (empirical ξhat) ℓ + (ε : EReal) * ((lipModulus ℓ : ENNReal) : EReal) := by
  exact WDRO7.main10 hN ξhat ℓ hconv hmeas husc hint ε hε
