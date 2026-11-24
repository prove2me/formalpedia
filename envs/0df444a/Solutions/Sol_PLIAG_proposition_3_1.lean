-- Prove2me | solution 1 for PLIAG.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T20:39:21.380207+00:00
-- url     : https://prove2.me/submissions/21c4264b-cb9c-4b50-85c1-7c53f794429b

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_IsLegendre
import Definitions.Def_PLIAG_optSet
import Definitions.Def_PLIAG_AssumptionB1
import Definitions.Def_PLIAG_AssumptionB4
import Definitions.Def_PLIAG_Phik

namespace PLIAGP31
open PLIAG AubinLipschitz Filter Topology

set_option linter.unusedSectionVars false

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cvx_real {φ : E → EReal} (hφ : TensorAHPE.IsProperClosedConvex φ) {a b : E}
    (ha : φ a ≠ ⊤) (hb : φ b ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    φ (s • a + t • b) ≤ ((s * (φ a).toReal + t * (φ b).toReal : ℝ) : EReal) := by
  have h1 : (a, (φ a).toReal) ∈ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    show φ a ≤ ((φ a).toReal : EReal); rw [EReal.coe_toReal ha (hφ.1 a)]
  have h2 : (b, (φ b).toReal) ∈ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    show φ b ≤ ((φ b).toReal : EReal); rw [EReal.coe_toReal hb (hφ.1 b)]
  have := hφ.2.2.2 h1 h2 hs ht hst
  simpa only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this

lemma cvx_ne_top {φ : E → EReal} (hφ : TensorAHPE.IsProperClosedConvex φ) {a b : E}
    (ha : φ a ≠ ⊤) (hb : φ b ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    φ (s • a + t • b) ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (cvx_real hφ ha hb hs ht hst)

lemma cvx_toReal {φ : E → EReal} (hφ : TensorAHPE.IsProperClosedConvex φ) {a b : E}
    (ha : φ a ≠ ⊤) (hb : φ b ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    (φ (s • a + t • b)).toReal ≤ s * (φ a).toReal + t * (φ b).toReal := by
  have := EReal.toReal_le_toReal (cvx_real hφ ha hb hs ht hst) (hφ.1 _) (EReal.coe_ne_top _)
  simpa only [EReal.toReal_coe] using this

lemma slope_le {F : E → ℝ} {F' : E →L[ℝ] ℝ} {u : E} (hF : HasFDerivAt F F' u) (v : E) (B : ℝ)
    (hB : ∀ s ∈ Set.Ioo (0:ℝ) 1, F (u + s • v) ≤ F u + s * B) : F' v ≤ B := by
  have h1 : HasDerivAt (fun s : ℝ => u + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add u
  have hg : HasDerivAt (fun s : ℝ => F (u + s • v)) (F' v) 0 :=
    hF.comp_hasDerivAt_of_eq (0:ℝ) h1 (by simp)
  have ht := hg.tendsto_slope_zero_right
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
  have := hB s hs
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  rw [inv_mul_le_iff₀ hs.1]; linarith

lemma cvx_grad {S : Set E} {ψ : E → ℝ} (hψ : ConvexOn ℝ S ψ) {z y : E} (hz : z ∈ S) (hy : y ∈ S)
    {ψ' : E →L[ℝ] ℝ} (hd : HasFDerivAt ψ ψ' z) : ψ z + ψ' (y - z) ≤ ψ y := by
  have := slope_le hd (y - z) (ψ y - ψ z) (fun s hs => by
    have e : z + s • (y - z) = (1 - s) • z + s • y := by module
    rw [e]
    have := hψ.2 hz hy (show (0:ℝ) ≤ 1 - s by linarith [hs.2]) hs.1.le (by ring)
    simp only [smul_eq_mul] at this
    linarith)
  linarith

lemma sum_ne_bot {ι : Type*} (s : Finset ι) (g : ι → EReal) (h : ∀ i, g i ≠ ⊥) :
    ∑ i ∈ s, g i ≠ ⊥ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons]; exact fun H => (EReal.add_eq_bot_iff.1 H).elim (h a) ih

lemma sum_coe {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ∑ i ∈ s, ((g i : ℝ) : EReal) = ((∑ i ∈ s, g i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, EReal.coe_add]

lemma sum_eq_top {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → EReal) (hb : ∀ i, g i ≠ ⊥)
    {i : ι} (hi : i ∈ s) (ht : g i = ⊤) : ∑ j ∈ s, g j = ⊤ := by
  rw [← Finset.add_sum_erase s g hi, ht]
  exact EReal.top_add_of_ne_bot (sum_ne_bot _ _ hb)

lemma lsc_add {f g : E → EReal} (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hfb : ∀ x, f x ≠ ⊥) (hgb : ∀ x, g x ≠ ⊥) : LowerSemicontinuous fun x => f x + g x :=
  hf.add' hg fun x => EReal.continuousAt_add (Or.inr (hgb x)) (Or.inl (hfb x))

lemma lsc_sum {ι : Type*} (s : Finset ι) (g : ι → E → EReal)
    (hl : ∀ i, LowerSemicontinuous (g i)) (hb : ∀ i x, g i x ≠ ⊥) :
    LowerSemicontinuous fun x => ∑ i ∈ s, g i x := by
  induction s using Finset.cons_induction with
  | empty => simpa using (lowerSemicontinuous_const : LowerSemicontinuous fun _ : E => (0:EReal))
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact lsc_add (hl a) ih (hb a) (fun x => sum_ne_bot _ _ (fun i => hb i x))

lemma lsc_cmul {f : E → EReal} (hf : LowerSemicontinuous f) {c : ℝ} (hc : 0 < c) :
    LowerSemicontinuous fun x => (c : EReal) * f x := by
  have hc0 : (c : EReal) ≠ 0 := by exact_mod_cast hc.ne'
  have hcont : Continuous fun e : EReal => (c : EReal) * e := by
    rw [continuous_iff_continuousAt]; intro e
    have := EReal.continuousAt_mul (p := ((c:EReal), e)) (Or.inl hc0) (Or.inl hc0)
      (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
    exact this.comp (continuousAt_const.prodMk continuousAt_id)
  exact hcont.comp_lowerSemicontinuous hf
    (fun a b hab => mul_le_mul_of_nonneg_left hab (by exact_mod_cast hc.le))

lemma cmul_ne_bot {c : ℝ} (hc : 0 < c) {e : EReal} (he : e ≠ ⊥) : (c : EReal) * e ≠ ⊥ := by
  induction e using EReal.rec with
  | bot => exact absurd rfl he
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

lemma lim_le {a b c : ℝ} (h : ∀ t ∈ Set.Ioo (0:ℝ) 1, a ≤ (1 - t) * b + t * c) : a ≤ b := by
  have ht : Tendsto (fun t : ℝ => (1 - t) * b + t * c) (𝓝[>] 0) (𝓝 ((1 - 0) * b + 0 * c)) :=
    ((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds |>.add
      (tendsto_id.mul tendsto_const_nhds)).mono_left nhdsWithin_le_nhds
  simp only [sub_zero, one_mul, zero_mul, add_zero] at ht
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht using h t ht

lemma level_bounded {d : ℕ} (Φ : EuclideanSpace ℝ (Fin d) → EReal)
    (Q X : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : Convex ℝ Q) (hQcl : IsClosed Q) (hlsc : LowerSemicontinuous Φ) (hbot : ∀ x, Φ x ≠ ⊥)
    (hcvx : ∀ a b, Φ a ≠ ⊤ → Φ b ≠ ⊤ → ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
       Φ (s • a + t • b) ≤ ((s * (Φ a).toReal + t * (Φ b).toReal : ℝ) : EReal))
    (hX : ∀ x, x ∈ X ↔ x ∈ Q ∧ ∀ y ∈ Q, Φ x ≤ Φ y) (hXc : IsCompact X)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ X) (hx0t : Φ x0 ≠ ⊤) (M : ℝ) :
    ∃ B, ∀ y ∈ Q, Φ y ≤ M → ‖y - x0‖ ≤ B := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x0).1 hXc.isBounded
  set ρ := max R 0 + 1 with hρ
  have hρpos : 0 < ρ := by positivity
  set m0 := (Φ x0).toReal
  have hm0 : Φ x0 = (m0 : EReal) := (EReal.coe_toReal hx0t (hbot x0)).symm
  have key : ∀ y ∈ Q, Φ y ≤ M → ρ < ‖y - x0‖ →
      ∃ u ∈ Q ∩ Metric.sphere x0 ρ,
        Φ u ≤ (((1 - ρ / ‖y - x0‖) * m0 + ρ / ‖y - x0‖ * M : ℝ) : EReal) := by
    intro y hyQ hyM hfar
    have hn : 0 < ‖y - x0‖ := hρpos.trans hfar
    set θ := ρ / ‖y - x0‖ with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := (div_le_one hn).2 hfar.le
    have hyt : Φ y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top M) hyM
    refine ⟨(1 - θ) • x0 + θ • y, ⟨hQc ((hX x0).1 hx0).1 hyQ (by linarith) hθ0 (by ring), ?_⟩, ?_⟩
    · rw [mem_sphere_iff_norm]
      have : (1 - θ) • x0 + θ • y - x0 = θ • (y - x0) := by module
      rw [this, norm_smul, Real.norm_of_nonneg hθ0, hθ, div_mul_cancel₀ _ hn.ne']
    · refine (hcvx x0 y hx0t hyt (1 - θ) θ (by linarith) hθ0 (by ring)).trans ?_
      have h1 : (Φ y).toReal ≤ M := by
        have := EReal.toReal_le_toReal hyM (hbot y) (EReal.coe_ne_top M)
        simpa only [EReal.toReal_coe] using this
      exact EReal.coe_le_coe_iff.2 (by nlinarith)
  by_cases hfar : ∃ y ∈ Q, Φ y ≤ M ∧ ρ < ‖y - x0‖
  · obtain ⟨y1, hy1Q, hy1M, hy1far⟩ := hfar
    obtain ⟨u1, hu1S, hu1le⟩ := key y1 hy1Q hy1M hy1far
    have hS : IsCompact (Q ∩ Metric.sphere x0 ρ) := (isCompact_sphere x0 ρ).inter_left hQcl
    obtain ⟨u0, hu0S, hu0min⟩ := (hlsc.lowerSemicontinuousOn _).exists_isMinOn ⟨u1, hu1S⟩ hS
    have hu0t : Φ u0 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) ((hu0min hu1S).trans hu1le)
    set δ := (Φ u0).toReal - m0 with hδdef
    have hδ : 0 < δ := by
      have hnX : u0 ∉ X := fun h => by
        have h1 := hR h
        rw [Metric.mem_closedBall] at h1
        have h2 := hu0S.2; rw [Metric.mem_sphere] at h2
        linarith [le_max_left R 0]
      rw [hX] at hnX; push Not at hnX
      obtain ⟨y', hy'Q, hlt⟩ := hnX hu0S.1
      have h1 : Φ x0 ≤ Φ y' := ((hX x0).1 hx0).2 y' hy'Q
      have h2 : Φ x0 < Φ u0 := lt_of_le_of_lt h1 hlt
      rw [hm0, ← EReal.coe_toReal hu0t (hbot u0)] at h2
      have := EReal.coe_lt_coe_iff.1 h2
      linarith
    refine ⟨max ρ (ρ * (M - m0) / δ), fun y hyQ hyM => ?_⟩
    by_cases hy : ‖y - x0‖ ≤ ρ
    · exact hy.trans (le_max_left _ _)
    push Not at hy
    obtain ⟨u, huS, hule⟩ := key y hyQ hyM hy
    have h1 := (hu0min huS).trans hule
    rw [← EReal.coe_toReal hu0t (hbot u0), EReal.coe_le_coe_iff] at h1
    have hn : 0 < ‖y - x0‖ := hρpos.trans hy
    refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ hδ]
    have h3 : δ ≤ ρ / ‖y - x0‖ * (M - m0) := by rw [hδdef]; nlinarith
    calc ‖y - x0‖ * δ ≤ ‖y - x0‖ * (ρ / ‖y - x0‖ * (M - m0)) := by gcongr
      _ = ρ * (M - m0) := by field_simp
  · push Not at hfar
    exact ⟨ρ, fun y hyQ hyM => hfar y hyQ hyM⟩

end General

section PL
variable {d N : ℕ}

lemma add_ne_bot' {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a + b ≠ ⊥ :=
  fun H => (EReal.add_eq_bot_iff.1 H).elim ha hb

lemma dom_convex {φ : EuclideanSpace ℝ (Fin d) → EReal} (hφ : TensorAHPE.IsProperClosedConvex φ) :
    Convex ℝ (effDom φ) :=
  fun _ ha _ hb _ _ hs ht hst => cvx_ne_top hφ ha hb hs ht hst

noncomputable def Dr (w : EuclideanSpace ℝ (Fin d) → EReal) (a b : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (w a).toReal - ((w b).toReal + inner ℝ (gradient (fun z => (w z).toReal) b) (a - b))

noncomputable def Aff (w : EuclideanSpace ℝ (Fin d) → EReal) (xk y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (w xk).toReal + inner ℝ (gradient (fun z => (w z).toReal) xk) (y - xk)

noncomputable def gv (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (J : ℕ → Finset (Fin N))
    (τd : ℕ → Fin N → ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) : EuclideanSpace ℝ (Fin d) :=
  ∑ j ∈ J k, gradient (fun z => (f j z).toReal) (x (k - τd k j))

noncomputable def Gp (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (h y).toReal + ∑ i ∈ (J k)ᶜ, (f i y).toReal + inner ℝ (gv f J τd x k) y

noncomputable def PR (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ) (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Gp f h J τd x k y + 1 / α * ((w y).toReal - Aff w (x k) y)

noncomputable def PhiR (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal)
    (h : EuclideanSpace ℝ (Fin d) → EReal) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ n, (f n y).toReal + (h y).toReal

lemma Dr_eq_Aff (w : EuclideanSpace ℝ (Fin d) → EReal) (y xk : EuclideanSpace ℝ (Fin d)) :
    Dr w y xk = (w y).toReal - Aff w xk y := rfl

lemma bregman_eq (w : EuclideanSpace ℝ (Fin d) → EReal) {a : EuclideanSpace ℝ (Fin d)}
    (b : EuclideanSpace ℝ (Fin d)) (ha : w a ≠ ⊤) (hb : w a ≠ ⊥) :
    bregman w a b = (Dr w a b : EReal) := by
  unfold bregman Dr
  conv_lhs => rw [← EReal.coe_toReal ha hb]
  rw [EReal.coe_sub]

lemma bregman_ne_bot (w : EuclideanSpace ℝ (Fin d) → EReal) {a : EuclideanSpace ℝ (Fin d)}
    (b : EuclideanSpace ℝ (Fin d)) (hb : w a ≠ ⊥) : bregman w a b ≠ ⊥ := by
  by_cases ha : w a = ⊤
  · unfold bregman; rw [ha, EReal.top_sub_coe]; exact top_ne_bot
  · rw [bregman_eq w b ha hb]; exact EReal.coe_ne_bot _

lemma bregman_top (w : EuclideanSpace ℝ (Fin d) → EReal) {a : EuclideanSpace ℝ (Fin d)}
    (b : EuclideanSpace ℝ (Fin d)) (ha : w a = ⊤) : bregman w a b = ⊤ := by
  unfold bregman; rw [ha, EReal.top_sub_coe]

lemma sg {w : EuclideanSpace ℝ (Fin d) → EReal} (hw : IsLegendre w) {u y : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ interior (effDom w)) (hy : w y ≠ ⊤) :
    (w u).toReal + inner ℝ (gradient (fun z => (w z).toReal) u) (y - u) ≤ (w y).toReal := by
  have hd := hasGradientAt_iff_hasFDerivAt.1
    ((hw.2.2.1 u hu).differentiableAt (isOpen_interior.mem_nhds hu)).hasGradientAt
  have hwu : w u ≠ ⊤ := interior_subset hu
  have := slope_le hd (y - u) ((w y).toReal - (w u).toReal) (fun s hs => by
    have e : u + s • (y - u) = (1 - s) • u + s • y := by module
    rw [e]
    have := cvx_toReal hw.1 hwu hy (show (0:ℝ) ≤ 1 - s by linarith [hs.2]) hs.1.le (by ring)
    linarith)
  rw [InnerProductSpace.toDual_apply_apply] at this
  linarith

lemma Dr_nonneg {w : EuclideanSpace ℝ (Fin d) → EReal} (hw : IsLegendre w) {y b : EuclideanSpace ℝ (Fin d)}
    (hb : b ∈ interior (effDom w)) (hy : w y ≠ ⊤) : 0 ≤ Dr w y b := by
  have := sg hw hb hy; unfold Dr; linarith

lemma desc {w : EuclideanSpace ℝ (Fin d) → EReal} {f : Fin N → EuclideanSpace ℝ (Fin d) → EReal}
    {Lc : Fin N → ℝ} (hw : IsLegendre w) (hB1 : AssumptionB1 w f Lc) (j : Fin N)
    {y z : EuclideanSpace ℝ (Fin d)} (hy : y ∈ interior (effDom w)) (hz : z ∈ interior (effDom w)) :
    (f j y).toReal ≤ (f j z).toReal + inner ℝ (gradient (fun q => (f j q).toReal) z) (y - z)
      + Lc j * Dr w y z := by
  have hzn := isOpen_interior.mem_nhds hz
  have hw' := hasGradientAt_iff_hasFDerivAt.1 ((hw.2.2.1 z hz).differentiableAt hzn).hasGradientAt
  have hf' := hasGradientAt_iff_hasFDerivAt.1
    (((hB1 j).2.2.1 z hz).differentiableAt hzn).hasGradientAt
  have := cvx_grad (hB1 j).2.2.2.2 hz hy ((hw'.const_mul (Lc j)).sub hf')
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul] at this
  unfold Dr
  linarith

variable {w : EuclideanSpace ℝ (Fin d) → EReal} {f : Fin N → EuclideanSpace ℝ (Fin d) → EReal}
  {h : EuclideanSpace ℝ (Fin d) → EReal} {Lc : Fin N → ℝ} {J : ℕ → Finset (Fin N)}
  {τd : ℕ → Fin N → ℕ} {α : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin d)} {k : ℕ}

lemma Phik_eq (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h) (hw : IsLegendre w)
    {y : EuclideanSpace ℝ (Fin d)} (hy : h y ≠ ⊤) (hwy : w y ≠ ⊤) :
    Phik w f h J τd α x k y = (PR w f h J τd α x k y : EReal) := by
  have e1 : h y = ((h y).toReal : EReal) := (EReal.coe_toReal hy (hh.1 y)).symm
  have e2 : ∑ i ∈ (J k)ᶜ, f i y = ((∑ i ∈ (J k)ᶜ, (f i y).toReal : ℝ) : EReal) := by
    rw [← sum_coe]
    exact Finset.sum_congr rfl fun i _ => (EReal.coe_toReal ((hB1 i).2.1 hwy) ((hB1 i).1.1 y)).symm
  unfold Phik
  rw [bregman_eq w (x k) hwy (hw.1.1 y), e2, e1]
  unfold PR Gp gv
  rw [Dr_eq_Aff]
  norm_cast

lemma Phik_top (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h) (hw : IsLegendre w)
    (hα : 0 < α) {y : EuclideanSpace ℝ (Fin d)} (hy : h y = ⊤ ∨ w y = ⊤) :
    Phik w f h J τd α x k y = ⊤ := by
  have hs : ∑ i ∈ (J k)ᶜ, f i y ≠ ⊥ := sum_ne_bot _ _ fun i => (hB1 i).1.1 y
  have hc : (0:ℝ) < 1 / α := by positivity
  unfold Phik
  rcases hy with hy | hy
  · rw [hy, EReal.top_add_of_ne_bot hs, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
      EReal.top_add_of_ne_bot (cmul_ne_bot hc (bregman_ne_bot w _ (hw.1.1 y)))]
  · rw [bregman_top w _ hy, EReal.coe_mul_top_of_pos hc]
    exact EReal.add_top_of_ne_bot (add_ne_bot' (add_ne_bot' (hh.1 y) hs) (EReal.coe_ne_bot _))

lemma Phik_ne_bot (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h) (hw : IsLegendre w)
    (hα : 0 < α) (y : EuclideanSpace ℝ (Fin d)) : Phik w f h J τd α x k y ≠ ⊥ := by
  unfold Phik
  exact add_ne_bot' (add_ne_bot' (add_ne_bot' (hh.1 y) (sum_ne_bot _ _ fun i => (hB1 i).1.1 y))
    (EReal.coe_ne_bot _)) (cmul_ne_bot (by positivity) (bregman_ne_bot w _ (hw.1.1 y)))

lemma Phik_lsc (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h) (hw : IsLegendre w)
    (hα : 0 < α) : LowerSemicontinuous (Phik w f h J τd α x k) := by
  have hbr : LowerSemicontinuous fun y => bregman w y (x k) := by
    unfold bregman
    simp only [sub_eq_add_neg, ← EReal.coe_neg]
    exact lsc_add hw.1.2.2.1 (Continuous.lowerSemicontinuous
      (continuous_coe_real_ereal.comp (by fun_prop))) hw.1.1 (fun _ => EReal.coe_ne_bot _)
  have hs := lsc_sum ((J k)ᶜ) f (fun i => (hB1 i).1.2.2.1) (fun i y => (hB1 i).1.1 y)
  have hsb : ∀ y, ∑ i ∈ (J k)ᶜ, f i y ≠ ⊥ := fun y => sum_ne_bot _ _ fun i => (hB1 i).1.1 y
  have hlin : LowerSemicontinuous fun y : EuclideanSpace ℝ (Fin d) =>
      ((inner ℝ (∑ j ∈ J k, gradient (fun z => (f j z).toReal) (x (k - τd k j))) y : ℝ) : EReal) :=
    Continuous.lowerSemicontinuous (continuous_coe_real_ereal.comp (by fun_prop))
  exact lsc_add (lsc_add (lsc_add hh.2.2.1 hs hh.1 hsb) hlin (fun y => add_ne_bot' (hh.1 y) (hsb y))
      (fun _ => EReal.coe_ne_bot _)) (lsc_cmul hbr (by positivity))
    (fun y => add_ne_bot' (add_ne_bot' (hh.1 y) (hsb y)) (EReal.coe_ne_bot _))
    (fun y => cmul_ne_bot (by positivity) (bregman_ne_bot w _ (hw.1.1 y)))

lemma Phi_eq (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h)
    {y : EuclideanSpace ℝ (Fin d)} (hf : ∀ n, f n y ≠ ⊤) (hy : h y ≠ ⊤) :
    Phi f h y = (PhiR f h y : EReal) := by
  unfold Phi PhiR
  rw [EReal.coe_add, ← sum_coe, EReal.coe_toReal hy (hh.1 y)]
  congr 1
  exact Finset.sum_congr rfl fun n _ => (EReal.coe_toReal (hf n) ((hB1 n).1.1 y)).symm

lemma Phi_ne_bot (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h)
    (y : EuclideanSpace ℝ (Fin d)) : Phi f h y ≠ ⊥ :=
  add_ne_bot' (sum_ne_bot _ _ fun n => (hB1 n).1.1 y) (hh.1 y)

lemma Phi_fin (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h)
    {y : EuclideanSpace ℝ (Fin d)} (hy : Phi f h y ≠ ⊤) : (∀ n, f n y ≠ ⊤) ∧ h y ≠ ⊤ := by
  classical
  refine ⟨fun n hn => hy ?_, fun H => hy ?_⟩
  · unfold Phi
    rw [sum_eq_top _ _ (fun n => (hB1 n).1.1 y) (Finset.mem_univ n) hn]
    exact EReal.top_add_of_ne_bot (hh.1 y)
  · unfold Phi; rw [H]; exact EReal.add_top_of_ne_bot (sum_ne_bot _ _ fun n => (hB1 n).1.1 y)

lemma Phi_lsc (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h) :
    LowerSemicontinuous (Phi f h) :=
  lsc_add (lsc_sum Finset.univ f (fun i => (hB1 i).1.2.2.1) (fun i y => (hB1 i).1.1 y)) hh.2.2.1
    (fun y => sum_ne_bot _ _ fun n => (hB1 n).1.1 y) hh.1

lemma Phi_cvx (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h)
    (a b : EuclideanSpace ℝ (Fin d)) (ha : Phi f h a ≠ ⊤) (hb : Phi f h b ≠ ⊤) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    Phi f h (s • a + t • b) ≤ ((s * (Phi f h a).toReal + t * (Phi f h b).toReal : ℝ) : EReal) := by
  obtain ⟨hfa, hha⟩ := Phi_fin hB1 hh ha
  obtain ⟨hfb, hhb⟩ := Phi_fin hB1 hh hb
  rw [Phi_eq hB1 hh hfa hha, Phi_eq hB1 hh hfb hhb,
    Phi_eq hB1 hh (fun n => cvx_ne_top (hB1 n).1 (hfa n) (hfb n) hs ht hst)
      (cvx_ne_top hh hha hhb hs ht hst), EReal.toReal_coe, EReal.toReal_coe, EReal.coe_le_coe_iff]
  unfold PhiR
  have h1 := cvx_toReal hh hha hhb hs ht hst
  have h2 : ∑ n, (f n (s • a + t • b)).toReal ≤ ∑ n, (s * (f n a).toReal + t * (f n b).toReal) :=
    Finset.sum_le_sum fun n _ => cvx_toReal (hB1 n).1 (hfa n) (hfb n) hs ht hst
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  linarith

lemma Gp_cvx (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h)
    {a b : EuclideanSpace ℝ (Fin d)} (ha : h a ≠ ⊤) (hb : h b ≠ ⊤) (hwa : w a ≠ ⊤) (hwb : w b ≠ ⊤)
    {t : ℝ} (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    Gp f h J τd x k ((1 - t) • a + t • b) ≤ (1 - t) * Gp f h J τd x k a + t * Gp f h J τd x k b := by
  unfold Gp
  have h1 := cvx_toReal hh ha hb (by linarith : (0:ℝ) ≤ 1 - t) t0 (by ring)
  have h2 : ∑ i ∈ (J k)ᶜ, (f i ((1 - t) • a + t • b)).toReal ≤
      ∑ i ∈ (J k)ᶜ, ((1 - t) * (f i a).toReal + t * (f i b).toReal) :=
    Finset.sum_le_sum fun i _ => cvx_toReal (hB1 i).1 ((hB1 i).2.1 hwa) ((hB1 i).2.1 hwb)
      (by linarith) t0 (by ring)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  linarith

lemma Aff_aff (xk a b : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Aff w xk ((1 - t) • a + t • b) = (1 - t) * Aff w xk a + t * Aff w xk b := by
  unfold Aff
  have : (1 - t) • a + t • b - xk = (1 - t) • (a - xk) + t • (b - xk) := by module
  rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring

lemma PR_cvx (hB1 : AssumptionB1 w f Lc) (hh : TensorAHPE.IsProperClosedConvex h) (hw : IsLegendre w)
    (hα : 0 < α)
    {a b : EuclideanSpace ℝ (Fin d)} (ha : h a ≠ ⊤) (hb : h b ≠ ⊤) (hwa : w a ≠ ⊤) (hwb : w b ≠ ⊤)
    {t : ℝ} (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    PR w f h J τd α x k ((1 - t) • a + t • b) ≤
      (1 - t) * PR w f h J τd α x k a + t * PR w f h J τd α x k b := by
  unfold PR
  have h1 := Gp_cvx (J := J) (τd := τd) (x := x) (k := k) hB1 hh ha hb hwa hwb t0 t1
  have h2 := Aff_aff (w := w) (x k) a b t
  have h3 := cvx_toReal hw.1 hwa hwb (by linarith : (0:ℝ) ≤ 1 - t) t0 (by ring)
  have h4 : (w ((1 - t) • a + t • b)).toReal - Aff w (x k) ((1 - t) • a + t • b) ≤
      (1 - t) * ((w a).toReal - Aff w (x k) a) + t * ((w b).toReal - Aff w (x k) b) := by
    rw [h2]; linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 1 / α)
  linarith

lemma lb {ℓ : ℕ → ℝ} {τ : ℕ} (hw : IsLegendre w) (hB1 : AssumptionB1 w f Lc)
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hα : 0 < α) (hα0 : τ = 0 → α ≤ 1 / ∑ j ∈ J k, Lc j)
    (hαpos : 0 < τ → α ≤ 1 / (ℓ 2 * ∑ j ∈ J k, Lc j))
    (hx : ∀ j ≤ k, x j ∈ interior (AubinLipschitz.effDom w)) :
    ∃ C : ℝ, ∀ y ∈ interior (effDom w), PhiR f h y ≤ PR w f h J τd α x k y + C := by
  classical
  have hzU : ∀ j, x (k - τd k j) ∈ interior (effDom w) := fun j => hx _ (Nat.sub_le _ _)
  have hxk : x k ∈ interior (effDom w) := hx k le_rfl
  have hS : 0 < ∑ j ∈ J k, Lc j := Finset.sum_pos (fun j _ => (hB1 j).2.2.2.1) (hJ k)
  have hℓ2 : 1 ≤ ℓ 2 := hℓ1 ▸ hℓm (by norm_num : (1:ℕ) ≤ 2)
  obtain ⟨lam, hlam0, hlamc, hlamD⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ lam * ∑ j ∈ J k, Lc j ≤ 1 / α ∧
      ∀ j, ∀ y ∈ interior (effDom w),
        Dr w y (x (k - τd k j)) ≤ lam * (Dr w (x k) (x (k - τd k j)) + Dr w y (x k)) := by
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · refine ⟨1, zero_le_one, ?_, ?_⟩
      · have := hα0 h0
        rw [le_div_iff₀ hS] at this
        rw [le_div_iff₀ hα]; linarith
      · intro j y _
        have : τd k j = 0 := Nat.le_zero.1 (h0 ▸ hA0 k j)
        simp only [this, Nat.sub_zero, Dr, sub_self, inner_zero_right]; linarith
    · refine ⟨ℓ 2, by linarith, ?_, ?_⟩
      · have := hαpos hpos
        rw [le_div_iff₀ (by positivity)] at this
        rw [le_div_iff₀ hα]; linarith
      · intro j y hy
        let v : ℕ → EuclideanSpace ℝ (Fin d) := fun i =>
          if i ≤ 1 then x (k - τd k j) else if i = 2 then x k else y
        have hv : ∀ i, v i ∈ interior (effDom w) := by
          intro i; have := hzU j; simp only [v]; split_ifs <;> assumption
        have := hB4 hpos v hv 1 3 le_rfl (by norm_num)
        have hI : Finset.Ico 1 3 = {1, 2} := by decide
        rw [hI, Finset.sum_pair (by norm_num)] at this
        simp only [v] at this
        norm_num at this
        rw [bregman_eq w _ (interior_subset hy) (hw.1.1 y),
          bregman_eq w _ (interior_subset hxk) (hw.1.1 _),
          bregman_eq w _ (interior_subset hy) (hw.1.1 y)] at this
        exact_mod_cast this
  refine ⟨∑ j ∈ J k, ((f j (x (k - τd k j))).toReal
      - inner ℝ (gradient (fun q => (f j q).toReal) (x (k - τd k j))) (x (k - τd k j))
      + Lc j * lam * Dr w (x k) (x (k - τd k j))), fun y hy => ?_⟩
  have hDnn : 0 ≤ Dr w y (x k) := Dr_nonneg hw hxk (interior_subset hy)
  have hterm : ∀ j ∈ J k, (f j y).toReal ≤ ((f j (x (k - τd k j))).toReal
      - inner ℝ (gradient (fun q => (f j q).toReal) (x (k - τd k j))) (x (k - τd k j))
      + Lc j * lam * Dr w (x k) (x (k - τd k j)))
      + inner ℝ (gradient (fun q => (f j q).toReal) (x (k - τd k j))) y
      + Lc j * lam * Dr w y (x k) := by
    intro j _
    have h1 := desc hw hB1 j hy (hzU j)
    have h2 := mul_le_mul_of_nonneg_left (hlamD j y hy) (hB1 j).2.2.2.1.le
    rw [inner_sub_right] at h1
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, ← Finset.sum_mul] at hsum
  have hsplit := Finset.sum_add_sum_compl (J k) (fun n => (f n y).toReal)
  have h3 : (∑ j ∈ J k, Lc j * lam) * Dr w y (x k) ≤ 1 / α * Dr w y (x k) := by
    apply mul_le_mul_of_nonneg_right _ hDnn
    rw [← Finset.sum_mul]; linarith
  unfold PhiR PR Gp gv
  rw [← Dr_eq_Aff]
  linarith

lemma interior_min (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hB1 : AssumptionB1 w f Lc) (hα : 0 < α)
    {p : EuclideanSpace ℝ (Fin d)} (hph : h p ≠ ⊤) (hpU : p ∈ interior (effDom w))
    {z : EuclideanSpace ℝ (Fin d)} (hzQ : z ∈ closure (effDom w))
    (hzmin : ∀ y ∈ closure (effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) :
    z ∈ interior (effDom w) := by
  by_contra hzU
  have hpw : w p ≠ ⊤ := interior_subset hpU
  have hPp := Phik_eq (J := J) (τd := τd) (α := α) (x := x) (k := k) hB1 hh hw hph hpw
  have hzle := hzmin p (subset_closure (interior_subset hpU))
  have hzt : Phik w f h J τd α x k z ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hPp]; exact EReal.coe_ne_top _) hzle
  have hhz : h z ≠ ⊤ := fun H => hzt (Phik_top hB1 hh hw hα (Or.inl H))
  have hwz : w z ≠ ⊤ := fun H => hzt (Phik_top hB1 hh hw hα (Or.inr H))
  have hPz := Phik_eq (J := J) (τd := τd) (α := α) (x := x) (k := k) hB1 hh hw hhz hwz
  have hDc := dom_convex hw.1
  have hzfr : z ∈ frontier (effDom w) := ⟨hzQ, hzU⟩
  set t : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 2) with ht_def
  have ht0 : ∀ n, 0 < t n := fun n => by simp only [ht_def]; positivity
  have ht2 : ∀ n, t n ≤ 1 / 2 := fun n => by
    simp only [ht_def]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
  set u : ℕ → EuclideanSpace ℝ (Fin d) := fun n => z + t n • (p - z) with hu_def
  have hu_eq : ∀ n, u n = (1 - t n) • z + t n • p := fun n => by simp only [hu_def]; module
  have huU : ∀ n, u n ∈ interior (effDom w) := fun n => by
    rw [hu_eq]
    exact hDc.openSegment_closure_interior_subset_interior hzQ hpU
      ⟨1 - t n, t n, by linarith [ht2 n], ht0 n, by ring, rfl⟩
  have htt : Tendsto t atTop (𝓝 0) := by
    simp only [ht_def]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hut : Tendsto u atTop (𝓝 z) := by
    have := (htt.smul_const (p - z)).const_add z
    simpa using this
  have hgrad := hw.2.2.2.1 u z hzfr huU hut
  have hcont : ContinuousAt (fun y => (w y).toReal) p :=
    ((hw.2.2.1 p hpU).differentiableAt (isOpen_interior.mem_nhds hpU)).continuousAt
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  obtain ⟨δ2, hδ2, hδ2'⟩ := Metric.isOpen_iff.1 isOpen_interior p hpU
  set r := min δ1 δ2 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < δ1 := by have := min_le_left δ1 δ2; rw [hr]; linarith
  have hr2 : r < δ2 := by have := min_le_right δ1 δ2; rw [hr]; linarith
  set c : ℝ := 1 / α with hc_def
  have hc : 0 < c := by positivity
  set gp := gradient (fun y => (w y).toReal) p with hgp
  set K1 := 1 + ‖gp‖ * ‖z - p‖ with hK1
  set W := (Gp f h J τd x k p - Gp f h J τd x k z) - c * (Aff w (x k) p - Aff w (x k) z) with hW
  have hK1pos : 0 < K1 := by positivity
  obtain ⟨n, hn⟩ := (hgrad.eventually_ge_atTop ((K1 + 1 + |W| / c) / r)).exists
  set g := gradient (fun y => (w y).toReal) (u n) with hg
  set tn := t n with htn
  have hbound_pos : 0 < (K1 + 1 + |W| / c) / r := by positivity
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le hbound_pos hn
  set q := p + (r / ‖g‖) • g with hq
  have hqd : dist q p = r := by
    rw [hq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ hgpos.ne']
  have hqU : q ∈ interior (effDom w) := hδ2' (by rw [Metric.mem_ball, hqd]; exact hr2)
  have hqF : (w q).toReal ≤ (w p).toReal + 1 := by
    have := hδ1' (show dist q p < δ1 by rw [hqd]; exact hr1)
    rw [Real.dist_eq] at this; linarith [(abs_lt.1 this).2]
  have s1 := sg hw (huU n) hwz
  have s2 := sg hw (huU n) (interior_subset hqU : w q ≠ ⊤)
  have s3 := sg hw hpU (interior_subset (huU n) : w (u n) ≠ ⊤)
  set I := inner ℝ g (p - z) with hI
  have e1 : inner ℝ g (z - u n) = -tn * I := by
    have : z - u n = (-tn) • (p - z) := by simp only [hu_def, htn]; module
    rw [this, real_inner_smul_right]
  have e2 : inner ℝ g (q - u n) = (1 - tn) * I + r * ‖g‖ := by
    have : q - u n = (1 - tn) • (p - z) + (r / ‖g‖) • g := by simp only [hq, hu_def, htn]; module
    rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have : r / ‖g‖ * ‖g‖ ^ 2 = r * ‖g‖ := by field_simp
    rw [this]
  have e3 : -(‖gp‖ * ‖z - p‖) ≤ inner ℝ gp (u n - p) := by
    have : u n - p = (1 - tn) • (z - p) := by simp only [hu_def, htn]; module
    rw [this, real_inner_smul_right]
    have h1 := neg_abs_le (inner ℝ gp (z - p))
    have h2 := abs_real_inner_le_norm gp (z - p)
    have h3 : 0 ≤ 1 - tn := by linarith [ht2 n]
    have h4 : 1 - tn ≤ 1 := by linarith [ht0 n]
    have h5 : 0 ≤ ‖gp‖ * ‖z - p‖ := by positivity
    nlinarith
  rw [e1] at s1
  rw [e2] at s2
  have hn' : K1 + 1 + |W| / c ≤ ‖g‖ * r := (div_le_iff₀ hr0).1 hn
  have hA : (1 - tn) * I ≤ -1 - |W| / c := by nlinarith
  have hIneg : I < 0 := by
    by_contra hcon; push Not at hcon
    have := mul_nonneg (show 0 ≤ 1 - tn by linarith [ht2 n]) hcon
    have : 0 ≤ |W| / c := by positivity
    linarith
  have htI : tn * I ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (ht0 n).le hIneg.le
  have hI2 : I ≤ -1 - |W| / c := by nlinarith
  have hcI : c * I ≤ -c - |W| := by
    have := mul_le_mul_of_nonneg_left hI2 hc.le
    rw [mul_sub, mul_div_cancel₀ _ hc.ne'] at this; linarith
  have hWI : W + c * I < 0 := by linarith [le_abs_self W]
  have hdec : tn * (W + c * I) < 0 := mul_neg_of_pos_of_neg (ht0 n) hWI
  have hhu : h (u n) ≠ ⊤ := by
    rw [hu_eq]; exact cvx_ne_top hh hhz hph (by linarith [ht2 n]) (ht0 n).le (by ring)
  have hwu : w (u n) ≠ ⊤ := interior_subset (huU n)
  have hG := Gp_cvx (J := J) (τd := τd) (x := x) (k := k) hB1 hh hhz hph hwz hpw (ht0 n).le
    (by linarith [ht2 n])
  have hAf := Aff_aff (w := w) (x k) z p tn
  rw [← hu_eq] at hG hAf
  have hFu : (w (u n)).toReal ≤ (w z).toReal + tn * I := by linarith
  have hcu : c * ((w (u n)).toReal - Aff w (x k) (u n)) ≤
      c * ((w z).toReal + tn * I - ((1 - tn) * Aff w (x k) z + tn * Aff w (x k) p)) := by
    apply mul_le_mul_of_nonneg_left _ hc.le; rw [hAf]; linarith
  have hlt : PR w f h J τd α x k (u n) < PR w f h J τd α x k z := by
    unfold PR; rw [← hc_def]; linarith
  have := hzmin (u n) (subset_closure (interior_subset (huU n)))
  rw [hPz, Phik_eq hB1 hh hw hhu hwu, EReal.coe_le_coe_iff] at this
  linarith

lemma unique_min (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hB1 : AssumptionB1 w f Lc) (hα : 0 < α)
    {p : EuclideanSpace ℝ (Fin d)} (hph : h p ≠ ⊤) (hpU : p ∈ interior (effDom w))
    {z1 z2 : EuclideanSpace ℝ (Fin d)} (h1U : z1 ∈ interior (effDom w)) (h2U : z2 ∈ interior (effDom w))
    (h1 : ∀ y ∈ closure (effDom w), Phik w f h J τd α x k z1 ≤ Phik w f h J τd α x k y)
    (h2 : ∀ y ∈ closure (effDom w), Phik w f h J τd α x k z2 ≤ Phik w f h J τd α x k y) :
    z1 = z2 := by
  by_contra hne
  have hUQ : interior (effDom w) ⊆ closure (effDom w) := interior_subset.trans subset_closure
  have hpw : w p ≠ ⊤ := interior_subset hpU
  have hPp := Phik_eq (J := J) (τd := τd) (α := α) (x := x) (k := k) hB1 hh hw hph hpw
  have fin : ∀ z ∈ interior (effDom w),
      (∀ y ∈ closure (effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) → h z ≠ ⊤ := by
    intro z _ hz H
    have := hz p (hUQ hpU)
    rw [Phik_top hB1 hh hw hα (Or.inl H), hPp] at this
    exact EReal.coe_ne_top _ (top_le_iff.1 this)
  have hh1 := fin z1 h1U h1
  have hh2 := fin z2 h2U h2
  have hw1 : w z1 ≠ ⊤ := interior_subset h1U
  have hw2 : w z2 ≠ ⊤ := interior_subset h2U
  have e12 := h1 z2 (hUQ h2U)
  have e21 := h2 z1 (hUQ h1U)
  rw [Phik_eq hB1 hh hw hh1 hw1, Phik_eq hB1 hh hw hh2 hw2, EReal.coe_le_coe_iff] at e12 e21
  set m := (1 - (1/2 : ℝ)) • z1 + (1/2 : ℝ) • z2 with hm
  have hmU : m ∈ interior (effDom w) :=
    (dom_convex hw.1).interior h1U h2U (by norm_num) (by norm_num) (by norm_num)
  have hhm : h m ≠ ⊤ := cvx_ne_top hh hh1 hh2 (by norm_num) (by norm_num) (by norm_num)
  have hwm : w m ≠ ⊤ := interior_subset hmU
  have hG := Gp_cvx (J := J) (τd := τd) (x := x) (k := k) hB1 hh hh1 hh2 hw1 hw2
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hAf := Aff_aff (w := w) (x k) z1 z2 (1/2)
  have hs := hw.2.2.2.2.2 h1U h2U hne (by norm_num : (0:ℝ) < 1 - 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num)
  simp only [smul_eq_mul] at hs
  rw [← hm] at hG hAf hs
  have hc : (0:ℝ) < 1 / α := by positivity
  have hcm : 1 / α * ((w m).toReal - Aff w (x k) m) <
      1 / α * ((1 - 1/2) * ((w z1).toReal - Aff w (x k) z1) + 1/2 * ((w z2).toReal - Aff w (x k) z2)) := by
    apply mul_lt_mul_of_pos_left _ hc; rw [hAf]; linarith
  have hlt : PR w f h J τd α x k m < PR w f h J τd α x k z1 := by
    unfold PR at *; linarith
  have := h1 m (hUQ hmU)
  rw [Phik_eq hB1 hh hw hh1 hw1, Phik_eq hB1 hh hw hhm hwm, EReal.coe_le_coe_iff] at this
  linarith

theorem main {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (Lc : Fin N → ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ)
    (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ)
    (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hXne : (optSet w f h).Nonempty) (hXc : IsCompact (optSet w f h))
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hB1 : AssumptionB1 w f Lc)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hdom : (AubinLipschitz.effDom h ∩ interior (AubinLipschitz.effDom w)).Nonempty)
    (hα : 0 < α) (hα0 : τ = 0 → α ≤ 1 / ∑ j ∈ J k, Lc j)
    (hαpos : 0 < τ → α ≤ 1 / (ℓ 2 * ∑ j ∈ J k, Lc j))
    (hx : ∀ j ≤ k, x j ∈ interior (AubinLipschitz.effDom w)) :
    (∃! z, z ∈ closure (AubinLipschitz.effDom w) ∧
        ∀ y ∈ closure (AubinLipschitz.effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) ∧
    ∀ z, z ∈ closure (AubinLipschitz.effDom w) →
        (∀ y ∈ closure (AubinLipschitz.effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) →
        z ∈ interior (AubinLipschitz.effDom w) := by
  classical
  obtain ⟨p, hph, hpU⟩ := hdom
  have hpw : w p ≠ ⊤ := interior_subset hpU
  have hUQ : interior (effDom w) ⊆ closure (effDom w) := interior_subset.trans subset_closure
  have hDc := dom_convex hw.1
  have hint : ∀ z, z ∈ closure (effDom w) →
      (∀ y ∈ closure (effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) →
      z ∈ interior (effDom w) :=
    fun z hz hmin => interior_min hw hh hB1 hα hph hpU hz hmin
  refine ⟨?_, hint⟩
  obtain ⟨C, hC⟩ := lb (h := h) hw hB1 hJ hA0 hℓm hℓ1 hB4 hα hα0 hαpos hx
  set Pp := PR w f h J τd α x k p with hPp_def
  have hPp : Phik w f h J τd α x k p = (Pp : EReal) := Phik_eq hB1 hh hw hph hpw
  obtain ⟨x0, hx0⟩ := hXne
  have hXiff : ∀ y, y ∈ optSet w f h ↔ y ∈ closure (effDom w) ∧
      ∀ y' ∈ closure (effDom w), Phi f h y ≤ Phi f h y' := by
    intro y; unfold optSet PhiStar
    constructor
    · rintro ⟨hy, he⟩; exact ⟨hy, fun y' hy' => he ▸ iInf₂_le y' hy'⟩
    · rintro ⟨hy, hm⟩
      exact ⟨hy, le_antisymm (le_iInf₂ fun y' hy' => hm y' hy') (iInf₂_le y hy)⟩
  have hfp : ∀ n, f n p ≠ ⊤ := fun n => (hB1 n).2.1 hpw
  have hx0t : Phi f h x0 ≠ ⊤ := by
    have := ((hXiff x0).1 hx0).2 p (hUQ hpU)
    rw [Phi_eq hB1 hh hfp hph] at this
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this
  obtain ⟨B, hB⟩ := level_bounded (Phi f h) (closure (effDom w)) (optSet w f h) hDc.closure
    isClosed_closure (Phi_lsc hB1 hh) (Phi_ne_bot hB1 hh) (Phi_cvx hB1 hh) hXiff hXc x0 hx0 hx0t
    (Pp + C)
  set K0 := {y | y ∈ interior (effDom w) ∧ Phik w f h J τd α x k y ≤ Pp} with hK0
  have hK0b : Bornology.IsBounded K0 := by
    rw [Metric.isBounded_iff_subset_closedBall x0]
    refine ⟨B, fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hwy : w y ≠ ⊤ := interior_subset hy.1
    have hhy : h y ≠ ⊤ := fun H => by
      have := hy.2; rw [Phik_top hB1 hh hw hα (Or.inl H)] at this
      exact EReal.coe_ne_top _ (top_le_iff.1 this)
    have h1 := hy.2
    rw [Phik_eq hB1 hh hw hhy hwy, EReal.coe_le_coe_iff] at h1
    have h2 := hC y hy.1
    apply hB y (hUQ hy.1)
    rw [Phi_eq hB1 hh (fun n => (hB1 n).2.1 hwy) hhy, EReal.coe_le_coe_iff]; linarith
  have hKc : IsCompact (closure K0) := hK0b.isCompact_closure
  have hpK : p ∈ K0 := ⟨hpU, hPp.le⟩
  obtain ⟨z, hzK, hzmin⟩ := ((Phik_lsc (J := J) (τd := τd) (x := x) (k := k) hB1 hh hw hα).lowerSemicontinuousOn
    _).exists_isMinOn ⟨p, subset_closure hpK⟩ hKc
  have hzQ : z ∈ closure (effDom w) := closure_mono (fun y hy => interior_subset hy.1) hzK
  have hzp : Phik w f h J τd α x k z ≤ Pp := (isMinOn_iff.1 hzmin _ (subset_closure hpK)).trans hPp.le
  have hzt : Phik w f h J τd α x k z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hzp
  have hhz : h z ≠ ⊤ := fun H => hzt (Phik_top hB1 hh hw hα (Or.inl H))
  have hwz : w z ≠ ⊤ := fun H => hzt (Phik_top hB1 hh hw hα (Or.inr H))
  have hPz := Phik_eq (J := J) (τd := τd) (α := α) (x := x) (k := k) hB1 hh hw hhz hwz
  have hglob : ∀ y ∈ closure (effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y := by
    intro y hyQ
    rcases le_or_gt (Pp : EReal) (Phik w f h J τd α x k y) with hle | hlt
    · exact hzp.trans hle
    have hyt : Phik w f h J τd α x k y ≠ ⊤ := ne_top_of_lt hlt
    have hhy : h y ≠ ⊤ := fun H => hyt (Phik_top hB1 hh hw hα (Or.inl H))
    have hwy : w y ≠ ⊤ := fun H => hyt (Phik_top hB1 hh hw hα (Or.inr H))
    rw [Phik_eq hB1 hh hw hhy hwy, EReal.coe_lt_coe_iff] at hlt
    rw [hPz, Phik_eq hB1 hh hw hhy hwy, EReal.coe_le_coe_iff]
    apply lim_le (c := Pp)
    intro t ht
    have hytU : (1 - t) • y + t • p ∈ interior (effDom w) :=
      hDc.openSegment_closure_interior_subset_interior hyQ hpU
        ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩
    have hhyt : h ((1 - t) • y + t • p) ≠ ⊤ :=
      cvx_ne_top hh hhy hph (by linarith [ht.2]) ht.1.le (by ring)
    have hwyt : w ((1 - t) • y + t • p) ≠ ⊤ := interior_subset hytU
    have hcv := PR_cvx (J := J) (τd := τd) (x := x) (k := k) hB1 hh hw hα hhy hph hwy hpw ht.1.le ht.2.le
    have hyK : (1 - t) • y + t • p ∈ K0 := ⟨hytU, by
      rw [Phik_eq hB1 hh hw hhyt hwyt, EReal.coe_le_coe_iff]; nlinarith [ht.1, ht.2]⟩
    have := isMinOn_iff.1 hzmin _ (subset_closure hyK)
    rw [hPz, Phik_eq hB1 hh hw hhyt hwyt, EReal.coe_le_coe_iff] at this
    linarith
  refine ⟨z, ⟨hzQ, hglob⟩, fun z' hz' => ?_⟩
  exact unique_min hw hh hB1 hα hph hpU (hint z' hz'.1 hz'.2) (hint z hzQ hglob) hz'.2 hglob

end PL

end PLIAGP31

open PLIAG in
theorem solution {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (Lc : Fin N → ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ)
    (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ)
    (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hXne : (optSet w f h).Nonempty) (hXc : IsCompact (optSet w f h))
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hB1 : AssumptionB1 w f Lc)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hdom : (AubinLipschitz.effDom h ∩ interior (AubinLipschitz.effDom w)).Nonempty)
    (hα : 0 < α) (hα0 : τ = 0 → α ≤ 1 / ∑ j ∈ J k, Lc j)
    (hαpos : 0 < τ → α ≤ 1 / (ℓ 2 * ∑ j ∈ J k, Lc j))
    (hx : ∀ j ≤ k, x j ∈ interior (AubinLipschitz.effDom w)) :
    (∃! z, z ∈ closure (AubinLipschitz.effDom w) ∧
        ∀ y ∈ closure (AubinLipschitz.effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) ∧
    ∀ z, z ∈ closure (AubinLipschitz.effDom w) →
        (∀ y ∈ closure (AubinLipschitz.effDom w), Phik w f h J τd α x k z ≤ Phik w f h J τd α x k y) →
        z ∈ interior (AubinLipschitz.effDom w) :=
  PLIAGP31.main w f h Lc ℓ τ J τd α x k hw hh hXne hXc hJ hA0 hB1 hℓm hℓ1 hB4 hdom hα hα0 hαpos hx
