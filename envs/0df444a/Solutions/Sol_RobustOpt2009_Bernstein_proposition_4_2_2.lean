-- Prove2me | solution 1 for RobustOpt2009.Bernstein.proposition_4_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:20:53.781218+00:00
-- url     : https://prove2.me/submissions/02dd1824-ea49-45ec-94d3-54e6adf4218c

import Mathlib

open Set Filter Topology

noncomputable section

namespace X8RB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- perspective value, same body as `perspectiveValue`. -/
def pv (H : E → EReal) (a : ℝ) (z : E) : EReal :=
  ⨅ β : {b : ℝ // 0 < b}, (β.val : EReal) * H (β.val⁻¹ • z) - ((β.val * a : ℝ) : EReal)

def cone (H : E → EReal) (a : ℝ) : Set E :=
  {z | ∃ β : ℝ, 0 < β ∧ H (β⁻¹ • z) ≤ (a : EReal)}

lemma x8_T_coe {β r a : ℝ} :
    (β : EReal) * (r : EReal) - ((β * a : ℝ) : EReal) = ((β * r - β * a : ℝ) : EReal) := by
  norm_cast

lemma x8_T_top {β a : ℝ} (hβ : 0 < β) :
    (β : EReal) * (⊤ : EReal) - ((β * a : ℝ) : EReal) = ⊤ := by
  rw [EReal.coe_mul_top_of_pos hβ, EReal.top_sub_coe]

/-- value of a term in terms of the real value of H -/
lemma x8_T_lt {H : E → EReal} {a β : ℝ} (hβ : 0 < β) {x : E} {c : ℝ} (hb : H x ≠ ⊥)
    (h : (β : EReal) * H x - ((β * a : ℝ) : EReal) < (c : EReal)) :
    ∃ r : ℝ, H x = r ∧ β * r - β * a < c := by
  induction hx : H x using EReal.rec with
  | bot => exact absurd hx hb
  | top => rw [hx, x8_T_top hβ] at h; simp at h
  | coe r => rw [hx, x8_T_coe] at h; exact ⟨r, rfl, by exact_mod_cast h⟩

variable (H : E → EReal) (a : ℝ)

/-- affine minorant from separation -/
lemma x8_minorant (hbot : ∀ z, H z ≠ ⊥)
    (hconv : Convex ℝ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c : ℝ, IsClosed {x | H x ≤ (c : EReal)})
    (hzero : (a : EReal) < H 0) (h0 : H 0 < ⊤) :
    ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ), a < c ∧ ∀ x (r : ℝ), H x = r → ℓ x + c ≤ r := by
  have hls : LowerSemicontinuous H := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    induction y using EReal.rec with
    | bot =>
      convert isClosed_empty
      ext x; simp [hbot x]
    | top => convert isClosed_univ; ext x; simp
    | coe c => exact hlsc c
  have hcl : IsClosed {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    have := hls.isClosed_epigraph
    exact this.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  have hnot : ((0 : E), a) ∉ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    simp only [mem_ofPred_eq, not_le]; exact hzero
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point hconv hcl hnot
  set s := f ((0 : E), (1 : ℝ))
  have hsplit : ∀ x t, f (x, t) = f (x, 0) + t * s := by
    intro x t
    have : ((x, t) : E × ℝ) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hfa : f ((0 : E), a) = a * s := by rw [hsplit, Prod.mk_zero_zero, map_zero, zero_add]
  obtain ⟨h0r, h0e⟩ : ∃ r : ℝ, H 0 = r := by
    induction hx : H 0 using EReal.rec with
    | bot => exact absurd hx (hbot 0)
    | top => rw [hx] at h0; simp at h0
    | coe r => exact ⟨r, rfl⟩
  have hs : s < 0 := by
    set t := max h0r (a + 1)
    have hmem : ((0 : E), t) ∈ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
      simp only [mem_ofPred_eq, h0e]; exact_mod_cast le_max_left _ _
    have h1 := hf _ hmem
    rw [hsplit] at h1
    have h2 : f ((0 : E), (0 : ℝ)) = 0 := by
      rw [Prod.mk_zero_zero, map_zero]
    rw [h2, zero_add] at h1
    have ht : a + 1 ≤ t := le_max_right _ _
    by_contra hns
    push Not at hns
    nlinarith
  refine ⟨-(1 / s) • (f.comp (ContinuousLinearMap.inl ℝ E ℝ)), u / s, ?_, ?_⟩
  · rw [hfa] at hu
    rw [lt_div_iff_of_neg hs]; linarith
  · intro x r hx
    have hmem : (x, r) ∈ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
      simp only [mem_ofPred_eq, hx]; exact le_rfl
    have h1 := hf _ hmem
    rw [hsplit] at h1
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
      Function.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    have : -(1 / s) * f (x, 0) + u / s = (u - f (x, 0)) / s := by field_simp; ring
    rw [this, div_le_iff_of_neg hs]
    linarith

lemma x8_T_le {H : E → EReal} {a β : ℝ} (hβ : 0 < β) {x : E} {h : ℝ} (hb : H x ≠ ⊥)
    (hle : H x ≤ (h : EReal)) :
    (β : EReal) * H x - ((β * a : ℝ) : EReal) ≤ ((β * h - β * a : ℝ) : EReal) := by
  induction hx : H x using EReal.rec with
  | bot => exact absurd hx hb
  | top => rw [hx] at hle; simp at hle
  | coe r =>
    rw [hx] at hle
    rw [x8_T_coe]
    have : r ≤ h := by exact_mod_cast hle
    exact_mod_cast (by nlinarith)

lemma x8_pv_le (z : E) {β : ℝ} (hβ : 0 < β) :
    pv H a z ≤ (β : EReal) * H (β⁻¹ • z) - ((β * a : ℝ) : EReal) :=
  iInf_le (fun b : {b : ℝ // 0 < b} =>
    (b.val : EReal) * H (b.val⁻¹ • z) - ((b.val * a : ℝ) : EReal)) ⟨β, hβ⟩

lemma x8_pv_fin (hbot : ∀ z, H z ≠ ⊥)
    (hconv : Convex ℝ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c : ℝ, IsClosed {x | H x ≤ (c : EReal)})
    (hzero : (a : EReal) < H 0) (hdom : (0 : E) ∈ interior {z | H z < ⊤}) (z : E) :
    pv H a z = ((pv H a z).toReal : EReal) := by
  have h0 : H 0 < ⊤ := (interior_subset hdom : (0 : E) ∈ {z | H z < ⊤})
  obtain ⟨ℓ, c, hac, hℓ⟩ := x8_minorant H a hbot hconv hlsc hzero h0
  have hlow : ((ℓ z : ℝ) : EReal) ≤ pv H a z := by
    refine le_iInf fun b => ?_
    obtain ⟨β, hβ⟩ := b
    show ((ℓ z : ℝ) : EReal) ≤ (β : EReal) * H (β⁻¹ • z) - ((β * a : ℝ) : EReal)
    induction hx : H (β⁻¹ • z) using EReal.rec with
    | bot => exact absurd hx (hbot _)
    | top => rw [x8_T_top hβ]; exact le_top
    | coe r =>
      rw [x8_T_coe]
      have h1 := hℓ _ r hx
      rw [map_smul, smul_eq_mul] at h1
      have h2 : ℓ z ≤ β * r - β * a := by
        have : β * (β⁻¹ * ℓ z + c) ≤ β * r := mul_le_mul_of_nonneg_left h1 hβ.le
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul] at this
        nlinarith
      exact_mod_cast h2
  have hup : pv H a z < ⊤ := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hdom)
    set β := 2 * (‖z‖ + 1) / ε
    have hβ : 0 < β := by positivity
    have hin : β⁻¹ • z ∈ Metric.ball (0 : E) ε := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
      have : β⁻¹ = ε / (2 * (‖z‖ + 1)) := by simp only [β, inv_div]
      rw [this, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg z]
    have hfin : H (β⁻¹ • z) < ⊤ := hball hin
    refine lt_of_le_of_lt (x8_pv_le H a z hβ) ?_
    induction hx : H (β⁻¹ • z) using EReal.rec with
    | bot => exact absurd hx (hbot _)
    | top => rw [hx] at hfin; simp at hfin
    | coe r => rw [x8_T_coe]; exact EReal.coe_lt_top _
  exact (EReal.coe_toReal hup.ne (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow)).symm

lemma x8_pv_convex (hbot : ∀ z, H z ≠ ⊥)
    (hconv : Convex ℝ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)})
    (hg : ∀ z, pv H a z = ((pv H a z).toReal : EReal)) :
    ConvexOn ℝ univ (fun z => (pv H a z).toReal) := by
  refine ⟨convex_univ, fun z1 _ z2 _ μ ν hμ hν hμν => ?_⟩
  simp only [smul_eq_mul]
  rcases hμ.eq_or_lt with h | hμ'
  · subst h; simp at hμν; subst hμν; simp
  rcases hν.eq_or_lt with h | hν'
  · subst h; simp at hμν; subst hμν; simp
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set g1 := (pv H a z1).toReal
  set g2 := (pv H a z2).toReal
  have e1 : pv H a z1 < ((g1 + ε : ℝ) : EReal) := by
    rw [hg z1]; exact_mod_cast (by linarith)
  have e2 : pv H a z2 < ((g2 + ε : ℝ) : EReal) := by
    rw [hg z2]; exact_mod_cast (by linarith)
  obtain ⟨⟨β1, hβ1⟩, hb1⟩ := iInf_lt_iff.mp e1
  obtain ⟨⟨β2, hβ2⟩, hb2⟩ := iInf_lt_iff.mp e2
  obtain ⟨h1, hh1, hl1⟩ := x8_T_lt hβ1 (hbot _) hb1
  obtain ⟨h2, hh2, hl2⟩ := x8_T_lt hβ2 (hbot _) hb2
  set β := μ * β1 + ν * β2
  have hβ : 0 < β := by positivity
  have hp1 : ((β1⁻¹ • z1, h1) : E × ℝ) ∈ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    simp only [mem_ofPred_eq, hh1]; exact le_rfl
  have hp2 : ((β2⁻¹ • z2, h2) : E × ℝ) ∈ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    simp only [mem_ofPred_eq, hh2]; exact le_rfl
  have hw : μ * β1 / β + ν * β2 / β = 1 := by field_simp; rfl
  have hm := hconv hp1 hp2 (by positivity) (by positivity) hw
  simp only [mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at hm
  have hx : (μ * β1 / β) • β1⁻¹ • z1 + (ν * β2 / β) • β2⁻¹ • z2 = β⁻¹ • (μ • z1 + ν • z2) := by
    rw [smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
    congr 2
    · field_simp
    · field_simp
  rw [hx] at hm
  have hT := x8_T_le (a := a) hβ (hbot _) hm
  have hpv := (x8_pv_le H a (μ • z1 + ν • z2) hβ).trans hT
  rw [hg] at hpv
  have hpv' := EReal.coe_le_coe_iff.mp hpv
  have ee : β * (μ * β1 / β * h1 + ν * β2 / β * h2) - β * a
      = μ * (β1 * h1 - β1 * a) + ν * (β2 * h2 - β2 * a) := by
    field_simp; ring
  rw [ee] at hpv'
  have := mul_lt_mul_of_pos_left hl1 hμ'
  have := mul_lt_mul_of_pos_left hl2 hν'
  nlinarith

theorem x8_core (hbot : ∀ z, H z ≠ ⊥)
    (hconv : Convex ℝ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c : ℝ, IsClosed {x | H x ≤ (c : EReal)})
    (hzero : (a : EReal) < H 0)
    (hdom : (0 : E) ∈ interior {z | H z < ⊤})
    (hstrict : ∃ z, H z < (a : EReal)) :
    (∀ z, ∃ r : ℝ, pv H a z = (r : EReal)) ∧
    Convex ℝ {p : E × ℝ | pv H a p.1 ≤ (p.2 : EReal)} ∧
    closure (cone H a) = {z | pv H a z ≤ 0} ∧
    (closure (cone H a)).Nonempty ∧
    IsClosed (closure (cone H a)) ∧ Convex ℝ (closure (cone H a)) ∧
    (0 : E) ∈ closure (cone H a) ∧
    (∀ z ∈ closure (cone H a), ∀ t : ℝ, 0 ≤ t → t • z ∈ closure (cone H a)) := by
  have hg := x8_pv_fin H a hbot hconv hlsc hzero hdom
  set g := fun z => (pv H a z).toReal with hgdef
  have hgc : ConvexOn ℝ univ g := x8_pv_convex H a hbot hconv hg
  have hgcont : Continuous g := continuousOn_univ.mp (hgc.continuousOn isOpen_univ)
  have hS : {z | pv H a z ≤ 0} = {z | g z ≤ 0} := by
    ext z; simp only [mem_ofPred_eq]; rw [hg z]; norm_cast
  obtain ⟨z0, hz0⟩ := hstrict
  have hz0c : z0 ∈ cone H a := ⟨1, one_pos, by rw [inv_one, one_smul]; exact hz0.le⟩
  have hsub : cone H a ⊆ {z | g z ≤ 0} := by
    rintro z ⟨β, hβ, hle⟩
    have := (x8_pv_le H a z hβ).trans (x8_T_le hβ (hbot _) hle)
    rw [hg z, sub_self] at this
    exact_mod_cast this
  have hgz0 : g z0 < 0 := by
    have h1 := x8_pv_le H a z0 one_pos
    rw [inv_one, one_smul] at h1
    induction hx : H z0 using EReal.rec with
    | bot => exact absurd hx (hbot _)
    | top => rw [hx] at hz0; simp at hz0
    | coe r =>
      rw [hx] at hz0 h1
      rw [x8_T_coe, hg z0] at h1
      have := EReal.coe_le_coe_iff.mp h1
      have : r < a := by exact_mod_cast hz0
      linarith
  have hneg : ∀ w, g w < 0 → w ∈ cone H a := by
    intro w hw
    have : pv H a w < ((0 : ℝ) : EReal) := by rw [hg w]; exact_mod_cast hw
    obtain ⟨⟨β, hβ⟩, hb⟩ := iInf_lt_iff.mp this
    obtain ⟨r, hr, hl⟩ := x8_T_lt hβ (hbot _) hb
    refine ⟨β, hβ, ?_⟩
    rw [hr]
    have : r < a := by nlinarith
    exact_mod_cast this.le
  have hcl : closure (cone H a) = {z | pv H a z ≤ 0} := by
    rw [hS]
    apply le_antisymm
    · exact closure_minimal hsub (isClosed_le hgcont continuous_const)
    · intro z hz
      have hT : Tendsto (fun s : ℝ => (1 - s) • z + s • z0) (𝓝[>] 0) (𝓝 z) := by
        have := ((by fun_prop : Continuous fun s : ℝ => (1 - s) • z + s • z0).tendsto 0)
        simp only [sub_zero, one_smul, zero_smul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto hT ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      apply hneg
      have h1 := hgc.2 (mem_univ z) (mem_univ z0) (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1.le
        (by ring)
      simp only [smul_eq_mul] at h1
      have hz' : g z ≤ 0 := hz
      have : (1 - s) * g z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hs.2]) hz'
      nlinarith [hs.1]
  have hcone : ∀ t : ℝ, 0 < t → MapsTo (fun z : E => t • z) (cone H a) (cone H a) := by
    rintro t ht z ⟨β, hβ, hle⟩
    refine ⟨t * β, by positivity, ?_⟩
    rw [smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
    exact hle
  have h0 : (0 : E) ∈ closure (cone H a) := by
    have hT : Tendsto (fun t : ℝ => t • z0) (𝓝[>] 0) (𝓝 0) := by
      have := ((by fun_prop : Continuous fun t : ℝ => t • z0).tendsto 0)
      simp only [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hT ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hcone t ht hz0c
  refine ⟨fun z => ⟨_, hg z⟩, ?_, hcl, ⟨z0, subset_closure hz0c⟩, isClosed_closure, ?_, h0, ?_⟩
  · have := hgc.convex_epigraph
    convert this using 1
    ext p; simp only [mem_ofPred_eq, mem_univ, true_and]; rw [hg p.1]; norm_cast
  · rw [hcl, hS]
    have := hgc.convex_le 0
    simpa using this
  · intro z hz t ht
    rcases ht.eq_or_lt with h | ht'
    · subst h; rw [zero_smul]; exact h0
    · exact ((hcone t ht').closure (continuous_const_smul t)) hz

end X8RB


open MeasureTheory Set Filter Topology

namespace X8RB2

lemma x8_chernoff {L : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w)))
    (z1 : ℝ) (z2 : Fin L → ℝ) (δ β : ℝ) (hβ : 0 < β) (c : ℝ)
    (hc : (z1 - δ) / β + Phi (β⁻¹ • z2) ≤ c) :
    P {ζ | δ < z1 + ∑ i, z2 i * ζ i} ≤ ENNReal.ofReal (Real.exp c) := by
  set f : (Fin L → ℝ) → ENNReal := fun ζ => ENNReal.ofReal (Real.exp ((z1 - δ) / β)) *
    ENNReal.ofReal (Real.exp (∑ i, (β⁻¹ • z2) i * ζ i)) with hf
  have hfe : ∀ ζ, f ζ = ENNReal.ofReal (Real.exp ((z1 + ∑ i, z2 i * ζ i - δ) / β)) := by
    intro ζ
    simp only [hf]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [div_eq_inv_mul]
    rw [show β⁻¹ * (z1 + ∑ i, z2 i * ζ i - δ) = β⁻¹ * z1 - β⁻¹ * δ + β⁻¹ * ∑ i, z2 i * ζ i by ring,
      Finset.mul_sum]
    simp only [mul_assoc]; ring
  have hsub : {ζ | δ < z1 + ∑ i, z2 i * ζ i} ⊆ {ζ | 1 ≤ f ζ} := by
    intro ζ hζ
    simp only [mem_setOf_eq] at hζ ⊢
    rw [hfe, ENNReal.one_le_ofReal, Real.one_le_exp_iff]
    exact div_nonneg (by linarith) hβ.le
  have hmeas : Measurable f := by fun_prop
  calc P {ζ | δ < z1 + ∑ i, z2 i * ζ i} ≤ P {ζ | 1 ≤ f ζ} := measure_mono hsub
    _ = 1 * P {ζ | 1 ≤ f ζ} := (one_mul _).symm
    _ ≤ ∫⁻ ζ, f ζ ∂P := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable 1
    _ = ENNReal.ofReal (Real.exp ((z1 - δ) / β)) *
          ∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, (β⁻¹ • z2) i * ζ i)) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp ((z1 - δ) / β)) * ENNReal.ofReal (Real.exp (Phi (β⁻¹ • z2))) := by
        gcongr; exact hmgf _
    _ = ENNReal.ofReal (Real.exp ((z1 - δ) / β + Phi (β⁻¹ • z2))) := by
        rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp c) := by
        gcongr

end X8RB2


open MeasureTheory Set Filter Topology

namespace X8RB2

theorem x8_422 {L : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hPhi : ConvexOn ℝ univ Phi) (hPhi0 : Phi 0 = 0)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w))) :
    let Z : Set (ℝ × (Fin L → ℝ)) :=
      closure {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
    let V : (ℝ × (Fin L → ℝ)) → EReal := fun z =>
      ⨅ β : {b : ℝ // 0 < b},
        ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)
    let S : Set (ℝ × (Fin L → ℝ)) := {z | V z ≤ 0}
    Z = S ∧ (∀ z, ∃ r : ℝ, V z = (r : EReal)) ∧
    Convex ℝ {p : (ℝ × (Fin L → ℝ)) × ℝ | V p.1 ≤ (p.2 : EReal)} ∧
    (∀ z ∈ S, P {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} ≤ ENNReal.ofReal ε) ∧
    IsClosed S ∧ Convex ℝ S ∧ (0 : ℝ × (Fin L → ℝ)) ∈ S ∧
    (∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S) ∧
    ((-1, 0) : ℝ × (Fin L → ℝ)) ∈ interior S ∧
    ((1, 0) : ℝ × (Fin L → ℝ)) ∉ S := by
  intro Z V S
  set a := Real.log ε with ha
  set H : (ℝ × (Fin L → ℝ)) → EReal := fun z => ((z.1 + Phi z.2 : ℝ) : EReal) with hH
  have hPc : Continuous Phi := continuousOn_univ.mp (hPhi.continuousOn isOpen_univ)
  have hla : a < 0 := Real.log_neg hε0 hε1
  have hlog : Real.log (1 / ε) = -a := by rw [one_div, Real.log_inv]
  have hVpv : V = X8RB.pv H a := by
    funext z
    simp only [V, X8RB.pv, H]
    congr 1; funext β
    rw [X8RB.x8_T_coe]
    congr 1
    obtain ⟨β, hβ⟩ := β
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hlog]
    field_simp
    ring
  have hfc : ConvexOn ℝ univ (fun z : ℝ × (Fin L → ℝ) => z.1 + Phi z.2) := by
    have h1 : ConvexOn ℝ univ (fun z : ℝ × (Fin L → ℝ) => z.1) :=
      (LinearMap.fst ℝ ℝ (Fin L → ℝ)).convexOn convex_univ
    have h2 : ConvexOn ℝ univ (fun z : ℝ × (Fin L → ℝ) => Phi z.2) := by
      have := hPhi.comp_linearMap (LinearMap.snd ℝ ℝ (Fin L → ℝ))
      exact this
    exact h1.add h2
  have hbot : ∀ z, H z ≠ ⊥ := fun z => EReal.coe_ne_bot _
  have hconv : Convex ℝ {p : (ℝ × (Fin L → ℝ)) × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    have := hfc.convex_epigraph
    convert this using 1
    ext p; simp only [H, mem_ofPred_eq, mem_univ, true_and, EReal.coe_le_coe_iff]
  have hlsc : ∀ c : ℝ, IsClosed {x | H x ≤ (c : EReal)} := by
    intro c
    have : {x | H x ≤ (c : EReal)} = {x : ℝ × (Fin L → ℝ) | x.1 + Phi x.2 ≤ c} := by
      ext x; simp only [H, mem_ofPred_eq, EReal.coe_le_coe_iff]
    rw [this]
    exact isClosed_le (by fun_prop) continuous_const
  have hzero : (a : EReal) < H 0 := by
    simp only [H, Prod.fst_zero, Prod.snd_zero, hPhi0, add_zero]; exact_mod_cast hla
  have hdom : (0 : ℝ × (Fin L → ℝ)) ∈ interior {z | H z < ⊤} := by
    have : {z | H z < ⊤} = univ := by ext z; simp only [H, mem_ofPred_eq, EReal.coe_lt_top, mem_univ]
    rw [this, interior_univ]; trivial
  have hstrict : ∃ z, H z < (a : EReal) := ⟨(a - 1, 0), by
    show ((a - 1 + Phi 0 : ℝ) : EReal) < a
    rw [hPhi0]; exact_mod_cast (by linarith)⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := X8RB.x8_core H a hbot hconv hlsc hzero hdom hstrict
  have hZ : Z = closure (X8RB.cone H a) := by
    simp only [Z]
    congr 1
    ext z
    simp only [mem_ofPred_eq, X8RB.cone, H, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    constructor
    · rintro ⟨α, hα, h⟩
      exact ⟨α⁻¹, inv_pos.mpr hα, by rw [inv_inv]; exact_mod_cast h⟩
    · rintro ⟨β, hβ, h⟩
      exact ⟨β⁻¹, inv_pos.mpr hβ, by exact_mod_cast h⟩
  have hSc : S = closure (X8RB.cone H a) := by
    simp only [S]; rw [hVpv, c3]
  refine ⟨by rw [hZ, hSc], fun z => by rw [hVpv]; exact c1 z, by rw [hVpv]; exact c2, ?_,
    by rw [hSc]; exact c5, by rw [hSc]; exact c6, by rw [hSc]; exact c7,
    by rw [hSc]; exact c8, ?_, ?_⟩
  · intro z hz
    have hz' : V z ≤ 0 := hz
    set s : ℕ → Set (Fin L → ℝ) := fun n => {ζ | (1 / ((n:ℝ) + 1)) < z.1 + ∑ i, z.2 i * ζ i}
    have hmono : Monotone s := by
      intro m n hmn ζ hζ
      simp only [s, mem_ofPred_eq] at hζ ⊢
      refine lt_of_le_of_lt ?_ hζ
      gcongr
    have hU : (⋃ n, s n) = {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} := by
      ext ζ; simp only [mem_iUnion, s, mem_ofPred_eq]; constructor
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
      · intro h; obtain ⟨n, hn⟩ := exists_nat_one_div_lt h; exact ⟨n, hn⟩
    have hb : ∀ n, P (s n) ≤ ENNReal.ofReal ε := by
      intro n
      set δ : ℝ := 1 / ((n:ℝ)+1)
      have hδ : 0 < δ := by positivity
      have : V z < ((δ:ℝ):EReal) := lt_of_le_of_lt hz' (by exact_mod_cast hδ)
      obtain ⟨⟨β, hβ⟩, hb⟩ := iInf_lt_iff.mp this
      have hb' : z.1 + β * Phi (β⁻¹ • z.2) + β * Real.log (1/ε) < δ := by exact_mod_cast hb
      have hc : (z.1 - δ)/β + Phi (β⁻¹ • z.2) ≤ Real.log ε := by
        rw [hlog] at hb'
        have e : (z.1 - δ)/β + Phi (β⁻¹ • z.2) = (z.1 - δ + β * Phi (β⁻¹ • z.2))/β := by
          field_simp
        rw [e, div_le_iff₀ hβ]; linarith
      have := x8_chernoff P Phi hmgf z.1 z.2 δ β hβ _ hc
      rwa [Real.exp_log hε0] at this
    rw [← hU]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hb
  · set Lg := Real.log (1/ε)
    have hL : 0 < Lg := by rw [hlog]; linarith
    set β0 : ℝ := 1 / (Lg + 1)
    have hβ0 : 0 < β0 := by positivity
    set U := {z : ℝ × (Fin L → ℝ) | z.1 + β0 * Phi (β0⁻¹ • z.2) + β0 * Lg < 0}
    have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
    have hUS : U ⊆ S := by
      intro z hz
      show V z ≤ 0
      refine (iInf_le _ ⟨β0, hβ0⟩).trans ?_
      exact_mod_cast hz.le
    apply interior_mono hUS
    rw [hUo.interior_eq]
    show (-1:ℝ) + β0 * Phi (β0⁻¹ • (0 : Fin L → ℝ)) + β0 * Lg < 0
    rw [smul_zero, hPhi0, mul_zero, add_zero]
    have : β0 * Lg < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    linarith
  · intro h
    have h' : V (1, 0) ≤ 0 := h
    have : ((1:ℝ):EReal) ≤ V (1,0) := by
      refine le_iInf fun ⟨β, hβ⟩ => ?_
      simp only [smul_zero, hPhi0, mul_zero, add_zero]
      have : 0 ≤ β * Real.log (1/ε) := by rw [hlog]; nlinarith
      exact_mod_cast (by linarith)
    exact absurd (EReal.coe_le_coe_iff.mp (this.trans (h'.trans_eq EReal.coe_zero.symm)))
      (by norm_num)

end X8RB2

open MeasureTheory Set in
theorem solution {L : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hPhi : ConvexOn ℝ univ Phi) (hPhi0 : Phi 0 = 0)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w))) :
    let Z : Set (ℝ × (Fin L → ℝ)) :=
      closure {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
    let V : (ℝ × (Fin L → ℝ)) → EReal := fun z =>
      ⨅ β : {b : ℝ // 0 < b},
        ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)
    let S : Set (ℝ × (Fin L → ℝ)) := {z | V z ≤ 0}
    Z = S ∧ (∀ z, ∃ r : ℝ, V z = (r : EReal)) ∧
    Convex ℝ {p : (ℝ × (Fin L → ℝ)) × ℝ | V p.1 ≤ (p.2 : EReal)} ∧
    (∀ z ∈ S, P {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} ≤ ENNReal.ofReal ε) ∧
    IsClosed S ∧ Convex ℝ S ∧ (0 : ℝ × (Fin L → ℝ)) ∈ S ∧
    (∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S) ∧
    ((-1, 0) : ℝ × (Fin L → ℝ)) ∈ interior S ∧
    ((1, 0) : ℝ × (Fin L → ℝ)) ∉ S :=
  X8RB2.x8_422 P Phi ε hε0 hε1 hPhi hPhi0 hmgf
