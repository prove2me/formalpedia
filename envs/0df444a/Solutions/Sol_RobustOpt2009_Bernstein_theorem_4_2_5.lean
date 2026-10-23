-- Prove2me | solution 1 for RobustOpt2009.Bernstein.theorem_4_2_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:33:39.15589+00:00
-- url     : https://prove2.me/submissions/60f4e445-69ff-4a57-9009-639f092667fa

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


open Set Filter Topology

namespace X8RB3

/-- Lagrange multiplier for one convex constraint under Slater's condition. -/
lemma x8_lagrange {F : Type*} [AddCommGroup F] [Module ℝ F] (ψ : F → EReal) (c : F → ℝ) (ρ : ℝ)
    (hbot : ∀ u, ψ u ≠ ⊥)
    (hconv : Convex ℝ {p : F × ℝ | ψ p.1 ≤ (p.2 : EReal)})
    (hc : ∀ u1 u2 (s t : ℝ), 0 < s → 0 < t → s + t = 1 →
      c (s • u1 + t • u2) = s * c u1 + t * c u2)
    (hslater : ∃ u, ∃ q : ℝ, ψ u = q ∧ q < -ρ)
    (hU : ∀ u (q : ℝ), ψ u = q → q ≤ -ρ → c u ≤ 0) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ u (q : ℝ), ψ u = q → c u ≤ β * (q + ρ) := by
  set A : Set (ℝ × ℝ) := {p | ∃ u, ∃ q : ℝ, ψ u = (q : EReal) ∧ q + ρ ≤ p.1 ∧ p.2 ≤ c u} with hA
  set Q : Set (ℝ × ℝ) := {p | p.1 < 0 ∧ 0 < p.2} with hQ
  have hQc : Convex ℝ Q := by
    rw [convex_iff_forall_pos]
    rintro p ⟨hp1, hp2⟩ r ⟨hr1, hr2⟩ s t hs ht _
    simp only [hQ, mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul]
    constructor <;> nlinarith [mul_pos hs ht]
  have hQo : IsOpen Q :=
    (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_const continuous_snd)
  have hAc : Convex ℝ A := by
    rw [convex_iff_forall_pos]
    rintro p ⟨u1, q1, hu1, h11, h12⟩ r ⟨u2, q2, hu2, h21, h22⟩ s t hs ht hst
    have hm : ψ (s • u1 + t • u2) ≤ ((s * q1 + t * q2 : ℝ) : EReal) := by
      have := hconv (x := (u1, q1)) (y := (u2, q2)) (by simp [hu1]) (by simp [hu2])
        hs.le ht.le hst
      exact this
    obtain ⟨q, hq⟩ : ∃ q : ℝ, ψ (s • u1 + t • u2) = q := by
      induction hx : ψ (s • u1 + t • u2) using EReal.rec with
      | bot => exact absurd hx (hbot _)
      | top => rw [hx] at hm; exact absurd hm (not_le.mpr (EReal.coe_lt_top _))
      | coe r => exact ⟨r, rfl⟩
    rw [hq] at hm
    have hm' : q ≤ s * q1 + t * q2 := by exact_mod_cast hm
    refine ⟨s • u1 + t • u2, q, hq, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have e : ρ = s * ρ + t * ρ := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h11 hs.le, mul_le_mul_of_nonneg_left h21 ht.le]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hc u1 u2 s t hs ht hst]
      nlinarith [mul_le_mul_of_nonneg_left h12 hs.le, mul_le_mul_of_nonneg_left h22 ht.le]
  have hdisj : Disjoint Q A := by
    rw [Set.disjoint_left]
    rintro p ⟨hp1, hp2⟩ ⟨u, q, hu, h1, h2⟩
    have := hU u q hu (by linarith)
    linarith
  obtain ⟨f, w, hfQ, hfA⟩ := geometric_hahn_banach_open hQc hQo hAc hdisj
  set l1 := f (1, 0)
  set l2 := f (0, 1)
  have hf : ∀ x y : ℝ, f (x, y) = x * l1 + y * l2 := by
    intro x y
    have : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hw : 0 ≤ w := by
    by_contra hw; push Not at hw
    set s := -w / (|l2 - l1| + 1)
    have hs : 0 < s := div_pos (by linarith) (by positivity)
    have hsd : s * (|l2 - l1| + 1) = -w := by
      simp only [s]; field_simp
    have h1 : -(|l2 - l1|) ≤ l2 - l1 := neg_abs_le _
    have := hfQ (-s, s) ⟨by linarith, hs⟩
    rw [hf] at this
    nlinarith [mul_le_mul_of_nonneg_left h1 hs.le]
  have hl1 : 0 ≤ l1 := by
    by_contra hl; push Not at hl
    set s := (|w| + |l2| + 1) / (-l1)
    have hs : 0 < s := div_pos (by positivity) (by linarith)
    have hsd : s * (-l1) = |w| + |l2| + 1 := by
      simp only [s]; exact div_mul_cancel₀ _ (by linarith)
    have := hfQ (-s, 1) ⟨by linarith, one_pos⟩
    rw [hf] at this
    nlinarith [le_abs_self w, neg_abs_le l2]
  have hl2 : l2 ≤ 0 := by
    by_contra hl; push Not at hl
    set s := (|w| + |l1| + 1) / l2
    have hs : 0 < s := div_pos (by positivity) hl
    have hsd : s * l2 = |w| + |l1| + 1 := by
      simp only [s]; field_simp
    have := hfQ (-1, s) ⟨by norm_num, hs⟩
    rw [hf] at this
    nlinarith [le_abs_self w, le_abs_self l1]
  have hmain : ∀ u (q : ℝ), ψ u = q → w ≤ (q + ρ) * l1 + c u * l2 := by
    intro u q hu
    have := hfA (q + ρ, c u) ⟨u, q, hu, le_rfl, le_rfl⟩
    rwa [hf] at this
  obtain ⟨u0, q0, hu0, hq0⟩ := hslater
  have h0 := hmain u0 q0 hu0
  rcases hl2.eq_or_lt with h | h
  · exfalso
    rw [h] at h0
    have hl1' : l1 = 0 := by nlinarith
    have := hfQ (-1, 1) ⟨by norm_num, one_pos⟩
    rw [hf, hl1', h] at this
    nlinarith
  · refine ⟨l1 / (-l2), div_nonneg hl1 (by linarith), fun u q hu => ?_⟩
    have := hmain u q hu
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

end X8RB3


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


open Set Filter Topology

namespace X8RB5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem x8_B12g (Ψ : E → ℝ) (ψ : F → EReal) (κ : F → E → ℝ) (ρ : ℝ)
    (hPsi : ConvexOn ℝ univ Ψ)
    (hbot : ∀ u, ψ u ≠ ⊥)
    (hconv : Convex ℝ {p : F × ℝ | ψ p.1 ≤ (p.2 : EReal)})
    (hcl : ∀ c : ℝ, IsClosed {u | ψ u ≤ (c : EReal)})
    (hbdd : ∀ c : ℝ, Bornology.IsBounded {u | ψ u ≤ (c : EReal)})
    (hκlin : ∀ u (t : ℝ) z, κ u (t • z) = t * κ u z)
    (hκcont : ∀ u, Continuous (κ u))
    (hκaff : ∀ u1 u2 (s t : ℝ) z, s + t = 1 → κ (s • u1 + t • u2) z = s * κ u1 z + t * κ u2 z)
    (hle : ∀ w u (q : ℝ), ψ u = q → κ u w - q ≤ Ψ w)
    (hlub : ∀ w (r : ℝ), (∀ u (q : ℝ), ψ u = q → κ u w - q ≤ r) → Ψ w ≤ r)
    (hρ : ρ < Ψ 0)
    (hstrict : ∃ z, Ψ z < ρ) :
    {u | ψ u ≤ ((-ρ : ℝ) : EReal)}.Nonempty ∧ Convex ℝ {u | ψ u ≤ ((-ρ : ℝ) : EReal)} ∧
    IsCompact {u | ψ u ≤ ((-ρ : ℝ) : EReal)} ∧
    ∀ z, z ∈ closure {z | ∃ α : ℝ, 0 < α ∧ Ψ (α • z) ≤ ρ} ↔
      ∀ u ∈ {u | ψ u ≤ ((-ρ : ℝ) : EReal)}, κ u z ≤ 0 := by
  have hκ0 : ∀ u, κ u 0 = 0 := by
    intro u; have := hκlin u 0 0; rw [zero_smul, zero_mul] at this; exact this
  have hfin : ∀ u (r : ℝ), ψ u ≤ (r : EReal) → ∃ q : ℝ, ψ u = q := by
    intro u r hr
    induction hx : ψ u using EReal.rec with
    | bot => exact absurd hx (hbot u)
    | top => rw [hx] at hr; exact absurd hr (not_le.mpr (EReal.coe_lt_top _))
    | coe q => exact ⟨q, rfl⟩
  have hsl : ∃ u, ∃ q : ℝ, ψ u = q ∧ q < -ρ := by
    by_contra hcon
    push Not at hcon
    have := hlub 0 ρ (fun u q hu => by rw [hκ0]; linarith [hcon u q hu])
    linarith
  have hlow : ∀ u (q : ℝ), ψ u = q → -Ψ 0 ≤ q := by
    intro u q hu
    have := hle 0 u q hu
    rw [hκ0] at this
    linarith
  obtain ⟨u0, q0, hu0, hq0⟩ := hsl
  have hUne : {u | ψ u ≤ ((-ρ : ℝ) : EReal)}.Nonempty :=
    ⟨u0, by show ψ u0 ≤ ((-ρ : ℝ) : EReal); rw [hu0]; exact_mod_cast hq0.le⟩
  have hUc : Convex ℝ {u | ψ u ≤ ((-ρ : ℝ) : EReal)} := by
    intro u1 h1 u2 h2 s t hs ht hst
    have h : ψ (s • u1 + t • u2) ≤ ((s * -ρ + t * -ρ : ℝ) : EReal) :=
      hconv (x := (u1, -ρ)) (y := (u2, -ρ)) h1 h2 hs ht hst
    rwa [show s * -ρ + t * -ρ = -ρ by rw [← add_mul, hst, one_mul]] at h
  have hUk : IsCompact {u | ψ u ≤ ((-ρ : ℝ) : EReal)} :=
    Metric.isCompact_of_isClosed_isBounded (hcl _) (hbdd _)
  refine ⟨hUne, hUc, hUk, fun z => ?_⟩
  set H : E → EReal := fun z => (Ψ z : EReal) with hH
  have hPc : Continuous Ψ := continuousOn_univ.mp (hPsi.continuousOn isOpen_univ)
  have hbot' : ∀ z, H z ≠ ⊥ := fun z => EReal.coe_ne_bot _
  have hconv' : Convex ℝ {p : E × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    have := hPsi.convex_epigraph
    convert this using 1
    ext p; simp only [H, mem_ofPred_eq, mem_univ, true_and, EReal.coe_le_coe_iff]
  have hlsc' : ∀ c : ℝ, IsClosed {x | H x ≤ (c : EReal)} := by
    intro c
    have : {x | H x ≤ (c : EReal)} = {x : E | Ψ x ≤ c} := by
      ext x; simp only [H, mem_ofPred_eq, EReal.coe_le_coe_iff]
    rw [this]
    exact isClosed_le hPc continuous_const
  have hzero' : (ρ : EReal) < H 0 := by simp only [H]; exact_mod_cast hρ
  have hdom' : (0 : E) ∈ interior {z | H z < ⊤} := by
    have : {z | H z < ⊤} = univ := by
      ext z; simp only [H, mem_ofPred_eq, EReal.coe_lt_top, mem_univ]
    rw [this, interior_univ]; trivial
  have hstrict' : ∃ z, H z < (ρ : EReal) := by
    obtain ⟨z, hz⟩ := hstrict; exact ⟨z, by simp only [H]; exact_mod_cast hz⟩
  obtain ⟨c1, -, c3, -⟩ := X8RB.x8_core H ρ hbot' hconv' hlsc' hzero' hdom' hstrict'
  have hdual : closure {z | ∃ α : ℝ, 0 < α ∧ Ψ (α • z) ≤ ρ} = closure (X8RB.cone H ρ) := by
    congr 1
    ext w
    simp only [mem_ofPred_eq, X8RB.cone, H]
    constructor
    · rintro ⟨α, hα, h⟩
      exact ⟨α⁻¹, inv_pos.mpr hα, by rw [inv_inv]; exact_mod_cast h⟩
    · rintro ⟨β, hβ, h⟩
      exact ⟨β⁻¹, inv_pos.mpr hβ, by exact_mod_cast h⟩
  constructor
  · intro hz
    have hT : IsClosed {w : E | ∀ u ∈ {u | ψ u ≤ ((-ρ : ℝ) : EReal)}, κ u w ≤ 0} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun u => isClosed_iInter fun _ =>
        isClosed_le (hκcont _) continuous_const
    have hsub : {w : E | ∃ α : ℝ, 0 < α ∧ Ψ (α • w) ≤ ρ} ⊆
        {w : E | ∀ u ∈ {u | ψ u ≤ ((-ρ : ℝ) : EReal)}, κ u w ≤ 0} := by
      rintro w ⟨α, hα, hw⟩ u hu
      obtain ⟨q, hq⟩ := hfin u _ hu
      have hq' : q ≤ -ρ := by
        have : ψ u ≤ ((-ρ : ℝ) : EReal) := hu
        rw [hq] at this; exact_mod_cast this
      have := hle (α • w) u q hq
      rw [hκlin] at this
      by_contra hc; push Not at hc
      nlinarith [mul_pos hα hc]
    exact closure_minimal hsub hT hz
  · intro hz
    obtain ⟨β, hβ, hβc⟩ := X8RB3.x8_lagrange ψ (fun u => κ u z) ρ hbot hconv
      (fun u1 u2 s t _ _ hst => hκaff u1 u2 s t z hst)
      ⟨u0, q0, hu0, hq0⟩
      (by
        intro u q hu hq
        apply hz u
        show ψ u ≤ ((-ρ : ℝ) : EReal)
        rw [hu]; exact_mod_cast hq)
    set K := Ψ 0 - ρ
    have hK : 0 < K := by simp only [K]; linarith
    rw [hdual, c3]
    show X8RB.pv H ρ z ≤ ((0 : ℝ) : EReal)
    obtain ⟨r, hr⟩ := c1 z
    rw [hr, EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set β' := β + ε / K
    have hβ' : 0 < β' := by positivity
    have hPhi : Ψ (β'⁻¹ • z) ≤ ρ + ε / β' := by
      refine hlub _ _ fun u q hx => ?_
      rw [hκlin]
      have h1 := hβc u q hx
      have h2 := hlow u q hx
      have h3 : κ u z ≤ β' * (q + ρ) + ε := by
        have : -(q + ρ) ≤ K := by simp only [K]; linarith
        have : (ε / K) * (-(q + ρ)) ≤ ε / K * K := mul_le_mul_of_nonneg_left this (by positivity)
        rw [div_mul_cancel₀ _ hK.ne'] at this
        simp only [β']
        nlinarith
      have h4 : β'⁻¹ * κ u z ≤ (q + ρ) + ε / β' := by
        rw [inv_mul_le_iff₀ hβ', mul_add, mul_div_cancel₀ _ hβ'.ne']
        exact h3
      linarith
    have hpv := X8RB.x8_pv_le H ρ z hβ'
    simp only [H] at hpv
    rw [X8RB.x8_T_coe, hr, EReal.coe_le_coe_iff] at hpv
    rw [zero_add]
    have : β' * Ψ (β'⁻¹ • z) ≤ β' * (ρ + ε / β') := mul_le_mul_of_nonneg_left hPhi hβ'.le
    rw [mul_add, mul_div_cancel₀ _ hβ'.ne'] at this
    linarith

end X8RB5


open MeasureTheory Set Filter Topology

namespace X8RB6

theorem x8_425 {L M : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ) (phi : (Fin M → ℝ) → EReal)
    (A : (Fin M → ℝ) →ₗ[ℝ] (Fin L → ℝ)) (a : Fin L → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hPhi : ConvexOn ℝ univ Phi) (hPhi0 : Phi 0 = 0)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w)))
    (hbot : ∀ u, phi u ≠ ⊥)
    (hconv : Convex ℝ {p : (Fin M → ℝ) × ℝ | phi p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c : ℝ, IsClosed {u | phi u ≤ (c : EReal)})
    (hbounded : ∀ c : ℝ, Bornology.IsBounded {u | phi u ≤ (c : EReal)})
    (hrep : ∀ w, (Phi w : EReal) =
      ⨆ u, ((∑ i, w i * (A u + a) i : ℝ) : EReal) - phi u) :
    let U : Set (Fin M → ℝ) := {u | phi u ≤ (Real.log (1 / ε) : EReal)}
    let Z : Set (ℝ × (Fin L → ℝ)) :=
      closure {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
    let V : (ℝ × (Fin L → ℝ)) → EReal := fun z =>
      ⨅ β : {b : ℝ // 0 < b},
        ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)
    U.Nonempty ∧ Convex ℝ U ∧ IsCompact U ∧
    (∀ z : ℝ × (Fin L → ℝ), z ∈ Z ↔
      ∀ ζ ∈ (fun u => A u + a) '' U, z.1 + ∑ i, ζ i * z.2 i ≤ 0) ∧
    (∀ z, ∃ r : ℝ, V z = (r : EReal)) ∧
    (∀ z, z ∈ Z ↔ V z ≤ 0) ∧
    (∀ z, V z ≤ 0 → P {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} ≤ ENNReal.ofReal ε) := by
  intro U Z V
  have h422 := X8RB2.x8_422 P Phi ε hε0 hε1 hPhi hPhi0 hmgf
  dsimp only at h422
  obtain ⟨d1, d2, -, d4, -⟩ := h422
  have hla : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hκlin : ∀ u (t : ℝ) (z : ℝ × (Fin L → ℝ)),
      (t • z).1 + ∑ i, (t • z).2 i * (A u + a) i = t * (z.1 + ∑ i, z.2 i * (A u + a) i) := by
    intro u t z
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum,
      mul_assoc]
  have hκaff : ∀ u1 u2 (s t : ℝ) (z : ℝ × (Fin L → ℝ)), s + t = 1 →
      z.1 + ∑ i, z.2 i * (A (s • u1 + t • u2) + a) i =
        s * (z.1 + ∑ i, z.2 i * (A u1 + a) i) + t * (z.1 + ∑ i, z.2 i * (A u2 + a) i) := by
    intro u1 u2 s t z hst
    have hv : A (s • u1 + t • u2) + a = s • (A u1 + a) + t • (A u2 + a) := by
      rw [map_add, map_smul, map_smul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(a i)) * hst
    have hsum : ∑ i, z.2 i * (s • (A u1 + a) + t • (A u2 + a)) i =
        s * ∑ i, z.2 i * (A u1 + a) i + t * ∑ i, z.2 i * (A u2 + a) i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hv]
    linear_combination (-z.1) * hst + hsum
  have hle : ∀ (w : ℝ × (Fin L → ℝ)) u (q : ℝ), phi u = q →
      (w.1 + ∑ i, w.2 i * (A u + a) i) - q ≤ w.1 + Phi w.2 := by
    intro w u q hu
    have := le_iSup (fun u => ((∑ i, w.2 i * (A u + a) i : ℝ) : EReal) - phi u) u
    rw [← hrep w.2, hu] at this
    have : (∑ i, w.2 i * (A u + a) i) - q ≤ Phi w.2 := by exact_mod_cast this
    linarith
  have hlub : ∀ (w : ℝ × (Fin L → ℝ)) (r : ℝ),
      (∀ u (q : ℝ), phi u = q → (w.1 + ∑ i, w.2 i * (A u + a) i) - q ≤ r) →
      w.1 + Phi w.2 ≤ r := by
    intro w r h
    have : (Phi w.2 : EReal) ≤ ((r - w.1 : ℝ) : EReal) := by
      rw [hrep]
      refine iSup_le fun u => ?_
      induction hx : phi u using EReal.rec with
      | bot => exact absurd hx (hbot u)
      | top => rw [EReal.sub_top]; exact bot_le
      | coe q =>
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have := h u q hx
        linarith
    have : Phi w.2 ≤ r - w.1 := by exact_mod_cast this
    linarith
  have hPsi : ConvexOn ℝ univ (fun z : ℝ × (Fin L → ℝ) => z.1 + Phi z.2) := by
    have h1 : ConvexOn ℝ univ (fun z : ℝ × (Fin L → ℝ) => z.1) :=
      (LinearMap.fst ℝ ℝ (Fin L → ℝ)).convexOn convex_univ
    have h2 : ConvexOn ℝ univ (fun z : ℝ × (Fin L → ℝ) => Phi z.2) :=
      hPhi.comp_linearMap (LinearMap.snd ℝ ℝ (Fin L → ℝ))
    exact h1.add h2
  obtain ⟨g1, g2, g3, g4⟩ := X8RB5.x8_B12g (fun z : ℝ × (Fin L → ℝ) => z.1 + Phi z.2) phi
    (fun u z => z.1 + ∑ i, z.2 i * (A u + a) i) (Real.log ε) hPsi hbot hconv hlsc hbounded
    hκlin (fun u => by fun_prop) hκaff hle hlub
    (by simp only [Prod.fst_zero, Prod.snd_zero, hPhi0, add_zero]; exact hla)
    ⟨(Real.log ε - 1, 0), by simp only [hPhi0, add_zero]; linarith⟩
  have hU : U = {u | phi u ≤ ((-Real.log ε : ℝ) : EReal)} := by
    simp only [U, one_div, Real.log_inv]
  rw [hU]
  refine ⟨g1, g2, g3, fun z => ?_, d2, fun z => ?_, fun z hz => d4 z hz⟩
  · have e1 : Z = closure {z : ℝ × (Fin L → ℝ) | ∃ α : ℝ, 0 < α ∧
        (α • z).1 + Phi (α • z).2 ≤ Real.log ε} := by
      simp only [Z, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [e1, g4 z, forall_mem_image]
    refine forall₂_congr fun u _ => ?_
    simp only [mul_comm]
  · show z ∈ closure {z : ℝ × (Fin L → ℝ) | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
      ↔ V z ≤ 0
    rw [d1]; exact Iff.rfl

end X8RB6

open MeasureTheory Set in
theorem solution {L M : ℕ} (P : Measure (Fin L → ℝ)) [IsProbabilityMeasure P]
    (Phi : (Fin L → ℝ) → ℝ) (phi : (Fin M → ℝ) → EReal)
    (A : (Fin M → ℝ) →ₗ[ℝ] (Fin L → ℝ)) (a : Fin L → ℝ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hPhi : ConvexOn ℝ univ Phi) (hPhi0 : Phi 0 = 0)
    (hmgf : ∀ w : Fin L → ℝ,
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (∑ i, w i * ζ i)) ∂P) ≤
        ENNReal.ofReal (Real.exp (Phi w)))
    (hbot : ∀ u, phi u ≠ ⊥)
    (hconv : Convex ℝ {p : (Fin M → ℝ) × ℝ | phi p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c : ℝ, IsClosed {u | phi u ≤ (c : EReal)})
    (hbounded : ∀ c : ℝ, Bornology.IsBounded {u | phi u ≤ (c : EReal)})
    (hrep : ∀ w, (Phi w : EReal) =
      ⨆ u, ((∑ i, w i * (A u + a) i : ℝ) : EReal) - phi u) :
    let U : Set (Fin M → ℝ) := {u | phi u ≤ (Real.log (1 / ε) : EReal)}
    let Z : Set (ℝ × (Fin L → ℝ)) :=
      closure {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}
    let V : (ℝ × (Fin L → ℝ)) → EReal := fun z =>
      ⨅ β : {b : ℝ // 0 < b},
        ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)
    U.Nonempty ∧ Convex ℝ U ∧ IsCompact U ∧
    (∀ z : ℝ × (Fin L → ℝ), z ∈ Z ↔
      ∀ ζ ∈ (fun u => A u + a) '' U, z.1 + ∑ i, ζ i * z.2 i ≤ 0) ∧
    (∀ z, ∃ r : ℝ, V z = (r : EReal)) ∧
    (∀ z, z ∈ Z ↔ V z ≤ 0) ∧
    (∀ z, V z ≤ 0 → P {ζ | 0 < z.1 + ∑ i, z.2 i * ζ i} ≤ ENNReal.ofReal ε) :=
  X8RB6.x8_425 P Phi phi A a ε hε0 hε1 hPhi hPhi0 hmgf hbot hconv hlsc hbounded hrep
