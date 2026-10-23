-- Prove2me | solution 1 for RobustOpt2009.Bernstein.theorem_B_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:29:06.671506+00:00
-- url     : https://prove2.me/submissions/695fc0da-6da4-4c42-bbc7-13dc7f185fca

import Definitions.Def_RobustOpt2009_Bernstein_Setup

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


open Set Filter Topology RobustOpt2009.Bernstein

namespace X8RB4

lemma x8_pair_smul_left {n : ℕ} (t : ℝ) (z y : Space n) :
    pairing (t • z) y = t * pairing z y := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma x8_pair_comb {n : ℕ} (s t : ℝ) (z y1 y2 : Space n) :
    pairing z (s • y1 + t • y2) = s * pairing z y1 + t * pairing z y2 := by
  simp only [pairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma x8_pair_cont {n : ℕ} (y : Space n) : Continuous fun z : Space n => pairing z y := by
  unfold pairing; fun_prop

lemma x8_pair_zero {n : ℕ} (y : Space n) : pairing 0 y = 0 := by
  simp [pairing]

theorem x8_B12 {n m : ℕ} (d : Setup n m) (ρ : ℝ) (e : Space n)
    (hPsi : ConvexOn ℝ univ d.Phi) (hQ2 : Q2 d)
    (hρ : ρ < d.Phi 0)
    (hlim : ∀ z, ∃ l : EReal, l < (ρ : EReal) ∧
      Tendsto (fun t : ℝ => (d.Phi (z + t • e) : EReal)) atTop (𝓝 l)) :
    (sublevel d.phi (-ρ)).Nonempty ∧ Convex ℝ (sublevel d.phi (-ρ)) ∧
    IsCompact (sublevel d.phi (-ρ)) ∧
    ∀ z, z ∈ dualCone d.Phi ρ ↔
      ∀ u ∈ sublevel d.phi (-ρ), pairing z (d.A u + d.a) ≤ 0 := by
  obtain ⟨hbot, hconv, hcl, hbdd, hrep⟩ := hQ2
  have hle : ∀ w u (q : ℝ), d.phi u = q → pairing w (d.A u + d.a) - q ≤ d.Phi w := by
    intro w u q hu
    have := le_iSup (fun u => ((pairing w (d.A u + d.a) : ℝ) : EReal) - d.phi u) u
    rw [← hrep w, hu] at this
    exact_mod_cast this
  have hfin : ∀ u (r : ℝ), d.phi u ≤ (r : EReal) → ∃ q : ℝ, d.phi u = q := by
    intro u r hr
    induction hx : d.phi u using EReal.rec with
    | bot => exact absurd hx (hbot u)
    | top => rw [hx] at hr; exact absurd hr (not_le.mpr (EReal.coe_lt_top _))
    | coe q => exact ⟨q, rfl⟩
  have hsl : ∃ u, ∃ q : ℝ, d.phi u = q ∧ q < -ρ := by
    have h1 : ((ρ : ℝ) : EReal) < ⨆ u, ((pairing 0 (d.A u + d.a) : ℝ) : EReal) - d.phi u := by
      rw [← hrep 0]; exact_mod_cast hρ
    obtain ⟨u, hu⟩ := lt_iSup_iff.mp h1
    induction hx : d.phi u using EReal.rec with
    | bot => exact absurd hx (hbot u)
    | top => rw [hx, EReal.sub_top] at hu; exact absurd hu (not_lt.mpr bot_le)
    | coe q =>
      rw [hx] at hu
      refine ⟨u, q, hx, ?_⟩
      have : ρ < pairing 0 (d.A u + d.a) - q := by exact_mod_cast hu
      rw [x8_pair_zero] at this
      linarith
  have hlow : ∀ u (q : ℝ), d.phi u = q → -d.Phi 0 ≤ q := by
    intro u q hu
    have := hle 0 u q hu
    rw [x8_pair_zero] at this
    linarith
  obtain ⟨u0, q0, hu0, hq0⟩ := hsl
  have hUne : (sublevel d.phi (-ρ)).Nonempty :=
    ⟨u0, by show d.phi u0 ≤ ((-ρ : ℝ) : EReal); rw [hu0]; exact_mod_cast hq0.le⟩
  have hUc : Convex ℝ (sublevel d.phi (-ρ)) := by
    intro u1 h1 u2 h2 s t hs ht hst
    have h : d.phi (s • u1 + t • u2) ≤ ((s * -ρ + t * -ρ : ℝ) : EReal) :=
      hconv (x := (u1, -ρ)) (y := (u2, -ρ)) h1 h2 hs ht hst
    rwa [show s * -ρ + t * -ρ = -ρ by rw [← add_mul, hst, one_mul]] at h
  have hUk : IsCompact (sublevel d.phi (-ρ)) :=
    Metric.isCompact_of_isClosed_isBounded (hcl _) (hbdd _)
  refine ⟨hUne, hUc, hUk, fun z => ?_⟩
  -- apply the general Lemma B.1.1
  set H : Space n → EReal := fun z => (d.Phi z : EReal) with hH
  have hPc : Continuous d.Phi := continuousOn_univ.mp (hPsi.continuousOn isOpen_univ)
  have hbot' : ∀ z, H z ≠ ⊥ := fun z => EReal.coe_ne_bot _
  have hconv' : Convex ℝ {p : Space n × ℝ | H p.1 ≤ (p.2 : EReal)} := by
    have := hPsi.convex_epigraph
    convert this using 1
    ext p; simp only [H, mem_ofPred_eq, mem_univ, true_and, EReal.coe_le_coe_iff]
  have hlsc' : ∀ c : ℝ, IsClosed {x | H x ≤ (c : EReal)} := by
    intro c
    have : {x | H x ≤ (c : EReal)} = {x : Space n | d.Phi x ≤ c} := by
      ext x; simp only [H, mem_ofPred_eq, EReal.coe_le_coe_iff]
    rw [this]
    exact isClosed_le hPc continuous_const
  have hzero' : (ρ : EReal) < H 0 := by simp only [H]; exact_mod_cast hρ
  have hdom' : (0 : Space n) ∈ interior {z | H z < ⊤} := by
    have : {z | H z < ⊤} = univ := by
      ext z; simp only [H, mem_ofPred_eq, EReal.coe_lt_top, mem_univ]
    rw [this, interior_univ]; trivial
  have hstrict' : ∃ z, H z < (ρ : EReal) := by
    obtain ⟨l, hl, ht⟩ := hlim 0
    obtain ⟨t, htt⟩ := (ht.eventually (gt_mem_nhds hl)).exists
    exact ⟨0 + t • e, htt⟩
  obtain ⟨c1, -, c3, -⟩ := X8RB.x8_core H ρ hbot' hconv' hlsc' hzero' hdom' hstrict'
  have hdual : dualCone d.Phi ρ = closure (X8RB.cone H ρ) := by
    unfold dualCone
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
    have hT : IsClosed {w : Space n | ∀ u ∈ sublevel d.phi (-ρ), pairing w (d.A u + d.a) ≤ 0} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun u => isClosed_iInter fun _ =>
        isClosed_le (x8_pair_cont _) continuous_const
    have hsub : {w : Space n | ∃ α : ℝ, 0 < α ∧ d.Phi (α • w) ≤ ρ} ⊆
        {w : Space n | ∀ u ∈ sublevel d.phi (-ρ), pairing w (d.A u + d.a) ≤ 0} := by
      rintro w ⟨α, hα, hw⟩ u hu
      obtain ⟨q, hq⟩ := hfin u _ hu
      have hq' : q ≤ -ρ := by
        have : d.phi u ≤ ((-ρ : ℝ) : EReal) := hu
        rw [hq] at this; exact_mod_cast this
      have := hle (α • w) u q hq
      rw [x8_pair_smul_left] at this
      by_contra hc; push Not at hc
      nlinarith [mul_pos hα hc]
    exact closure_minimal hsub hT hz
  · intro hz
    obtain ⟨β, hβ, hβc⟩ := X8RB3.x8_lagrange d.phi (fun u => pairing z (d.A u + d.a)) ρ hbot hconv
      (by
        intro u1 u2 s t _ _ hst
        have : d.A (s • u1 + t • u2) + d.a = s • (d.A u1 + d.a) + t • (d.A u2 + d.a) := by
          rw [map_add, map_smul, map_smul]
          ext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination (-(d.a i)) * hst
        rw [this, x8_pair_comb])
      ⟨u0, q0, hu0, hq0⟩
      (by
        intro u q hu hq
        apply hz u
        show d.phi u ≤ ((-ρ : ℝ) : EReal)
        rw [hu]; exact_mod_cast hq)
    set K := d.Phi 0 - ρ
    have hK : 0 < K := by simp only [K]; linarith
    rw [hdual, c3]
    show X8RB.pv H ρ z ≤ ((0 : ℝ) : EReal)
    obtain ⟨r, hr⟩ := c1 z
    rw [hr, EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set β' := β + ε / K
    have hβ' : 0 < β' := by positivity
    have hPhi : d.Phi (β'⁻¹ • z) ≤ ρ + ε / β' := by
      have : (d.Phi (β'⁻¹ • z) : EReal) ≤ ((ρ + ε / β' : ℝ) : EReal) := by
        rw [hrep]
        refine iSup_le fun u => ?_
        induction hx : d.phi u using EReal.rec with
        | bot => exact absurd hx (hbot u)
        | top => rw [EReal.sub_top]; exact bot_le
        | coe q =>
          rw [← EReal.coe_sub, EReal.coe_le_coe_iff, x8_pair_smul_left]
          have h1 := hβc u q hx
          have h2 := hlow u q hx
          have h3 : pairing z (d.A u + d.a) ≤ β' * (q + ρ) + ε := by
            have : -(q + ρ) ≤ K := by simp only [K]; linarith
            have : (ε / K) * (-(q + ρ)) ≤ ε / K * K := mul_le_mul_of_nonneg_left this (by positivity)
            rw [div_mul_cancel₀ _ hK.ne'] at this
            simp only [β']
            nlinarith
          have h4 : β'⁻¹ * pairing z (d.A u + d.a) ≤ (q + ρ) + ε / β' := by
            rw [inv_mul_le_iff₀ hβ', mul_add, mul_div_cancel₀ _ hβ'.ne']
            exact h3
          linarith
      exact_mod_cast this
    have hpv := X8RB.x8_pv_le H ρ z hβ'
    simp only [H] at hpv
    rw [X8RB.x8_T_coe, hr, EReal.coe_le_coe_iff] at hpv
    rw [zero_add]
    have : β' * d.Phi (β'⁻¹ • z) ≤ β' * (ρ + ε / β') := mul_le_mul_of_nonneg_left hPhi hβ'.le
    rw [mul_add, mul_div_cancel₀ _ hβ'.ne'] at this
    linarith

end X8RB4

open Set Filter Topology RobustOpt2009.Bernstein in
theorem solution {n m : ℕ} (d : Setup n m) (ρ : ℝ) (e : Space n)
    (hPsi : ConvexOn ℝ univ d.Phi) (hQ2 : Q2 d)
    (hρ : ρ < d.Phi 0)
    (hlim : ∀ z, ∃ l : EReal, l < (ρ : EReal) ∧
      Tendsto (fun t : ℝ => (d.Phi (z + t • e) : EReal)) atTop (𝓝 l)) :
    (sublevel d.phi (-ρ)).Nonempty ∧ Convex ℝ (sublevel d.phi (-ρ)) ∧
    IsCompact (sublevel d.phi (-ρ)) ∧
    ∀ z, z ∈ dualCone d.Phi ρ ↔
      ∀ u ∈ sublevel d.phi (-ρ), pairing z (d.A u + d.a) ≤ 0 :=
  X8RB4.x8_B12 d ρ e hPsi hQ2 hρ hlim
