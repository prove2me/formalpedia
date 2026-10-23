-- Prove2me | solution 1 for RobustOpt2009.Bernstein.lemma_B_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:15:20.552626+00:00
-- url     : https://prove2.me/submissions/8e8731c8-3236-494a-a710-c7945d27eed9

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

open Set RobustOpt2009.Bernstein in
theorem solution {n : ℕ} (H : Space n → EReal) (a : ℝ)
    (hbot : ∀ z, H z ≠ ⊥)
    (hconv : Convex ℝ {p : Space n × ℝ | H p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ c, IsClosed (sublevel H c))
    (hzero : (a : EReal) < H 0)
    (hdom : (0 : Space n) ∈ interior {z | H z < ⊤})
    (hstrict : ∃ z, H z < (a : EReal)) :
    (∀ z, ∃ r : ℝ, perspectiveValue H a z = (r : EReal)) ∧
    Convex ℝ {p : Space n × ℝ | perspectiveValue H a p.1 ≤ (p.2 : EReal)} ∧
    closure (initialCone H a) = {z | perspectiveValue H a z ≤ 0} ∧
    (closure (initialCone H a)).Nonempty ∧
    IsClosed (closure (initialCone H a)) ∧ Convex ℝ (closure (initialCone H a)) ∧
    (0 : Space n) ∈ closure (initialCone H a) ∧
    (∀ z ∈ closure (initialCone H a), ∀ t : ℝ, 0 ≤ t →
      t • z ∈ closure (initialCone H a)) :=
  X8RB.x8_core H a hbot hconv hlsc hzero hdom hstrict
