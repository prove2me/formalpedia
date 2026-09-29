-- Prove2me | solution 1 for UpperHalfPlane.eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6c9adde7-3dd2-569c-877f-af96dd5e9cb3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos

noncomputable section

p2m_open "UpperHalfPlane P2MW.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos.UpperHalfPlane Filter Complex MulAction"
open scoped MatrixGroups Topology Modular

namespace UpperHalfPlane
p2m_export "UpperHalfPlane" "continuous_im isOpen_upperHalfPlaneSet ofComplex_apply_of_im_pos σ ρ atImInfty denom denom_ne_zero_of_im J ofComplex_apply continuous_coe im_pos coe_smul_of_det_pos mk re isEmbedding_coe atImInfty_mem im num coe_smul ofComplex"
namespace FibreUSC
p2m_open "UpperHalfPlane"

theorem det_entries (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - ((γ 0 1 : ℤ) : ℂ) * γ 1 0 = 1 := by
  have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this

theorem num_mul_denom_sub (γ : SL(2, ℤ)) (z w : ℂ) :
    num γ z * denom γ w - num γ w * denom γ z = z - w := by
  have h' := det_entries γ
  simp only [num, denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom, Complex.ofReal_intCast]
  linear_combination (z - w) * h'

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem num_eq (γ : SL(2, ℤ)) (z : ℂ) :
    num γ z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom γ z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hz.ne'

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem mob_sub_mob (γ : SL(2, ℤ)) {z w : ℂ} (hz : denom γ z ≠ 0) (hw : denom γ w ≠ 0) :
    mob γ z - mob γ w = (z - w) / (denom γ z * denom γ w) := by
  rw [mob, mob, div_sub_div _ _ hz hw, mul_comm (denom _ z) (num _ w), num_mul_denom_sub]

theorem analyticAt_denom (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (denom (γ : GL (Fin 2) ℝ)) z := by
  have : denom (γ : GL (Fin 2) ℝ) = fun z => ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) :=
    funext (denom_eq γ)
  rw [this]
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_num (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (num (γ : GL (Fin 2) ℝ)) z := by
  have : num (γ : GL (Fin 2) ℝ) = fun z => ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) :=
    funext (num_eq γ)
  rw [this]
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (mob γ) z :=
  (analyticAt_num γ z).div (analyticAt_denom γ z) (denom_ne_zero' γ hz)

theorem eventually_im_pos (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
  mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem tendsto_mob (σ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (mob σ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (mob σ τ)) := by
  refine tendsto_nhdsWithin_iff.2
    ⟨((analyticAt_mob σ τ.im_pos).continuousAt.tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [eventually_im_pos τ, self_mem_nhdsWithin] with z him hne
  rw [Set.mem_compl_iff, Set.mem_singleton_iff, ← sub_eq_zero,
    mob_sub_mob σ (denom_ne_zero' σ him) (denom_ne_zero' σ τ.im_pos)]
  exact div_ne_zero (sub_ne_zero.2 hne)
    (mul_ne_zero (denom_ne_zero' σ him) (denom_ne_zero' σ τ.im_pos))

theorem tendsto_transport (G : ℍ → ℂ) (σ : SL(2, ℤ)) (y : ℍ) {t : ℂ}
    (h : Tendsto (fun z : ℂ => G (ofComplex z)) (𝓝[≠] ((σ • y : ℍ) : ℂ)) (𝓝 t)) :
    Tendsto (fun z : ℂ => G (σ • ofComplex z)) (𝓝[≠] (y : ℂ)) (𝓝 t) := by
  rw [coe_smul] at h
  refine (h.comp (tendsto_mob σ y)).congr' ?_
  filter_upwards [eventually_im_pos y] with z him
  simp only [Function.comp_apply]
  congr 1
  rw [ofComplex_apply_of_im_pos him, ← ofComplex_apply (σ • ⟨z, him⟩), coe_smul]

variable (F : ℍ → ℂ)

def Lim (t : ℂ) (y : ℍ) : Prop :=
  Tendsto (fun z : ℂ => F (ofComplex z)) (𝓝[≠] (y : ℂ)) (𝓝 t)

theorem lim_iff_order_pos {F} (t : ℂ) (y : ℍ)
    (hF : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (y : ℂ)) :
    Lim F t y ↔ 0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (y : ℂ) := by
  have hG : MeromorphicAt (fun z : ℂ => F (ofComplex z) - t) (y : ℂ) :=
    hF.sub (MeromorphicAt.const t _)
  rw [← tendsto_zero_iff_meromorphicOrderAt_pos hG, tendsto_sub_nhds_zero_iff]
  rfl

theorem bounded_below_of_not_lim {F} {t₀ : ℂ} {x : ℍ}
    (hF : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (x : ℂ)) (hx : ¬ Lim F t₀ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z in 𝓝[≠] (x : ℂ), δ ≤ ‖F (ofComplex z) - t₀‖ := by
  have hG : MeromorphicAt (fun z : ℂ => F (ofComplex z) - t₀) (x : ℂ) :=
    hF.sub (MeromorphicAt.const t₀ _)
  have hle : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t₀) (x : ℂ) ≤ 0 :=
    not_lt.mp fun h => hx ((lim_iff_order_pos t₀ x hF).mpr h)
  rcases hle.lt_or_eq with hlt | heq
  · refine ⟨1, one_pos, ?_⟩
    exact (tendsto_norm_cobounded_atTop.comp
      (tendsto_cobounded_of_meromorphicOrderAt_neg hlt)).eventually (eventually_ge_atTop (1 : ℝ))
  · obtain ⟨c, hc, hlim⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hG heq
    have hc' : 0 < ‖c‖ / 2 := by positivity
    refine ⟨‖c‖ / 2, hc', ?_⟩
    filter_upwards [hlim (Metric.ball_mem_nhds c hc')] with z hz
    have hz : dist (F (ofComplex z) - t₀) c < ‖c‖ / 2 := hz
    rw [dist_eq_norm] at hz
    have := norm_sub_norm_le c (F (ofComplex z) - t₀)
    rw [norm_sub_rev] at hz
    linarith

theorem eventually_not_lim {F} {t₀ : ℂ} {x : ℍ}
    (hF : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (x : ℂ)) (hx : ¬ Lim F t₀ x) :
    ∀ᶠ p : ℂ × ℍ in 𝓝 (t₀, x), ¬ Lim F p.1 p.2 := by
  obtain ⟨δ, hδ, hev⟩ := bounded_below_of_not_lim hF hx
  obtain ⟨V, hV, hVo, hxV⟩ : ∃ V : Set ℂ, (∀ z ∈ V, z ≠ (x : ℂ) → δ ≤ ‖F (ofComplex z) - t₀‖) ∧
      IsOpen V ∧ (x : ℂ) ∈ V := by
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hev
    obtain ⟨V, hV, hVo, hxV⟩ := hev
    exact ⟨V, hV, hVo, hxV⟩
  have ht : ∀ᶠ t in 𝓝 t₀, dist t t₀ < δ / 2 := Metric.ball_mem_nhds t₀ (half_pos hδ)
  have hy : ∀ᶠ y : ℍ in 𝓝 x, (y : ℂ) ∈ V :=
    continuous_coe.continuousAt.tendsto.eventually (hVo.mem_nhds hxV)
  rw [nhds_prod_eq]
  refine (ht.prod_mk hy).mono ?_
  rintro ⟨t, y⟩ ⟨ht, hy⟩ hlim
  have h1 : ∀ᶠ z in 𝓝[≠] (y : ℂ), dist (F (ofComplex z)) t < δ / 2 :=
    hlim (Metric.ball_mem_nhds t (half_pos hδ))
  have h2 : ∀ᶠ z in 𝓝[≠] (y : ℂ), z ∈ V := mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy)
  have h3 : ∀ᶠ z in 𝓝[≠] (y : ℂ), z ≠ (x : ℂ) := by
    by_cases hxy : (y : ℂ) = x
    · rw [hxy]; exact self_mem_nhdsWithin
    · exact mem_nhdsWithin_of_mem_nhds (eventually_ne_nhds hxy)
  obtain ⟨z, hz1, hz2, hz3⟩ := (h1.and (h2.and h3)).exists
  have hδz := hV z hz2 hz3
  have : ‖F (ofComplex z) - t₀‖ ≤ dist (F (ofComplex z)) t + dist t t₀ := by
    rw [← dist_eq_norm]; exact dist_triangle _ _ _
  linarith

theorem cusp_step {F} {t₀ : ℂ} (σ : SL(2, ℤ)) {L : ℂ} (hL : L ≠ t₀)
    (hlim : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ A : ℝ, ∀ᶠ t in 𝓝 t₀, ∀ d : ℍ, A < d.im → ¬ Lim F t (σ • d) := by
  set ε : ℝ := dist L t₀ / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; exact half_pos (dist_pos.mpr hL)
  have hmem : {τ : ℍ | dist (F (σ • τ)) L < ε} ∈ atImInfty := hlim (Metric.ball_mem_nhds L hε)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hmem
  refine ⟨A, ?_⟩
  have ht : ∀ᶠ t in 𝓝 t₀, dist t t₀ < ε / 2 := Metric.ball_mem_nhds t₀ (half_pos hε)
  filter_upwards [ht] with t ht d hd hP
  have hP' := tendsto_transport F σ d hP
  have h1 : ∀ᶠ z in 𝓝[≠] (d : ℂ), dist (F (σ • ofComplex z)) t < ε / 2 :=
    hP' (Metric.ball_mem_nhds t (half_pos hε))
  have h2 : ∀ᶠ z in 𝓝[≠] (d : ℂ), A < (ofComplex z).im := by
    have hopen : IsOpen {z : ℂ | A < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds (show A < (d : ℂ).im from hd)),
      eventually_im_pos d] with z hz him
    rwa [ofComplex_apply_of_im_pos him]
  obtain ⟨z, hz1, hz2⟩ := (h1.and h2).exists
  have h3 : dist (F (σ • ofComplex z)) L < ε := hA (ofComplex z) hz2.le
  have := dist_triangle4 L (F (σ • ofComplex z)) t t₀
  rw [dist_comm] at h3
  have h4 : dist L t₀ = 2 * ε := by rw [hε_def]; ring
  linarith

def box (A : ℝ) : Set ℍ :=
  ((↑) : ℍ → ℂ) ⁻¹' (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Set.Icc (1 / 2 : ℝ) A)

theorem isCompact_box (A : ℝ) : IsCompact (box A) := by
  have hS : IsCompact (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Set.Icc (1 / 2 : ℝ) A) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hsub : (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Set.Icc (1 / 2 : ℝ) A) ⊆
      Set.range ((↑) : ℍ → ℂ) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    have him : 0 < z.im := by linarith [hz.2.1]
    exact ⟨⟨z, him⟩, rfl⟩
  refine isEmbedding_coe.isInducing.isCompact_iff.mpr ?_
  rw [box, Set.image_preimage_eq_of_subset hsub]
  exact hS

theorem mem_box_of_mem_fd {d : ℍ} (hd : d ∈ 𝒟) {A : ℝ} (hA : d.im ≤ A) : d ∈ box A := by
  obtain ⟨h1, h2⟩ := hd
  rw [Complex.normSq_apply, show (d : ℂ).re = d.re from rfl, show (d : ℂ).im = d.im from rfl] at h1
  rw [abs_le] at h2
  have him := d.im_pos
  have hre : d.re * d.re ≤ 1 / 4 := by nlinarith [h2.1, h2.2]
  have him' : (1 / 2 : ℝ) ≤ d.im := by nlinarith [h1, hre, him]
  refine Complex.mem_reProdIm.mpr ⟨⟨?_, ?_⟩, ⟨him', hA⟩⟩
  · exact h2.1
  · exact h2.2

variable (Γ : Subgroup SL(2, ℤ))

def ρ (q : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ) := (Quotient.out q)⁻¹

theorem reduce (τ : ℍ) :
    ∃ g : SL(2, ℤ), ∃ h : SL(2, ℤ), h ∈ Γ ∧ g • τ ∈ 𝒟 ∧
      ρ Γ (QuotientGroup.mk g) • (g • τ) = h • τ := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
  refine ⟨g, (h : SL(2, ℤ))⁻¹, inv_mem h.2, hg, ?_⟩
  show (Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ))⁻¹ • g • τ = _
  rw [hh, mul_inv_rev, mul_smul, inv_smul_smul]

theorem main [Γ.FiniteIndex]
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {U : Set ℍ} (hU : IsOpen U)
    (hfib : ∀ τ : ℍ, 0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t₀) (τ : ℂ) →
      ∃ γ ∈ Γ, γ • τ ∈ U) :
    ∀ᶠ t in 𝓝 t₀, ∀ τ : ℍ,
      0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) →
        ∃ γ ∈ Γ, γ • τ ∈ U := by

  set Us : Set ℍ := {y : ℍ | ∃ γ ∈ Γ, γ • y ∈ U} with hUs

  have hloc : ∀ x : ℍ, ∀ᶠ p : ℂ × ℍ in 𝓝 (t₀, x), Lim F p.1 p.2 → p.2 ∈ Us := by
    intro x
    by_cases hx : Lim F t₀ x
    · obtain ⟨γ, hγ, hγx⟩ := hfib x ((lim_iff_order_pos t₀ x (hF x)).mp hx)
      have hcont : Continuous fun y : ℍ => γ • y := continuous_const_smul (γ : GL (Fin 2) ℝ)
      have hV : ∀ᶠ y : ℍ in 𝓝 x, γ • y ∈ U :=
        hcont.continuousAt.tendsto.eventually (hU.mem_nhds hγx)
      have : ∀ᶠ p : ℂ × ℍ in 𝓝 (t₀, x), γ • p.2 ∈ U := by
        rw [nhds_prod_eq]; exact hV.prod_inr (𝓝 t₀)
      exact this.mono fun p hp _ => ⟨γ, hγ, hp⟩
    · exact (eventually_not_lim (hF x) hx).mono fun p hp hl => absurd hl hp

  have hcusp' : ∀ q : SL(2, ℤ) ⧸ Γ, ∃ A : ℝ, ∀ᶠ t in 𝓝 t₀, ∀ d : ℍ, A < d.im →
      ¬ Lim F t (ρ Γ q • d) := by
    intro q
    obtain ⟨L, hL, hlim⟩ := hcusp (ρ Γ q)
    exact cusp_step (ρ Γ q) hL hlim
  choose A hA using hcusp'
  set K : Set ℍ := ⋃ q : SL(2, ℤ) ⧸ Γ, (fun d : ℍ => ρ Γ q • d) '' box (A q) with hK
  have hKc : IsCompact K :=
    isCompact_iUnion fun q => (isCompact_box (A q)).image
      (continuous_const_smul ((ρ Γ q : SL(2, ℤ)) : GL (Fin 2) ℝ))
  have hcompact : ∀ᶠ t in 𝓝 t₀, ∀ y ∈ K, Lim F t y → y ∈ Us :=
    hKc.eventually_forall_of_forall_eventually fun y _ => hloc y
  have hcusps : ∀ᶠ t in 𝓝 t₀, ∀ q : SL(2, ℤ) ⧸ Γ, ∀ d : ℍ, A q < d.im →
      ¬ Lim F t (ρ Γ q • d) := eventually_all.mpr hA

  filter_upwards [hcompact, hcusps] with t hcompact hcusps τ hord
  have hP : Lim F t τ := (lim_iff_order_pos t τ (hF τ)).mpr hord
  obtain ⟨g, h, hh, hgd, hy⟩ := reduce Γ τ
  set d : ℍ := g • τ with hd
  set y : ℍ := ρ Γ (QuotientGroup.mk g) • d with hy_def

  have hPy : Lim F t y := by
    have hτ : τ = h⁻¹ • y := by rw [hy, inv_smul_smul]
    have h1 : Lim F t (h⁻¹ • y) := hτ ▸ hP
    have h2 := tendsto_transport F h⁻¹ y h1
    have h3 : (fun z : ℂ => F (h⁻¹ • ofComplex z)) = fun z : ℂ => F (ofComplex z) :=
      funext fun z => hΓ h⁻¹ (inv_mem hh) _
    rw [h3] at h2
    exact h2

  suffices hyU : y ∈ Us by
    obtain ⟨γ, hγ, hγy⟩ := hyU
    refine ⟨γ * h, mul_mem hγ hh, ?_⟩
    rw [mul_smul, ← hy]
    exact hγy
  by_cases him : d.im ≤ A (QuotientGroup.mk g)
  · exact hcompact y (Set.mem_iUnion.mpr ⟨QuotientGroup.mk g, d, mem_box_of_mem_fd hgd him, rfl⟩)
      hPy
  · exact absurd hPy (hcusps (QuotientGroup.mk g) d (not_le.mp him))

end UpperHalfPlane.FibreUSC

end

p2m_open "UpperHalfPlane P2MW.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos.UpperHalfPlane"
open scoped MatrixGroups Topology

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {U : Set ℍ} (hU : IsOpen U)
    (hfib : ∀ τ : ℍ, 0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t₀) (τ : ℂ) →
      ∃ γ ∈ Γ, γ • τ ∈ U) :
    ∀ᶠ t in 𝓝 t₀, ∀ τ : ℍ,
      0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) →
        ∃ γ ∈ Γ, γ • τ ∈ U :=
  UpperHalfPlane.FibreUSC.main F Γ hF hΓ t₀ hcusp hU hfib

end S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
end P2MW
export P2MW.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos (solution)
