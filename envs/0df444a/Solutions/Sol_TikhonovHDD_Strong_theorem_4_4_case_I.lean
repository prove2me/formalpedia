-- Prove2me | solution 1 for TikhonovHDD.Strong.theorem_4_4_case_I
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:30:10.524714+00:00
-- url     : https://prove2.me/submissions/94dfbe7f-c3d0-4993-8791-4ec6e48d784b

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting
import Theorems.Thm_TikhonovHDD_Strong_theorem_3_1

open Set Filter Topology
open TikhonovHDD.Strong


namespace TikhCaseIAux


theorem alg (α β a c t ε ε' e xx vv gg xv xg vg sv sg sx ss b p : ℝ)
    (hb : b = 2 * α / 3) (hp : p = α / 3 - 1)
    (hα : 3 ≤ α) (hβ : 0 ≤ β) (ha : 1 < a) (hc : 0 < c) (ht : 0 < t)
    (hε : 0 ≤ ε) (hε' : ε' ≤ -(a * β / 2) * ε ^ 2) (he : 0 ≤ e)
    (hxx : 0 ≤ xx) (hvv : 0 ≤ vv) (hgg : 0 ≤ gg) (hn : 0 ≤ xx + 2 * sx)
    (hgrad : e ≤ xg)
    (hy1 : t * xg ≤ t ^ 2 / (4 * c ^ 2) * gg + c ^ 2 * xx)
    (hy2 : -(ε * (xg + sg)) ≤ gg / a + a / 4 * ε ^ 2 * (xx + 2 * sx + ss))
    (hC3 : b * p + 2 * β * (p + 1) * c ^ 2 ≤ t ^ 2 * ε)
    (hC4 : (p + 2) * β / 2 + b * (p + 1) / (4 * c ^ 2) ≤ t * (1 - 1 / a)) :
    p * (t * (t - β) * e + t ^ 2 * ε / 2 * (xx + 2 * sx)
        + (b ^ 2 * xx + t ^ 2 * vv + t ^ 2 * β ^ 2 * gg + 2 * b * t * xv + 2 * b * β * t * xg
          + 2 * t ^ 2 * β * vg) / 2)
      + t * ((2 * t - β) * e + t * (t - β) * vg + (t * ε + t ^ 2 * ε' / 2) * (xx + 2 * sx)
        + t ^ 2 * ε * (xv + sv)
        + ((b + 1 - α) * b * xv + (b + 1 - α) * t * vv + (b + 1 - α) * t * β * vg
          + (β - t) * b * xg + (β - t) * t * vg + (β - t) * t * β * gg
          - t * ε * b * xx - t * ε * t * xv - t * ε * t * β * xg
          - t * ε * b * sx - t * ε * t * sv - t * ε * t * β * sg))
      ≤ a * β / 4 * ε ^ 2 * t ^ 3 * ss := by
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hc2 : 0 < c ^ 2 := by positivity
  -- nonpositive pieces
  have h1 : t * ((1 - α / 3) * t - α / 3 * β) * e ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ he
    apply mul_nonpos_of_nonneg_of_nonpos ht.le
    nlinarith
  have hA : (1 - α / 3) * t ^ 2 * ε / 2 + t ^ 3 * ε' / 2 + a * β / 4 * ε ^ 2 * t ^ 3 ≤ 0 := by
    have h1' : (1 - α / 3) * t ^ 2 * ε / 2 ≤ 0 := by
      have : 0 ≤ t ^ 2 * ε := by positivity
      nlinarith
    have h2' : t ^ 3 * ε' / 2 + a * β / 4 * ε ^ 2 * t ^ 3 = t ^ 3 / 2 * (ε' + a * β / 2 * ε ^ 2) := by ring
    have h3' : t ^ 3 / 2 * (ε' + a * β / 2 * ε ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have h2 : ((1 - α / 3) * t ^ 2 * ε / 2 + t ^ 3 * ε' / 2 + a * β / 4 * ε ^ 2 * t ^ 3)
      * (xx + 2 * sx) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA hn
  have h3 : (b ^ 2 * p / 2 + b * β * (p + 1) * c ^ 2 - b * t ^ 2 * ε / 2) * xx ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hxx
    have : b ^ 2 * p / 2 + b * β * (p + 1) * c ^ 2 - b * t ^ 2 * ε / 2
        = b / 2 * (b * p + 2 * β * (p + 1) * c ^ 2 - t ^ 2 * ε) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have h4 : ((p + 2) * β ^ 2 * t ^ 2 / 2 + b * β * (p + 1) * t ^ 2 / (4 * c ^ 2)
      - β * t ^ 3 * (1 - 1 / a)) * gg ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hgg
    have : (p + 2) * β ^ 2 * t ^ 2 / 2 + b * β * (p + 1) * t ^ 2 / (4 * c ^ 2)
      - β * t ^ 3 * (1 - 1 / a)
        = β * t ^ 2 * ((p + 2) * β / 2 + b * (p + 1) / (4 * c ^ 2) - t * (1 - 1 / a)) := by
      ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have h5 : -(p / 2 * t ^ 2 * vv) ≤ 0 := by
    have : 0 ≤ p / 2 * t ^ 2 * vv := by positivity
    linarith
  have s1 : b * t ^ 2 * e ≤ b * t ^ 2 * xg := mul_le_mul_of_nonneg_left hgrad (by positivity)
  have s2 : b * β * (p + 1) * (t * xg) ≤ b * β * (p + 1) * (t ^ 2 / (4 * c ^ 2) * gg + c ^ 2 * xx) :=
    mul_le_mul_of_nonneg_left hy1 (by positivity)
  have s3 : β * t ^ 3 * (-(ε * (xg + sg))) ≤ β * t ^ 3 * (gg / a + a / 4 * ε ^ 2 * (xx + 2 * sx + ss)) :=
    mul_le_mul_of_nonneg_left hy2 (by positivity)
  subst hb hp
  linear_combination h1 + h2 + h3 + h4 + h5 + s1 + s2 + s3


theorem young1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) (s c : ℝ)
    (hs : 0 ≤ s) (hc : 0 < c) :
    s * inner ℝ u v ≤ s ^ 2 / (4 * c ^ 2) * inner ℝ u u + c ^ 2 * inner ℝ v v := by
  have h := real_inner_le_norm u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h1 : s * inner ℝ u v ≤ s * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left h hs
  have hid : s ^ 2 / (4 * c ^ 2) * ‖u‖ ^ 2 + c ^ 2 * ‖v‖ ^ 2 - s * (‖u‖ * ‖v‖)
      = (s * ‖u‖ / (2 * c) - c * ‖v‖) ^ 2 := by
    field_simp; ring
  have := sq_nonneg (s * ‖u‖ / (2 * c) - c * ‖v‖)
  linarith

theorem young2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 ≤ ε) :
    -(ε * inner ℝ u v) ≤ inner ℝ u u / a + a / 4 * ε ^ 2 * inner ℝ v v := by
  have h : -inner ℝ u v ≤ ‖u‖ * ‖v‖ := (neg_le_abs _).trans (abs_real_inner_le_norm u v)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h1 : ε * (-inner ℝ u v) ≤ ε * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left h hε
  have hid : ‖u‖ ^ 2 / a + a / 4 * ε ^ 2 * ‖v‖ ^ 2 - ε * (‖u‖ * ‖v‖)
      = a * (‖u‖ / a - ε * ‖v‖ / 2) ^ 2 := by
    field_simp; ring
  have := mul_nonneg ha.le (sq_nonneg (‖u‖ / a - ε * ‖v‖ / 2))
  linarith

theorem alg_vec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (xs V Gv S A HV : H) (α β a c s ε ε' e b p : ℝ)
    (hb : b = 2 * α / 3) (hp : p = α / 3 - 1)
    (hα : 3 ≤ α) (hβ : 0 ≤ β) (ha : 1 < a) (hc : 0 < c) (hs : 0 < s)
    (hε : 0 ≤ ε) (hε' : ε' ≤ -(a * β / 2) * ε ^ 2) (he : 0 ≤ e)
    (hgrad : e ≤ inner ℝ Gv (xs - S)) (hcase : ‖S‖ ≤ ‖xs‖)
    (hode : A + (α / s) • V + β • HV + Gv + ε • xs = 0)
    (hC3 : b * p + 2 * β * (p + 1) * c ^ 2 ≤ s ^ 2 * ε)
    (hC4 : (p + 2) * β / 2 + b * (p + 1) / (4 * c ^ 2) ≤ s * (1 - 1 / a)) :
    p * (s * (s - β) * e + s ^ 2 * ε / 2 * (‖xs‖ ^ 2 - ‖S‖ ^ 2)
        + ‖b • (xs - S) + s • (V + β • Gv)‖ ^ 2 / 2)
      + s * ((2 * s - β) * e + s * (s - β) * inner ℝ Gv V
        + ((2 * s * ε + s ^ 2 * ε') / 2 * (‖xs‖ ^ 2 - ‖S‖ ^ 2) + s ^ 2 * ε / 2 * (2 * inner ℝ xs V))
        + 2 * inner ℝ (b • (xs - S) + s • (V + β • Gv))
            (b • V + (s • (A + β • HV) + (V + β • Gv))) / 2)
      ≤ a * β / 4 * ε ^ 2 * s ^ 3 * ‖S‖ ^ 2 := by
  obtain ⟨X, rfl⟩ : ∃ X, xs = X + S := ⟨xs - S, by abel⟩
  simp only [add_sub_cancel_right] at hgrad ⊢
  have hsA : s • (A + β • HV) = -(α • V + s • Gv + (s * ε) • (X + S)) := by
    have hA : A + β • HV = -((α / s) • V + Gv + ε • (X + S)) := by
      rw [eq_neg_iff_add_eq_zero, ← hode]; abel
    rw [hA, smul_neg, smul_add, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hs.ne']
  rw [hsA]
  have hn : 0 ≤ inner ℝ X X + 2 * inner ℝ S X := by
    have h1 : ‖S‖ ^ 2 ≤ ‖X + S‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcase 2
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h1
    simp only [inner_add_left, inner_add_right, real_inner_comm] at h1
    linarith
  have hy1 := young1 Gv X s c hs.le hc
  have hy2 := young2 Gv (X + S) a ε (by linarith) hε
  have key := alg α β a c s ε ε' e (inner ℝ X X) (inner ℝ V V) (inner ℝ Gv Gv) (inner ℝ X V)
    (inner ℝ Gv X) (inner ℝ Gv V) (inner ℝ S V) (inner ℝ Gv S) (inner ℝ S X) (inner ℝ S S) b p
    hb hp hα hβ ha hc hs hε hε' he (real_inner_self_nonneg) (real_inner_self_nonneg)
    (real_inner_self_nonneg) hn hgrad hy1
    (by simp only [inner_add_left, inner_add_right, real_inner_comm] at hy2 ⊢; linarith) hC3 hC4
  simp only [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm] at key ⊢
  linarith

end TikhCaseIAux

namespace TikhKey2Aux

theorem grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (w u : H) (hd : DifferentiableAt ℝ g w) :
    fderiv ℝ g w (u - w) ≤ g u - g w := by
  set h : ℝ → ℝ := fun s => g (w + s • (u - w)) with hh
  have hline : HasDerivAt (fun s : ℝ => w + s • (u - w)) (u - w) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (u - w)).const_add w
  have hder : HasDerivAt h (fderiv ℝ g w (u - w)) 0 := by
    have hd' : HasFDerivAt g (fderiv ℝ g w) (w + (0:ℝ) • (u - w)) := by
      simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0:ℝ) hline
  have hlim := hder.tendsto_slope_zero_right
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hc := hconv.2 (mem_univ w) (mem_univ u) (show (0:ℝ) ≤ 1 - t by linarith) ht0.le
    (show (1 - t) + t = 1 by ring)
  have heq : (1 - t) • w + t • u = w + t • (u - w) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq] at hc
  simp only [smul_eq_mul] at hc
  have h0 : h 0 = g w := by simp [hh]
  have ht' : h (0 + t) = g (w + t • (u - w)) := by simp [hh]
  rw [ht', h0, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht0]
  linarith

/-- Strong convergence to the minimum-norm minimizer from `g(y) → min g` and
`limsup ‖y‖ ≤ ‖x⋆‖`. -/
theorem key2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (hdiff : Differentiable ℝ g) (xstar : H)
    (hxs : IsMinNormMinimizer g xstar) {ι : Type*} (F : Filter ι) (y : ι → H)
    (hg : Tendsto (fun t => g (y t)) F (𝓝 (g xstar)))
    (hb : ∀ η > (0:ℝ), ∀ᶠ t in F, ‖y t‖ ≤ ‖xstar‖ + η) :
    Tendsto y F (𝓝 xstar) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  set G := F ⊓ 𝓟 {t | ¬ dist (y t) xstar < η} with hGdef
  have hGF : G ≤ F := inf_le_left
  have hηG : ∀ᶠ t in G, η ≤ ‖y t - xstar‖ := by
    have : {t | ¬ dist (y t) xstar < η} ∈ G := mem_inf_of_right (mem_principal_self _)
    filter_upwards [this] with t ht
    simpa [dist_eq_norm] using ht
  have : G.NeBot := by
    rw [hGdef, ← frequently_iff_neBot]; exact hcon
  set r := ‖xstar‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  set z : ι → WeakDual ℝ H := fun t => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (y t))
    with hz
  have hzK : ∀ ρ > (0:ℝ), ∀ᶠ t in G,
      z t ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) (r + ρ) := by
    intro ρ hρ
    filter_upwards [(hb ρ hρ).filter_mono hGF] with t ht
    simpa [hz] using ht
  obtain ⟨φ, -, hφ⟩ := (WeakDual.isCompact_closedBall (𝕜 := ℝ) (0 : StrongDual ℝ H)
    (r + 1)).exists_clusterPt (f := map z G) (le_principal_iff.2 (hzK 1 one_pos))
  have hev : ∀ (v : H) (c : ℝ), (∀ᶠ t in G, inner ℝ (y t) v ≤ c) → φ v ≤ c := by
    intro v c h
    have hcl : IsClosed ((fun ψ : WeakDual ℝ H => ψ v) ⁻¹' Iic c) :=
      isClosed_Iic.preimage (WeakDual.eval_continuous v)
    refine hcl.mem_of_mapClusterPt hφ ?_
    filter_upwards [h] with t ht
    simpa [hz] using ht
  set w : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ) with hwdef
  have hw : ∀ v, inner ℝ w v = φ v := fun v => by
    rw [hwdef, InnerProductSpace.toDual_symm_apply]; rfl
  have hwr : ‖w‖ ≤ r := by
    refine le_of_forall_pos_le_add fun ρ hρ => ?_
    have hmem : φ ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) (r + ρ) :=
      (WeakDual.isClosed_closedBall (0 : StrongDual ℝ H) (r + ρ)).mem_of_mapClusterPt hφ
        (hzK ρ hρ)
    have : ‖WeakDual.toStrongDual φ‖ ≤ r + ρ := by simpa using hmem
    rw [hwdef, LinearIsometryEquiv.norm_map]; exact this
  -- w is a minimizer
  have hgw : g w ≤ g xstar := by
    by_contra hlt
    push Not at hlt
    set d := g w - g xstar with hd
    set ℓ := fderiv ℝ g w with hℓ
    set v : H := (InnerProductSpace.toDual ℝ H).symm ℓ with hvdef
    have hv : ∀ u, inner ℝ u v = ℓ u := by
      intro u; rw [real_inner_comm, hvdef, InnerProductSpace.toDual_symm_apply]
    have h1 : ∀ᶠ t in G, g (y t) < g xstar + d / 2 :=
      (hg.mono_left hGF).eventually (eventually_lt_nhds (by linarith))
    have h2 := hev v (ℓ w - d / 2) (h1.mono fun t ht => by
      rw [hv]
      have := grad_ineq g hconv w (y t) (hdiff w)
      rw [map_sub] at this
      linarith)
    rw [← hw, hv] at h2
    linarith
  have hmS : (1/2 : ℝ) • w + (1/2 : ℝ) • xstar ∈ argminSet g := by
    intro u
    have hc := hconv.2 (mem_univ w) (mem_univ xstar) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at hc
    have := hxs.1 u
    linarith [hgw]
  have hm := hxs.2 _ hmS
  have hmeq : (1/2 : ℝ) • w + (1/2 : ℝ) • xstar = (1/2 : ℝ) • (w + xstar) := by
    rw [smul_add]
  rw [hmeq, norm_smul] at hm
  have hm2 : 2 * r ≤ ‖w + xstar‖ := by
    rw [← hr] at hm; norm_num at hm; linarith
  have hsq : (2 * r) ^ 2 ≤ ‖w + xstar‖ ^ 2 := pow_le_pow_left₀ (by linarith) hm2 2
  have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwr 2
  have hexp := norm_add_sq_real w xstar
  have hp : r ^ 2 ≤ inner ℝ w xstar := by rw [← hr] at hexp; nlinarith
  -- final contradiction
  set ρ : ℝ := min 1 (η ^ 2 / (2 * (2 * r + 1))) with hρ
  have hρpos : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ η ^ 2 / (2 * (2 * r + 1)) := min_le_right _ _
  have hρ3 : ρ * (2 * r + 1) ≤ η ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hρ2 (by linarith : (0:ℝ) ≤ 2 * r + 1)
    have e2 : η ^ 2 / (2 * (2 * r + 1)) * (2 * r + 1) = η ^ 2 / 2 := by
      field_simp
    linarith
  have hfin := hev xstar (r ^ 2 - η ^ 2 / 4) (by
    filter_upwards [hηG, (hb ρ hρpos).filter_mono hGF] with t h1 h2
    have e := norm_sub_sq_real (y t) xstar
    have a1 : η ^ 2 ≤ ‖y t - xstar‖ ^ 2 := pow_le_pow_left₀ hη.le h1 2
    have a2 : ‖y t‖ ^ 2 ≤ (r + ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have a3 : (r + ρ) ^ 2 ≤ r ^ 2 + η ^ 2 / 2 := by nlinarith
    rw [← hr] at e
    linarith)
  rw [← hw] at hfin
  have : 0 < η ^ 2 := by positivity
  linarith

end TikhKey2Aux


theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hGA : GeneralAssumption g t₀ ε ε')
    (hx : IsSolution g α β t₀ ε u₀ v₀ x xd xdd)
    (hε_int : MeasureTheory.IntegrableOn (fun t => ε t / t) (Ici t₀))
    (hε_lim : Tendsto
      (fun t => β / (ε t * t ^ (α / 3 + 1)) * ∫ s in t₀..t, ε s ^ 2 * s ^ (α / 3 + 1))
      atTop (𝓝 0))
    (hε_deriv : ∃ a > (1 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε' t ≤ -(a * β / 2) * ε t ^ 2)
    (hα3 : α = 3 → Tendsto (fun t => t ^ 2 * ε t) atTop atTop)
    (hα3lt : 3 < α → ∃ c > (0 : ℝ),
      ∀ᶠ t in atTop, 2 / 3 * α * (1 / 3 * α - 1 + β * c ^ 2) ≤ t ^ 2 * ε t)
    (hxstar : IsMinNormMinimizer g xstar)
    (hcase : ∃ T ≥ t₀, ∀ t ≥ T, ‖xstar‖ ≤ ‖x t‖) :
    Tendsto x atTop (𝓝 xstar) := by
  obtain ⟨a, ha, t₁, ht₁, hεd⟩ := hε_deriv
  obtain ⟨T, hT, hTc⟩ := hcase
  obtain ⟨r, hr⟩ : ∃ r, r = ‖xstar‖ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * α / 3 := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = α / 3 - 1 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg _
  have hgi : ∀ z v : H, fderiv ℝ g z v = inner ℝ (gradient g z) v := fun z v => by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hmin : minValue g = g xstar :=
    IsLeast.csInf_eq ⟨⟨xstar, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hxstar.1 u⟩
  have hg : Tendsto (fun t => g (x t)) atTop (𝓝 (g xstar)) := by
    rw [← hmin]
    exact theorem_3_1 g α β t₀ ε ε' u₀ v₀ x xd xdd ht₀ hα hβ hGA hx
      (Or.inl ⟨hε_int, a, ha, t₁, ht₁, hεd⟩)
  obtain ⟨c, hc, hC3ev⟩ : ∃ c > (0:ℝ), ∀ᶠ t in atTop,
      b * p + 2 * β * (p + 1) * c ^ 2 ≤ t ^ 2 * ε t := by
    rcases eq_or_lt_of_le hα with h3 | h3
    · refine ⟨1, one_pos, ?_⟩
      have hb' : b * p + 2 * β * (p + 1) * 1 ^ 2 = 2 * β := by rw [hb, hp, ← h3]; ring
      rw [hb']; exact (hα3 h3.symm).eventually_ge_atTop _
    · obtain ⟨c, hc, hev⟩ := hα3lt h3
      refine ⟨c, hc, hev.mono fun t ht => ?_⟩
      have : b * p + 2 * β * (p + 1) * c ^ 2 = 2 / 3 * α * (1 / 3 * α - 1 + β * c ^ 2) := by
        rw [hb, hp]; ring
      rw [this]; exact ht
  have hC4ev : ∀ᶠ t in atTop,
      (p + 2) * β / 2 + b * (p + 1) / (4 * c ^ 2) ≤ t * (1 - 1 / a) := by
    have h1a : 0 < 1 - 1 / a := by
      have : 1 / a < 1 := (div_lt_one (by linarith)).2 ha
      linarith
    exact ((Tendsto.atTop_mul_const h1a tendsto_id).eventually_ge_atTop _).mono
      fun t ht => by simpa using ht
  obtain ⟨t₆, ht₆⟩ := eventually_atTop.1 ((eventually_ge_atTop (t₀ + 1)).and
    ((eventually_ge_atTop t₁).and ((eventually_ge_atTop T).and
    ((eventually_ge_atTop β).and (hC3ev.and hC4ev)))))
  have ht60 : t₀ + 1 ≤ t₆ := (ht₆ t₆ le_rfl).1
  -- the (corrected) energy functional
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ, Q = fun s => s * (s - β) * (g (x s) - g xstar)
      + s ^ 2 * ε s / 2 * (‖x s‖ ^ 2 - r ^ 2)
      + ‖b • (x s - xstar) + s • (xd s + β • gradient g (x s))‖ ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun s => ε s ^ 2 * s ^ (α / 3 + 1) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = a * β / 4 * r ^ 2 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; have : 0 ≤ a := by linarith
                         positivity
  have hεc : ContinuousOn ε (Ici t₀) := fun s hs =>
    (hGA.hasDerivWithinAt_eps s hs).continuousWithinAt
  have hfc : ContinuousOn f (Ici t₀) := by
    rw [hf]
    exact (hεc.pow 2).mul (fun s hs => (Real.continuousAt_rpow_const s _
      (Or.inl (ne_of_gt (lt_of_lt_of_le ht₀ hs)))).continuousWithinAt)
  have hfnn : ∀ s, t₀ ≤ s → 0 ≤ f s := fun s hs => by
    rw [hf]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hfii : ∀ u v, t₀ ≤ u → t₀ ≤ v → IntervalIntegrable f MeasureTheory.volume u v := by
    intro u v hu hv
    refine (hfc.mono fun w hw => ?_).intervalIntegrable
    rcases Set.mem_uIcc.1 hw with h | h
    · exact le_trans hu h.1
    · exact le_trans hv h.1
  -- derivative of Φ(s) = s^p Q(s) - C ∫_{t₆}^s f
  have hΦd : ∀ s, t₀ < s → ∃ D, HasDerivAt (fun s => s ^ p * Q s - C * ∫ τ in t₆..s, f τ) D s ∧
      (t₆ ≤ s → D ≤ 0) := by
    intro s hs
    have hs0 : 0 < s := lt_trans ht₀ hs
    have hsI : s ∈ Ici t₀ := le_of_lt hs
    have hmem : Ici t₀ ∈ 𝓝 s := Ici_mem_nhds hs
    obtain ⟨hd1, hd2, hode⟩ := hx.1 s hsI
    have hxs : HasDerivAt x (xd s) s := hd1.hasDerivAt hmem
    have hxds : HasDerivAt xd (xdd s) s := hd2.hasDerivAt hmem
    have hεs : HasDerivAt ε (ε' s) s := (hGA.hasDerivWithinAt_eps s hsI).hasDerivAt hmem
    have hG : HasDerivAt (fun s => gradient g (x s)) (fderiv ℝ (gradient g) (x s) (xd s)) s :=
      (hGA.differentiable_gradient (x s)).hasFDerivAt.comp_hasDerivAt s hxs
    have hgd : HasDerivAt (fun s => g (x s)) (fderiv ℝ g (x s) (xd s)) s :=
      (hGA.differentiable (x s)).hasFDerivAt.comp_hasDerivAt s hxs
    have hu := ((hxs.sub_const xstar).const_smul b).add
      ((hasDerivAt_id' s).smul (hxds.add (hG.const_smul β)))
    have hQd := ((((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const β)).mul
      (hgd.sub_const (g xstar))).add
      ((((hasDerivAt_pow 2 s).mul hεs).div_const 2).mul (hxs.norm_sq.sub_const (r ^ 2)))).add
      (hu.norm_sq.div_const 2)
    have hE := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs0.ne')).mul hQd
    have hI : HasDerivAt (fun u => ∫ τ in t₆..u, f τ) (f s) s :=
      intervalIntegral.integral_hasDerivAt_right (hfii t₆ s (by linarith) hs.le)
        ((hfc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi s hs)
        (hfc.continuousAt hmem)
    have hΦ := hE.sub (hI.const_mul C)
    rw [hQ]
    refine ⟨_, hΦ, fun hs6 => ?_⟩
    obtain ⟨-, hst₁, hsT, hsβ, hC3, hC4⟩ := ht₆ s hs6
    have hB := TikhCaseIAux.alg_vec (x s) (xd s) (gradient g (x s)) xstar (xdd s)
      (fderiv ℝ (gradient g) (x s) (xd s)) α β a c s (ε s) (ε' s) (g (x s) - g xstar) b p
      hb hp hα hβ ha hc hs0 (hGA.eps_nonneg s hsI) (hεd s hst₁)
      (by have := hxstar.1 (x s); linarith)
      (by
        have h1 := TikhKey2Aux.grad_ineq g hGA.convex (x s) xstar (hGA.differentiable (x s))
        rw [hgi, inner_sub_right] at h1
        rw [inner_sub_right]
        linarith)
      (hTc s hsT) hode hC3 hC4
    rw [← hr] at hB
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', one_smul, Nat.reduceSub,
      pow_one, Nat.cast_ofNat, hgi]
    rw [Real.rpow_sub_one hs0.ne', hf]
    have hsp : s ^ (α / 3 + 1) = s ^ p * s ^ 2 := by
      rw [show α / 3 + 1 = p + 2 by rw [hp]; ring, Real.rpow_add hs0, Real.rpow_two]
    simp only [hsp]
    have hpos : 0 ≤ s ^ p / s := div_nonneg (Real.rpow_nonneg hs0.le _) hs0.le
    rw [hC]
    have hne : s ≠ 0 := hs0.ne'
    calc _ = s ^ p / s * ((p * (s * (s - β) * (g (x s) - g xstar)
        + s ^ 2 * ε s / 2 * (‖x s‖ ^ 2 - r ^ 2)
        + ‖b • (x s - xstar) + s • (xd s + β • gradient g (x s))‖ ^ 2 / 2)
      + s * ((2 * s - β) * (g (x s) - g xstar) + s * (s - β) * inner ℝ (gradient g (x s)) (xd s)
        + ((2 * s * ε s + s ^ 2 * ε' s) / 2 * (‖x s‖ ^ 2 - r ^ 2)
          + s ^ 2 * ε s / 2 * (2 * inner ℝ (x s) (xd s)))
        + 2 * inner ℝ (b • (x s - xstar) + s • (xd s + β • gradient g (x s)))
            (b • xd s + (s • (xdd s + β • (fderiv ℝ (gradient g) (x s)) (xd s))
              + (xd s + β • gradient g (x s)))) / 2))
        - a * β / 4 * ε s ^ 2 * s ^ 3 * r ^ 2) := by
          field_simp
          ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos (by linarith)
  -- monotonicity
  have hanti : AntitoneOn (fun s => s ^ p * Q s - C * ∫ τ in t₆..s, f τ) (Ici t₆) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro s hs
      have hs' : t₀ < s := by have : t₆ ≤ s := hs; linarith
      obtain ⟨D, hD, -⟩ := hΦd s hs'
      exact hD.continuousAt.continuousWithinAt
    · rw [interior_Ici]
      intro s hs
      have hs' : t₀ < s := by have : t₆ < s := hs; linarith
      obtain ⟨D, hD, -⟩ := hΦd s hs'
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro s hs
      have hs6 : t₆ < s := hs
      obtain ⟨D, hD, hle⟩ := hΦd s (by linarith)
      rw [hD.deriv]; exact hle hs6.le
  -- upper and lower bounds
  have hbound : ∀ t, t₆ ≤ t →
      t ^ p * t ^ 2 * ε t * (‖x t‖ ^ 2 - r ^ 2) / 2 ≤ t₆ ^ p * Q t₆ + C * ∫ τ in t₀..t, f τ := by
    intro t ht
    have h1 := hanti (show t₆ ∈ Ici t₆ from le_refl t₆) ht ht
    simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at h1
    have ht0 : 0 < t := by linarith
    have htβ : β ≤ t := (ht₆ t ht).2.2.2.1
    have hQlow : t ^ 2 * ε t / 2 * (‖x t‖ ^ 2 - r ^ 2) ≤ Q t := by
      rw [hQ]
      have e1 : 0 ≤ t * (t - β) * (g (x t) - g xstar) :=
        mul_nonneg (mul_nonneg ht0.le (by linarith)) (by have := hxstar.1 (x t); linarith)
      have e2 : 0 ≤ ‖b • (x t - xstar) + t • (xd t + β • gradient g (x t))‖ ^ 2 / 2 := by
        positivity
      simp only
      linarith
    have hpp : 0 ≤ t ^ p := Real.rpow_nonneg ht0.le _
    have h2 := mul_le_mul_of_nonneg_left hQlow hpp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hfii t₀ t₆ le_rfl (by linarith)) (hfii t₆ t (by linarith) (by linarith))
    have hnn : 0 ≤ ∫ τ in t₀..t₆, f τ :=
      intervalIntegral.integral_nonneg (by linarith) (fun u hu => hfnn u hu.1)
    have h3 : C * ∫ τ in t₆..t, f τ ≤ C * ∫ τ in t₀..t, f τ :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    have h4 : t ^ p * t ^ 2 * ε t * (‖x t‖ ^ 2 - r ^ 2) / 2
        = t ^ p * (t ^ 2 * ε t / 2 * (‖x t‖ ^ 2 - r ^ 2)) := by ring
    linarith
  -- growth of ε(t) t^{α/3+1}
  have hWeq : ∀ t, 0 < t → ε t * t ^ (α / 3 + 1) = t ^ 2 * ε t * t ^ p := fun t ht => by
    rw [show α / 3 + 1 = p + 2 by rw [hp]; ring, Real.rpow_add ht, Real.rpow_two]; ring
  have hW : Tendsto (fun t => ε t * t ^ (α / 3 + 1)) atTop atTop := by
    rcases eq_or_lt_of_le hα with h3 | h3
    · have hp' : p = 0 := by rw [hp, ← h3]; norm_num
      refine (hα3 h3.symm).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [hWeq t ht, hp', Real.rpow_zero, mul_one]
    · obtain ⟨c', hc', hev⟩ := hα3lt h3
      have hk : 0 < 2 / 3 * α * (1 / 3 * α - 1 + β * c' ^ 2) := by
        have : 0 < 1 / 3 * α - 1 := by linarith
        have : 0 ≤ β * c' ^ 2 := by positivity
        have : 0 < α := by linarith
        positivity
      have hpp : 0 < p := by rw [hp]; linarith
      refine tendsto_atTop_mono' _ ?_ ((tendsto_rpow_atTop hpp).const_mul_atTop hk)
      filter_upwards [hev, eventually_gt_atTop 0] with t h1 ht
      rw [hWeq t ht]
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.le _)
  have hlim2 : Tendsto (fun t => 2 * (t₆ ^ p * Q t₆) * (ε t * t ^ (α / 3 + 1))⁻¹
      + a * r ^ 2 / 2 * (β / (ε t * t ^ (α / 3 + 1)) * ∫ s in t₀..t, ε s ^ 2 * s ^ (α / 3 + 1)))
      atTop (𝓝 0) := by
    have h0 := ((tendsto_const_nhds (x := 2 * (t₆ ^ p * Q t₆))).mul
      hW.inv_tendsto_atTop).add ((tendsto_const_nhds (x := a * r ^ 2 / 2)).mul hε_lim)
    simp only [mul_zero, add_zero] at h0
    exact h0
  have hnorm : ∀ η > (0:ℝ), ∀ᶠ t in atTop, ‖x t‖ ≤ ‖xstar‖ + η := by
    intro η hη
    have hη2 : (0:ℝ) < η ^ 2 := by positivity
    filter_upwards [hlim2.eventually (eventually_lt_nhds hη2), eventually_ge_atTop t₆,
      hW.eventually_gt_atTop 0] with t h1 h2 h3
    have hb1 := hbound t h2
    have ht0 : 0 < t := by linarith
    rw [hf] at hb1
    rw [← hr]
    have hW' : t ^ p * t ^ 2 * ε t = ε t * t ^ (α / 3 + 1) := by rw [hWeq t ht0]; ring
    rw [hW'] at hb1
    set W := ε t * t ^ (α / 3 + 1) with hWdef
    set I := ∫ s in t₀..t, ε s ^ 2 * s ^ (α / 3 + 1) with hIdef
    have h5 : ‖x t‖ ^ 2 - r ^ 2 ≤ 2 * (t₆ ^ p * Q t₆) * W⁻¹ + a * r ^ 2 / 2 * (β / W * I) := by
      have e : 2 * (t₆ ^ p * Q t₆) * W⁻¹ + a * r ^ 2 / 2 * (β / W * I)
          = 2 * (t₆ ^ p * Q t₆ + C * I) / W := by
        rw [hC]; field_simp; ring
      rw [e, le_div_iff₀ h3]
      linarith
    have h6 : ‖x t‖ ^ 2 < (r + η) ^ 2 := by nlinarith
    by_contra hcon
    push Not at hcon
    have := pow_le_pow_left₀ (by positivity) hcon.le 2
    linarith
  exact TikhKey2Aux.key2 g hGA.convex hGA.differentiable xstar hxstar atTop x hg hnorm
