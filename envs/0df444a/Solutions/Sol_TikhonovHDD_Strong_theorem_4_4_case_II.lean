-- Prove2me | solution 1 for TikhonovHDD.Strong.theorem_4_4_case_II
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:15:04.155068+00:00
-- url     : https://prove2.me/submissions/837d0839-df1d-4937-824f-245a416fe5b5

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting
import Theorems.Thm_TikhonovHDD_Strong_theorem_3_1

open Set Filter Topology
open TikhonovHDD.Strong

namespace TikhKeyAux

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

theorem key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (hdiff : Differentiable ℝ g) (xstar : H)
    (hxs : IsMinNormMinimizer g xstar) {ι : Type*} (F : Filter ι) (y : ι → H)
    (hg : Tendsto (fun t => g (y t)) F (𝓝 (g xstar))) (hb : ∀ᶠ t in F, ‖y t‖ ≤ ‖xstar‖) :
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
  set z : ι → WeakDual ℝ H := fun t => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (y t))
    with hz
  set K : Set (WeakDual ℝ H) := WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) r
    with hK
  have hzK : ∀ᶠ t in G, z t ∈ K := by
    filter_upwards [hb.filter_mono hGF] with t ht
    simpa [hK, hz] using ht
  obtain ⟨φ, hφK, hφ⟩ := (WeakDual.isCompact_closedBall (𝕜 := ℝ) (0 : StrongDual ℝ H) r).exists_clusterPt
    (f := map z G) (le_principal_iff.2 hzK)
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
    have : ‖WeakDual.toStrongDual φ‖ ≤ r := by simpa [hK] using hφK
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
  have hwS : w ∈ argminSet g := fun u => hgw.trans (hxs.1 u)
  -- midpoint argument
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
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : (2 * r) ^ 2 ≤ ‖w + xstar‖ ^ 2 := pow_le_pow_left₀ (by linarith) hm2 2
  have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwr 2
  have hexp := norm_add_sq_real w xstar
  have hp : r ^ 2 ≤ inner ℝ w xstar := by rw [← hr] at hexp; nlinarith
  -- final contradiction
  have hfin := hev xstar (r ^ 2 - η ^ 2 / 2) (by
    filter_upwards [hηG, hb.filter_mono hGF] with t h1 h2
    have e := norm_sub_sq_real (y t) xstar
    have a1 : η ^ 2 ≤ ‖y t - xstar‖ ^ 2 := pow_le_pow_left₀ hη.le h1 2
    have a2 : ‖y t‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [← hr] at e
    linarith)
  rw [← hw] at hfin
  have : 0 < η ^ 2 := by positivity
  linarith

end TikhKeyAux

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
    (hcase : ∃ T ≥ t₀, ∀ t ≥ T, ‖x t‖ < ‖xstar‖) :
    Tendsto x atTop (𝓝 xstar) := by
  have hmin : minValue g = g xstar :=
    IsLeast.csInf_eq ⟨⟨xstar, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hxstar.1 u⟩
  have hg : Tendsto (fun t => g (x t)) atTop (𝓝 (g xstar)) := by
    rw [← hmin]
    exact theorem_3_1 g α β t₀ ε ε' u₀ v₀ x xd xdd ht₀ hα hβ hGA hx (Or.inl ⟨hε_int, hε_deriv⟩)
  obtain ⟨T, -, hT⟩ := hcase
  refine TikhKeyAux.key g hGA.convex hGA.differentiable xstar hxstar atTop x hg ?_
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (hT t ht).le
