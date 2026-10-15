-- Prove2me | solution 1 for Plasticity.Ext.InvarianceOfDomain
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T09:14:42.576919+00:00
-- url     : https://prove2.me/submissions/6b6fea16-2572-489f-ad34-bdf5d33b60db

/-
Invariance of domain from Brouwer's fixed point theorem.

Ported from the open Mathlib pull request
  https://github.com/leanprover-community/mathlib4/pull/36770
  "feat: invariance of domain via Brouwer's fixed point theorem"
  (file `Mathlib/AlgebraicTopology/InvarianceOfDomain.lean`, head commit 230d75a,
  author Xmask19 (Kai Lam)), released under the Apache License 2.0
  (https://www.apache.org/licenses/LICENSE-2.0); original notice:
  "Copyright (c) 2026 Kai Lam. All rights reserved. Released under Apache 2.0 license."
That file follows T. Tao, "Brouwer's fixed point and invariance of domain theorems, and
Hilbert's fifth problem", What's new, 13 June 2011.
Adaptations: Part 2 of the pull request only (the Tao argument); a general finite-dimensional
real normed space with Brouwer's theorem as an explicit hypothesis instead of a type class;
a basis instead of an orthonormal basis in the Stone–Weierstrass step; an arbitrary Haar
measure; the approximation tolerance halved so that no minimum of `‖P‖` over `Σ₁` is needed;
Brouwer for the sup-norm ball of `ι → ℝ` taken from the card `Plasticity.Ext.Brouwer`.
-/
import Theorems.Thm_Plasticity_Ext_Brouwer
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace Sol_Plasticity_Ext_InvarianceOfDomain

open Metric Set MeasureTheory

/-- Brouwer's fixed point property for the closed unit ball of a normed group `E`. -/
def BrouwerBall (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ F : E → E, ContinuousOn F (closedBall 0 1) → MapsTo F (closedBall 0 1) (closedBall 0 1) →
    ∃ x ∈ closedBall (0 : E) 1, F x = x

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Stone–Weierstrass: a continuous self-map of `E` is uniformly approximated on a compact set
by a differentiable (coordinatewise polynomial) map. -/
theorem differentiable_approx {δ : ℝ} (hδ : 0 < δ) {K : Set E} (hK : IsCompact K)
    (G : E → E) (hG : Continuous G) :
    ∃ P : E → E, Differentiable ℝ P ∧ ∀ y ∈ K, ‖P y - G y‖ < δ := by
  let b := Module.finBasis ℝ E
  let n := Module.finrank ℝ E
  let L : E ≃L[ℝ] (Fin n → ℝ) := b.equivFunL
  let coord (i : Fin n) : C(E, ℝ) := ⟨fun x => L x i, by fun_prop⟩
  let A : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ (Set.range coord)
  have hA_diff : ∀ g ∈ A, Differentiable ℝ (g : E → ℝ) := by
    let D : Subalgebra ℝ C(E, ℝ) :=
      { carrier := {g | Differentiable ℝ (g : E → ℝ)}
        zero_mem' := differentiable_const 0
        one_mem' := differentiable_const 1
        add_mem' := fun hf hg => hf.add hg
        mul_mem' := fun hf hg => hf.mul hg
        algebraMap_mem' := fun r => differentiable_const r }
    have hAD : A ≤ D := Algebra.adjoin_le (by
      rintro _ ⟨i, rfl⟩
      exact ((ContinuousLinearMap.proj i).comp (L : E →L[ℝ] (Fin n → ℝ))).differentiable)
    exact fun g hg => hAD hg
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    have hL : L x ≠ L y := L.injective.ne hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hL
    exact ⟨coord i, ⟨coord i, Algebra.subset_adjoin (Set.mem_range_self i), rfl⟩, hi⟩
  set C : ℝ := ‖(L.symm : (Fin n → ℝ) →L[ℝ] E)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  set ε' : ℝ := δ / (C + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hδ (by linarith)
  have approx (i : Fin n) :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints hAsep
      ⟨fun y => L (G y) i, by fun_prop⟩ hK hε'pos
  choose p hpA hp using approx
  refine ⟨fun y => L.symm (fun i => p i y), ?_, ?_⟩
  · exact (L.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp
      (differentiable_pi.mpr fun i => hA_diff _ (hpA i))
  · intro y hy
    set v : Fin n → ℝ := fun i => p i y - L (G y) i with hv_def
    have hv : ‖v‖ < ε' := (pi_norm_lt_iff hε'pos).mpr fun i => by simpa [v] using hp i y hy
    have heq : L.symm (fun i => p i y) - G y = L.symm v := by
      rw [show v = (fun i => p i y) - L (G y) from rfl, map_sub, L.symm_apply_apply]
    rw [heq]
    calc ‖L.symm v‖ ≤ C * ‖v‖ := (L.symm : (Fin n → ℝ) →L[ℝ] E).le_opNorm v
      _ ≤ C * ε' := by gcongr
      _ < (C + 1) * ε' := by nlinarith
      _ = δ := by rw [hε']; field_simp

/-- A differentiable self-map of `E` misses points of every ball around the origin on any
sphere: the image of a sphere has Haar measure zero. -/
theorem exists_small_not_mem_image_sphere {P : E → E} (hP : Differentiable ℝ P) (c : E)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ v : E, ‖v‖ < r ∧ v ∉ P '' sphere c ε := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have h0 : (Measure.addHaar : Measure E) (P '' sphere c ε) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ hP.differentiableOn
      (Measure.addHaar_sphere_of_ne_zero _ c hε.ne')
  by_contra! h
  have hsub : ball (0 : E) r ⊆ P '' sphere c ε := fun v hv => h v (mem_ball_zero_iff.mp hv)
  have h1 := measure_mono (μ := (Measure.addHaar : Measure E)) hsub
  rw [h0] at h1
  exact (measure_ball_pos (Measure.addHaar : Measure E) (0 : E) hr).ne'
    (le_antisymm h1 zero_le)

/-- A continuous injective map on the closed unit ball has a continuous left inverse defined
on all of `E` (inverse on the compact image, then Tietze extension). -/
theorem exists_continuous_leftInverse {f : E → E} (hf : ContinuousOn f (closedBall 0 1))
    (hinj : InjOn f (closedBall 0 1)) :
    ∃ G : E → E, Continuous G ∧ ∀ x ∈ closedBall (0 : E) 1, G (f x) = x := by
  have hK : IsCompact (f '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn hf
  let Φ := Equiv.Set.imageOfInjOn f (closedBall 0 1) hinj
  have : CompactSpace (closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hΦ : Continuous Φ := continuous_induced_rng.mpr hf.domRestrict
  let inv : C(f '' closedBall 0 1, E) :=
    ⟨fun y => (Φ.symm y : E), continuous_subtype_val.comp hΦ.continuous_symm_of_equiv_compact_to_t2⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK.isClosed inv
  refine ⟨g, g.continuous, fun x hx => ?_⟩
  have h1 : g (f x) = inv ⟨f x, mem_image_of_mem f hx⟩ := by
    rw [← hg]; rfl
  rw [h1]
  have h2 : (⟨f x, mem_image_of_mem f hx⟩ : f '' closedBall 0 1) = Φ ⟨x, hx⟩ := rfl
  show (Φ.symm ⟨f x, mem_image_of_mem f hx⟩ : E) = x
  rw [h2, Φ.symm_apply_apply]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Stability of zero (Tao's Lemma 6): if `G` is a left inverse of `f` on the closed unit
ball and `Gt` is continuous on `f '' closedBall 0 1` and uniformly `1`-close to `G` there,
then `Gt` has a zero on `f '' closedBall 0 1`. Uses Brouwer's theorem. -/
theorem stability_of_zero (hB : BrouwerBall E) {f : E → E}
    (hf : ContinuousOn f (closedBall 0 1)) {G : E → E}
    (hG : ∀ x ∈ closedBall (0 : E) 1, G (f x) = x) {Gt : E → E}
    (hGt : ContinuousOn Gt (f '' closedBall 0 1))
    (hbound : ∀ y ∈ f '' closedBall 0 1, ‖G y - Gt y‖ ≤ 1) :
    ∃ y ∈ f '' closedBall 0 1, Gt y = 0 := by
  obtain ⟨x, hx, hfx⟩ := hB (fun x => x - Gt (f x))
    (continuousOn_id.sub (hGt.comp hf (mapsTo_image f _))) (by
      intro x hx
      have h := hbound (f x) (mem_image_of_mem f hx)
      rw [hG x hx] at h
      simpa [mem_closedBall, dist_zero_right] using h)
  exact ⟨f x, mem_image_of_mem f hx, by simpa using hfx⟩

/-- Invariance of domain, local form: if `f` is continuous and injective on the closed unit
ball, then `f 0` is an interior point of `f '' closedBall 0 1`. -/
theorem mem_interior_image (hB : BrouwerBall E) {f : E → E}
    (hf : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (closedBall 0 1)) :
    f 0 ∈ interior (f '' closedBall 0 1) := by
  obtain ⟨G, hGc, hGinv⟩ := exists_continuous_leftInverse hf hinj
  have hK : IsCompact (f '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn hf
  have hG0 : G (f 0) = 0 := hGinv 0 (mem_closedBall_self zero_le_one)
  by_contra hnot
  -- `G` is small near `f 0`.
  obtain ⟨η, hη, hηG⟩ := Metric.continuousAt_iff.mp hGc.continuousAt (1 / 10 : ℝ) (by norm_num)
  set ε := η / 2 with hε_def
  have hεpos : 0 < ε := half_pos hη
  -- A point `c` near `f 0` outside the image.
  obtain ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    by_contra! h
    exact hnot (mem_interior.mpr ⟨ball (f 0) ε, fun c hc => h c (mem_ball.mp hc), isOpen_ball,
      mem_ball_self hεpos⟩)
  have hG_small : ∀ y, ‖y - c‖ ≤ ε → ‖G y‖ < 1 / 10 := by
    intro y hy
    have hd : dist y (f 0) < η := by
      calc dist y (f 0) ≤ dist y c + dist c (f 0) := dist_triangle _ _ _
        _ < ε + ε := by rw [dist_eq_norm]; linarith
        _ = η := by rw [hε_def]; ring
    have := hηG hd
    rwa [hG0, dist_zero_right] at this
  -- `Σ₁` and `Σ₂`.
  set S1 : Set E := f '' closedBall 0 1 ∩ {y | ε ≤ ‖y - c‖} with hS1
  set S2 : Set E := sphere c ε with hS2
  have hS1c : IsCompact S1 :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hSc : IsCompact (S1 ∪ S2) := hS1c.union (isCompact_sphere c ε)
  have hne : ∀ y ∈ f '' closedBall 0 1, y - c ≠ 0 := fun y hy h =>
    hc2 (by rwa [sub_eq_zero.mp h] at hy)
  -- The retraction `Φ` of `f '' closedBall 0 1` onto `Σ₁ ∪ Σ₂`.
  let Phi : E → E := fun y => c + max (ε / ‖y - c‖) 1 • (y - c)
  have hPhi_far : ∀ y, ε ≤ ‖y - c‖ → Phi y = y := by
    intro y hy
    have hpos : 0 < ‖y - c‖ := lt_of_lt_of_le hεpos hy
    have h1 : ε / ‖y - c‖ ≤ 1 := (div_le_one hpos).mpr hy
    simp only [Phi, max_eq_right h1, one_smul, add_sub_cancel]
  have hPhi_near : ∀ y, y - c ≠ 0 → ‖y - c‖ ≤ ε → Phi y ∈ S2 := by
    intro y hy0 hy
    have hpos : 0 < ‖y - c‖ := norm_pos_iff.mpr hy0
    have h1 : 1 ≤ ε / ‖y - c‖ := (one_le_div hpos).mpr hy
    simp only [Phi, max_eq_left h1, hS2, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos hεpos hpos)]
    field_simp
  have hPhi_mem : ∀ y ∈ f '' closedBall 0 1, Phi y ∈ S1 ∪ S2 := by
    intro y hy
    rcases le_or_gt ε ‖y - c‖ with h | h
    · left; rw [hPhi_far y h]; exact ⟨hy, h⟩
    · right; exact hPhi_near y (hne y hy) h.le
  have hPhi_cont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine continuousOn_const.add (ContinuousOn.smul ?_ (continuousOn_id.sub continuousOn_const))
    refine ContinuousOn.sup (continuousOn_const.div (continuousOn_id.sub continuousOn_const).norm
      ?_) continuousOn_const
    intro y hy
    exact norm_ne_zero_iff.mpr (hne y hy)
  -- `G` does not vanish on `Σ₁`, hence is bounded below there.
  have hGne : ∀ y ∈ S1, G y ≠ 0 := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩ h
    rw [hGinv x hx] at h
    subst h
    rw [dist_comm, dist_eq_norm] at hc1
    exact absurd hy (not_le.mpr hc1)
  obtain ⟨δ, hδpos, hδle, hδG⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 10 ∧ ∀ y ∈ S1, δ ≤ ‖G y‖ := by
    rcases S1.eq_empty_or_nonempty with h | h
    · exact ⟨1 / 10, by norm_num, le_rfl, by simp [h]⟩
    · obtain ⟨z, hz, hmin⟩ := hS1c.exists_isMinOn h hGc.norm.continuousOn
      exact ⟨min ‖G z‖ (1 / 10), lt_min (norm_pos_iff.mpr (hGne z hz)) (by norm_num),
        min_le_right _ _, fun y hy => (min_le_left _ _).trans (hmin hy)⟩
  -- Smooth approximation `P` and a small regular value `v`.
  obtain ⟨P, hPd, hPG⟩ := differentiable_approx (half_pos hδpos) hSc G hGc
  obtain ⟨v, hv, hvS2⟩ := exists_small_not_mem_image_sphere hPd c hεpos (half_pos hδpos)
  let Gt : E → E := fun y => P (Phi y) - v
  have hGt_cont : ContinuousOn Gt (f '' closedBall 0 1) :=
    (hPd.continuous.comp_continuousOn hPhi_cont).sub continuousOn_const
  have hbound : ∀ y ∈ f '' closedBall 0 1, ‖G y - Gt y‖ ≤ 1 := by
    intro y hy
    rcases le_or_gt ε ‖y - c‖ with h | h
    · have h1 := hPG y (Or.inl ⟨hy, h⟩)
      have e : G y - Gt y = -(P y - G y) + v := by simp only [Gt, hPhi_far y h]; abel
      rw [e]
      calc ‖-(P y - G y) + v‖ ≤ ‖-(P y - G y)‖ + ‖v‖ := norm_add_le _ _
        _ ≤ 1 := by rw [norm_neg]; linarith
    · have hp : Phi y ∈ S2 := hPhi_near y (hne y hy) h.le
      have hp' : ‖Phi y - c‖ = ε := mem_sphere_iff_norm.mp hp
      have h1 := hPG (Phi y) (Or.inr hp)
      have h2 := hG_small (Phi y) hp'.le
      have h3 := hG_small y h.le
      have e : G y - Gt y = (G y - G (Phi y)) - (P (Phi y) - G (Phi y)) + v := by
        simp only [Gt]; abel
      rw [e]
      calc ‖(G y - G (Phi y)) - (P (Phi y) - G (Phi y)) + v‖
          ≤ ‖(G y - G (Phi y)) - (P (Phi y) - G (Phi y))‖ + ‖v‖ := norm_add_le _ _
        _ ≤ ‖G y - G (Phi y)‖ + ‖P (Phi y) - G (Phi y)‖ + ‖v‖ := by
          gcongr; exact norm_sub_le _ _
        _ ≤ ‖G y‖ + ‖G (Phi y)‖ + ‖P (Phi y) - G (Phi y)‖ + ‖v‖ := by
          gcongr; exact norm_sub_le _ _
        _ ≤ 1 := by linarith
  -- Brouwer gives a zero of `Gt`, which is impossible.
  obtain ⟨y, hy, hy0⟩ := stability_of_zero hB hf hGinv hGt_cont hbound
  have hPv : P (Phi y) = v := sub_eq_zero.mp hy0
  rcases hPhi_mem y hy with hS | hS
  · have h1 := hPG (Phi y) (Or.inl hS)
    have h2 := hδG (Phi y) hS
    have h3 : ‖G (Phi y)‖ ≤ ‖P (Phi y) - G (Phi y)‖ + ‖P (Phi y)‖ := by
      calc ‖G (Phi y)‖ = ‖-(P (Phi y) - G (Phi y)) + P (Phi y)‖ := by congr 1; abel
        _ ≤ ‖-(P (Phi y) - G (Phi y))‖ + ‖P (Phi y)‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    have h4 : ‖P (Phi y)‖ = ‖v‖ := by rw [hPv]
    linarith
  · exact hvS2 ⟨Phi y, hS, hPv⟩

/-- Invariance of domain: a continuous injective map on an open set has open image. -/
theorem isOpen_image (hB : BrouwerBall E) {U : Set E} (hU : IsOpen U) {f : E → E}
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  set ε := r / 2 with hε_def
  have hε : 0 < ε := half_pos hr
  have hsub : closedBall x ε ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hrU
  let g : E → E := fun v => x + ε • v
  have hgU : MapsTo g (closedBall 0 1) U := by
    intro v hv
    apply hsub
    rw [mem_closedBall_zero_iff] at hv
    rw [mem_closedBall, dist_eq_norm]
    simp only [g, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
    nlinarith
  have hgc : Continuous g := by fun_prop
  have hginj : Function.Injective g := by
    intro a b h
    simp only [g, add_right_inj] at h
    exact smul_right_injective E hε.ne' h
  have h := mem_interior_image hB (f := f ∘ g) (hf.comp hgc.continuousOn hgU)
    (hinj.comp hginj.injOn hgU)
  have h0 : (f ∘ g) 0 = f x := by simp [g]
  rw [h0] at h
  have hsub' : (f ∘ g) '' closedBall 0 1 ⊆ f '' U := by
    rw [image_comp]; exact image_mono hgU.image_subset
  exact mem_interior_iff_mem_nhds.mp (interior_mono hsub' h)

end General

/-- Brouwer's theorem for the sup-norm unit ball of `ι → ℝ`, which is the cube `[-1, 1]^ι`. -/
theorem brouwerBall_pi {ι : Type*} [Fintype ι] : BrouwerBall (ι → ℝ) := by
  intro F hF hmaps
  have hball : closedBall (0 : ι → ℝ) 1 = Icc (-1) 1 := by
    rw [closedBall_pi _ zero_le_one, ← pi_univ_Icc]
    congr 1
    funext i
    simp [Real.closedBall_eq_Icc]
  rw [hball] at hF hmaps ⊢
  exact Plasticity.Ext.Brouwer F hF hmaps

end Sol_Plasticity_Ext_InvarianceOfDomain

theorem solution {ι : Type*} [Fintype ι] (U : Set (ι → ℝ)) (hU : IsOpen U)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    IsOpen (f '' U) :=
  Sol_Plasticity_Ext_InvarianceOfDomain.isOpen_image
    Sol_Plasticity_Ext_InvarianceOfDomain.brouwerBall_pi hU hf hinj
