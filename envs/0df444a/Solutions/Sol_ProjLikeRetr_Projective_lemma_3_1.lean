-- Prove2me | solution 1 for ProjLikeRetr.Projective.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:39:33.044957+00:00
-- url     : https://prove2.me/submissions/b51c131f-d419-4d20-963f-7304f2a3f744

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open RandomGradFree.Nonsmooth
open scoped ContDiff

namespace ProjLikeRetr.Projective

open ProjLikeRetr.Retractor Filter Topology

set_option linter.unusedSectionVars false

section Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- the coordinate space -/
abbrev FF (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- the coordinate slice subspace `{z | z i = 0 for i ≥ d}` -/
def Sd (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) : Submodule ℝ (FF E) where
  carrier := {z | ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → z i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; simp
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

omit [FiniteDimensional ℝ E] in
theorem mem_Sd {d : ℕ} {z : FF E} : z ∈ Sd E d ↔ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → z i = 0 :=
  Iff.rfl

/-- A chart -/
structure Chart (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) where
  φ : OpenPartialHomeomorph E (FF E)
  hk : 1 ≤ k
  h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source
  h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target

variable {k : ℕ} (c : Chart E k)

/-- derivative of chart -/
noncomputable def Chart.L (y : E) : E →L[ℝ] FF E := fderiv ℝ c.φ y
/-- derivative of inverse chart at the image point -/
noncomputable def Chart.R (y : E) : FF E →L[ℝ] E := fderiv ℝ c.φ.symm (c.φ y)

theorem Chart.hasFDerivAt_L {y : E} (hy : y ∈ c.φ.source) : HasFDerivAt c.φ (c.L y) y := by
  have h := c.h1.contDiffAt (c.φ.open_source.mem_nhds hy)
  exact (h.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp c.hk)).hasFDerivAt

theorem Chart.hasFDerivAt_R {y : E} (hy : y ∈ c.φ.source) : HasFDerivAt c.φ.symm (c.R y) (c.φ y) := by
  have h := c.h2.contDiffAt (c.φ.open_target.mem_nhds (c.φ.map_source hy))
  exact (h.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp c.hk)).hasFDerivAt

theorem Chart.L_R {y : E} (hy : y ∈ c.φ.source) (z : FF E) : c.L y (c.R y z) = z := by
  have h1 : HasFDerivAt c.φ (c.L y) (c.φ.symm (c.φ y)) := by
    rw [c.φ.left_inv hy]; exact c.hasFDerivAt_L hy
  have h2 := h1.comp (c.φ y) (c.hasFDerivAt_R hy)
  have h3 : HasFDerivAt (c.φ ∘ c.φ.symm) (ContinuousLinearMap.id ℝ (FF E)) (c.φ y) := by
    apply (hasFDerivAt_id (c.φ y)).congr_of_eventuallyEq
    filter_upwards [c.φ.open_target.mem_nhds (c.φ.map_source hy)] with w hw
    simp [c.φ.right_inv hw]
  have := h2.unique h3
  have := congrArg (fun f => f z) this
  simpa using this

theorem Chart.R_L {y : E} (hy : y ∈ c.φ.source) (w : E) : c.R y (c.L y w) = w := by
  have h2 := (c.hasFDerivAt_R hy).comp y (c.hasFDerivAt_L hy)
  have h3 : HasFDerivAt (c.φ.symm ∘ c.φ) (ContinuousLinearMap.id ℝ E) y := by
    apply (hasFDerivAt_id y).congr_of_eventuallyEq
    filter_upwards [c.φ.open_source.mem_nhds hy] with w hw
    simp [c.φ.left_inv hw]
  have := h2.unique h3
  have := congrArg (fun f => f w) this
  simpa using this



theorem cone_sub_mem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Submodule ℝ V) {p : V} (hp : p ∈ S) : tangentConeAt ℝ (S : Set V) p ⊆ S := by
  intro v hv
  obtain ⟨α, l, hl, cc, dd, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  have hclosed : IsClosed (S : Set V) := Submodule.closed_of_finiteDimensional S
  refine hclosed.mem_of_tendsto hcd ?_
  filter_upwards [hds] with n hn
  have : dd n ∈ S := by
    have := S.sub_mem hn hp
    simpa using this
  exact S.smul_mem _ this

variable {d : ℕ}

theorem Chart.curve (y : E) (hy : y ∈ c.φ.source) (v : FF E) :
    HasDerivAt (fun t : ℝ => c.φ.symm (c.φ y + t • v)) (c.R y v) 0 := by
  have h1 : HasFDerivAt c.φ.symm (c.R y) (c.φ y + (0:ℝ) • v) := by
    simpa using c.hasFDerivAt_R hy
  have h2 : HasDerivAt (fun t : ℝ => c.φ y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add (c.φ y)
  exact h1.comp_hasDerivAt (0:ℝ) h2

theorem Chart.curve_mem {M : Set E} (hs : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0})
    (y : E) (hy : y ∈ c.φ.source) (v : FF E) (hv : v ∈ Sd E d) (hyM : y ∈ M) :
    ∀ᶠ t : ℝ in 𝓝 0, c.φ.symm (c.φ y + t • v) ∈ M ∧ c.φ.symm (c.φ y + t • v) ∈ c.φ.source := by
  have hcont : Continuous (fun t : ℝ => c.φ y + t • v) := by fun_prop
  have h0 : c.φ y + (0:ℝ) • v ∈ c.φ.target := by simpa using c.φ.map_source hy
  have hev : ∀ᶠ t : ℝ in 𝓝 0, c.φ y + t • v ∈ c.φ.target :=
    hcont.continuousAt.eventually (c.φ.open_target.mem_nhds h0)
  filter_upwards [hev] with t ht
  have hsrc := c.φ.map_target ht
  refine ⟨?_, hsrc⟩
  have : c.φ.symm (c.φ y + t • v) ∈ M ∩ c.φ.source := by
    rw [hs]
    refine ⟨hsrc, ?_⟩
    intro i hi
    rw [c.φ.right_inv ht]
    have hyS : c.φ y ∈ Sd E d := by
      have : y ∈ M ∩ c.φ.source := ⟨hyM, hy⟩
      rw [hs] at this
      exact this.2
    exact (Sd E d).add_mem hyS ((Sd E d).smul_mem t hv) i hi
  exact this.1

theorem Chart.mem_M_iff {M : Set E} (hs : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0})
    {y : E} (hy : y ∈ c.φ.source) : y ∈ M ↔ c.φ y ∈ Sd E d := by
  constructor
  · intro h
    have : y ∈ M ∩ c.φ.source := ⟨h, hy⟩
    rw [hs] at this
    exact this.2
  · intro h
    have : y ∈ {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0} := ⟨hy, h⟩
    rw [← hs] at this
    exact this.1

theorem Chart.tangentSpace_eq {M : Set E} (hs : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0})
    {y : E} (hy : y ∈ c.φ.source) (hyM : y ∈ M) :
    tangentSpace M y = (Sd E d).comap (c.L y : E →ₗ[ℝ] FF E) := by
  apply le_antisymm
  · unfold tangentSpace
    rw [Submodule.span_le]
    intro v hv
    have hv' : v ∈ tangentConeAt ℝ (M ∩ c.φ.source) y := by
      rwa [tangentConeAt_inter_nhds (c.φ.open_source.mem_nhds hy)]
    have h := ((c.hasFDerivAt_L hy).hasFDerivWithinAt (s := M ∩ c.φ.source)).mapsTo_tangent_cone hv'
    have hyS : c.φ y ∈ Sd E d := (c.mem_M_iff hs hy).mp hyM
    have hsub : c.φ '' (M ∩ c.φ.source) ⊆ (Sd E d : Set (FF E)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (c.mem_M_iff hs hx.2).mp hx.1
    have := cone_sub_mem (Sd E d) hyS (tangentConeAt_mono hsub h)
    exact this
  · intro w hw
    apply Submodule.subset_span
    have hLw : c.L y w ∈ Sd E d := hw
    have hder := c.curve y hy (c.L y w)
    rw [c.R_L hy] at hder
    have hslope := hder.tendsto_slope_zero
    have hmem := c.curve_mem hs y hy (c.L y w) hLw hyM
    apply mem_tangentConeAt_of_seq (𝓝[≠] (0:ℝ)) (fun t => t⁻¹)
      (fun t => c.φ.symm (c.φ y + t • c.L y w) - y)
    · have := hder.continuousAt.tendsto
      simp only [zero_smul, add_zero, c.φ.left_inv hy] at this
      have := this.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      simpa using this.sub_const y
    · filter_upwards [nhdsWithin_le_nhds hmem] with t ht
      simpa using ht.1
    · simpa [c.φ.left_inv hy] using hslope

theorem Chart.contDiffAt_R {y : E} (hy : y ∈ c.φ.source) {m : WithTop ℕ∞} (hm : m + 1 ≤ (k : WithTop ℕ∞)) :
    ContDiffAt ℝ m c.R y := by
  have h1 : ContDiffAt ℝ (k : WithTop ℕ∞) c.φ.symm (c.φ y) :=
    c.h2.contDiffAt (c.φ.open_target.mem_nhds (c.φ.map_source hy))
  have h2 : ContDiffAt ℝ m (fderiv ℝ c.φ.symm) (c.φ y) := h1.fderiv_right hm
  have h3 : ContDiffAt ℝ (k : WithTop ℕ∞) c.φ y := c.h1.contDiffAt (c.φ.open_source.mem_nhds hy)
  have h4 : ContDiffAt ℝ m c.φ y := h3.of_le (le_trans (le_self_add) hm)
  exact h2.comp y h4

theorem Chart.contDiffAt_L {y : E} (hy : y ∈ c.φ.source) {m : WithTop ℕ∞} (hm : m + 1 ≤ (k : WithTop ℕ∞)) :
    ContDiffAt ℝ m c.L y := by
  have h3 : ContDiffAt ℝ (k : WithTop ℕ∞) c.φ y := c.h1.contDiffAt (c.φ.open_source.mem_nhds hy)
  exact h3.fderiv_right hm

theorem Chart.continuousAt_R {y : E} (hy : y ∈ c.φ.source) : ContinuousAt c.R y := by
  refine (c.contDiffAt_R hy (m := 0) ?_).continuousAt
  have : ((1 : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast c.hk
  simpa using this

theorem tangent_normalBundle_core (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    Submodule.span ℝ (tangentConeAt ℝ (ProjLikeRetr.Retractor.normalBundle M) (xbar, 0)) =
      (ProjLikeRetr.Retractor.tangentSpace M xbar).prod (ProjLikeRetr.Retractor.normalSpace M xbar) := by
  obtain ⟨hd, hxM, φ, hxs, h1, h2, hs⟩ := hM
  let c : Chart E k := ⟨φ, by omega, h1, h2⟩
  have hs' : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0} := hs
  apply le_antisymm
  · -- cone ⊆ product
    rw [Submodule.span_le]
    rintro ⟨a, b⟩ hab
    obtain ⟨α, l, hl, cc, dd, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hab
    have hd1 : Tendsto (fun n => (dd n).1) l (𝓝 0) := by
      have := (continuous_fst.tendsto (0 : E × E)).comp hd0
      simpa [Function.comp_def] using this
    have hc1 : Tendsto (fun n => cc n • (dd n).1) l (𝓝 a) := by
      have := (continuous_fst.tendsto ((a, b) : E × E)).comp hcd
      simpa [Function.comp_def] using this
    have hc2 : Tendsto (fun n => cc n • (dd n).2) l (𝓝 b) := by
      have := (continuous_snd.tendsto ((a, b) : E × E)).comp hcd
      simpa [Function.comp_def] using this
    have hmem : ∀ᶠ n in l, xbar + (dd n).1 ∈ M ∧ (dd n).2 ∈ normalSpace M (xbar + (dd n).1) := by
      filter_upwards [hds] with n hn
      simpa [normalBundle] using hn
    refine ⟨?_, ?_⟩
    · -- a ∈ tangentSpace
      show a ∈ (tangentSpace M xbar : Set E)
      apply Submodule.subset_span
      refine mem_tangentConeAt_of_seq l cc (fun n => (dd n).1) hd1 ?_ hc1
      filter_upwards [hmem] with n hn using hn.1
    · show b ∈ normalSpace M xbar
      unfold normalSpace
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [c.tangentSpace_eq hs' hxs hxM] at hu
      have hu' : c.L xbar u ∈ Sd E d := hu
      have hsrc : ∀ᶠ n in l, xbar + (dd n).1 ∈ c.φ.source := by
        have : Tendsto (fun n => xbar + (dd n).1) l (𝓝 xbar) := by
          simpa using tendsto_const_nhds.add hd1
        exact this.eventually (c.φ.open_source.mem_nhds hxs)
      have hRc : Tendsto (fun n => c.R (xbar + (dd n).1) (c.L xbar u)) l (𝓝 u) := by
        have h0 : Tendsto (fun n => xbar + (dd n).1) l (𝓝 xbar) := by
          simpa using tendsto_const_nhds.add hd1
        have hcont := (c.continuousAt_R hxs).tendsto.comp h0
        have := (ContinuousLinearMap.apply ℝ E (c.L xbar u)).continuous.continuousAt.tendsto.comp hcont
        simpa [Function.comp_def, c.R_L hxs] using this
      have hin : Tendsto (fun n => inner ℝ (c.R (xbar + (dd n).1) (c.L xbar u)) (cc n • (dd n).2)) l
          (𝓝 (inner ℝ u b)) := hRc.inner hc2
      have hz : ∀ᶠ n in l, inner ℝ (c.R (xbar + (dd n).1) (c.L xbar u)) (cc n • (dd n).2) = 0 := by
        filter_upwards [hmem, hsrc] with n hn hns
        have hT : c.R (xbar + (dd n).1) (c.L xbar u) ∈ tangentSpace M (xbar + (dd n).1) := by
          rw [c.tangentSpace_eq hs' hns hn.1]
          show c.L _ (c.R _ _) ∈ Sd E d
          rw [c.L_R hns]; exact hu'
        have hperp := (Submodule.mem_orthogonal _ _).mp hn.2 _ hT
        rw [inner_smul_right, hperp, mul_zero]
      have h0 : Tendsto (fun n => inner ℝ (c.R (xbar + (dd n).1) (c.L xbar u)) (cc n • (dd n).2)) l (𝓝 0) :=
        tendsto_const_nhds.congr' (hz.mono fun n hn => hn.symm)
      exact tendsto_nhds_unique hin h0
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have h_a : ((a, 0) : E × E) ∈ Submodule.span ℝ (tangentConeAt ℝ (normalBundle M) (xbar, 0)) := by
      have : tangentSpace M xbar ≤ (Submodule.span ℝ (tangentConeAt ℝ (normalBundle M) (xbar, 0))).comap (LinearMap.inl ℝ E E) := by
        unfold tangentSpace
        rw [Submodule.span_le]
        intro v hv
        obtain ⟨α, l, hl, cc, dd, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
        apply Submodule.subset_span
        apply mem_tangentConeAt_of_seq l cc (fun n => (dd n, (0 : E)))
        · have := ((continuous_id.prodMk continuous_const).tendsto (0 : E) |>.comp hd0 :
            Tendsto ((fun x : E => (x, (0:E))) ∘ dd) l (𝓝 ((0:E), (0:E))))
          simpa [Function.comp_def, Prod.mk_zero_zero] using this
        · filter_upwards [hds] with n hn
          simp only [normalBundle, Set.mem_setOf_eq, Prod.mk_add_mk, add_zero]
          exact ⟨hn, Submodule.zero_mem _⟩
        · have := ((continuous_id.prodMk continuous_const).tendsto v |>.comp hcd :
            Tendsto ((fun x : E => (x, (0:E))) ∘ (fun n => cc n • dd n)) l (𝓝 (v, (0:E))))
          simpa [Function.comp_def, Prod.smul_mk] using this
      exact this ha
    have h_b : ((0, b) : E × E) ∈ Submodule.span ℝ (tangentConeAt ℝ (normalBundle M) (xbar, 0)) := by
      apply Submodule.subset_span
      apply mem_tangentConeAt_of_add_smul_mem (l := 𝓝[≠] (0:ℝ)) (c := fun t => t)
      · exact tendsto_id
      · filter_upwards with t
        simp only [normalBundle, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add]
        exact ⟨hxM, Submodule.smul_mem _ _ hb⟩
    have := Submodule.add_mem _ h_a h_b
    simpa using this

/-- the adjoint as a continuous linear map -/
noncomputable def adjL (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    (E →L[ℝ] FF E) →L[ℝ] (FF E →L[ℝ] E) where
  toFun := fun B => ContinuousLinearMap.adjoint B
  map_add' := fun B B' => map_add _ B B'
  map_smul' := fun a B => by simp
  cont := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := FF E)).continuous

theorem adjL_apply (B : E →L[ℝ] FF E) : adjL E B = ContinuousLinearMap.adjoint B := rfl

theorem Chart.normal_aux {y : E} (hy : y ∈ c.φ.source) (u : E)
    (hu : u ∈ ((Sd E d).comap (c.L y : E →ₗ[ℝ] FF E))ᗮ) :
    ContinuousLinearMap.adjoint (c.R y) u ∈ (Sd E d)ᗮ ∧
      ContinuousLinearMap.adjoint (c.L y) (ContinuousLinearMap.adjoint (c.R y) u) = u := by
  constructor
  · rw [Submodule.mem_orthogonal]
    intro s hs
    rw [ContinuousLinearMap.adjoint_inner_right]
    refine (Submodule.mem_orthogonal _ _).mp hu _ ?_
    show c.L y (c.R y s) ∈ Sd E d
    rw [c.L_R hy]; exact hs
  · apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, c.R_L hy]

variable (d)

/-- the map to which the inverse function theorem is applied -/
noncomputable def Chart.G (z : FF E) : E :=
  c.φ.symm ((Sd E d).starProjection z) +
    (ContinuousLinearMap.adjoint (c.L (c.φ.symm ((Sd E d).starProjection z)))) (z - (Sd E d).starProjection z)

/-- its derivative at the base point -/
noncomputable def Chart.G' (y : E) : FF E →L[ℝ] E :=
  (c.R y).comp (Sd E d).starProjection +
    (ContinuousLinearMap.adjoint (c.L y)).comp (ContinuousLinearMap.id ℝ (FF E) - (Sd E d).starProjection)

variable {d}

theorem PS_self {z : FF E} (hz : z ∈ Sd E d) : (Sd E d).starProjection z = z :=
  Submodule.starProjection_eq_self_iff.mpr hz

theorem Chart.G_base {xbar : E} (hx : xbar ∈ c.φ.source) (hxS : c.φ xbar ∈ Sd E d) :
    c.G d (c.φ xbar) = xbar := by
  simp [Chart.G, PS_self hxS, c.φ.left_inv hx]

theorem Chart.contDiffAt_G {xbar : E} (hx : xbar ∈ c.φ.source) (hxS : c.φ xbar ∈ Sd E d)
    {m : WithTop ℕ∞} (hm : m + 1 ≤ (k : WithTop ℕ∞)) : ContDiffAt ℝ m (c.G d) (c.φ xbar) := by
  have hmk : m ≤ (k : WithTop ℕ∞) := le_trans le_self_add hm
  have hPS : (Sd E d).starProjection (c.φ xbar) = c.φ xbar := PS_self hxS
  have hsymm : ContDiffAt ℝ m c.φ.symm ((Sd E d).starProjection (c.φ xbar)) := by
    rw [hPS]
    exact (c.h2.contDiffAt (c.φ.open_target.mem_nhds (c.φ.map_source hx))).of_le hmk
  have hψ : ContDiffAt ℝ m (fun z => c.φ.symm ((Sd E d).starProjection z)) (c.φ xbar) :=
    hsymm.comp _ (Sd E d).starProjection.contDiff.contDiffAt
  have hψ0 : c.φ.symm ((Sd E d).starProjection (c.φ xbar)) = xbar := by
    rw [hPS, c.φ.left_inv hx]
  have hL : ContDiffAt ℝ m c.L (c.φ.symm ((Sd E d).starProjection (c.φ xbar))) := by
    rw [hψ0]; exact c.contDiffAt_L hx hm
  have hB : ContDiffAt ℝ m (fun z => adjL E (c.L (c.φ.symm ((Sd E d).starProjection z)))) (c.φ xbar) :=
    (adjL E).contDiff.contDiffAt.comp _ (ContDiffAt.comp (f := fun z => c.φ.symm ((Sd E d).starProjection z)) (c.φ xbar) hL hψ)
  have hu : ContDiffAt ℝ m (fun z : FF E => z - (Sd E d).starProjection z) (c.φ xbar) :=
    contDiffAt_id.sub (Sd E d).starProjection.contDiff.contDiffAt
  exact hψ.add (hB.clm_apply hu)

theorem Chart.hasFDerivAt_G {xbar : E} (hx : xbar ∈ c.φ.source) (hxS : c.φ xbar ∈ Sd E d)
    (hk2 : 2 ≤ k) : HasFDerivAt (c.G d) (c.G' d xbar) (c.φ xbar) := by
  have hPS : (Sd E d).starProjection (c.φ xbar) = c.φ xbar := PS_self hxS
  have hm1 : (1 : WithTop ℕ∞) + 1 ≤ (k : WithTop ℕ∞) := by
    have : ((2 : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk2
    simpa [one_add_one_eq_two] using this
  have hψ0 : c.φ.symm ((Sd E d).starProjection (c.φ xbar)) = xbar := by
    rw [hPS, c.φ.left_inv hx]
  have hR : HasFDerivAt c.φ.symm (c.R xbar) ((Sd E d).starProjection (c.φ xbar)) := by
    rw [hPS]; exact c.hasFDerivAt_R hx
  have hψ : HasFDerivAt (fun z => c.φ.symm ((Sd E d).starProjection z))
      ((c.R xbar).comp (Sd E d).starProjection) (c.φ xbar) :=
    hR.comp (c.φ xbar) (Sd E d).starProjection.hasFDerivAt
  have hL : ContDiffAt ℝ 1 c.L (c.φ.symm ((Sd E d).starProjection (c.φ xbar))) := by
    rw [hψ0]; exact c.contDiffAt_L hx hm1
  have hLd : DifferentiableAt ℝ (fun z => adjL E (c.L (c.φ.symm ((Sd E d).starProjection z)))) (c.φ xbar) := by
    have hψc : ContDiffAt ℝ 1 (fun z => c.φ.symm ((Sd E d).starProjection z)) (c.φ xbar) := by
      have : ContDiffAt ℝ 1 c.φ.symm ((Sd E d).starProjection (c.φ xbar)) := by
        rw [hPS]
        exact (c.h2.contDiffAt (c.φ.open_target.mem_nhds (c.φ.map_source hx))).of_le
          (by exact_mod_cast c.hk)
      exact this.comp _ (Sd E d).starProjection.contDiff.contDiffAt
    have := (adjL E).contDiff.contDiffAt.comp _ (ContDiffAt.comp (f := fun z => c.φ.symm ((Sd E d).starProjection z)) (c.φ xbar) hL hψc)
    exact this.differentiableAt one_ne_zero
  have hB := hLd.hasFDerivAt
  have hu : HasFDerivAt (fun z : FF E => z - (Sd E d).starProjection z)
      (ContinuousLinearMap.id ℝ (FF E) - (Sd E d).starProjection) (c.φ xbar) :=
    (hasFDerivAt_id _).sub (Sd E d).starProjection.hasFDerivAt
  have hcl := hB.clm_apply hu
  have := hψ.add hcl
  refine this.congr_fderiv ?_
  ext z
  simp [Chart.G', hPS, adjL_apply, c.φ.left_inv hx]

theorem Chart.G'_injective {xbar : E} (hx : xbar ∈ c.φ.source) : Function.Injective (c.G' d xbar) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  set p := (Sd E d).starProjection z with hp
  have hpS : p ∈ Sd E d := Submodule.starProjection_apply_mem _ _
  have hqS : z - p ∈ (Sd E d)ᗮ := Submodule.sub_starProjection_mem_orthogonal z
  have hz' : c.R xbar p + ContinuousLinearMap.adjoint (c.L xbar) (z - p) = 0 := by
    simpa [Chart.G', hp] using hz
  have h1 : inner ℝ (c.R xbar p) (ContinuousLinearMap.adjoint (c.L xbar) (z - p)) = 0 := by
    rw [ContinuousLinearMap.adjoint_inner_right, c.L_R hx]
    exact (Submodule.mem_orthogonal _ _).mp hqS _ hpS
  have h2 : c.R xbar p = - ContinuousLinearMap.adjoint (c.L xbar) (z - p) := eq_neg_of_add_eq_zero_left hz'
  have h3 : inner ℝ (c.R xbar p) (c.R xbar p) = 0 := by
    nth_rewrite 2 [h2]
    rw [inner_neg_right, h1, neg_zero]
  have h4 : c.R xbar p = 0 := inner_self_eq_zero.mp h3
  have hp0 : p = 0 := by
    have := c.L_R hx p
    rw [h4] at this
    simpa using this.symm
  have hA : ContinuousLinearMap.adjoint (c.L xbar) (z - p) = 0 := by
    rw [h4] at h2; exact neg_eq_zero.mp h2.symm
  have hq0 : z - p = 0 := by
    apply ext_inner_right ℝ
    intro v
    have := congrArg (fun a => inner ℝ a (c.R xbar v)) hA
    simp only [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, c.L_R hx] at this
    simpa using this
  rw [hp0] at hq0
  simpa using hq0

theorem Chart.G'_equiv {xbar : E} (hx : xbar ∈ c.φ.source) :
    ∃ e : FF E ≃L[ℝ] E, (e : FF E →L[ℝ] E) = c.G' d xbar := by
  have hinj := c.G'_injective (d := d) hx
  have hfr : Module.finrank ℝ (FF E) = Module.finrank ℝ E := by simp
  have hsurj : Function.Surjective (c.G' d xbar) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (c.G' d xbar : FF E →ₗ[ℝ] E)) hfr).mp hinj
  refine ⟨ContinuousLinearEquiv.ofBijective (c.G' d xbar) ?_ ?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mpr hinj
  · exact LinearMap.range_eq_top.mpr hsurj
  · ext z; simp

theorem Chart.first_order {M : Set E}
    (hs : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0})
    {z : E} (hz : z ∈ c.φ.source) (hzM : z ∈ M) (x : E) (hmin : ∀ w ∈ M, ‖x - z‖ ≤ ‖x - w‖) :
    x - z ∈ ((Sd E d).comap (c.L z : E →ₗ[ℝ] FF E))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hLw : c.L z w ∈ Sd E d := hw
  have hder := c.curve z hz (c.L z w)
  rw [c.R_L hz] at hder
  have hd2 := ((hasDerivAt_const (0:ℝ) x).sub hder).norm_sq
  have hmem := c.curve_mem hs z hz (c.L z w) hLw hzM
  have hloc : IsLocalMin (fun t : ℝ => ‖x - c.φ.symm (c.φ z + t • c.L z w)‖ ^ 2) 0 := by
    filter_upwards [hmem] with t ht
    have h0 : ‖x - c.φ.symm (c.φ z + (0:ℝ) • c.L z w)‖ = ‖x - z‖ := by simp [c.φ.left_inv hz]
    simp only [h0]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin _ ht.1) 2
  have := hloc.hasDerivAt_eq_zero hd2
  simp [c.φ.left_inv hz] at this
  rw [real_inner_comm]
  exact this

theorem Chart.exists_MP {M : Set E}
    (hs : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0})
    {xbar : E} (hxM : xbar ∈ M) {r : ℝ} (hr : Metric.closedBall xbar r ⊆ c.φ.source)
    {x : E} (hx : dist x xbar < r / 2) : ∃ z, IsMetricProjection M x z := by
  have hKeq : M ∩ Metric.closedBall xbar r =
      Metric.closedBall xbar r ∩ c.φ ⁻¹' (Sd E d : Set (FF E)) := by
    ext y
    constructor
    · rintro ⟨hyM, hyb⟩
      exact ⟨hyb, (c.mem_M_iff hs (hr hyb)).mp hyM⟩
    · rintro ⟨hyb, hyS⟩
      exact ⟨(c.mem_M_iff hs (hr hyb)).mpr hyS, hyb⟩
  have hclosed : IsClosed (M ∩ Metric.closedBall xbar r) := by
    rw [hKeq]
    exact (c.φ.continuousOn.mono hr).preimage_isClosed_of_isClosed Metric.isClosed_closedBall
      (Submodule.closed_of_finiteDimensional (Sd E d))
  have hcomp : IsCompact (M ∩ Metric.closedBall xbar r) :=
    (isCompact_closedBall xbar r).of_isClosed_subset hclosed Set.inter_subset_right
  have hr0 : 0 < r := by
    have := dist_nonneg (x := x) (y := xbar)
    linarith
  obtain ⟨z, hzK, hzmin⟩ := hcomp.exists_isMinOn ⟨xbar, hxM, Metric.mem_closedBall_self hr0.le⟩
    (f := fun w => ‖x - w‖) (by fun_prop)
  have hzx : ‖x - z‖ ≤ ‖x - xbar‖ := hzmin ⟨hxM, Metric.mem_closedBall_self hr0.le⟩
  refine ⟨z, hzK.1, fun w hw => ?_⟩
  by_cases hwb : w ∈ Metric.closedBall xbar r
  · exact hzmin ⟨hw, hwb⟩
  · have h1 : r < dist w xbar := by simpa [Metric.mem_closedBall] using hwb
    have h2 : dist w xbar ≤ ‖x - w‖ + ‖x - xbar‖ := by
      rw [dist_eq_norm]
      calc ‖w - xbar‖ = ‖(x - xbar) - (x - w)‖ := by congr 1; abel
        _ ≤ ‖x - xbar‖ + ‖x - w‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have h3 : ‖x - xbar‖ < r / 2 := by rwa [← dist_eq_norm]
    linarith

end Chart

theorem lemma_3_1_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ δ > 0, ∃ P : E → E,
      (∀ x ∈ Metric.ball xbar δ, {z | IsMetricProjection M x z} = {P x}) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection xbar := by
  obtain ⟨hd, hxM, φ, hxs, h1, h2, hs⟩ := hM
  let c : Chart E k := ⟨φ, by omega, h1, h2⟩
  have hs' : M ∩ c.φ.source = {x | x ∈ c.φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → c.φ x i = 0} := hs
  have hxs' : xbar ∈ c.φ.source := hxs
  have hz0S : c.φ xbar ∈ Sd E d := (c.mem_M_iff hs' hxs').mp hxM
  have hm : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ (k : WithTop ℕ∞) := by
    have : (k - 1) + 1 ≤ k := by omega
    exact_mod_cast this
  have hm0 : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have : k - 1 ≠ 0 := by omega
    exact_mod_cast this
  have hmtop : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ ∞ := by
    simp
  have hGd : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (c.G d) (c.φ xbar) :=
    c.contDiffAt_G hxs' hz0S hm
  obtain ⟨e, he⟩ := c.G'_equiv (d := d) hxs'
  have hGf : HasFDerivAt (c.G d) (e : FF E →L[ℝ] E) (c.φ xbar) := by
    rw [he]; exact c.hasFDerivAt_G hxs' hz0S hk
  have hstrict := hGd.hasStrictFDerivAt' hGf hm0
  have hGbase : c.G d (c.φ xbar) = xbar := c.G_base hxs' hz0S
  -- the local inverse
  set H : E → FF E := hGd.localInverse hGf hm0 with hH
  have hHG : ∀ᶠ z in 𝓝 (c.φ xbar), H (c.G d z) = z := hstrict.eventually_left_inverse
  have hHbase : H xbar = c.φ xbar := by
    have := hstrict.localInverse_apply_image
    rw [hGbase] at this
    exact this
  have hHsm : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) H xbar := by
    have := hGd.to_localInverse hGf hm0
    rwa [hGbase] at this
  have hHder : HasFDerivAt H (e.symm : E →L[ℝ] FF E) xbar := by
    have := hstrict.to_localInverse.hasFDerivAt
    rwa [hGbase] at this
  -- the projection map
  let P : E → E := fun x => c.φ.symm ((Sd E d).starProjection (H x))
  have hPS0 : (Sd E d).starProjection (c.φ xbar) = c.φ xbar := PS_self hz0S
  have hPsm : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P xbar := by
    have hsymm : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) c.φ.symm ((Sd E d).starProjection (H xbar)) := by
      rw [hHbase, hPS0]
      exact (c.h2.contDiffAt (c.φ.open_target.mem_nhds (c.φ.map_source hxs'))).of_le
        (le_trans le_self_add hm)
    exact hsymm.comp xbar ((Sd E d).starProjection.contDiff.contDiffAt.comp xbar hHsm)
  have hPev : ∀ᶠ y in 𝓝 xbar, ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P y := hPsm.eventually hmtop
  -- derivative
  have hPder : HasFDerivAt P ((c.R xbar).comp ((Sd E d).starProjection.comp (e.symm : E →L[ℝ] FF E))) xbar := by
    have hR : HasFDerivAt c.φ.symm (c.R xbar) ((Sd E d).starProjection (H xbar)) := by
      rw [hHbase, hPS0]; exact c.hasFDerivAt_R hxs'
    have hPSd : HasFDerivAt (fun x => (Sd E d).starProjection (H x))
        ((Sd E d).starProjection.comp (e.symm : E →L[ℝ] FF E)) xbar :=
      (Sd E d).starProjection.hasFDerivAt.comp xbar hHder
    exact hR.comp xbar hPSd
  have hTeq := c.tangentSpace_eq hs' hxs' hxM
  have hproj : (c.R xbar).comp ((Sd E d).starProjection.comp (e.symm : E →L[ℝ] FF E)) =
      (tangentSpace M xbar).starProjection := by
    ext x
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hTeq]
      show c.L xbar (c.R xbar _) ∈ Sd E d
      rw [c.L_R hxs']
      exact Submodule.starProjection_apply_mem _ _
    · intro w hw
      rw [hTeq] at hw
      have hw' : c.L xbar w ∈ Sd E d := hw
      set u0 := e.symm x with hu0
      have hex : c.R xbar ((Sd E d).starProjection u0) +
          ContinuousLinearMap.adjoint (c.L xbar) (u0 - (Sd E d).starProjection u0) = x := by
        have := congrArg (fun f => f u0) he
        simp only [ContinuousLinearEquiv.coe_coe] at this
        have h3 : e u0 = x := by simp [hu0]
        rw [← h3, this]
        simp [Chart.G']
      have : x - c.R xbar ((Sd E d).starProjection u0) =
          ContinuousLinearMap.adjoint (c.L xbar) (u0 - (Sd E d).starProjection u0) := by
        rw [← hex]; abel
      show inner ℝ (x - c.R xbar ((Sd E d).starProjection u0)) w = 0
      rw [this, ContinuousLinearMap.adjoint_inner_left]
      exact (Submodule.mem_orthogonal _ _).mp (Submodule.sub_starProjection_mem_orthogonal u0) _ hw' |> fun h => by
        rw [real_inner_comm]; exact h
  -- neighbourhood constants
  obtain ⟨ε, hε, hεH⟩ : ∃ ε > 0, ∀ z : FF E, dist z (c.φ xbar) < ε → H (c.G d z) = z := by
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hHG
    exact ⟨ε, hε, fun z hz => h hz⟩
  set C : ℝ := ‖c.R xbar‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  have hev : ∀ᶠ y in 𝓝 xbar, y ∈ c.φ.source ∧ dist (c.φ y) (c.φ xbar) < ε / 2 ∧ ‖c.R y‖ ≤ C ∧
      ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P y := by
    have a1 := c.φ.open_source.mem_nhds hxs'
    have a2 : ∀ᶠ y in 𝓝 xbar, dist (c.φ y) (c.φ xbar) < ε / 2 :=
      (c.φ.continuousAt hxs').eventually (Metric.ball_mem_nhds _ (by positivity))
    have a3 : ∀ᶠ y in 𝓝 xbar, ‖c.R y‖ < C :=
      Filter.Tendsto.eventually_lt_const (by linarith : ‖c.R xbar‖ < C)
        (c.continuousAt_R hxs').norm.tendsto
    filter_upwards [a1, a2, a3, hPev] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3.le, h4⟩
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hδ0 : 0 < min (ρ / 4) (ε / (4 * C)) := by positivity
  have hδρ : min (ρ / 4) (ε / (4 * C)) ≤ ρ / 4 := min_le_left _ _
  have hδε : min (ρ / 4) (ε / (4 * C)) ≤ ε / (4 * C) := min_le_right _ _
  refine ⟨min (ρ / 4) (ε / (4 * C)), hδ0, P, ?_, ?_, ?_⟩
  · intro x hx
    have hxd : dist x xbar < min (ρ / 4) (ε / (4 * C)) := hx
    have hexists : ∃ z, IsMetricProjection M x z := by
      refine c.exists_MP hs' hxM (r := ρ / 2) ?_ (by linarith)
      intro y hy
      have : y ∈ Metric.ball xbar ρ := by
        rw [Metric.mem_ball]
        have := Metric.mem_closedBall.mp hy
        linarith
      exact (hρ y this).1
    have hkey : ∀ z, IsMetricProjection M x z → z = P x := by
      rintro z ⟨hzM, hzmin⟩
      have hxz : ‖x - z‖ ≤ ‖x - xbar‖ := hzmin xbar hxM
      have hxb : ‖x - xbar‖ < min (ρ / 4) (ε / (4 * C)) := by rwa [← dist_eq_norm]
      have hxz' : ‖x - z‖ < min (ρ / 4) (ε / (4 * C)) := lt_of_le_of_lt hxz hxb
      have hzb : z ∈ Metric.ball xbar ρ := by
        rw [Metric.mem_ball]
        calc dist z xbar ≤ dist z x + dist x xbar := dist_triangle _ _ _
          _ = ‖x - z‖ + dist x xbar := by rw [dist_comm, dist_eq_norm]
          _ < ρ := by linarith
      obtain ⟨hzs, hzφ, hzR, -⟩ := hρ z hzb
      have hperp := c.first_order hs' hzs hzM x hzmin
      obtain ⟨hwS, hAw⟩ := c.normal_aux hzs (x - z) hperp
      set w := ContinuousLinearMap.adjoint (c.R z) (x - z) with hw
      have hφzS : c.φ z ∈ Sd E d := (c.mem_M_iff hs' hzs).mp hzM
      have hPSz' : (Sd E d).starProjection (c.φ z + w) = c.φ z := by
        apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hφzS
        intro s hs0
        have : c.φ z + w - c.φ z = w := by abel
        rw [this, real_inner_comm]
        exact (Submodule.mem_orthogonal _ _).mp hwS s hs0
      have hGz' : c.G d (c.φ z + w) = x := by
        simp only [Chart.G, hPSz', c.φ.left_inv hzs, add_sub_cancel_left]
        rw [hAw]; abel
      have hnw : ‖w‖ ≤ C * ‖x - z‖ := by
        have h1 : ‖w‖ ≤ ‖ContinuousLinearMap.adjoint (c.R z)‖ * ‖x - z‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have h2 : ‖(ContinuousLinearMap.adjoint (c.R z) : E →L[ℝ] FF E)‖ = ‖c.R z‖ :=
          LinearIsometryEquiv.norm_map (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := FF E) (F := E)) (c.R z)
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right hzR (norm_nonneg _))
      have hCd : C * min (ρ / 4) (ε / (4 * C)) ≤ ε / 4 := by
        calc C * min (ρ / 4) (ε / (4 * C)) ≤ C * (ε / (4 * C)) := by gcongr
          _ = ε / 4 := by field_simp
      have hdist : dist (c.φ z + w) (c.φ xbar) < ε := by
        calc dist (c.φ z + w) (c.φ xbar) ≤ dist (c.φ z + w) (c.φ z) + dist (c.φ z) (c.φ xbar) :=
              dist_triangle _ _ _
          _ = ‖w‖ + dist (c.φ z) (c.φ xbar) := by rw [dist_eq_norm]; simp
          _ < ε := by
              have : ‖w‖ ≤ C * min (ρ / 4) (ε / (4 * C)) :=
                hnw.trans (mul_le_mul_of_nonneg_left hxz'.le hCpos.le)
              linarith
      have hH := hεH _ hdist
      rw [hGz'] at hH
      show z = c.φ.symm ((Sd E d).starProjection (H x))
      rw [hH, hPSz', c.φ.left_inv hzs]
    obtain ⟨z1, hz1⟩ := hexists
    have hz1P := hkey z1 hz1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact hkey z
    · intro hz; rw [hz, ← hz1P]; exact hz1
  · intro y hy
    have hy' : y ∈ Metric.ball xbar ρ := Metric.ball_subset_ball (by linarith) hy
    exact (hρ y hy').2.2.2.contDiffWithinAt
  · rw [← hproj]; exact hPder

end ProjLikeRetr.Projective

open ProjLikeRetr.Projective


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ δ > 0, ∃ P : E → E,
      (∀ x ∈ Metric.ball xbar δ, {z | IsMetricProjection M x z} = {P x}) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection xbar := by
  exact lemma_3_1_core k d hk M xbar hM
