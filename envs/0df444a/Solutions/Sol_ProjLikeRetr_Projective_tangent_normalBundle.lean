-- Prove2me | solution 1 for ProjLikeRetr.Projective.tangent_normalBundle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:31:19.592389+00:00
-- url     : https://prove2.me/submissions/60ec210e-8ac0-4656-aac0-a3f9a74dc4a2

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle



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

end Chart

end ProjLikeRetr.Projective

open ProjLikeRetr.Projective


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    Submodule.span ℝ (tangentConeAt ℝ (ProjLikeRetr.Retractor.normalBundle M) (xbar, 0)) =
      (ProjLikeRetr.Retractor.tangentSpace M xbar).prod (ProjLikeRetr.Retractor.normalSpace M xbar) := by
  exact tangent_normalBundle_core k d hk M xbar hM
