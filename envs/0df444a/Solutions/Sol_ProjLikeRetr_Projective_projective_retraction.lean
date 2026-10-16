-- Prove2me | solution 1 for ProjLikeRetr.Projective.projective_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T02:00:56.311976+00:00
-- url     : https://prove2.me/submissions/3816f1ee-25db-4f72-b5e3-94f95b2d1d50

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Projective_IsRetractionAt

set_option autoImplicit false

open RandomGradFree.Nonsmooth
open scoped Topology

namespace PLR80850C


open Filter Topology in
theorem P2M0c1c1cfb_key {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (x p : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M p) (hp : IsMetricProjection M x p)
    (v : E) (hv : v ∈ tangentConeAt ℝ M p) : inner ℝ (x - p) v = 0 := by
  obtain ⟨-, hpM, φ, hpS, hφ, hψ, hslice⟩ := hM
  have hk1 : ((k : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hSn : φ.source ∈ 𝓝 p := φ.open_source.mem_nhds hpS
  have hpT : φ p ∈ φ.target := φ.map_source hpS
  have hTn : φ.target ∈ 𝓝 (φ p) := φ.open_target.mem_nhds hpT
  have hφd : DifferentiableAt ℝ φ p := (hφ.differentiableOn hk1).differentiableAt hSn
  have hψd : DifferentiableAt ℝ φ.symm (φ p) := (hψ.differentiableOn hk1).differentiableAt hTn
  set A := fderiv ℝ φ p with hA
  set B := fderiv ℝ φ.symm (φ p) with hB
  have hsl : ∀ y, y ∈ M ∩ φ.source ↔
      (y ∈ φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ y i = 0) := by
    intro y; rw [hslice]; rfl
  have hpφ : ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ p i = 0 := ((hsl p).1 ⟨hpM, hpS⟩).2
  -- B ∘ A = id
  have hBA : ∀ u, B (A u) = u := by
    have h1 : HasFDerivAt (φ.symm ∘ φ) (B.comp A) p := hψd.hasFDerivAt.comp p hφd.hasFDerivAt
    have h2 : HasFDerivAt (φ.symm ∘ φ) (ContinuousLinearMap.id ℝ E) p :=
      (hasFDerivAt_id p).congr_of_eventuallyEq (by
        filter_upwards [φ.eventually_left_inverse hpS] with y hy
        exact hy)
    have h3 := h1.unique h2
    intro u
    have := congrArg (fun L : E →L[ℝ] E => L u) h3
    simpa using this
  -- A v lies in the slice
  have hAv : ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → (A v) i = 0 := by
    intro i hi
    have hg : HasFDerivAt (fun y => (EuclideanSpace.proj i : _ →L[ℝ] ℝ) (φ y))
        ((EuclideanSpace.proj i : _ →L[ℝ] ℝ).comp A) p :=
      (EuclideanSpace.proj i : _ →L[ℝ] ℝ).hasFDerivAt.comp p hφd.hasFDerivAt
    have hg0 : HasFDerivWithinAt (fun y => (EuclideanSpace.proj i : _ →L[ℝ] ℝ) (φ y))
        (0 : E →L[ℝ] ℝ) (M ∩ φ.source) p := by
      refine (hasFDerivWithinAt_const (0 : ℝ) p (M ∩ φ.source)).congr ?_ ?_
      · intro y hy
        have := ((hsl y).1 hy).2 i hi
        simpa using this
      · simpa using hpφ i hi
    have hv' : v ∈ tangentConeAt ℝ (M ∩ φ.source) p := by
      rw [tangentConeAt_inter_nhds hSn]; exact hv
    have := hg.hasFDerivWithinAt.unique_on hg0 hv'
    simpa using this
  -- the curve
  set w := A v with hw
  let c : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun t => φ p + t • w
  have hc0 : c 0 = φ p := by simp [c]
  have hcd : HasDerivAt c w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (φ p)
    simpa [c] using this
  have hct : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ φ.target := by
    have hcont : Continuous c := by fun_prop
    have := hcont.tendsto 0
    rw [hc0] at this
    exact this hTn
  have hγ : HasDerivAt (φ.symm ∘ c) (B w) 0 :=
    hψd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcd hc0.symm
  have hγ0 : (φ.symm ∘ c) 0 = p := by
    simp only [Function.comp, hc0]; exact φ.left_inv hpS
  have hmin : IsLocalMin (fun t => ‖x - (φ.symm ∘ c) t‖ ^ 2) 0 := by
    filter_upwards [hct] with t ht
    have hs : φ.symm (c t) ∈ φ.source := φ.map_target ht
    have hr : φ (φ.symm (c t)) = c t := φ.right_inv ht
    have hmem : φ.symm (c t) ∈ M ∩ φ.source := by
      refine (hsl _).2 ⟨hs, ?_⟩
      intro i hi
      rw [hr]
      simp [c, hpφ i hi, hAv i hi]
    have := hp.2 _ hmem.1
    rw [hγ0]
    simp only [Function.comp]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hd := (hγ.const_sub x).norm_sq
  have h0 := hmin.hasDerivAt_eq_zero hd
  rw [hγ0, hBA] at h0
  rw [inner_neg_right] at h0
  linarith

open RandomGradFree.Nonsmooth in
theorem optimality_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (x p : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M p) (hp : IsMetricProjection M x p) :
    p ∈ M ∧ x - p ∈ ProjLikeRetr.Retractor.normalSpace M p := by
  refine ⟨hp.1, ?_⟩
  unfold ProjLikeRetr.Retractor.normalSpace ProjLikeRetr.Retractor.tangentSpace
  rw [Submodule.mem_orthogonal']
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv => exact P2M0c1c1cfb_key k d hk M x p hM hp v hv
  | zero => simp
  | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
  | smul r a _ ha => rw [inner_smul_right, ha, mul_zero]


theorem nearest_exists_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ ε > 0, ∀ y ∈ Metric.ball xbar ε, ∃ z, IsMetricProjection M y z := by
  obtain ⟨-, hxM, φ, hxφ, -, -, h3⟩ := hM
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 φ.open_source xbar hxφ
  have hcb : Metric.closedBall xbar (ρ / 2) ⊆ φ.source :=
    fun z hz => hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (by linarith))
  set K : Set E := M ∩ Metric.closedBall xbar (ρ / 2) with hK
  have hKeq : K = Metric.closedBall xbar (ρ / 2) ∩
      φ ⁻¹' {w | ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → w i = 0} := by
    ext z
    constructor
    · rintro ⟨hzM, hzb⟩
      have : z ∈ M ∩ φ.source := ⟨hzM, hcb hzb⟩
      rw [h3] at this
      exact ⟨hzb, this.2⟩
    · rintro ⟨hzb, hz⟩
      have : z ∈ {x | x ∈ φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ x i = 0} :=
        ⟨hcb hzb, hz⟩
      rw [← h3] at this
      exact ⟨this.1, hzb⟩
  have hclosedset : IsClosed {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) |
      ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → w i = 0} := by
    have : {w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) |
      ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → w i = 0} =
        ⋂ i : Fin (Module.finrank ℝ E), {w | d ≤ i.val → w i = 0} := by
      ext w; simp
    rw [this]
    refine isClosed_iInter fun i => ?_
    by_cases hi : d ≤ i.val
    · simp only [hi, true_imp_iff]
      exact isClosed_eq (by fun_prop) continuous_const
    · simp [hi]
  have hKclosed : IsClosed K := by
    rw [hKeq]
    exact (φ.continuousOn.mono hcb).preimage_isClosed_of_isClosed Metric.isClosed_closedBall hclosedset
  have hKcomp : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKclosed
      (Metric.isBounded_closedBall.subset (by rw [hK]; exact Set.inter_subset_right))
  have hxK : xbar ∈ K := ⟨hxM, Metric.mem_closedBall_self (by linarith)⟩
  refine ⟨ρ / 4, by linarith, fun y hy => ?_⟩
  obtain ⟨z, hzK, hzmin⟩ := hKcomp.exists_isMinOn ⟨xbar, hxK⟩
    (f := fun w => ‖y - w‖) (by fun_prop)
  refine ⟨z, hzK.1, fun w hw => ?_⟩
  by_cases hwb : w ∈ Metric.closedBall xbar (ρ / 2)
  · exact hzmin ⟨hw, hwb⟩
  · have h1 : ρ / 2 < dist w xbar := by simpa [Metric.mem_closedBall] using hwb
    have h2 : dist y xbar < ρ / 4 := Metric.mem_ball.1 hy
    have h3' : ‖y - z‖ ≤ ‖y - xbar‖ := hzmin hxK
    have h4 : dist w xbar ≤ dist w y + dist y xbar := dist_triangle _ _ _
    simp only [dist_eq_norm] at h4 h2 h1
    have h5 : ‖w - y‖ = ‖y - w‖ := norm_sub_rev _ _
    linarith



noncomputable def trunc (n d : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 (fun i : Fin n => if i.val < d then u i else 0)
      map_add' := by
        intro a b; ext i; by_cases h : i.val < d <;> simp [h]
      map_smul' := by
        intro c a; ext i; by_cases h : i.val < d <;> simp [h] }

theorem trunc_apply (n d : ℕ) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    trunc n d u i = if i.val < d then u i else 0 := rfl

theorem trunc_idem (n d : ℕ) (u : EuclideanSpace ℝ (Fin n)) : trunc n d (trunc n d u) = trunc n d u := by
  ext i; by_cases h : i.val < d <;> simp [trunc_apply, h]

theorem trunc_eq_self_iff (n d : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    trunc n d u = u ↔ ∀ i : Fin n, d ≤ i.val → u i = 0 := by
  constructor
  · intro h i hi
    have := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w i) h
    simp only [trunc_apply] at this
    have hi' : ¬ i.val < d := by omega
    simpa [hi'] using this.symm
  · intro h
    ext i
    by_cases hi : i.val < d
    · simp [trunc_apply, hi]
    · have := h i (by omega)
      simp [trunc_apply, hi, this]

theorem inner_trunc_sub (n d : ℕ) (a b : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (trunc n d a) (b - trunc n d b) = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < d
  · simp [trunc_apply, hi]
  · simp [trunc_apply, hi]

noncomputable def adjCLM (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F] :
    (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
  { toFun := fun A => ContinuousLinearMap.adjoint A
    map_add' := fun A B => map_add _ A B
    map_smul' := fun c A => by simp
    cont := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous }

theorem adjCLM_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (A : E →L[ℝ] F) : adjCLM E F A = ContinuousLinearMap.adjoint A := rfl

theorem adjCLM_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (A : E →L[ℝ] F) (y : F) (x : E) : inner ℝ (adjCLM E F A y) x = inner ℝ y (A x) :=
  ContinuousLinearMap.adjoint_inner_left A x y

/-- injectivity of `Dm ∘ π + Dᵀ ∘ (1 - π)` -/
theorem L_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n d : ℕ)
    (D : E →L[ℝ] EuclideanSpace ℝ (Fin n)) (Dm : EuclideanSpace ℝ (Fin n) →L[ℝ] E)
    (h1 : D.comp Dm = ContinuousLinearMap.id ℝ _) (h2 : Dm.comp D = ContinuousLinearMap.id ℝ _) :
    Function.Injective
      ((Dm.comp (trunc n d) + (adjCLM E (EuclideanSpace ℝ (Fin n)) D).comp
        (ContinuousLinearMap.id ℝ _ - trunc n d)) : EuclideanSpace ℝ (Fin n) →L[ℝ] E) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at hh
  have hDm : ∀ w, D (Dm w) = w := fun w => by simpa using congrArg (fun T => T w) h1
  have hD : ∀ x, Dm (D x) = x := fun x => by simpa using congrArg (fun T => T x) h2
  have hperp : inner ℝ (adjCLM E _ D (h - trunc n d h)) (Dm (trunc n d h)) = 0 := by
    rw [adjCLM_inner, hDm]
    rw [real_inner_comm]
    exact inner_trunc_sub n d h h
  have hnorm : inner ℝ (Dm (trunc n d h)) (Dm (trunc n d h)) = 0 := by
    have := congrArg (fun v => inner ℝ v (Dm (trunc n d h))) hh
    simp only [inner_add_left, inner_zero_left] at this
    rw [hperp] at this; simpa using this
  have h0 : Dm (trunc n d h) = 0 := inner_self_eq_zero.1 hnorm
  have hπ : trunc n d h = 0 := by
    have := hDm (trunc n d h); rw [h0] at this; simpa using this.symm
  rw [h0, zero_add, hπ, sub_zero] at hh
  have hAh : ∀ x, inner ℝ h (D x) = 0 := by
    intro x
    rw [← adjCLM_inner, hh]; simp
  have := hAh (Dm h)
  rw [hDm] at this
  exact inner_self_eq_zero.1 this


noncomputable def Ssub (n d : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.ker ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - trunc n d :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))

theorem mem_Ssub (n d : ℕ) (u : EuclideanSpace ℝ (Fin n)) : u ∈ Ssub n d ↔ trunc n d u = u := by
  simp only [Ssub, LinearMap.mem_ker]
  change u - trunc n d u = 0 ↔ _
  rw [sub_eq_zero]; exact eq_comm

theorem closed_Ssub (n d : ℕ) : IsClosed (Ssub n d : Set (EuclideanSpace ℝ (Fin n))) :=
  ContinuousLinearMap.isClosed_ker _

theorem tangentCone_sub_closed {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F)) {s : Set F} (hs : s ⊆ S) {w : F} (hw : w ∈ S) :
    tangentConeAt ℝ s w ⊆ S := by
  intro v hv
  obtain ⟨ι, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  refine hS.mem_of_tendsto hcd ?_
  filter_upwards [hds] with i hi
  refine S.smul_mem _ ?_
  have := S.sub_mem (hs hi) hw
  simpa using this

section chart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n)))

theorem chart_hasFDerivAt (k : ℕ) (hk : 1 ≤ k) (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) {x : E} (hx : x ∈ φ.source) :
    HasFDerivAt φ (fderiv ℝ φ x) x ∧ HasFDerivAt φ.symm (fderiv ℝ φ.symm (φ x)) (φ x) := by
  have hk1 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  refine ⟨?_, ?_⟩
  · exact ((h1.differentiableOn hk1).differentiableAt (φ.open_source.mem_nhds hx)).hasFDerivAt
  · exact ((h2.differentiableOn hk1).differentiableAt
      (φ.open_target.mem_nhds (φ.map_source hx))).hasFDerivAt

theorem chart_fderiv_comp (k : ℕ) (hk : 1 ≤ k) (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) {x : E} (hx : x ∈ φ.source) :
    (fderiv ℝ φ x).comp (fderiv ℝ φ.symm (φ x)) = ContinuousLinearMap.id ℝ _ ∧
    (fderiv ℝ φ.symm (φ x)).comp (fderiv ℝ φ x) = ContinuousLinearMap.id ℝ _ := by
  obtain ⟨hd1, hd2⟩ := chart_hasFDerivAt φ k hk h1 h2 hx
  constructor
  · have hd1' : HasFDerivAt φ (fderiv ℝ φ x) (φ.symm (φ x)) := by
      rw [φ.left_inv hx]; exact hd1
    have hc := hd1'.comp (φ x) hd2
    have hid := (hasFDerivAt_id (𝕜 := ℝ) (φ x)).congr_of_eventuallyEq
      (φ.eventually_right_inverse (φ.map_source hx))
    exact hc.unique hid
  · have hc := hd2.comp x hd1
    have hid := (hasFDerivAt_id (𝕜 := ℝ) x).congr_of_eventuallyEq (φ.eventually_left_inverse hx)
    exact hc.unique hid

theorem tangentCone_trunc (k d : ℕ) (hk : 1 ≤ k) (M : Set E)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target)
    (h3 : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i : Fin n, d ≤ i.val → φ x i = 0})
    {x : E} (hxM : x ∈ M) (hx : x ∈ φ.source) {v : E} (hv : v ∈ tangentConeAt ℝ M x) :
    trunc n d (fderiv ℝ φ x v) = fderiv ℝ φ x v := by
  obtain ⟨hd1, -⟩ := chart_hasFDerivAt φ k hk h1 h2 hx
  have hv' : v ∈ tangentConeAt ℝ (M ∩ φ.source) x := by
    rw [tangentConeAt_inter_nhds (φ.open_source.mem_nhds hx)]; exact hv
  have hmaps := hd1.hasFDerivWithinAt.mapsTo_tangent_cone (s := M ∩ φ.source) hv'
  have himg : φ '' (M ∩ φ.source) ⊆ (Ssub n d : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hz
    rw [h3] at hz'
    exact (mem_Ssub n d _).2 ((trunc_eq_self_iff n d _).2 hz'.2)
  have hxS : φ x ∈ Ssub n d := by
    have hz : x ∈ M ∩ φ.source := ⟨hxM, hx⟩
    exact himg ⟨x, hz, rfl⟩
  have := tangentCone_sub_closed (Ssub n d) (closed_Ssub n d) himg hxS hmaps
  exact (mem_Ssub n d _).1 this

theorem range_subset_tangentCone (k d : ℕ) (hk : 1 ≤ k) (M : Set E)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target)
    (h3 : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i : Fin n, d ≤ i.val → φ x i = 0})
    {x : E} (hxM : x ∈ M) (hx : x ∈ φ.source) (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ φ.symm (φ x) (trunc n d h) ∈ tangentConeAt ℝ M x := by
  obtain ⟨-, hd2⟩ := chart_hasFDerivAt φ k hk h1 h2 hx
  have hu : φ x ∈ Ssub n d := by
    have hz : x ∈ M ∩ φ.source := ⟨hxM, hx⟩
    rw [h3] at hz
    exact (mem_Ssub n d _).2 ((trunc_eq_self_iff n d _).2 hz.2)
  have hh : trunc n d h ∈ Ssub n d := (mem_Ssub n d _).2 (trunc_idem n d h)
  have hseg : openSegment ℝ (φ x) (φ x + trunc n d h) ⊆ (Ssub n d : Set (EuclideanSpace ℝ (Fin n))) :=
    (Ssub n d).convex.openSegment_subset hu ((Ssub n d).add_mem hu hh)
  have hc := mem_tangentConeAt_of_openSegment_subset hseg
  simp only [add_sub_cancel_left] at hc
  have hc' : trunc n d h ∈ tangentConeAt ℝ ((Ssub n d : Set (EuclideanSpace ℝ (Fin n))) ∩ φ.target) (φ x) := by
    rw [tangentConeAt_inter_nhds (φ.open_target.mem_nhds (φ.map_source hx))]; exact hc
  have hmaps := hd2.hasFDerivWithinAt.mapsTo_tangent_cone
    (s := (Ssub n d : Set (EuclideanSpace ℝ (Fin n))) ∩ φ.target) hc'
  rw [φ.left_inv hx] at hmaps
  refine tangentConeAt_mono ?_ hmaps
  rintro _ ⟨u, ⟨huS, hut⟩, rfl⟩
  have hsrc : φ.symm u ∈ φ.source := φ.map_target hut
  have hφ : φ (φ.symm u) = u := φ.right_inv hut
  have : φ.symm u ∈ M ∩ φ.source := by
    rw [h3]
    refine ⟨hsrc, fun i hi => ?_⟩
    rw [hφ]
    have := (trunc_eq_self_iff n d u).1 ((mem_Ssub n d u).1 huS) i hi
    exact this
  exact this.1

theorem tangentSpace_eq (k d : ℕ) (hk : 1 ≤ k) (M : Set E)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target)
    (h3 : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i : Fin n, d ≤ i.val → φ x i = 0})
    {x : E} (hxM : x ∈ M) (hx : x ∈ φ.source) :
    ProjLikeRetr.Retractor.tangentSpace M x =
      LinearMap.range (((fderiv ℝ φ.symm (φ x)).comp (trunc n d) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] E) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) := by
  obtain ⟨hc1, hc2⟩ := chart_fderiv_comp φ k hk h1 h2 hx
  apply le_antisymm
  · unfold ProjLikeRetr.Retractor.tangentSpace
    refine Submodule.span_le.2 fun v hv => ?_
    have := tangentCone_trunc φ k d hk M h1 h2 h3 hxM hx hv
    refine ⟨fderiv ℝ φ x v, ?_⟩
    change (fderiv ℝ φ.symm (φ x)) (trunc n d (fderiv ℝ φ x v)) = v
    rw [this]
    simpa using congrArg (fun T => T v) hc2
  · rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span (range_subset_tangentCone φ k d hk M h1 h2 h3 hxM hx h)

end chart

section ift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

noncomputable def Psi (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) : E :=
  φ.symm (trunc n d u) +
    (adjCLM E (EuclideanSpace ℝ (Fin n)) (fderiv ℝ φ (φ.symm (trunc n d u)))) (u - trunc n d u)

noncomputable def Lmap (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (d : ℕ) (x : E) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] E :=
  (fderiv ℝ φ.symm (φ x)).comp (trunc n d) +
    (adjCLM E (EuclideanSpace ℝ (Fin n)) (fderiv ℝ φ x)).comp
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - trunc n d)

theorem Psi_at (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    {x : E} (hx : x ∈ φ.source) (hu : trunc n d (φ x) = φ x) : Psi φ d (φ x) = x := by
  simp [Psi, hu, φ.left_inv hx]

theorem Psi_smooth (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ) (hk : 2 ≤ k)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target)
    {x : E} (hx : x ∈ φ.source) (hu : trunc n d (φ x) = φ x) :
    ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (Psi φ d) (φ x) := by
  have hkk : (((k - 1 : ℕ) : WithTop ℕ∞)) + 1 ≤ (k : WithTop ℕ∞) := by
    have : (k - 1) + 1 = k := by omega
    exact_mod_cast this.le
  have hle : (((k - 1 : ℕ) : WithTop ℕ∞)) ≤ (k : WithTop ℕ∞) := le_trans le_self_add hkk
  have hT : φ x ∈ φ.target := φ.map_source hx
  have hg0 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin n) => trunc n d u) (φ x) :=
    (trunc n d).contDiff.contDiffAt
  have hg2 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin n) => φ.symm (trunc n d u)) (φ x) := by
    have hs : ContDiffAt ℝ (k : WithTop ℕ∞) φ.symm (trunc n d (φ x)) := by
      rw [hu]; exact h2.contDiffAt (φ.open_target.mem_nhds hT)
    exact hs.comp (φ x) hg0
  have hdφ : ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ φ y) φ.source :=
    h1.fderiv_of_isOpen φ.open_source hkk
  have hg3 : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ (φ.symm (trunc n d u))) (φ x) := by
    have hs : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ φ y) (φ.symm (trunc n d (φ x))) := by
      rw [hu, φ.left_inv hx]; exact hdφ.contDiffAt (φ.open_source.mem_nhds hx)
    exact hs.comp (φ x) (hg2.of_le hle)
  have hg4 : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => adjCLM E (EuclideanSpace ℝ (Fin n)) (fderiv ℝ φ (φ.symm (trunc n d u)))) (φ x) :=
    (adjCLM E (EuclideanSpace ℝ (Fin n))).contDiff.contDiffAt.comp (φ x) hg3
  have hg5 : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => u - trunc n d u) (φ x) :=
    (contDiffAt_id.sub (hg0.of_le hle))
  exact (hg2.of_le hle).add (hg4.clm_apply hg5)

theorem Psi_hasFDerivAt (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ) (hk : 2 ≤ k)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target)
    {x : E} (hx : x ∈ φ.source) (hu : trunc n d (φ x) = φ x) :
    HasFDerivAt (Psi φ d) (Lmap φ d x) (φ x) := by
  obtain ⟨-, hd2⟩ := chart_hasFDerivAt φ k (by omega) h1 h2 hx
  have hsm := Psi_smooth φ k d hk h1 h2 hx hu
  have hm1 : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have : k - 1 ≠ 0 := by omega
    exact_mod_cast this
  have hkk : (((k - 1 : ℕ) : WithTop ℕ∞)) + 1 ≤ (k : WithTop ℕ∞) := by
    have : (k - 1) + 1 = k := by omega
    exact_mod_cast this.le
  have hle : (((k - 1 : ℕ) : WithTop ℕ∞)) ≤ (k : WithTop ℕ∞) := le_trans le_self_add hkk
  have hd2' : HasFDerivAt φ.symm (fderiv ℝ φ.symm (φ x)) (trunc n d (φ x)) := by
    rw [hu]; exact hd2
  have hg2 : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => φ.symm (trunc n d u))
      ((fderiv ℝ φ.symm (φ x)).comp (trunc n d)) (φ x) :=
    hd2'.comp (φ x) (trunc n d).hasFDerivAt
  have hT : φ x ∈ φ.target := φ.map_source hx
  have hg0 : ContDiffAt ℝ (k : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin n) => trunc n d u) (φ x) :=
    (trunc n d).contDiff.contDiffAt
  have hg2c : ContDiffAt ℝ (k : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin n) => φ.symm (trunc n d u)) (φ x) := by
    have hs : ContDiffAt ℝ (k : WithTop ℕ∞) φ.symm (trunc n d (φ x)) := by
      rw [hu]; exact h2.contDiffAt (φ.open_target.mem_nhds hT)
    exact hs.comp (φ x) hg0
  have hdφ : ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ φ y) φ.source :=
    h1.fderiv_of_isOpen φ.open_source hkk
  have hg3 : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ (φ.symm (trunc n d u))) (φ x) := by
    have hs : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ φ y) (φ.symm (trunc n d (φ x))) := by
      rw [hu, φ.left_inv hx]; exact hdφ.contDiffAt (φ.open_source.mem_nhds hx)
    exact hs.comp (φ x) (hg2c.of_le hle)
  have hg4 : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => adjCLM E (EuclideanSpace ℝ (Fin n)) (fderiv ℝ φ (φ.symm (trunc n d u)))) (φ x) :=
    (adjCLM E (EuclideanSpace ℝ (Fin n))).contDiff.contDiffAt.comp (φ x) hg3
  have hg4d := (hg4.differentiableAt hm1).hasFDerivAt
  have hg5 : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => u - trunc n d u)
      (ContinuousLinearMap.id ℝ _ - trunc n d) (φ x) :=
    (hasFDerivAt_id (𝕜 := ℝ) (φ x)).sub (trunc n d).hasFDerivAt
  have hcl := hg4d.clm_apply hg5
  have hfull := hg2.add hcl
  have hval : (φ x) - trunc n d (φ x) = 0 := by rw [hu]; simp
  have hsymm : φ.symm (trunc n d (φ x)) = x := by rw [hu, φ.left_inv hx]
  refine hfull.congr_fderiv ?_
  simp [Lmap, hval, hsymm]

theorem Lmap_equiv (hn : Module.finrank ℝ E = n)
    (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ) (hk : 2 ≤ k)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) {x : E} (hx : x ∈ φ.source) :
    ∃ Leq : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E, (Leq : EuclideanSpace ℝ (Fin n) →L[ℝ] E) = Lmap φ d x := by
  obtain ⟨hc1, hc2⟩ := chart_fderiv_comp φ k (by omega) h1 h2 hx
  have hinj := L_injective (E := E) n d (fderiv ℝ φ x) (fderiv ℝ φ.symm (φ x)) hc1 hc2
  have hinj' : Function.Injective (Lmap φ d x : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) := hinj
  have hsurj : Function.Surjective (Lmap φ d x : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hn])).1 hinj'
  exact ⟨(LinearEquiv.ofBijective (Lmap φ d x : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) ⟨hinj', hsurj⟩).toContinuousLinearEquiv, rfl⟩

end ift

section ift2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

theorem ift_core (hn : Module.finrank ℝ E = n)
    (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ) (hk : 2 ≤ k)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) {x : E} (hx : x ∈ φ.source)
    (hu : trunc n d (φ x) = φ x) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) E)
      (Leq : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E),
      (∀ u, e u = Psi φ d u) ∧ φ x ∈ e.source ∧ x ∈ e.target ∧
      (Leq : EuclideanSpace ℝ (Fin n) →L[ℝ] E) = Lmap φ d x ∧
      ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) e.symm x ∧
      HasFDerivAt e.symm (Leq.symm : E →L[ℝ] EuclideanSpace ℝ (Fin n)) x := by
  obtain ⟨Leq, hLeq⟩ := Lmap_equiv hn φ k d hk h1 h2 hx
  have hfd : HasFDerivAt (Psi φ d) (Leq : EuclideanSpace ℝ (Fin n) →L[ℝ] E) (φ x) := by
    rw [hLeq]; exact Psi_hasFDerivAt φ k d hk h1 h2 hx hu
  have hcd := Psi_smooth φ k d hk h1 h2 hx hu
  have hm : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have : k - 1 ≠ 0 := by omega
    exact_mod_cast this
  have hPx : Psi φ d (φ x) = x := Psi_at φ d hx hu
  refine ⟨hcd.toOpenPartialHomeomorph (Psi φ d) hfd hm, Leq, fun u => rfl,
    hcd.mem_toOpenPartialHomeomorph_source hfd hm, ?_, hLeq, ?_, ?_⟩
  · have := hcd.image_mem_toOpenPartialHomeomorph_target hfd hm
    rwa [hPx] at this
  · have := hcd.to_localInverse hfd hm
    rw [hPx] at this
    exact this
  · have := ((hcd.hasStrictFDerivAt' hfd hm).to_localInverse).hasFDerivAt
    rw [hPx] at this
    exact this

theorem Lmap_continuousAt (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ)
    (hk : 2 ≤ k) (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) {x : E} (hx : x ∈ φ.source) :
    ContinuousAt (fun z => Lmap φ d z) x := by
  have hm : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast (by omega : 1 ≤ k)
  have hc2 : ContinuousAt (fun w => fderiv ℝ φ.symm w) (φ x) :=
    (h2.continuousOn_fderiv_of_isOpen φ.open_target hm).continuousAt
      (φ.open_target.mem_nhds (φ.map_source hx))
  have hc1 : ContinuousAt (fun z => fderiv ℝ φ z) x :=
    (h1.continuousOn_fderiv_of_isOpen φ.open_source hm).continuousAt (φ.open_source.mem_nhds hx)
  have hφ : ContinuousAt φ x := φ.continuousAt hx
  have hA : ContinuousAt (fun z => adjCLM E (EuclideanSpace ℝ (Fin n)) (fderiv ℝ φ z)) x :=
    (adjCLM E (EuclideanSpace ℝ (Fin n))).continuous.continuousAt.comp hc1
  have hB : ContinuousAt (fun z => fderiv ℝ φ.symm (φ z)) x := hc2.comp hφ
  unfold Lmap
  exact (hB.clm_comp continuousAt_const).add (hA.clm_comp continuousAt_const)

theorem L_bound (hn : Module.finrank ℝ E = n)
    (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ) (hk : 2 ≤ k)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target) {x : E} (hx : x ∈ φ.source) :
    ∃ C > 0, ∀ᶠ z in 𝓝 x, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ C * ‖Lmap φ d z h‖ := by
  obtain ⟨Leq, hLeq⟩ := Lmap_equiv hn φ k d hk h1 h2 hx
  set K : ℝ := ‖(Leq.symm : E →L[ℝ] EuclideanSpace ℝ (Fin n))‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  have hcont := Lmap_continuousAt φ k d hk h1 h2 hx
  have hev := hcont.eventually (Metric.ball_mem_nhds (Lmap φ d x) (show 0 < 1 / (2 * K) by positivity))
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hev] with z hz h
  have hz' : ‖Lmap φ d z - Lmap φ d x‖ < 1 / (2 * K) := by
    rw [← dist_eq_norm]; exact hz
  have h0 : ‖h‖ ≤ K * ‖Lmap φ d x h‖ := by
    have : h = Leq.symm (Lmap φ d x h) := by
      rw [← hLeq]; simp
    calc ‖h‖ = ‖Leq.symm (Lmap φ d x h)‖ := by rw [← this]
      _ ≤ ‖(Leq.symm : E →L[ℝ] EuclideanSpace ℝ (Fin n))‖ * ‖Lmap φ d x h‖ :=
          (Leq.symm : E →L[ℝ] EuclideanSpace ℝ (Fin n)).le_opNorm _
      _ ≤ K * ‖Lmap φ d x h‖ := by
          apply mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (norm_nonneg _)
  have h1' : ‖Lmap φ d x h‖ ≤ ‖Lmap φ d z h‖ + ‖h‖ / (2 * K) := by
    have e1 : Lmap φ d x h = Lmap φ d z h - (Lmap φ d z - Lmap φ d x) h := by simp
    calc ‖Lmap φ d x h‖ ≤ ‖Lmap φ d z h‖ + ‖(Lmap φ d z - Lmap φ d x) h‖ := by
          rw [e1]; exact norm_sub_le _ _
      _ ≤ ‖Lmap φ d z h‖ + ‖Lmap φ d z - Lmap φ d x‖ * ‖h‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Lmap φ d z h‖ + 1 / (2 * K) * ‖h‖ := by
          gcongr
      _ = ‖Lmap φ d z h‖ + ‖h‖ / (2 * K) := by ring
  have h2' : K * (‖h‖ / (2 * K)) = ‖h‖ / 2 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1' hKpos.le, norm_nonneg h]

theorem normal_decomp (hn : Module.finrank ℝ E = n)
    (φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin n))) (k d : ℕ) (hk : 2 ≤ k) (M : Set E)
    (h1 : ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source)
    (h2 : ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target)
    (h3 : M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i : Fin n, d ≤ i.val → φ x i = 0})
    {z : E} (hzM : z ∈ M) (hz : z ∈ φ.source) {v : E}
    (hv : v ∈ ProjLikeRetr.Retractor.normalSpace M z) :
    ∃ h : EuclideanSpace ℝ (Fin n), trunc n d h = 0 ∧ Lmap φ d z h = v := by
  obtain ⟨hc1, hc2⟩ := chart_fderiv_comp φ k (by omega) h1 h2 hz
  have hDm : ∀ w, fderiv ℝ φ z (fderiv ℝ φ.symm (φ z) w) = w :=
    fun w => by simpa using congrArg (fun T => T w) hc1
  have hinj := L_injective (E := E) n d (fderiv ℝ φ z) (fderiv ℝ φ.symm (φ z)) hc1 hc2
  have hinj' : Function.Injective (Lmap φ d z : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) := hinj
  have hsurj : Function.Surjective (Lmap φ d z : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hn])).1 hinj'
  obtain ⟨h, hh⟩ := hsurj v
  have hh' : Lmap φ d z h = v := hh
  have hT := tangentSpace_eq φ k d (by omega) M h1 h2 h3 hzM hz
  have hmem : fderiv ℝ φ.symm (φ z) (trunc n d h) ∈ ProjLikeRetr.Retractor.tangentSpace M z := by
    rw [hT]; exact ⟨h, rfl⟩
  have hperp1 : inner ℝ (fderiv ℝ φ.symm (φ z) (trunc n d h)) v = 0 :=
    Submodule.inner_right_of_mem_orthogonal hmem hv
  have hperp2 : inner ℝ (adjCLM E _ (fderiv ℝ φ z) (h - trunc n d h))
      (fderiv ℝ φ.symm (φ z) (trunc n d h)) = 0 := by
    rw [adjCLM_inner, hDm, real_inner_comm]
    exact inner_trunc_sub n d h h
  have hLh : v = fderiv ℝ φ.symm (φ z) (trunc n d h) +
      adjCLM E _ (fderiv ℝ φ z) (h - trunc n d h) := by
    rw [← hh']; simp [Lmap]
  have hnorm : inner ℝ (fderiv ℝ φ.symm (φ z) (trunc n d h)) (fderiv ℝ φ.symm (φ z) (trunc n d h)) = 0 := by
    have := hperp1
    rw [hLh, inner_add_right, real_inner_comm (adjCLM E _ (fderiv ℝ φ z) (h - trunc n d h)), hperp2] at this
    simpa using this
  have h0 : fderiv ℝ φ.symm (φ z) (trunc n d h) = 0 := inner_self_eq_zero.1 hnorm
  have hπ : trunc n d h = 0 := by
    have := hDm (trunc n d h); rw [h0] at this; simpa using this.symm
  exact ⟨h, hπ, hh'⟩

end ift2

theorem normal_foot_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ δ > 0, ∃ η > 0, ∃ P : E → E,
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection xbar ∧
      ∀ y ∈ Metric.ball xbar δ, ∀ z ∈ M, dist z xbar < η →
        y - z ∈ ProjLikeRetr.Retractor.normalSpace M z → z = P y := by
  obtain ⟨hdle, hxM, φ, hxφ, h1, h2, h3⟩ := hM
  have hu : trunc (Module.finrank ℝ E) d (φ xbar) = φ xbar := by
    have hz : xbar ∈ M ∩ φ.source := ⟨hxM, hxφ⟩
    rw [h3] at hz
    exact (trunc_eq_self_iff _ d _).2 hz.2
  obtain ⟨e, Leq, hePsi, hsrc, htgt, hLeq, hcd, hder⟩ := ift_core rfl φ k d hk h1 h2 hxφ hu
  have hexbar : e.symm xbar = φ xbar := by
    have : e (φ xbar) = xbar := by rw [hePsi]; exact Psi_at φ d hxφ hu
    calc e.symm xbar = e.symm (e (φ xbar)) := by rw [this]
      _ = φ xbar := e.left_inv hsrc
  have hkk : (((k - 1 : ℕ) : WithTop ℕ∞)) + 1 ≤ (k : WithTop ℕ∞) := by
    have : (k - 1) + 1 = k := by omega
    exact_mod_cast this.le
  have hle : (((k - 1 : ℕ) : WithTop ℕ∞)) ≤ (k : WithTop ℕ∞) := le_trans le_self_add hkk
  set P : E → E := fun y => φ.symm (trunc (Module.finrank ℝ E) d (e.symm y)) with hP
  -- smoothness of P at xbar
  have hPcd : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P xbar := by
    have hs : ContDiffAt ℝ (k : WithTop ℕ∞) φ.symm (trunc (Module.finrank ℝ E) d (e.symm xbar)) := by
      rw [hexbar, hu]; exact h2.contDiffAt (φ.open_target.mem_nhds (φ.map_source hxφ))
    exact (hs.of_le hle).comp xbar ((trunc (Module.finrank ℝ E) d).contDiff.contDiffAt.comp xbar hcd)
  -- derivative of P at xbar
  have hd2 := (chart_hasFDerivAt φ k (by omega) h1 h2 hxφ).2
  have hd2' : HasFDerivAt φ.symm (fderiv ℝ φ.symm (φ xbar))
      (trunc (Module.finrank ℝ E) d (e.symm xbar)) := by
    rw [hexbar, hu]; exact hd2
  have hPder0 := hd2'.comp xbar (((trunc (Module.finrank ℝ E) d).hasFDerivAt).comp xbar hder)
  have hPder : HasFDerivAt P (((fderiv ℝ φ.symm (φ xbar)).comp (trunc (Module.finrank ℝ E) d)).comp
      (Leq.symm : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) xbar := by
    rw [ContinuousLinearMap.comp_assoc]; exact hPder0
  have hT := tangentSpace_eq φ k d (by omega) M h1 h2 h3 hxM hxφ
  obtain ⟨hc1, hc2⟩ := chart_fderiv_comp φ k (by omega) h1 h2 hxφ
  have hDm : ∀ w, fderiv ℝ φ xbar (fderiv ℝ φ.symm (φ xbar) w) = w :=
    fun w => by simpa using congrArg (fun T => T w) hc1
  have hid : ((fderiv ℝ φ.symm (φ xbar)).comp (trunc (Module.finrank ℝ E) d)).comp
      (Leq.symm : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =
      (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection := by
    ext v
    set h := Leq.symm v with hh
    have hLh : Lmap φ d xbar h = v := by
      have : (Leq : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E) h = v := by
        rw [hh]; simp
      rw [← hLeq]; exact this
    have hv : v = fderiv ℝ φ.symm (φ xbar) (trunc (Module.finrank ℝ E) d h) +
        adjCLM E _ (fderiv ℝ φ xbar) (h - trunc (Module.finrank ℝ E) d h) := by
      rw [← hLh]; simp [Lmap]
    symm
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hT]; exact ⟨h, rfl⟩
    · intro w hw
      rw [hT] at hw
      obtain ⟨g, rfl⟩ := hw
      have : v - fderiv ℝ φ.symm (φ xbar) (trunc (Module.finrank ℝ E) d h) =
          adjCLM E _ (fderiv ℝ φ xbar) (h - trunc (Module.finrank ℝ E) d h) := by
        rw [hv]; abel
      show inner ℝ (v - fderiv ℝ φ.symm (φ xbar) (trunc (Module.finrank ℝ E) d h))
        (fderiv ℝ φ.symm (φ xbar) (trunc (Module.finrank ℝ E) d g)) = 0
      rw [this, adjCLM_inner, hDm, real_inner_comm]
      exact inner_trunc_sub _ d g h
  rw [hid] at hPder
  -- neighbourhood bookkeeping
  have hmne : ((k - 1 : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
    | (norm_cast; exact ENat.natCast_ne_top _)
    | (norm_cast; exact ENat.coe_ne_top _)
    | (intro h; exact ENat.coe_ne_top (k-1) (WithTop.coe_injective (by simpa using h)))
  have hev1 : ∀ᶠ y in 𝓝 xbar, ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P y ∧ y ∈ e.target :=
    (hPcd.eventually hmne).and (e.open_target.eventually_mem htgt)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 e.open_source (φ xbar) hsrc
  obtain ⟨C, hC, hCev⟩ := L_bound rfl φ k d hk h1 h2 hxφ
  have hev2 : ∀ᶠ z in 𝓝 xbar, z ∈ φ.source ∧ dist (φ z) (φ xbar) < ρ / 2 :=
    (φ.open_source.eventually_mem hxφ).and
      ((φ.continuousAt hxφ).eventually (Metric.ball_mem_nhds _ (half_pos hρ)))
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.eventually_nhds_iff_ball.1 hev1
  obtain ⟨η1, hη1, hη1'⟩ := Metric.eventually_nhds_iff_ball.1 (hCev.and hev2)
  have hσ : 0 < ρ / (4 * C) := by positivity
  refine ⟨min δ1 (ρ / (4 * C)), lt_min hδ1 hσ, min η1 (ρ / (4 * C)), lt_min hη1 hσ, P, ?_, hPder, ?_⟩
  · intro y hy
    exact (hδ1' y (Metric.ball_subset_ball (min_le_left _ _) hy)).1.contDiffWithinAt
  · intro y hy z hzM hzη hz
    have hy' : dist y xbar < min δ1 (ρ / (4 * C)) := hy
    have hzη' : dist z xbar < min η1 (ρ / (4 * C)) := hzη
    have hzb : z ∈ Metric.ball xbar η1 :=
      lt_of_lt_of_le hzη' (min_le_left _ _)
    obtain ⟨hbound, hzsrc, hzφ⟩ := hη1' z hzb
    obtain ⟨h, hπ, hLz⟩ := normal_decomp rfl φ k d hk M h1 h2 h3 hzM hzsrc hz
    have hφz : trunc (Module.finrank ℝ E) d (φ z) = φ z := by
      have hz' : z ∈ M ∩ φ.source := ⟨hzM, hzsrc⟩
      rw [h3] at hz'
      exact (trunc_eq_self_iff _ d _).2 hz'.2
    have hyz : ‖y - z‖ < ρ / (2 * C) := by
      have e1 : ‖y - z‖ ≤ ‖y - xbar‖ + ‖xbar - z‖ := by
        have := norm_add_le (y - xbar) (xbar - z)
        simpa using this
      have e2 : ‖y - xbar‖ < ρ / (4 * C) := by
        have := lt_of_lt_of_le hy' (min_le_right _ _)
        simpa [dist_eq_norm] using this
      have e3 : ‖xbar - z‖ < ρ / (4 * C) := by
        have := lt_of_lt_of_le hzη' (min_le_right _ _)
        rw [dist_comm, dist_eq_norm] at this
        exact this
      have e4 : ρ / (4 * C) + ρ / (4 * C) = ρ / (2 * C) := by field_simp; ring
      linarith
    have hhn : ‖h‖ < ρ / 2 := by
      have := hbound h
      rw [hLz] at this
      have h5 : C * ‖y - z‖ < ρ / 2 := by
        calc C * ‖y - z‖ < C * (ρ / (2 * C)) := by gcongr
          _ = ρ / 2 := by field_simp
      linarith
    have hdist : dist (φ z + h) (φ xbar) < ρ := by
      calc dist (φ z + h) (φ xbar) ≤ dist (φ z + h) (φ z) + dist (φ z) (φ xbar) := dist_triangle _ _ _
        _ = ‖h‖ + dist (φ z) (φ xbar) := by simp [dist_eq_norm]
        _ < ρ := by linarith
    have hu_src : φ z + h ∈ e.source := hball hdist
    have htr : trunc (Module.finrank ℝ E) d (φ z + h) = φ z := by
      rw [map_add, hπ, add_zero, hφz]
    have hAh : adjCLM E _ (fderiv ℝ φ z) h = y - z := by
      have := hLz
      simp only [Lmap, hπ, map_zero, ContinuousLinearMap.comp_apply, zero_add,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, sub_zero] at this
      exact this
    have hPsi : Psi φ d (φ z + h) = y := by
      unfold Psi
      rw [htr, φ.left_inv hzsrc, add_sub_cancel_left, hAh]
      abel
    have heu : e (φ z + h) = y := by rw [hePsi]; exact hPsi
    have hsy : e.symm y = φ z + h := by rw [← heu]; exact e.left_inv hu_src
    show z = φ.symm (trunc (Module.finrank ℝ E) d (e.symm y))
    rw [hsy, htr, φ.left_inv hzsrc]

/-- Lemma 3.1 (checks that the decomposition closes). -/
theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ δ > 0, ∃ P : E → E,
      (∀ x ∈ Metric.ball xbar δ, {z | IsMetricProjection M x z} = {P x}) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection xbar := by
  obtain ⟨ε, hε, hex⟩ := nearest_exists_local k d M xbar hM
  obtain ⟨δ, hδ, η, hη, P, hPc, hPd, huniq⟩ := normal_foot_local k d hk M xbar hM
  have hM' := hM
  obtain ⟨hdle, hxbar, φ, hxφ, h1, h2, h3⟩ := hM'
  obtain ⟨ε2, hε2, hball⟩ := Metric.isOpen_iff.1 φ.open_source xbar hxφ
  set δ0 := min (min ε δ) (min (η / 2) (ε2 / 2)) with hδ0
  have hδ0pos : 0 < δ0 := lt_min (lt_min hε hδ) (lt_min (half_pos hη) (half_pos hε2))
  have key : ∀ y ∈ Metric.ball xbar δ0, ∀ z, IsMetricProjection M y z → z = P y := by
    intro y hy z hz
    have hyd : dist y xbar < δ0 := hy
    have hzy : dist z y ≤ dist y xbar := by
      have := hz.2 xbar hxbar
      rw [dist_comm z y, dist_eq_norm, dist_eq_norm]; exact this
    have hzx : dist z xbar < 2 * δ0 := by
      have := dist_triangle z y xbar; linarith
    have hzη : dist z xbar < η := by
      have : δ0 ≤ η / 2 := le_trans (min_le_right _ _) (min_le_left _ _); linarith
    have hzε : dist z xbar < ε2 := by
      have : δ0 ≤ ε2 / 2 := le_trans (min_le_right _ _) (min_le_right _ _); linarith
    have hzM : z ∈ M := hz.1
    have hsub : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M z :=
      ⟨hdle, hzM, φ, hball hzε, h1, h2, h3⟩
    have hn := (optimality_3_2 k d hk M y z hsub hz).2
    have hyδ : y ∈ Metric.ball xbar δ :=
      Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) hy
    exact huniq y hyδ z hzM hzη hn
  refine ⟨δ0, hδ0pos, P, ?_, ?_, hPd⟩
  · intro y hy
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact key y hy z
    · rintro rfl
      have hyε : y ∈ Metric.ball xbar ε :=
        Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hy
      obtain ⟨z0, hz0⟩ := hex y hyε
      rw [← key y hy z0 hz0]; exact hz0
  · exact hPc.mono (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)))



/-- P2: the submanifold chart at `xbar` is a chart at every nearby point of `M`. -/
theorem submanifoldAt_nhds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ ε > 0, ∀ x ∈ M, x ∈ Metric.ball xbar ε → ProjLikeRetr.Retractor.IsSubmanifoldAt k d M x := by
  obtain ⟨hd, _, φ, hx, h1, h2, h3⟩ := hM
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 φ.open_source xbar hx
  exact ⟨ε, hε, fun x hxM hxb => ⟨hd, hxM, φ, hball hxb, h1, h2, h3⟩⟩

/-- P3: one map `P` on a ball whose derivative at each point `x ∈ M` near `xbar` is the
projector onto `T_M(x)`, given Lemma 3.1 at every submanifold point. -/
theorem projection_fderiv_on_M {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar)
    (h31 : ∀ x : E, ProjLikeRetr.Retractor.IsSubmanifoldAt k d M x →
      ∃ δ > 0, ∃ P : E → E,
        (∀ y ∈ Metric.ball x δ, {z | IsMetricProjection M y z} = {P y}) ∧
        ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball x δ) ∧
        HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M x).starProjection x) :
    ∃ δ > 0, ∃ δ' > 0, δ' ≤ δ ∧ ∃ P : E → E,
      (∀ y ∈ Metric.ball xbar δ, {z | IsMetricProjection M y z} = {P y}) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      ∀ x ∈ M, x ∈ Metric.ball xbar δ' →
        HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M x).starProjection x := by
  obtain ⟨δ, hδ, P, hPs, hPc, -⟩ := h31 xbar hM
  obtain ⟨ε, hε, hε'⟩ := submanifoldAt_nhds k d M xbar hM
  refine ⟨δ, hδ, min δ ε, lt_min hδ hε, min_le_left _ _, P, hPs, hPc, ?_⟩
  intro x hxM hxb
  have hxb1 : x ∈ Metric.ball xbar δ := Metric.ball_subset_ball (min_le_left _ _) hxb
  have hxb2 : x ∈ Metric.ball xbar ε := Metric.ball_subset_ball (min_le_right _ _) hxb
  obtain ⟨δx, hδx, Px, hPxs, -, hPxd⟩ := h31 x (hε' x hxM hxb2)
  refine hPxd.congr_of_eventuallyEq ?_
  have hU : Metric.ball xbar δ ∩ Metric.ball x δx ∈ 𝓝 x :=
    Filter.inter_mem (Metric.isOpen_ball.mem_nhds hxb1) (Metric.ball_mem_nhds x hδx)
  filter_upwards [hU] with y hy
  have e1 := hPs y hy.1
  have e2 := hPxs y hy.2
  rw [e1] at e2
  exact Set.singleton_eq_singleton_iff.1 e2

/-- Parent glue: Prop. 3.2 from Lemma 3.1 (at every submanifold point). -/
theorem projective_retraction_of_lemma_3_1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar)
    (h31 : ∀ x : E, ProjLikeRetr.Retractor.IsSubmanifoldAt k d M x →
      ∃ δ > 0, ∃ P : E → E,
        (∀ y ∈ Metric.ball x δ, {z | IsMetricProjection M y z} = {P y}) ∧
        ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball x δ) ∧
        HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M x).starProjection x) :
    ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[ProjLikeRetr.Retractor.tangentBundle M] (xbar, 0), {z | IsMetricProjection M (p.1 + p.2) z} = {r p}) ∧
      ProjLikeRetr.Projective.IsRetractionAt k M r xbar := by
  obtain ⟨δ, hδ, δ', hδ', hle, P, hPs, hPc, hPd⟩ := projection_fderiv_on_M k d M xbar hM h31
  set O : Set (E × E) := {p | p.1 ∈ Metric.ball xbar δ' ∧ p.1 + p.2 ∈ Metric.ball xbar δ} with hO
  have hOopen : IsOpen O :=
    (Metric.isOpen_ball.preimage continuous_fst).inter
      (Metric.isOpen_ball.preimage (continuous_fst.add continuous_snd))
  have hOmem : (xbar, (0 : E)) ∈ O := by
    refine ⟨Metric.mem_ball_self hδ', ?_⟩
    show xbar + (0 : E) ∈ Metric.ball xbar δ
    rw [add_zero]; exact Metric.mem_ball_self hδ
  refine ⟨fun p => P (p.1 + p.2), ?_, hk, ⟨d, hM⟩, O, hOopen, hOmem, ?_, ?_, ?_, ?_⟩
  · apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [hOopen.mem_nhds hOmem] with p hp
    exact hPs _ hp.2
  · intro p hp
    have h := hPs _ hp.1.2
    have hmem : P (p.1 + p.2) ∈ {z | IsMetricProjection M (p.1 + p.2) z} := by
      rw [h]; rfl
    exact hmem.1
  · refine hPc.comp (contDiff_fst.add contDiff_snd).contDiffOn ?_
    intro p hp
    exact hp.1.2
  · intro x hx
    have hxM : x ∈ M := hx.2.1
    have h := hPs _ hx.1.2
    have hself : x ∈ {z | IsMetricProjection M (x + 0) z} := by
      refine ⟨hxM, fun w _ => ?_⟩
      simp
    rw [h] at hself
    simpa using hself.symm
  · intro x hx
    have hxM : x ∈ M := hx.2.1
    have hd := hPd x hxM hx.1.1
    set T := ProjLikeRetr.Retractor.tangentSpace M x
    have hlin : HasFDerivAt (fun u : T => x + (u : E)) T.subtypeL 0 := by
      simpa using (T.subtypeL.hasFDerivAt (x := (0 : T))).const_add x
    have hd' : HasFDerivAt P T.starProjection (x + ((0 : T) : E)) := by simpa using hd
    have hc := hd'.comp (0 : T) hlin
    have hcomp : T.starProjection.comp T.subtypeL = T.subtypeL := by
      ext u
      exact Submodule.starProjection_eq_self_iff.2 u.2
    rw [hcomp] at hc
    exact hc


end PLR80850C

open ProjLikeRetr.Projective RandomGradFree.Nonsmooth Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ r : E × E → E,
      (∀ᶠ p in 𝓝[ProjLikeRetr.Retractor.tangentBundle M] (xbar, 0), {z | IsMetricProjection M (p.1 + p.2) z} = {r p}) ∧
      IsRetractionAt k M r xbar := by
  exact PLR80850C.projective_retraction_of_lemma_3_1 k d hk M xbar hM
    (fun x hx => PLR80850C.lemma_3_1 k d hk M x hx)
