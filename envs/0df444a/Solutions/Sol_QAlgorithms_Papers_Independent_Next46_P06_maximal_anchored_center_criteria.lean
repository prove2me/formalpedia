-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.maximal_anchored_center_criteria
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:54:37.535554+00:00
-- url     : https://prove2.me/submissions/05201b30-2706-4ef7-bbf2-9830197a5f78

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06
noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Remark 6.5, PDF p.16: the center criterion and the equality in the
commutative case are both retained. -/
theorem g61c_bbg_mem {T : X →L[ℂ] X} {x y : X} : (x, y) ∈ banachBoundedGraph T ↔ y = T x := Iff.rfl

theorem g61c_bbg_inj {T S : X →L[ℂ] X} (h : banachBoundedGraph T = banachBoundedGraph S) : T = S := by
  ext x
  have : (x, T x) ∈ banachBoundedGraph S := by rw [← h]; rfl
  exact this

theorem g61c_bv_eq {A : Graph X} {T : X →L[ℂ] X} (h : A = banachBoundedGraph T) : boundedValue A = T := by
  have hb : Bounded A := ⟨T, h⟩
  unfold boundedValue; rw [dif_pos hb]
  exact g61c_bbg_inj ((Classical.choose_spec hb).symm.trans h)

theorem g61c_bv_spec {A : Graph X} (h : Bounded A) : A = banachBoundedGraph (boundedValue A) := by
  obtain ⟨T, hT⟩ := h; rw [g61c_bv_eq hT]; exact hT

theorem g61c_bdd_mem {A : Graph X} (h : Bounded A) (x : X) : (x, boundedValue A x) ∈ A := by
  have hs := g61c_bv_spec h
  have : (x, boundedValue A x) ∈ banachBoundedGraph (boundedValue A) := rfl
  rwa [← hs] at this

theorem g61c_bdd_val {A : Graph X} (h : Bounded A) {x y : X} (hxy : (x, y) ∈ A) : y = boundedValue A x := by
  rw [g61c_bv_spec h] at hxy; exact hxy

section g61c_proto
variable {Phi : F → Graph X} {S : Set F}

theorem g61c_fun (hP : ProtoOn Phi S) {f : F} (hf : f ∈ S) {x y z : X}
    (h1 : (x, y) ∈ Phi f) (h2 : (x, z) ∈ Phi f) : y = z := (hP.2.1 f hf).2.2.2.2 x y z h1 h2

theorem g61c_zero (hP : ProtoOn Phi S) {f : F} (hf : f ∈ S) : ((0 : X), (0 : X)) ∈ Phi f :=
  (hP.2.1 f hf).2.1

theorem g61c_closed (hP : ProtoOn Phi S) {f : F} (hf : f ∈ S) : IsClosed (Phi f) :=
  (hP.2.1 f hf).1

theorem g61c_one (hP : ProtoOn Phi S) (x : X) : (x, x) ∈ Phi 1 := by
  rw [hP.2.2.1]; rfl

theorem g61c_one_iff (hP : ProtoOn Phi S) {x y : X} : (x, y) ∈ Phi 1 ↔ y = x := by
  rw [hP.2.2.1]; rfl

theorem g61c_smul (hP : ProtoOn Phi S) {f : F} (hf : f ∈ S) (c : ℂ) {x y : X}
    (h : (x, y) ∈ Phi f) : (x, c • y) ∈ Phi (c • f) :=
  hP.2.2.2.1 c f hf ⟨y, h, rfl⟩

theorem g61c_add (hP : ProtoOn Phi S) {f g : F} (hf : f ∈ S) (hg : g ∈ S) {x y z : X}
    (h1 : (x, y) ∈ Phi f) (h2 : (x, z) ∈ Phi g) : (x, y + z) ∈ Phi (f + g) :=
  hP.2.2.2.2.1 f hf g hg ⟨y, z, h1, h2, rfl⟩

theorem g61c_mul (hP : ProtoOn Phi S) {f g : F} (hf : f ∈ S) (hg : g ∈ S) {x y w : X}
    (h1 : (x, y) ∈ Phi g) (h2 : (y, w) ∈ Phi f) : (x, w) ∈ Phi (f * g) :=
  (hP.2.2.2.2.2 f hf g hg).1 ⟨y, h1, h2⟩

theorem g61c_mul_dom (hP : ProtoOn Phi S) {f g : F} (hf : f ∈ S) (hg : g ∈ S) (hfg : f * g ∈ S)
    {x y w : X} (h1 : (x, y) ∈ Phi g) (h2 : (x, w) ∈ Phi (f * g)) : (y, w) ∈ Phi f := by
  have hx : x ∈ graphDomain (graphMul (Phi f) (Phi g)) := by
    rw [(hP.2.2.2.2.2 f hf g hg).2]; exact ⟨⟨y, h1⟩, ⟨w, h2⟩⟩
  obtain ⟨w', y', hy', hw'⟩ := hx
  have := g61c_fun hP hg h1 hy'; subst this
  have := g61c_fun hP hfg h2 (g61c_mul hP hf hg hy' hw'); subst this
  exact hw'

end g61c_proto

theorem g61c_mul_bbg (T S : X →L[ℂ] X) :
    graphMul (banachBoundedGraph T) (banachBoundedGraph S) = banachBoundedGraph (T.comp S) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hz, hy⟩
    change z = S x at hz; change y = T z at hy
    change y = T (S x); rw [hy, hz]
  · intro h; exact ⟨S x, rfl, h⟩

theorem g61c_add_bbg (T S : X →L[ℂ] X) :
    graphAdd (banachBoundedGraph T) (banachBoundedGraph S) = banachBoundedGraph (T + S) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, w, hz, hw, hy⟩
    change z = T x at hz; change w = S x at hw; change y = z + w at hy
    change y = T x + S x; rw [hy, hz, hw]
  · intro h; exact ⟨T x, S x, rfl, rfl, h⟩

theorem g61c_scale_bbg (c : ℂ) (T : X →L[ℂ] X) :
    graphScale c (banachBoundedGraph T) = banachBoundedGraph (c • T) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hz, hy⟩
    change z = T x at hz; change y = c • z at hy
    change y = c • T x; rw [hy, hz]
  · intro h; exact ⟨T x, rfl, h⟩

theorem g61c_id_bbg : (identityGraph : Graph X) = banachBoundedGraph (ContinuousLinearMap.id ℂ X) := rfl
theorem g61c_scale_eq {Phi : F → Graph X} (hP : Proto Phi) (c : ℂ) (f : F)
    (h : c ≠ 0 ∨ Bounded (Phi f)) : Phi (c • f) = graphScale c (Phi f) := by
  apply Set.Subset.antisymm _ (hP.2.2.2.1 c f trivial)
  rintro ⟨x, y⟩ hxy
  rcases h with hc | hb
  · refine ⟨c⁻¹ • y, ?_, by simp [smul_smul, hc]⟩
    have := g61c_smul hP trivial c⁻¹ hxy
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · refine ⟨boundedValue (Phi f) x, g61c_bdd_mem hb x, ?_⟩
    exact g61c_fun hP trivial hxy (g61c_smul hP trivial c (g61c_bdd_mem hb x))

theorem g61c_add_eq {Phi : F → Graph X} (hP : Proto Phi) (f g : F) (hb : Bounded (Phi g)) :
    graphAdd (Phi f) (Phi g) = Phi (f + g) := by
  apply Set.Subset.antisymm (hP.2.2.2.2.1 f trivial g trivial)
  rintro ⟨x, y⟩ hxy
  have h1 := g61c_smul hP trivial (-1) (g61c_bdd_mem hb x)
  have h2 := g61c_add hP trivial trivial hxy h1
  have e : f + g + (-1 : ℂ) • g = f := by simp
  rw [e] at h2
  exact ⟨_, _, h2, g61c_bdd_mem hb x, by simp⟩

theorem g61c_mul_eq {Phi : F → Graph X} (hP : Proto Phi) (f g : F) (hb : Bounded (Phi g)) :
    graphMul (Phi f) (Phi g) = Phi (f * g) := by
  apply Set.Subset.antisymm (hP.2.2.2.2.2 f trivial g trivial).1
  rintro ⟨x, w⟩ hxw
  exact ⟨_, g61c_bdd_mem hb x, g61c_mul_dom hP trivial trivial trivial (g61c_bdd_mem hb x) hxw⟩


theorem g61c_det_fwd {Phi : F → Graph X} (hP : Proto Phi) {e f : F} (he : Bounded (Phi e))
    {x y : X} (h : (x, y) ∈ Phi f) : ∃ z, (x, z) ∈ Phi (e * f) ∧ (y, z) ∈ Phi e :=
  ⟨_, g61c_mul hP trivial trivial h (g61c_bdd_mem he y), g61c_bdd_mem he y⟩

theorem g61c_det_mono {Phi : F → Graph X} (hP : Proto Phi) {M M' : Set F} {f : F}
    (hM' : M' ⊆ boundedElements Phi) (hMM : M ⊆ M') (h : Determines Phi M f) :
    Determines Phi M' f := by
  refine ⟨hM', fun x y => ⟨fun hxy e he => g61c_det_fwd hP (hM' he.1) hxy, fun H => ?_⟩⟩
  exact (h.2 x y).2 fun e he => H e ⟨hMM he.1, he.2⟩

theorem g61c_det_sep {Phi : F → Graph X} (hP : Proto Phi) {M : Set F} {f : F}
    (h : Determines Phi M f) : PointSeparating Phi (M ∩ regularizers Phi f) := by
  intro x hx
  have h0 : ((0 : X), x) ∈ Phi f := (h.2 0 x).2 fun e he => ⟨0, g61c_zero hP trivial, hx e he⟩
  exact (g61c_fun hP trivial (g61c_zero hP trivial) h0).symm

theorem g61c_zero_bdd {Phi : F → Graph X} (hP : Proto Phi) : Bounded (Phi 0) := by
  have : Phi 0 = banachBoundedGraph 0 := by
    rw [show (0 : F) = (0 : ℂ) • (1 : F) by simp, g61c_scale_eq hP 0 1
      (Or.inr ⟨ContinuousLinearMap.id ℂ X, hP.2.2.1⟩), hP.2.2.1, g61c_id_bbg, g61c_scale_bbg, zero_smul]
  exact ⟨0, this⟩

theorem g61c_rep_sep {rho : F → X →L[ℂ] X} {S : Set F} :
    PointSeparating (representationGraphs rho) S ↔ ∀ x : X, (∀ e ∈ S, rho e x = 0) → x = 0 := by
  constructor
  · intro h x hx; exact h x fun e he => (hx e he).symm
  · intro h x hx; exact h x fun e he => (hx e he).symm

theorem g61c_anchor_mono {rho : F → X →L[ℂ] X} {S T : Set F} (hST : S ⊆ T)
    (h : AnchorSet (representationGraphs rho) S) : AnchorSet (representationGraphs rho) T :=
  ⟨h.1.mono hST, fun e _ => ⟨rho e, rfl⟩, fun x hx => h.2.2 x fun e he => hx e (hST he)⟩

theorem g61c_anch_comp {rho : F → X →L[ℂ] X} {E : Set F} (hrho : AlgebraRepresentationOn rho E)
    {A : Set F} (hAE : A ⊆ E) (hA : AnchorSet (representationGraphs rho) A) (B : F → Set F)
    (hB : ∀ d ∈ A, B d ⊆ E ∧ AnchorSet (representationGraphs rho) (B d)) (C : Set F)
    (hC : ∀ d ∈ A, ∀ d' ∈ B d, d' * d ∈ C) : AnchorSet (representationGraphs rho) C := by
  obtain ⟨d, hd⟩ := hA.1
  obtain ⟨d', hd'⟩ := (hB d hd).2.1
  refine ⟨⟨_, hC d hd d' hd'⟩, fun e _ => ⟨rho e, rfl⟩, ?_⟩
  rw [g61c_rep_sep]
  intro x hx
  refine g61c_rep_sep.1 hA.2.2 x fun d hd => ?_
  refine g61c_rep_sep.1 (hB d hd).2.2.2 _ fun d' hd' => ?_
  have := hx _ (hC d hd d' hd')
  rw [((hrho.2.2.1 d' ((hB d hd).1 hd') d (hAE hd)).2)] at this
  exact this

theorem g61c_bracket_E {E : Set F} (hE : SubalgebraSet E) {f : F} (hf : f ∈ E) :
    symbolBracket E f = E := by
  ext d; exact ⟨fun h => h.1, fun h => ⟨h, (hE.2.1 d h f hf).2⟩⟩

theorem g61c_maxA_anchored {rho : F → X →L[ℂ] X} {E : Set F} (hrho : AlgebraRepresentationOn rho E)
    (hnd : Nondegenerate rho E) {f : F} (hf : f ∈ maximalAnchored rho E) :
    Anchored (representationGraphs rho) E f :=
  g61c_anch_comp hrho le_rfl hnd (fun e => symbolBracket E (e * f))
    (fun e he => ⟨fun d hd => hd.1, hf e he⟩) _
    (fun e he d hd => ⟨(hrho.1.2.1 d hd.1 e he).2, by rw [mul_assoc]; exact hd.2⟩)

theorem solution [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    (∀ f, AnchorSet (representationGraphs rho) (setCenter E ∩ symbolBracket E f) →
      f ∈ maximalAnchored rho E) ∧
    ((∀ f g : F, f * g = g * f) →
      maximalAnchored rho E = {f | Anchored (representationGraphs rho) E f}) := by
  have hE := hrho.1
  refine ⟨fun f hf e he => g61c_anchor_mono ?_ hf, fun hcomm => ?_⟩
  · rintro d ⟨⟨hdE, hdc⟩, hdf⟩
    refine ⟨hdE, ?_⟩
    rw [← mul_assoc, hdc e he, mul_assoc]; exact (hE.2.1 e he _ hdf.2).2
  · ext f
    refine ⟨fun hf => g61c_maxA_anchored hrho hnd hf, fun hf e he => g61c_anchor_mono ?_ hf⟩
    rintro d ⟨hdE, hdf⟩
    refine ⟨hdE, ?_⟩
    rw [← mul_assoc, hcomm d e, mul_assoc]; exact (hE.2.1 e he _ hdf).2



end

