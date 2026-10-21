-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.extension_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:03:23.299318+00:00
-- url     : https://prove2.me/submissions/406939ca-ddf9-4a58-87ae-4fb8da5b1d6c

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

/-- Theorem 6.1 (Extension Theorem), PDF pp.13–14. The representation on E
need not be unital and E need not contain 1. Formula (6.1) specifies the
constructed calculus and does not replace the existence assertion. -/
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

theorem g61c_maxA_alg {rho : F → X →L[ℂ] X} {E : Set F}
    (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    UnitalSubalgebraSet (maximalAnchored rho E) ∧ E ⊆ maximalAnchored rho E ∧
    AnchoredSet (representationGraphs rho) E (maximalAnchored rho E) ∧
    ∀ S : Subalgebra ℂ F, E ⊆ (S : Set F) →
      AnchoredSet (representationGraphs rho) E (S : Set F) → (S : Set F) ⊆ maximalAnchored rho E := by
  have hE := hrho.1
  have hEsub : E ⊆ maximalAnchored rho E := fun f hf e he => by
    rw [g61c_bracket_E hE (hE.2.1 e he f hf).2]; exact hnd
  refine ⟨⟨⟨?_, fun f hf g hg => ⟨?_, ?_⟩, fun c f hf => ?_⟩, ?_⟩, hEsub,
    fun f hf => g61c_maxA_anchored hrho hnd hf, ?_⟩
  · exact hEsub hE.1
  · intro e he
    refine g61c_anch_comp hrho (fun d hd => hd.1) (hf e he) (fun d => symbolBracket E (d * e * g))
      (fun d hd => ⟨fun d' hd' => hd'.1, hg _ (hE.2.1 d hd.1 e he).2⟩) _ ?_
    intro d hd d' hd'
    refine ⟨(hE.2.1 d' hd'.1 d hd.1).2, ?_⟩
    have : d' * d * (e * (f + g)) = d' * (d * (e * f)) + d' * (d * e * g) := by noncomm_ring
    rw [this]
    exact (hE.2.1 _ (hE.2.1 d' hd'.1 _ hd.2).2 _ hd'.2).1
  · intro e he
    refine g61c_anch_comp hrho (fun d hd => hd.1) (hf e he) (fun d => symbolBracket E (d * (e * f) * g))
      (fun d hd => ⟨fun d' hd' => hd'.1, hg _ hd.2⟩) _ ?_
    intro d hd d' hd'
    refine ⟨(hE.2.1 d' hd'.1 d hd.1).2, ?_⟩
    have : d' * d * (e * (f * g)) = d' * (d * (e * f) * g) := by noncomm_ring
    rw [this]; exact hd'.2
  · intro e he
    refine g61c_anchor_mono ?_ (hf e he)
    rintro d ⟨hdE, hdf⟩
    refine ⟨hdE, ?_⟩
    rw [mul_smul_comm, mul_smul_comm]; exact hE.2.2 c _ hdf
  · intro e he
    rw [mul_one, g61c_bracket_E hE he]; exact hnd
  · intro S hES hS f hf e he
    exact hS _ (S.mul_mem (hES he) hf)

section g61c_ce
variable {rho : F → X →L[ℂ] X} {E : Set F}

theorem g61c_sepw {A : Set F} (hA : AnchorSet (representationGraphs rho) A) {w : X}
    (h : ∀ d ∈ A, rho d w = 0) : w = 0 := g61c_rep_sep.1 hA.2.2 w h

theorem g61c_rmul (hrho : AlgebraRepresentationOn rho E) {a b : F} (ha : a ∈ E) (hb : b ∈ E)
    (v : X) : rho a (rho b v) = rho (a * b) v := by
  rw [(hrho.2.2.1 a ha b hb).2]; rfl

theorem g61c_Em (hrho : AlgebraRepresentationOn rho E) {a b : F} (ha : a ∈ E) (hb : b ∈ E) :
    a * b ∈ E := (hrho.1.2.1 a ha b hb).2

theorem g61c_ce_E (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) {e : F}
    (he : e ∈ E) : canonicalAlgebraicExtension rho E e = banachBoundedGraph (rho e) := by
  ext ⟨x, y⟩
  show (∀ d ∈ symbolBracket E e, rho (d * e) x = rho d y) ↔ y = rho e x
  rw [g61c_bracket_E hrho.1 he]
  constructor
  · intro h
    have : rho e x - y = 0 := g61c_sepw hnd fun d hd => by
      rw [map_sub, g61c_rmul hrho hd he, h d hd, sub_self]
    exact (sub_eq_zero.1 this).symm
  · intro h d hd; rw [h, g61c_rmul hrho hd he]

theorem g61c_ce_fun (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) {f : F}
    (hf : f ∈ maximalAnchored rho E) {x y z : X}
    (h1 : (x, y) ∈ canonicalAlgebraicExtension rho E f)
    (h2 : (x, z) ∈ canonicalAlgebraicExtension rho E f) : y = z := by
  have : y - z = 0 := g61c_sepw (g61c_maxA_anchored hrho hnd hf) fun d hd => by
    rw [map_sub, ← h1 d hd, ← h2 d hd, sub_self]
  exact sub_eq_zero.1 this

theorem g61c_ce_mul (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) {f g : F}
    (hf : f ∈ maximalAnchored rho E) (hg : g ∈ maximalAnchored rho E) {x y w : X}
    (hy : (x, y) ∈ canonicalAlgebraicExtension rho E g)
    (hw : (y, w) ∈ canonicalAlgebraicExtension rho E f) :
    (x, w) ∈ canonicalAlgebraicExtension rho E (f * g) := by
  intro e he
  have hEe := he.1
  have key := g61c_anch_comp hrho (fun d hd => hd.1) (hf e hEe)
    (fun d => symbolBracket E (d * (e * f) * g))
    (fun d hd => ⟨fun d' hd' => hd'.1, hg _ hd.2⟩)
    {c | c ∈ E ∧ rho c (rho (e * (f * g)) x - rho e w) = 0} (by
      intro d hd d' hd'
      have hd'd := g61c_Em hrho hd'.1 hd.1
      refine ⟨hd'd, ?_⟩
      have m1 : d' * (d * (e * f)) ∈ E := g61c_Em hrho hd'.1 hd.2
      have m2 : d' * d * e ∈ E := g61c_Em hrho hd'd hEe
      have a1 := hy (d' * (d * (e * f))) ⟨m1, by
        rw [show d' * (d * (e * f)) * g = d' * (d * (e * f) * g) by noncomm_ring]; exact hd'.2⟩
      have a2 := hw (d' * d * e) ⟨m2, by
        rw [show d' * d * e * f = d' * (d * (e * f)) by noncomm_ring]; exact m1⟩
      rw [map_sub, g61c_rmul hrho hd'd he.2, g61c_rmul hrho hd'd hEe, ← a2,
        show d' * d * (e * (f * g)) = d' * (d * (e * f)) * g by noncomm_ring, a1,
        show d' * d * e * f = d' * (d * (e * f)) by noncomm_ring, sub_self])
  exact (sub_eq_zero.1 (g61c_sepw key fun c hc => hc.2))

theorem g61c_ce_calc (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    CalculusOn (canonicalAlgebraicExtension rho E) (maximalAnchored rho E) := by
  set S := maximalAnchored rho E
  have hE := hrho.1
  have hS := g61c_maxA_alg hrho hnd
  have hES : E ⊆ S := hS.2.1
  have hbE : ∀ e ∈ E, Bounded ((canonicalAlgebraicExtension rho E) e) := fun e he => ⟨rho e, g61c_ce_E hrho hnd he⟩
  have hP : ProtoOn (canonicalAlgebraicExtension rho E) S := by
    refine ⟨hS.1, fun f hf => ⟨?_, ?_, ?_, ?_, fun x y z h1 h2 => g61c_ce_fun hrho hnd hf h1 h2⟩,
      ?_, ?_, ?_, fun f hf g hg => ⟨?_, ?_⟩⟩
    · have : (canonicalAlgebraicExtension rho E) f = ⋂ d ∈ symbolBracket E f, {p : X × X | rho (d * f) p.1 = rho d p.2} := by
        ext p; simp [canonicalAlgebraicExtension]
      rw [this]
      exact isClosed_biInter fun d _ => isClosed_eq ((rho (d * f)).continuous.comp continuous_fst)
        ((rho d).continuous.comp continuous_snd)
    · intro d _; simp
    · intro x y z w h1 h2 d hd
      show rho (d * f) (x + z) = rho d (y + w)
      rw [map_add, map_add, h1 d hd, h2 d hd]
    · intro c x y h d hd
      show rho (d * f) (c • x) = rho d (c • y)
      rw [map_smul, map_smul, h d hd]
    · ext ⟨x, y⟩
      show (∀ d ∈ symbolBracket E 1, rho (d * 1) x = rho d y) ↔ y = x
      have h1 : symbolBracket E 1 = E := by ext e; simp [symbolBracket]
      rw [h1]
      constructor
      · intro h
        have : y - x = 0 := g61c_sepw hnd fun d hd => by
          rw [map_sub, ← h d hd, mul_one, sub_self]
        exact sub_eq_zero.1 this
      · intro h d _; rw [h, mul_one]
    · rintro c f hf ⟨x, y⟩ ⟨y', hy', rfl⟩ d hd
      show rho (d * (c • f)) x = rho d (c • y')
      by_cases hc : c = 0
      · subst hc; simp [hrho.2.1]
      · have hdf : d * f ∈ E := by
          have := hE.2.2 c⁻¹ _ hd.2
          rwa [mul_smul_comm, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        rw [mul_smul_comm, hrho.2.2.2 c _ hdf, map_smul, ContinuousLinearMap.smul_apply,
          hy' d ⟨hd.1, hdf⟩]
    · rintro f hf g hg ⟨x, s⟩ ⟨y, z, hy, hz, rfl⟩ e he
      have hEe := he.1
      have key := g61c_anch_comp hrho (fun d hd => hd.1) (hf e hEe)
        (fun d => symbolBracket E (d * e * g))
        (fun d hd => ⟨fun d' hd' => hd'.1, hg _ (g61c_Em hrho hd.1 hEe)⟩)
        {c | c ∈ E ∧ rho c (rho (e * (f + g)) x - rho e (y + z)) = 0} (by
          intro d hd d' hd'
          have hd'd := g61c_Em hrho hd'.1 hd.1
          refine ⟨hd'd, ?_⟩
          have m1 : d' * (d * (e * f)) ∈ E := g61c_Em hrho hd'.1 hd.2
          have m2 : d' * d * e ∈ E := g61c_Em hrho hd'd hEe
          have a1 := hy (d' * d * e) ⟨m2, by
            rw [show d' * d * e * f = d' * (d * (e * f)) by noncomm_ring]; exact m1⟩
          have a2 := hz (d' * d * e) ⟨m2, by
            rw [show d' * d * e * g = d' * (d * e * g) by noncomm_ring]; exact hd'.2⟩
          rw [map_sub, g61c_rmul hrho hd'd he.2, g61c_rmul hrho hd'd hEe, map_add, ← a1, ← a2,
            show d' * d * (e * (f + g)) = d' * (d * (e * f)) + d' * (d * e * g) by noncomm_ring,
            (hrho.2.2.1 _ m1 _ hd'.2).1,
            show d' * d * e * f = d' * (d * (e * f)) by noncomm_ring,
            show d' * d * e * g = d' * (d * e * g) by noncomm_ring]
          simp)
      exact (sub_eq_zero.1 (g61c_sepw key fun c hc => hc.2))
    · rintro ⟨x, w⟩ ⟨y, hy, hw⟩
      exact g61c_ce_mul hrho hnd hf hg hy hw
    · ext x
      constructor
      · rintro ⟨w, y, hy, hw⟩
        exact ⟨⟨y, hy⟩, ⟨w, g61c_ce_mul hrho hnd hf hg hy hw⟩⟩
      · rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        refine ⟨w, y, hy, fun e he => ?_⟩
        have hef := he.2
        have hA := hg (e * f) hef
        have : rho (e * f) y - rho e w = 0 := g61c_sepw hA fun d hd => by
          have b1 := hy (d * (e * f)) ⟨g61c_Em hrho hd.1 hef, by rw [mul_assoc]; exact hd.2⟩
          have b2 := hw (d * e) ⟨g61c_Em hrho hd.1 he.1, by
            rw [show d * e * (f * g) = d * (e * f * g) by noncomm_ring]; exact hd.2⟩
          rw [map_sub, g61c_rmul hrho hd.1 hef, g61c_rmul hrho hd.1 he.1, ← b1, ← b2,
            show d * e * (f * g) = d * (e * f) * g by noncomm_ring, sub_self]
        exact sub_eq_zero.1 this
  refine ⟨hP, fun f hf => ⟨Set.inter_subset_right, fun x y => ⟨?_, ?_⟩⟩⟩
  · intro hxy d hd
    obtain ⟨T, hT⟩ := hd.2.1
    refine ⟨T y, ?_, by rw [hT]; rfl⟩
    exact (hP.2.2.2.2.2 d hd.1.1 f hf).1 ⟨y, hxy, by rw [hT]; rfl⟩
  · intro H e he
    obtain ⟨z, h1, h2⟩ := H e ⟨⟨hES he.1, hbE e he.1⟩, hbE e he.1, hbE _ he.2⟩
    rw [g61c_ce_E hrho hnd he.2] at h1
    rw [g61c_ce_E hrho hnd he.1] at h2
    change z = rho (e * f) x at h1
    change z = rho e y at h2
    rw [← h1, ← h2]

end g61c_ce

theorem g61c_cec {rho : F → X →L[ℂ] X} {E : Set F}
    (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    CalculusOn (canonicalAlgebraicExtension rho E) (maximalAnchored rho E) ∧
    (∀ e ∈ E, canonicalAlgebraicExtension rho E e = banachBoundedGraph (rho e)) ∧
    AlgebraicCoreOn (canonicalAlgebraicExtension rho E) E (maximalAnchored rho E) ∧
    ∀ Psi : F → Graph X, CalculusOn Psi (maximalAnchored rho E) →
      (∀ e ∈ E, Psi e = banachBoundedGraph (rho e)) →
      ∀ f ∈ maximalAnchored rho E, Psi f = canonicalAlgebraicExtension rho E f := by
  have hS := g61c_maxA_alg hrho hnd
  have hES := hS.2.1
  have hbE : ∀ e ∈ E, Bounded (canonicalAlgebraicExtension rho E e) :=
    fun e he => ⟨rho e, g61c_ce_E hrho hnd he⟩
  refine ⟨g61c_ce_calc hrho hnd, fun e he => g61c_ce_E hrho hnd he, ?_, ?_⟩
  · refine ⟨fun e he => ⟨hES he, hbE e he⟩, fun f hf => ⟨fun e he => hbE e he,
      fun e he => hbE e he.1, fun x y => ⟨?_, ?_⟩⟩⟩
    · intro hxy e he
      refine ⟨rho (e * f) x, by rw [g61c_ce_E hrho hnd he.1.2]; rfl, ?_⟩
      rw [g61c_ce_E hrho hnd he.1.1]
      exact hxy e he.1
    · intro H e he
      obtain ⟨z, h1, h2⟩ := H e ⟨he, hbE e he.1, hbE _ he.2⟩
      rw [g61c_ce_E hrho hnd he.2] at h1
      rw [g61c_ce_E hrho hnd he.1] at h2
      change z = rho (e * f) x at h1
      change z = rho e y at h2
      rw [← h1, ← h2]
  · intro Psi hPsi hag f hf
    have hP := hPsi.1
    apply Set.Subset.antisymm
    · rintro ⟨x, y⟩ hxy e he
      have h1 : (y, rho e y) ∈ Psi e := by rw [hag e he.1]; rfl
      have h2 := g61c_mul hP (hES he.1) hf hxy h1
      rw [hag _ he.2] at h2
      exact h2.symm
    · rintro ⟨x, y⟩ hxy
      refine ((hPsi.2 f hf).2 x y).2 fun d hd => ?_
      have hdS : d ∈ maximalAnchored rho E := hd.1.1
      have Bd : Bounded (Psi d) := hd.2.1
      have Bdf : Bounded (Psi (d * f)) := hd.2.2
      have hdfS : d * f ∈ maximalAnchored rho E := (hS.1.1.2.1 d hdS f hf).2
      set z1 := boundedValue (Psi (d * f)) x
      set z2 := boundedValue (Psi d) y
      have hz1 : (x, z1) ∈ Psi (d * f) := g61c_bdd_mem Bdf x
      have hz2 : (y, z2) ∈ Psi d := g61c_bdd_mem Bd y
      have hu : z1 - z2 = 0 := by
        have key := g61c_anch_comp hrho (fun k hk => hk.1) (g61c_maxA_anchored hrho hnd hdS)
          (fun k => symbolBracket E (k * d * f)) (fun k hk => ⟨fun k' hk' => hk'.1, hf _ hk.2⟩)
          {c | c ∈ E ∧ rho c (z1 - z2) = 0} (by
            intro k hk k' hk'
            have hkk := g61c_Em hrho hk'.1 hk.1
            refine ⟨hkk, ?_⟩
            have m1 : k' * (k * d) ∈ E := g61c_Em hrho hk'.1 hk.2
            have a1 : (x, rho (k' * k) z1) ∈ Psi (k' * k * (d * f)) :=
              g61c_mul hP (hES hkk) hdfS hz1 (by rw [hag _ hkk]; rfl)
            rw [show k' * k * (d * f) = k' * (k * d * f) by noncomm_ring, hag _ hk'.2] at a1
            have a2 : (y, rho (k' * k) z2) ∈ Psi (k' * k * d) :=
              g61c_mul hP (hES hkk) hdS hz2 (by rw [hag _ hkk]; rfl)
            rw [show k' * k * d = k' * (k * d) by noncomm_ring, hag _ m1] at a2
            have a3 := hxy (k' * (k * d)) ⟨m1, by
              rw [show k' * (k * d) * f = k' * (k * d * f) by noncomm_ring]; exact hk'.2⟩
            change rho (k' * k) z1 = rho (k' * (k * d * f)) x at a1
            change rho (k' * k) z2 = rho (k' * (k * d)) y at a2
            rw [map_sub, a1, a2, show k' * (k * d * f) = k' * (k * d) * f by noncomm_ring, a3,
              sub_self])
        exact g61c_sepw key fun c hc => hc.2
      rw [sub_eq_zero] at hu
      exact ⟨z1, hz1, hu ▸ hz2⟩

theorem solution [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E)
    (hanchor : AnchoredSet (representationGraphs rho) E Set.univ) :
    ∃ Phi : F → Graph X, AbstractCalculus Phi ∧
      (∀ e ∈ E, Phi e = banachBoundedGraph (rho e)) ∧
      (∀ f, Phi f = canonicalAlgebraicExtension rho E f) ∧
      (∀ Psi : F → Graph X, AbstractCalculus Psi →
        (∀ e ∈ E, Psi e = banachBoundedGraph (rho e)) → Psi = Phi) := by
  have hnd : Nondegenerate rho E := by
    have := hanchor 1 trivial
    have h1 : symbolBracket E 1 = E := by ext e; simp [symbolBracket]
    unfold Anchored at this; rwa [h1] at this
  have hmax : maximalAnchored rho E = Set.univ :=
    Set.eq_univ_of_forall fun f e _ => hanchor (e * f) trivial
  obtain ⟨hC, hE1, _, hU⟩ := g61c_cec hrho hnd
  rw [hmax] at hC hU
  exact ⟨canonicalAlgebraicExtension rho E, hC, hE1, fun f => rfl,
    fun Psi hPsi hag => funext fun f => hU Psi hPsi hag f trivial⟩



end

