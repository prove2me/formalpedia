-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.anchored_bounded_part_determines
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:48:31.62151+00:00
-- url     : https://prove2.me/submissions/20327ebb-c52e-4c4d-84e1-174e69ff4d69

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

/-- Theorem 4.2, PDF pp.8–10: both determination and the multiplicative-core
conclusion are retained, without an ambient commutativity hypothesis. -/
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

theorem g61c_bdd_mul {Phi : F → Graph X} (hP : Proto Phi) {a b : F} (ha : Bounded (Phi a))
    (hb : Bounded (Phi b)) : Bounded (Phi (a * b)) := by
  obtain ⟨T, hT⟩ := ha; obtain ⟨S, hS⟩ := hb
  exact ⟨T.comp S, by rw [← g61c_mul_eq hP a b ⟨S, hS⟩, hT, hS, g61c_mul_bbg]⟩

theorem g61c_anch_det {Phi : F → Graph X} (hPhi : AbstractCalculus Phi) {E : Set F}
    (hE : E ⊆ boundedElements Phi) (hanchor : AnchoredSet Phi E (boundedElements Phi)) (f : F) :
    Determines Phi E f := by
  have hP : Proto Phi := hPhi.1
  refine ⟨hE, fun x y => ⟨fun hxy e he => g61c_det_fwd hP (hE he.1) hxy, fun H => ?_⟩⟩
  refine ((hPhi.2 f trivial).2 x y).2 fun d hd => ?_
  have Bd : Bounded (Phi d) := hd.2.1
  have Bdf : Bounded (Phi (d * f)) := hd.2.2
  set z1 := boundedValue (Phi (d * f)) x
  set z2 := boundedValue (Phi d) y
  have hz1 : (x, z1) ∈ Phi (d * f) := g61c_bdd_mem Bdf x
  have hz2 : (y, z2) ∈ Phi d := g61c_bdd_mem Bd y
  have hu : z1 - z2 = 0 := by
    refine (hanchor d Bd).2.2 _ fun e he => ?_
    have Be : Bounded (Phi e) := hE he.1
    have Bedf : Bounded (Phi (e * d * f)) := by
      rw [mul_assoc]; exact g61c_bdd_mul hP Be Bdf
    obtain ⟨z, h1, h2⟩ := H (e * d) ⟨he.2, hE he.2, Bedf⟩
    have a1 : (x, boundedValue (Phi e) z1) ∈ Phi (e * (d * f)) :=
      g61c_mul hP trivial trivial hz1 (g61c_bdd_mem Be z1)
    rw [← mul_assoc] at a1
    have b1 := g61c_fun hP trivial a1 h1
    have a2 : (y, boundedValue (Phi e) z2) ∈ Phi (e * d) :=
      g61c_mul hP trivial trivial hz2 (g61c_bdd_mem Be z2)
    have b2 := g61c_fun hP trivial a2 h2
    have hm := g61c_bdd_mem Be (z1 - z2)
    rw [map_sub, b1, b2, sub_self] at hm
    exact hm
  rw [sub_eq_zero] at hu
  exact ⟨z1, hz1, hu ▸ hz2⟩

theorem solution [CompleteSpace X] (Phi : F → Graph X) (hPhi : AbstractCalculus Phi)
    (E : Set F) (hE : E ⊆ boundedElements Phi)
    (hanchor : AnchoredSet Phi E (boundedElements Phi)) :
    (∀ f, Determines Phi E f) ∧
    (MulClosedSet E → AlgebraicCoreOn Phi E Set.univ) := by
  have hP : Proto Phi := hPhi.1
  refine ⟨g61c_anch_det hPhi hE hanchor, fun hmc => ⟨fun e he => ⟨trivial, hE he⟩, fun f _ =>
    ⟨hE, fun e he => hE he.1, fun x y => ⟨fun hxy e he => g61c_det_fwd hP (hE he.1.1) hxy,
      fun H => ?_⟩⟩⟩⟩
  refine ((g61c_anch_det hPhi hE hanchor f).2 x y).2 fun e he => ?_
  have Be : Bounded (Phi e) := hE he.1
  have Bef : Bounded (Phi (e * f)) := he.2.2
  set z1 := boundedValue (Phi (e * f)) x
  set z2 := boundedValue (Phi e) y
  have hz1 : (x, z1) ∈ Phi (e * f) := g61c_bdd_mem Bef x
  have hz2 : (y, z2) ∈ Phi e := g61c_bdd_mem Be y
  have hu : z1 - z2 = 0 := by
    refine (hanchor (e * f) Bef).2.2 _ fun k hk => ?_
    have Bk : Bounded (Phi k) := hE hk.1
    have hke : k * e ∈ E := hmc k hk.1 e he.1
    have hkef : k * e * f ∈ E := by rw [mul_assoc]; exact hk.2
    obtain ⟨z, h1, h2⟩ := H (k * e) ⟨⟨hke, hkef⟩, hE hke, hE hkef⟩
    have a1 : (x, boundedValue (Phi k) z1) ∈ Phi (k * (e * f)) :=
      g61c_mul hP trivial trivial hz1 (g61c_bdd_mem Bk z1)
    rw [← mul_assoc] at a1
    have b1 := g61c_fun hP trivial a1 h1
    have a2 : (y, boundedValue (Phi k) z2) ∈ Phi (k * e) :=
      g61c_mul hP trivial trivial hz2 (g61c_bdd_mem Bk z2)
    have b2 := g61c_fun hP trivial a2 h2
    have hm := g61c_bdd_mem Bk (z1 - z2)
    rw [map_sub, b1, b2, sub_self] at hm
    exact hm
  rw [sub_eq_zero] at hu
  exact ⟨z1, hz1, hu ▸ hz2⟩



end

