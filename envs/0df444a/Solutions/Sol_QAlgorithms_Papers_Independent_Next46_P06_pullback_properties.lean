-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.pullback_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:43:33.316001+00:00
-- url     : https://prove2.me/submissions/4ee66c9e-a300-45a3-8d4d-db2dab1763a8

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

/-- Lemma 5.3, PDF p.11: all five clauses. Restriction is expressed on the
ambient carrier with explicit range guards. Clause (e) is one-way only. -/
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

theorem g61c_comm_det {Phi : F → Graph X} (hPhi : AbstractCalculus Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (f : F) (E : Set F)
    (hE : E ⊆ regularizers Phi f) (hanchor : AnchorSet Phi E) :
    Determines Phi E f := by
  have hP : Proto Phi := hPhi.1
  refine ⟨hanchor.2.1, fun x y => ⟨fun hxy e he => g61c_det_fwd hP (hanchor.2.1 he.1) hxy,
    fun H => ?_⟩⟩
  refine ((hPhi.2 f trivial).2 x y).2 fun d hd => ?_
  have Bd : Bounded (Phi d) := hd.2.1
  have Bdf : Bounded (Phi (d * f)) := hd.2.2
  set z1 := boundedValue (Phi (d * f)) x
  set z2 := boundedValue (Phi d) y
  have hz1 : (x, z1) ∈ Phi (d * f) := g61c_bdd_mem Bdf x
  have hz2 : (y, z2) ∈ Phi d := g61c_bdd_mem Bd y
  have hu : z1 - z2 = 0 := by
    refine hanchor.2.2 _ fun e he => ?_
    have Be : Bounded (Phi e) := hanchor.2.1 he
    obtain ⟨z, h1, h2⟩ := H e ⟨he, hE he⟩
    set Te := boundedValue (Phi e)
    have a1 : (x, Te z1) ∈ Phi (e * (d * f)) := g61c_mul hP trivial trivial hz1 (g61c_bdd_mem Be z1)
    have a2 : (x, boundedValue (Phi d) z) ∈ Phi (d * (e * f)) :=
      g61c_mul hP trivial trivial h1 (g61c_bdd_mem Bd z)
    have r1 : e * (d * f) = d * (e * f) := by
      rw [← mul_assoc, ← mul_assoc, hcomm e d]
    rw [r1] at a1
    have b1 := g61c_fun hP trivial a1 a2
    have a3 : (y, Te z2) ∈ Phi (e * d) := g61c_mul hP trivial trivial hz2 (g61c_bdd_mem Be z2)
    have a4 : (y, boundedValue (Phi d) z) ∈ Phi (d * e) :=
      g61c_mul hP trivial trivial h2 (g61c_bdd_mem Bd z)
    rw [hcomm e d] at a3
    have b2 := g61c_fun hP trivial a3 a4
    have hm := g61c_bdd_mem Be (z1 - z2)
    rw [map_sub, b1, b2, sub_self] at hm
    exact hm
  rw [sub_eq_zero] at hu
  exact ⟨z1, hz1, hu ▸ hz2⟩

theorem g61c_proto_on {Phi : F → Graph X} (hP : Proto Phi) {S : Set F} (hS : UnitalSubalgebraSet S) :
    ProtoOn Phi S :=
  ⟨hS, fun f _ => hP.2.1 f trivial, hP.2.2.1, fun c f _ => hP.2.2.2.1 c f trivial,
    fun f _ g _ => hP.2.2.2.2.1 f trivial g trivial, fun f _ g _ => hP.2.2.2.2.2 f trivial g trivial⟩

theorem g61c_usub (S : Subalgebra ℂ F) : UnitalSubalgebraSet (S : Set F) :=
  ⟨⟨S.zero_mem, fun _ hf _ hg => ⟨S.add_mem hf hg, S.mul_mem hf hg⟩, fun c _ hf => S.smul_mem hf c⟩,
    S.one_mem⟩

theorem g61c_restr {Phi : F → Graph X} (hPhi : AbstractCalculus Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (S : Subalgebra ℂ F)
    (hanchor : ∀ g : S, AnchorSet Phi (regularizers Phi (g : F) ∩ (S : Set F))) :
    CalculusOn Phi (S : Set F) := by
  refine ⟨g61c_proto_on hPhi.1 (g61c_usub S), fun f hf => ?_⟩
  have h := g61c_comm_det hPhi hcomm f _ Set.inter_subset_left (hanchor ⟨f, hf⟩)
  exact g61c_det_mono hPhi.1 Set.inter_subset_right (fun e he => ⟨he.2, he.1.1⟩) h

theorem g61c_pb_det {Phi : F → Graph X} (eta : G →ₐ[ℂ] F) (E : Set G) (g : G) :
    Determines (pullback Phi eta) E g ↔ Determines Phi (eta '' E) (eta g) := by
  have key : ∀ x y, (∀ e ∈ E ∩ regularizers (pullback Phi eta) g,
      regularizingEquation (pullback Phi eta) g e x y) ↔
      (∀ e ∈ eta '' E ∩ regularizers Phi (eta g), regularizingEquation Phi (eta g) e x y) := by
    intro x y; constructor
    · rintro h _ ⟨⟨e, he, rfl⟩, hr1, hr2⟩
      obtain ⟨z, h1, h2⟩ := h e ⟨he, hr1, show Bounded (Phi (eta (e * g))) by rw [map_mul]; exact hr2⟩
      exact ⟨z, by rw [← map_mul]; exact h1, h2⟩
    · rintro h e ⟨he, hr1, hr2⟩
      obtain ⟨z, h1, h2⟩ := h (eta e) ⟨⟨e, he, rfl⟩, hr1,
        show Bounded (Phi (eta e * eta g)) by rw [← map_mul]; exact hr2⟩
      exact ⟨z, show (x, z) ∈ Phi (eta (e * g)) by rw [map_mul]; exact h1, h2⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rintro _ ⟨e, he, rfl⟩; exact h1 he, fun x y => (h2 x y).trans (key x y)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun e he => h1 ⟨e, he, rfl⟩, fun x y => (h2 x y).trans (key x y).symm⟩

theorem g61c_pb_anchor {Phi : F → Graph X} (eta : G →ₐ[ℂ] F) (E : Set G) :
    AnchorSet (pullback Phi eta) E ↔ AnchorSet Phi (eta '' E) := by
  simp only [AnchorSet, PointSeparating, pullback, boundedElements, Set.image_nonempty,
    Set.image_subset_iff, Set.forall_mem_image, Set.preimage_setOf_eq]

theorem g61c_pb_proto {Phi : F → Graph X} (hP : Proto Phi) (eta : G →ₐ[ℂ] F) :
    Proto (pullback Phi eta) := by
  refine ⟨⟨⟨trivial, fun _ _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => trivial⟩, trivial⟩,
    fun f _ => hP.2.1 (eta f) trivial, ?_, ?_, ?_, ?_⟩
  · show Phi (eta 1) = _; rw [map_one]; exact hP.2.2.1
  · intro c f _; show _ ⊆ Phi (eta (c • f)); rw [map_smul]; exact hP.2.2.2.1 c _ trivial
  · intro f _ g _; show _ ⊆ Phi (eta (f + g)); rw [map_add]; exact hP.2.2.2.2.1 _ trivial _ trivial
  · intro f _ g _; show graphMul (Phi (eta f)) (Phi (eta g)) ⊆ Phi (eta (f * g)) ∧
      graphDomain (graphMul (Phi (eta f)) (Phi (eta g))) =
        graphDomain (Phi (eta g)) ∩ graphDomain (Phi (eta (f * g)))
    rw [map_mul]
    exact hP.2.2.2.2.2 _ trivial _ trivial

theorem g61c_pb_reg {Phi : F → Graph X} (hP : Proto Phi) (eta : G →ₐ[ℂ] F) :
    AbstractCalculus (pullback Phi eta) ↔ CalculusOn Phi (Set.range eta) := by
  have hr : UnitalSubalgebraSet (Set.range eta) := by
    have := g61c_usub eta.range; rwa [AlgHom.coe_range] at this
  have hs : eta '' (Set.univ ∩ boundedElements (pullback Phi eta)) =
      Set.range eta ∩ boundedElements Phi := by
    ext f; constructor
    · rintro ⟨g, ⟨_, hg⟩, rfl⟩; exact ⟨⟨g, rfl⟩, hg⟩
    · rintro ⟨⟨g, rfl⟩, hg⟩; exact ⟨g, ⟨trivial, hg⟩, rfl⟩
  constructor
  · intro h
    refine ⟨g61c_proto_on hP hr, ?_⟩
    rintro _ ⟨g, rfl⟩
    rw [← hs, ← g61c_pb_det]; exact h.2 g trivial
  · intro h
    refine ⟨g61c_pb_proto hP eta, fun g _ => ?_⟩
    rw [g61c_pb_det, hs]; exact h.2 _ ⟨g, rfl⟩

theorem solution [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (eta : G →ₐ[ℂ] F) (E : Set G) (hE : E ⊆ boundedElements (pullback Phi eta)) (g : G) :
    (boundedElements (pullback Phi eta) = eta ⁻¹' boundedElements Phi ∧
      eta '' boundedElements (pullback Phi eta) = boundedElements Phi ∩ Set.range eta ∧
      eta '' boundedElements (pullback Phi eta) = {f | f ∈ Set.range eta ∧ Bounded (Phi f)}) ∧
    (AnchorSet (pullback Phi eta) E ↔ AnchorSet Phi (eta '' E)) ∧
    (eta '' symbolBracket E g ⊆ symbolBracket (eta '' E) (eta g)) ∧
    (Determines (pullback Phi eta) E g ↔ Determines Phi (eta '' E) (eta g)) ∧
    (AlgebraicCoreOn (pullback Phi eta) E Set.univ →
      AlgebraicCoreOn Phi (eta '' E) (Set.range eta)) := by
  refine ⟨⟨rfl, ?_, ?_⟩, g61c_pb_anchor eta E, ?_, g61c_pb_det eta E g, ?_⟩
  · exact (Set.image_preimage_eq_inter_range : eta '' (eta ⁻¹' boundedElements Phi) = _)
  · rw [show boundedElements (pullback Phi eta) = eta ⁻¹' boundedElements Phi from rfl,
      Set.image_preimage_eq_inter_range]
    ext f; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, boundedElements]; exact and_comm
  · rintro _ ⟨e, ⟨he, heg⟩, rfl⟩
    exact ⟨⟨e, he, rfl⟩, ⟨e * g, heg, map_mul eta e g⟩⟩
  · intro hc
    refine ⟨fun f hf => ?_, ?_⟩
    · obtain ⟨e, he, rfl⟩ := hf
      exact ⟨⟨e, rfl⟩, (hc.1 he).2⟩
    · rintro _ ⟨g, rfl⟩
      have hg := (hc.2 g trivial)
      have himg : eta '' E ⊆ boundedElements Phi := by
        rintro _ ⟨e, he, rfl⟩; exact (hc.1 he).2
      refine ⟨himg, ?_⟩
      have h2 := (g61c_pb_det eta _ g).1 hg.2
      refine g61c_det_mono hPhi (fun e he => himg he.1) ?_ h2
      rintro _ ⟨e, ⟨he, heg⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, ⟨e * g, heg, map_mul eta e g⟩⟩



end

