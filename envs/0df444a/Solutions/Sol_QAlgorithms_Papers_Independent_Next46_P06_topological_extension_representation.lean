-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.topological_extension_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:05:51.454348+00:00
-- url     : https://prove2.me/submissions/f85bf2a8-c78b-4ada-8c9d-24291132dc6e

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

/-- Theorem 9.1, PDF pp.22–23: the constructed map is a (possibly nonunital)
complex algebra homomorphism extending rho, under exactly the two convergence
axioms. The index type is arbitrary, including the empty type. -/
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
section g61c_top
variable {I : Type*} {rho : F → X →L[ℂ] X} {E : Set F} {A : Set (X →L[ℂ] X)}
  {tau1 : (I → F) → F → Prop} {tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop}

theorem g61c_tg_add (hrho : AlgebraRepresentationOn rho E) (hA : SubalgebraSet A)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ) (htau2 : AlgebraicConvergenceOn tau2 A)
    {f g : F} {T T' : X →L[ℂ] X} (h : topologicalGraph rho E A tau1 tau2 f T)
    (h' : topologicalGraph rho E A tau1 tau2 g T') :
    topologicalGraph rho E A tau1 tau2 (f + g) (T + T') := by
  obtain ⟨hT, e, he, h1, h2⟩ := h
  obtain ⟨hT', e', he', h1', h2'⟩ := h'
  refine ⟨(hA.2.1 T hT T' hT').1, fun i => e i + e' i, fun i => (hrho.1.2.1 _ (he i) _ (he' i)).1,
    (htau1.2.2.2.1 e e' f g h1 h1').1, ?_⟩
  rw [show (fun i => rho (e i + e' i)) = (fun i => rho (e i) + rho (e' i)) from
    funext fun i => (hrho.2.2.1 _ (he i) _ (he' i)).1]
  exact (htau2.2.2.2.1 _ _ _ _ h2 h2').1

theorem g61c_tg_mul (hrho : AlgebraRepresentationOn rho E) (hA : SubalgebraSet A)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ) (htau2 : AlgebraicConvergenceOn tau2 A)
    {f g : F} {T T' : X →L[ℂ] X} (h : topologicalGraph rho E A tau1 tau2 f T)
    (h' : topologicalGraph rho E A tau1 tau2 g T') :
    topologicalGraph rho E A tau1 tau2 (f * g) (T * T') := by
  obtain ⟨hT, e, he, h1, h2⟩ := h
  obtain ⟨hT', e', he', h1', h2'⟩ := h'
  refine ⟨(hA.2.1 T hT T' hT').2, fun i => e i * e' i, fun i => (hrho.1.2.1 _ (he i) _ (he' i)).2,
    (htau1.2.2.2.1 e e' f g h1 h1').2, ?_⟩
  rw [show (fun i => rho (e i * e' i)) = (fun i => rho (e i) * rho (e' i)) from
    funext fun i => (hrho.2.2.1 _ (he i) _ (he' i)).2]
  exact (htau2.2.2.2.1 _ _ _ _ h2 h2').2

theorem g61c_tg_smul (hrho : AlgebraRepresentationOn rho E) (hA : SubalgebraSet A)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ) (htau2 : AlgebraicConvergenceOn tau2 A)
    (c : ℂ) {f : F} {T : X →L[ℂ] X} (h : topologicalGraph rho E A tau1 tau2 f T) :
    topologicalGraph rho E A tau1 tau2 (c • f) (c • T) := by
  obtain ⟨hT, e, he, h1, h2⟩ := h
  refine ⟨hA.2.2 c T hT, fun i => c • e i, fun i => hrho.1.2.2 c _ (he i),
    htau1.2.2.2.2 c e f h1, ?_⟩
  rw [show (fun i => rho (c • e i)) = (fun i => c • rho (e i)) from
    funext fun i => hrho.2.2.2 c _ (he i)]
  exact htau2.2.2.2.2 c _ _ h2

theorem g61c_tg_const (hrho : AlgebraRepresentationOn rho E)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ) (htau2 : AlgebraicConvergenceOn tau2 A)
    (himage : ∀ e ∈ E, rho e ∈ A) {e : F} (he : e ∈ E) :
    topologicalGraph rho E A tau1 tau2 e (rho e) :=
  ⟨himage e he, fun _ => e, fun _ => he, htau1.2.2.1 e trivial, htau2.2.2.1 (rho e) (himage e he)⟩

theorem g61c_tg_unique (hrho : AlgebraRepresentationOn rho E) (hA : SubalgebraSet A)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ) (htau2 : AlgebraicConvergenceOn tau2 A)
    (hclosable : JointClosable rho E tau1 tau2)
    {f : F} {T T' : X →L[ℂ] X} (h : topologicalGraph rho E A tau1 tau2 f T)
    (h' : topologicalGraph rho E A tau1 tau2 f T') : T = T' := by
  obtain ⟨_, e, he, h1, h2⟩ := g61c_tg_add hrho hA htau1 htau2 h (g61c_tg_smul hrho hA htau1 htau2 (-1) h')
  rw [show f + (-1 : ℂ) • f = 0 by simp] at h1
  have := hclosable e he _ h1 h2
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at this
  exact this

theorem g61c_tv_eq (hrho : AlgebraRepresentationOn rho E) (hA : SubalgebraSet A)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ) (htau2 : AlgebraicConvergenceOn tau2 A)
    (hclosable : JointClosable rho E tau1 tau2)
    {f : F} {T : X →L[ℂ] X} (h : topologicalGraph rho E A tau1 tau2 f T) :
    topologicalValue rho E A tau1 tau2 f = T := by
  have hex : ∃ T, topologicalGraph rho E A tau1 tau2 f T := ⟨T, h⟩
  unfold topologicalValue; rw [dif_pos hex]
  exact g61c_tg_unique hrho hA htau1 htau2 hclosable (Classical.choose_spec hex) h

end g61c_top


theorem solution [CompleteSpace X] {I : Type*}
    (rho : F → X →L[ℂ] X) (E : Set F) (hrho : AlgebraRepresentationOn rho E)
    (A : Set (X →L[ℂ] X)) (hA : SubalgebraSet A)
    (himage : ∀ e ∈ E, rho e ∈ A)
    (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ)
    (htau2 : AlgebraicConvergenceOn tau2 A)
    (hclosable : JointClosable rho E tau1 tau2) :
    SubalgebraSet (topologicalDomain rho E A tau1 tau2) ∧
    E ⊆ topologicalDomain rho E A tau1 tau2 ∧
    AlgebraRepresentationOn (topologicalValue rho E A tau1 tau2) (topologicalDomain rho E A tau1 tau2) ∧
    (∀ e ∈ E, topologicalValue rho E A tau1 tau2 e = rho e) ∧
    (∀ f T, topologicalGraph rho E A tau1 tau2 f T →
      topologicalValue rho E A tau1 tau2 f = T) := by
  have tv := fun {f} {T} (h : topologicalGraph rho E A tau1 tau2 f T) =>
    g61c_tv_eq hrho hA htau1 htau2 hclosable h
  have h0 := g61c_tg_const hrho htau1 htau2 himage hrho.1.1
  have hsub : SubalgebraSet (topologicalDomain rho E A tau1 tau2) := by
    refine ⟨⟨_, h0⟩, fun f ⟨T, hT⟩ g ⟨T', hT'⟩ => ⟨⟨_, g61c_tg_add hrho hA htau1 htau2 hT hT'⟩,
      ⟨_, g61c_tg_mul hrho hA htau1 htau2 hT hT'⟩⟩, fun c f ⟨T, hT⟩ =>
      ⟨_, g61c_tg_smul hrho hA htau1 htau2 c hT⟩⟩
  refine ⟨hsub, fun e he => ⟨_, g61c_tg_const hrho htau1 htau2 himage he⟩,
    ⟨hsub, ?_, ?_, ?_⟩, fun e he => tv (g61c_tg_const hrho htau1 htau2 himage he),
    fun f T h => tv h⟩
  · rw [tv h0]; exact hrho.2.1
  · rintro f ⟨T, hT⟩ g ⟨T', hT'⟩
    rw [tv hT, tv hT', tv (g61c_tg_add hrho hA htau1 htau2 hT hT'),
      tv (g61c_tg_mul hrho hA htau1 htau2 hT hT')]
    exact ⟨rfl, rfl⟩
  · rintro c f ⟨T, hT⟩
    rw [tv hT, tv (g61c_tg_smul hrho hA htau1 htau2 c hT)]



end

