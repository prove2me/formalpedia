-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.bounded_calculi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:32:56.101986+00:00
-- url     : https://prove2.me/submissions/9e50f6fd-73e2-4a09-bb3e-11b6209fee41

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

/-- Example 3.3, PDF p.7: bounded proto-calculi are exactly unital bounded
representations, and every such representation satisfies FC4. -/
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

theorem g61c_bbg_closedop (T : X →L[ℂ] X) : BanachClosedOperator (banachBoundedGraph T) := by
  refine ⟨isClosed_eq continuous_snd (T.continuous.comp continuous_fst), (map_zero T).symm, ?_, ?_, ?_⟩
  · intro x y z w h1 h2
    change y = T x at h1; change w = T z at h2
    change y + w = T (x + z); rw [map_add, h1, h2]
  · intro c x y h
    change y = T x at h
    change c • y = T (c • x); rw [map_smul, h]
  · intro x y z h1 h2
    change y = T x at h1; change z = T x at h2
    rw [h1, h2]

theorem g61c_dom_bbg (T : X →L[ℂ] X) : graphDomain (banachBoundedGraph T) = Set.univ := by
  ext x; simp only [Set.mem_univ, iff_true]; exact ⟨T x, rfl⟩

theorem g61c_hom_proto (rho : F →ₐ[ℂ] (X →L[ℂ] X)) :
    Proto (fun f => banachBoundedGraph (rho f)) := by
  refine ⟨⟨⟨trivial, fun _ _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => trivial⟩, trivial⟩,
    fun f _ => g61c_bbg_closedop _, ?_, ?_, ?_, ?_⟩
  · simp only [map_one]; rfl
  · intro c f _
    simp only [map_smul, g61c_scale_bbg]; exact le_rfl
  · intro f _ g _
    simp only [map_add, g61c_add_bbg]; exact le_rfl
  · intro f _ g _
    simp only [map_mul, g61c_mul_bbg, g61c_dom_bbg, Set.inter_univ]
    exact ⟨le_rfl, trivial⟩


theorem solution [CompleteSpace X] (Phi : F → Graph X) :
    ((Proto Phi ∧ ∀ f, Bounded (Phi f)) ↔
      ∃ rho : F →ₐ[ℂ] (X →L[ℂ] X), ∀ f, Phi f = banachBoundedGraph (rho f)) ∧
    (∀ rho : F →ₐ[ℂ] (X →L[ℂ] X), AbstractCalculus (fun f => banachBoundedGraph (rho f))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hP, hb⟩
    have hval : ∀ f, Phi f = banachBoundedGraph (boundedValue (Phi f)) := fun f => g61c_bv_spec (hb f)
    have hsc : ∀ c : ℂ, Phi (c • (1 : F)) = banachBoundedGraph (c • ContinuousLinearMap.id ℂ X) := by
      intro c
      rw [g61c_scale_eq hP c 1 (Or.inr (hb 1)), hP.2.2.1, g61c_id_bbg, g61c_scale_bbg]
    let rho : F →ₐ[ℂ] (X →L[ℂ] X) :=
      { toFun := fun f => boundedValue (Phi f)
        map_one' := g61c_bv_eq hP.2.2.1
        map_mul' := fun a b => by
          apply g61c_bv_eq
          rw [← g61c_mul_eq hP _ _ (hb b)]
          conv_lhs => rw [hval a, hval b]
          exact g61c_mul_bbg _ _
        map_zero' := by
          apply g61c_bv_eq
          rw [show (0 : F) = (0 : ℂ) • (1 : F) by simp, hsc]
          simp
        map_add' := fun a b => by
          apply g61c_bv_eq
          rw [← g61c_add_eq hP _ _ (hb b)]
          conv_lhs => rw [hval a, hval b]
          exact g61c_add_bbg _ _
        commutes' := fun c => by
          apply g61c_bv_eq
          rw [Algebra.algebraMap_eq_smul_one, hsc, Algebra.algebraMap_eq_smul_one]
          rfl }
    exact ⟨rho, hval⟩
  · rintro ⟨rho, hrho⟩
    have : Phi = fun f => banachBoundedGraph (rho f) := funext hrho
    subst this
    exact ⟨g61c_hom_proto rho, fun f => ⟨rho f, rfl⟩⟩
  · intro rho
    refine ⟨g61c_hom_proto rho, fun f _ => ⟨fun e _ => ⟨rho e, rfl⟩, fun x y => ⟨?_, ?_⟩⟩⟩
    · intro h e _
      refine ⟨rho (e * f) x, rfl, ?_⟩
      change rho (e * f) x = rho e y
      change y = rho f x at h
      rw [h, map_mul]; rfl
    · intro h
      have hb : ∀ g : F, Bounded (banachBoundedGraph (rho g)) := fun g => ⟨rho g, rfl⟩
      obtain ⟨z, h1, h2⟩ := h 1 ⟨⟨trivial, hb 1⟩, hb 1, by rw [one_mul]; exact hb f⟩
      change z = rho (1 * f) x at h1
      change z = rho 1 y at h2
      change y = rho f x
      rw [map_one, one_mul] at *
      rw [← h1]; exact h2.symm



end

