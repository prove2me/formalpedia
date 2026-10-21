-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.proto_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:30:34.774148+00:00
-- url     : https://prove2.me/submissions/c5779fbb-7448-439d-957d-3a85f5ba9686

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

/-- Theorem 2.1, PDF p.5: all four assertions, with actual domains and a
noncommutative ambient algebra. The zero-scalar exception is explicit. -/
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


theorem solution [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi) :
    (∀ (c : ℂ) f, c ≠ 0 ∨ Bounded (Phi f) → Phi (c • f) = graphScale c (Phi f)) ∧
    (∀ f g, Bounded (Phi g) →
      graphAdd (Phi f) (Phi g) = Phi (f + g) ∧ graphMul (Phi f) (Phi g) = Phi (f * g)) ∧
    (∀ f g, f * g = 1 → InjectiveGraph (Phi g) ∧ graphInverse (Phi g) ⊆ Phi f ∧
      (f * g = g * f → graphInverse (Phi g) = Phi f)) ∧
    (∃ B : Subalgebra ℂ F, (B : Set F) = boundedElements Phi ∧
      ∃ rho : B →ₐ[ℂ] (X →L[ℂ] X), ∀ f : B, Phi (f : F) = banachBoundedGraph (rho f)) := by
  refine ⟨fun c f h => g61c_scale_eq hPhi c f h, fun f g hb => ⟨g61c_add_eq hPhi f g hb,
    g61c_mul_eq hPhi f g hb⟩, ?_, ?_⟩
  · intro f g hfg
    have key : ∀ x y, (x, y) ∈ Phi g → (y, x) ∈ Phi f := by
      intro x y h
      have h1 : (x, x) ∈ Phi (f * g) := by rw [hfg]; exact g61c_one hPhi x
      exact g61c_mul_dom hPhi trivial trivial trivial h h1
    refine ⟨fun x z y h1 h2 => g61c_fun hPhi trivial (key _ _ h1) (key _ _ h2),
      fun p hp => key _ _ hp, fun hc => ?_⟩
    apply Set.Subset.antisymm (fun p hp => key _ _ hp)
    rintro ⟨y, x⟩ h
    have h1 : (y, y) ∈ Phi (g * f) := by rw [← hc, hfg]; exact g61c_one hPhi y
    exact g61c_mul_dom hPhi trivial trivial trivial h h1
  · have hbadd : ∀ f g, Bounded (Phi f) → Bounded (Phi g) → Bounded (Phi (f + g)) := by
      rintro f g ⟨T, hT⟩ ⟨S, hS⟩
      exact ⟨T + S, by rw [← g61c_add_eq hPhi f g ⟨S, hS⟩, hT, hS, g61c_add_bbg]⟩
    have hbmul : ∀ f g, Bounded (Phi f) → Bounded (Phi g) → Bounded (Phi (f * g)) := by
      rintro f g ⟨T, hT⟩ ⟨S, hS⟩
      exact ⟨T.comp S, by rw [← g61c_mul_eq hPhi f g ⟨S, hS⟩, hT, hS, g61c_mul_bbg]⟩
    have hb1 : Bounded (Phi 1) := ⟨ContinuousLinearMap.id ℂ X, hPhi.2.2.1⟩
    have hbsmul : ∀ (c : ℂ) f, Bounded (Phi f) → Bounded (Phi (c • f)) := by
      rintro c f ⟨T, hT⟩
      exact ⟨c • T, by rw [g61c_scale_eq hPhi c f (Or.inr ⟨T, hT⟩), hT, g61c_scale_bbg]⟩
    let B : Subalgebra ℂ F :=
      { carrier := boundedElements Phi
        mul_mem' := fun {a b} ha hb => hbmul a b ha hb
        add_mem' := fun {a b} ha hb => hbadd a b ha hb
        algebraMap_mem' := fun c => by
          show Bounded (Phi (algebraMap ℂ F c))
          rw [Algebra.algebraMap_eq_smul_one]; exact hbsmul c 1 hb1 }
    refine ⟨B, rfl, ?_⟩
    have hval : ∀ f : B, Phi (f : F) = banachBoundedGraph (boundedValue (Phi (f : F))) :=
      fun f => g61c_bv_spec f.2
    have hsc : ∀ c : ℂ, Phi (c • (1 : F)) = banachBoundedGraph (c • ContinuousLinearMap.id ℂ X) := by
      intro c
      rw [g61c_scale_eq hPhi c 1 (Or.inr hb1), hPhi.2.2.1, g61c_id_bbg, g61c_scale_bbg]
    let rho : B →ₐ[ℂ] (X →L[ℂ] X) :=
      { toFun := fun f => boundedValue (Phi (f : F))
        map_one' := g61c_bv_eq hPhi.2.2.1
        map_mul' := fun a b => by
          apply g61c_bv_eq
          show Phi ((a : F) * b) = _
          rw [← g61c_mul_eq hPhi _ _ b.2]
          conv_lhs => rw [hval a, hval b]
          exact g61c_mul_bbg _ _
        map_zero' := by
          apply g61c_bv_eq
          rw [show ((0 : B) : F) = (0 : ℂ) • (1 : F) by simp, hsc]
          simp
        map_add' := fun a b => by
          apply g61c_bv_eq
          show Phi ((a : F) + b) = _
          rw [← g61c_add_eq hPhi _ _ b.2]
          conv_lhs => rw [hval a, hval b]
          exact g61c_add_bbg _ _
        commutes' := fun c => by
          apply g61c_bv_eq
          rw [show ((algebraMap ℂ B c : B) : F) = c • (1 : F) by
            simp [Algebra.algebraMap_eq_smul_one], hsc, Algebra.algebraMap_eq_smul_one]
          rfl }
    exact ⟨rho, fun f => hval f⟩



end

