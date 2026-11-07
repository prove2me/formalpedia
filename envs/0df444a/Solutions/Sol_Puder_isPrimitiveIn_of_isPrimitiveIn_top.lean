-- Prove2me | solution 1 for Puder.isPrimitiveIn_of_isPrimitiveIn_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T09:43:55.814803+00:00
-- url     : https://prove2.me/submissions/b980c3cf-c49b-4864-b529-540b51dc094e

import Mathlib
import Definitions.Def_StrongConvPuder

noncomputable section
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver

namespace Puder.PartB

variable {ι : Type} {G : Type} [Group G]

theorem basis_lift_apply {H : Type} [Group H] (bG : FreeGroupBasis ι G) (f : ι → H) (i : ι) :
    bG.lift f (bG i) = f i := by
  simp

theorem ofUniqueLift_apply (X : Type) (of : X → G)
    (h : ∀ {H : Type} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) (x : X) :
    FreeGroupBasis.ofUniqueLift X of h x = of x := by
  show (FreeGroupBasis.ofUniqueLift X of h).repr.symm (FreeGroup.of x) = of x
  simp [FreeGroupBasis.ofUniqueLift, FreeGroupBasis.ofLift]

variable {A : Type} [MulAction G A]

set_option backward.isDefEq.respectTransparency.types false in
/-- The action groupoid of `G` on `A` is free on the arrows `(e, a)` with `bG e • a = c`. -/
@[instance_reducible]
def actionFree (bG : FreeGroupBasis ι G) : IsFreeGroupoid (ActionCategory G A) where
  quiverGenerators :=
    ⟨fun a b => { e : ι // bG e • a.back = b.back }⟩
  of := fun (e : Subtype _) => ⟨bG e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : ι → (A → X) ⋊[mulAutArrow] G := fun e =>
      ⟨fun b => @f ⟨(), _⟩ ⟨(), b⟩ ⟨e, smul_inv_smul _ b⟩, bG e⟩
    have hF' : ∀ e, bG.lift f' (bG e) = f' e := basis_lift_apply bG f'
    have uF' : ∀ F, (∀ e, F (bG e) = f' e) → F = bG.lift f' := fun F hF =>
      bG.ext_hom _ _ fun e => by rw [hF, hF']
    set F' := bG.lift f'
    refine ⟨uncurry F' ?_, ?_, ?_⟩
    · suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id _ by
        exact DFunLike.ext_iff.mp this
      refine bG.ext_hom _ _ (fun x ↦ ?_)
      rw [MonoidHom.comp_apply, hF']
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b⟩ ⟨e, h : bG e • a = b⟩
      change (F' (bG _)).left _ = _
      rw [hF']
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have : curry E = F' := by
        apply uF'
        intro e
        ext
        · convert! hE _ _ _
          rfl
        · rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intros
        simp only [← this, uncurry_map, curry_apply_left, coe_back, homOfPair.val]
        rfl

section Tree

open IsFreeGroupoid IsFreeGroupoid.SpanningTree

variable {V : Type} [Groupoid.{0} V] [IsFreeGroupoid V]
  (T : WideSubquiver (Symmetrify <| Generators V)) [Arborescence T]

/-- The root of `T`, as an object of `V`. -/
def root' : V :=
  show T from root T

/-- The generating arrows of `V` outside the (symmetrified) tree `T`. -/
abbrev OffTree : Type :=
  ((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _)

theorem treeHom_root' : treeHom T (root' T) = 𝟙 _ :=
  treeHom_root T

theorem loopOfHom_root (p : root' T ⟶ root' T) : loopOfHom T p = p := by
  have key : ∀ (q : root' T ⟶ root' T) [IsIso q], q = 𝟙 _ → q ≫ p ≫ inv q = p := by
    intro q _ hq
    subst hq
    simp
  exact @key (treeHom T (root' T)) (IsIso.of_groupoid _) (treeHom_root' T)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The vertex group at the root, with its explicit free basis of loops from the arrows
outside the tree (Mathlib's `endIsFree`, with data). -/
theorem endBasis_unique : ∀ {H : Type} [Group H] (f : OffTree T → H),
    ∃! F : End (root' T) →* H, ∀ e, F (loopOfHom T (of e.val.hom)) = f e :=
    (by
      intro X _ f
      let f' : Labelling (Generators V) X := fun a b e =>
        if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
      rcases unique_lift f' with ⟨F', hF', uF'⟩
      refine ⟨F'.mapEnd _, ?_, ?_⟩
      · suffices ∀ {x y} (q : x ⟶ y), F'.map (loopOfHom T q) = (F'.map q : X) by
          rintro ⟨⟨a, b, e⟩, h⟩
          simp only [Functor.mapEnd, DFunLike.coe, this, hF']
          exact dif_neg h
        intro x y q
        suffices ∀ {a} (p : Path (root T) a), F'.map (homOfPath T p) = 1 by
          simp only [this, treeHom, comp_as_mul, inv_as_inv, loopOfHom, inv_one, mul_one,
            one_mul, Functor.map_inv, Functor.map_comp]
        intro a p
        induction p with
        | nil => rw [homOfPath, F'.map_id, id_as_one]
        | cons p e ih =>
          rw [homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
          rcases e with ⟨e | e, eT⟩
          · rw [hF']
            exact dif_pos (Or.inl eT)
          · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
            exact dif_pos (Or.inr eT)
      · intro E hE
        ext x
        suffices (functorOfMonoidHom T E).map x = F'.map x by
          rw [functorOfMonoidHom_map, loopOfHom_root] at this
          exact this
        congr
        apply uF'
        intro a b e
        change E (loopOfHom T _) = dite _ _ _
        split_ifs with h
        · rw [loopOfHom_eq_id T e h, ← End.one_def, E.map_one]
        · exact hE ⟨⟨a, b, e⟩, h⟩)

def endBasis : FreeGroupBasis (OffTree T) (End (root' T)) :=
  FreeGroupBasis.ofUniqueLift (OffTree T)
    (fun e => loopOfHom T (of e.val.hom)) (endBasis_unique T)

theorem endBasis_apply (e : OffTree T) : endBasis T e = loopOfHom T (of e.val.hom) :=
  ofUniqueLift_apply _ _ (endBasis_unique T) e

/-- A loop at the root is never an arrow of the tree. -/
theorem loop_mem_offTree (e : @Quiver.Hom (Generators V) _ (root' (V := V) T) (root' (V := V) T)) :
    (⟨root' (V := V) T, root' (V := V) T, e⟩ : Total (Generators V)) ∈
      ((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _) := by
  rintro (H | H)
  · have := Subsingleton.elim (α := Path (root T) (root T)) Path.nil
      (Path.cons Path.nil ⟨Sum.inl e, H⟩)
    exact Path.nil_ne_cons _ _ this
  · have := Subsingleton.elim (α := Path (root T) (root T)) Path.nil
      (Path.cons Path.nil ⟨Sum.inr e, H⟩)
    exact Path.nil_ne_cons _ _ this

theorem endBasis_loop (e : @Quiver.Hom (Generators V) _ (root' (V := V) T) (root' (V := V) T)) :
    endBasis T ⟨⟨root' (V := V) T, root' (V := V) T, e⟩, loop_mem_offTree T e⟩ = of e := by
  rw [endBasis_apply]
  exact loopOfHom_root T _

end Tree

open IsFreeGroupoid in
theorem isPrimitiveIn_of_isPrimitiveIn_top {d : ℕ} {w : FreeGroup (Fin d)}
    (hw : IsPrimitiveIn ⊤ w) (J : Subgroup (FreeGroup (Fin d))) (hJ : w ∈ J) :
    IsPrimitiveIn J w := by
  obtain ⟨ι, b, i, hi⟩ := hw
  let b' : FreeGroupBasis ι (FreeGroup (Fin d)) := b.map Subgroup.topEquiv
  have hb' : b' i = w := hi
  let inst : IsFreeGroupoid (ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)) := actionFree b'
  let r : ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J) := objEquiv (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J) ↑(1 : FreeGroup (Fin d))
  have hc : IsConnected (ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)) :=
    inferInstance
  have : RootedConnected (V := Symmetrify (Generators (ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)))) r :=
    ⟨fun c => path_nonempty_of_hom
      (@nonempty_hom_of_preconnected_groupoid _ _ (by exact hc.toIsPreconnected) r c)⟩
  let T := geodesicSubtree (V := Symmetrify (Generators (ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)))) r
  let _ : Arborescence T := geodesicArborescence _
  have hfix : b' i • (r : ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)).back = r.back := by
    rw [hb']
    change w • ((1 : FreeGroup (Fin d)) : FreeGroup (Fin d) ⧸ J) = ((1 : FreeGroup (Fin d)) : FreeGroup (Fin d) ⧸ J)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simpa using J.inv_mem hJ
  let e0 : @Quiver.Hom (Generators (ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J))) _ (root' (V := ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)) T)
      (root' (V := ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)) T) := ⟨i, hfix⟩
  refine ⟨OffTree T, (endBasis T).map (endMulEquivSubgroup J),
    ⟨⟨_, _, e0⟩, loop_mem_offTree T e0⟩, ?_⟩
  have key : ∀ y : End (root' (V := ActionCategory (FreeGroup (Fin d)) (FreeGroup (Fin d) ⧸ J)) T),
      y = @IsFreeGroupoid.of _ _ inst _ _ e0 → ((endMulEquivSubgroup J y : J) : FreeGroup (Fin d)) = w := by
    rintro y rfl
    exact hb'
  exact key _ (endBasis_loop T e0)

end Puder.PartB

theorem solution {d : ℕ} {w : FreeGroup (Fin d)} (hw : Puder.IsPrimitiveIn ⊤ w)
    (J : Subgroup (FreeGroup (Fin d))) (hJ : w ∈ J) : Puder.IsPrimitiveIn J w :=
  Puder.PartB.isPrimitiveIn_of_isPrimitiveIn_top hw J hJ
