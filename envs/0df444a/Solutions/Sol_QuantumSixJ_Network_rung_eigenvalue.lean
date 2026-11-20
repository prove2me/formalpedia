-- Prove2me | solution 1 for QuantumSixJ.Network.rung_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T11:44:06.2296+00:00
-- url     : https://prove2.me/submissions/bdafe90a-33fa-4b93-8ad4-b9da7205e8ea

import Definitions.Def_QuantumSixJNetwork
import Theorems.Thm_QuantumSixJ_scalar_foundations
import Theorems.Thm_QuantumSixJ_tet_two_evaluations
import Theorems.Thm_QuantumSixJ_Network_diagram_calculus

open CategoryTheory MonoidalCategory
universe v u
noncomputable section
open QuantumSixJ
open scoped BigOperators QuantumSixJ Classical

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

namespace QuantumSixJ.Network

set_option maxRecDepth 8192

set_option maxRecDepth 8192

/-- Splitting a strand by an otherwise arbitrary covector. -/
private def rungSplit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (S : SuQ2Data C) {a b l : ℕ}
    (f : S.V b ⊗ S.V a ⊗ S.V l ⟶ 𝟙_ C) : S.V l ⟶ S.V a ⊗ S.V b :=
  𝟙 _ ⊗≫ (S.cup a ▷ S.V l) ⊗≫
    (S.V a ◁ ((S.cup b ▷ S.V a) ▷ S.V l)) ⊗≫
    (S.V a ◁ S.V b ◁ f) ⊗≫ 𝟙 _

/-- Fusing two strands by an otherwise arbitrary covector. -/
private def rungFuse {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (S : SuQ2Data C) {a b l : ℕ}
    (f : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) : S.V a ⊗ S.V b ⟶ S.V l :=
  𝟙 _ ⊗≫ ((S.V a ⊗ S.V b) ◁ S.cup l) ⊗≫ (f ▷ S.V l) ⊗≫ 𝟙 _

private lemma rungFuse_mate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    rungFuse S f =
      (tensorRightHomEquiv
        (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C))
        ((α_ (S.V a) (S.V b) (S.V l)).hom ≫ f) ≫
          (λ_ (S.V l)).hom := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [rungFuse, tensorRightHomEquiv, monoidalComp,
    SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
    ExactPairing.evaluation]

private lemma rungFuse_cap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (g : S.V a ⊗ S.V b ⊗ S.V l ⟶ 𝟙_ C) :
    (rungFuse S g ▷ S.V l) ≫ S.cap l =
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ g := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv
    (S.V a ⊗ S.V b) (S.V l) (S.V l) (𝟙_ C)
  rw [rungFuse_mate]
  simpa [e, tensorRightHomEquiv, monoidalComp, SuQ2Data.cup,
    SuQ2Data.cap, ExactPairing.coevaluation, ExactPairing.evaluation,
    ← unitors_equal] using
    e.left_inv ((α_ (S.V a) (S.V b) (S.V l)).hom ≫ g)

/-- A rotation converts the right mate defining `rungFuse` to a left mate. -/
private lemma rungRotate_mate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorRightHomEquiv
      (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C))
      ((α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f) =
      (((tensorLeftHomEquiv
        (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)) f ≫
          (ρ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eL := tensorLeftHomEquiv
    (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)
  let eR := tensorRightHomEquiv
    (S.V b ⊗ S.V a) (S.V l) (S.V l) (𝟙_ C)
  let q : S.V b ⊗ S.V a ⟶ 𝟙_ C ⊗ S.V l :=
    (eL f ≫ (ρ_ (S.V l)).hom) ≫ (λ_ (S.V l)).inv
  have hrotate :
      (α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f =
        eR.symm q := by
    dsimp [eR, eL, q, tensorRightHomEquiv, tensorLeftHomEquiv]
    simp only [Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation]
    monoidal
  change eR ((α_ (S.V b) (S.V a) (S.V l)).hom ≫ Vertex.rotate f) = q
  calc
    _ = eR (eR.symm q) := by rw [hrotate]
    _ = q := eR.right_inv q

private lemma rungFuse_rotate {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b : ℕ)
    (f : S.V a ⊗ S.V b ⊗ S.V b ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    rungFuse S (Vertex.rotate f) =
      (tensorLeftHomEquiv
        (S.V b ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)) f ≫
          (ρ_ (S.V a)).hom := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [rungFuse_mate, rungRotate_mate]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The single left mate can instead be obtained by one cup, a fuse, and one
cap. This is the small sliding step used in the rung calculation. -/
private lemma rungFuse_mate_swap {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b : ℕ)
    (g : S.V a ⊗ S.V b ⊗ S.V b ⟶ 𝟙_ C) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorLeftHomEquiv
      (S.V b ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)) g ≫ (ρ_ (S.V a)).hom =
      𝟙 _ ⊗≫ (S.cup a ▷ (S.V b ⊗ S.V b)) ⊗≫
        (S.V a ◁ (rungFuse S g ▷ S.V b)) ⊗≫
          (S.V a ◁ S.cap b) ⊗≫ 𝟙 _ := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp only [monoidalComp]
  simp
  slice_rhs 6 7 =>
    rw [← MonoidalCategory.whiskerLeft_comp, rungFuse_cap]
  dsimp [tensorLeftHomEquiv]
  monoidal

/-- Closing the two output strands of an abstract split gives the second
rotation of its covector. -/
private lemma rungRotate2_split {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a t : ℕ)
    (f : S.V t ⊗ S.V a ⊗ S.V a ⟶ 𝟙_ C) :
    Vertex.rotate (Vertex.rotate f) =
      (rungSplit S f ▷ (S.V t ⊗ S.V a)) ≫
        (α_ (S.V a) (S.V t) (S.V t ⊗ S.V a)).hom ≫
          S.V a ◁ (α_ (S.V t) (S.V t) (S.V a)).inv ≫
            S.V a ◁ (S.cap t ▷ S.V a) ≫
              S.V a ◁ (λ_ (S.V a)).hom ≫ S.cap a := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [rungSplit, Vertex.rotate, monoidalComp,
    SuQ2Data.cup, SuQ2Data.cap, ExactPairing.coevaluation,
    ExactPairing.evaluation]
  monoidal

/-- A redundant cup/cap loop may be slid through two disjoint operators. -/
private lemma rungSnake_core {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A T X : C) [ExactPairing T T]
    (p : A ⟶ A ⊗ T) (k : T ⊗ X ⟶ 𝟙_ C) :
    (𝟙 (A ⊗ X) ⊗≫ (p ▷ X) ⊗≫ (A ◁ k) ⊗≫ (ρ_ A).hom) =
      (𝟙 (A ⊗ X) ⊗≫ (A ◁ (ExactPairing.coevaluation' : 𝟙_ C ⟶ T ⊗ T) ▷ X) ⊗≫
        ((A ⊗ T) ◁ k) ⊗≫ (p ▷ T) ⊗≫
          (A ◁ (ExactPairing.evaluation' : T ⊗ T ⟶ 𝟙_ C)) ⊗≫
            (ρ_ A).hom) := by
  let e := tensorLeftHomEquiv X T T (𝟙_ C)
  have h := congrArg
    (fun k' : T ⊗ X ⟶ 𝟙_ C =>
      (𝟙 (A ⊗ X) ⊗≫ (p ▷ X) ⊗≫ (A ◁ k') ⊗≫ (ρ_ A).hom))
    (e.left_inv k)
  refine h.symm.trans ?_
  let q : X ⟶ T := e k ≫ (ρ_ T).hom
  have hx := MonoidalCategory.whisker_exchange p q
  have hx' := congrArg
    (fun z : A ⊗ X ⟶ (A ⊗ T) ⊗ T =>
      z ≫ (α_ A T T).hom ≫
        (A ◁ (ExactPairing.evaluation' : T ⊗ T ⟶ 𝟙_ C)) ≫ (ρ_ A).hom)
    hx.symm
  simp [q, e, tensorLeftHomEquiv, monoidalComp] at hx' ⊢
  convert hx' using 1 <;> monoidal

/-- General rung/cap slide. The two input covectors are arbitrary; no
cyclicity or normalization is needed for the diagram deformation itself. -/
lemma agent_rung_slide {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (a b t : ℕ)
    (f : S.V t ⊗ S.V a ⊗ S.V a ⟶ 𝟙_ C)
    (g : S.V t ⊗ S.V b ⊗ S.V b ⟶ 𝟙_ C) :
    ((((rungSplit S f ▷ S.V b) ⊗≫
        (S.V a ◁ rungFuse S g)) ▷ (S.V b ⊗ S.V a)) ⊗≫
      (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
        (α_ (S.V a) (S.V b) (S.V b ⊗ S.V a)).hom ≫
          (𝟙 _ ⊗≫ (S.V a ◁ (rungFuse S (Vertex.rotate g) ▷ S.V a)) ⊗≫
            Vertex.rotate (Vertex.rotate f)) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  rw [rungFuse_rotate, rungFuse_mate_swap, rungRotate2_split]
  simp [monoidalComp]
  slice_lhs 6 7 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, rungFuse_cap]
  slice_rhs 10 11 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← comp_whiskerRight, rungFuse_cap]
  generalize rungSplit S f = p
  have h := rungSnake_core (S.V a) (S.V t) (S.V b ⊗ S.V b) p g
  have h' := congrArg
    (fun z : S.V a ⊗ (S.V b ⊗ S.V b) ⟶ S.V a =>
      (α_ (S.V a ⊗ S.V b) (S.V b) (S.V a)).inv ≫
        ((α_ (S.V a) (S.V b) (S.V b)).hom ▷ S.V a) ≫
          (z ▷ S.V a) ≫ S.cap a) h
  simp [monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
    ExactPairing.coevaluation, ExactPairing.evaluation] at h' ⊢
  convert h' using 1 <;> monoidal

private lemma author_rung_identity {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W) (a b : ℕ) :
    ((((W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b)) ▷
        (S.V b ⊗ S.V a)) ⊗≫
      (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
        (α_ (S.V a) (S.V b) (S.V b ⊗ S.V a)).hom ≫ W.Hcov a b b a 2 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have h := agent_rung_slide S a b 2 (W.vertex 2 a a) (W.vertex 2 b b)
  rw [hW.cyclic 2 a a, hW.cyclic a a 2, hW.cyclic 2 b b] at h
  simpa only [rungSplit, rungFuse, Vertex.split, Vertex.fuse, Vertex.Hcov] using h

set_option maxRecDepth 8192

/-- The two nested caps close `split l b a` back to its defining vertex. -/
private lemma close_split_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ) :
    ((S.V a ⊗ S.V b) ◁ W.split l b a) ≫
      (((𝟙 (S.V a ⊗ S.V b)) ▷ (S.V b ⊗ S.V a)) ⊗≫
        (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
      (𝟙 (S.V a ⊗ S.V b)) ▷ S.V l ≫
        (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eB := tensorLeftHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let eA := tensorLeftHomEquiv (S.V b ⊗ S.V l) (S.V a) (S.V a) (𝟙_ C)
  let u : S.V b ⊗ S.V l ⟶ S.V a := eA (W.vertex a b l) ≫ (ρ_ (S.V a)).hom
  have hsplit : W.split l b a = eB u := by
    dsimp [eB, eA, u, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hB : S.V b ◁ W.split l b a ≫
      (α_ (S.V b) (S.V b) (S.V a)).inv ≫
        S.cap b ▷ S.V a ≫ (λ_ (S.V a)).hom = u := by
    rw [hsplit]
    simpa [eB, tensorLeftHomEquiv, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal] using
      eB.left_inv u
  have hunit : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
    rw [unitors_equal]
    simp
  have hA : S.V a ◁ u ≫ S.cap a = W.vertex a b l := by
    simpa [u, eA, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, ← unitors_equal, hunit] using
      eA.left_inv (W.vertex a b l)
  have hB' : S.V a ◁ S.V b ◁ W.split l b a ≫
      S.V a ◁ (α_ (S.V b) (S.V b) (S.V a)).inv ≫
        S.V a ◁ S.cap b ▷ S.V a ≫ S.V a ◁ (λ_ (S.V a)).hom ≫ S.cap a =
      S.V a ◁ u ≫ S.cap a := by
    simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using
      congrArg (fun t : S.V b ⊗ S.V l ⟶ S.V a => S.V a ◁ t ≫ S.cap a) hB
  simp [monoidalComp]
  rw [hB', hA]

/-- Tensor interchange inserts an arbitrary operator before the same two-cap
mate cancellation. -/
private lemma attach_split_aux {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (a b l : ℕ)
    (k : S.V a ⊗ S.V b ⟶ S.V a ⊗ S.V b) :
    ((S.V a ⊗ S.V b) ◁ W.split l b a) ≫
      ((k ▷ (S.V b ⊗ S.V a)) ⊗≫
        (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
      k ▷ S.V l ≫ (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have h := congrArg (fun t : (S.V a ⊗ S.V b) ⊗ S.V l ⟶ 𝟙_ C =>
    k ▷ S.V l ≫ t) (close_split_aux S W a b l)
  simpa only [monoidalComp, Category.assoc, MonoidalCategory.whisker_exchange,
    MonoidalCategory.whisker_exchange_assoc, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.comp_id] using h

/-- Attach the two left split boxes to the cap/rung deformation. -/
private lemma author_attach_identity {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W) (a b l : ℕ)
    (hcup : ∀ x y m : ℕ, S.cup m ≫ (W.split m x y ▷ S.V m) =
      W.vertexUp x y m ≫ (α_ (S.V x) (S.V y) (S.V m)).inv)
    (hr : ((((W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b)) ▷
        (S.V b ⊗ S.V a)) ⊗≫
      (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a) =
        (α_ (S.V a) (S.V b) (S.V b ⊗ S.V a)).hom ≫ W.Hcov a b b a 2) :
    W.tet a a b b l 2 =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫
        (((W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b)) ▷ S.V l) ≫
          (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  simp [Vertex.tet, Vertex.X, monoidalComp]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← hr]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l), hcup]
  simp only [Category.assoc]
  congr 1
  congr 1
  simpa [monoidalComp, Category.assoc] using
    (attach_split_aux S W a b l
      ((W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b)))

private lemma lower_rotate_mates_of_rotate3 {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear K C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (a b l : ℕ)
    (f : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C)
    (h3 : Vertex.rotate (Vertex.rotate (Vertex.rotate f)) = f) :
    letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
    (tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b))
      ((tensorLeftHomEquiv
        (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C))
        (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
    (tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a))
      ((tensorRightHomEquiv
        (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C))
        ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
          (λ_ (S.V a)).hom) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let eLb := tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eLa := tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b)
  let eRa := tensorRightHomEquiv (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let close (h : S.V l ⟶ S.V a ⊗ S.V b) : S.V l ⊗ S.V b ⊗ S.V a ⟶ 𝟙_ C :=
    (α_ (S.V l) (S.V b) (S.V a)).inv ≫
      eRa.symm (eRb.symm h ≫ (λ_ (S.V a)).inv)
  have close_injective : Function.Injective close := by
    intro x y hxy
    apply eRb.symm.injective
    rw [← cancel_mono (λ_ (S.V a)).inv]
    apply eRa.symm.injective
    rw [← cancel_epi (α_ (S.V l) (S.V b) (S.V a)).inv]
    exact hxy
  have close_right :
      close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
        (λ_ (S.V a)).hom)) = f := by
    simp only [close, Equiv.symm_apply_apply, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have close_left_rotate3 :
      close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := by
    simp [close, eLa, eLb, eRa, eRb, tensorLeftHomEquiv, tensorRightHomEquiv,
      Vertex.rotate, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, monoidalComp]
    monoidal
  change eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom) =
    eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫ (λ_ (S.V a)).hom)
  apply close_injective
  calc
    close (eLa (eLb (Vertex.rotate f) ≫ (ρ_ (S.V b)).hom)) =
        Vertex.rotate (Vertex.rotate (Vertex.rotate f)) := close_left_rotate3
    _ = f := h3
    _ = close (eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ f) ≫
      (λ_ (S.V a)).hom)) := close_right.symm

private lemma lower_cup_split {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalLinear K C] (S : SuQ2Data C) (W : Vertex S)
    (hW : VertexNormalized W) (a b l : ℕ) :
    S.cup l ≫ (W.split l a b ▷ S.V l) =
      W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  let e := tensorRightHomEquiv (𝟙_ C) (S.V l) (S.V l) (S.V a ⊗ S.V b)
  let eLa := tensorLeftHomEquiv (S.V l) (S.V a) (S.V a) (S.V b)
  let eLb := tensorLeftHomEquiv (S.V a ⊗ S.V l) (S.V b) (S.V b) (𝟙_ C)
  let eRa := tensorRightHomEquiv (S.V l ⊗ S.V b) (S.V a) (S.V a) (𝟙_ C)
  let eRb := tensorRightHomEquiv (S.V l) (S.V b) (S.V b) (S.V a)
  let r : S.V l ⟶ S.V a ⊗ S.V b :=
    eRb (eRa ((α_ (S.V l) (S.V b) (S.V a)).hom ≫ W.vertex l b a) ≫
      (λ_ (S.V a)).hom)
  have hsplit : W.split l a b = eLa (eLb (W.vertex b a l) ≫ (ρ_ (S.V b)).hom) := by
    dsimp [eLa, eLb, tensorLeftHomEquiv]
    simp only [Vertex.split, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hup : W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv =
      e ((λ_ (S.V l)).hom ≫ r) := by
    dsimp [e, r, eRa, eRb, tensorRightHomEquiv]
    simp only [Vertex.vertexUp, SuQ2Data.cup, ExactPairing.coevaluation]
    monoidal
  have hrot3 : Vertex.rotate (Vertex.rotate (Vertex.rotate (W.vertex l b a))) =
      W.vertex l b a := by
    rw [hW.cyclic l b a, hW.cyclic b a l, hW.cyclic a l b]
  have hm : W.split l a b = r := by
    rw [hsplit, ← hW.cyclic l b a]
    exact lower_rotate_mates_of_rotate3 S a b l (W.vertex l b a) hrot3
  calc
    S.cup l ≫ (W.split l a b ▷ S.V l) = e ((λ_ (S.V l)).hom ≫ W.split l a b) := by
      simp [e, tensorRightHomEquiv, SuQ2Data.cup,
        ExactPairing.coevaluation, comp_whiskerRight, unitors_equal]
    _ = e ((λ_ (S.V l)).hom ≫ r) := by rw [hm]
    _ = W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv := hup.symm



/-! The author's five diagrams in their supplied order; scalar factors omitted.
Composition is left to right; tensor factors are top to bottom.
The cut morphisms have boundary (a,b,b,a). Their common left attachment is
the l-cup followed by split l a b and split l b a.
-/

namespace AuthorDeformation

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
  (S : SuQ2Data C) (W : Vertex S)

/-- The rung without the scalar factor in K2. -/
noncomputable def rung (a b : ℕ) : S.V a ⊗ S.V b ⟶ S.V a ⊗ S.V b :=
  (W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b)

/-- Two nested caps, closing b first, then a. -/
noncomputable def caps (a b : ℕ) :
    (S.V a ⊗ S.V b) ⊗ (S.V b ⊗ S.V a) ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a

/-- Local part of D1: rung followed by the nested caps. -/
noncomputable def cut1 (a b : ℕ) :
    (S.V a ⊗ S.V b) ⊗ (S.V b ⊗ S.V a) ⟶ 𝟙_ C :=
  (rung S W a b ▷ (S.V b ⊗ S.V a)) ⊗≫
    (S.V a ◁ (S.cap b ▷ S.V a)) ⊗≫ S.cap a

/-- Local part of D2: pull the b-cap onto fuse 2 b b, leaving vertex 2 b b.
```
 a --[split a a 2]-- a ---------------------------------.
            |                                          |
            2 --.                                      |
                |                                      |
 b -------------[vertex 2 b b]                          |
 b -------------[            ]                          |
 a ----------------------------------------------------'
```
-/
noncomputable def cut2 (a b : ℕ) :
    (S.V a ⊗ S.V b) ⊗ (S.V b ⊗ S.V a) ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ ((W.split a a 2 ▷ S.V b) ▷ (S.V b ⊗ S.V a)) ⊗≫
    (S.V a ◁ (W.vertex 2 b b ▷ S.V a)) ⊗≫ S.cap a

/-- Local part of D3: rotate to fuse b b 2 and retain the 2-cap and a-cap.
```
 a --[split a a 2]-- a ---------------------------------.
            |                                          |
            2 ---------------------------------.       |
                                               |       |
 b ----------------[fuse b b 2]-- 2 ------------'       |
 b ----------------[          ]                         |
 a ----------------------------------------------------'
```
-/
noncomputable def cut3 (a b : ℕ) :
    (S.V a ⊗ S.V b) ⊗ (S.V b ⊗ S.V a) ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ ((W.split a a 2 ▷ S.V b) ▷ (S.V b ⊗ S.V a)) ⊗≫
    (S.V a ◁ (S.V 2 ◁ (W.fuse b b 2 ▷ S.V a))) ⊗≫
    (S.V a ◁ (S.cap 2 ▷ S.V a)) ⊗≫ S.cap a

/-- Attach the two left splits and their l-cup. -/
noncomputable def close (a b l : ℕ)
    (f : (S.V a ⊗ S.V b) ⊗ (S.V b ⊗ S.V a) ⟶ 𝟙_ C) : 𝟙_ C ⟶ 𝟙_ C :=
  S.cup l ≫ (W.split l a b ⊗ₘ W.split l b a) ≫ f

/-- D0: vertexUp, rung on a,b, identity on l, closing vertex. -/
noncomputable def D0 (a b l : ℕ) : 𝟙_ C ⟶ 𝟙_ C :=
  W.vertexUp a b l ≫ (α_ (S.V a) (S.V b) (S.V l)).inv ≫
    (rung S W a b ▷ S.V l) ≫
      (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l

/-- D1: two split states, rung, nested b- and a-caps. -/
noncomputable def D1 (a b l : ℕ) : 𝟙_ C ⟶ 𝟙_ C := close S W a b l (cut1 S W a b)

/-- D2: pull the b-cap onto the lower rung box. -/
noncomputable def D2 (a b l : ℕ) : 𝟙_ C ⟶ 𝟙_ C := close S W a b l (cut2 S W a b)

/-- D3: fuse b,b and cap the two 2 strands explicitly. -/
noncomputable def D3 (a b l : ℕ) : 𝟙_ C ⟶ 𝟙_ C := close S W a b l (cut3 S W a b)

/-- D4: the author's final diagram, with no change of Tet orientation.
```
          +-----------+                                  +-----------+
          |           |---------------- a ---------------|           |
 .--- l --| split     |                                  |           |
 |        | l a b     |-- b --+-----------+               |           |
 |        +-----------+       | fuse      |--- 2 ---------| vertex    |
 |        +-----------+       | b b 2     |               | a 2 a     |
 |        | l b a     |-- b --+-----------+               |           |
 `--- l --| split     |                                  |           |
          |           |---------------- a ---------------|           |
          +-----------+                                  +-----------+
```
-/
noncomputable def D4 (a b l : ℕ) : 𝟙_ C ⟶ 𝟙_ C :=
  S.cup l ≫ (W.split l a b ⊗ₘ W.split l b a) ≫
    (α_ (S.V a) (S.V b) (S.V b ⊗ S.V a)).hom ≫ W.Hcov a b b a 2

lemma D0_eq_D1 (hW : VertexNormalized W) (a b l : ℕ) :
    D0 S W a b l = D1 S W a b l := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  dsimp [D0, D1, close, cut1, caps]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l),
    lower_cup_split S W hW a b l]
  simp only [Category.assoc]
  congr 1
  congr 1
  simpa [monoidalComp, Category.assoc] using
    (attach_split_aux S W a b l (rung S W a b)).symm

lemma cut1_eq_cut2 (a b : ℕ) : cut1 S W a b = cut2 S W a b := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hf := rungFuse_cap S 2 b b (W.vertex 2 b b)
  change (W.fuse 2 b b ▷ S.V b) ≫ S.cap b =
    (α_ (S.V 2) (S.V b) (S.V b)).hom ≫ W.vertex 2 b b at hf
  have h := congrArg
    (fun f : (S.V 2 ⊗ S.V b) ⊗ S.V b ⟶ 𝟙_ C =>
      𝟙 ((S.V a ⊗ S.V b) ⊗ (S.V b ⊗ S.V a)) ⊗≫
        ((W.split a a 2 ▷ S.V b) ▷ (S.V b ⊗ S.V a)) ⊗≫
          (S.V a ◁ (f ▷ S.V a)) ⊗≫ S.cap a) hf
  simp [cut1, cut2, rung, monoidalComp] at h ⊢
  convert h using 1 <;> monoidal

lemma D1_eq_D2 (a b l : ℕ) : D1 S W a b l = D2 S W a b l := by
  unfold D1 D2
  rw [cut1_eq_cut2]

lemma cut2_eq_cut3 (hW : VertexNormalized W) (a b : ℕ) :
    cut2 S W a b = cut3 S W a b := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hr := rungFuse_rotate S 2 b (W.vertex 2 b b)
  rw [hW.cyclic 2 b b] at hr
  change W.fuse b b 2 =
    (tensorLeftHomEquiv (S.V b ⊗ S.V b) (S.V 2) (S.V 2) (𝟙_ C))
      (W.vertex 2 b b) ≫ (ρ_ (S.V 2)).hom at hr
  have hv : (𝟙 _ ⊗≫ (S.V 2 ◁ W.fuse b b 2) ⊗≫ S.cap 2) =
      W.vertex 2 b b := by
    rw [hr]
    let e := tensorLeftHomEquiv (S.V b ⊗ S.V b) (S.V 2) (S.V 2) (𝟙_ C)
    have hu : (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
      rw [unitors_equal]
      simp
    simpa [e, tensorLeftHomEquiv, monoidalComp, SuQ2Data.cup, SuQ2Data.cap,
      ExactPairing.coevaluation, ExactPairing.evaluation, hu] using
      e.left_inv (W.vertex 2 b b)
  simp [cut2, cut3, monoidalComp]
  rw [← hv]
  simp [monoidalComp]
  all_goals monoidal

lemma D2_eq_D3 (hW : VertexNormalized W) (a b l : ℕ) :
    D2 S W a b l = D3 S W a b l := by
  unfold D2 D3
  rw [cut2_eq_cut3 S W hW]

lemma D3_eq_D4 (hW : VertexNormalized W) (a b l : ℕ) :
    D3 S W a b l = D4 S W a b l := by
  have hr := author_rung_identity S W hW a b
  change cut1 S W a b =
    (α_ (S.V a) (S.V b) (S.V b ⊗ S.V a)).hom ≫ W.Hcov a b b a 2 at hr
  have hlocal := (cut1_eq_cut2 S W a b).trans (cut2_eq_cut3 S W hW a b)
  unfold D3 close D4
  rw [← hlocal, hr]

/-- Identifies the endpoint by definition, without Tet symmetry or evaluation. -/
lemma D4_eq_tet (a b l : ℕ) : D4 S W a b l = W.tet a a b b l 2 := by
  simp [D4, Vertex.tet, Vertex.X, monoidalComp]

/-- Complete author-supplied deformation, without scalar evaluations. -/
theorem upper_deformation (hW : VertexNormalized W) (a b l : ℕ) :
    D0 S W a b l = W.tet a a b b l 2 := by
  calc
    D0 S W a b l = D1 S W a b l := D0_eq_D1 S W hW a b l
    _ = D2 S W a b l := D1_eq_D2 S W a b l
    _ = D3 S W a b l := D2_eq_D3 S W hW a b l
    _ = D4 S W a b l := D3_eq_D4 S W hW a b l
    _ = W.tet a a b b l 2 := D4_eq_tet S W a b l

/-- The same deformation from the original closed upper bubble, with K2's
scalar prefactor restored. No numerical Tet evaluation is assumed. -/
theorem closed_upper_deformation (hW : VertexNormalized W) (a b l : ℕ) :
    S.cup l ≫ ((W.split l a b ≫ W.K2 a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) • W.tet a a b b l 2 := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hf := rungFuse_cap S a b l (W.vertex a b l)
  change (W.fuse a b l ▷ S.V l) ≫ S.cap l =
    (α_ (S.V a) (S.V b) (S.V l)).hom ≫ W.vertex a b l at hf
  have hnat : S.cup l ≫
      ((W.split l a b ≫ rung S W a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
        W.tet a a b b l 2 := by
    rw [← upper_deformation S W hW a b l]
    rw [comp_whiskerRight, comp_whiskerRight]
    simp only [Category.assoc]
    rw [← Category.assoc (S.cup l) (W.split l a b ▷ S.V l),
      lower_cup_split S W hW a b l]
    simp only [Category.assoc]
    rw [hf]
    rfl
  have h := congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C =>
    ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) • f) hnat
  simpa [Vertex.K2, rung, monoidalComp, Category.assoc, smul_smul] using h

end
end AuthorDeformation

end QuantumSixJ.Network

namespace QuantumSixJ.Network
private lemma iota_delta_ne_zero_aux (l : ℕ) : ι (Δ (l : ℤ)) ≠ 0 := by
  apply (map_ne_zero_iff _ _).2 (delta_ne_zero l (by omega))
  unfold ι
  apply RatFunc.map_injective
  · exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  · exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective

private lemma unit_scalar_injective_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) :
    Function.Injective (fun r : K => r • 𝟙 (𝟙_ C)) := by
  intro r s hrs
  have hrs0 : r • 𝟙 (S.V 0) = s • 𝟙 (S.V 0) := by
    have h := congrArg (fun f : 𝟙_ C ⟶ 𝟙_ C => S.unitIso.hom ≫ f ≫ S.unitIso.inv) hrs
    simpa [smul_smul] using h
  have hd : (0 : S.V 0 ⟶ S.V 0) = (r - s) • 𝟙 (S.V 0) := by
    rw [sub_smul, hrs0, sub_self]
  have hz : (0 : S.V 0 ⟶ S.V 0) = (0 : K) • 𝟙 (S.V 0) := by simp
  exact sub_eq_zero.mp ((hS.simple 0 0).unique hd hz)

/-- Simplicity recovers an endomorphism of `V l` from its scalar closure. -/
private lemma endo_from_closed_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear K C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (hS : SuQ2Axioms S) (l : ℕ) (f : S.V l ⟶ S.V l) (u : K)
    (hclosed : S.cup l ≫ (f ▷ S.V l) ≫ S.cap l = u • 𝟙 (𝟙_ C)) :
    f = (u / ι (Δ (l : ℤ))) • 𝟙 (S.V l) := by
  letI (n : ℕ) : ExactPairing (S.V n) (S.V n) := S.pairing n
  have hunit := unit_scalar_injective_aux S hS
  obtain ⟨s, hs, _⟩ := hS.simple l f
  have hclosed' : S.cup l ≫ (f ▷ S.V l) ≫ S.cap l =
      (s * ι (Δ (l : ℤ))) • 𝟙 (𝟙_ C) := by
    rw [hs]
    simp [hS.loop, smul_smul]
  have hscalar : s * ι (Δ (l : ℤ)) = u := by
    apply hunit
    exact hclosed'.symm.trans hclosed
  have hΔ := iota_delta_ne_zero_aux l
  have hsval : s = u / ι (Δ (l : ℤ)) := (eq_div_iff hΔ).2 hscalar
  rw [← hsval]
  exact hs
private lemma qzero_aux : ⟬(0 : ℤ)⟭ = 0 := by simp [qInt]

private lemma lambda_zero_left_aux (b l : ℤ) (h : Admissible 0 b l) : Λ 0 b l = 0 := by
  rw [Λ, if_pos h]
  have hbl : b = l := by rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩; omega
  rw [show (0 + b - l) / 2 = 0 by rw [hbl]; simp]
  simp only [zero_add, zero_sub, neg_zero, add_zero, sub_zero]
  rw [show (-b + l) / 2 = 0 by rw [hbl]; simp]
  rw [qzero_aux]
  ring

private lemma lambda_zero_right_aux (a l : ℤ) (h : Admissible a 0 l) : Λ a 0 l = 0 := by
  rw [Λ, if_pos h]
  have hal : a = l := by rcases h with ⟨ha, hb, hc, h1, h2, h3, hp⟩; omega
  rw [show (-a + 0 + l) / 2 = 0 by rw [hal]; simp]
  simp only [zero_add, zero_sub, neg_zero, add_zero, sub_zero]
  rw [show (a - l) / 2 = 0 by rw [hal]; simp]
  rw [qzero_aux]
  ring

section RungEigenvalue
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]

private lemma iota_theta_ne_zero (a b l : ℕ) (hab : Admissible (a : ℤ) b l) :
    ι (θ (a : ℤ) b l) ≠ 0 := by
  apply (map_ne_zero_iff _ _).2 (theta_ne_zero a b l hab)
  unfold ι
  apply RatFunc.map_injective
  · exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  · exact Polynomial.map_injective _ (algebraMap ℚ ℂ).injective

private lemma split_zero (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (a b l : ℕ) (hab : ¬ Admissible (a : ℤ) b l) :
    W.split l a b = 0 := by
  have hbad : ¬ Admissible (b : ℤ) a l := by
    intro h; apply hab; dsimp [Admissible] at *; omega
  have hz := (diagram_calculus S W hS hW).2.1 b a l hbad
  simp [Vertex.split, hz, monoidalComp]

private lemma closed_scalar (S : SuQ2Data C) (W : Vertex S) (hW : VertexNormalized W)
    (hSeed : TetSeed W) (a b l : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Admissible (a : ℤ) b l) :
    S.cup l ≫ ((W.split l a b ≫ W.K2 a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
      ι (θ (a : ℤ) b l * Λ (a : ℤ) b l) • 𝟙 (𝟙_ C) := by
  rw [AuthorDeformation.closed_upper_deformation S W hW, hSeed.tet_two]
  simp only [smul_smul]
  congr 1
  rw [← map_mul]
  exact congrArg ι (QuantumSixJ.tet_two_evaluations.2.2.1 a b l
    (by exact_mod_cast ha) (by exact_mod_cast hb) hab)

lemma split_eigenvalue (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (hSeed : TetSeed W) (a b l : ℕ) :
    W.split l a b ≫ W.K2 a b = ι (Λ a b l) • W.split l a b := by
  by_cases hab : Admissible (a : ℤ) b l
  swap
  · rw [split_zero S W hS hW a b l hab]; simp
  by_cases ha : a = 0
  · subst a
    simp [Vertex.K2, qzero_aux, lambda_zero_left_aux b l hab, monoidalComp]
  by_cases hb : b = 0
  · subst b
    simp [Vertex.K2, qzero_aux, lambda_zero_right_aux a l hab, monoidalComp]
  have hθ := iota_theta_ne_zero a b l hab
  have hΔ := iota_delta_ne_zero_aux l
  have hclosed := endo_from_closed_aux S hS l
    (W.split l a b ≫ W.K2 a b ≫ W.fuse a b l)
    (ι (θ (a : ℤ) b l * Λ (a : ℤ) b l))
    (closed_scalar S W hW hSeed a b l (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab)
  have hf (n : ℕ) :
      (W.split l a b ≫ W.K2 a b - ι (Λ a b l) • W.split l a b) ≫ W.fuse a b n = 0 := by
    rw [Preadditive.sub_comp, Linear.smul_comp]
    by_cases hn : n = l
    · subst n
      rw [Category.assoc, hclosed, (diagram_calculus S W hS hW).1 a b l]
      simp only [map_mul, smul_smul]
      have he : ι (θ (a : ℤ) b l) * ι (Λ (a : ℤ) b l) / ι (Δ (l : ℤ)) =
          ι (Λ (a : ℤ) b l) * (ι (θ (a : ℤ) b l) / ι (Δ (l : ℤ))) := by ring
      rw [he, sub_self]
    · rw [show (W.split l a b ≫ W.K2 a b) ≫ W.fuse a b n = 0 from
        hS.disjoint l n (Ne.symm hn) _,
        show W.split l a b ≫ W.fuse a b n = 0 from hS.disjoint l n (Ne.symm hn) _]
      simp
  have hz : W.split l a b ≫ W.K2 a b - ι (Λ a b l) • W.split l a b = 0 := by
    let f := W.split l a b ≫ W.K2 a b - ι (Λ a b l) • W.split l a b
    calc
      f = f ≫ 𝟙 (S.V a ⊗ S.V b) := by simp
      _ = f ≫ (∑ n ∈ fusionRange a b,
          (ι (Δ n) / ι (θ a b n)) • (W.fuse a b n ≫ W.split n a b)) := by
        rw [(diagram_calculus S W hS hW).2.2.2 a b]
      _ = 0 := by
        simp [f, Preadditive.comp_sum, Linear.comp_smul, ← Category.assoc, hf]
  exact sub_eq_zero.mp hz

lemma state_eigenvalue (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S)
    (hW : VertexNormalized W) (hSeed : TetSeed W) (a b c d l : ℕ) :
    W.X a b c d l ≫ W.Kop a b c d = ι (Λ a b l) • W.X a b c d l := by
  have hK : (α_ (S.V a ⊗ S.V b) (S.V c) (S.V d)).inv ≫
      W.K2 a b ▷ S.V c ▷ S.V d ≫ (α_ (S.V a ⊗ S.V b) (S.V c) (S.V d)).hom =
      W.K2 a b ▷ (S.V c ⊗ S.V d) := by simp
  simp [Vertex.X, Vertex.Kop, monoidalComp]
  slice_lhs 3 5 => rw [hK]
  rw [← MonoidalCategory.tensorHom_id (W.K2 a b) (S.V c ⊗ S.V d)]
  slice_lhs 2 3 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [Category.comp_id, split_eigenvalue S W hS hW hSeed a b l]
  simp [MonoidalCategory.tensorHom_def]

end RungEigenvalue

end QuantumSixJ.Network

open QuantumSixJ.Network
theorem solution {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) (hSeed : TetSeed W) :
    (∀ a b l : ℕ,
      S.cup l ≫ ((W.split l a b ≫ W.K2 a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
        ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) • W.tet a a b b l 2) ∧
    (∀ a b l : ℕ,
      W.split l a b ≫ W.K2 a b = ι (Λ a b l) • W.split l a b) ∧
    (∀ a b c d l : ℕ,
      W.X a b c d l ≫ W.Kop a b c d = ι (Λ a b l) • W.X a b c d l) := by
  exact ⟨AuthorDeformation.closed_upper_deformation S W hW,
    split_eigenvalue S W hS hW hSeed, state_eigenvalue S W hS hW hSeed⟩
