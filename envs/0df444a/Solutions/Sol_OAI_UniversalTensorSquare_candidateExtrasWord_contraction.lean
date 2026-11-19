-- Prove2me | solution 1 for OAI.UniversalTensorSquare.candidateExtrasWord_contraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:45.31493+00:00
-- url     : https://prove2.me/submissions/68ece346-5414-4e0f-a215-73bb0603d67e

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_ShortColumns_one_extra_lifted
import Theorems.Thm_OAI_Saxl_ShortColumns_one_extra_transpose_lifted
import Theorems.Thm_OAI_Saxl_perm_of_equal_content
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CoordinateSector
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
theorem altWord_sector {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop)
    (ha : ∀ i, Q (a i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      altWord (G ⊓ sectorGroup D) a := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite ↥(G ⊓ sectorGroup D)
  have hh (g : G) :
      (∀ i, Q ((a ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) i) ↔ D i) ↔
        (g : Equiv.Perm (Fin n)) ∈ sectorGroup D := by
    constructor
    · intro h i
      have h' := (ha _).symm.trans (h ((g : Equiv.Perm (Fin n)) i))
      simpa using h'.symm
    · intro h i
      exact (ha _).trans (by simpa using (h (((g : Equiv.Perm (Fin n))⁻¹) i)).symm)
  unfold altWord
  simp only [map_sum, map_smul, wordRep_single, coordinateProjection_single, hh, smul_ite, smul_zero]
  let e : {g : G // (g : Equiv.Perm (Fin n)) ∈ sectorGroup D} ≃ ↥(G ⊓ sectorGroup D) := {
    toFun := fun g => ⟨g.val.val, g.val.property, g.property⟩
    invFun := fun g => ⟨⟨g.val, g.property.1⟩, g.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Finset.sum_filter]
  rw [← Finset.sum_attach]
  apply Fintype.sum_equiv ?_ _ _ ?_
  · exact (Equiv.subtypeEquivRight (fun g => by simp)).trans e
  · intro g
    rfl

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.sumPerm_mul _root_.OAI.Saxl.sumPerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/

lemma altWord_split_term {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    (signC (sumPerm e g h) • wordRep n d (sumPerm e g h) (Pi.single w 1)) v =
    (signC g • wordRep a d g (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC h • wordRep b d h (Pi.single (rightWord e w) 1)) (rightWord e v) := by
  rw [single_positionProduct e w]
  change signC (sumPerm e g h) *
    ((Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e (v ∘ sumPerm e g h)) *
      (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e (v ∘ sumPerm e g h))) = _
  have h₁ : leftWord e (v ∘ sumPerm e g h) = leftWord e v ∘ g := by
    ext i; simp [leftWord]
  have h₂ : rightWord e (v ∘ sumPerm e g h) = rightWord e v ∘ h := by
    ext i; simp [rightWord]
  rw [h₁,h₂,signC_sumPerm]
  change _ = (signC g * (Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e v ∘ g)) *
    (signC h * (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e v ∘ h))
  ring

/- Independent block permutations factor with exactly the product sign. -/
theorem altWord_split {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (G : Subgroup (Equiv.Perm (Fin n))) (G₁ : Subgroup (Equiv.Perm (Fin a)))
    (G₂ : Subgroup (Equiv.Perm (Fin b))) (E : G ≃ G₁ × G₂)
    (hE : ∀ g : G, (g : Equiv.Perm (Fin n)) =
      sumPerm e ((E g).1 : Equiv.Perm (Fin a)) ((E g).2 : Equiv.Perm (Fin b)))
    (w : Fin n → Fin d) :
    altWord G w = positionProduct e (altWord G₁ (leftWord e w)) (altWord G₂ (rightWord e w)) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G₁
  let := Fintype.ofFinite G₂
  ext v
  unfold altWord
  simp only [Finset.sum_apply, positionProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : G₁ × G₂,
      (signC (p.1 : Equiv.Perm (Fin a)) • wordRep a d p.1 (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC (p.2 : Equiv.Perm (Fin b)) • wordRep b d p.2 (Pi.single (rightWord e w) 1)) (rightWord e v) := by
        apply Fintype.sum_equiv E
        intro g
        rw [hE g]
        exact altWord_split_term e w v _ _
    _ = _ := Fintype.sum_prod_type _



theorem altWord_fiber_split {n a b d : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Fin n → α) (w : Fin n → Fin d) :
    altWord (fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) w =
      positionProduct e
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inl i)))) (leftWord e w))
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inr i)))) (rightWord e w)) := by
  apply altWord_split e _ _ _ (fiberSplit e f).symm
  intro g
  exact (congrArg Subtype.val ((fiberSplit e f).apply_symm_apply g)).symm


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/

lemma averagedMap_apply {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) (x : X) :
    averagedMap ρ σ f x = ∑ g : G, σ g (f (ρ g⁻¹ x)) := by
  simp only [averagedMap, Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply,
    LinearMap.comp_apply]

/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
theorem sector_average_nonzero {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (H : Subgroup G) (f : X →ₗ[ℂ] Y) (hf : f ≠ 0)
    (he : ∀ g ∈ H, ∀ x, f (ρ g x) = σ g (f x))
    (P : Y →ₗ[ℂ] Y) (hP : ∀ x, P (f x) = f x)
    (hkill : ∀ g ∉ H, ∀ x, P (σ g (f x)) = 0) :
    averagedMap ρ σ f ≠ 0 := by
  classical
  have hproj (x : X) : P (averagedMap ρ σ f x) =
      ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) • f x := by
    rw [averagedMap_apply, map_sum]
    have hh (g : G) : P (σ g (f (ρ g⁻¹ x))) = if g ∈ H then f x else 0 := by
      by_cases hg : g ∈ H
      · rw [ite_eq_left hg, ← he g hg, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        exact hP x
      · rw [ite_eq_right hg]
        exact hkill g hg _
    simp only [hh]
    simp [Finset.sum_ite, Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, by simp⟩)
  intro hz
  apply hf
  ext x
  have heq := hproj x
  rw [hz] at heq
  change P 0 = _ at heq
  rw [map_zero] at heq
  exact (smul_eq_zero.mp heq.symm).resolve_left hc

open scoped MonoidAlgebra

end Saxl

namespace Saxl

theorem sector_support_transfer {n d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (D : Fin n → Prop) (A : Fin d → Prop) (z : WordSpace n d)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ sectorGroup D, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ cyclic (wordRep n d) z)
    (hs : ∀ x w, f x w ≠ 0 → wordSector D A w) :
    ∃ F : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation,
      F ≠ 0 := by
  classical
  let P := coordinateProjection (wordSector D A)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if wordSector D A w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ sectorGroup D) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if wordSector D A w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw (g i)).symm.trans (hh i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (sectorGroup D) f hf he P hP hk
  have hmem (x) : F x ∈ cyclic (wordRep n d) z := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact (cyclic (wordRep n d) z).apply_mem_toSubmodule g (hm _)
  let G : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨G, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/

lemma alphabetSub_iff {n d : ℕ} (A : Fin d → Prop) (x : WordSpace n d) :
    x ∈ alphabetSub n d A ↔ ∀ w, x w ≠ 0 → ∀ i, A (w i) := by
  change (∀ w, (∃ i, ¬ A (w i)) → x w = 0) ↔ _
  constructor
  · intro h w hw i
    by_contra hn
    exact hw (h w ⟨i,hn⟩)
  · intro h w hw
    by_contra hn
    obtain ⟨i,hi⟩ := hw
    exact hi (h w hn i)

lemma cyclic_alphabet {n d : ℕ} (A : Fin d → Prop) (v : WordSpace n d)
    (hv : v ∈ alphabetSub n d A) (x : WordSpace n d) (hx : x ∈ cyclic (wordRep n d) v) :
    x ∈ alphabetSub n d A := (cyclic_le _ _ _).mpr hv hx

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/

lemma positionProduct_sector {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (A : Fin d → Prop) (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ alphabetSub a d A) (hy : y ∈ alphabetSub b d (fun z => ¬A z)) :
    positionProduct e x y ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  intro w hw
  by_contra hn
  apply hw
  have hxy : x (leftWord e w) ≠ 0 ∧ y (rightWord e w) ≠ 0 := mul_ne_zero_iff.mp hn
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,leftWord] using
      (alphabetSub_iff A x).mp hx _ hxy.1 j
  | inr j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,rightWord] using
      (alphabetSub_iff (fun z => ¬A z) y).mp hy _ hxy.2 j

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma halfRows_rowLen (μ : YoungDiagram) (i : ℕ) :
    (halfRows μ).rowLen i = μ.rowLen i / 2 := by
  have hh : ∀ j, j < (halfRows μ).rowLen i ↔ j < μ.rowLen i / 2 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_halfRows]
    omega
  have h₁ := hh ((halfRows μ).rowLen i)
  have h₂ := hh (μ.rowLen i / 2)
  omega

lemma halfRows_card (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    2 * (halfRows μ).card = μ.card := by
  have hc := Fintype.card_congr (pairedCells μ he)
  simpa only [Fintype.card_sum, Fintype.card_coe, ← two_mul] using hc

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem specht_map_back_of_nonzero {n : ℕ} {μ : YoungDiagram}
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X) (t : Tableau n μ)
    (F : Representation.IntertwiningMap ρ (spechtRep t)) (hF : F ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t) ρ, f ≠ 0 := by
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨f, hf⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have he := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    H ⟨polytabloid t, mem_cyclic _ _⟩) hf
  change F (f _) = _ at he
  rw [hz] at he
  change F 0 = _ at he
  rw [map_zero] at he
  exact polytabloid_ne_zero t (congrArg Subtype.val he.symm)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_GeneralDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_pair_transpose {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (x : WordSpace n d) (y : WordSpace n e) :
    dotProduct (wordMap L x) y = dotProduct x (wordMap (fun b a => L a b) y) := by
  classical
  change (∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b) =
    ∑ a, x a * ∑ b, y b * ∏ i, L (a i) (b i)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem specht_to_cyclic_of_pair {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (L : Fin (μ.colLen 0) → Fin d → ℂ)
    (u : WordSpace n d)
    (h : dotProduct (wordMap L (polytabloid t)) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, F ≠ 0 := by
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let F : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) :=
    pr.comp ((wordMap (fun b a => L a b)).comp (subrepInclusion _))
  apply specht_map_back_of_nonzero _ t F
  intro hz
  have hp := subrepProject_pair (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
    (wordMap (fun b a => L a b) u) ⟨polytabloid t, mem_cyclic _ _⟩
  have he : pr (wordMap (fun b a => L a b) u) = 0 :=
    congrArg (fun H : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) =>
      H ⟨u, mem_cyclic _ _⟩) hz
  rw [he] at hp
  change dotProduct (0 : WordSpace n (μ.colLen 0)) (polytabloid t) =
    dotProduct (wordMap (fun b a => L a b) u) (polytabloid t) at hp
  rw [zero_dotProduct] at hp
  rw [wordMap_pair_transpose, dotProduct_comm]
    at h
  exact h hp.symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SingletonPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Pairs. -/

section

noncomputable section
namespace Saxl

lemma letterLift_comp {n a b c : ℕ} (φ : Fin a → Fin b) (ψ : Fin b → Fin c)
    (x : WordSpace n a) : letterLift ψ (letterLift φ x) = letterLift (ψ ∘ φ) x := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul, map_smul, map_smul, letterLift_single,
    letterLift_single, letterLift_single]
  rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

lemma cyclic_translate_eq {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (g : G) (v : X) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic _ _))
  · apply (cyclic_le _ _ _).mpr
    have h := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic _ _)
    change v ∈ (cyclic ρ (ρ g v)).toSubmodule
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PolynomialDetection
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma jointContent_apply {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e)
    (j : Fin d × Fin e) : jointContent a b j =
      (Finset.univ.filter (fun i => (a i, b i) = j)).card := by
  classical
  simp [jointContent, Finsupp.single_apply, eq_comm]

lemma perm_of_equal_jointContent {n d e : ℕ}
    (a a' : Fin n → Fin d) (b b' : Fin n → Fin e)
    (h : jointContent a b = jointContent a' b') :
    ∃ g : Equiv.Perm (Fin n), a' ∘ g = a ∧ b' ∘ g = b := by
  classical
  have hc : ∀ j : Fin (d*e),
      (Finset.univ.filter (fun i => finProdFinEquiv (a i,b i) = j)).card =
      (Finset.univ.filter (fun i => finProdFinEquiv (a' i,b' i) = j)).card := by
    intro j
    have hh := DFunLike.congr_fun h (finProdFinEquiv.symm j)
    simp only [jointContent_apply] at hh
    simpa only [← Equiv.eq_symm_apply] using hh
  obtain ⟨g, hg⟩ := perm_of_equal_content
    (fun i => finProdFinEquiv (a i, b i))
    (fun i => finProdFinEquiv (a' i, b' i)) hc
  refine ⟨g, ?_, ?_⟩
  · funext i
    exact congrArg Prod.fst (finProdFinEquiv.injective (congrFun hg i))
  · funext i
    exact congrArg Prod.snd (finProdFinEquiv.injective (congrFun hg i))

lemma intertwiner_jointContent {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a a' : Fin n → Fin d) (b b' : Fin n → Fin e)
    (h : jointContent a b = jointContent a' b') :
    F (Pi.single a 1) b = F (Pi.single a' 1) b' := by
  classical
  obtain ⟨g, ha, hb⟩ := perm_of_equal_jointContent a a' b b' h
  have hs : wordRep n d g (Pi.single a 1) = Pi.single a' 1 := by
    ext w
    change (Pi.single a 1 : WordSpace n d) (w ∘ g) = (Pi.single a' 1 : WordSpace n d) w
    simp only [Pi.single_apply]
    have he : (w ∘ g = a) ↔ w = a' := by
      rw [← ha]
      exact ⟨fun h => funext (fun i => by
        have hh := congrFun h (g⁻¹ i)
        simpa using hh),
        fun h => by rw [h]⟩
    simp only [he]
  have hh := congrFun (LinearMap.congr_fun (F.isIntertwining' g) (Pi.single a 1)) b'
  simp only [LinearMap.comp_apply] at hh
  rw [hs] at hh
  change F (Pi.single a' 1) b' = F (Pi.single a 1) (b' ∘ g) at hh
  rw [hb] at hh
  exact hh.symm

lemma eval_jointContent_monomial {n d e : ℕ}
    (a : Fin n → Fin d) (b : Fin n → Fin e)
    (c : ℂ) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2)
      (MvPolynomial.monomial (jointContent a b) c) =
      c * ∏ i, L (a i) (b i) := by
  classical
  rw [jointContent, MvPolynomial.monomial_sum_index]
  simp only [map_mul, MvPolynomial.eval_C, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  change MvPolynomial.eval _ (MvPolynomial.X (a i, b i)) = _
  exact MvPolynomial.eval_X _

lemma pairingPolynomial_eval {n d e : ℕ}
    (x : WordSpace n d) (y : WordSpace n e) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2) (pairingPolynomial x y) =
      dotProduct (wordMap L x) y := by
  classical
  simp only [pairingPolynomial, map_sum, eval_jointContent_monomial]
  change (∑ a, ∑ b, x a * y b * ∏ i, L (a i) (b i)) =
    ∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma jointContentWeight_apply {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    jointContentWeight F (jointContent a b) = F (Pi.single a 1) b := by
  classical
  unfold jointContentWeight
  have hab : ∃ a' b', jointContent a' b' = jointContent a b := ⟨a,b,rfl⟩
  rw [dite_eq_left hab]
  exact intertwiner_jointContent F _ a _ b hab.choose_spec.choose_spec

lemma pairingPolynomial_zero_pair {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (y : WordSpace n e) (h : pairingPolynomial x y = 0) :
    dotProduct (F x) y = 0 := by
  classical
  let w : MvPolynomial (Fin d × Fin e) ℂ →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ (jointContentWeight F)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  have he := congrArg w h
  have hw (m : (Fin d × Fin e) →₀ ℕ) (c : ℂ) :
      w (MvPolynomial.monomial m c) = c * jointContentWeight F m := by
    change Finsupp.linearCombination ℂ (jointContentWeight F) (Finsupp.single m c) = _
    simp
  have he' : (∑ a, ∑ b, (x a * y b) * F (Pi.single a 1) b) = 0 := by
    simpa only [pairingPolynomial, map_sum, map_zero, hw, jointContentWeight_apply] using he
  have hx : x = ∑ a, x a • Pi.single a 1 := by
    ext a
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp only [map_smul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  convert he' using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem wordMap_detects_intertwiner {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (y : WordSpace n e)
    (h : dotProduct (F x) y ≠ 0) :
    ∃ L : Fin d → Fin e → ℂ, dotProduct (wordMap L x) y ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply pairingPolynomial_zero_pair F
  apply MvPolynomial.funext
  intro L
  simpa only [map_zero, pairingPolynomial_eval] using
    (pairingPolynomial_eval x y (fun a b => L (a,b))).trans (hn _)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_DualPolytabloid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Polytabloid. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open scoped MonoidAlgebra

theorem dual_polytabloid_necessary {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d)
    (f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation) (hf : f ≠ 0) :
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin (μ.colLen 0) → Fin d → ℂ),
      dotProduct (wordMap L (wordRep n (μ.colLen 0) g (polytabloid t))) u ≠ 0 := by
  let := specht_irreducible t
  have hfi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let E := (subrepInclusion (cyclic (wordRep n d) u)).comp f
  have hEi : Function.Injective E := Subtype.val_injective.comp hfi
  obtain ⟨R, hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id (spechtRep t))
  have hRu : R u ≠ 0 := by
    intro h0
    let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
    have hm := intertwiner_cyclic_mem R u (E p) (f p).property
    rw [h0, cyclic_zero_mem_iff] at hm
    have hi := congrArg (fun H : Representation.IntertwiningMap (spechtRep t)
      (spechtRep t) => H p) hR
    change R (E p) = p at hi
    exact polytabloid_ne_zero t (congrArg Subtype.val (hi.symm.trans hm))
  have hv : (R u).val ≠ 0 := by
    intro hz
    exact hRu (Subtype.ext hz)
  obtain ⟨g, hg⟩ := specht_detect t (R u).property hv
  let F := (subrepInclusion (spechtSub t)).comp R
  have hp : dotProduct (F u)
      (wordRep n (μ.colLen 0) g⁻¹ (polytabloid t)) ≠ 0 := by
    rw [wordPair_move] at hg
    exact hg
  obtain ⟨L,hL⟩ := wordMap_detects_intertwiner F u _ hp
  refine ⟨g⁻¹, fun b a => L a b, ?_⟩
  rw [wordMap_pair_transpose, dotProduct_comm] at hL
  exact hL

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ProductInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma externalWordMap_tmul {n a b d : ℕ} {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d)) (x : X) (y : Y) :
    externalWordMap e F G (x ⊗ₜ[ℂ] y) = positionProduct e (F x) (G y) :=
  positionTensor_tmul e (F x) (G y)

lemma externalWordMap_injective {n a b d : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d))
    (hF : Function.Injective F) (hG : Function.Injective G) :
    Function.Injective (externalWordMap e F G) :=
  (positionTensor e).injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _ hF hG)

theorem external_cyclic_support {n a b d : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (τ : Representation ℂ (Equiv.Perm (Fin b)) Z)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬ A z))
    (F : Representation.IntertwiningMap σ (cyclic (wordRep a d) v).toRepresentation)
    (G : Representation.IntertwiningMap τ (cyclic (wordRep b d) u).toRepresentation)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ))
    (hf : f ≠ 0) :
    ∃ H : Representation.IntertwiningMap ρ
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, H ≠ 0 := by
  let F' := (subrepInclusion (cyclic (wordRep a d) v)).comp F
  let G' := (subrepInclusion (cyclic (wordRep b d) u)).comp G
  let T := externalWordMap e F' G'
  let L := T.comp f
  have hT : Function.Injective T := externalWordMap_injective e F' G'
    (Subtype.val_injective.comp hF) (Subtype.val_injective.comp hG)
  have hL : L ≠ 0 := intertwining_comp_ne_zero T hT f hf
  have hm (z : Y ⊗[ℂ] Z) : T z ∈ cyclic (wordRep n d) (positionProduct e v u) := by
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      rw [show T (x ⊗ₜ[ℂ] y) = positionProduct e (F' x) (G' y) from
        externalWordMap_tmul e F' G' x y]
      exact product_mem_cyclic e v u (F' x) (G' y) (F x).property (G y).property
  have hs (z : Y ⊗[ℂ] Z) : T z ∈
      coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      rw [show T (x ⊗ₜ[ℂ] y) = positionProduct e (F' x) (G' y) from
        externalWordMap_tmul e F' G' x y]
      exact positionProduct_sector e A (F' x) (G' y)
        (cyclic_alphabet A v hv _ (F x).property)
        (cyclic_alphabet (fun z => ¬ A z) u hu _ (G y).property)
  apply sector_support_transfer ρ (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L.toLinearMap
  · intro hz
    exact hL (Representation.IntertwiningMap.ext hz)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g :=
      sumPerm_restrictions e g'
    rw [← heq]
    exact LinearMap.congr_fun (L.isIntertwining'
      (leftRestriction e g', rightRestriction e g')) x
  · intro x
    exact hm (f x)
  · intro x w hw
    by_contra hn
    exact hw (hs (f x) w hn)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Reorder. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Columns

lemma positionProduct_pair {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x u : WordSpace a d) (y v : WordSpace b d) :
    dotProduct (positionProduct e x y) (positionProduct e u v) =
      dotProduct x u * dotProduct y v := by
  classical
  let E : (Fin n → Fin d) ≃ (Fin a → Fin d) × (Fin b → Fin d) :=
    (Equiv.arrowCongr e (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  rw [dotProduct, dotProduct, dotProduct, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type (fun p : (Fin a → Fin d) × (Fin b → Fin d) =>
    x p.1 * u p.1 * (y p.2 * v p.2))]
  apply Fintype.sum_equiv E
  intro w
  change (x (leftWord e w) * y (rightWord e w)) *
      (u (leftWord e w) * v (rightWord e w)) =
      (x (leftWord e w) * u (leftWord e w)) *
      (y (rightWord e w) * v (rightWord e w))
  ring

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma row_lt_some_height {rs : List ℕ} (c : Cells rs) :
    ∃ h ∈ rs, row c < h := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons h rs ih =>
    rcases c with c | c
    · exact ⟨h,by simp,c.isLt⟩
    · obtain ⟨h,hh,hc⟩ := ih c
      exact ⟨h,List.mem_cons_of_mem _ hh,hc⟩

lemma placed_height {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (B : ℕ) (hB : ∀ h ∈ rs, h ≤ B) :
    μ.colLen 0 ≤ B := by
  by_contra hh
  let x : μ.cells := ⟨(B,0),YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩
  obtain ⟨h,hh,hc⟩ := row_lt_some_height (e.symm x)
  have ha := hr (e.symm x)
  rw [Equiv.apply_symm_apply] at ha
  change B = row (e.symm x) at ha
  have hb := hB h hh
  omega

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma doubled_map {α β : Type*} (f : α → β) (xs : List α) :
    (doubled xs).map f = doubled (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [doubled_cons, List.map_cons, ih]

lemma doubled_sum (xs : List ℕ) : (doubled xs).sum = 2*xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [doubled_cons, List.sum_cons, ih]; omega

lemma doubled_countP {α : Type*} (p : α → Bool) (xs : List α) :
    (doubled xs).countP p = 2*xs.countP p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [doubled_cons, List.countP_cons, ih]; split <;> omega

lemma doubled_mem {α : Type*} (x : α) (xs : List α) : x ∈ doubled xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [doubled_cons, List.mem_cons, ih, or_self_left]

lemma doubled_perm {α : Type*} {xs ys : List α} (h : xs.Perm ys) :
    (doubled xs).Perm (doubled ys) :=
  h.flatMap (fun _ _ => List.Perm.refl _)

theorem balanced_heights (xs : List ℕ) (D : ℕ) (hD : ∀ h ∈ xs, h ≤ 2*D) :
    ∃ ps : List (ℕ × ℕ),
      ps.map (fun p => p.1+p.2) = xs ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = xs.sum/2 ∧
      (ps.map Prod.snd).sum = (xs.sum+1)/2 := by
  induction xs with
  | nil => exact ⟨[],rfl,by simp,by simp,by simp⟩
  | cons j xs ih =>
    obtain ⟨ps,ht,hp,ha,hb⟩ := ih (fun h hh => hD h (by simp [hh]))
    let a := if xs.sum % 2 = 0 then j/2 else (j+1)/2
    let b := j-a
    have hj := hD j (by simp)
    have hab : a + b = j := by unfold b a; split_ifs <;> omega
    have haD : a ≤ D := by unfold a; split_ifs <;> omega
    have hbD : b ≤ D := by unfold b a; split_ifs <;> omega
    refine ⟨(a,b)::ps,?_,?_,?_,?_⟩
    · simp only [List.map_cons, hab, ht]
    · intro p hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨haD,hbD⟩
      · exact hp p hp'
    · simp only [List.map_cons, List.sum_cons, ha]
      unfold a; split_ifs <;> omega
    · simp only [List.map_cons, List.sum_cons, hb]
      unfold b a; split_ifs <;> omega

lemma odd_sum_has_odd (xs : List ℕ) (h : xs.sum % 2 = 1) :
    ∃ j ∈ xs, j % 2 = 1 := by
  induction xs with
  | nil => simp at h
  | cons j xs ih =>
    by_cases hj : j % 2 = 1
    · exact ⟨j,by simp,hj⟩
    · have ht : xs.sum % 2 = 1 := by simp only [List.sum_cons] at h; omega
      obtain ⟨k,hk,hko⟩ := ih ht
      exact ⟨k,List.mem_cons_of_mem _ hk,hko⟩

theorem balanced_even_splits (xs : List ℕ) (D : ℕ)
    (hD : ∀ h ∈ xs, h ≤ 2*D) (he : xs.sum % 2 = 0) :
    ∃ ps : List (ℕ × ℕ),
      ps.map (fun p => p.1+p.2) = doubled xs ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = xs.sum ∧
      (ps.map Prod.snd).sum = xs.sum ∧
      (∀ i, Even ((ps.map Prod.fst).countP (fun h => decide (i<h)))) ∧
      (∀ i, Even ((ps.map Prod.snd).countP (fun h => decide (i<h)))) := by
  obtain ⟨ps,ht,hp,ha,hb⟩ := balanced_heights xs D hD
  refine ⟨doubled ps,?_,?_,?_,?_,?_,?_⟩
  · rw [doubled_map,ht]
  · intro p hh; exact hp p ((doubled_mem p ps).mp hh)
  · rw [doubled_map,doubled_sum,ha]; omega
  · rw [doubled_map,doubled_sum,hb]; omega
  · intro i; rw [doubled_map,doubled_countP]; exact even_two_mul _
  · intro i; rw [doubled_map,doubled_countP]; exact even_two_mul _

theorem balanced_double_splits (xs : List ℕ) (D : ℕ)
    (hD : ∀ h ∈ xs, h ≤ 2*D) :
    ∃ ps : List (ℕ × ℕ),
      (ps.map (fun p => p.1+p.2)).Perm (doubled xs) ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = xs.sum ∧
      (ps.map Prod.snd).sum = xs.sum ∧
      ShortColumns.RowParity (xs.sum%2) (columnShape (ps.map Prod.fst)) ∧
      ShortColumns.RowParity (xs.sum%2) (columnShape (ps.map Prod.snd)) := by
  by_cases he : xs.sum % 2 = 0
  · obtain ⟨ps,ht,hp,ha,hb,hra,hrb⟩ := balanced_even_splits xs D hD he
    refine ⟨ps,ht ▸ List.Perm.refl _,hp,ha,hb,?_,?_⟩
    · simpa only [he, ShortColumns.RowParity, ↓reduceIte, columnShape_rowLen] using hra
    · simpa only [he, ShortColumns.RowParity, ↓reduceIte, columnShape_rowLen] using hrb
  · have ho : xs.sum % 2 = 1 := by omega
    obtain ⟨j,hj,hjo⟩ := odd_sum_has_odd xs ho
    let ys := xs.erase j
    have hperm : xs.Perm (j::ys) := List.perm_cons_erase hj
    have hsum : xs.sum = j + ys.sum := by simpa only [List.sum_cons] using hperm.sum_eq
    have hys : ys.sum % 2 = 0 := by omega
    have hDy : ∀ h ∈ ys, h ≤ 2*D := by
      intro h hh; exact hD h ((hperm.mem_iff).mpr (List.mem_cons_of_mem _ hh))
    obtain ⟨ps,ht,hp,ha,hb,hra,hrb⟩ := balanced_even_splits ys D hDy hys
    let k := j/2
    have hjk : j = 2*k+1 := by dsimp [k]; omega
    have hkD : k+1 ≤ D := by have := hD j hj; omega
    let qs := (k+1,k)::(k,k+1)::ps
    have hta : (qs.map Prod.fst) = (k+1)::k::(ps.map Prod.fst) := rfl
    have htb : (qs.map Prod.snd) = k::(k+1)::(ps.map Prod.snd) := rfl
    have rowVals (zs : List ℕ) (i : ℕ) :
        ((k+1)::k::zs).countP (fun h => decide (i<h)) =
          zs.countP (fun h => decide (i<h)) +
            (if i<k then 2 else if i=k then 1 else 0) := by
      simp only [List.countP_cons, decide_eq_true_eq]
      split_ifs <;> omega
    have hpA : ShortColumns.RowParity 1 (columnShape (qs.map Prod.fst)) := by
      simp only [ShortColumns.RowParity, Nat.one_ne_zero, ite_false, if_false]
      refine ⟨k,?_,?_⟩
      · rw [columnShape_rowLen,hta,rowVals]
        simp only [lt_self_iff_false, ite_false, if_false]
        exact (hra k).add_odd odd_one
      · intro i hi
        rw [columnShape_rowLen,hta,rowVals]
        simp only [hi, ite_false, if_false]
        split_ifs
        · exact (hra i).add (by decide : Even 2)
        · simpa using hra i
    have countSwap (i : ℕ) :
        (qs.map Prod.snd).countP (fun h => decide (i<h)) =
          ((k+1)::k::(ps.map Prod.snd)).countP (fun h => decide (i<h)) := by
      rw [htb]
      exact List.Perm.countP_eq _ (List.Perm.swap _ _ _)
    have hpB : ShortColumns.RowParity 1 (columnShape (qs.map Prod.snd)) := by
      simp only [ShortColumns.RowParity, Nat.one_ne_zero, ite_false, if_false]
      refine ⟨k,?_,?_⟩
      · rw [columnShape_rowLen,countSwap,rowVals]
        simp only [lt_self_iff_false, ite_false, if_false]
        exact (hrb k).add_odd odd_one
      · intro i hi
        rw [columnShape_rowLen,countSwap,rowVals]
        simp only [hi, ite_false, if_false]
        split_ifs
        · exact (hrb i).add (by decide : Even 2)
        · simpa using hrb i
    refine ⟨qs,?_,?_,?_,?_,by rwa [ho],by rwa [ho]⟩
    · have ht' : qs.map (fun p => p.1+p.2) = doubled (j::ys) := by
        simp only [qs,List.map_cons,ht,doubled_cons]
        rw [show k+1+k = j by omega, show k+(k+1) = j by omega]
      exact ht' ▸ (doubled_perm hperm).symm
    · intro p hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨hkD,by omega⟩
      · rcases List.mem_cons.mp hh with rfl | hh
        · exact ⟨by omega,hkD⟩
        · exact hp p hh
    · rw [hta,List.sum_cons,List.sum_cons,ha]; omega
    · rw [htb,List.sum_cons,List.sum_cons,hb]; omega

lemma columnShape_perm {xs ys : List ℕ} (hp : xs.Perm ys) :
    columnShape xs = columnShape ys := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  change (i,j) ∈ columnShape xs ↔ (i,j) ∈ columnShape ys
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen,
    columnShape_rowLen, columnShape_rowLen, hp.countP_eq]

lemma count_columns (μ : YoungDiagram) (i : ℕ) :
    μ.transpose.rowLens.countP (fun h => decide (i<h)) = μ.rowLen i :=
  (placed_rowLen (toYoung μ) (fun _ => rfl) i).symm

lemma columnShape_doubled_halfRows (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    columnShape (doubled (halfRows μ).transpose.rowLens) = μ := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  change (i,j) ∈ columnShape _ ↔ (i,j) ∈ μ
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen,
    columnShape_rowLen,doubled_countP,count_columns,halfRows_rowLen]
  have hh := (Nat.even_iff.mp (he i))
  omega

lemma columns_bounded (μ : YoungDiagram) (D : ℕ) (hD : μ.colLen 0 ≤ D) :
    ∀ h ∈ μ.transpose.rowLens, h ≤ D := by
  intro h hh
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hh
  exact le_trans (by simpa only [YoungDiagram.rowLen_transpose] using μ.colLen_anti 0 i (Nat.zero_le _)) hD

theorem even_rows_allocation (r D : ℕ) (μ : YoungDiagram) (hm : μ.card = 2*r)
    (he : ∀ i, Even (μ.rowLen i)) (hD : μ.colLen 0 ≤ 2*D) :
    ∃ ps : List (ℕ × ℕ),
      columnShape (ps.map (fun p => p.1+p.2)) = μ ∧
      (∀ p ∈ ps, p.1 ≤ D ∧ p.2 ≤ D) ∧
      (ps.map Prod.fst).sum = r ∧ (ps.map Prod.snd).sum = r ∧
      ShortColumns.RowParity (r%2) (columnShape (ps.map Prod.fst)) ∧
      ShortColumns.RowParity (r%2) (columnShape (ps.map Prod.snd)) := by
  let xs := (halfRows μ).transpose.rowLens
  have hx : xs.sum = r := by
    have hc := placed_card (toYoung (halfRows μ))
    have hc' := halfRows_card μ he
    change (halfRows μ).card = xs.sum at hc
    omega
  obtain ⟨ps,ht,hp,ha,hb,hpa,hpb⟩ := balanced_double_splits xs D
    (columns_bounded (halfRows μ) (2*D) (by rwa [halfRows_height μ he]))
  refine ⟨ps,?_,hp,ha.trans hx,hb.trans hx,?_,?_⟩
  · exact (columnShape_perm ht).trans (columnShape_doubled_halfRows μ he)
  · rwa [hx] at hpa
  · rwa [hx] at hpb

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandLetters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Letters. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma bandExtraLetter_injective {M b δ D : ℕ} (hD : M+b+δ ≤ D) :
    Function.Injective (@bandExtraLetter M b δ D hD) := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [bandExtraLetter] at hv
  split_ifs at hv <;> omega

lemma bandExtraLetter_high {M b δ D : ℕ} (hM : 4 ≤ M) (hD : M+b+δ ≤ D)
    (c : Fin ((ShortColumns.shape b δ).transpose.colLen 0)) :
    2 ≤ (bandExtraLetter hD c).val := by
  dsimp only [bandExtraLetter]
  split_ifs <;> omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CommonBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common Basis. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem finite_polynomials_common_point {ι σ : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℂ) (hp : ∀ i, p i ≠ 0)
    (q : MvPolynomial σ ℂ) (hq : q ≠ 0) :
    ∃ v : σ → ℂ, MvPolynomial.eval v q ≠ 0 ∧
      ∀ i, MvPolynomial.eval v (p i) ≠ 0 := by
  classical
  have hprod : q * ∏ i, p i ≠ 0 := mul_ne_zero hq
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have he : ∃ v : σ → ℂ, MvPolynomial.eval v (q * ∏ i, p i) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hprod
    exact MvPolynomial.funext (fun v => by simpa only [map_zero] using hn v)
  obtain ⟨v,hv⟩ := he
  simp only [map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_const] at hv
  exact ⟨v,hv⟩

theorem wordMap_common_invertible {ι : Type*} [Fintype ι] (n : ι → ℕ) (d : ℕ)
    (x y : ∀ i, WordSpace (n i) d)
    (h : ∀ i, ∃ L : Fin d → Fin d → ℂ,
      dotProduct (wordMap L (x i)) (y i) ≠ 0) :
    ∃ L : Fin d → Fin d → ℂ, (Matrix.of L).det ≠ 0 ∧
      ∀ i, dotProduct (wordMap L (x i)) (y i) ≠ 0 := by
  have hp (i) : pairingPolynomial (x i) (y i) ≠ 0 := by
    obtain ⟨L,hL⟩ := h i
    intro hz
    apply hL
    rw [← pairingPolynomial_eval, hz, map_zero]
  obtain ⟨v,hv,hp⟩ := finite_polynomials_common_point
    (fun i => pairingPolynomial (x i) (y i)) hp
    (Matrix.mvPolynomialX (Fin d) (Fin d) ℂ).det
    (Matrix.det_mvPolynomialX_ne_zero (Fin d) ℂ)
  refine ⟨fun a b => v (a,b), ?_, ?_⟩
  · exact (Matrix.eval_det_mvPolynomialX (Fin d) ℂ v) ▸ hv
  · intro i
    exact (pairingPolynomial_eval (x i) (y i) (fun a b => v (a,b))) ▸ hp i

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_FlagColumns
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flag Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

lemma blocks_pair_tensorList {α : Type*} (k : α → ℕ) {d : ℕ}
    (v : ∀ a, WordSpace (k a) d) (as : List α) (N : ℕ → Fin d → ℂ) :
    dotProduct (blocks (as.map k) N) (tensorList k v as) =
      (as.map (fun a => dotProduct (wedge (k a) N) (v a))).prod := by
  induction as with
  | nil =>
    change dotProduct (blocks [] N) (fun _ => (1 : ℂ)) = 1
    rw [blocks_nil]
    change (∑ _ : Fin 0 → Fin d, (1:ℂ) * 1) = 1
    simp
  | cons a as ih =>
    change dotProduct (blocks (k a :: as.map k) N)
      (positionProduct finSumFinEquiv.symm (v a) (tensorList k v as)) = _
    rw [blocks_cons]
    change dotProduct
      (positionProduct (n := k a + (as.map k).sum) finSumFinEquiv.symm
        (wedge (k a) N) (blocks (as.map k) N))
      (positionProduct finSumFinEquiv.symm (v a) (tensorList k v as)) = _
    rw [positionProduct_pair, ih]
    rfl

lemma altWord_injective_base {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (ha : Function.Injective a) : altWord G a a = 1 := by
  classical
  let := Fintype.ofFinite G
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single 1]
  · simp [wordRep]
  · intro g hg hne
    have hn : a ∘ (g : Equiv.Perm (Fin n)) ≠ a := by
      intro he
      apply hne
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact ha (congrFun he i)
    change signC g.val * (Pi.single a (1 : ℂ) : WordSpace n d)
      (a ∘ g.val) = 0
    rw [Pi.single_eq_of_ne hn, mul_zero]
  · simp

lemma altWord_real {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) : star (altWord G a) = altWord G a := by
  classical
  let := Fintype.ofFinite G
  funext w
  simp only [altWord, Pi.star_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro g hg
  simp [signC, wordRep, Pi.single_apply]

lemma wedge_eq_mapped_alt {r d : ℕ} (h : r ≤ d) (N : ℕ → Fin d → ℂ) :
    wedge r N = wordMap (fun i a => N i.val a)
      (altWord (⊤ : Subgroup (Equiv.Perm (Fin r))) (Fin.castLE h)) := by
  classical
  rw [altWord_inverse_sum, map_sum]
  unfold wedge
  symm
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin r)))
  let e : (⊤ : Subgroup (Equiv.Perm (Fin r))) ≃ Equiv.Perm (Fin r) :=
    { toFun := Subtype.val
      invFun := fun π => ⟨π, Subgroup.mem_top π⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply Fintype.sum_equiv e
  intro π
  simp only [map_smul]
  congr 1
  funext w
  rw [wordMap_single]
  rfl

theorem common_flag_tensorList {α : Type*} (k : α → ℕ) (d : ℕ)
    (v : ∀ a, WordSpace (k a) d) (as : List α)
    (hd : ∀ a ∈ as, k a ≤ d)
    (h : ∀ a ∈ as, ∃ N : ℕ → Fin d → ℂ,
      dotProduct (wedge (k a) N) (v a) ≠ 0) :
    ∃ L : Fin d → Fin d → ℂ, (Matrix.of L).det ≠ 0 ∧
      dotProduct (blocks (as.map k) (fun i a => if hi : i < d then L ⟨i,hi⟩ a else 0))
        (tensorList k v as) ≠ 0 := by
  classical
  let ι := {a // a ∈ as}
  let : Fintype ι := Fintype.ofFinite _
  let x : ∀ a : ι, WordSpace (k a.val) d := fun a =>
    altWord ⊤ (Fin.castLE (hd a.val a.property))
  have hx (a : ι) : ∃ L : Fin d → Fin d → ℂ,
      dotProduct (wordMap L (x a)) (v a.val) ≠ 0 := by
    obtain ⟨N,hN⟩ := h a.val a.property
    refine ⟨fun i j => N i.val j, ?_⟩
    rwa [← wedge_eq_mapped_alt (hd a.val a.property)]
  obtain ⟨L,hL,hp⟩ := wordMap_common_invertible (fun a : ι => k a.val) d x
    (fun a => v a.val) hx
  refine ⟨L,hL,?_⟩
  rw [blocks_pair_tensorList]
  apply List.prod_ne_zero
  intro hz
  obtain ⟨a,ha,heq⟩ := List.mem_map.mp hz
  have he : wedge (k a) (fun i b => if hi : i < d then L ⟨i,hi⟩ b else 0) =
      wordMap L (x ⟨a,ha⟩) := by
    rw [wedge_eq_mapped_alt (hd a ha)]
    have hn : (fun (i : Fin d) b => if hi : i.val < d then L ⟨i.val,hi⟩ b else 0) = L := by
      funext i b
      exact dite_eq_left i.isLt
    rw [hn]
  exact hp ⟨a,ha⟩ (he ▸ heq)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnTensorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Tensor Split. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns

lemma splitCons_left_first {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin a) :
    (splitCons (a := a) (b := b) e).symm (Sum.inl (Fin.castAdd A i)) =
      Fin.castAdd n (Fin.castAdd b i) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitCons_right_first {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin b) :
    (splitCons (a := a) (b := b) e).symm (Sum.inr (Fin.castAdd B i)) =
      Fin.castAdd n (Fin.natAdd a i) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitCons_left_rest {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin A) :
    (splitCons (a := a) (b := b) e).symm (Sum.inl (Fin.natAdd a i)) =
      Fin.natAdd (a+b) (e.symm (Sum.inl i)) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitCons_right_rest {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin B) :
    (splitCons (a := a) (b := b) e).symm (Sum.inr (Fin.natAdd b i)) =
      Fin.natAdd (a+b) (e.symm (Sum.inr i)) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitPositions_left_first (a b : ℕ) (ps : List (ℕ × ℕ)) (i : Fin a) :
    (splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.castAdd (ps.map Prod.fst).sum i)) =
      Fin.castAdd (ps.map (fun p => p.1+p.2)).sum (Fin.castAdd b i) := by
  exact splitCons_left_first (splitPositions ps) i

lemma splitPositions_right_first (a b : ℕ) (ps : List (ℕ × ℕ)) (i : Fin b) :
    (splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.castAdd (ps.map Prod.snd).sum i)) =
      Fin.castAdd (ps.map (fun p => p.1+p.2)).sum (Fin.natAdd a i) := by
  exact splitCons_right_first (splitPositions ps) i

lemma splitPositions_left_rest (a b : ℕ) (ps : List (ℕ × ℕ))
    (i : Fin (ps.map Prod.fst).sum) :
    (splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.natAdd a i)) =
      Fin.natAdd (a+b) ((splitPositions ps).symm (Sum.inl i)) := by
  exact splitCons_left_rest (splitPositions ps) i

lemma splitPositions_right_rest (a b : ℕ) (ps : List (ℕ × ℕ))
    (i : Fin (ps.map Prod.snd).sum) :
    (splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.natAdd b i)) =
      Fin.natAdd (a+b) ((splitPositions ps).symm (Sum.inr i)) := by
  exact splitCons_right_rest (splitPositions ps) i

theorem tensorList_split {d : ℕ}
    (v : ∀ p : ℕ × ℕ, WordSpace p.1 d) (u : ∀ p : ℕ × ℕ, WordSpace p.2 d)
    (ps : List (ℕ × ℕ)) :
    positionProduct (splitPositions ps) (tensorList Prod.fst v ps) (tensorList Prod.snd u ps) =
      tensorList (fun p => p.1+p.2)
        (fun p => positionProduct finSumFinEquiv.symm (v p) (u p)) ps := by
  induction ps with
  | nil => funext w; change (1:ℂ)*1=1; ring
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    funext w
    have hll : leftWord finSumFinEquiv.symm (leftWord (splitPositions ((a,b)::ps)) w) =
        leftWord finSumFinEquiv.symm (leftWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.castAdd _ i))) =
        w (Fin.castAdd _ (Fin.castAdd _ i))
      erw [splitPositions_left_first]
      rfl
    have hrl : leftWord finSumFinEquiv.symm (rightWord (splitPositions ((a,b)::ps)) w) =
        rightWord finSumFinEquiv.symm (leftWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.castAdd _ i))) =
        w (Fin.castAdd _ (Fin.natAdd _ i))
      erw [splitPositions_right_first]
      rfl
    have hlr : rightWord finSumFinEquiv.symm (leftWord (splitPositions ((a,b)::ps)) w) =
        leftWord (splitPositions ps) (rightWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.natAdd _ i))) =
        w (Fin.natAdd _ ((splitPositions ps).symm (Sum.inl i)))
      erw [splitPositions_left_rest]
      rfl
    have hrr : rightWord finSumFinEquiv.symm (rightWord (splitPositions ((a,b)::ps)) w) =
        rightWord (splitPositions ps) (rightWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.natAdd _ i))) =
        w (Fin.natAdd _ ((splitPositions ps).symm (Sum.inr i)))
      erw [splitPositions_right_rest]
      rfl
    change ((v (a,b) _) * tensorList Prod.fst v ps _) *
      ((u (a,b) _) * tensorList Prod.snd u ps _) =
        ((v (a,b) _) * (u (a,b) _)) * _
    erw [hll,hrl,hlr,hrr, ← ih]
    change (_ * _) * (_ * _) = (_ * _) * (_ * _)
    exact mul_mul_mul_comm _ _ _ _

lemma blocks_eq_tensorList {α : Type*} (k : α → ℕ) {d : ℕ}
    (N : ℕ → Fin d → ℂ) (as : List α) :
    blocks (as.map k) N = tensorList k (fun a => wedge (k a) N) as := by
  induction as with
  | nil => exact blocks_nil N
  | cons a as ih => exact (blocks_cons (k a) (as.map k) N).trans (by rw [ih]; rfl)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_SplitFlag
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split Flag. -/

section

noncomputable section
namespace Saxl.FlagColumns

lemma pure_single {n d : ℕ} (a : Fin n → Fin d) :
    pure (fun i => Pi.single (a i) 1) = Pi.single a 1 := by
  classical
  funext w
  by_cases h : w = a
  · subst w
    simp [pure]
  · rw [Pi.single_eq_of_ne h]
    unfold pure
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne hi 1)

lemma wedge_base {n d : ℕ} (a : Fin n → Fin d) :
    ∃ N : ℕ → Fin d → ℂ, wedge n N = altWord ⊤ a := by
  classical
  refine ⟨fun i => if hi : i < n then Pi.single (a ⟨i,hi⟩) 1 else 0, ?_⟩
  rw [altWord_inverse_sum]
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin n)))
  let e : (⊤ : Subgroup (Equiv.Perm (Fin n))) ≃ Equiv.Perm (Fin n) :=
    { toFun := Subtype.val
      invFun := fun π => ⟨π, Subgroup.mem_top π⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  symm
  unfold wedge
  apply Fintype.sum_equiv e
  intro π
  change signC π.val • Pi.single (a ∘ π.val) 1 =
    signC π.val • pure (fun i => if hi : (π.val i).val < n then
      Pi.single (a ⟨(π.val i).val,hi⟩) 1 else 0)
  simp only [dite_eq_left (π.val _).isLt]
  congr 1
  exact (pure_single (a ∘ π.val)).symm

lemma coordinateProjection_pair {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x y : WordSpace n d) :
    dotProduct (coordinateProjection P x) y = dotProduct x (coordinateProjection P y) := by
  classical
  apply Finset.sum_congr rfl
  intro w hw
  simp only [coordinateProjection_apply]
  split_ifs <;> simp

lemma coordinateProjection_idempotent {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) :
    coordinateProjection P (coordinateProjection P x) = coordinateProjection P x := by
  classical
  ext w
  simp only [coordinateProjection_apply]
  split_ifs <;> rfl

lemma coordinateProjection_star {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) :
    star (coordinateProjection P x) = coordinateProjection P (star x) := by
  classical
  funext w
  simp only [Pi.star_apply, coordinateProjection_apply]
  split_ifs <;> simp

theorem split_column_nonzero {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) (hw : Function.Injective w) (Q : Fin d → Prop)
    (hQ : ∀ i, Q (w i) ↔ (e i).isLeft = true) :
    ∃ N : ℕ → Fin d → ℂ,
      dotProduct (wedge n N) (positionProduct e (altWord ⊤ (leftWord e w))
        (altWord ⊤ (rightWord e w))) ≠ 0 := by
  classical
  let P := fun v : Fin n → Fin d => ∀ i, Q (v i) ↔ (e i).isLeft = true
  let y := altWord (⊤ : Subgroup (Equiv.Perm (Fin n))) w
  let z := coordinateProjection P y
  have hf {m : ℕ} : fiberGroup (fun _ : Fin m => ()) = ⊤ := by
    apply Subgroup.ext
    intro g
    simp [fiberGroup]
  have hz : z = positionProduct e (altWord ⊤ (leftWord e w))
      (altWord ⊤ (rightWord e w)) := by
    change coordinateProjection P (altWord ⊤ w) = _
    rw [altWord_sector ⊤ w Q _ hQ, ← hf (m := n),
      altWord_fiber_split e (fun _ => ()) w]
    simp only [hf]
  have hz0 : z ≠ 0 := by
    intro hn
    have hh := congrFun hn w
    have he : z w = 1 := by
      change coordinateProjection P y w = 1
      rw [coordinateProjection_apply, ite_eq_left (show P w from hQ)]
      exact altWord_injective_base ⊤ w hw
    exact one_ne_zero (he.symm.trans hh)
  have hzr : star z = z := by
    change star (coordinateProjection P y) = _
    rw [coordinateProjection_star, altWord_real]
  obtain ⟨N,hN⟩ := wedge_base w
  refine ⟨N, ?_⟩
  rw [hN, ← hz]
  intro hn
  have hh : dotProduct z (star z) = 0 := by
    rw [hzr]
    change dotProduct (coordinateProjection P y) (coordinateProjection P y) = 0
    rw [coordinateProjection_pair, coordinateProjection_idempotent]
    exact hn
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact hz0 (dotProduct_self_star_eq_zero.mp hh)

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnRestriction
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Restriction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

lemma wedge_coordinateFlag {r h d : ℕ} (hr : r ≤ h) (ι : Fin h → Fin d) :
    wedge r (coordinateFlag ι) = altWord ⊤ (ι ∘ Fin.castLE hr) := by
  classical
  rw [altWord_inverse_sum]
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin r)))
  let e : (⊤ : Subgroup (Equiv.Perm (Fin r))) ≃ Equiv.Perm (Fin r) :=
    { toFun := Subtype.val
      invFun := fun π => ⟨π, Subgroup.mem_top π⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  symm
  unfold wedge
  apply Fintype.sum_equiv e
  intro π
  change signC π.val • Pi.single ((ι ∘ Fin.castLE hr) ∘ π.val) 1 =
    signC π.val • pure (fun i => coordinateFlag ι (π.val i).val)
  congr 1
  have he : (fun i : Fin r => coordinateFlag ι (π.val i).val) =
      fun i => Pi.single (ι (Fin.castLE hr (π.val i))) 1 := by
    funext i
    exact dite_eq_left (lt_of_lt_of_le (π.val i).isLt hr)
  rw [he, pure_single]
  rfl

lemma column_split_basis_nonzero {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    ∃ N : ℕ → Fin (A+B) → ℂ, dotProduct (wedge (a+b) N)
      (positionProduct finSumFinEquiv.symm
        (wedge a (coordinateFlag (Fin.castAdd B)))
        (wedge b (coordinateFlag (Fin.natAdd A)))) ≠ 0 := by
  classical
  let e : Fin (a+b) ≃ Fin a ⊕ Fin b := finSumFinEquiv.symm
  let w : Fin (a+b) → Fin (A+B) :=
    fun i => finSumFinEquiv (Sum.map (Fin.castLE ha) (Fin.castLE hb) (e i))
  have hw : Function.Injective w := by
    intro i j hij
    apply e.injective
    exact (Sum.map_injective.mpr ⟨Fin.castLE_injective ha, Fin.castLE_injective hb⟩)
      (finSumFinEquiv.injective hij)
  have hQ : ∀ i, (finSumFinEquiv.symm (w i)).isLeft = true ↔ (e i).isLeft = true := by
    intro i
    simp only [w, Equiv.symm_apply_apply]
    cases e i <;> rfl
  obtain ⟨N,hN⟩ := split_column_nonzero e w hw
    (fun j => (finSumFinEquiv.symm j).isLeft = true) hQ
  refine ⟨N, ?_⟩
  have hl : leftWord e w = Fin.castAdd B ∘ Fin.castLE ha := by
    funext i
    simp [leftWord, w]
  have hr : rightWord e w = Fin.natAdd A ∘ Fin.castLE hb := by
    funext i
    simp [rightWord, w]
  rw [wedge_coordinateFlag ha, wedge_coordinateFlag hb]
  rwa [hl,hr] at hN

theorem split_blocks_nonzero (ps : List (ℕ × ℕ)) (A B : ℕ)
    (ha : ∀ p ∈ ps, p.1 ≤ A) (hb : ∀ p ∈ ps, p.2 ≤ B) :
    ∃ N : ℕ → Fin (A+B) → ℂ,
      dotProduct (blocks (ps.map (fun p => p.1+p.2)) N)
        (positionProduct (splitPositions ps)
          (blocks (ps.map Prod.fst) (coordinateFlag (Fin.castAdd B)))
          (blocks (ps.map Prod.snd) (coordinateFlag (Fin.natAdd A)))) ≠ 0 := by
  let v := fun p : ℕ × ℕ =>
    positionProduct finSumFinEquiv.symm
      (wedge p.1 (coordinateFlag (Fin.castAdd B)))
      (wedge p.2 (coordinateFlag (Fin.natAdd A)))
  obtain ⟨L,hL,hp⟩ := common_flag_tensorList (fun p : ℕ × ℕ => p.1+p.2)
    (A+B) v ps (fun p hp => Nat.add_le_add (ha p hp) (hb p hp))
    (fun p hp => column_split_basis_nonzero (ha p hp) (hb p hp))
  refine ⟨fun i a => if hi : i < A+B then L ⟨i,hi⟩ a else 0, ?_⟩
  rw [blocks_eq_tensorList Prod.fst, blocks_eq_tensorList Prod.snd, tensorList_split]
  exact hp

lemma placed_blocks_in_range {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (N : ℕ → Fin d → ℂ) : blocks rs N ∈ (placedFlagMap e N).range := by
  refine ⟨⟨polytabloid ((enumerate rs).trans e),mem_cyclic _ _⟩, ?_⟩
  exact mapped_placed e hr hc N

lemma product_in_external_range {n a b d : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d))
    (x : WordSpace a d) (y : WordSpace b d) (hx : x ∈ F.range) (hy : y ∈ G.range) :
    positionProduct e x y ∈ (externalWordMap e F G).range := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  exact ⟨x ⊗ₜ[ℂ] y,externalWordMap_tmul e F G x y⟩

lemma external_range_restriction_support {n a b d : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} [ρ.IsIrreducible]
    {σ : Representation ℂ (Equiv.Perm (Fin a)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin b)) Z}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap σ (wordRep a d))
    (G : Representation.IntertwiningMap τ (wordRep b d))
    (x : WordSpace a d) (y : WordSpace b d) (hx : x ∈ F.range) (hy : y ∈ G.range)
    (f : Representation.IntertwiningMap ρ
      (cyclic (wordRep n d) (positionProduct e x y)).toRepresentation) (hf : f ≠ 0) :
    ∃ R : Representation.IntertwiningMap (ρ.comp (sumPermHom e))
      (externalTensor σ τ), R ≠ 0 := by
  exact cyclic_restriction_support ρ _ _ (sumPermHom e) (positionProduct e x y)
    (externalWordMap e F G) (product_in_external_range e F G x y hx hy) f hf

lemma placed_pair_support {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (N : ℕ → Fin d → ℂ) (u : WordSpace rs.sum d)
    (hN : dotProduct (blocks rs N) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep ((enumerate rs).trans e))
      (cyclic (wordRep rs.sum d) u).toRepresentation, F ≠ 0 := by
  apply specht_to_cyclic_of_pair ((enumerate rs).trans e)
    (fun i : Fin (μ.colLen 0) => N i.val) u
  rwa [mapped_placed e hr hc N]

theorem column_split_restriction (ps : List (ℕ × ℕ))
    (α β γ : YoungDiagram)
    (ea : Cells (ps.map Prod.fst) ≃ α.cells)
    (eb : Cells (ps.map Prod.snd) ≃ β.cells)
    (et : Cells (ps.map (fun p => p.1+p.2)) ≃ γ.cells)
    (hra : ∀ c, (ea c).val.1 = row c)
    (hrb : ∀ c, (eb c).val.1 = row c)
    (hrt : ∀ c, (et c).val.1 = row c)
    (hca : ∀ c c', (ea c).val.2 = (ea c').val.2 ↔ col c = col c')
    (hcb : ∀ c c', (eb c).val.2 = (eb c').val.2 ↔ col c = col c')
    (hct : ∀ c c', (et c).val.2 = (et c').val.2 ↔ col c = col c')
    (A B : ℕ) (ha : ∀ p ∈ ps, p.1 ≤ A) (hb : ∀ p ∈ ps, p.2 ≤ B) :
    ∃ F : Representation.IntertwiningMap
      ((spechtRep ((enumerate (ps.map (fun p => p.1+p.2))).trans et)).comp
        (sumPermHom (splitPositions ps)))
      (externalTensor (spechtRep ((enumerate (ps.map Prod.fst)).trans ea))
        (spechtRep ((enumerate (ps.map Prod.snd)).trans eb))), F ≠ 0 := by
  let a := (enumerate (ps.map Prod.fst)).trans ea
  let b := (enumerate (ps.map Prod.snd)).trans eb
  let t := (enumerate (ps.map (fun p => p.1+p.2))).trans et
  let Na : ℕ → Fin (A+B) → ℂ := coordinateFlag (Fin.castAdd (n := A) B)
  let Nb : ℕ → Fin (A+B) → ℂ := coordinateFlag (Fin.natAdd (m := B) A)
  let u := positionProduct (splitPositions ps)
    (blocks (ps.map Prod.fst) Na) (blocks (ps.map Prod.snd) Nb)
  obtain ⟨N,hN⟩ := split_blocks_nonzero ps A B ha hb
  obtain ⟨F,hF⟩ := placed_pair_support et hrt hct N u hN
  let := specht_irreducible t
  exact external_range_restriction_support (splitPositions ps)
    (placedFlagMap ea Na) (placedFlagMap eb Nb) _ _
    (placed_blocks_in_range ea hra hca Na) (placed_blocks_in_range eb hrb hcb Nb) F hF

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SignedInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma signRestrictionMap_ne_zero {n a b : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin a)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin b)) Z}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ))
    (hf : f ≠ 0) : signRestrictionMap e f ≠ 0 := by
  intro h
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun H => H x) h

theorem signed_external_cyclic_support {n a b d : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (τ : Representation ℂ (Equiv.Perm (Fin b)) Z)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬ A z))
    (F : Representation.IntertwiningMap σ (signTwist (cyclic (wordRep a d) v).toRepresentation))
    (G : Representation.IntertwiningMap τ (signTwist (cyclic (wordRep b d) u).toRepresentation))
    (hF : Function.Injective F) (hG : Function.Injective G)
    (f : Representation.IntertwiningMap (ρ.comp (sumPermHom e)) (externalTensor σ τ))
    (hf : f ≠ 0) :
    ∃ H : Representation.IntertwiningMap (signTwist ρ)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, H ≠ 0 := by
  exact external_cyclic_support (signTwist ρ) (signTwist σ) (signTwist τ) e v u A hv hu
    (signDomainMap F) (signDomainMap G) hF hG (signRestrictionMap e f)
    (signRestrictionMap_ne_zero e f hf)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Extras. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma cyclic_positionProduct_eq {n a b d : ℕ} (e e' : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (w : WordSpace b d) :
    cyclic (wordRep n d) (positionProduct e v w) =
      cyclic (wordRep n d) (positionProduct e' v w) := by
  have h : wordRep n d (e'.trans e.symm) (positionProduct e' v w) =
      positionProduct e v w := by
    ext x
    change v (fun i => x ((e'.trans e.symm) (e'.symm (Sum.inl i)))) *
      w (fun i => x ((e'.trans e.symm) (e'.symm (Sum.inr i)))) = _
    
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [← h, cyclic_translate_eq]

lemma restriction_equal_degrees {n a b n' a' b' : ℕ} {α β γ : YoungDiagram}
    (ha : a = a') (hb : b = b') (hn : n = n')
    (ta : Tableau a α) (tb : Tableau b β) (tt : Tableau n γ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ((spechtRep tt).comp (sumPermHom e))
      (externalTensor (spechtRep ta) (spechtRep tb))) (hF : F ≠ 0) :
    ∃ (sa : Tableau a' α) (sb : Tableau b' β) (st : Tableau n' γ)
      (e' : Fin n' ≃ Fin a' ⊕ Fin b'),
      ∃ G : Representation.IntertwiningMap ((spechtRep st).comp (sumPermHom e'))
        (externalTensor (spechtRep sa) (spechtRep sb)), G ≠ 0 := by
  subst a'; subst b'; subst n'
  exact ⟨ta,tb,tt,e,F,hF⟩

theorem even_rows_restriction (r D : ℕ) (θ : YoungDiagram) (hθ : θ.card = 2*r)
    (he : ∀ i, Even (θ.rowLen i)) (hd : θ.colLen 0 ≤ 2*D) :
    ∃ (α β : YoungDiagram) (ta : Tableau r α) (tb : Tableau r β)
      (tt : Tableau (2*r) θ) (e : Fin (2*r) ≃ Fin r ⊕ Fin r),
      α.colLen 0 ≤ D ∧ β.colLen 0 ≤ D ∧
      ShortColumns.RowParity (r%2) α ∧ ShortColumns.RowParity (r%2) β ∧
      ∃ F : Representation.IntertwiningMap ((spechtRep tt).comp (sumPermHom e))
        (externalTensor (spechtRep ta) (spechtRep tb)), F ≠ 0 := by
  obtain ⟨ps,ht,hp,ha,hb,hpa,hpb⟩ := Columns.even_rows_allocation r D θ hθ he hd
  let α := Columns.columnShape (ps.map Prod.fst)
  let β := Columns.columnShape (ps.map Prod.snd)
  obtain ⟨ea,hra,hca⟩ := Columns.columnShape_placement (ps.map Prod.fst)
  obtain ⟨eb,hrb,hcb⟩ := Columns.columnShape_placement (ps.map Prod.snd)
  have heθ := Columns.columnShape_placement (ps.map (fun p => p.1+p.2))
  rw [ht] at heθ
  obtain ⟨et,hrt,hct⟩ := heθ
  obtain ⟨F,hF⟩ := FlagColumns.column_split_restriction ps α β θ ea eb et
    hra hrb hrt hca hcb hct D D (fun p h => (hp p h).1) (fun p h => (hp p h).2)
  have hn : (ps.map (fun p => p.1+p.2)).sum = 2*r :=
    (Columns.placed_card et).symm.trans hθ
  obtain ⟨ta,tb,tt,e,G,hG⟩ := restriction_equal_degrees ha hb hn _ _ _ _ F hF
  refine ⟨α,β,ta,tb,tt,e,?_,?_,hpa,hpb,G,hG⟩
  · exact Columns.placed_height ea hra D (by
      intro h hh; obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hh; exact (hp p hp').1)
  · exact Columns.placed_height eb hrb D (by
      intro h hh; obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hh; exact (hp p hp').2)

namespace ShortColumns

theorem two_extras (r d : ℕ) (s₁ s₂ : Tableau r (shape (r/2) (r%2)))
    (φ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
      (shape (r/2) (r%2)).colLen 0) → Fin d)
    (ψ : Fin ((shape (r/2) (r%2)).transpose.transpose.colLen 0 *
      (shape (r/2) (r%2)).transpose.colLen 0) → Fin d)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (A : Fin d → Prop) (hA : ∀ x, A (φ x)) (hB : ∀ x, ¬ A (ψ x))
    (e : Fin (2*r) ≃ Fin r ⊕ Fin r)
    (η : YoungDiagram) (hη : η.card = 2*r) (t : Tableau (2*r) η)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r) d) (positionProduct e
        (letterLift φ (rowColumnWord s₁))
        (letterLift ψ (rowColumnWord (transposeTableau s₂))))).toRepresentation,
      F ≠ 0 := by
  obtain ⟨α,β,ta,tb,tt,e₀,ha,hb,hpa,hpb,f,hf⟩ :=
    even_rows_restriction r 4 η.transpose (by rwa [transpose_card])
      (by simpa only [YoungDiagram.rowLen_transpose] using he)
      (by simpa only [YoungDiagram.colLen_transpose] using hd)
  obtain ⟨Fa,hFa⟩ := one_extra_lifted r d s₁ φ hφ α ta hpa ha
  obtain ⟨Fb,hFb⟩ := one_extra_transpose_lifted r d s₂ ψ hψ β tb hpb hb
  have hs := signed_external_cyclic_support (spechtRep tt) (spechtRep ta) (spechtRep tb)
    e₀ (letterLift φ (rowColumnWord s₁)) (letterLift ψ (rowColumnWord (transposeTableau s₂))) A
    (letterLift_mem_alphabet A φ hA _) (letterLift_mem_alphabet (fun x => ¬ A x) ψ hB _)
    Fa Fb hFa hFb f hf
  rw [cyclic_positionProduct_eq e₀ e] at hs
  obtain ⟨H,hH⟩ := hs
  have hEq := specht_sign_transpose_uts t
  change Nonempty ((spechtRep t).Equiv
    (signTwist (spechtSub (transposeTableau t)).toRepresentation)) at hEq
  rw [spechtSub_tableau_independent (transposeTableau t) tt] at hEq
  obtain ⟨E⟩ := hEq
  refine ⟨H.comp E.toIntertwiningMap, ?_⟩
  intro hz
  apply hH
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := E.surjective x
  exact congrArg (fun K => K y) hz

end ShortColumns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Extras. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

lemma bandNELetter_injective {M b δ : ℕ} (hM : 4 ≤ M) :
    Function.Injective (@bandNELetter M b δ hM) :=
  pairLetterMap_injective _ _ (bandExtraLetter_injective _) (Fin.castLE_injective _)

lemma bandSWLetter_injective {M b δ : ℕ} (hM : 4 ≤ M) :
    Function.Injective (@bandSWLetter M b δ hM) :=
  pairLetterMap_injective _ _ ((Fin.castLE_injective _).comp (Fin.cast_injective _))
    (bandExtraLetter_injective _)

lemma candidateExtrasWord_eq {M b δ r : ℕ} (hM : 4 ≤ M)
    (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidateExtrasWord hM s₁ s₂ = positionProduct (candidateExtraSplit r)
      (letterLift (bandNELetter hM) (rowColumnWord s₁))
      (letterLift (bandSWLetter hM) (rowColumnWord (transposeTableau s₂))) := by
  unfold candidateExtrasWord rowColumnWord bandNELetter bandSWLetter
  rw [letterLift_wordTensor, letterLift_wordTensor, ← letterLift_comp]
  rw [polytabloid_doubleTranspose]

lemma bandNELetter_high {M b δ : ℕ} (hM : 4 ≤ M) (x) :
    2 ≤ ((finProdFinEquiv.symm (@bandNELetter M b δ hM x)).1).val := by
  simpa only [bandNELetter, pairLetterMap, Equiv.symm_apply_apply, bandLongRowLetter]
    using bandExtraLetter_high hM _ (finProdFinEquiv.symm x).1

lemma bandSWLetter_low {M b δ : ℕ} (hM : 4 ≤ M) (x) :
    ((finProdFinEquiv.symm (@bandSWLetter M b δ hM x)).1).val < 2 := by
  simp only [bandSWLetter, pairLetterMap, Equiv.symm_apply_apply,
    Function.comp_apply, bandShortRowLetter, Fin.val_castLE, Fin.val_cast]
  have h := (finProdFinEquiv.symm x).1.isLt
  have he := congrArg (fun μ : YoungDiagram => μ.colLen 0)
    (YoungDiagram.transpose_transpose (ShortColumns.shape b δ))
  have hh := ShortColumns.height_le b δ
  omega

theorem candidateExtrasWord_support {M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (η : YoungDiagram) (hη : η.card = 2*r) (t : Tableau (2*r) η)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r) _) (candidateExtrasWord hM s₁ s₂)).toRepresentation,
      F ≠ 0 := by
  rw [candidateExtrasWord_eq]
  have hb : r/2 = b := by omega
  have hδ' : r%2 = δ := by omega
  have H := ShortColumns.two_extras r
    ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0)
  rw [hb,hδ'] at H
  exact H s₁ s₂ (bandNELetter hM) (bandSWLetter hM)
    (bandNELetter_injective hM) (bandSWLetter_injective hM)
    (fun a => 2 ≤ (finProdFinEquiv.symm a).1.val)
    (bandNELetter_high hM) (fun a => Nat.not_le.mpr (bandSWLetter_low hM a))
    (candidateExtraSplit r) η hη t he hd

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_FlagDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flag Detection. -/

section

noncomputable section
namespace Saxl

lemma cyclic_support_tableau {n d : ℕ} {μ : YoungDiagram}
    (s t : Tableau n μ) (u : WordSpace n d)
    (h : ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0 := by
  change ∃ f : Representation.IntertwiningMap (spechtSub s).toRepresentation
    (cyclic (wordRep n d) u).toRepresentation, f ≠ 0 at h
  rw [spechtSub_tableau_independent s t] at h
  exact h

lemma cyclic_support_relabel_iff {n m d : ℕ} {μ : YoungDiagram}
    (e : Fin n ≃ Fin m) (s : Tableau n μ) (t : Tableau m μ) (u : WordSpace n d) :
    (∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep m d) (relabelWord e u)).toRepresentation, f ≠ 0) ↔
    (∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  change (∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (wordRep n d e u)).toRepresentation, f ≠ 0) ↔ _
  rw [cyclic_action_eq]
  constructor
  · exact cyclic_support_tableau t s u
  · exact cyclic_support_tableau s t u

lemma relabelWord_alphabet {n m d : ℕ} (e : Fin n ≃ Fin m)
    (P : Fin d → Prop) (u : WordSpace n d) (hu : u ∈ alphabetSub n d P) :
    relabelWord e u ∈ alphabetSub m d P := by
  intro w hw
  obtain ⟨i,hi⟩ := hw
  apply hu
  exact ⟨e.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩

end Saxl
namespace Saxl.FlagColumns
open Columns

lemma blocks_congr_word {d : ℕ} (rs : List ℕ) (N Q : ℕ → Fin d → ℂ)
    (w : Fin rs.sum → Fin d) (h : ∀ i k, N i (w k) = Q i (w k)) :
    blocks rs N w = blocks rs Q w := by
  classical
  simp only [blocks, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pure]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact h _ _

theorem columns_necessary {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (s : Tableau rs.sum μ) (u : WordSpace rs.sum d)
    (P : Fin d → Prop) (hu : u ∈ alphabetSub rs.sum d P)
    (hs : ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep rs.sum d) u).toRepresentation, f ≠ 0) :
    ∃ (g : Equiv.Perm (Fin rs.sum)) (Q : ℕ → Fin d → ℂ),
      (∀ i a, ¬P a → Q i a = 0) ∧
      dotProduct (blocks rs Q) (relabelWord g u) ≠ 0 := by
  classical
  let t := (enumerate rs).trans e
  obtain ⟨f,hf⟩ := cyclic_support_tableau s t u hs
  obtain ⟨g,L,hL⟩ := dual_polytabloid_necessary t u f hf
  rw [(wordMap L).isIntertwining, wordPair_move] at hL
  let N : ℕ → Fin d → ℂ := fun i a => if hi : i < μ.colLen 0 then L ⟨i,hi⟩ a else 0
  have hN : wordMap L (polytabloid t) = blocks rs N := by
    convert (mapped_placed e hr hc N) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    funext i a
    change L i a = if hi : (i : ℕ) < μ.colLen 0 then L ⟨i,hi⟩ a else 0
    simp only [dite_eq_left i.isLt]
  rw [hN] at hL
  let Q : ℕ → Fin d → ℂ := fun i a => if P a then N i a else 0
  refine ⟨g⁻¹,Q,fun i a ha => ite_eq_right ha,?_⟩
  have hu' := relabelWord_alphabet g⁻¹ P u hu
  have he : dotProduct (blocks rs Q) (relabelWord g⁻¹ u) =
      dotProduct (blocks rs N) (relabelWord g⁻¹ u) := by
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hz : relabelWord g⁻¹ u w = 0
    · simp only [hz,mul_zero]
    · congr 1
      apply blocks_congr_word
      intro i k
      exact ite_eq_left (by
        by_contra hh
        exact hz (hu' w ⟨k,hh⟩))
  rw [he]
  exact hL

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_BandContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Contractions. -/

section

noncomputable section
namespace Saxl

lemma positionProduct_alphabet {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (P : Fin d → Prop) (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d P) (hu : u ∈ alphabetSub b d P) :
    positionProduct e v u ∈ alphabetSub n d P := by
  intro w hw
  obtain ⟨i,hi⟩ := hw
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    change v (leftWord e w) * u (rightWord e w) = 0
    rw [hv _ ⟨j,hi⟩, zero_mul]
  | inr j =>
    change v (leftWord e w) * u (rightWord e w) = 0
    rw [hu _ ⟨j,hi⟩, mul_zero]

end Saxl
namespace UniversalTensorSquare
open Saxl
open Saxl.FlagColumns

lemma bandSWLetter_high {M b δ : ℕ} (hM : 4 ≤ M) (x) :
    2 ≤ ((finProdFinEquiv.symm (@bandSWLetter M b δ hM x)).2).val := by
  simpa only [bandSWLetter, pairLetterMap, Equiv.symm_apply_apply, bandLongColLetter]
    using bandExtraLetter_high hM _ (finProdFinEquiv.symm x).2

lemma candidateExtrasWord_alphabet {M b δ r : ℕ} (hM : 4 ≤ M)
    (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidateExtrasWord hM s₁ s₂ ∈ alphabetSub (2*r) _
      (fun a => ¬candidatePathAlphabet M b δ a) := by
  rw [candidateExtrasWord_eq]
  apply positionProduct_alphabet
  · apply letterLift_mem_alphabet
    intro a ha
    exact Nat.not_lt.mpr (bandNELetter_high hM a) ha.1
  · apply letterLift_mem_alphabet
    intro a ha
    exact Nat.not_lt.mpr (bandSWLetter_high hM a) ha.2

theorem candidateExtrasWord_contraction_oai {M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (η : YoungDiagram) (hη : η.card = 2*r)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8)
    (rs : List ℕ) (hn : rs.sum = 2*r) (e : Columns.Cells rs ≃ η.cells)
    (er : ∀ c, (e c).val.1 = Columns.row c)
    (ec : ∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c') :
    ∃ (g : Equiv.Perm (Fin rs.sum))
      (Q : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ),
      (∀ i a, candidatePathAlphabet M b δ a → Q i a = 0) ∧
      dotProduct (blocks rs Q) (relabelWord g
        (relabelWord (finCongr hn).symm (candidateExtrasWord hM s₁ s₂))) ≠ 0 := by
  let u := canonicalTableau η hη
  have hs := candidateExtrasWord_support hM hδ hr s₁ s₂ η hη u he hd
  let v : Tableau rs.sum η := (Columns.enumerate rs).trans e
  have hs' := (cyclic_support_relabel_iff (finCongr hn).symm u v
    (candidateExtrasWord hM s₁ s₂)).mpr hs
  obtain ⟨g,Q,hQ,hp⟩ := columns_necessary e er ec v _
    (fun a => ¬candidatePathAlphabet M b δ a)
    (relabelWord_alphabet _ _ _ (candidateExtrasWord_alphabet hM s₁ s₂)) hs'
  exact ⟨g,Q,fun i a ha => hQ i a (not_not_intro ha),hp⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.candidateExtrasWord_contraction_oai := @OAI.UniversalTensorSquare.candidateExtrasWord_contraction_oai
