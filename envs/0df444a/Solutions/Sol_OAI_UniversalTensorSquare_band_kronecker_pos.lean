-- Prove2me | solution 1 for OAI.UniversalTensorSquare.band_kronecker_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:39.37433+00:00
-- url     : https://prove2.me/submissions/b5a3f151-963b-4285-ae70-217f5ca0b183

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_UniversalTensorSquare_candidateExtrasWord_contraction
import Theorems.Thm_OAI_UniversalTensorSquare_candidatePathWord_contraction
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_kronecker_pos_of_subdiagram

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

lemma altWord_move {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (r : G) :
    altWord G (a ∘ (r : Equiv.Perm (Fin n))) =
      signC (r : Equiv.Perm (Fin n)) • altWord G a := by
  classical
  let := Fintype.ofFinite G
  have he : Pi.single (a ∘ (r : Equiv.Perm (Fin n))) (1 : ℂ) =
      wordRep n d (r⁻¹ : G) (Pi.single a 1) := by
    rw [wordRep_single]
    rfl
  unfold altWord
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, Finset.smul_sum]
  apply (Equiv.sum_comp (Equiv.mulRight r) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC ((g*r : G) : Equiv.Perm (Fin n)) •
    wordRep n d (((g*r : G) : Equiv.Perm (Fin n)) * (r : Equiv.Perm (Fin n))⁻¹) (Pi.single a 1) = _
  simp only [Subgroup.coe_mul, map_mul, mul_inv_cancel_right, smul_smul]
  rw [mul_comm (signC (g : Equiv.Perm (Fin n)))]

/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
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

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/

lemma altWord_sector_rotated {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop) (r : G)
    (ha : ∀ i, Q ((a ∘ (r : Equiv.Perm (Fin n))) i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      signC (r : Equiv.Perm (Fin n)) • altWord (G ⊓ sectorGroup D) (a ∘ (r : Equiv.Perm (Fin n))) := by
  have hh := altWord_sector G (a ∘ (r : Equiv.Perm (Fin n))) Q D ha
  rw [altWord_move, map_smul] at hh
  rw [← hh, smul_smul, signC_mul_self, one_smul]

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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordRelabel
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Relabel. -/

section

noncomputable section
namespace Saxl
open scoped TensorProduct

lemma coordinateProjection_wordTensor {n a b : ℕ}
    (P : (Fin n → Fin a) → Prop) (Q : (Fin n → Fin b) → Prop)
    (x : WordSpace n a) (y : WordSpace n b) :
    coordinateProjection (fun w => P (splitLeft w) ∧ Q (splitRight w))
        (wordTensor n a b (x ⊗ₜ[ℂ] y)) =
      wordTensor n a b (coordinateProjection P x ⊗ₜ[ℂ] coordinateProjection Q y) := by
  classical
  ext w
  simp only [coordinateProjection_apply, wordTensor_tmul]
  by_cases hp : P (splitLeft w) <;> by_cases hq : Q (splitRight w) <;> simp [hp,hq]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Allocation. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma prefixFill_le (f : ℕ → ℕ) (r i : ℕ) : prefixFill f r i ≤ f i := min_le_left _ _

lemma prefixFill_antitone {f : ℕ → ℕ} (hf : Antitone f) (r : ℕ) :
    Antitone (prefixFill f r) := by
  intro i j hij
  apply min_le_min (hf hij)
  apply Nat.sub_le_sub_left
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

lemma prefixFill_sum (f : ℕ → ℕ) (r k : ℕ) :
    (∑ i ∈ Finset.range k, prefixFill f r i) = min r (∑ i ∈ Finset.range k, f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, prefixFill]
    omega

lemma columnCut_le (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f) :
    columnCut μ f hf ≤ μ := fun _ h => (Finset.mem_filter.mp h).1

lemma columnCut_colLen (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f)
    (hb : ∀ i, f i ≤ μ.colLen i) (i : ℕ) : (columnCut μ f hf).colLen i = f i := by
  have H (j : ℕ) : j < (columnCut μ f hf).colLen i ↔ j < f i := by
    rw [← YoungDiagram.mem_iff_lt_colLen]
    change ((j,i) ∈ μ.cells.filter _) ↔ _
    simp only [Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_colLen.mpr (h.trans_le (hb i)),h⟩⟩
  have h₁ := H ((columnCut μ f hf).colLen i)
  have h₂ := H (f i)
  omega

lemma columnCut_card (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f)
    (hb : ∀ i, f i ≤ μ.colLen i) :
    (columnCut μ f hf).card = ∑ i ∈ Finset.range (μ.rowLen 0), f i := by
  have hw : (columnCut μ f hf).rowLen 0 ≤ μ.rowLen 0 := by
    by_contra hh
    have he := columnCut_le μ f hf (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hh))
    exact Nat.lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp he)
  rw [← transpose_card, ← rowPrefix_eq_card _ (by simpa using hw)]
  simp only [rowPrefix, YoungDiagram.rowLen_transpose, columnCut_colLen μ f hf hb]

lemma extraCapacity_antitone (μ : YoungDiagram) (d q : ℕ) :
    Antitone (extraCapacity μ d q) := by
  intro i j hij
  dsimp only [extraCapacity]
  split_ifs with hj hi hi
  · exact Nat.div_le_div_right (Nat.sub_le_sub_right (μ.colLen_anti i j hij) d)
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

lemma extraCapacity_sum (μ : YoungDiagram) (d q : ℕ) :
    (∑ i ∈ Finset.range (μ.rowLen 0), extraCapacity μ d q i) = bandCapacity μ d q := by
  classical
  have hs : ∀ i, μ.rowLen 0 ≤ i → μ.colLen i = 0 := by
    intro i hi
    simpa only [YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose] using
      rowLen_zero_of_height_le μ.transpose (by simpa using hi)
  unfold bandCapacity
  by_cases hq : q ≤ μ.rowLen 0
  · rw [← Finset.sum_subset (Finset.range_mono hq) (by
      intro i hi hni
      simp only [Finset.mem_range] at hni
      simp [extraCapacity, hni])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [extraCapacity, Finset.mem_range.mp hi, ite_true, if_true]
  · have hh : μ.rowLen 0 ≤ q := by omega
    rw [← Finset.sum_subset (Finset.range_mono hh) (by
      intro i hi hni
      simp only [Finset.mem_range, not_lt] at hni
      simp only [hs i hni, Nat.zero_sub, Nat.zero_div])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [extraCapacity, (Finset.mem_range.mp hi).trans_le hh, ite_true, if_true]

lemma pathCapacity_sum (μ : YoungDiagram) (d : ℕ) :
    (∑ i ∈ Finset.range (μ.rowLen 0), min d (μ.colLen i)) = rowPrefix μ d := by
  rw [← rowTruncate_card, ← transpose_card]
  have hw : (rowTruncate μ d).rowLen 0 ≤ μ.rowLen 0 := by
    rw [rowTruncate_rowLen]
    split_ifs <;> omega
  rw [← rowPrefix_eq_card _ (by simpa using hw)]
  simp only [rowPrefix, YoungDiagram.rowLen_transpose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Nat.le_antisymm
  · by_contra hn
    have hh : ((rowTruncate μ d).colLen i,i) ∈ rowTruncate μ d :=
      mem_rowTruncate.mpr ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by omega), by omega⟩
    exact Nat.lt_irrefl _ (YoungDiagram.mem_iff_lt_colLen.mp hh)
  · by_contra hn
    have hh : (min d (μ.colLen i),i) ∈ rowTruncate μ d :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have ht := mem_rowTruncate.mp hh
    have hc := YoungDiagram.mem_iff_lt_colLen.mp ht.1
    omega

theorem band_subdiagram_allocation (lam : YoungDiagram) (K r d q : ℕ)
    (hK : K ≤ rowPrefix lam d) (hclear : d*q+7+d ≤ K)
    (hr : r ≤ bandCapacity lam d q) :
    ∃ π η μ : YoungDiagram,
      μ ≤ lam ∧ π.card = K ∧ η.card = 2*r ∧ μ.card = K+2*r ∧
      (∀ i, μ.colLen i = π.colLen i + η.colLen i) ∧
      (∀ i, π.colLen i ≤ d) ∧
      (∀ i, Even (η.colLen i)) ∧ η.rowLen 0 ≤ q ∧
      (∀ i, 0 < η.colLen i → π.colLen i = d) := by
  let p := prefixFill (fun i => min d (lam.colLen i)) K
  let e := fun i => 2*prefixFill (extraCapacity lam d q) r i
  have hpanti : Antitone p := prefixFill_antitone (fun _ _ h => min_le_min le_rfl (lam.colLen_anti _ _ h)) K
  have heanti : Antitone e := fun _ _ h => Nat.mul_le_mul_left 2
    (prefixFill_antitone (extraCapacity_antitone lam d q) r h)
  have hpbound (i : ℕ) : p i ≤ min d (lam.colLen i) := prefixFill_le _ _ _
  have hebound (i : ℕ) : e i ≤ lam.colLen i-d := by
    have hh := Nat.mul_le_mul_left 2 (prefixFill_le (extraCapacity lam d q) r i)
    have hc : extraCapacity lam d q i ≤ (lam.colLen i-d)/2 := by
      dsimp [extraCapacity]
      split_ifs <;> omega
    dsimp only [e]
    omega
  have hpb (i : ℕ) : p i ≤ lam.colLen i := (hpbound i).trans (min_le_right _ _)
  have heb (i : ℕ) : e i ≤ lam.colLen i := (hebound i).trans (Nat.sub_le _ _)
  have hpos (i : ℕ) (hi : 0 < e i) : i < q ∧ d ≤ lam.colLen i := by
    have hh := prefixFill_le (extraCapacity lam d q) r i
    have hc : 0 < extraCapacity lam d q i := by dsimp [e] at hi; omega
    dsimp only [extraCapacity] at hc
    split_ifs at hc with h
    · exact ⟨h, by omega⟩
    · omega
  have hsbound (i : ℕ) : p i+e i ≤ lam.colLen i := by
    by_cases hi : 0 < e i
    · have hh := (hpos i hi).2
      have hp := (hpbound i).trans (min_le_left _ _)
      have he := hebound i
      omega
    · have hp := hpb i
      omega
  let π := columnCut lam p hpanti
  let η := columnCut lam e heanti
  let μ := columnCut lam (fun i => p i+e i) (fun _ _ h => Nat.add_le_add (hpanti h) (heanti h))
  have hπ (i) : π.colLen i = p i := columnCut_colLen _ _ _ hpb i
  have hη (i) : η.colLen i = e i := columnCut_colLen _ _ _ heb i
  have hμ (i) : μ.colLen i = p i+e i := columnCut_colLen _ _ _ hsbound i
  have hpSum : (∑ i ∈ Finset.range (lam.rowLen 0), p i) = K := by
    rw [prefixFill_sum, pathCapacity_sum, min_eq_left hK]
  have heSum : (∑ i ∈ Finset.range (lam.rowLen 0), e i) = 2*r := by
    rw [← Finset.mul_sum, prefixFill_sum, extraCapacity_sum, min_eq_left hr]
  refine ⟨π,η,μ,columnCut_le _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (columnCut_card _ _ _ hpb).trans hpSum
  · exact (columnCut_card _ _ _ heb).trans heSum
  · refine (columnCut_card lam (fun i => p i+e i)
      (fun _ _ h => Nat.add_le_add (hpanti h) (heanti h)) hsbound).trans ?_
    rw [Finset.sum_add_distrib, hpSum, heSum]
  · intro i
    rw [hμ,hπ,hη]
  · intro i
    exact (hπ i).le.trans ((hpbound i).trans (min_le_left _ _))
  · intro i
    rw [hη]
    exact even_two_mul _
  · by_contra hh
    have h : 0 < η.colLen q := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hh))
    rw [hη] at h
    exact Nat.lt_irrefl _ (hpos q h).1
  · intro i hi
    rw [hπ]
    rw [hη] at hi
    obtain ⟨hiq,hid⟩ := hpos i hi
    have hs : (∑ j ∈ Finset.range i, min d (lam.colLen j)) ≤ i*d := by
      simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using
        (Finset.sum_le_sum (s := Finset.range i) (fun j _ => min_le_left d (lam.colLen j)))
    have hmul : (i+1)*d ≤ q*d := Nat.mul_le_mul_right d hiq
    dsimp only [p, prefixFill]
    rw [min_eq_left hid]
    apply min_eq_left
    apply Nat.le_sub_of_add_le
    have hc : q*d ≤ K := by simpa only [Nat.mul_comm] using (show d*q ≤ K by omega)
    calc d + (∑ j ∈ Finset.range i, min d (lam.colLen j)) ≤ d+i*d := Nat.add_le_add_left hs _
      _ = (i+1)*d := by ring
      _ ≤ q*d := hmul
      _ ≤ K := hc

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_PathGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Path Geometry. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

theorem path_endpoint_clearance (M b δ : ℕ) (hM : 4 ≤ M)
    (q : Fin (2*M-1)) (hle : 4 ≤ q.val) (hri : q.val+4 < 2*M-1) :
    2 ≤ (candidatePathCell M b δ q).1 ∧
      2 ≤ (candidatePathCell M b δ q).2 := by
  simp only [candidatePathCell]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp only
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Clearance. -/

section

noncomputable section
namespace Saxl

lemma altWord_support {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a w : Fin n → Fin d) (hw : altWord G a w ≠ 0) :
    ∃ g : G, w = a ∘ g.val := by
  classical
  let := Fintype.ofFinite G
  rw [altWord_inverse_sum] at hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw
  obtain ⟨g, hg, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine ⟨g, ?_⟩
  by_contra he
  exact hn (by rw [Pi.single_eq_of_ne he, mul_zero])

end Saxl

namespace UniversalTensorSquare
open Saxl

lemma candidateRotateRow_small {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hr : 2 ≤ x.val.1)
    (ht : M-2 ≤ x.val.1+x.val.2) :
    (candidateRotateRow M b δ hM x).val.2 < 2 := by
  have hx := mem_candidate.mp x.property
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
    else (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)) < 2
  rw [ite_eq_right (by omega)]
  rcases x with ⟨⟨i,j⟩,hx0⟩
  dsimp only at *
  split_ifs <;> omega

lemma candidateRotateCol_small {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hc : 2 ≤ x.val.2)
    (ht : M-2 ≤ x.val.1+x.val.2) :
    (candidateRotateCol M b δ hM x).val.1 < 2 := by
  apply candidateRotateRow_small hM (candidateSwap M b δ x) hc
  change M-2 ≤ x.val.2+x.val.1
  omega

lemma candidateBandRow_seed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (rightWord (candidateCutPositions t)
      (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n))) i).val =
        (candidateRotateRow M b δ hM (candidateBandTableau t i)).val.2 := by
  simp only [rightWord, Function.comp_apply, rowWord, transposeTableau,
    candidateRotateRowPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

lemma candidateBandCol_seed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (rightWord (candidateCutPositions t)
      (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n))) i).val =
        (candidateRotateCol M b δ hM (candidateBandTableau t i)).val.1 := by
  simp only [rightWord, Function.comp_apply, rowWord,
    candidateRotateColPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem candidateBandRow_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) → Fin ((candidate M b δ).transpose.colLen 0))
    (hw : candidateBandRow hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (hi : 2 ≤ (candidateBandTableau t i).val.1) : (w i).val < 2 := by
  obtain ⟨g,rfl⟩ := altWord_support _ _ w hw
  have hg := g.property i
  change (candidateBandTableau t (g.val i)).val.1 = (candidateBandTableau t i).val.1 at hg
  change (rightWord (candidateCutPositions t) _ (g.val i)).val < 2
  rw [candidateBandRow_seed]
  exact candidateRotateRow_small hM _ (by rwa [hg]) (candidateBandTableau_outside t _)

theorem candidateBandCol_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) → Fin ((candidate M b δ).colLen 0))
    (hw : candidateBandCol hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (hi : 2 ≤ (candidateBandTableau t i).val.2) : (w i).val < 2 := by
  obtain ⟨g,rfl⟩ := altWord_support _ _ w hw
  have hg := g.property i
  change (candidateBandTableau t (g.val i)).val.2 = (candidateBandTableau t i).val.2 at hg
  change (rightWord (candidateCutPositions t) _ (g.val i)).val < 2
  rw [candidateBandCol_seed]
  exact candidateRotateCol_small hM _ (by rwa [hg]) (candidateBandTableau_outside t _)

theorem candidateBandWord_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : candidateBandWord hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (hi : 2 ≤ (candidateBandTableau t i).val.1)
    (hj : 2 ≤ (candidateBandTableau t i).val.2) :
    candidatePathAlphabet M b δ (w i) := by
  rw [candidateBandWord, wordTensor_tmul] at hw
  exact ⟨candidateBandRow_clearance hM t _ (mul_ne_zero_iff.mp hw).1 i hi,
    candidateBandCol_clearance hM t _ (mul_ne_zero_iff.mp hw).2 i hj⟩

theorem candidateBandWord_path_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : candidateBandWord hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (q : Fin (2*M-1)) (hq : (candidateBandTableau t i).val = candidatePathCell M b δ q)
    (hle : 4 ≤ q.val) (hri : q.val+4 < 2*M-1) : candidatePathAlphabet M b δ (w i) := by
  obtain ⟨ha,hb⟩ := path_endpoint_clearance M b δ hM q hle hri
  apply candidateBandWord_clearance hM t w hw i <;> rwa [hq]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CandidateShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Shuffle. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateRotateRow_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRotateRow M b δ hM x).val.2 =
      if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (if x.val.2 < M-2-x.val.1 then x.val.2+2
        else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
      else (if x.val.2 < M-2-x.val.1 then x.val.2+2
        else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2) := rfl

lemma candidateRowShuffle_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRowShuffle M b δ hM x).val.2 =
      if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (Equiv.swap (M+b-1) (M+b+δ-1) x.val.2) else x.val.2 := by
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)
      else (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)) = _
  split_ifs <;> rfl

private lemma separatedFirstRowNumber (M b δ j : ℕ) (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hj : M-2 ≤ j) (hj' : j < M+b+δ) :
    Equiv.swap (M-1) (M+b-1)
      (if Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j) < M-2 then
        Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)+2
      else if Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j) < M-2+2 then
        Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)-(M-2)
      else Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)) =
      if j = M-2 then 0 else if j = M+b+δ-1 then 1
      else if j < M+b-1 then j else j+1 := by
  have hs₀ : Equiv.swap (M-1) (M+b-1) (M-2) = M-2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have ht₀ : Equiv.swap (M+b-1) (M+b+δ-1) (M-2) = M-2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  by_cases hj₀ : j = M-2
  · subst j
    rw [ite_eq_left rfl, ht₀, hs₀, ite_eq_right (by omega), ite_eq_left (by omega), Nat.sub_self]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [ite_eq_right hj₀]
  by_cases hj₁ : j = M+b+δ-1
  · subst j
    rw [Equiv.swap_apply_right, Equiv.swap_apply_right, ite_eq_left rfl,
      ite_eq_right (by omega), ite_eq_left (by omega)]
    have he : M-1-(M-2) = 1 := by omega
    rw [he]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [ite_eq_right hj₁]
  let l := Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)
  have hl : M-2 ≤ l := by
    dsimp only [l]
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have hl₀ : l ≠ M-2 := by
    intro he
    have he' := congrArg (fun z => Equiv.swap (M+b-1) (M+b+δ-1) (Equiv.swap (M-1) (M+b-1) z)) he
    simp only [l, Equiv.swap_apply_self, hs₀, ht₀] at he'
    exact hj₀ he'
  have hl₁ : l ≠ M-1 := by
    intro he
    have he' := congrArg (fun z => Equiv.swap (M+b-1) (M+b+δ-1) (Equiv.swap (M-1) (M+b-1) z)) he
    simp only [l, Equiv.swap_apply_self, Equiv.swap_apply_left] at he'
    exact hj₁ he'
  change Equiv.swap (M-1) (M+b-1) (if l < M-2 then l+2 else if l < M-2+2 then l-(M-2) else l) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp only [l]
  rw [Equiv.swap_apply_self]
  by_cases he : j = M+b-1
  · subst j
    rw [Equiv.swap_apply_left, ite_eq_right (by omega)]
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne he hj₁, ite_eq_left (by omega)]

lemma candidateSeparatedRow_band (M b δ : ℕ) (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (hx : M-2 ≤ x.val.1+x.val.2) :
    (candidateSeparatedRow M b δ hM x).val.2 =
      if x.val.1 = 0 then
        if x.val.2 = M-2 then 0 else if x.val.2 = M+b+δ-1 then 1
        else if x.val.2 < M+b-1 then x.val.2 else x.val.2+1
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2 := by
  change (candidateRotateRow M b δ hM (candidateRowShuffle M b δ hM x)).val.2 = _
  rw [candidateRotateRow_col, candidateRowShuffle_row, candidateRowShuffle_col]
  have hm := mem_candidate.mp x.property
  rcases x with ⟨⟨i,j⟩,hm0⟩
  dsimp only at *
  by_cases hi : i = 0
  · subst i
    simp only [ite_true, if_true, Nat.sub_zero]
    exact separatedFirstRowNumber M b δ j hM hδ (by omega) (by omega)
  · simp only [hi, ite_false, if_false]
    rw [ite_eq_right (show ¬j < M-2-i by omega)]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Split. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateBandParts_cell {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (x : Fin (2*M-1) ⊕ (Fin r ⊕ Fin r)) :
    (candidateBandTableau t ((candidateBandPartsEquiv hM t s₁ s₂).symm x)).val =
      (candidatePartsCell M b δ hM
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr s₁ s₂)) x)).val.val := by
  change ((candidateComplementEquiv t)
    (((candidateComplementEquiv t).symm)
      (candidatePartsCell M b δ hM _))).val.val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma candidateBandSplit_path {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (q : Fin (2*M-1)) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl q))).val =
      candidatePathCell M b δ q :=
  candidateBandParts_cell hM t s₁ s₂ (Sum.inl q)

lemma candidateBandSplit_NE {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (i : Fin r) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inl i))))).val =
        candidateNECell M (s₁ i) := by
  simpa only [candidateBandSplit, candidateExtraSplit, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, candidatePartsCell,
    Sum.map_inl, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
    using candidateBandParts_cell hM t s₁ s₂ (Sum.inr (Sum.inl i))

lemma candidateBandSplit_SW {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (i : Fin r) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inr i))))).val =
        (candidateNECell M (s₂ i)).swap := by
  simpa only [candidateBandSplit, candidateExtraSplit, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, candidatePartsCell,
    Sum.map_inl, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
    using candidateBandParts_cell hM t s₁ s₂ (Sum.inr (Sum.inr i))

lemma candidatePathCell_swap {M b δ : ℕ} (hM : 4 ≤ M)
    (i : Fin (2*M-1)) :
    (candidatePathCell M b δ i).swap = candidatePathCell M b δ i.rev := by
  have hi := i.isLt
  unfold candidatePathCell
  simp only [Fin.val_rev]
  split_ifs <;> simp only [Prod.swap_prod_mk, Prod.mk.injEq] <;> omega

lemma candidateParts_row_sectors {M b δ : ℕ} (hM : 4 ≤ M)
    (x y : CandidateBandParts M b δ)
    (hrow : (candidatePartsCell M b δ hM x).val.val.1 =
      (candidatePartsCell M b δ hM y).val.val.1) :
    (Sum.isLeft x = true ↔ Sum.isLeft y = true) ↔
      ((candidatePartsCell M b δ hM x).val.val ∈ attachmentNE M b δ ↔
        (candidatePartsCell M b δ hM y).val.val ∈ attachmentNE M b δ) := by
  have H (q : Fin (2*M-1)) (z : (ShortColumns.shape b δ).cells) :
      (candidatePathCell M b δ q).1 ≠ (candidateNECell M z).2 := by
    have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
    have hq := q.isLt
    unfold candidatePathCell candidateNECell
    split_ifs <;> dsimp only <;> omega
  have N (z : (ShortColumns.shape b δ).cells) :
      (candidateNECell M z).swap ∉ attachmentNE M b δ := by
    have hz := candidateNECell_mem hM z
    simp only [mem_attachmentNE, candidateNECell, Prod.swap_prod_mk] at hz ⊢
    omega
  rcases x with x | (x | x) <;> rcases y with y | (y | y) <;>
    dsimp only [candidatePartsCell] at hrow ⊢
  all_goals try simp only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true,
    true_iff, false_iff, (pathCell_not_attachment M b δ hM _).1,
    candidateNECell_mem hM, N, iff_self]
  all_goals try first | exact False.elim (H _ _ hrow) |
    exact False.elim (H _ _ hrow.symm) | trivial
  all_goals have hx := (ShortColumns.mem_shape b δ x.val.1 x.val.2).mp x.property
  all_goals have hy := (ShortColumns.mem_shape b δ y.val.1 y.val.2).mp y.property
  all_goals dsimp only [candidateNECell, Prod.swap] at hrow
  all_goals omega

lemma candidateBandRow_sector_eq {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t i).val.1) ⊓
      sectorGroup (fun i => (candidateBandTableau t i).val ∈ attachmentNE M b δ) =
    fiberGroup (fun i => (candidateBandTableau t i).val.1) ⊓
      sectorGroup (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true) := by
  apply Subgroup.ext
  intro g
  change ((∀ i, (candidateBandTableau t (g i)).val.1 = (candidateBandTableau t i).val.1) ∧ _) ↔
    ((∀ i, (candidateBandTableau t (g i)).val.1 = (candidateBandTableau t i).val.1) ∧ _)
  apply and_congr_right
  intro hg
  change (∀ i, _ ↔ _) ↔ (∀ i, _ ↔ _)
  apply forall_congr'
  intro i
  let E := candidateBandPartsEquiv hM t s₁ s₂
  let f := Equiv.sumCongr (Equiv.refl (Fin (2*M-1))) (Equiv.sumCongr s₁ s₂)
  have H (i) : (candidateBandTableau t i).val =
      (candidatePartsCell M b δ hM (f (E i))).val.val := by
    rw [← candidateBandParts_cell hM t s₁ s₂, Equiv.symm_apply_apply]
  have hh := candidateParts_row_sectors hM (f (E (g i))) (f (E i)) (by
    rw [← H, ← H]; exact hg i)
  dsimp only at *
  simp_rw [H]
  have hside (j) : (f (E j)).isLeft = ((candidateBandSplit hM t s₁ s₂) j).isLeft := by
    dsimp only [candidateBandSplit, Equiv.trans_apply, f]
    cases E j <;> rfl
  rw [hside, hside] at hh
  exact hh.symm

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Groups. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidatePartsCell_swap {M b δ : ℕ} (hM : 4 ≤ M) (x : CandidateBandParts M b δ) :
    (candidatePartsCell M b δ hM (candidatePartsSwap x)).val.val =
      (candidatePartsCell M b δ hM x).val.val.swap := by
  rcases x with q | (z | z)
  · exact (candidatePathCell_swap hM q).symm
  · rfl
  · exact Prod.swap_swap _ |>.symm

lemma candidateParts_col_sectors {M b δ : ℕ} (hM : 4 ≤ M)
    (x y : CandidateBandParts M b δ)
    (hcol : (candidatePartsCell M b δ hM x).val.val.2 =
      (candidatePartsCell M b δ hM y).val.val.2) :
    (Sum.isLeft x = true ↔ Sum.isLeft y = true) ↔
      ((candidatePartsCell M b δ hM x).val.val.swap ∈ attachmentNE M b δ ↔
        (candidatePartsCell M b δ hM y).val.val.swap ∈ attachmentNE M b δ) := by
  have H := candidateParts_row_sectors hM (candidatePartsSwap x) (candidatePartsSwap y)
    (by simpa only [candidatePartsCell_swap, Prod.fst_swap] using hcol)
  rw [candidatePartsCell_swap, candidatePartsCell_swap] at H
  have he (z : CandidateBandParts M b δ) : (candidatePartsSwap z).isLeft = z.isLeft := by
    rcases z with z | (z | z) <;> rfl
  simpa only [he] using H

lemma candidateBandCol_sector_eq {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t i).val.2) ⊓
      sectorGroup (fun i => (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ) =
    fiberGroup (fun i => (candidateBandTableau t i).val.2) ⊓
      sectorGroup (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true) := by
  apply Subgroup.ext
  intro g
  change ((∀ i, (candidateBandTableau t (g i)).val.2 = (candidateBandTableau t i).val.2) ∧ _) ↔
    ((∀ i, (candidateBandTableau t (g i)).val.2 = (candidateBandTableau t i).val.2) ∧ _)
  apply and_congr_right
  intro hg
  change (∀ i, _ ↔ _) ↔ (∀ i, _ ↔ _)
  apply forall_congr'
  intro i
  let E := candidateBandPartsEquiv hM t s₁ s₂
  let f := Equiv.sumCongr (Equiv.refl (Fin (2*M-1))) (Equiv.sumCongr s₁ s₂)
  have H (i) : (candidateBandTableau t i).val =
      (candidatePartsCell M b δ hM (f (E i))).val.val := by
    rw [← candidateBandParts_cell hM t s₁ s₂, Equiv.symm_apply_apply]
  have hh := candidateParts_col_sectors hM (f (E (g i))) (f (E i)) (by
    rw [← H, ← H]; exact hg i)
  dsimp only at *
  simp_rw [H]
  have hside (j) : (f (E j)).isLeft = ((candidateBandSplit hM t s₁ s₂) j).isLeft := by
    dsimp only [candidateBandSplit, Equiv.trans_apply, f]
    cases E j <;> rfl
  rw [hside, hside] at hh
  exact hh.symm

lemma candidateBand_extra_sector {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (p : (ℕ × ℕ) → ℕ) (hp : p = Prod.fst ∨ p = Prod.snd) :
    fiberGroup (fun i => p (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val) =
    fiberGroup (fun i => p (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val) ⊓
      sectorGroup (fun i => (candidateExtraSplit r i).isLeft = true) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg, ?_⟩
    intro i
    have H := hg i
    obtain ⟨j,hj⟩ := (candidateExtraSplit r).symm.surjective i
    obtain ⟨k,hk⟩ := (candidateExtraSplit r).symm.surjective (g i)
    change (candidateExtraSplit r (g i)).isLeft = true ↔ (candidateExtraSplit r i).isLeft = true
    rw [← hk, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change p (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr (g i)))).val =
      p (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val at H
    rw [← hk, ← hj] at H
    cases k with
    | inl k =>
      cases j with
      | inl j => rfl
      | inr j =>
        rw [candidateBandSplit_NE, candidateBandSplit_SW] at H
        have hx := (ShortColumns.mem_shape b δ (s₁ k).val.1 (s₁ k).val.2).mp (s₁ k).property
        have hy := (ShortColumns.mem_shape b δ (s₂ j).val.1 (s₂ j).val.2).mp (s₂ j).property
        rcases hp with rfl | rfl <;> dsimp only [candidateNECell, Prod.swap] at H <;> omega
    | inr k =>
      cases j with
      | inr j => rfl
      | inl j =>
        rw [candidateBandSplit_SW, candidateBandSplit_NE] at H
        have hx := (ShortColumns.mem_shape b δ (s₂ k).val.1 (s₂ k).val.2).mp (s₂ k).property
        have hy := (ShortColumns.mem_shape b δ (s₁ j).val.1 (s₁ j).val.2).mp (s₁ j).property
        rcases hp with rfl | rfl <;> dsimp only [candidateNECell, Prod.swap] at H <;> omega
  · exact inf_le_left

lemma candidateBandRow_NE_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inl i))))).val.1) =
      columnGroup (transposeTableau s₁) := by
  simp_rw [candidateBandSplit_NE]
  rfl

lemma candidateBandRow_SW_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inr i))))).val.1) =
      columnGroup s₂ := by
  simp_rw [candidateBandSplit_SW]
  apply Subgroup.ext
  intro g
  change (∀ i, M-1+(s₂ (g i)).val.2 = M-1+(s₂ i).val.2) ↔ (∀ i, (s₂ (g i)).val.2 = (s₂ i).val.2)
  simp only [Nat.add_left_cancel_iff]

lemma candidateBandCol_NE_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inl i))))).val.2) =
      columnGroup s₁ := by
  simp_rw [candidateBandSplit_NE]
  apply Subgroup.ext
  intro g
  change (∀ i, M-1+(s₁ (g i)).val.2 = M-1+(s₁ i).val.2) ↔ (∀ i, (s₁ (g i)).val.2 = (s₁ i).val.2)
  simp only [Nat.add_left_cancel_iff]

lemma candidateBandCol_SW_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inr i))))).val.2) =
      columnGroup (transposeTableau s₂) := by
  simp_rw [candidateBandSplit_SW]
  rfl

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Seeds. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateSeparatedRow_extra {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (hx : M-2 ≤ x.val.1+x.val.2) :
    2 ≤ (candidateSeparatedRow M b δ hM x).val.2 ↔ x.val ∈ attachmentNE M b δ := by
  rw [candidateSeparatedRow_band M b δ hM hδ x hx]
  have hm := mem_candidate.mp x.property
  rcases x with ⟨⟨i,j⟩,hm0⟩
  simp only [mem_attachmentNE]
  dsimp only at *
  split_ifs <;> omega

lemma candidateBandRowShuffle_cell {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    candidateBandTableau t ((candidateBandRowShuffle hM t).val i) =
      candidateRowShuffle M b δ hM (candidateBandTableau t i) := by
  exact congrArg (fun x : candidateComplement M b δ => x.val)
    ((candidateComplementEquiv t).apply_symm_apply
      (candidateComplementRowShuffle M b δ hM (candidateComplementEquiv t i)))

lemma candidateBandRowSeed_val {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (candidateBandRowSeed hM t i).val =
      (candidateSeparatedRow M b δ hM (candidateBandTableau t i)).val.2 := by
  rw [candidateBandRowSeed, Function.comp_apply, candidateBandRow_seed,
    candidateBandRowShuffle_cell]
  rfl

lemma candidateBandRowSeed_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    2 ≤ (candidateBandRowSeed hM t i).val ↔
      (candidateBandTableau t i).val ∈ attachmentNE M b δ := by
  rw [candidateBandRowSeed_val]
  exact candidateSeparatedRow_extra hM hδ _ (candidateBandTableau_outside t i)

theorem candidateBandRow_project_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val ∈ attachmentNE M b δ) (candidateBandRow hM t) =
    signC (candidateBandRowShuffle hM t).val •
      altWord (fiberGroup (fun i => (candidateBandTableau t i).val.1) ⊓
        sectorGroup (fun i => (candidateBandTableau t i).val ∈ attachmentNE M b δ))
          (candidateBandRowSeed hM t) := by
  exact altWord_sector_rotated _ _ (fun a => 2 ≤ a.val) _
    (candidateBandRowShuffle hM t) (candidateBandRowSeed_extra hM hδ t)

lemma candidateBandColShuffle_cell {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    candidateBandTableau t ((candidateBandColShuffle hM t).val i) =
      candidateColShuffle M b δ hM (candidateBandTableau t i) := by
  exact congrArg (fun x : candidateComplement M b δ => x.val)
    ((candidateComplementEquiv t).apply_symm_apply
      (candidateComplementColShuffle M b δ hM (candidateComplementEquiv t i)))

lemma candidateBandColSeed_val {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (candidateBandColSeed hM t i).val =
      (candidateSeparatedRow M b δ hM (candidateSwap M b δ (candidateBandTableau t i))).val.2 := by
  rw [candidateBandColSeed, Function.comp_apply, candidateBandCol_seed,
    candidateBandColShuffle_cell]
  simp only [candidateRotateCol, candidateColShuffle, candidateSeparatedRow,
    Equiv.trans_apply]
  rfl

lemma candidateBandColSeed_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    2 ≤ (candidateBandColSeed hM t i).val ↔
      (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ := by
  rw [candidateBandColSeed_val]
  apply candidateSeparatedRow_extra hM hδ
  have h := candidateBandTableau_outside t i
  change M-2 ≤ (candidateBandTableau t i).val.2+(candidateBandTableau t i).val.1
  omega

theorem candidateBandCol_project_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ) (candidateBandCol hM t) =
    signC (candidateBandColShuffle hM t).val •
      altWord (fiberGroup (fun i => (candidateBandTableau t i).val.2) ⊓
        sectorGroup (fun i => (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ))
          (candidateBandColSeed hM t) := by
  exact altWord_sector_rotated _ _ (fun a => 2 ≤ a.val) _
    (candidateBandColShuffle hM t) (candidateBandColSeed_extra hM hδ t)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandLetters
attribute [-simp] _root_.OAI.Saxl.Balance.appendShortCells_left _root_.OAI.Saxl.Balance.appendShortCells_right
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

lemma candidateSeparatedRow_NE {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (z : (ShortColumns.shape b δ).cells)
    (hx : x.val = candidateNECell M z) :
    (candidateSeparatedRow M b δ hM x).val.2 =
      if z.val.2 < b then M-1+z.val.2 else M+z.val.2 := by
  classical
  have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
  rw [candidateSeparatedRow_band M b δ hM hδ x (by rw [hx]; dsimp [candidateNECell]; omega), hx]
  dsimp +instances only [candidateNECell]
  split_ifs <;> omega

lemma candidateSeparatedRow_SW {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (z : (ShortColumns.shape b δ).cells)
    (hx : x.val = (candidateNECell M z).swap) :
    (candidateSeparatedRow M b δ hM x).val.2 = z.val.1 := by
  classical
  have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
  rw [candidateSeparatedRow_band M b δ hM hδ x (by rw [hx]; dsimp [candidateNECell]; omega), hx]
  dsimp +instances only [candidateNECell, Prod.swap]
  split_ifs <;> omega

lemma candidateBandRowSeed_NE {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    leftWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t)) =
      bandExtraLetter (le_of_eq (candidateRowAlphabet_size hM).symm) ∘
        rowWord (transposeTableau s₁) := by
  funext i
  apply Fin.ext
  rw [leftWord, rightWord, candidateBandRowSeed_val]
  exact candidateSeparatedRow_NE hM hδ _ (s₁ i) (candidateBandSplit_NE hM t s₁ s₂ i)

lemma candidateBandRowSeed_SW {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    rightWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t)) =
      Fin.castLE (show (ShortColumns.shape b δ).colLen 0 ≤
        (candidate M b δ).transpose.colLen 0 from
        (ShortColumns.height_le b δ).trans (by rw [candidateRowAlphabet_size hM]; omega)) ∘
          rowWord s₂ := by
  funext i
  apply Fin.ext
  rw [rightWord, rightWord, candidateBandRowSeed_val]
  exact candidateSeparatedRow_SW hM hδ _ (s₂ i) (candidateBandSplit_SW hM t s₁ s₂ i)

lemma candidateBandColSeed_NE {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    leftWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t)) =
      Fin.castLE (show (ShortColumns.shape b δ).colLen 0 ≤
        (candidate M b δ).colLen 0 from
        (ShortColumns.height_le b δ).trans (by rw [candidateColAlphabet_size hM]; omega)) ∘
          rowWord s₁ := by
  funext i
  apply Fin.ext
  rw [leftWord, rightWord, candidateBandColSeed_val]
  apply candidateSeparatedRow_SW hM hδ _ (s₁ i)
  change (candidateBandTableau t _).val.swap = _
  rw [candidateBandSplit_NE]

lemma candidateBandColSeed_SW {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    rightWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t)) =
      bandExtraLetter (le_of_eq (candidateColAlphabet_size hM).symm) ∘
        rowWord (transposeTableau s₂) := by
  funext i
  apply Fin.ext
  rw [rightWord, rightWord, candidateBandColSeed_val]
  apply candidateSeparatedRow_NE hM hδ _ (s₂ i)
  change (candidateBandTableau t _).val.swap = _
  rw [candidateBandSplit_SW, Prod.swap_swap]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Factor. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

lemma candidateBandRow_extras {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    altWord (fiberGroup (fun i => (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val.1))
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t)) =
      positionProduct (candidateExtraSplit r)
        (letterLift (bandLongRowLetter hM) (polytabloid (transposeTableau s₁)))
        (letterLift (bandShortRowLetter hM) (polytabloid s₂)) := by
  rw [candidateBand_extra_sector hM t s₁ s₂ Prod.fst (Or.inl rfl), altWord_fiber_split,
    candidateBandRow_NE_group, candidateBandRow_SW_group,
    candidateBandRowSeed_NE hM hδ, candidateBandRowSeed_SW hM hδ]
  simp only [polytabloid_eq_altWord, letterLift_altWord]
  rfl

lemma candidateBandCol_extras {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    altWord (fiberGroup (fun i => (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val.2))
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t)) =
      positionProduct (candidateExtraSplit r)
        (letterLift (bandShortColLetter hM) (polytabloid s₁))
        (letterLift (bandLongColLetter hM) (polytabloid (transposeTableau s₂))) := by
  rw [candidateBand_extra_sector hM t s₁ s₂ Prod.snd (Or.inr rfl), altWord_fiber_split,
    candidateBandCol_NE_group, candidateBandCol_SW_group,
    candidateBandColSeed_NE hM hδ, candidateBandColSeed_SW hM hδ]
  simp only [polytabloid_eq_altWord, letterLift_altWord]
  rfl

lemma candidateBandRow_factor {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val ∈ attachmentNE M b δ) (candidateBandRow hM t) =
    signC (candidateBandRowShuffle hM t).val •
      positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathRow hM t s₁ s₂)
        (positionProduct (candidateExtraSplit r)
          (letterLift (bandLongRowLetter hM) (polytabloid (transposeTableau s₁)))
          (letterLift (bandShortRowLetter hM) (polytabloid s₂))) := by
  rw [candidateBandRow_project_extra hM hδ, candidateBandRow_sector_eq hM t s₁ s₂,
    altWord_fiber_split, candidateBandRow_extras hM hδ]
  rfl

lemma candidateBandCol_factor {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ) (candidateBandCol hM t) =
    signC (candidateBandColShuffle hM t).val •
      positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathCol hM t s₁ s₂)
        (positionProduct (candidateExtraSplit r)
          (letterLift (bandShortColLetter hM) (polytabloid s₁))
          (letterLift (bandLongColLetter hM) (polytabloid (transposeTableau s₂)))) := by
  rw [candidateBandCol_project_extra hM hδ, candidateBandCol_sector_eq hM t s₁ s₂,
    altWord_fiber_split, candidateBandCol_extras hM hδ]
  rfl

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Separated. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

theorem candidateBandPattern_factor {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection (candidateBandPattern t) (candidateBandWord hM t) =
      (signC (candidateBandRowShuffle hM t).val * signC (candidateBandColShuffle hM t).val) •
        positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathWord hM t s₁ s₂)
          (candidateExtrasWord hM s₁ s₂) := by
  change coordinateProjection (fun w =>
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ)
      (splitLeft w) ∧
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ)
      (splitRight w)) _ = _
  rw [candidateBandWord, coordinateProjection_wordTensor
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ)
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ),
    candidateBandRow_factor hM hδ t s₁ s₂, candidateBandCol_factor hM hδ t s₁ s₂,
    TensorProduct.smul_tmul_smul, map_smul, wordTensor_positionProduct,
    wordTensor_positionProduct]
  rfl

lemma candidateNECell_swap_not_mem {M b δ : ℕ} (hM : 4 ≤ M)
    (z : (ShortColumns.shape b δ).cells) :
    (candidateNECell M z).swap ∉ attachmentNE M b δ := by
  have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
  rw [mem_attachmentNE]
  dsimp only [candidateNECell, Prod.swap]
  omega

lemma candidateBandWord_sector_iff {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : candidateBandWord hM t w ≠ 0) :
    wordSector (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true)
      (candidatePathAlphabet M b δ) w ↔ candidateBandPattern t w := by
  have hw' := hw
  rw [candidateBandWord, wordTensor_tmul] at hw'
  have hr := (mul_ne_zero_iff.mp hw').1
  have hc := (mul_ne_zero_iff.mp hw').2
  have H (i : Fin (candidateBandSize t)) :
      (candidatePathAlphabet M b δ (w i) ↔
        ((candidateBandSplit hM t s₁ s₂) i).isLeft = true) ↔
      ((2 ≤ (splitLeft w i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ) ∧
       (2 ≤ (splitRight w i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ)) := by
    obtain ⟨p,rfl⟩ := (candidateBandSplit hM t s₁ s₂).symm.surjective i
    cases p with
    | inl q =>
      rw [candidateBandSplit_path]
      simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,
        (pathCell_not_attachment M b δ hM q).1,
        (pathCell_not_attachment M b δ hM q).2, iff_false,
        not_le, candidatePathAlphabet, splitLeft, splitRight]
    | inr j =>
      obtain ⟨p,rfl⟩ := (candidateExtraSplit r).symm.surjective j
      cases p with
      | inl z =>
        have hc' := candidateBandCol_clearance hM t _ hc
          ((candidateBandSplit hM t s₁ s₂).symm
            (Sum.inr ((candidateExtraSplit r).symm (Sum.inl z)))) (by
          rw [candidateBandSplit_NE]
          dsimp only [candidateNECell]
          omega)
        rw [candidateBandSplit_NE]
        simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,
          candidateNECell_mem hM, candidateNECell_swap_not_mem hM, iff_true]
        change (¬ ((splitLeft w _).val < 2 ∧ (splitRight w _).val < 2)) ↔
          (2 ≤ (splitLeft w _).val ∧ ¬2 ≤ (splitRight w _).val)
        omega
      | inr z =>
        have hr' := candidateBandRow_clearance hM t _ hr
          ((candidateBandSplit hM t s₁ s₂).symm
            (Sum.inr ((candidateExtraSplit r).symm (Sum.inr z)))) (by
          rw [candidateBandSplit_SW]
          dsimp only [candidateNECell, Prod.swap]
          omega)
        rw [candidateBandSplit_SW]
        simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,
          Prod.swap_swap, candidateNECell_mem hM, candidateNECell_swap_not_mem hM, iff_true]
        change (¬ ((splitLeft w _).val < 2 ∧ (splitRight w _).val < 2)) ↔
          (¬2 ≤ (splitLeft w _).val ∧ 2 ≤ (splitRight w _).val)
        omega
  change (∀ i, _) ↔ ((∀ i, _) ∧ ∀ i, _)
  exact (forall_congr' H).trans forall_and

theorem candidateBandWord_separated {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection
        (wordSector (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true)
          (candidatePathAlphabet M b δ)) (candidateBandWord hM t) =
      (signC (candidateBandRowShuffle hM t).val * signC (candidateBandColShuffle hM t).val) •
        positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathWord hM t s₁ s₂)
          (candidateExtrasWord hM s₁ s₂) := by
  classical
  rw [← candidateBandPattern_factor hM hδ t s₁ s₂]
  ext w
  simp only [coordinateProjection_apply]
  by_cases hw : candidateBandWord hM t w = 0
  · simp only [hw, ite_self]
  · rw [candidateBandWord_sector_iff hM t s₁ s₂ w hw]

end UniversalTensorSquare
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
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split Flag. -/

section

noncomputable section
namespace Saxl.FlagColumns

lemma coordinateProjection_pair {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x y : WordSpace n d) :
    dotProduct (coordinateProjection P x) y = dotProduct x (coordinateProjection P y) := by
  classical
  apply Finset.sum_congr rfl
  intro w hw
  simp only [coordinateProjection_apply]
  split_ifs <;> simp

end Saxl.FlagColumns
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

end Saxl
namespace Saxl.FlagColumns
open Columns

theorem columns_sufficient {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (s : Tableau rs.sum μ) (u : WordSpace rs.sum d) (N : ℕ → Fin d → ℂ)
    (h : dotProduct (blocks rs N) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep rs.sum d) u).toRepresentation, f ≠ 0 := by
  apply cyclic_support_tableau ((enumerate rs).trans e) s u
  apply specht_to_cyclic_of_pair _ (fun i a => N i.val a) u
  rwa [mapped_placed e hr hc N]

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

lemma relabelWord_trans {n m k d : ℕ} (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k)
    (v : WordSpace n d) : relabelWord f (relabelWord e v) = relabelWord (e.trans f) v := rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_NoMixedColumns
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! No Mixed Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

lemma wedge_apply_det {r d : ℕ} (N : ℕ → Fin d → ℂ) (w : Fin r → Fin d) :
    wedge r N w = (Matrix.of (fun i j : Fin r => N i.val (w j))).det := by
  classical
  simp only [wedge, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    pure, Matrix.det_apply', Matrix.of_apply, signC]
  rfl

theorem wedge_split_of_zero {a b d : ℕ}
    (L N Q : ℕ → Fin d → ℂ) (w : Fin (a+b) → Fin d)
    (hN : ∀ i : Fin a, L i.val = N i.val)
    (hQ : ∀ i : Fin b, L (a+i.val) = Q i.val)
    (hz : ∀ (i : Fin b) (j : Fin a), Q i.val (w (Fin.castAdd b j)) = 0) :
    wedge (a+b) L w = wedge a N (leftWord finSumFinEquiv.symm w) *
      wedge b Q (rightWord finSumFinEquiv.symm w) := by
  classical
  rw [wedge_apply_det, wedge_apply_det, wedge_apply_det]
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b))]
  let A : Matrix (Fin a) (Fin a) ℂ := fun i j => N i.val (w (Fin.castAdd b j))
  let B : Matrix (Fin a) (Fin b) ℂ := fun i j => N i.val (w (Fin.natAdd a j))
  let D : Matrix (Fin b) (Fin b) ℂ := fun i j => Q i.val (w (Fin.natAdd a j))
  have hm : (Matrix.of (fun i j : Fin (a+b) => L i.val (w j))).submatrix
      (finSumFinEquiv : Fin a ⊕ Fin b → Fin (a+b)) finSumFinEquiv =
      Matrix.fromBlocks A B 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · exact congrFun (hN i) _
    · exact congrFun (hN i) _
    · exact (congrFun (hQ i) _).trans (hz i j)
    · exact congrFun (hQ i) _
  rw [hm, Matrix.det_fromBlocks_zero₂₁]
  rfl

lemma joinedFlag_right {D d : ℕ} (N Q : ℕ → Fin D → ℂ) (i : ℕ) :
    joinedFlag d N Q (d+i) = Q i := by
  simp [joinedFlag]

theorem joinedFlag_column_factor {a b d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ha : a ≤ d) (hb : b ≠ 0 → a = d)
    (hQ : ∀ i c, P c → Q i c = 0) (w : Fin (a+b) → Fin D)
    (hw : b ≠ 0 → ∀ i : Fin a, P (w (Fin.castAdd b i))) :
    wedge (a+b) (joinedFlag d N Q) w =
      wedge a N (leftWord finSumFinEquiv.symm w) *
        wedge b Q (rightWord finSumFinEquiv.symm w) := by
  apply wedge_split_of_zero
  · intro i
    exact ite_eq_left (i.isLt.trans_le ha)
  · intro i
    have hb' : b ≠ 0 := by have hi := i.isLt; omega
    rw [hb hb']
    exact joinedFlag_right N Q i.val
  · intro i j
    have hb' : b ≠ 0 := by have hi := i.isLt; omega
    exact hQ i.val _ (hw hb' j)

theorem blocks_factor_of_clearSlots {d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ps : List (ℕ × ℕ))
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hQ : ∀ i c, P c → Q i c = 0)
    (w : Fin (ps.map (fun p => p.1+p.2)).sum → Fin D) (hw : clearSlots P ps w) :
    blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q) w =
      positionProduct (splitPositions ps) (blocks (ps.map Prod.fst) N)
        (blocks (ps.map Prod.snd) Q) w := by
  rw [blocks_eq_tensorList Prod.fst, blocks_eq_tensorList Prod.snd, tensorList_split,
    blocks_eq_tensorList (fun p : ℕ × ℕ => p.1+p.2)]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    have hl := joinedFlag_column_factor N Q P (ha (a,b) (by simp))
      (hb (a,b) (by simp)) hQ (leftWord finSumFinEquiv.symm w) hw.1
    have hr := ih (fun p hp => ha p (by simp [hp]))
      (fun p hp => hb p (by simp [hp])) (rightWord finSumFinEquiv.symm w) hw.2
    change wedge (a+b) (joinedFlag d N Q) _ * _ =
      (wedge a N _ * wedge b Q _) * _
    erw [hl,hr]
    rfl

theorem blocks_pair_factor_of_clearSlots {d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ps : List (ℕ × ℕ))
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hQ : ∀ i c, P c → Q i c = 0)
    (z : WordSpace (ps.map (fun p => p.1+p.2)).sum D)
    (hz : ∀ w, z w ≠ 0 → clearSlots P ps w) :
    dotProduct (blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q)) z =
      dotProduct (positionProduct (splitPositions ps) (blocks (ps.map Prod.fst) N)
        (blocks (ps.map Prod.snd) Q)) z := by
  apply Finset.sum_congr rfl
  intro w hw
  by_cases he : z w = 0
  · simp only [he, mul_zero]
  · rw [blocks_factor_of_clearSlots N Q P ps ha hb hQ w (hz w he)]

lemma blocks_alphabet {D : ℕ} (rs : List ℕ) (N : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (hN : ∀ i c, ¬P c → N i c = 0) :
    blocks rs N ∈ alphabetSub rs.sum D P := by
  classical
  intro w hw
  obtain ⟨i,hi⟩ := hw
  simp only [blocks, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro π hπ
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hN _ _ hi)

theorem band_contraction_factor {d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ps : List (ℕ × ℕ))
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hN : ∀ i c, ¬P c → N i c = 0) (hQ : ∀ i c, P c → Q i c = 0)
    (z : WordSpace (ps.map (fun p => p.1+p.2)).sum D)
    (hz : ∀ w, z w ≠ 0 → clearSlots P ps w)
    (v : WordSpace (ps.map Prod.fst).sum D) (u : WordSpace (ps.map Prod.snd).sum D)
    (c : ℂ)
    (hsep : coordinateProjection
        (wordSector (fun i => ((splitPositions ps) i).isLeft = true) P) z =
      c • positionProduct (splitPositions ps) v u) :
    dotProduct (blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q)) z =
      c * (dotProduct (blocks (ps.map Prod.fst) N) v *
        dotProduct (blocks (ps.map Prod.snd) Q) u) := by
  classical
  rw [blocks_pair_factor_of_clearSlots N Q P ps ha hb hQ z hz]
  let f := positionProduct (splitPositions ps) (blocks (ps.map Prod.fst) N)
    (blocks (ps.map Prod.snd) Q)
  let S := wordSector (fun i => ((splitPositions ps) i).isLeft = true) P
  have hf : f ∈ coordinateSub _ _ S := positionProduct_sector (splitPositions ps) P _ _
    (blocks_alphabet _ N P hN)
    (blocks_alphabet _ Q (fun a => ¬P a) (fun i a h => hQ i a (not_not.mp h)))
  have he : coordinateProjection S f = f := by
    funext w
    rw [coordinateProjection_apply]
    split_ifs with h
    · rfl
    · exact (hf w h).symm
  change dotProduct f z = _
  rw [← he, coordinateProjection_pair, hsep]
  rw [dotProduct_smul, smul_eq_mul, positionProduct_pair]

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Gluing. -/

section

noncomputable section
namespace Saxl.FlagColumns

lemma clearSlots_of_columnsAway {D K : ℕ} (P : Fin D → Prop)
    (ps : List (ℕ × ℕ)) (o : ℕ) (hs : columnsAway K ps o)
    (w : Fin (ps.map (fun p => p.1+p.2)).sum → Fin D)
    (hw : ∀ i : Fin (ps.map Prod.fst).sum, 4 ≤ o+i.val → o+i.val+4 < K →
      P (w ((splitPositions ps).symm (Sum.inl i)))) : clearSlots P ps w := by
  induction ps generalizing o with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    constructor
    · intro hb i
      have hi := i.isLt
      have h₁ := (hs.1 hb).1
      have h₂ := (hs.1 hb).2
      have H := hw (Fin.castAdd (ps.map Prod.fst).sum i) (by simp only [Fin.val_castAdd]; omega)
        (by simp only [Fin.val_castAdd]; omega)
      erw [splitPositions_left_first] at H
      exact H
    · apply ih (o+a) hs.2 (rightWord finSumFinEquiv.symm w)
      intro i h₁ h₂
      have H := hw (Fin.natAdd a i) (by change 4 ≤ o+(a+i.val); omega)
        (by change o+(a+i.val)+4 < K; omega)
      erw [splitPositions_left_rest] at H
      exact H

end Saxl.FlagColumns
namespace Saxl

lemma joinedPositionEquiv_left {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (i : Fin a) :
    joinedPositionEquiv e f p q (e.symm (Sum.inl i)) = f.symm (Sum.inl (p i)) := by
  simp [joinedPositionEquiv]

lemma joinedPositionEquiv_right {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (i : Fin b) :
    joinedPositionEquiv e f p q (e.symm (Sum.inr i)) = f.symm (Sum.inr (q i)) := by
  simp [joinedPositionEquiv]

lemma relabelWord_positionProduct {n m a b A B D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B)
    (v : WordSpace a D) (u : WordSpace b D) :
    relabelWord (joinedPositionEquiv e f p q) (positionProduct e v u) =
      positionProduct f (relabelWord p v) (relabelWord q u) := by
  ext w
  change v _ * u _ = v _ * u _
  congr 1
  · congr 1
    funext i
    exact congrArg w (joinedPositionEquiv_left e f p q i)
  · congr 1
    funext i
    exact congrArg w (joinedPositionEquiv_right e f p q i)

lemma joinedPositionEquiv_isLeft {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (i : Fin n) :
    (f (joinedPositionEquiv e f p q i)).isLeft = (e i).isLeft := by
  simp only [joinedPositionEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases e i <;> rfl

lemma wordSector_joinedPositionEquiv {n m a b A B D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (P : Fin D → Prop)
    (w : Fin m → Fin D) :
    wordSector (fun i => (e i).isLeft = true) P (w ∘ joinedPositionEquiv e f p q) ↔
      wordSector (fun i => (f i).isLeft = true) P w := by
  change (∀ i, P (w (joinedPositionEquiv e f p q i)) ↔ (e i).isLeft = true) ↔ _
  simp only [← joinedPositionEquiv_isLeft e f p q]
  exact ((joinedPositionEquiv e f p q).surjective.forall
    (p := fun i => P (w i) ↔ (f i).isLeft = true)).symm

lemma coordinateProjection_relabel_split {n m a b A B D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (P : Fin D → Prop)
    (z : WordSpace n D) :
    coordinateProjection (wordSector (fun i => (f i).isLeft = true) P)
      (relabelWord (joinedPositionEquiv e f p q) z) =
    relabelWord (joinedPositionEquiv e f p q)
      (coordinateProjection (wordSector (fun i => (e i).isLeft = true) P) z) := by
  classical
  ext w
  simp only [relabelWord_apply, coordinateProjection_apply,
    wordSector_joinedPositionEquiv e f p q P w]

end Saxl

namespace UniversalTensorSquare
open Saxl Saxl.FlagColumns

theorem candidateBandWord_support_of_columns {n M b δ r d : ℕ}
    (hM : 4 ≤ M) (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hd : d ≤ 4)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (ps : List (ℕ × ℕ)) (hp : (ps.map Prod.fst).sum = 2*M-1)
    (he : (ps.map Prod.snd).sum = 2*r)
    (ha : ∀ p ∈ ps, 1 ≤ p.1 ∧ p.1 ≤ d)
    (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d) (hc : columnsAway (2*M-1) ps 0)
    (μ η : YoungDiagram) (hη : η.card = 2*r)
    (hηe : ∀ i, Even (η.colLen i)) (hηw : η.rowLen 0 ≤ 8)
    (Eμ : Columns.Cells (ps.map (fun p => p.1+p.2)) ≃ μ.cells)
    (Eμr : ∀ c, (Eμ c).val.1 = Columns.row c)
    (Eμc : ∀ c c', (Eμ c).val.2 = (Eμ c').val.2 ↔ Columns.col c = Columns.col c')
    (Eη : Columns.Cells (ps.map Prod.snd) ≃ η.cells)
    (Eηr : ∀ c, (Eη c).val.1 = Columns.row c)
    (Eηc : ∀ c c', (Eη c).val.2 = (Eη c').val.2 ↔ Columns.col c = Columns.col c')
    (s : Tableau (candidateBandSize t) μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep _ _) (candidateBandWord hM t)).toRepresentation, F ≠ 0 := by
  obtain ⟨N,hN,hNp⟩ := candidatePathWord_contraction hM hδ t s₁ s₂ (ps.map Prod.fst) (by
    intro a ha'
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp ha'
    exact ⟨(ha p hp').1,(ha p hp').2.trans hd⟩) hp
  obtain ⟨g,Q,hQ,hQp⟩ := candidateExtrasWord_contraction hM hδ hr s₁ s₂ η hη hηe hηw
    (ps.map Prod.snd) he Eη Eηr Eηc
  let e := candidateBandSplit hM t s₁ s₂
  let f := splitPositions ps
  let p := (finCongr hp).symm
  let q := (finCongr he).symm.trans g
  let E := joinedPositionEquiv e f p q
  let z := relabelWord E (candidateBandWord hM t)
  let v := relabelWord p (candidatePathWord hM t s₁ s₂)
  let u := relabelWord q (candidateExtrasWord hM s₁ s₂)
  let c := signC (candidateBandRowShuffle hM t).val * signC (candidateBandColShuffle hM t).val
  have hz : ∀ w, z w ≠ 0 → clearSlots (candidatePathAlphabet M b δ) ps w := by
    intro w hw
    apply clearSlots_of_columnsAway (candidatePathAlphabet M b δ) ps 0 hc w
    intro i h₁ h₂
    have H := candidateBandWord_path_clearance hM t (w ∘ E) hw
      (e.symm (Sum.inl (finCongr hp i))) (finCongr hp i)
      (candidateBandSplit_path hM t s₁ s₂ _) (by change 4 ≤ i.val; omega)
      (by change i.val+4 < 2*M-1; omega)
    change candidatePathAlphabet M b δ (w (E (e.symm (Sum.inl (finCongr hp i))))) at H
    dsimp only [E] at H
    rw [joinedPositionEquiv_left, show p (finCongr hp i) = i from
      (finCongr hp).symm_apply_apply i] at H
    exact H
  have hsep : coordinateProjection
      (wordSector (fun i => (f i).isLeft = true) (candidatePathAlphabet M b δ)) z =
      c • positionProduct f v u := by
    rw [coordinateProjection_relabel_split e f p q, candidateBandWord_separated hM hδ t s₁ s₂,
      map_smul, relabelWord_positionProduct]
  have hsign {k : ℕ} (g : Equiv.Perm (Fin k)) : signC g ≠ 0 := by
    have H := signC_mul_self g
    intro hz
    rw [hz,zero_mul] at H
    exact zero_ne_one H
  have hc' : c ≠ 0 := mul_ne_zero (hsign _) (hsign _)
  have Hpair := band_contraction_factor N Q (candidatePathAlphabet M b δ) ps
    (fun p hp => (ha p hp).2) hb hN hQ z hz v u c hsep
  have hnon : dotProduct (blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q)) z ≠ 0 := by
    rw [Hpair]
    exact mul_ne_zero hc' (mul_ne_zero hNp (by
      change dotProduct (blocks (ps.map Prod.snd) Q)
        (relabelWord ((finCongr he).symm.trans g) (candidateExtrasWord hM s₁ s₂)) ≠ 0
      rw [← relabelWord_trans]
      exact hQp))
  have hs := columns_sufficient Eμ Eμr Eμc ((Columns.enumerate _).trans Eμ) z
    (joinedFlag d N Q) hnon
  exact (cyclic_support_relabel_iff E s ((Columns.enumerate _).trans Eμ)
    (candidateBandWord hM t)).mp hs

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ColumnClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Clearance. -/

section

noncomputable section
namespace Saxl.FlagColumns

lemma columnsAway_append (K : ℕ) (xs ys : List (ℕ × ℕ)) (o : ℕ) :
    columnsAway K (xs++ys) o ↔
      columnsAway K xs o ∧ columnsAway K ys (o+(xs.map Prod.fst).sum) := by
  induction xs generalizing o with
  | nil => simp [columnsAway]
  | cons x xs ih =>
    obtain ⟨a,b⟩ := x
    simp only [List.cons_append, columnsAway, ih, List.map_cons, List.sum_cons]
    simp only [Nat.add_assoc, and_assoc]

lemma columnsAway_of_zero (K : ℕ) (ps : List (ℕ × ℕ))
    (h : ∀ p ∈ ps, p.2 = 0) (o : ℕ) : columnsAway K ps o := by
  induction ps generalizing o with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    exact ⟨fun hb => (hb (h (a,b) (by simp))).elim,
      ih (fun p hp => h p (by simp [hp])) _⟩

lemma columnsAway_of_bounds (K : ℕ) (ps : List (ℕ × ℕ)) (o : ℕ)
    (hl : 4 ≤ o) (hr : o+(ps.map Prod.fst).sum+4 ≤ K) : columnsAway K ps o := by
  induction ps generalizing o with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    simp only [List.map_cons, List.sum_cons] at hr
    exact ⟨fun _ => ⟨hl,by omega⟩, ih (o+a) (by omega) (by omega)⟩

lemma prefix_bounded_sum {α : Type*} (w : α → ℕ) (d : ℕ)
    (xs : List α) (hb : ∀ x ∈ xs, w x ≤ d) (k : ℕ)
    (hk : k ≤ (xs.map w).sum) :
    ∃ pre post, xs = pre++post ∧ k ≤ (pre.map w).sum ∧
      (pre.map w).sum ≤ k+(d-1) := by
  induction xs generalizing k with
  | nil =>
    exact ⟨[],[],rfl,hk,by simp⟩
  | cons x xs ih =>
    by_cases hk0 : k = 0
    · subst k
      exact ⟨[],x::xs,rfl,by simp,by simp⟩
    by_cases hx : k ≤ w x
    · refine ⟨[x],xs,rfl,by simpa using hx,?_⟩
      have hh := hb x (by simp)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · have hk' : k-w x ≤ (xs.map w).sum := by
        simp only [List.map_cons, List.sum_cons] at hk
        omega
      obtain ⟨pre,post,hpp,hl,hr⟩ := ih (fun x hx => hb x (by simp [hx])) (k-w x) hk'
      refine ⟨x::pre,post,by rw [hpp]; rfl,?_,?_⟩ <;>
        simp only [List.map_cons, List.sum_cons] <;> omega

theorem reorder_columns_away (ps : List (ℕ × ℕ)) (d K q : ℕ)
    (hK : (ps.map Prod.fst).sum = K)
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hc : (ps.filter (fun p => p.2 ≠ 0)).length ≤ q)
    (hclear : d*q+7+d ≤ K) :
    ∃ qs : List (ℕ × ℕ), qs.Perm ps ∧ columnsAway K qs 0 := by
  classical
  let chosen := ps.filter (fun p => p.2 ≠ 0)
  let free := ps.filter (fun p => p.2 = 0)
  have hperm : (chosen++free).Perm ps := by
    simpa only [chosen,free,decide_not, Bool.not_not] using
      List.filter_append_perm (fun p : ℕ × ℕ => decide (p.2 ≠ 0)) ps
  have hchosen : (chosen.map Prod.fst).sum = chosen.length*d := by
    have he : chosen.map Prod.fst = chosen.map (fun _ => d) := by
      apply List.map_congr_left
      intro p hp
      exact hb p (List.mem_filter.mp hp).1 (of_decide_eq_true (List.mem_filter.mp hp).2)
    rw [he, List.map_const', List.sum_replicate, smul_eq_mul]
  have hsum : (chosen.map Prod.fst).sum+(free.map Prod.fst).sum = K := by
    simpa only [List.map_append, List.sum_append] using (hperm.map Prod.fst).sum_eq.trans hK
  have hlen : chosen.length*d ≤ d*q := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left d hc
  have hd : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hz : (ps.map Prod.fst).sum = 0 := List.sum_eq_zero_iff.mpr (by
      intro a ha'
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha'
      have H := ha p hp
      rw [hd0] at H
      exact Nat.le_zero.mp H)
    omega
  have hfree : 7+d ≤ (free.map Prod.fst).sum := by rw [hchosen] at hsum; omega
  obtain ⟨pre,post,hpp,hl,hr⟩ := prefix_bounded_sum Prod.fst d free
    (fun p hp => ha p (List.mem_filter.mp hp).1) 4 (by omega)
  have hz : ∀ p ∈ pre++post, p.2 = 0 := by
    rw [← hpp]
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have hs : (pre.map Prod.fst).sum+(chosen.map Prod.fst).sum+(post.map Prod.fst).sum = K := by
    rw [hpp,List.map_append,List.sum_append] at hsum
    omega
  have hpost : 4 ≤ (post.map Prod.fst).sum := by
    rw [hpp,List.map_append,List.sum_append] at hfree
    omega
  refine ⟨pre++chosen++post,?_,?_⟩
  · rw [List.append_assoc]
    apply List.Perm.trans _ hperm
    rw [hpp]
    simpa only [List.append_assoc] using (List.Perm.append_right post
      (List.perm_append_comm (l₁ := pre) (l₂ := chosen)))
  · rw [columnsAway_append, columnsAway_append]
    refine ⟨⟨columnsAway_of_zero K pre (fun p hp => hz p (List.mem_append_left _ hp)) 0,?_⟩,?_⟩
    · apply columnsAway_of_bounds <;> omega
    · exact columnsAway_of_zero K post (fun p hp => hz p (List.mem_append_right _ hp)) _

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandAllocationLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Allocation Lists. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma colLen_pos_iff (μ : YoungDiagram) (i : ℕ) :
    0 < μ.colLen i ↔ i < μ.rowLen 0 := by
  rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]

lemma positive_column_list (μ : YoungDiagram) (W : ℕ) (hW : μ.rowLen 0 ≤ W) :
    ((List.range W).map μ.colLen).filter (fun a => 0 < a) = μ.transpose.rowLens := by
  rw [List.filter_map]
  have h : (List.range W).filter ((fun a => decide (0 < a)) ∘ μ.colLen) =
      List.range (μ.rowLen 0) := by
    calc _ = (List.range W).filter (fun i => decide (i < μ.rowLen 0)) := by
           apply List.filter_congr
           intro i hi
           simp only [Function.comp_apply, colLen_pos_iff]
         _ = List.range (μ.rowLen 0) := by
           rw [← List.Ico.zero_bot W, List.Ico.filter_lt_of_ge hW, List.Ico.zero_bot]
  rw [h]
  simp only [YoungDiagram.rowLens, YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro i hi
  exact (YoungDiagram.rowLen_transpose μ i).symm

lemma column_list_sum (μ : YoungDiagram) (W : ℕ) (hW : μ.rowLen 0 ≤ W) :
    ((List.range W).map μ.colLen).sum = μ.card := by
  rw [← List.sum_toFinset μ.colLen List.nodup_range]
  simpa only [List.toFinset_range, rowPrefix, YoungDiagram.rowLen_transpose, transpose_card]
    using rowPrefix_eq_card μ.transpose (by simpa using hW)

lemma place_padded_columns (μ : YoungDiagram) (W : ℕ) (hW : μ.rowLen 0 ≤ W)
    (rs : List ℕ) (h : rs.Perm ((List.range W).map μ.colLen)) :
    ∃ e : Columns.Cells rs ≃ μ.cells,
      (∀ c, (e c).val.1 = Columns.row c) ∧
      (∀ c d, (e c).val.2 = (e d).val.2 ↔ Columns.col c = Columns.col d) := by
  obtain ⟨e,hr,hc⟩ := Columns.discard_zero_columns rs
  have hh := h.filter (fun a => decide (0 < a))
  rw [positive_column_list μ W hW] at hh
  obtain ⟨f,hr',hc'⟩ := Columns.place_columns μ hh
  exact ⟨e.trans f,fun c => (hr' (e c)).trans (hr c),
    fun c d => (hc' (e c) (e d)).trans (hc c d)⟩

lemma width_le_of_cols {π μ : YoungDiagram} (h : ∀ i, π.colLen i ≤ μ.colLen i) :
    π.rowLen 0 ≤ μ.rowLen 0 := by
  by_contra hh
  have hi : 0 < π.colLen (μ.rowLen 0) := (colLen_pos_iff _ _).mpr (by omega)
  have hi' : 0 < μ.colLen (μ.rowLen 0) := hi.trans_le (h _)
  exact Nat.lt_irrefl _ ((colLen_pos_iff _ _).mp hi')

theorem band_subdiagram_columns (lam : YoungDiagram) (K r d q : ℕ)
    (hd : 1 ≤ d) (hK : K ≤ rowPrefix lam d) (hclear : d*q+7+d ≤ K)
    (hr : r ≤ bandCapacity lam d q) :
    ∃ μ η : YoungDiagram, ∃ ps : List (ℕ × ℕ),
      μ ≤ lam ∧ μ.card = K+2*r ∧ η.card = 2*r ∧
      (ps.map Prod.fst).sum = K ∧ (ps.map Prod.snd).sum = 2*r ∧
      (∀ p ∈ ps, 1 ≤ p.1 ∧ p.1 ≤ d) ∧
      (∀ p ∈ ps, p.2 ≠ 0 → p.1 = d) ∧
      Saxl.FlagColumns.columnsAway K ps 0 ∧
      (∀ i, Even (η.colLen i)) ∧ η.rowLen 0 ≤ q ∧
      (∃ e : Columns.Cells (ps.map (fun p => p.1+p.2)) ≃ μ.cells,
        (∀ c, (e c).val.1 = Columns.row c) ∧
        (∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c')) ∧
      (∃ e : Columns.Cells (ps.map Prod.snd) ≃ η.cells,
        (∀ c, (e c).val.1 = Columns.row c) ∧
        (∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c')) := by
  obtain ⟨π,η,μ,hμlam,hπcard,hηcard,hμcard,hcolsh,hplen,heven,hηw,hchosen⟩ :=
    band_subdiagram_allocation lam K r d q hK hclear hr
  let W := μ.rowLen 0
  let ps := (List.range W).map (fun i => (π.colLen i, η.colLen i))
  have hπw : π.rowLen 0 ≤ W := width_le_of_cols (fun i => by rw [hcolsh]; omega)
  have hηw' : η.rowLen 0 ≤ W := width_le_of_cols (fun i => by rw [hcolsh]; omega)
  have hs₁ : (ps.map Prod.fst).sum = K := by
    simpa only [ps,List.map_map,Function.comp_def] using
      (column_list_sum π W hπw).trans hπcard
  have hs₂ : (ps.map Prod.snd).sum = 2*r := by
    simpa only [ps,List.map_map,Function.comp_def] using
      (column_list_sum η W hηw').trans hηcard
  have ha : ∀ p ∈ ps, 1 ≤ p.1 ∧ p.1 ≤ d := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hm : 0 < μ.colLen i := (colLen_pos_iff μ i).mpr (List.mem_range.mp hi)
    rw [hcolsh] at hm
    by_cases he : 0 < η.colLen i
    · exact ⟨by rw [hchosen i he]; exact hd,hplen i⟩
    · exact ⟨by omega,hplen i⟩
  have hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d := by
    intro p hp hn
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact hchosen i (Nat.pos_of_ne_zero hn)
  have hlen : (ps.filter (fun p => p.2 ≠ 0)).length ≤ q := by
    have hh : (ps.filter (fun p => p.2 ≠ 0)).length = η.rowLen 0 := by
      dsimp only [ps]
      rw [List.filter_map, List.length_map]
      have hh : (List.range W).filter ((fun p : ℕ × ℕ => decide (p.2 ≠ 0)) ∘
          (fun i => (π.colLen i,η.colLen i))) = List.range (η.rowLen 0) := by
        calc _ = (List.range W).filter (fun i => decide (i < η.rowLen 0)) := by
               apply List.filter_congr
               intro i hi
               simp only [Function.comp_apply, Nat.pos_iff_ne_zero.symm, colLen_pos_iff]
             _ = List.range (η.rowLen 0) := by
               rw [← List.Ico.zero_bot W,List.Ico.filter_lt_of_ge hηw',List.Ico.zero_bot]
      rw [hh,List.length_range]
    exact hh.le.trans hηw
  obtain ⟨qs,hqs,hqc⟩ := Saxl.FlagColumns.reorder_columns_away ps d K q hs₁
    (fun p hp => (ha p hp).2) hb hlen hclear
  refine ⟨μ,η,qs,hμlam,hμcard,hηcard,(hqs.map Prod.fst).sum_eq.trans hs₁,
    (hqs.map Prod.snd).sum_eq.trans hs₂,
    fun p hp => ha p (hqs.mem_iff.mp hp),fun p hp => hb p (hqs.mem_iff.mp hp),
    hqc,heven,hηw,?_,?_⟩
  · apply place_padded_columns μ W le_rfl
    have hh := hqs.map (fun p => p.1+p.2)
    simpa only [ps,List.map_map,Function.comp_def,← hcolsh] using hh
  · apply place_padded_columns η W hηw'
    simpa only [ps,List.map_map,Function.comp_def] using hqs.map Prod.snd

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_BandCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Band Criterion. -/

section

noncomputable section
namespace Saxl.ShortColumns

lemma card (b δ : ℕ) (hδ : δ ≤ 1) : (shape b δ).card = 2*b+δ := by
  have h (n : ℕ) (t : Tableau n (shape b δ)) : (shape b δ).card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe, YoungDiagram.card] using
      (Fintype.card_congr t).symm
  rcases (by omega : δ = 0 ∨ δ = 1) with rfl | rfl
  · simpa only [Nat.add_zero] using h _ (evenTableau b)
  · exact h _ (oddTableau b)

end Saxl.ShortColumns
namespace UniversalTensorSquare
open Saxl

lemma candidateBandSize_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (t : Tableau n (candidate M b δ)) :
    candidateBandSize t = 2*M-1+2*r := by
  let s := canonicalTableau (ShortColumns.shape b δ) ((ShortColumns.card b δ hδ).trans hr.symm)
  simpa only [Fintype.card_fin, Fintype.card_sum] using
    Fintype.card_congr (candidateBandSplit hM t s s)

theorem band_kronecker_pos_oai {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (t : Tableau n (candidate M b δ))
    (lam : YoungDiagram) (s : Tableau n lam) (hband : BandTest M r lam) :
    0 < kronecker t t s := by
  obtain ⟨d,hd₁,hd₄,q,hq,hK,hclear,hrcap⟩ := hband
  obtain ⟨μ,η,ps,hμlam,hμcard,hηcard,hp,he,ha,hb,hc,hηe,hηw,
    ⟨Eμ,Eμr,Eμc⟩,⟨Eη,Eηr,Eηc⟩⟩ :=
    band_subdiagram_columns lam (2*M-1) r d q hd₁ hK hclear hrcap
  let a := canonicalTableau (ShortColumns.shape b δ) ((ShortColumns.card b δ hδ).trans hr.symm)
  let v := canonicalTableau μ (hμcard.trans (candidateBandSize_eq hM hδ hr t).symm)
  obtain ⟨F,hF⟩ := candidateBandWord_support_of_columns hM hδ hr hd₄ t a a ps hp he ha hb hc
    μ η hηcard hηe (hηw.trans hq) Eμ Eμr Eμc Eη Eηr Eηc v
  exact candidate_kronecker_pos_of_subdiagram hM t hμlam v s F hF

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.band_kronecker_pos_oai := @OAI.UniversalTensorSquare.band_kronecker_pos_oai
