-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg13299
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:10:52.069444+00:00
-- url     : https://prove2.me/submissions/d9886c9a-5442-4556-8377-0d88470f76d0

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US022
import Definitions.Def_OAIQ259US023
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg115
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_UniversalTensorSquare_transposeRows_eq

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

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
theorem hom_to_cyclic_of_pair {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  let f := (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)).comp ((wordMap L).comp inc)
  refine ⟨f, ?_⟩
  intro hf
  have hp := subrepProject_pair (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx) (wordMap L x.val) ⟨u, mem_cyclic _ _⟩
  have he : f x = 0 := by rw [hf]; rfl
  change (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)) (wordMap L x.val) = 0 at he
  rw [he] at hp
  exact h (hp.symm.trans (zero_dotProduct _))

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
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

lemma pair_alt (w : Fin 2 → Fin 2) :
    Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) w = J (w 0) (w 1) := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin 2)))
  unfold Saxl.altWord
  rw [Finset.sum_apply]
  change (∑ g : (⊤ : Subgroup (Equiv.Perm (Fin 2))), Saxl.signC (g : Equiv.Perm (Fin 2)) *
    ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ (g : Equiv.Perm (Fin 2))))) = _
  calc
    _ = ∑ g : Equiv.Perm (Fin 2), Saxl.signC g *
        ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ g)) :=
      Fintype.sum_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 2))).toEquiv _ _ (by intro g; rfl)
    _ = _ := by
      have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
      rw [hu]
      have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
      simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
      have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
      rw [hw]
      generalize h0 : w 0 = a
      generalize h1 : w 1 = b
      fin_cases a <;> fin_cases b <;>
        (first | (simp [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; all_goals first | (norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; done) | rfl | decide) | (norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; done) | norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J])

end Saxl.PathLayer

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

theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)



lemma cyclic_smul_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (c : ℂ) (hc : c ≠ 0) :
    cyclic ρ (c • v) = cyclic ρ v := by
  apply le_antisymm
  · apply (cyclic_le _ _ _).mpr
    exact Submodule.smul_mem _ _ (mem_cyclic ρ v)
  · apply (cyclic_le _ _ _).mpr
    have hh := Submodule.smul_mem (cyclic ρ (c • v)).toSubmodule c⁻¹ (mem_cyclic ρ (c • v))
    change v ∈ (cyclic ρ (c • v)).toSubmodule
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

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
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SquareDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) :
    cyclic (wordRep n (α.colLen 0 * β.colLen 0))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
        (spechtTensorMap a b).range := by
  unfold spechtTensorMap
  apply (cyclic_le _ _ _).mpr
  exact ⟨(⟨polytabloid a', polytabloid_mem_all a a'⟩ : Specht a) ⊗ₜ[ℂ]
    (⟨polytabloid b', polytabloid_mem_all b b'⟩ : Specht b), rfl⟩

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
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

lemma symmetricPairs_real {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    star (symmetricPairs e d) = symmetricPairs e d := by
  ext w
  simp only [Pi.star_apply, symmetricPairs]
  split_ifs <;> simp

lemma symmetricPairs_contraction {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (x y : WordSpace m d) :
    dotProduct (positionProduct e x y) (symmetricPairs e d) = dotProduct x y := by
  classical
  unfold dotProduct
  calc
    _ = ∑ p : (Fin m → Fin d) × (Fin m → Fin d),
        x p.1 * y p.2 * (if p.1 = p.2 then 1 else 0) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro w
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp

lemma real_self_pair_ne_zero {n d : ℕ} (x : WordSpace n d)
    (hr : star x = x) (hx : x ≠ 0) : dotProduct x x ≠ 0 := by
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  intro he
  apply hx
  exact dotProduct_self_star_eq_zero.mp (by simpa only [hr] using he)

lemma pairedTableau_left {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inl i))).val =
      ((s i).val.1, 2*(s i).val.2) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_right {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inr i))).val =
      ((s i).val.1, 2*(s i).val.2+1) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_group_sector {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    columnGroup (pairedTableau μ he e s) ≤ sectorGroup (fun i => (e i).isLeft = true) := by
  intro g hg i
  have hc := hg i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  obtain ⟨k,hk⟩ := e.symm.surjective (g (e.symm j))
  rw [← hk] at hc ⊢
  cases j <;> cases k <;>
    simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, Sum.isLeft_inr] at *
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega

lemma pairedTableau_factor {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) :
    polytabloid (pairedTableau μ he e s) = positionProduct e
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s))
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s)) := by
  let t := pairedTableau μ he e s
  let f : Fin n → ℕ := fun i => (t i).val.2
  have hn : columnGroup t = fiberGroup f := rfl
  have hg : columnGroup t = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    rw [← hn]
    exact (inf_eq_left.mpr (pairedTableau_group_sector μ he e s)).symm
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inl (g i)))).val.2 =
      (t (e.symm (Sum.inl i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_left, Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inr (g i)))).val.2 =
      (t (e.symm (Sum.inr i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_right, Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hw₁ : leftWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [pairedTableau_left]
  have hw₂ : rightWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inr i))).val.1 = (s i).val.1
    rw [pairedTableau_right]
  change polytabloid t = _
  rw [polytabloid_eq_altWord, hg, altWord_fiber_split, hl, hr, hw₁, hw₂,
    ← letterLift_altWord, ← polytabloid_eq_altWord]

lemma letterLift_real {n a b : ℕ} (φ : Fin a → Fin b) (x : WordSpace n a)
    (hr : star x = x) : star (letterLift φ x) = letterLift φ x := by
  classical
  funext w
  change star (∑ c, x c * ∏ i, if φ (c i) = w i then (1 : ℂ) else 0) = _
  simp only [star_sum, star_mul, star_prod, apply_ite, star_one, star_zero]
  have hx (c) : star (x c) = x c := congrFun hr c
  simp_rw [hx]
  simp only [letterLift, wordMap, mul_comm]
  rfl

lemma letterLift_pair {n a b : ℕ} (φ : Fin a → Fin b)
    (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (letterLift φ x) y = dotProduct x (fun w => y (φ ∘ w)) := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_smul, letterLift_single]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext w
  simp [Pi.single_apply]

lemma letterLift_symmetricPairs_pair {n m a b : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (φ : Fin a → Fin b)
    (hφ : Function.Injective φ) (x : WordSpace n a) :
    dotProduct (letterLift φ x) (symmetricPairs e b) =
      dotProduct x (symmetricPairs e a) := by
  rw [letterLift_pair]
  congr 1
  funext w
  have hh : leftWord e (φ ∘ w) = rightWord e (φ ∘ w) ↔
      leftWord e w = rightWord e w := by
    constructor
    · intro h
      funext i
      exact hφ (congrFun h i)
    · intro h
      funext i
      exact congrArg φ (congrFun h i)
  simp only [symmetricPairs, hh]

lemma pairedTableau_contraction {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    dotProduct (polytabloid (pairedTableau μ he e s))
      (symmetricPairs e (μ.colLen 0)) ≠ 0 := by
  rw [pairedTableau_factor, symmetricPairs_contraction]
  apply real_self_pair_ne_zero
  · exact letterLift_real _ _ (polytabloid_real s)
  · intro hz
    apply polytabloid_ne_zero s
    exact letterLift_injective _ (Fin.cast_injective _) (hz.trans (map_zero _).symm)

lemma halfRows_card (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    2 * (halfRows μ).card = μ.card := by
  have hc := Fintype.card_congr (pairedCells μ he)
  simpa only [Fintype.card_sum, Fintype.card_coe, ← two_mul] using hc

theorem even_rows_symmetricPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPairs e d)).toRepresentation, F ≠ 0 := by
  have hn : μ.card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have hnm : n = 2*m := by
    simpa only [Fintype.card_fin, Fintype.card_sum, ← two_mul] using Fintype.card_congr e
  have hm : (halfRows μ).card = m := by
    have hc := halfRows_card μ he
    omega
  let s := canonicalTableau (halfRows μ) hm
  let es : Fin n ≃ Fin m ⊕ Fin m := t.trans ((pairedCells μ he).symm.trans
    (Equiv.sumCongr s.symm s.symm))
  have ht : pairedTableau μ he es s = t := by
    apply Equiv.ext
    intro i
    change pairedCells μ he ((Equiv.sumCongr s s)
      ((Equiv.sumCongr s s).symm ((pairedCells μ he).symm (t i)))) = t i
    simp only [Equiv.apply_symm_apply]
  let φ : Fin (μ.colLen 0) → Fin d := Fin.castLE hd
  have hh : dotProduct (letterLift φ (polytabloid t)) (symmetricPairs es d) ≠ 0 := by
    rw [letterLift_symmetricPairs_pair _ φ (Fin.castLE_injective hd), ← ht]
    exact pairedTableau_contraction μ he es s
  have hsupp := hom_to_cyclic_of_pair
    (fun a b => if φ a = b then 1 else 0) (spechtSub t)
    ⟨polytabloid t, mem_cyclic _ _⟩ (symmetricPairs es d) (symmetricPairs_real es) hh
  let g : Equiv.Perm (Fin n) := e.trans es.symm
  have hg : wordRep n d g (symmetricPairs e d) = symmetricPairs es d := by
    funext w
    have hl : leftWord e (w ∘ g) = leftWord es w := by
      funext i
      simp [leftWord, g]
    have hr : rightWord e (w ∘ g) = rightWord es w := by
      funext i
      simp [rightWord, g]
    change (if leftWord e (w ∘ g) = rightWord e (w ∘ g) then 1 else 0) = _
    simp only [hl, hr, symmetricPairs]
  have hc : cyclic (wordRep n d) (symmetricPairs es d) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [← hg, cyclic_action_eq]
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (symmetricPairs es d)).toRepresentation, f ≠ 0 at hsupp
  rw [hc] at hsupp
  exact hsupp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma pairFormTensor_one {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    pairFormTensor e (1 : Matrix (Fin d) (Fin d) ℂ) = symmetricPairs e d := by
  classical
  funext w
  change (∏ i, if leftWord e w i = rightWord e w i then (1 : ℂ) else 0) = _
  by_cases hw : leftWord e w = rightWord e w
  · simp [hw, symmetricPairs]
  · have hi : ∃ i, leftWord e w i ≠ rightWord e w i := by
      exact not_forall.mp (fun he => hw (funext he))
    obtain ⟨i, hi⟩ := hi
    rw [symmetricPairs, ite_eq_right hw]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma pairFormTensor_smul {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (c : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    pairFormTensor e (c • B) = c^m • pairFormTensor e B := by
  funext w
  simp [pairFormTensor, Finset.prod_mul_distrib]

lemma wordMap_pairFormTensor {n m a b : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin a → Fin b → ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    wordMap L (pairFormTensor e B) = pairFormTensor e
      (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) := by
  classical
  funext w
  change (∑ c, pairFormTensor e B c * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i) := by
      apply Fintype.sum_equiv (pairWordsEquiv e)
      intro c
      simp only [pairWordsEquiv_apply, pairFormTensor, Finset.prod_mul_distrib]
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ x : Fin m ⊕ Fin m, L (c (e.symm x)) (w (e.symm x)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by
            rw [Fintype.prod_sum_type]
            rfl
      rw [he, mul_assoc]
    _ = _ := by
      change (∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i)) =
        ∏ i, ∑ p : Fin a × Fin a,
          B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i)
      exact (Fintype.prod_sum (fun (i : Fin m) (p : Fin a × Fin a) =>
        B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i))).symm

theorem even_rows_pairFormTensor_support {n m a d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (B : Matrix (Fin a) (Fin a) ℂ)
    (L : Fin a → Fin d → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hL : (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) =
      c • (1 : Matrix (Fin d) (Fin d) ℂ))
    (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n a) (pairFormTensor e B)).toRepresentation, F ≠ 0 := by
  have hmap : wordMap L (pairFormTensor e B) = c^m • symmetricPairs e d := by
    rw [wordMap_pairFormTensor, hL, pairFormTensor_smul, pairFormTensor_one]
  have hs := even_rows_symmetricPairs_support e μ t he hd
  have hcyc : cyclic (wordRep n d) (wordMap L (pairFormTensor e B)) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [hmap, cyclic_smul_eq _ _ _ (pow_ne_zero m hc)]
  rw [← hcyc] at hs
  obtain ⟨F,hF⟩ := hs
  exact cyclic_projection_support (wordMap L) (pairFormTensor e B) F hF

lemma shortPairCongruence_gram :
    (fun j k => ∑ p : Fin 4 × Fin 4,
      shortPairForm p.1 p.2 * shortPairCongruence p.1 j * shortPairCongruence p.2 k) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    (first | (simp [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; all_goals first | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; done) | rfl | decide) | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; done) | norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply])

theorem even_rows_shortPair_support {n m : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4) (pairFormTensor e shortPairForm)).toRepresentation, F ≠ 0 :=
  even_rows_pairFormTensor_support e shortPairForm shortPairCongruence 2 (by norm_num)
    shortPairCongruence_gram μ t he hd

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ShortColumns
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.ShortColumns

lemma shortPairForm_eq (i j : Fin 4) :
    shortPairForm i j = PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).1 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).1 *
      PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).2 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).2 := by
  fin_cases i <;> fin_cases j <;>
    (first | (simp [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; all_goals first | (norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; done) | rfl | decide) | (norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; done) | norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat])

lemma evenTableau_polytabloid (b : ℕ) :
    letterLift (Fin.castLE (height_le b 0)) (polytabloid (evenTableau b)) = evenAlt b := by
  rw [polytabloid_eq_altWord, letterLift_altWord]
  rfl

lemma evenAlt_step (b : ℕ) :
    evenAlt (b+1) = positionProduct (appendEven b) (evenAlt b)
      (altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  have hs (i : Fin (2*(b+1))) :
      (appendEven b i).isLeft = true ↔ i.val/2 < b := by
    obtain ⟨j,rfl⟩ := (appendEven b).symm.surjective i
    cases j with
    | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff,
        appendEven_left]; omega
    | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true,
        appendEven_right, false_iff]; omega
  have hg : fiberGroup (fun i : Fin (2*(b+1)) => i.val/2) =
      fiberGroup (fun i : Fin (2*(b+1)) => i.val/2) ⊓
        sectorGroup (fun i => (appendEven b i).isLeft = true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg, ?_⟩
      intro i
      change (appendEven b (g i)).isLeft = true ↔ (appendEven b i).isLeft = true
      rw [hs,hs]
      exact congrArg (fun k => k < b) (hg i) |>.to_iff
    · exact inf_le_left
  have hr : fiberGroup (fun i : Fin 2 => ((appendEven b).symm (Sum.inr i)).val/2) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ True
    simp only [appendEven_right]
    constructor
    · intro _; trivial
    · intro _ i; have hi := i.isLt; have hgi := (g i).isLt; omega
  unfold evenAlt
  rw [hg, altWord_fiber_split, hr]
  congr 2
  funext i
  apply Fin.ext
  change (2*b+i.val)%2 = i.val
  omega

lemma evenAlt_zero (w : Fin 0 → Fin 2) : evenAlt 0 w = 1 := by
  classical
  let := Fintype.ofFinite (fiberGroup (fun i : Fin (2*0) => i.val/2))
  have hu : (Finset.univ : Finset (fiberGroup (fun i : Fin (2*0) => i.val/2))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  unfold evenAlt altWord
  rw [hu, Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (fun i : Fin 0 => (⟨i.val%2, _⟩ : Fin 2)) (1 : ℂ) : WordSpace 0 2) w = 1
  rw [Pi.single_apply, ite_eq_left (Subsingleton.elim _ _)]

lemma evenAlt_formula (b : ℕ) (w : Fin (2*b) → Fin 2) :
    evenAlt b w = ∏ i : Fin b,
      PathLayer.J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩) := by
  induction b with
  | zero => simpa using evenAlt_zero w
  | succ b ih =>
    rw [evenAlt_step]
    change evenAlt b (leftWord (appendEven b) w) *
      altWord ⊤ (fun i : Fin 2 => i) (rightWord (appendEven b) w) = _
    rw [ih, PathLayer.pair_alt, Fin.prod_univ_castSucc]
    rfl

lemma even_square (b : ℕ) :
    wordTensor (2*b) 2 2 (evenAlt b ⊗ₜ[ℂ] evenAlt b) =
      pairFormTensor (pairSplit b) shortPairForm := by
  funext w
  rw [wordTensor_tmul, evenAlt_formula, evenAlt_formula]
  change (∏ i : Fin b, _) * (∏ i : Fin b, _) =
    ∏ i, shortPairForm (leftWord (pairSplit b) w i) (rightWord (pairSplit b) w i)
  simp only [shortPairForm_eq, leftWord, rightWord, Finset.prod_mul_distrib,
    splitLeft, splitRight]
  rfl

end Saxl.ShortColumns
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

namespace ShortColumns

theorem even_columnSquare_support (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (columnSquareCyclic (evenTableau b)).toRepresentation, F ≠ 0 := by
  let F := pairWordMap (n := 2*b) (letterLift (Fin.castLE (height_le b 0)))
    (letterLift (Fin.castLE (height_le b 0)))
  have hF : F (columnSquareWord (evenTableau b)) =
      pairFormTensor (pairSplit b) shortPairForm := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, evenTableau_polytabloid, even_square]
  have hs := even_rows_shortPair_support (pairSplit b) μ t he hd
  rw [← hF] at hs
  obtain ⟨g,hg⟩ := hs
  exact cyclic_projection_support F (columnSquareWord (evenTableau b)) g hg

end ShortColumns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SquareSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Columns

lemma kronecker_pos_input_transpose {n : ℕ} {α μ : YoungDiagram}
    (a : Tableau n α) (t : Tableau n μ)
    (b : Tableau n α.transpose) (h : 0 < kronecker a a t) :
    0 < kronecker b b t := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup (Specht b ⊗[ℂ] Specht b) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨e⟩ := specht_sign_transpose_uts a
  let f := (e.trans (signTwistEquiv
    (spechtShapeEquiv rfl (transposeTableau a) b)))
  let g := (tensorRepEquiv f f).trans (signTensorCancel (spechtRep b) (spechtRep b))
  obtain ⟨F,hF⟩ := (kronecker_pos_iff a a t).mp h
  apply (kronecker_pos_iff b b t).mpr
  refine ⟨g.toIntertwiningMap.comp F,?_⟩
  intro hz
  apply hF
  ext x
  apply g.injective
  have hh := congrArg (fun H => H x) hz
  change g (F x) = 0 at hh
  change g (F x) = g (0 : Specht a ⊗[ℂ] Specht a)
  exact hh.trans g.toIntertwiningMap.toLinearMap.map_zero.symm

lemma SquareOccurs.input_transpose {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    SquareOccurs α.transpose μ := by
  obtain ⟨n,a,t,ht⟩ := h
  exact ⟨n,transposeTableau a,t,kronecker_pos_input_transpose a t _ ht⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

lemma rowDiagram_rowLen {rs : List ℕ} (h : GoodRows rs) (i : ℕ) :
    (rowDiagram rs).rowLen i = rs[i]?.getD 0 := by
  rw [rowDiagram_eq rs h,ofRowLens_rowLen]

lemma rowDiagram_height {rs : List ℕ} (h : GoodRows rs) :
    (rowDiagram rs).colLen 0 = rs.length := by
  rw [← YoungDiagram.length_rowLens,rowDiagram_rows h]

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma rowDiagram_transposeRows {rs : List ℕ} (h : GoodRows rs) :
    rowDiagram (transposeRows rs) = (rowDiagram rs).transpose := by
  rw [transposeRows_eq h,rowDiagram_rowLens]

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowSquareTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Square Tools. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_even {p rs : List ℕ} (m : ℕ)
    (hp : GoodRows p) (hr : GoodRows rs) (hm : 0 < m)
    (he : p = [m,m] ∨ transposeRows p = [m,m])
    (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*m) (heven : ∀ r ∈ rs, Even r) :
    RowSquare p rs := by
  let t := canonicalTableau (rowDiagram rs) ((rowDiagram_card _).trans hrs)
  have hev (i : ℕ) : Even ((rowDiagram rs).rowLen i) := by
    rw [rowDiagram_rowLen hr]
    cases h : rs[i]? with
    | none => simp
    | some a => exact heven a (List.mem_of_getElem? h)
  obtain ⟨F,hF⟩ := ShortColumns.even_columnSquare_support m (rowDiagram rs) t hev
    (by rwa [rowDiagram_height hr])
  let a := ShortColumns.evenTableau m
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨Z,hZ⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap a a)
    (columnSquareCyclic a) (polytabloidTensor_cyclic_le_range a a a a)
  have hh : SquareOccurs (ShortColumns.shape m 0) (rowDiagram rs) :=
    ⟨2*m,a,t,(kronecker_pos_iff a a t).mpr
      ⟨Z.comp F,intertwining_comp_ne_zero Z hZ F hF⟩⟩
  have hrows : GoodRows [m,m] := by
    constructor
    · apply List.Pairwise.sortedGE; simp
    · simp; omega
  have hshape : ShortColumns.shape m 0 = rowDiagram [m,m] := by
    rw [rowDiagram_eq _ hrows]; rfl
  rw [hshape] at hh
  rcases he with rfl | he
  · exact hh
  · rw [← he,rowDiagram_transposeRows hp] at hh
    simpa only [YoungDiagram.transpose_transpose] using hh.input_transpose

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14 : RowSquare [2,2] [2,2] := by
  exact rowSquare_even 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg41 : RowSquare [3,2] [3,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg507 : RowSquare [3,3,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg14 sg21

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4009 : RowSquare [5,5,2,2,2] [3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg507

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8328 : RowSquare [5,5,2,2,2,2,2,1] [6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4009

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13299_oai : RowSquare [8,7,2,2,2,2,2,1] [8,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg8328

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg13299_oai := @OAI.UniversalTensorSquare.sg13299_oai
