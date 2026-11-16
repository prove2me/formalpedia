-- Prove2me | solution 1 for OAI.UniversalTensorSquare.rowSquare_join
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:47:49.112618+00:00
-- url     : https://prove2.me/submissions/19f9c73d-5e71-48e0-b92a-250b30e46e06

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

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
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma signTwist_irreducible {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (signTwist ρ) := by
  let cv : Subrepresentation (signTwist ρ) ≃o Subrepresentation ρ :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            have h := S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx)
            change signC g • (signC g • (ρ g x)) ∈ S.toSubmodule at h
            simpa only [smul_smul, signC_mul_self, one_smul] using h }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            exact S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx) }
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl
      map_rel_iff' := by intros; rfl }
  exact cv.isSimpleOrder_iff.mpr inferInstance

lemma orbitAverage_base {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
theorem specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  classical
  let tt := transposeTableau t
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin n) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin n), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep n (μ.transpose.colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin n)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin n)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin n)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin n)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) •
        wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_YoungRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/

lemma perm_of_equal_content {n d : ℕ} (a b : Fin n → Fin d)
    (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
      (Finset.univ.filter (fun i => b i = j)).card) :
    ∃ g : Equiv.Perm (Fin n), b ∘ g = a := by
  classical
  let e (j) : {i // a i = j} ≃ {i // b i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using h j)
  let g := (Equiv.sigmaFiberEquiv a).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b))
  refine ⟨g, ?_⟩
  funext i
  exact (e (a i) ⟨i,rfl⟩).property

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  intro x y h
  apply Subtype.ext
  unfold intertwiningLiftSubrep at h
  have hh := (intertwiningRangeEquiv f hf).symm.injective h
  exact congrArg (fun z : f.range => (z : Y)) hh

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

lemma spechtTensorMap_injective {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) : Function.Injective (spechtTensorMap a b) := by
  unfold spechtTensorMap
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub a).toSubmodule.subtype_injective (spechtSub b).toSubmodule.subtype_injective

lemma polytabloidTensor_real {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) :
    star (wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid b)) =
      wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid b) := by
  funext w
  simp only [Pi.star_apply, wordTensor_tmul, star_mul]
  have h₁ := congrFun (polytabloid_real a) (splitLeft w)
  have h₂ := congrFun (polytabloid_real b) (splitRight w)
  change star (polytabloid b (splitRight w)) * star (polytabloid a (splitLeft w)) = _
  rw [show star (polytabloid a (splitLeft w)) = _ from h₁,
    show star (polytabloid b (splitRight w)) = _ from h₂]
  exact mul_comm _ _

lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) :
    cyclic (wordRep n (α.colLen 0 * β.colLen 0))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
        (spechtTensorMap a b).range := by
  unfold spechtTensorMap
  apply (cyclic_le _ _ _).mpr
  exact ⟨(⟨polytabloid a', polytabloid_mem_all a a'⟩ : Specht a) ⊗ₜ[ℂ]
    (⟨polytabloid b', polytabloid_mem_all b b'⟩ : Specht b), rfl⟩

theorem kronecker_pos_of_contraction {n : ℕ} {α β μ : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) (t s : Tableau n μ)
    (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ)
    (h : dotProduct (wordMap L (polytabloid s))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0) :
    0 < kronecker a b t := by
  let z := wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')
  let S := cyclic (wordRep n (α.colLen 0 * β.colLen 0)) z
  obtain ⟨f, hf⟩ := hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ z (polytabloidTensor_real a' b') h
  let F := @intertwiningLiftSubrep (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  have hF : Function.Injective F := @intertwiningLiftSubrep_injective (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  apply (kronecker_pos_iff a b t).mpr
  refine ⟨F.comp f, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hzero := congrArg (fun H => H x) hz
  change F (f x) = 0 at hzero
  change F (f x) = F 0
  simpa only [map_zero] using hzero

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

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SingletonPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Pairs. -/

section

noncomputable section
namespace Saxl

lemma wordMap_positionProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin d → Fin D → ℂ) (x : WordSpace a d) (y : WordSpace b d) :
    wordMap L (positionProduct e x y) =
      positionProduct e (wordMap L x) (wordMap L y) := by
  classical
  funext w
  change (∑ c, (x (leftWord e c) * y (rightWord e c)) * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ p : (Fin a → Fin d) × (Fin b → Fin d),
        (x p.1 * ∏ i, L (p.1 i) (leftWord e w i)) *
          (y p.2 * ∏ i, L (p.2 i) (rightWord e w i)) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro c
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ z : Fin a ⊕ Fin b, L (c (e.symm z)) (w (e.symm z)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by rw [Fintype.prod_sum_type]; rfl
      rw [he]
      change _ = (x (leftWord e c) * _) * (y (rightWord e c) * _)
      dsimp [positionWordsEquiv]
      ring
    _ = _ := by
      change _ = (∑ c, x c * ∏ i, L (c i) (leftWord e w i)) *
        (∑ c, y c * ∏ i, L (c i) (rightWord e w i))
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]

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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_WordRelabel
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

lemma relabelWord_letterLift {n m d D : ℕ} (e : Fin n ≃ Fin m) (f : Fin d → Fin D)
    (v : WordSpace n d) : relabelWord e (letterLift f v) = letterLift f (relabelWord e v) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  exact (Representation.IntertwiningMap.isIntertwining _ _ (letterLift f) e v).symm

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

lemma columnShape_height (rs : List ℕ) (B : ℕ) (hB : ∀ h ∈ rs, h ≤ B) :
    (columnShape rs).colLen 0 ≤ B := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_height e hr B hB

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

lemma wordMap_letterLift {n a b c : ℕ} (f : Fin a → Fin b)
    (L : Fin b → Fin c → ℂ) (x : WordSpace n a) :
    wordMap L (letterLift f x) = wordMap (fun i j => L (f i) j) x := by
  classical
  have h : (wordMap L).comp (letterLift f) = wordMap (fun i j => L (f i) j) (n := n) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.pi_ext
    intro w c
    have he : (Pi.single w c : WordSpace n a) = c • Pi.single w 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul]
    congr 1
    change wordMap L (letterLift f (Pi.single w 1)) = wordMap _ (Pi.single w 1)
    rw [letterLift_single]
    ext v
    simp only [wordMap_single, Function.comp_apply]
  exact congrArg (fun F => F x) h

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_StandardColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

lemma standard_lift (rs : List ℕ) {d D : ℕ} (hd : (columnShape rs).colLen 0 ≤ d)
    (hD : d ≤ D) :
    letterLift (Fin.castLE hD) (blocks rs (standard d)) = blocks rs (standard D) := by
  obtain ⟨e,hr,hc⟩ := columnShape_placement rs
  rw [standard_placed e hr hc hd,standard_placed e hr hc (hd.trans hD),letterLift_comp]
  rfl

end Saxl.FlagColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_TransposeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transpose Support. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

lemma canonical_sign_transpose {n : ℕ} (μ : YoungDiagram) (hμ : μ.card = n) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau μ hμ)).Equiv
      (Saxl.signTwist (Saxl.spechtRep
        (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ))))) := by
  obtain ⟨e⟩ := Saxl.specht_sign_transpose (Saxl.canonicalTableau μ hμ)
  let e' := Saxl.equivOfSubrepEq
    (Saxl.spechtSub (Saxl.transposeTableau (Saxl.canonicalTableau μ hμ)))
    (Saxl.spechtSub
      (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ)))
    (Saxl.spechtSub_tableau_independent _ _)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma canonical_self_sign {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).Equiv
      (Saxl.signTwist (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)))) := by
  obtain ⟨e⟩ := canonical_sign_transpose lam hlam
  let e' := spechtShapeEquiv hself
    (Saxl.canonicalTableau lam.transpose ((Saxl.transpose_card lam).trans hlam))
    (Saxl.canonicalTableau lam hlam)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma tensorAnti_injective {n : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (e : σ.Equiv (Saxl.signTwist τ)) :
    Function.Injective (Saxl.tensorAnti ρ e.toIntertwiningMap) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ X) e.toLinearEquiv).injective

lemma kronecker_pos_transpose {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
    (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)) := by
  obtain ⟨eL⟩ := canonical_self_sign lam hlam hself
  obtain ⟨eν⟩ := canonical_sign_transpose ν hν
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp hpos
  let A := Saxl.tensorAnti (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))
    eL.toIntertwiningMap
  let B := (Saxl.signTwistMap
    (Y := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f).comp (Saxl.signCancelMap eν.symm.toIntertwiningMap)
  apply (Saxl.kronecker_pos_iff _ _ _).mpr
  refine ⟨A.comp B, ?_⟩
  intro hz
  apply hf
  ext x
  have h := congrArg (fun F => F (eν x)) hz
  have hi : Function.Injective A := tensorAnti_injective _ eL
  apply hi
  change A (f x) = A 0
  change A (f (eν.symm (eν x))) = 0 at h
  simpa only [eν.symm_apply_apply, map_zero] using h

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ContractionNecessary
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction Necessary. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma polytabloid_action {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    polytabloid (g.symm.trans t) = wordRep n (μ.colLen 0) g (polytabloid t) := by
  rw [polytabloid_move t (g.symm.trans t)]
  have he : tableauMove t (g.symm.trans t) = g := by
    ext i
    simp [tableauMove]
  rw [he]

lemma spechtTensor_linear_ext {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (R : WordSpace n (α.colLen 0 * β.colLen 0) →ₗ[ℂ] Z)
    (h : ∀ (a' : Tableau n α) (b' : Tableau n β),
      R (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) = 0)
    (z : Specht a ⊗[ℂ] Specht b) : R (spechtTensorMap a b z) = 0 := by
  have aux (x : WordSpace n (α.colLen 0)) (hx : x ∈ spechtSub a)
      (y : WordSpace n (β.colLen 0)) (hy : y ∈ spechtSub b) :
      R (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k,rfl⟩ := hy
        dsimp only
        rw [←polytabloid_action,←polytabloid_action]
        exact h _ _
      | zero => simp
      | add y w hy hw ihy ihw => simp only [TensorProduct.tmul_add,map_add,ihy,ihw,add_zero]
      | smul c y hy ih => simp only [TensorProduct.tmul_smul,map_smul,ih,smul_zero]
    | zero => simp
    | add x w hx hw ihx ihw => simp only [TensorProduct.add_tmul,map_add,ihx,ihw,add_zero]
    | smul c x hx ih => simp only [TensorProduct.smul_tmul,TensorProduct.tmul_smul,map_smul,ih,smul_zero]
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy,add_zero]
  | tmul x y =>
    unfold spechtTensorMap
    change R (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val)) = 0
    exact aux x.val x.property y.val y.property

theorem kronecker_contraction_necessary {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (h : 0 < kronecker a b t) :
    ∃ (a' : Tableau n α) (b' : Tableau n β) (s : Tableau n μ)
      (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ),
      dotProduct (wordMap L (polytabloid s))
        (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0 := by
  classical
  obtain ⟨F,hF⟩ := (kronecker_pos_iff a b t).mp h
  let := specht_irreducible t
  have hFi : Function.Injective F := (Representation.IsIrreducible.injective_or_eq_zero (W := Specht a ⊗[ℂ] Specht b) F).resolve_right hF
  let E := (spechtTensorMap a b).comp F
  have hEi : Function.Injective E := (spechtTensorMap_injective a b).comp hFi
  obtain ⟨R,hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id (spechtRep t))
  have he : ∃ (a' : Tableau n α) (b' : Tableau n β),
      R (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0 := by
    by_contra hn
    push Not at hn
    let p : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
    have hz := spechtTensor_linear_ext a b R.toLinearMap hn (F p)
    have hi := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) => H p) hR
    change R (spechtTensorMap a b (F p)) = p at hi
    change R (spechtTensorMap a b (F p)) = 0 at hz
    have hp : p = 0 := hi.symm.trans hz
    exact polytabloid_ne_zero t (congrArg Subtype.val hp)
  obtain ⟨a',b',hab⟩ := he
  let y := wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')
  have hv : (R y).val ≠ 0 := fun hz => hab (Subtype.ext hz)
  obtain ⟨g,hg⟩ := specht_detect t (R y).property hv
  rw [wordPair_move] at hg
  let H := (spechtInclusion t).comp R
  obtain ⟨L,hL⟩ := wordMap_detects_intertwiner H y _ hg
  rw [wordMap_pair_transpose,dotProduct_comm,←polytabloid_action] at hL
  exact ⟨a',b',g.trans t,fun a b => L b a,hL⟩

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupTensor
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Tensor. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_lifts_pair {n a b A B : ℕ} (f : Fin a → Fin A) (g : Fin b → Fin B)
    (L : Fin A → Fin B → ℂ) (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (wordMap L (letterLift f x)) (letterLift g y) =
      dotProduct (wordMap (fun i j => L (f i) (g j)) x) y := by
  rw [wordMap_letterLift,wordMap_pair_transpose,dotProduct_comm,
    wordMap_letterLift,wordMap_pair_transpose,dotProduct_comm]

lemma wordMap_lifts_nonzero {n a b A B : ℕ} (f : Fin a → Fin A) (g : Fin b → Fin B)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : WordSpace n a) (y : WordSpace n b)
    (h : ∃ L : Fin a → Fin b → ℂ, dotProduct (wordMap L x) y ≠ 0) :
    ∃ L : Fin A → Fin B → ℂ,
      dotProduct (wordMap L (letterLift f x)) (letterLift g y) ≠ 0 := by
  classical
  obtain ⟨L,hL⟩ := h
  refine ⟨Function.extend f (fun i => Function.extend g (L i) 0) 0, ?_⟩
  simpa only [wordMap_lifts_pair,hf.extend_apply,hg.extend_apply] using hL

lemma wordMap_common_two {n m a b : ℕ}
    (x : WordSpace n a) (y : WordSpace n b) (z : WordSpace m a) (w : WordSpace m b)
    (h : ∃ L : Fin a → Fin b → ℂ, dotProduct (wordMap L x) y ≠ 0)
    (h' : ∃ L : Fin a → Fin b → ℂ, dotProduct (wordMap L z) w ≠ 0) :
    ∃ L : Fin a → Fin b → ℂ,
      dotProduct (wordMap L x) y ≠ 0 ∧ dotProduct (wordMap L z) w ≠ 0 := by
  classical
  have hp : pairingPolynomial x y ≠ 0 := by
    obtain ⟨L,hL⟩ := h
    intro hz
    apply hL
    rw [←pairingPolynomial_eval,hz,map_zero]
  have hq : pairingPolynomial z w ≠ 0 := by
    obtain ⟨L,hL⟩ := h'
    intro hz
    apply hL
    rw [←pairingPolynomial_eval,hz,map_zero]
  obtain ⟨v,hv,hv'⟩ := finite_polynomials_common_point (ι := Unit)
    (fun _ => pairingPolynomial z w) (fun _ => hq) (pairingPolynomial x y) hp
  exact ⟨fun a b => v (a,b),
    (pairingPolynomial_eval x y (fun a b => v (a,b))) ▸ hv,
    (pairingPolynomial_eval z w (fun a b => v (a,b))) ▸ hv' ()⟩

lemma relabelWord_polytabloid {n m : ℕ} {μ : YoungDiagram}
    (e : Fin n ≃ Fin m) (t : Tableau n μ) :
    relabelWord e (polytabloid t) = polytabloid (e.symm.trans t) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  exact (polytabloid_action t e).symm

namespace FlagColumns
open Columns

lemma standardTableau_spec (rs : List ℕ) :
    blocks rs (standard ((columnShape rs).colLen 0)) = polytabloid (standardTableau rs) :=
  (standard_exists_tableau rs).choose_spec

lemma positioned_standard {n D : ℕ} (rs : List ℕ) (e : Fin n ≃ Fin rs.sum)
    (hD : (columnShape rs).colLen 0 ≤ D) :
    positioned rs e (standard D) =
      letterLift (Fin.castLE hD) (polytabloid (e.trans (standardTableau rs))) := by
  unfold positioned
  rw [←standard_lift rs le_rfl hD,standardTableau_spec,relabelWord_letterLift,
    relabelWord_polytabloid,Equiv.symm_symm]

lemma tableau_positioned {n D : ℕ} (rs : List ℕ) (t : Tableau n (columnShape rs))
    (hD : (columnShape rs).colLen 0 ≤ D) :
    ∃ e : Fin n ≃ Fin rs.sum,
      positioned rs e (standard D) = letterLift (Fin.castLE hD) (polytabloid t) := by
  refine ⟨t.trans (standardTableau rs).symm,?_⟩
  rw [positioned_standard rs _ hD]
  have he : (t.trans (standardTableau rs).symm).trans (standardTableau rs) = t := by
    apply Equiv.ext
    intro i
    simp
  rw [he]

lemma positioned_append {n m d : ℕ} (rs ss : List ℕ)
    (e : Fin n ≃ Fin rs.sum) (f : Fin m ≃ Fin ss.sum) (N : ℕ → Fin d → ℂ) :
    ∃ g : Fin (n+m) ≃ Fin (rs++ss).sum,
      positioned (rs++ss) g N = positionProduct finSumFinEquiv.symm
        (positioned rs e N) (positioned ss f N) := by
  let g : Fin (n+m) ≃ Fin (rs++ss).sum :=
    finSumFinEquiv.symm.trans ((e.sumCongr f).trans (appendPositions rs ss).symm)
  refine ⟨g,?_⟩
  unfold positioned
  rw [blocks_append]
  funext w
  have hl : leftWord (appendPositions rs ss) (w ∘ g.symm) =
      (leftWord finSumFinEquiv.symm w) ∘ e.symm := by
    funext i
    simp [leftWord,g]
  have hr : rightWord (appendPositions rs ss) (w ∘ g.symm) =
      (rightWord finSumFinEquiv.symm w) ∘ f.symm := by
    funext i
    simp [rightWord,g]
  change blocks rs N _ * blocks ss N _ = _
  rw [hl,hr]
  rfl

lemma kronecker_pos_of_positioned {n D : ℕ} {rs ss ts : List ℕ}
    (a : Tableau n (columnShape rs)) (b : Tableau n (columnShape ss))
    (t : Tableau n (columnShape ts))
    (ea : Fin n ≃ Fin rs.sum) (eb : Fin n ≃ Fin ss.sum) (et : Fin n ≃ Fin ts.sum)
    (ha : (columnShape rs).colLen 0 ≤ D) (hb : (columnShape ss).colLen 0 ≤ D)
    (ht : (columnShape ts).colLen 0 ≤ D) (L : Fin D → Fin (D*D) → ℂ)
    (h : dotProduct (wordMap L (positioned ts et (standard D)))
      (wordTensor _ _ _ (positioned rs ea (standard D) ⊗ₜ[ℂ]
        positioned ss eb (standard D))) ≠ 0) : 0 < kronecker a b t := by
  rw [positioned_standard _ _ ha,positioned_standard _ _ hb,positioned_standard _ _ ht,
    ←letterLift_wordTensor,wordMap_lifts_pair] at h
  exact kronecker_pos_of_contraction a _ b _ t _ _ h

lemma nonzero_positioned_of_kronecker_pos {n D : ℕ} {rs ss ts : List ℕ}
    (a : Tableau n (columnShape rs)) (b : Tableau n (columnShape ss))
    (t : Tableau n (columnShape ts))
    (ha : (columnShape rs).colLen 0 ≤ D) (hb : (columnShape ss).colLen 0 ≤ D)
    (ht : (columnShape ts).colLen 0 ≤ D) (h : 0 < kronecker a b t) :
    ∃ (ea : Fin n ≃ Fin rs.sum) (eb : Fin n ≃ Fin ss.sum) (et : Fin n ≃ Fin ts.sum)
      (L : Fin D → Fin (D*D) → ℂ),
      dotProduct (wordMap L (positioned ts et (standard D)))
        (wordTensor _ _ _ (positioned rs ea (standard D) ⊗ₜ[ℂ]
          positioned ss eb (standard D))) ≠ 0 := by
  obtain ⟨a',b',t',L,hL⟩ := kronecker_contraction_necessary a b t h
  obtain ⟨ea,hea⟩ := tableau_positioned rs a' ha
  obtain ⟨eb,heb⟩ := tableau_positioned ss b' hb
  obtain ⟨et,het⟩ := tableau_positioned ts t' ht
  obtain ⟨M,hM⟩ := wordMap_lifts_nonzero (Fin.castLE ht)
    (pairLetterMap (Fin.castLE ha) (Fin.castLE hb)) (Fin.castLE_injective _)
    (pairLetterMap_injective _ _ (Fin.castLE_injective _) (Fin.castLE_injective _))
    _ _ ⟨L,hL⟩
  refine ⟨ea,eb,et,M,?_⟩
  rwa [hea,heb,het,←letterLift_wordTensor]

end FlagColumns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_KroneckerSemigroup
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kronecker Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open Columns FlagColumns

lemma tableau_card_eq {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : μ.card = n := by
  have h := Fintype.card_congr t
  simpa only [Fintype.card_fin,Fintype.card_coe,YoungDiagram.card] using h.symm

lemma columnTableau_sum {n : ℕ} {rs : List ℕ} (t : Tableau n (columnShape rs)) :
    rs.sum = n := (columnShape_card rs).symm.trans (tableau_card_eq t)

lemma columnShape_height_sum (rs : List ℕ) : (columnShape rs).colLen 0 ≤ rs.sum :=
  columnShape_height rs rs.sum (fun a ha => List.single_le_sum (fun x _ => Nat.zero_le x) a ha)

theorem kronecker_pos_append {n m : ℕ} {ra rb rt sa sb st : List ℕ}
    (a : Tableau n (columnShape ra)) (b : Tableau n (columnShape rb))
    (t : Tableau n (columnShape rt))
    (c : Tableau m (columnShape sa)) (d : Tableau m (columnShape sb))
    (u : Tableau m (columnShape st))
    (A : Tableau (n+m) (columnShape (ra++sa)))
    (B : Tableau (n+m) (columnShape (rb++sb)))
    (T : Tableau (n+m) (columnShape (rt++st)))
    (h : 0 < kronecker a b t) (h' : 0 < kronecker c d u) :
    0 < kronecker A B T := by
  have ha : (columnShape ra).colLen 0 ≤ n+m := by
    have := columnShape_height_sum ra
    rw [columnTableau_sum a] at this
    omega
  have hb : (columnShape rb).colLen 0 ≤ n+m := by
    have := columnShape_height_sum rb
    rw [columnTableau_sum b] at this
    omega
  have ht : (columnShape rt).colLen 0 ≤ n+m := by
    have := columnShape_height_sum rt
    rw [columnTableau_sum t] at this
    omega
  have hc : (columnShape sa).colLen 0 ≤ n+m := by
    have := columnShape_height_sum sa
    rw [columnTableau_sum c] at this
    omega
  have hd : (columnShape sb).colLen 0 ≤ n+m := by
    have := columnShape_height_sum sb
    rw [columnTableau_sum d] at this
    omega
  have hu : (columnShape st).colLen 0 ≤ n+m := by
    have := columnShape_height_sum st
    rw [columnTableau_sum u] at this
    omega
  obtain ⟨ea,eb,et,L,hL⟩ := nonzero_positioned_of_kronecker_pos a b t ha hb ht h
  obtain ⟨ec,ed,eu,M,hM⟩ := nonzero_positioned_of_kronecker_pos c d u hc hd hu h'
  obtain ⟨P,hP,hP'⟩ := wordMap_common_two _ _ _ _ ⟨L,hL⟩ ⟨M,hM⟩
  obtain ⟨eA,heA⟩ := positioned_append ra sa ea ec (standard (n+m))
  obtain ⟨eB,heB⟩ := positioned_append rb sb eb ed (standard (n+m))
  obtain ⟨eT,heT⟩ := positioned_append rt st et eu (standard (n+m))
  apply kronecker_pos_of_positioned A B T eA eB eT
    (by simpa [List.sum_append,columnTableau_sum a,columnTableau_sum c] using
      columnShape_height_sum (ra++sa))
    (by simpa [List.sum_append,columnTableau_sum b,columnTableau_sum d] using
      columnShape_height_sum (rb++sb))
    (by simpa [List.sum_append,columnTableau_sum t,columnTableau_sum u] using
      columnShape_height_sum (rt++st)) P
  rw [heA,heB,heT,wordTensor_positionProduct,wordMap_positionProduct,positionProduct_pair]
  exact mul_ne_zero hP hP'

end Saxl
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

lemma kronecker_pos_of_shapes {n : ℕ} {α β μ A B T : YoungDiagram}
    (ha : α = A) (hb : β = B) (ht : μ = T)
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (c : Tableau n A) (d : Tableau n B) (u : Tableau n T)
    (h : 0 < kronecker a b t) : 0 < kronecker c d u := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht b) := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup (Specht c ⊗[ℂ] Specht d) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨F,hF⟩ := (kronecker_pos_iff a b t).mp h
  let e := tensorRepEquiv (spechtShapeEquiv ha a c) (spechtShapeEquiv hb b d)
  let f := spechtShapeEquiv ht.symm u t
  apply (kronecker_pos_iff c d u).mpr
  refine ⟨e.toIntertwiningMap.comp (F.comp f.toIntertwiningMap),?_⟩
  intro hz
  apply hF
  ext x
  apply e.injective
  have hh := congrArg (fun H => H (f.symm x)) hz
  change e (F (f (f.symm x))) = 0 at hh
  change e (F x) = e (0 : Specht a ⊗[ℂ] Specht b)
  have hx : e (F x) = 0 := by simpa only [f.apply_symm_apply] using hh
  exact hx.trans e.toIntertwiningMap.toLinearMap.map_zero.symm

lemma kronecker_pos_input_transpose {n : ℕ} {α μ : YoungDiagram}
    (a : Tableau n α) (t : Tableau n μ)
    (b : Tableau n α.transpose) (h : 0 < kronecker a a t) :
    0 < kronecker b b t := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup (Specht b ⊗[ℂ] Specht b) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨e⟩ := specht_sign_transpose a
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

lemma SquareOccurs.card_eq {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    α.card = μ.card := by
  obtain ⟨n,a,t,_⟩ := h
  exact (tableau_card_eq a).trans (tableau_card_eq t).symm

lemma SquareOccurs.pos {n : ℕ} {α μ : YoungDiagram} (h : SquareOccurs α μ)
    (a : Tableau n α) (t : Tableau n μ) : 0 < kronecker a a t := by
  obtain ⟨m,b,u,hu⟩ := h
  have he : m = n := (tableau_card_eq b).symm.trans (tableau_card_eq a)
  subst m
  exact kronecker_pos_of_shapes rfl rfl rfl b b u a a t hu

lemma SquareOccurs.input_transpose {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    SquareOccurs α.transpose μ := by
  obtain ⟨n,a,t,ht⟩ := h
  exact ⟨n,transposeTableau a,t,kronecker_pos_input_transpose a t _ ht⟩

lemma SquareOccurs.target_transpose {α μ : YoungDiagram}
    (hs : α.transpose = α) (h : SquareOccurs α μ) : SquareOccurs α μ.transpose := by
  have he := h.card_eq
  let a := canonicalTableau α rfl
  let t := canonicalTableau μ he.symm
  exact ⟨α.card,a,transposeTableau t,kronecker_pos_of_shapes rfl rfl rfl _ _ _ _ _ _
    (kronecker_pos_transpose α rfl hs μ he.symm (h.pos a t))⟩

lemma columnShape_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    columnShape rs = columnShape ss := by
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  rw [columnShape_rowLen,columnShape_rowLen,h.countP_eq]

lemma SquareOccurs.append {rs ss ts us : List ℕ}
    (h : SquareOccurs (columnShape rs) (columnShape ts))
    (h' : SquareOccurs (columnShape ss) (columnShape us)) :
    SquareOccurs (columnShape (rs++ss)) (columnShape (ts++us)) := by
  obtain ⟨n,a,t,ht⟩ := h
  obtain ⟨m,b,u,hu⟩ := h'
  have he : (columnShape (rs++ss)).card = n+m := by
    rw [columnShape_card,List.sum_append,columnTableau_sum a,columnTableau_sum b]
  have hf : (columnShape (ts++us)).card = n+m := by
    rw [columnShape_card,List.sum_append,columnTableau_sum t,columnTableau_sum u]
  let A := canonicalTableau _ he
  let T := canonicalTableau _ hf
  exact ⟨n+m,A,T,kronecker_pos_append a a t b b u A A T ht hu⟩

lemma columnShape_diagram (μ : YoungDiagram) :
    columnShape μ.transpose.rowLens = μ := by
  obtain ⟨e,hr,_⟩ := columnShape_placement μ.transpose.rowLens
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  obtain ⟨f,hf,_⟩ := place_columns μ (List.Perm.refl _)
  rw [placed_rowLen e hr,placed_rowLen f hf]

lemma columnShape_sorted (rs : List ℕ) (hs : rs.SortedGE) (hp : ∀ a ∈ rs, 0 < a) :
    columnShape rs = (YoungDiagram.ofRowLens rs hs).transpose := by
  conv_lhs => rw [← YoungDiagram.rowLens_ofRowLens_eq_self hp (hw := hs)]
  simpa only [YoungDiagram.transpose_transpose] using
    columnShape_diagram ((YoungDiagram.ofRowLens rs hs).transpose)

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

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  rw [rowDiagram,columnShape_sorted rs h.1 h.2,YoungDiagram.transpose_transpose]

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

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

lemma headD_rowLens (μ : YoungDiagram) : μ.rowLens.headD 0 = μ.rowLen 0 := by
  have h (xs : List ℕ) : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  rw [h, ← ofRowLens_rowLen μ.rowLens μ.rowLens_sorted,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma transposeRows_rowLens (μ : YoungDiagram) :
    transposeRows μ.rowLens = μ.transpose.rowLens := by
  unfold transposeRows
  rw [headD_rowLens]
  conv_rhs => rw [YoungDiagram.rowLens,YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro j _
  rw [YoungDiagram.rowLen_transpose]
  have he := congrArg (fun θ : YoungDiagram => θ.colLen j) (rowDiagram_rowLens μ)
  simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using he

lemma transposeRows_eq {rs : List ℕ} (h : GoodRows rs) :
    transposeRows rs = (rowDiagram rs).transpose.rowLens := by
  conv_lhs => rw [← rowDiagram_rows h,transposeRows_rowLens]

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

lemma columnShape_transposeRows {p : List ℕ} (hp : GoodRows p) :
    columnShape (transposeRows p) = rowDiagram p := by
  rw [transposeRows_eq hp,columnShape_diagram]

lemma rowSquare_join_oai {p q x y a b : List ℕ} (hc : RowJoin p q x y a b)
    (h : RowSquare x a) (h' : RowSquare y b) : RowSquare p q := by
  obtain ⟨hp,hq,hx,hy,ha,hb,hp',hq'⟩ := hc
  unfold RowSquare at h h' ⊢
  rw [← columnShape_transposeRows hx,← columnShape_transposeRows ha] at h
  rw [← columnShape_transposeRows hy,← columnShape_transposeRows hb] at h'
  have hh := h.append h'
  have ht : SquareOccurs (rowDiagram p)
      (columnShape (transposeRows a ++ transposeRows b)) := by
    rcases hp' with hp' | hp'
    · simpa only [columnShape_perm hp',columnShape_transposeRows hp] using hh
    · rw [columnShape_perm hp'] at hh
      exact hh.input_transpose
  rcases hq' with hq' | ⟨hs,hq'⟩
  · simpa only [columnShape_perm hq',columnShape_transposeRows hq] using ht
  · rw [columnShape_perm hq'] at ht
    have hself : (rowDiagram p).transpose = rowDiagram p := by
      rw [← rowDiagram_transposeRows hp,hs]
    exact ht.target_transpose hself

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.rowSquare_join_oai := @OAI.UniversalTensorSquare.rowSquare_join_oai
