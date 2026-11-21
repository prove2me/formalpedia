-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:45:17.336618+00:00
-- url     : https://prove2.me/submissions/0403a262-ab3d-420d-aaaa-43c5889dd77e

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_band_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck35
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_12All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree35_23All
import Theorems.Thm_OAI_UniversalTensorSquare_packingPlan_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg4720

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

namespace Saxl

lemma altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  let := Fintype.ofFinite (fiberGroup c)
  let := Fintype.ofFinite (fiberGroup (c ∘ e))
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (fiberRelabel e c)
  intro g
  have hs : signC ((fiberRelabel e c g).val) = signC g.val := by
    change signC (e.permCongr g.val) = _
    simp only [signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace m d) ((w ∘ e.symm) ∘ (e.permCongr g.val))
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa [Equiv.permCongr] using congrFun h j
  · intro h
    funext i
    simpa [Equiv.permCongr] using congrFun h (e i)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

end Saxl.Columns

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
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

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
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

lemma colPrefix_eq_sum (μ : YoungDiagram) (i : ℕ) :
    colPrefix μ i = ∑ k ∈ Finset.range i, μ.colLen k := by
  simp only [colPrefix, rowPrefix, YoungDiagram.rowLen_transpose]

lemma mem_colTruncate (μ : YoungDiagram) (i : ℕ) (a b : ℕ) :
    (a,b) ∈ colTruncate μ i ↔ (a,b) ∈ μ ∧ b < i := by
  simp only [colTruncate, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    Saxl.mem_rowTruncate]

lemma rowTruncate_subset (μ : YoungDiagram) (j : ℕ) :
    (rowTruncate μ j).cells ⊆ μ.cells := by
  intro p hp
  exact (Saxl.mem_rowTruncate.mp hp).1

lemma colTruncate_subset (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).cells ⊆ μ.cells := by
  rintro ⟨a,b⟩ hp
  exact ((mem_colTruncate μ i a b).mp hp).1

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
    μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
      rowPrefix μ j + colPrefix μ i +
        (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card := by
  have hu : (rowTruncate μ j).cells ∪ (colTruncate μ i).cells ⊆ μ.cells :=
    Finset.union_subset (rowTruncate_subset μ j) (colTruncate_subset μ i)
  have h₁ := Finset.card_sdiff_add_card_eq_card hu
  have h₂ := Finset.card_union_add_card_inter
    (rowTruncate μ j).cells (colTruncate μ i).cells
  have h₃ := rowTruncate_card μ j
  have h₄ := colTruncate_card μ i
  change (rowTruncate μ j).cells.card = _ at h₃
  change (colTruncate μ i).cells.card = _ at h₄
  change μ.cells.card + _ = _
  omega

lemma corner_subset_rectangle (μ : YoungDiagram) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) ⊆
      Finset.Ico j (μ.colLen (i-1)) ×ˢ Finset.Ico i (μ.rowLen (j-1)) := by
  rintro ⟨a,b⟩ hp
  simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
    mem_rowTruncate, mem_colTruncate, not_or] at hp
  have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
  have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
  have ha' : a < μ.colLen (i-1) := YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (by omega) hp.1)
  have hb' : b < μ.rowLen (j-1) := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (by omega) le_rfl hp.1)
  simpa only [Finset.mem_product, Finset.mem_Ico] using And.intro ⟨ha, ha'⟩ ⟨hb,hb'⟩

lemma prefix_last_mul_le (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    j * μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have h := Finset.sum_le_sum (s := Finset.range j) (f := fun _ => μ.rowLen (j-1))
    (g := fun a => μ.rowLen a) (by
      intro a ha
      exact μ.rowLen_anti a (j-1) (by have := Finset.mem_range.mp ha; omega))
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h

lemma capacity_floor_bound (x f : ℕ) : x ≤ 2*((x-f)/2)+f+1 := by omega

lemma prefix_le_capacity (μ : YoungDiagram) (d q : ℕ) :
    colPrefix μ q ≤ 2*bandCapacity μ d q + q*(d+1) := by
  rw [colPrefix_eq_sum, bandCapacity]
  have h := Finset.sum_le_sum (s := Finset.range q)
    (fun k _ => capacity_floor_bound (μ.colLen k) d)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc] using h

end UniversalTensorSquare
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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_TransposeSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
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

theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) := by
  constructor
  · exact kronecker_pos_transpose lam hlam hself ν hν
  · intro h
    have ht := kronecker_pos_transpose lam hlam hself ν.transpose
      ((Saxl.transpose_card ν).trans hν) h
    obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp ht
    let e := spechtShapeEquiv (YoungDiagram.transpose_transpose ν).symm
      (Saxl.canonicalTableau ν hν)
      (Saxl.canonicalTableau ν.transpose.transpose
        ((Saxl.transpose_card ν.transpose).trans ((Saxl.transpose_card ν).trans hν)))
    apply (Saxl.kronecker_pos_iff _ _ _).mpr
    refine ⟨f.comp e.toIntertwiningMap, ?_⟩
    intro hz
    apply hf
    ext x
    have hh := congrArg (fun F => F (e.symm x)) hz
    change f (e (e.symm x)) = 0 at hh
    simpa using hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Intermediate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma first_prefix_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K)
    (h : K ≤ rowPrefix μ 4) :
    ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ K ≤ rowPrefix μ d ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  let h' : ∃ d, K ≤ rowPrefix μ d := ⟨4,h⟩
  refine ⟨Nat.find h', ?_, Nat.find_min' h' h, Nat.find_spec h', ?_⟩
  · have hx := Nat.find_spec h'
    by_contra hh
    have hd : Nat.find h' = 0 := by omega
    change K ≤ rowPrefix μ (Nat.find h') at hx
    rw [hd] at hx
    simp only [rowPrefix, Finset.range_zero, Finset.sum_empty] at hx
    omega
  · intro hd
    exact Nat.lt_of_not_ge (Nat.find_min h' (by omega))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Capacity. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma prefix_last_after_first (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    μ.rowLen 0 + (j-1)*μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have he : j = (j-1)+1 := by omega
  unfold rowPrefix
  conv_rhs => rw [he, Finset.sum_range_succ']
  have hh := Finset.sum_le_sum (s := Finset.range (j-1))
    (f := fun _ => μ.rowLen (j-1)) (g := fun a => μ.rowLen (a+1)) (by
      intro a ha
      exact μ.rowLen_anti _ _ (by have := Finset.mem_range.mp ha; omega))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
  omega

lemma endpointBound_sound (μ : YoungDiagram) {i U H : ℕ} (hi : 0 < i)
    (hU : rowPrefix μ i ≤ U) (hH : H ≤ μ.rowLen 0) :
    μ.rowLen (i-1) ≤ endpointBound i U H := by
  unfold endpointBound
  split_ifs with he
  · subst i
    simpa [rowPrefix] using hU
  · apply le_min
    · apply (Nat.le_div_iff_mul_le hi).mpr
      simpa [Nat.mul_comm] using (prefix_last_mul_le μ hi).trans hU
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < i-1)).mpr
      have h := prefix_last_after_first μ hi
      have hx : (i-1)*μ.rowLen (i-1) ≤ U-H := by omega
      simpa [Nat.mul_comm] using hx

lemma prefix_intersection_hook (μ : YoungDiagram) {i j H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0)
    (hHp : 0 < H) (hWp : 0 < W) :
    min i W + min j H - 1 ≤
      ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card := by
  let A := (rectangle 1 (min i W)).cells
  let B := (rectangle (min j H) 1).cells
  have hA : A ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < 1 ∧ b < min i W := mem_rectangle.mp hp
    have ha : a = 0 := by omega
    subst a
    have hc : (0,b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,hj⟩ ⟨hc,lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hB : B ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < min j H ∧ b < 1 := mem_rectangle.mp hp
    have hb : b = 0 := by omega
    subst b
    have hc : (a,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,lt_of_lt_of_le hx.1 (min_le_left _ _)⟩ ⟨hc,hi⟩
  have hAB : A ∩ B = {(0,0)} := by
    ext ⟨a,b⟩
    simp only [Finset.mem_inter,Finset.mem_singleton,Prod.mk.injEq]
    simp only [A,B,rectangle,Finset.mem_product,Finset.mem_range]
    omega
  have he := Finset.card_union_add_card_inter A B
  have ha : A.card = min i W := by simp [A,rectangle]
  have hb : B.card = min j H := by simp [B,rectangle]
  rw [hAB,Finset.card_singleton,ha,hb] at he
  have h := Finset.card_le_card (Finset.union_subset hA hB)
  omega

lemma area_le_refined (μ : YoungDiagram) {i j U V X Y H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V)
    (hX : μ.colLen (i-1) ≤ X) (hY : μ.rowLen (j-1) ≤ Y)
    (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0) (hHp : 0 < H) (hWp : 0 < W) :
    μ.card ≤ refinedArea i j U V X Y H W := by
  classical
  have hid := strip_area_identity μ i j
  have hh := prefix_intersection_hook μ hi hj hH hW hHp hWp
  by_cases hcell : (j-1,i-1) ∈ μ
  · have heq : (rowTruncate μ j).cells ∩ (colTruncate μ i).cells =
        (rectangle j i).cells := by
      ext ⟨a,b⟩
      simp only [Finset.mem_inter, YoungDiagram.mem_cells, mem_rowTruncate,
        mem_colTruncate, mem_rectangle]
      constructor
      · tauto
      · rintro ⟨ha,hb⟩
        have hx := μ.up_left_mem (by omega : a ≤ j-1) (by omega : b ≤ i-1) hcell
        tauto
    have hint : ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card = j*i := by
      rw [heq]
      simp only [rectangle,Finset.card_product,Finset.card_range]
    have hcor := Finset.card_le_card (corner_subset_rectangle μ hi hj)
    simp only [Finset.card_product,Nat.card_Ico] at hcor
    have hmul := Nat.mul_le_mul (Nat.sub_le_sub_right hX j) (Nat.sub_le_sub_right hY i)
    have hx : j ≤ μ.colLen (i-1) := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcell; omega
    have hy : i ≤ μ.rowLen (j-1) := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell; omega
    rw [hint] at hid
    have hup : i*j ≤ U+V := by
      have ht := prefix_last_mul_le μ.transpose hi
      simp only [YoungDiagram.rowLen_transpose] at ht
      change i * μ.colLen (i-1) ≤ colPrefix μ i at ht
      nlinarith
    have hsub := Nat.sub_add_cancel hup
    have ha : μ.card ≤ U+V-i*j+(X-j)*(Y-i) := by
      rw [Nat.mul_comm j i] at hid
      omega
    unfold refinedArea
    rw [ite_eq_left ⟨hx.trans hX,hy.trans hY⟩]
    exact ha.trans (le_max_right _ _)
  · have hz : μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff,Finset.mem_union,YoungDiagram.mem_cells,
        mem_rowTruncate,mem_colTruncate,not_or] at hp
      have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1,ha⟩
      have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1,hb⟩
      exact hcell (μ.up_left_mem (by omega) (by omega) hp.1)
    rw [hz,Finset.card_empty,add_zero] at hid
    have ha : μ.card ≤ U+V-(min i W+min j H-1) := by omega
    unfold refinedArea
    split_ifs
    · exact ha.trans (le_max_left _ _)
    · exact ha

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma minHeight_pos (n : ℕ) (B : List (ℕ × ℕ)) : 0 < minHeight n B := by
  induction B with
  | nil => simp [minHeight]
  | cons p B ih =>
    simp only [minHeight,List.foldr_cons]
    split_ifs
    · exact lt_of_lt_of_le ih (le_max_right _ _)
    · exact ih

lemma minHeight_sound {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {B : List (ℕ × ℕ)} (hb : RowBounds μ B) :
    minHeight n B ≤ μ.colLen 0 := by
  have hpos : 0 < μ.colLen 0 := by
    have hc := rowPrefix_eq_card μ (k := 0)
    by_contra h
    have hz := hc (by omega)
    simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hz
    omega
  induction B with
  | nil => exact hpos
  | cons p B ih =>
    have hp := hb p (by simp)
    have htail : RowBounds μ B := fun q hq => hb q (by simp [hq])
    simp only [minHeight,List.foldr_cons]
    split_ifs with hh
    · apply max_le _ (ih htail)
      by_contra h
      have := rowPrefix_eq_card μ (show μ.colLen 0 ≤ p.1 by omega)
      omega
    · exact ih htail

lemma rowLen_first_le_prefix (μ : YoungDiagram) {i : ℕ} (hi : 0 < i) :
    μ.rowLen 0 ≤ rowPrefix μ i := by
  have h := rowPrefix_mono μ (show 1 ≤ i from hi)
  simpa [rowPrefix] using h

lemma impossibleBounds_false {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B)
    (h : impossibleBounds n A B) : False := by
  have hH := minHeight_sound hn μ hcard hb
  have hW := minHeight_sound hn μ.transpose ((transpose_card _).trans hcard) ha
  simp only [YoungDiagram.colLen_transpose] at hW
  rcases h with ⟨p,hp,h⟩ | ⟨q,hq,h⟩ | ⟨p,hp,q,hq,h⟩
  · have hs := (rowLen_first_le_prefix μ.transpose (ha p hp).1).trans (ha p hp).2
    simp only [YoungDiagram.rowLen_transpose] at hs
    omega
  · have hs := (rowLen_first_le_prefix μ (hb q hq).1).trans (hb q hq).2
    omega
  · have hX := endpointBound_sound μ.transpose (ha p hp).1 (ha p hp).2
      (show minHeight n B ≤ μ.transpose.rowLen 0 by simpa using hH)
    have hY := endpointBound_sound μ (hb q hq).1 (hb q hq).2 hW
    have ht := area_le_refined μ (ha p hp).1 (hb q hq).1 (ha p hp).2
      (hb q hq).2 (by simpa using hX) hY hH hW (minHeight_pos n B) (minHeight_pos n A)
    omega

lemma rowPrefix_eq_take (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ k = (μ.rowLens.take k).sum := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ,ih]
    by_cases hk : k < μ.rowLens.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      congr 1
      exact YoungDiagram.get_rowLens.symm
    · have hh : μ.colLen 0 ≤ k := by simpa only [YoungDiagram.length_rowLens] using Nat.le_of_not_gt hk
      rw [rowLen_zero_of_height_le μ hh,add_zero]
      rw [List.take_of_length_le (Nat.le_of_not_gt hk),
        List.take_of_length_le (by omega : μ.rowLens.length ≤ k+1)]

lemma not_dominates_witness {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : ¬ Dominates μ θ) :
    ∃ k, 1 ≤ k ∧ k ≤ θ.colLen 0 ∧ rowPrefix μ k < rowPrefix θ k := by
  classical
  obtain ⟨k,hk⟩ := not_forall.mp h
  have hk' : rowPrefix μ k < rowPrefix θ k := Nat.lt_of_not_ge hk
  by_cases hb : k ≤ θ.colLen 0
  · refine ⟨k,?_,hb,hk'⟩
    by_contra ht
    have hz : k = 0 := by omega
    simp [hz,rowPrefix] at hk'
  · refine ⟨θ.colLen 0,?_,le_rfl,?_⟩
    · by_contra ht
      have hz : θ.colLen 0 = 0 := by omega
      have hs := rowPrefix_eq_card θ (le_of_eq hz)
      simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hs
      have hu := rowPrefix_le_card θ k
      omega
    · have hle := rowPrefix_mono μ (show θ.colLen 0 ≤ k by omega)
      rw [rowPrefix_eq_card θ (by omega), ← hc] at hk'
      rw [rowPrefix_eq_card θ le_rfl, ← hc]
      omega

lemma coreImpossible_false (μ : YoungDiagram) {K d : ℕ}
    (hd : K ≤ rowPrefix μ d) {A : List (ℕ × ℕ)} (ha : RowBounds μ A)
    (h : coreImpossible K d A) : False := by
  obtain ⟨p,hp,hpd,hpK⟩ := h
  have hle := (hd.trans (rowPrefix_mono μ hpd)).trans (ha p hp).2
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_KroneckerSemigroup
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

lemma dominates_of_rowsDom {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : RowsDom μ.rowLens θ.rowLens) : Dominates μ θ := by
  intro k
  by_cases hk : k ≤ θ.colLen 0
  · rw [rowPrefix_eq_take,rowPrefix_eq_take]
    exact h k (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  · have hh := h (θ.colLen 0) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    rw [← rowPrefix_eq_take,← rowPrefix_eq_take,rowPrefix_eq_card θ le_rfl,← hc] at hh
    rw [rowPrefix_eq_card θ (by omega),← hc]
    exact hh.trans (rowPrefix_mono μ (by omega))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma mem_partitionLists (k : ℕ) (rs : List ℕ) (n b : ℕ)
    (hsum : rs.sum = n) (hlen : rs.length ≤ k)
    (hpos : ∀ a ∈ rs, 0 < a) (hbound : ∀ a ∈ rs, a ≤ b)
    (hsort : rs.SortedGE) : rs ∈ partitionLists k n b := by
  induction k generalizing rs n b with
  | zero =>
    have hr : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [partitionLists]
  | succ k ih =>
    cases rs with
    | nil =>
      simp only [List.sum_nil] at hsum
      subst n
      simp [partitionLists]
    | cons a rs =>
      have ha : 0 < a := hpos a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      have hab : a ≤ b := hbound a (by simp)
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_Icc.mpr ⟨ha, le_min han hab⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨rs, ih rs (n-a) a ?_ ?_ ?_ ?_ ?_, rfl⟩
      · simp only [List.sum_cons] at hsum
        omega
      · simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
      · intro x hx
        exact hpos x (by simp [hx])
      · intro x hx
        exact (List.pairwise_cons.mp hsort.pairwise).1 x hx
      · exact (List.pairwise_cons.mp hsort.pairwise).2.sortedGE

lemma rowLens_mem_partitionLists (μ : YoungDiagram) :
    μ.rowLens ∈ partitionLists μ.card μ.card μ.card := by
  apply mem_partitionLists
  · exact (Saxl.card_eq_sum_rowLens μ).symm
  · rw [Saxl.card_eq_sum_rowLens]
    exact List.length_le_sum_of_one_le _ fun a ha => μ.pos_of_mem_rowLens a ha
  · exact fun a ha => μ.pos_of_mem_rowLens a ha
  · intro a ha
    rw [Saxl.card_eq_sum_rowLens]
    exact List.single_le_sum (fun x _ => Nat.zero_le x) a ha
  · exact μ.rowLens_sorted

lemma diagramOfCols_cols (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) : (diagramOfCols rs hs).transpose.rowLens = rs := by
  simp only [diagramOfCols, YoungDiagram.transpose_transpose]
  exact YoungDiagram.rowLens_ofRowLens_eq_self hp

lemma eq_diagramOfCols (μ : YoungDiagram) (rs : List ℕ) (hs : rs.SortedGE)
    (h : μ.transpose.rowLens = rs) : μ = diagramOfCols rs hs := by
  subst rs
  simp only [diagramOfCols, YoungDiagram.ofRowLens_to_rowLens_eq_self,
    YoungDiagram.transpose_transpose]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ColumnCertificates
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Certificates. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma polytabloid_reindex {n m : ℕ} {μ : YoungDiagram} (t : Tableau m μ)
    (e : Fin n ≃ Fin m) (w : Fin n → Fin (μ.colLen 0)) :
    polytabloid (e.trans t) w = polytabloid t (w ∘ e.symm) := by
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord]
  exact (altWord_fiber_relabel e (fun i => (t i).val.2) (rowWord t) w).symm

namespace Columns

lemma polytabloid_column_expansion (μ : YoungDiagram) :
    polytabloid (columnTableau μ) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π) 1 := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  rw [polytabloid_eq_altWord, altWord_inverse_sum]
  symm
  apply Fintype.sum_equiv (columnEquiv μ)
  intro π
  rw [← columnPerm_sign μ π]
  congr 2
  funext q
  apply Fin.ext
  change row (perm π (enumerate μ.transpose.rowLens q)) =
    ((columnTableau μ) ((columnEquiv μ π).val q)).val.1
  rw [columnTableau_val]
  simp only [columnEquiv, Equiv.ofBijective_apply, columnPerm, Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]

lemma polytabloid_placed_expansion {n : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin μ.transpose.rowLens.sum) :
    polytabloid (e.trans (columnTableau μ)) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π ∘ e) 1 := by
  classical
  funext w
  rw [polytabloid_reindex, polytabloid_column_expansion]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hw
    funext q
    have h := congrFun hw (e q)
    simpa using h
  · intro hw
    funext q
    have h := congrFun hw (e.symm q)
    simpa using h

lemma sgInteger_cast {rs : List ℕ} (π : Perms rs) : (sgInteger π : ℂ) = sg π := by
  induction rs with
  | nil => simp [sgInteger, sg]
  | cons r rs ih => simp only [sgInteger, sg, Int.cast_mul, ih]

lemma contractionInteger_correct {n : ℕ} (α β μ : YoungDiagram)
    (rsA rsB rsT : List ℕ) (ha : α.transpose.rowLens = rsA)
    (hb : β.transpose.rowLens = rsB) (ht : μ.transpose.rowLens = rsT)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) :
    dotProduct (wordMap (pairFlag L) (polytabloid (tableFor μ rsT ht et)))
      (wordTensor _ _ _ (polytabloid (tableFor α rsA ha ea) ⊗ₜ[ℂ]
        polytabloid (tableFor β rsB hb eb))) =
      (contractionInteger rsA rsB rsT ea eb et L : ℂ) := by
  subst rsA rsB rsT
  simp only [tableFor, polytabloid_placed_expansion, map_sum, map_smul,
    sum_dotProduct, smul_dotProduct]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul_smul, map_sum, map_smul, wordTensor_single,
    dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_single_one, wordMap_single,
    contractionInteger, Int.cast_sum, Int.cast_mul, Int.cast_prod, sgInteger_cast]
  apply Finset.sum_congr rfl
  intro π hπ
  conv_lhs => arg 2; rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  simp only [mul_assoc]
  congr 3
  apply Finset.prod_congr rfl
  intro q hq
  simp only [pairFlag, mergeWords, Equiv.symm_apply_apply, signedRowWord, Function.comp_apply]

theorem kronecker_pos_of_integer_certificate {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (rsA rsB rsT : List ℕ) (ha : α.transpose.rowLens = rsA)
    (hb : β.transpose.rowLens = rsB) (ht : μ.transpose.rowLens = rsT)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) (hcert : contractionInteger rsA rsB rsT ea eb et L ≠ 0) :
    0 < kronecker a b t := by
  apply kronecker_pos_of_contraction a (tableFor α rsA ha ea)
    b (tableFor β rsB hb eb) t (tableFor μ rsT ht et) (pairFlag L)
  rw [contractionInteger_correct]
  exact_mod_cast hcert

end Columns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma Domains.full_weight {rs : List ℕ} (σ : Perms rs) :
    (full rs).weight σ = sgInteger σ := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full, weight, sgInteger, Finset.mem_univ, ite_true, if_true, ih]

lemma Domains.atValue_weight {rs : List ℕ} (D : Domains rs) (c : Cells rs)
    (j : ℕ) (σ : Perms rs) :
    (D.atValue c j).weight σ = D.weight σ *
      (if row (perm σ c) = j then 1 else 0) := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    cases c with
    | inl i =>
      simp only [atValue, weight, Finset.mem_filter, perm, Equiv.sumCongr_apply,
        Sum.map_inl, row]
      split_ifs <;> simp_all
    | inr c =>
      simp only [atValue, weight, perm, Equiv.sumCongr_apply, Sum.map_inr, row, ih,
        mul_assoc]

lemma Domains.weight_eq_zero {rs : List ℕ} (D : Domains rs)
    (h : D.vanished = true) (σ : Perms rs) : D.weight σ = 0 := by
  induction rs with
  | nil => simp [vanished] at h
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    simp only [vanished, Bool.or_eq_true] at h
    rcases h with h | h
    · have hs : s = ∅ := of_decide_eq_true h
      simp [weight, hs]
    · simp only [weight, ih D h σ, mul_zero]

lemma Domains.mass_eq_sum {rs : List ℕ} (D : Domains rs) :
    D.mass = ∑ σ : Perms rs, D.weight σ := by
  classical
  induction rs with
  | nil => simp [mass, weight, Perms]
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [Perms, Fintype.sum_prod_type, weight, ← Finset.mul_sum, ← ih,
      ← Finset.sum_mul, mass]
    congr 1
    simp

lemma domainContraction_nil {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F [] flag = D.mass * E.mass * F.mass := by
  simp only [domainContraction, List.map_nil, List.prod_nil, mul_one,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Domains.mass_eq_sum]

lemma domainContraction_zero {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : (D.vanished || E.vanished || F.vanished) = true) :
    domainContraction D E F edges flag = 0 := by
  rw [domainContraction]
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · simp only [Domains.weight_eq_zero D h, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero E h, mul_zero, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero F h, mul_zero, zero_mul, Finset.sum_const_zero]

lemma triple_indicator_sum (flag : Finset (ℕ × ℕ × ℕ)) (a b c : ℕ) :
    (∑ v ∈ flag, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0)) =
      if (a,b,c) ∈ flag then 1 else 0 := by
  have hh : ∀ v : ℕ × ℕ × ℕ, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0) =
      if (a,b,c) = v then 1 else 0 := by
    rintro ⟨x,y,z⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [hh]
  rw [Finset.sum_ite_eq]

lemma domainContraction_cons {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  classical
  simp only [domainContraction, List.map_cons, List.prod_cons, Domains.atValue_weight]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  trans (D.weight π * E.weight σ * F.weight τ) *
    (∑ v ∈ flag, (if row (perm π c.1) = v.1 then (1 : ℤ) else 0) *
      (if row (perm σ c.2.1) = v.2.1 then 1 else 0) *
      (if row (perm τ c.2.2) = v.2.2 then 1 else 0)) *
    (edges.map (fun e => if (row (perm π e.1), row (perm σ e.2.1),
      row (perm τ e.2.2)) ∈ flag then (1 : ℤ) else 0)).prod
  · rw [triple_indicator_sum]
    ring
  · simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring

lemma domainContraction_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    {cs es : List (Edge rsT rsA rsB)} (hp : cs.Perm es)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F cs flag = domainContraction D E F es flag := by
  simp only [domainContraction]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  exact congrArg (_ * ·) ((hp.map _).prod_eq)

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_DomainSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain Solver. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma domainContraction_cons_options {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ edgeOptions D E F c flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  rw [domainContraction_cons, edgeOptions, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with h
  · rfl
  · apply domainContraction_zero
    simpa only [Bool.or_eq_true, Bool.not_eq_false, not_and_or, or_assoc] using h

lemma bringBest_perm {α : Type*} (score : α → ℕ) (cs : List α) :
    (bringBest score cs).Perm cs := by
  induction cs with
  | nil => exact List.Perm.refl _
  | cons c cs ih =>
    rw [bringBest]
    cases he : bringBest score cs with
    | nil =>
      rw [he] at ih
      exact List.Perm.cons c ih
    | cons d ds =>
      rw [he] at ih
      simp only
      split_ifs
      · exact List.Perm.cons c ih
      · exact (List.Perm.swap _ _ _).trans (List.Perm.cons c ih)

lemma orderEdges_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    (orderEdges D E F edges flag).Perm edges := bringBest_perm _ _

theorem solveDomains_correct {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : edges.length ≤ fuel) :
    solveDomains fuel D E F edges flag = domainContraction D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    have hh : orderEdges D E F edges flag = [] := by
      apply List.length_eq_zero_iff.mp
      rw [(orderEdges_perm D E F edges flag).length_eq]
      omega
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · rw [hh]
      rw [← domainContraction_perm D E F (orderEdges_perm D E F edges flag) flag, hh]
      exact (domainContraction_nil D E F flag).symm
  | succ fuel ih =>
    rw [solveDomains]
    split_ifs with hv
    · exact (domainContraction_zero D E F edges flag hv).symm
    · have hp := orderEdges_perm D E F edges flag
      rw [← domainContraction_perm D E F hp flag]
      cases he : orderEdges D E F edges flag with
      | nil => exact (domainContraction_nil D E F flag).symm
      | cons c cs =>
        have hlen : cs.length ≤ fuel := by
          have hl := hp.length_eq
          rw [he, List.length_cons] at hl
          omega
        rw [domainContraction_cons_options]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih _ _ _ _ hlen

lemma contractionInteger_domains {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      domainContraction (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  simp only [contractionInteger, domainContraction, Domains.full_weight,
    certificateEdges, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

theorem contractionInteger_solve {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveDomains n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [solveDomains_correct n _ _ _ _ _ (by simp [certificateEdges])]
  exact contractionInteger_domains ..

end Saxl.Columns
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_VectorDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma permVector_get {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (permVector π)[i.val]?.getD 0 = (π i).val := by
  simp [permVector,i.isLt]

lemma sign_eq_aux {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = Equiv.Perm.signAux π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => simp [Equiv.Perm.signAux_one]
  | swap_mul π i j hij ih =>
    rw [Equiv.Perm.sign_mul,Equiv.Perm.signAux_mul,ih,
      Equiv.Perm.sign_swap hij,Equiv.Perm.signAux_swap hij]

lemma vectorSign_perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    vectorSign n (permVector π) = (Equiv.Perm.sign π : ℤ) := by
  rw [sign_eq_aux]
  simp only [vectorSign,Equiv.Perm.signAux,Units.coe_prod,permVector_get]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.le_def]
  split_ifs <;> rfl

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_CompactDomainsCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Domains Core. -/

section

open scoped BigOperators
namespace Saxl.Columns

lemma CompactDomain.mem_describe {n : ℕ} (π σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    σ ∈ CompactDomain.describe (some (π,s)) ↔ ∀ i, i ∉ s → σ i = π i := by
  simp [describe]

lemma CompactDomain.describe_full (n : ℕ) : (full n).describe = Finset.univ := by
  ext σ; simp [full,mem_describe]

lemma CompactDomain.describe_atValue {n : ℕ} (D : CompactDomain n) (i : Fin n) (j : ℕ) :
    (D.atValue i j).describe = D.describe.filter (fun σ => (σ i).val = j) := by
  cases D with
  | none => simp [atValue,describe]
  | some ds =>
    rcases ds with ⟨π,s⟩
    ext σ
    simp only [Finset.mem_filter,mem_describe]
    by_cases hj : j < n
    · let k := π.symm ⟨j,hj⟩
      have hk : π k = ⟨j,hj⟩ := π.apply_symm_apply _
      by_cases hi : i ∈ s
      · by_cases hks : k ∈ s
        · simp only [atValue,dite_eq_left hj,ite_eq_left hi,show π.symm ⟨j,hj⟩ ∈ s from hks,
            ite_true, if_true,mem_describe]
          constructor
          · intro h
            constructor
            · intro x hx
              have hxi : x ≠ i := by intro he; subst x; exact hx hi
              have hxk : x ≠ π.symm ⟨j,hj⟩ := by intro he; subst x; exact hx hks
              simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxi hxk] using
                h x (by simp [hx])
            · have hh := h i (by simp)
              simpa [Equiv.Perm.mul_apply,k] using congrArg Fin.val hh
          · rintro ⟨h,hv⟩ x hx
            by_cases hxi : x = i
            · subst x
              simpa [Equiv.Perm.mul_apply,k] using (Fin.ext hv : σ i = ⟨j,hj⟩)
            · have hxs : x ∉ s := by simpa [Finset.mem_erase,hxi] using hx
              have hxk : x ≠ π.symm ⟨j,hj⟩ := by intro he; subst x; exact hxs hks
              simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hxi hxk] using h x hxs
        · simp only [atValue,dite_eq_left hj,ite_eq_left hi,show π.symm ⟨j,hj⟩ ∉ s from hks,
            ite_false, if_false,describe,Finset.notMem_empty,false_iff,not_and]
          intro h hv
          have hki : k = i := σ.injective ((h k hks).trans (hk.trans (Fin.ext hv).symm))
          exact hks (hki.symm ▸ hi)
      · by_cases hv : (π i).val = j
        · simp only [atValue,dite_eq_left hj,ite_eq_right hi,ite_eq_left hv,mem_describe]
          exact ⟨fun h => ⟨h,(congrArg Fin.val (h i hi)).trans hv⟩,fun h => h.1⟩
        · simp only [atValue,dite_eq_left hj,ite_eq_right hi,ite_eq_right hv,describe,Finset.notMem_empty,
            false_iff,not_and]
          intro h he
          exact hv ((congrArg Fin.val (h i hi)).symm.trans he)
    · simp only [atValue,dite_eq_right hj,describe,Finset.notMem_empty,false_iff,not_and]
      intro h hv
      exact hj (hv ▸ (σ i).isLt)

lemma CompactDomain.describe_vanished {n : ℕ} (D : CompactDomain n) :
    decide (D.describe = ∅) = D.vanished := by
  cases D with
  | none => rfl
  | some ds =>
    rcases ds with ⟨π,s⟩
    have hh : π ∈ CompactDomain.describe (some (π,s)) := by simp only [mem_describe]; tauto
    have hn := Finset.ne_empty_of_mem hh
    simp only [hn,decide_false,vanished,Option.isNone_some]

lemma compact_sum_sign {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) =
      if s.card ≤ 1 then (Equiv.Perm.sign π : ℤ) else 0 := by
  by_cases hs : s.card ≤ 1
  · rw [ite_eq_left hs]
    have he : CompactDomain.describe (some (π,s)) = {π} := by
      ext σ
      rw [CompactDomain.mem_describe,Finset.mem_singleton]
      constructor
      · intro h
        apply Equiv.ext
        intro i
        by_cases hi : i ∈ s
        · let k := π.symm (σ i)
          have hk : π k = σ i := π.apply_symm_apply _
          by_cases hks : k ∈ s
          · have hki : k = i := Finset.card_le_one.mp hs k hks i hi
            exact (hki ▸ hk).symm
          · have hki : k = i := σ.injective ((h k hks).trans hk)
            exact (hki ▸ hk).symm
        · exact h i hi
      · rintro rfl i hi; rfl
    simp only [he,Finset.sum_singleton]
  · rw [ite_eq_right hs]
    obtain ⟨i,hi,k,hk,hik⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    let τ := Equiv.swap i k
    have ht : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hik
    have hm (σ : Equiv.Perm (Fin n)) :
        σ * τ ∈ CompactDomain.describe (some (π,s)) ↔
        σ ∈ CompactDomain.describe (some (π,s)) := by
      simp only [CompactDomain.mem_describe]
      have hh (x : Fin n) (hx : x ∉ s) : τ x = x := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro he; subst x; exact hx hi
        · intro he; subst x; exact hx hk
      simp only [Equiv.Perm.mul_apply]
      constructor <;> intro h x hx <;> simpa only [hh x hx] using h x hx
    have he : (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) =
        ∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign (σ * τ) : ℤ) := by
      apply Finset.sum_bij (fun σ _ => σ * τ)
      · intro σ hσ; exact (hm σ).mpr hσ
      · intro σ hσ ρ hρ h; exact mul_right_cancel h
      · intro σ hσ
        refine ⟨σ * τ,(hm σ).mpr hσ,?_⟩
        simp [τ,mul_assoc]
      · intro σ hσ
        simp [τ,mul_assoc]
    have hn : (∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign (σ * τ) : ℤ)) =
        -(∑ σ ∈ CompactDomain.describe (some (π,s)), (Equiv.Perm.sign σ : ℤ)) := by
      simp only [Equiv.Perm.sign_mul,ht,Units.val_neg,mul_neg_one,
        Finset.sum_neg_distrib]
    omega

lemma CompactDomain.describe_mass {n : ℕ} (D : CompactDomain n) :
    (∑ σ ∈ D.describe, (Equiv.Perm.sign σ : ℤ)) = D.mass := by
  cases D with
  | none => simp [describe,mass]
  | some ds =>
    rcases ds with ⟨π,s⟩
    simp only [mass,vectorSign_perm,compact_sum_sign]

lemma CompactDomains.describe_full (rs : List ℕ) : (full rs).describe = Domains.full rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full,describe,Domains.full,CompactDomain.describe_full,ih]; rfl

lemma CompactDomains.describe_atValue {rs : List ℕ} (D : CompactDomains rs) (c : Cells rs) (j : ℕ) :
    (D.atValue c j).describe = D.describe.atValue c j := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    cases c with
    | inl i => simp only [atValue,describe,Domains.atValue,CompactDomain.describe_atValue]; rfl
    | inr c => simp only [atValue,describe,Domains.atValue,ih]; rfl

lemma CompactDomains.describe_vanished {rs : List ℕ} (D : CompactDomains rs) :
    D.describe.vanished = D.vanished := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [describe,Domains.vanished,vanished,CompactDomain.describe_vanished,ih]

lemma CompactDomains.describe_mass {rs : List ℕ} (D : CompactDomains rs) :
    D.describe.mass = D.mass := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [describe,Domains.mass,mass,CompactDomain.describe_mass,ih]

lemma compactEdgeOptions_describe {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (c : Edge rsT rsA rsB) (flag : Finset (ℕ × ℕ × ℕ)) :
    edgeOptions D.describe E.describe F.describe c flag = compactEdgeOptions D E F c flag := by
  simp only [compactEdgeOptions,edgeOptions,← CompactDomains.describe_atValue,
    CompactDomains.describe_vanished]

lemma compactOrderEdges_describe {rsT rsA rsB : List ℕ}
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    orderEdges D.describe E.describe F.describe edges flag = compactOrderEdges D E F edges flag := by
  simp only [compactOrderEdges,orderEdges,compactEdgeOptions_describe]

lemma solveCompact_describe {rsT rsA rsB : List ℕ} (fuel : ℕ)
    (D : CompactDomains rsT) (E : CompactDomains rsA) (F : CompactDomains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) :
    solveDomains fuel D.describe E.describe F.describe edges flag = solveCompact fuel D E F edges flag := by
  induction fuel generalizing D E F edges with
  | zero =>
    rw [solveCompact,solveDomains]
    simp only [CompactDomains.describe_vanished,compactOrderEdges_describe,CompactDomains.describe_mass]
    all_goals (split <;> rfl)
  | succ fuel ih =>
    rw [solveCompact,solveDomains]
    simp only [CompactDomains.describe_vanished,compactOrderEdges_describe,CompactDomains.describe_mass]
    split
    · rfl
    · cases he : compactOrderEdges D E F edges flag with
      | nil => rfl
      | cons c cs =>
        simp only [compactEdgeOptions_describe,← CompactDomains.describe_atValue,ih]

lemma contractionInteger_compact {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveCompact n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  rw [contractionInteger_solve,← CompactDomains.describe_full,← CompactDomains.describe_full,
    ← CompactDomains.describe_full,solveCompact_describe]

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CandidateColumns
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma candidate_rowLens {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1 := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]
    simp [candidateLengths]
  apply List.ext_getElem
  · simp only [YoungDiagram.length_rowLens,hh,List.length_append,List.length_cons,
      List.length_nil,List.length_reverse,List.length_range',List.length_replicate]
    omega
  · intro i hi hj
    rw [YoungDiagram.get_rowLens,candidate_rowLen _ _ _ _ hM]
    by_cases hi0 : i = 0
    · subst i
      simp [candidateLengths]
    by_cases hi1 : i = 1
    · subst i
      simp [candidateLengths]
    have hi2 : 2 ≤ i := by omega
    have hlen : i < M+b+δ := by simpa only [YoungDiagram.length_rowLens,hh] using hi
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons,List.length_nil, Nat.zero_add]
    simp only [candidateLengths,ite_eq_right hi0,ite_eq_right hi1]
    by_cases him : i < M-2
    · rw [ite_eq_left him,List.getElem_append_left (by simp; omega),List.getElem_reverse,
        List.getElem_range']
      simp only [List.length_range',Nat.one_mul]
      omega
    · rw [ite_eq_right him,List.getElem_append_right (by simp; omega)]
      simp only [List.length_reverse,List.length_range']
      by_cases hib : i < M-1+b
      · rw [ite_eq_left hib,List.getElem_append_left (by simp; omega),List.getElem_replicate]
      · rw [ite_eq_right hib,ite_eq_left hlen,List.getElem_append_right (by simp; omega),
          List.getElem_replicate]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_SentinelExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sentinel Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma testWidth_valid_pos {M f : ℕ} (hf : 1 ≤ f) (hw : 0 < testWidth M f) :
    testWidth M f ≤ 8 ∧ f * testWidth M f + 7 + f ≤ 2*M-1 := by
  refine ⟨min_le_left _ _, ?_⟩
  have hh := Nat.mul_le_mul_left f (min_le_right 8 ((2*M-8-f)/f))
  have hh' := Nat.div_mul_le_self (2*M-8-f) f
  have hq : 0 < (2*M-8-f)/f := lt_of_lt_of_le hw (min_le_right _ _)
  have hn : f ≤ 2*M-8-f := by simpa using (Nat.le_div_iff_mul_le (by omega)).mp hq
  unfold testWidth
  nlinarith [Nat.sub_add_cancel (show f ≤ 2*M-8 by omega),
    Nat.sub_add_cancel (show 8 ≤ 2*M by omega),
    Nat.sub_add_cancel (show 1 ≤ 2*M by omega)]

lemma sentinel_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K) :
    ∃ d, 1 ≤ d ∧ d ≤ 5 ∧ (d ≤ 4 → K ≤ rowPrefix μ d) ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  by_cases hh : K ≤ rowPrefix μ 4
  · obtain ⟨d,hd,h4,hp,hl⟩ := first_prefix_height μ hK hh
    exact ⟨d,hd,by omega,fun _ => hp,hl⟩
  · exact ⟨5,by decide,le_rfl,by omega,by simpa using Nat.lt_of_not_ge hh⟩

lemma prefixBounds_sound_sentinel (μ : YoungDiagram) {M r d e : ℕ}
    (hM : 1 ≤ M) (hr : 0 < r)
    (hd : 1 < d → colPrefix μ (d-1) < 2*M-1)
    (he : e ≤ 4 → 2*M-1 ≤ rowPrefix μ e) (hfail : ¬BandTest M r μ) :
    ∀ p ∈ prefixBounds M r d e, 0 < p.1 ∧ colPrefix μ p.1 ≤ p.2 := by
  intro p hp
  simp only [prefixBounds,List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hd'
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      subst p
      exact ⟨by omega,by have := hd hd'; dsimp; omega⟩
    · simp at hp
  · obtain ⟨k,hk,hkp⟩ := List.mem_filterMap.mp hp
    simp only [List.mem_range] at hk
    split_ifs at hkp with hke
    · have hp' := Option.some.inj hkp
      subst p
      have hw := testWidth_valid_pos (by omega : 1 ≤ k+1) hke.2
      have hc : bandCapacity μ (k+1) (testWidth M (k+1)) < r := by
        by_contra hh
        apply hfail
        exact ⟨k+1,by omega,by omega,testWidth M (k+1),hw.1,
          (he (by omega)).trans (rowPrefix_mono μ hke.1),hw.2,by omega⟩
      have hb := prefix_le_capacity μ (k+1) (testWidth M (k+1))
      exact ⟨hke.2,by dsimp; omega⟩

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

lemma SquareOccurs.of_packing {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
    (hv : p.Valid d) (hb : BandsValid p.bands) (hh : lam.colLen 0 = d)
    (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
    (hlam : lam.card = n) (hμ : μ.card = n)
    (hd : Dominates μ (rowDiagram p.parts)) : SquareOccurs lam μ := by
  exact ⟨n,canonicalTableau lam hlam,canonicalTableau μ hμ,
    packingPlan_pos p hv hb hh hc hp _ _ hd⟩

end UniversalTensorSquare

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma candidate_cone {n M b δ : ℕ} (hM : 4 ≤ M)
    (hn : (candidate M b δ).card = n) (p : PackingPlan) (q : List ℕ)
    (hq : GoodRows q) (hqn : q.sum = n)
    (hv : p.Valid (M+b+δ)) (hb : BandsValid p.bands)
    (hc : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hp : p.parts.Perm q) (μ : YoungDiagram) (hμ : μ.card = n)
    (hd : RowsDom μ.rowLens q) : SquareOccurs (candidate M b δ) μ := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  apply SquareOccurs.of_packing p hv hb hh
  · rw [candidate_transpose,candidate_rowLens hM]; exact hc
  · exact fun a ha => hq.2 a (hp.mem_iff.mp ha)
  · exact hn
  · exact hμ
  · have he : rowDiagram p.parts = rowDiagram q := by
      unfold rowDiagram; rw [columnShape_perm hp]
    rw [he]
    apply dominates_of_rowsDom
    · rw [rowDiagram_card,hqn,hμ]
    · simpa only [rowDiagram_rows hq] using hd

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

theorem semantic_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (P : List ℕ → Prop)
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens P) :
    BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨
      Dominates μ.transpose θ ∨ P μ.rowLens := by
  classical
  by_contra hh
  push Not at hh
  rcases hh with ⟨hband,hband',hdom,hdom',hP⟩
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := sentinel_height μ.transpose (show 0 < 2*M-1 by omega)
  obtain ⟨e,he,he',hWe,hWe'⟩ := sentinel_height μ (show 0 < 2*M-1 by omega)
  obtain ⟨a,ha,ha',hA⟩ := not_dominates_witness ((transpose_card _).trans hc |>.trans ht.symm) hdom'
  obtain ⟨b,hb,hb',hB⟩ := not_dominates_witness (hc.trans ht.symm) hdom
  have hAf := prefixBounds_sound_sentinel μ hM hr hHd' hWe hband
  have hBf := prefixBounds_sound_sentinel μ.transpose hM hr
    (by simpa only [colPrefix,YoungDiagram.transpose_transpose] using hWe') hHd hband'
  let A := prefixBounds M r d e ++ [(a,(θ.rowLens.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(θ.rowLens.take b).sum-1)]
  have hAbb : RowBounds μ.transpose A := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hAf p hp
    · have heq : p = (a,(θ.rowLens.take a).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hA
      exact ⟨ha,by dsimp; omega⟩
  have hBbb : RowBounds μ B := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simpa only [colPrefix,YoungDiagram.transpose_transpose] using hBf p hp
    · have heq : p = (b,(θ.rowLens.take b).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hB
      exact ⟨hb,by dsimp; omega⟩
  have h := check (d-1) (by simp; omega) (e-1) (by simp; omega)
    (a-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    (b-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  have hde : d-1+1 = d := by omega
  have hee : e-1+1 = e := by omega
  have hae : a-1+1 = a := by omega
  have hbe : b-1+1 = b := by omega
  rw [hde,hee,hae,hbe] at h
  rcases h with ⟨h4,h⟩ | ⟨h4,h⟩ | h | h
  · exact coreImpossible_false μ.transpose (hHd h4) hAbb h
  · exact coreImpossible_false μ (hWe h4) hBbb h
  · exact impossibleBounds_false hn μ hc hAbb hBbb h
  · exact hP (h μ hc hAbb hBbb)

theorem candidate_semantic_pos {n M b δ r : ℕ} (hM : 4 ≤ M)
    (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
    (hn : (candidate M b δ).card = n)
    (q : List ℕ) (hq : GoodRows q) (hqn : q.sum = n)
    (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
    (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hparts : p.parts.Perm q) (P : List ℕ → Prop)
    (hP : ∀ rs, GoodRows rs → rs.sum = n → P rs → SquareOccurs (candidate M b δ) (rowDiagram rs))
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (c+1) q P)
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  have hposn : 0 < n := by rw [← hn,candidate_card _ _ _ (by omega)]; omega
  have hp : ∀ a ∈ p.parts, 0 < a := fun a ha => hq.2 a (hparts.mem_iff.mp ha)
  have hshape : (columnShape p.parts).transpose = rowDiagram q := by
    rw [columnShape_perm hparts]; rfl
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  have hc : p.columns.Perm (candidate M b δ).transpose.rowLens := by
    rw [candidate_transpose,candidate_rowLens hM]; exact hcols
  have cone (ν : YoungDiagram) (hν : ν.card = n) (hd : Dominates ν (rowDiagram q)) :
      0 < kronecker (canonicalTableau (candidate M b δ) hn)
        (canonicalTableau (candidate M b δ) hn) (canonicalTableau ν hν) := by
    apply packingPlan_pos p hv hbands hh hc hp
    simpa only [hshape] using hd
  have htcheck : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range (rowDiagram q).rowLens.length, ∀ c ∈ List.range (rowDiagram q).rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (c+1) (rowDiagram q).rowLens P := by
    simpa only [rowDiagram_rows hq] using check
  rcases semantic_capacity_dichotomy μ (rowDiagram q) hposn (by omega) hrpos hμ
    ((rowDiagram_card q).trans hqn) P htcheck with h | h | h | h | h
  · exact band_kronecker_pos hM hδ hr _ μ _ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact band_kronecker_pos hM hδ hr _ μ.transpose _ h
  · exact cone μ hμ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact cone μ.transpose ((transpose_card μ).trans hμ) h
  · have ht := hP μ.rowLens ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩
      ((card_eq_sum_rowLens μ).symm.trans hμ) h
    rw [rowDiagram_rowLens] at ht
    exact ht.pos _ _

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ResidualTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

namespace RowTree

lemma find_sound {P : List ℕ → Prop} {t : RowTree} (h : t.All P)
    {rs : List ℕ} (hf : t.find rs = true) : P rs := by
  induction t with
  | empty => simp [find] at hf
  | node key l r hl hr =>
    simp only [find] at hf
    obtain ⟨hk,hL,hR⟩ := h
    split_ifs at hf with he hc
    · simpa only [he] using hk
    · exact hl hL hf
    · exact hr hR hf

end RowTree

lemma treeResidual_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs : List (List ℕ)} {t : RowTree}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (htree : t.All (fun rs => SquareOccurs (candidate M b δ) (rowDiagram rs)))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : TreeResidual M r qs t rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  rcases h with h | h | h
  · exact residualProperty_sound hM hδ hn hre hcones (by simp) hgood hsum h
  · exact RowTree.find_sound htree h
  · have hh := RowTree.find_sound htree h
    rw [rowDiagram_transposeRows hgood] at hh
    simpa only [YoungDiagram.transpose_transpose] using
      hh.target_transpose (candidate_transpose M b δ)

lemma rowDiagram_candidate {M b δ : ℕ} (hM : 4 ≤ M) :
    rowDiagram ([M+b+δ,M-1+b] ++ (List.range' 3 (M-4)).reverse ++
      List.replicate (b+1) 2 ++ List.replicate (1+δ) 1) = candidate M b δ := by
  rw [← candidate_rowLens hM, rowDiagram_rowLens]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCone35_1 (μ : YoungDiagram) (hμ : μ.card = 35)
    (hd : RowsDom μ.rowLens degreeRows35_1) : SquareOccurs (candidate 6 3 1) μ := by
  exact candidate_cone (by decide) degreeCard35 degreePlan35_1 degreeRows35_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

lemma degreeCones35 : ∀ q ∈ degreeQs35, ∀ μ : YoungDiagram, μ.card = 35 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 3 1) μ := by
  intro q hq
  simp only [degreeQs35,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone35_1

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeSeven
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Seven. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma sevenWitness_cols : sevenWitness.transpose.rowLens = [4,1,1,1] :=
  diagramOfCols_cols _ _ (by simp)

lemma sevenWitness_self : sevenWitness.transpose = sevenWitness := by
  apply YoungDiagram.ext
  decide

lemma sevenCertificate0 : contractionInteger [4,1,1,1] [4,1,1,1] [1,1,1,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB0 sevenPlaceT0 sevenFlag0 = -6 := by
  unfold sevenFlag0
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate1 : contractionInteger [4,1,1,1] [4,1,1,1] [2,1,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB1 sevenPlaceT1 sevenFlag1 = -2 := by
  unfold sevenFlag1
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate2 : contractionInteger [4,1,1,1] [4,1,1,1] [2,2,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB2 sevenPlaceT2 sevenFlag2 = 2 := by
  unfold sevenFlag2
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate3 : contractionInteger [4,1,1,1] [4,1,1,1] [3,1,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB3 sevenPlaceT3 sevenFlag3 = -10 := by
  unfold sevenFlag3
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate4 : contractionInteger [4,1,1,1] [4,1,1,1] [2,2,2,1]
    (Equiv.refl (Fin 7)) sevenPlaceB4 sevenPlaceT4 sevenFlag4 = 2 := by
  unfold sevenFlag4
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate5 : contractionInteger [4,1,1,1] [4,1,1,1] [3,2,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB5 sevenPlaceT5 sevenFlag5 = -2 := by
  unfold sevenFlag5
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate6 : contractionInteger [4,1,1,1] [4,1,1,1] [4,1,1,1]
    (Equiv.refl (Fin 7)) sevenPlaceB6 sevenPlaceT6 sevenFlag6 = 2 := by
  unfold sevenFlag6
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

lemma sevenCertificate7 : contractionInteger [4,1,1,1] [4,1,1,1] [3,2,2]
    (Equiv.refl (Fin 7)) sevenPlaceB7 sevenPlaceT7 sevenFlag7 = 2 := by
  unfold sevenFlag7
  simp_rw [← List.mem_toFinset]
  erw [contractionInteger_compact]
  decide +kernel

noncomputable section

lemma seven_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 7)
    (eb : Equiv.Perm (Fin 7)) (et : Fin 7 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [4,1,1,1] [4,1,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  exact kronecker_pos_of_integer_certificate _ _ _ [4,1,1,1] [4,1,1,1] rs
    sevenWitness_cols sevenWitness_cols (diagramOfCols_cols _ _ hp)
    (Equiv.refl _) eb et L hc

lemma seven_positive0 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [1,1,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [1,1,1,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB0 sevenPlaceT0 sevenFlag0
  intro hz
  have hh : (-6 : ℤ) = 0 := sevenCertificate0.symm.trans hz
  norm_num at hh

lemma seven_positive1 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,1,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB1 sevenPlaceT1 sevenFlag1
  intro hz
  have hh : (-2 : ℤ) = 0 := sevenCertificate1.symm.trans hz
  norm_num at hh

lemma seven_positive2 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,2,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,2,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB2 sevenPlaceT2 sevenFlag2
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate2.symm.trans hz
  norm_num at hh

lemma seven_positive3 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,1,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB3 sevenPlaceT3 sevenFlag3
  intro hz
  have hh : (-10 : ℤ) = 0 := sevenCertificate3.symm.trans hz
  norm_num at hh

lemma seven_positive4 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [2,2,2,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [2,2,2,1] (by decide) (by simp) rfl
    sevenPlaceB4 sevenPlaceT4 sevenFlag4
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate4.symm.trans hz
  norm_num at hh

lemma seven_positive5 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,2,1,1] (by decide) (by simp) rfl
    sevenPlaceB5 sevenPlaceT5 sevenFlag5
  intro hz
  have hh : (-2 : ℤ) = 0 := sevenCertificate5.symm.trans hz
  norm_num at hh

lemma seven_positive6 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [4,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [4,1,1,1] (by decide) (by simp) rfl
    sevenPlaceB6 sevenPlaceT6 sevenFlag6
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate6.symm.trans hz
  norm_num at hh

lemma seven_positive7 :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau (diagramOfCols [3,2,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply seven_positive_certificate [3,2,2] (by decide) (by simp) rfl
    sevenPlaceB7 sevenPlaceT7 sevenFlag7
  intro hz
  have hh : (2 : ℤ) = 0 := sevenCertificate7.symm.trans hz
  norm_num at hh

lemma seven_positive_target_eq {μ ν : YoungDiagram} (hμ : μ.card = 7) (hν : ν.card = 7)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

lemma partitionLists_seven : partitionLists 7 7 7 =
    {[7],[6,1],[5,2],[5,1,1],[4,3],[4,2,1],[4,1,1,1],[3,3,1],[3,2,2],[3,2,1,1],[3,1,1,1,1],[2,2,2,1],[2,2,1,1,1],[2,1,1,1,1,1],[1,1,1,1,1,1,1]} := by decide

theorem seven_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 7) :
    0 < kronecker (canonicalTableau sevenWitness sevenWitness_card)
      (canonicalTableau sevenWitness sevenWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_seven] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [7] (by decide) h
    have ht : diagramOfCols [7] (by decide) =
        (diagramOfCols [1,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive0
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,1] (by decide) h
    have ht : diagramOfCols [6,1] (by decide) =
        (diagramOfCols [2,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive1
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,2] (by decide) h
    have ht : diagramOfCols [5,2] (by decide) =
        (diagramOfCols [2,2,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive2
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,1,1] (by decide) h
    have ht : diagramOfCols [5,1,1] (by decide) =
        (diagramOfCols [3,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive3
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,3] (by decide) h
    have ht : diagramOfCols [4,3] (by decide) =
        (diagramOfCols [2,2,2,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive4
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,1] (by decide) h
    have ht : diagramOfCols [4,2,1] (by decide) =
        (diagramOfCols [3,2,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive5
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,1,1,1] (by decide) h
    subst ν
    exact seven_positive6
  · have he := eq_diagramOfCols ν [3,3,1] (by decide) h
    have ht : diagramOfCols [3,3,1] (by decide) =
        (diagramOfCols [3,2,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose sevenWitness sevenWitness_card sevenWitness_self
      _ _ seven_positive7
    exact seven_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [3,2,2] (by decide) h
    subst ν
    exact seven_positive7
  · have he := eq_diagramOfCols ν [3,2,1,1] (by decide) h
    subst ν
    exact seven_positive5
  · have he := eq_diagramOfCols ν [3,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive3
  · have he := eq_diagramOfCols ν [2,2,2,1] (by decide) h
    subst ν
    exact seven_positive4
  · have he := eq_diagramOfCols ν [2,2,1,1,1] (by decide) h
    subst ν
    exact seven_positive2
  · have he := eq_diagramOfCols ν [2,1,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive1
  · have he := eq_diagramOfCols ν [1,1,1,1,1,1,1] (by decide) h
    subst ν
    exact seven_positive0

universe u

end
end UniversalTensorSquare
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

lemma sg184 : RowSquare [4,1,1,1] [3,2,2] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [3,2,2])
  have hh : SquareOccurs sevenWitness (rowDiagram [3,2,2]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [3,2,2]),
      seven_kronecker_pos _ (rowDiagram_card [3,2,2])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [3,2,2])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5619 : RowSquare [6,4,1,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21479 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4720 sg5619

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree35_24All : degreeTree35_24.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21479,degreeTree35_12All,degreeTree35_23All⟩

lemma degreeTreeAll35 : degreeTree35.All
    (fun rs => SquareOccurs (candidate 6 3 1) (rowDiagram rs)) := by
  have hp : rowDiagram [10,8,4,3,2,2,2,2,1,1] = candidate 6 3 1 := rowDiagram_candidate (M := 6) (b := 3) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree35_24All

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos35_oai (μ : YoungDiagram) (hμ : μ.card = 35) :
    0 < kronecker (canonicalTableau (candidate 6 3 1) degreeCard35)
      (canonicalTableau (candidate 6 3 1) degreeCard35) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 7) (by decide) (by decide) rfl (by decide)
    degreeCard35 degreeRows35_0 (by decide) (by decide)
    degreePlan35_0 (by decide) (by decide) (by decide) (by decide) degreeP35 ?_
    degreeCheck35 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard35 rfl degreeCones35
    degreeTreeAll35 hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos35_oai := @OAI.UniversalTensorSquare.degree_pos35_oai
