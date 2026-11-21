-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_356All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:30:36.13696+00:00
-- url     : https://prove2.me/submissions/7d230e6b-e802-4a25-875e-32bf309cc8a8

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_Saxl_Balance_short_pair_support
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10223
import Theorems.Thm_OAI_UniversalTensorSquare_sg10224
import Theorems.Thm_OAI_UniversalTensorSquare_sg11307
import Theorems.Thm_OAI_UniversalTensorSquare_sg11498
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg19
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg28211
import Theorems.Thm_OAI_UniversalTensorSquare_sg28220
import Theorems.Thm_OAI_UniversalTensorSquare_sg28221
import Theorems.Thm_OAI_UniversalTensorSquare_sg28222
import Theorems.Thm_OAI_UniversalTensorSquare_sg28223
import Theorems.Thm_OAI_UniversalTensorSquare_sg28225
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg7454
import Theorems.Thm_OAI_UniversalTensorSquare_sg789
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468

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

lemma SquareOccurs.input_transpose {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    SquareOccurs α.transpose μ := by
  obtain ⟨n,a,t,ht⟩ := h
  exact ⟨n,transposeTableau a,t,kronecker_pos_input_transpose a t _ ht⟩

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

lemma rowSquare_of_cols {p q cs : List ℕ} (hp : GoodRows p) (hq : GoodRows q)
    (he : cs = transposeRows p ∨ cs = p)
    (h : SquareOccurs (columnShape cs) (columnShape (transposeRows q))) : RowSquare p q := by
  rw [columnShape_transposeRows hq] at h
  rcases he with rfl | rfl
  · simpa only [columnShape_transposeRows hp] using h
  · exact h.input_transpose

lemma kronecker_pos_of_projected {n : ℕ} {α μ : YoungDiagram}
    (a : Tableau n α) (t : Tableau n μ)
    (P : (Fin n → Fin (α.colLen 0 * α.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a P hP).toRepresentation) (hF : F ≠ 0) :
    0 < kronecker a a t := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨Z,hZ⟩ := subrepresentation_embeds_of_le_range
    ((invariantCoordinateProjection P hP).comp (spechtTensorMap a a))
    (projectedSpechtTensor a a P hP) le_rfl
  exact (kronecker_pos_iff a a t).mpr ⟨Z.comp F,intertwining_comp_ne_zero Z hZ F hF⟩

lemma rowSquare_short {p rs : List ℕ} (q δ : ℕ)
    (hp : GoodRows p) (hr : GoodRows rs) (hq : 0 < q) (hδ : δ = 1 ∨ δ = 2)
    (he : [q+δ,q] = transposeRows p ∨ [q+δ,q] = p)
    (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*q+δ)
    (ho : δ = 2 → ∃ j ∈ List.range (rs.sum+1),
      rs.countP (fun x => decide (j < x)) % 2 = 1) : RowSquare p rs := by
  have hs : GoodRows [q+δ,q] := by
    constructor
    · apply List.Pairwise.sortedGE; simp
    · simp; omega
  have hc : columnShape [q+δ,q] = (ShortColumns.shape q δ).transpose := by
    rw [columnShape_sorted _ hs.1 hs.2]; rfl
  let a := canonicalTableau (columnShape [q+δ,q])
    (show (columnShape [q+δ,q]).card = 2*q+δ by rw [columnShape_card]; simp; omega)
  let t := canonicalTableau (rowDiagram rs) ((rowDiagram_card _).trans hrs)
  have ha := a
  rw [hc] at ha
  obtain ⟨F,hF⟩ := short_pair_support q δ rfl hδ ha (rowDiagram rs) t
    (by rwa [rowDiagram_height hr]) (by
      intro hd
      obtain ⟨j,_,hj⟩ := ho hd
      exact ⟨j,by simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using hj⟩)
  have hh := kronecker_pos_of_projected ha t _ _ F hF
  apply rowSquare_of_cols hp hr he
  rw [columnShape_transposeRows hr,hc]
  exact ⟨2*q+δ,ha,t,hh⟩

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert92 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB92 sgT92) sgFlag92 = 1 := by
  decide +kernel

lemma sg92 : RowSquare [4,1,1] [3,3] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB92 sgT92 sgFlag92
  change solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB92 sgT92) sgFlag92 ≠ 0
  rw [sgCert92]
  norm_num

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg74 : RowSquare [3,2,1] [1,1,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [1,1,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1])) he) hh

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1])) he) hh

lemma sg181 : RowSquare [4,1,1,1] [2,2,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1])) he) hh

lemma sg1079 : RowSquare [6,4] [5,2,2,1] := by
  exact rowSquare_short 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg3299 : RowSquare [5,4,3,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [5,4,3,2,1] = (staircase 5) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [5,4,3,2,1]) (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 5) (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]) :=
    ⟨15,canonicalTableau _ (staircase_card 5),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]),
      saxl_kronecker_pos 5 (by decide) _ (rowDiagram_card [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])) he) hh

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

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

lemma sg135 : RowSquare [3,1,1,1,1] [4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg33

lemma sg137 : RowSquare [3,1,1,1,1] [4,3] := by
  exact rowSquare_join (by decide) sg0 sg92

lemma sg142 : RowSquare [3,2,1,1] [2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg74

lemma sg247 : RowSquare [2,2,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg19

lemma sg370 : RowSquare [5,1,1,1] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg178

lemma sg374 : RowSquare [5,1,1,1] [3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg179

lemma sg517 : RowSquare [4,1,1,1,1,1] [3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg178

lemma sg523 : RowSquare [4,1,1,1,1,1] [4,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg181

lemma sg589 : RowSquare [5,1,1,1,1] [2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg137

lemma sg608 : RowSquare [5,1,1,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg135

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg788 : RowSquare [3,3,1,1,1,1] [9,1] := by
  exact rowSquare_join (by decide) sg1 sg247

lemma sg1052 : RowSquare [6,2,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg69

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1361 : RowSquare [6,1,1,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg523

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2177 : RowSquare [6,4,2,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg142

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

lemma sg3876 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg374

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7813 : RowSquare [6,6,2,2,2,2] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg788 sg789

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6901 : RowSquare [5,4,3,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg3299

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

lemma sg8348 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1682

lemma sg8416 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2626

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10328 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1361

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8723 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg517 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10703 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9535 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1052 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14506 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg523 sg5735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15578 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1079 sg7813

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 69. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28212 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2177 sg15578

lemma sg28213 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3876 sg14506

lemma sg28214 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10223

lemma sg28215 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11307

lemma sg28216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6901 sg11498

lemma sg28217 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10328

lemma sg28218 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8348 sg10703

lemma sg28219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10224

lemma sg28224 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,5,4,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8723 sg9535

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree43_356All_oai : degreeTree43_356.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28218,⟨sg28214,⟨sg28212,⟨sg28211,True.intro,True.intro⟩,⟨sg28213,True.intro,True.intro⟩⟩,⟨sg28216,⟨sg28215,True.intro,True.intro⟩,⟨sg28217,True.intro,True.intro⟩⟩⟩,⟨sg28222,⟨sg28220,⟨sg28219,True.intro,True.intro⟩,⟨sg28221,True.intro,True.intro⟩⟩,⟨sg28224,⟨sg28223,True.intro,True.intro⟩,⟨sg28225,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_356All_oai := @OAI.UniversalTensorSquare.degreeTree43_356All_oai
